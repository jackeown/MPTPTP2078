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
% DateTime   : Thu Dec  3 12:09:54 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 446 expanded)
%              Number of clauses        :   86 ( 121 expanded)
%              Number of leaves         :   19 ( 151 expanded)
%              Depth                    :   18
%              Number of atoms          :  538 (3357 expanded)
%              Number of equality atoms :  208 ( 880 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
           => ! [X4] :
                ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                  & v1_funct_1(X4) )
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f33])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
          & k1_xboole_0 != X1
          & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
          & m1_subset_1(X5,X1) )
     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK5) != k7_partfun1(X0,X4,k1_funct_1(X3,sK5))
        & k1_xboole_0 != X1
        & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
        & m1_subset_1(sK5,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
              & k1_xboole_0 != X1
              & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK4),X5) != k7_partfun1(X0,sK4,k1_funct_1(X3,X5))
            & k1_xboole_0 != X1
            & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK4))
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( k1_funct_1(k8_funct_2(X1,X2,X0,sK3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(sK3,X5))
                & k1_xboole_0 != X1
                & r1_tarski(k2_relset_1(X1,X2,sK3),k1_relset_1(X2,X0,X4))
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK3,X1,X2)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                    & k1_xboole_0 != X1
                    & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                    & m1_subset_1(X5,X1) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != sK1
                  & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4))
                  & m1_subset_1(X5,sK1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X3,sK1,sK2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))
    & k1_xboole_0 != sK1
    & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    & m1_subset_1(sK5,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f34,f40,f39,f38,f37])).

fof(f67,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f69,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f64,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f68,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f41])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
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

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

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
    inference(nnf_transformation,[],[f28])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f63,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f61,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f62,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f31])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X1,X2)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f70,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1764,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_784,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | X1 != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_2])).

cnf(c_785,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_784])).

cnf(c_1759,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_785])).

cnf(c_3674,plain,
    ( sK1 = k1_xboole_0
    | r2_hidden(sK5,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1764,c_1759])).

cnf(c_35,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1991,plain,
    ( ~ m1_subset_1(X0,sK1)
    | r2_hidden(X0,sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_785])).

cnf(c_2083,plain,
    ( ~ m1_subset_1(sK5,sK1)
    | r2_hidden(sK5,sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1991])).

cnf(c_2084,plain,
    ( k1_xboole_0 = sK1
    | m1_subset_1(sK5,sK1) != iProver_top
    | r2_hidden(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2083])).

cnf(c_3739,plain,
    ( r2_hidden(sK5,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3674,c_35,c_20,c_2084])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1763,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_8,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1769,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2201,plain,
    ( v5_relat_1(sK4,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1763,c_1769])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1761,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1767,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2274,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1761,c_1767])).

cnf(c_21,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1765,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2442,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2274,c_1765])).

cnf(c_4,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1773,plain,
    ( r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v5_relat_1(X0,X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2917,plain,
    ( v5_relat_1(sK3,k1_relset_1(sK2,sK0,sK4)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2442,c_1773])).

cnf(c_32,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1952,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2142,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1952])).

cnf(c_2143,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2142])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2415,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2416,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2415])).

cnf(c_3495,plain,
    ( v5_relat_1(sK3,k1_relset_1(sK2,sK0,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2917,c_32,c_2143,c_2416])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1768,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2724,plain,
    ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1763,c_1768])).

cnf(c_3499,plain,
    ( v5_relat_1(sK3,k1_relat_1(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3495,c_2724])).

cnf(c_7,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X2),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1770,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
    | r2_hidden(k1_funct_1(X0,X2),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_17,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1766,plain,
    ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
    | v5_relat_1(X1,X0) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3704,plain,
    ( k7_partfun1(X0,X1,k1_funct_1(X2,X3)) = k1_funct_1(X1,k1_funct_1(X2,X3))
    | v5_relat_1(X1,X0) != iProver_top
    | v5_relat_1(X2,k1_relat_1(X1)) != iProver_top
    | r2_hidden(X3,k1_relat_1(X2)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1770,c_1766])).

cnf(c_4186,plain,
    ( k7_partfun1(X0,sK4,k1_funct_1(sK3,X1)) = k1_funct_1(sK4,k1_funct_1(sK3,X1))
    | v5_relat_1(sK4,X0) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3499,c_3704])).

cnf(c_2725,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1761,c_1768])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_746,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_26])).

cnf(c_747,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_746])).

cnf(c_749,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_747,c_25])).

cnf(c_3177,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2725,c_749])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_28,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_302,plain,
    ( sK2 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_28])).

cnf(c_3384,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3177,c_302])).

cnf(c_4211,plain,
    ( k7_partfun1(X0,sK4,k1_funct_1(sK3,X1)) = k1_funct_1(sK4,k1_funct_1(sK3,X1))
    | v5_relat_1(sK4,X0) != iProver_top
    | r2_hidden(X1,sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4186,c_3384])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_30,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_33,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_34,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2139,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK0))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1952])).

cnf(c_2140,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK2,sK0)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2139])).

cnf(c_2412,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2413,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2412])).

cnf(c_4613,plain,
    ( k7_partfun1(X0,sK4,k1_funct_1(sK3,X1)) = k1_funct_1(sK4,k1_funct_1(sK3,X1))
    | v5_relat_1(sK4,X0) != iProver_top
    | r2_hidden(X1,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4211,c_30,c_32,c_33,c_34,c_2140,c_2143,c_2413,c_2416])).

cnf(c_4622,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,X0)) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2201,c_4613])).

cnf(c_4762,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_3739,c_4622])).

cnf(c_1375,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1996,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != X0
    | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != X0
    | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_1375])).

cnf(c_3807,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))
    | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_1996])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X3,X4))
    | ~ m1_subset_1(X5,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_funct_1(k8_funct_2(X1,X2,X3,X0,X4),X5) = k1_funct_1(X4,k1_funct_1(X0,X5))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_719,plain,
    ( ~ r1_tarski(k2_relset_1(X0,X1,X2),k1_relset_1(X1,X3,X4))
    | ~ m1_subset_1(X5,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X4)
    | v1_xboole_0(X1)
    | k1_funct_1(k8_funct_2(X0,X1,X3,X2,X4),X5) = k1_funct_1(X4,k1_funct_1(X2,X5))
    | sK3 != X2
    | sK2 != X1
    | sK1 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_26])).

cnf(c_720,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | ~ m1_subset_1(X2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK2)
    | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_719])).

cnf(c_724,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | ~ m1_subset_1(X2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_720,c_28,c_27,c_25,c_20])).

cnf(c_725,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | ~ m1_subset_1(X2,sK1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2)) ),
    inference(renaming,[status(thm)],[c_724])).

cnf(c_1942,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,sK4))
    | ~ m1_subset_1(X1,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | ~ v1_funct_1(sK4)
    | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,sK4),X1) = k1_funct_1(sK4,k1_funct_1(sK3,X1)) ),
    inference(instantiation,[status(thm)],[c_725])).

cnf(c_2209,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,sK4))
    | ~ m1_subset_1(sK5,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | ~ v1_funct_1(sK4)
    | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_1942])).

cnf(c_2418,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ m1_subset_1(sK5,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ v1_funct_1(sK4)
    | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_2209])).

cnf(c_19,negated_conjecture,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f70])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4762,c_3807,c_2418,c_19,c_21,c_22,c_23,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:37:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.78/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/0.98  
% 2.78/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.78/0.98  
% 2.78/0.98  ------  iProver source info
% 2.78/0.98  
% 2.78/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.78/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.78/0.98  git: non_committed_changes: false
% 2.78/0.98  git: last_make_outside_of_git: false
% 2.78/0.98  
% 2.78/0.98  ------ 
% 2.78/0.98  
% 2.78/0.98  ------ Input Options
% 2.78/0.98  
% 2.78/0.98  --out_options                           all
% 2.78/0.98  --tptp_safe_out                         true
% 2.78/0.98  --problem_path                          ""
% 2.78/0.98  --include_path                          ""
% 2.78/0.98  --clausifier                            res/vclausify_rel
% 2.78/0.98  --clausifier_options                    --mode clausify
% 2.78/0.98  --stdin                                 false
% 2.78/0.98  --stats_out                             all
% 2.78/0.98  
% 2.78/0.98  ------ General Options
% 2.78/0.98  
% 2.78/0.98  --fof                                   false
% 2.78/0.98  --time_out_real                         305.
% 2.78/0.98  --time_out_virtual                      -1.
% 2.78/0.98  --symbol_type_check                     false
% 2.78/0.98  --clausify_out                          false
% 2.78/0.98  --sig_cnt_out                           false
% 2.78/0.98  --trig_cnt_out                          false
% 2.78/0.98  --trig_cnt_out_tolerance                1.
% 2.78/0.98  --trig_cnt_out_sk_spl                   false
% 2.78/0.98  --abstr_cl_out                          false
% 2.78/0.98  
% 2.78/0.98  ------ Global Options
% 2.78/0.98  
% 2.78/0.98  --schedule                              default
% 2.78/0.98  --add_important_lit                     false
% 2.78/0.98  --prop_solver_per_cl                    1000
% 2.78/0.98  --min_unsat_core                        false
% 2.78/0.98  --soft_assumptions                      false
% 2.78/0.98  --soft_lemma_size                       3
% 2.78/0.98  --prop_impl_unit_size                   0
% 2.78/0.98  --prop_impl_unit                        []
% 2.78/0.98  --share_sel_clauses                     true
% 2.78/0.98  --reset_solvers                         false
% 2.78/0.98  --bc_imp_inh                            [conj_cone]
% 2.78/0.98  --conj_cone_tolerance                   3.
% 2.78/0.98  --extra_neg_conj                        none
% 2.78/0.98  --large_theory_mode                     true
% 2.78/0.98  --prolific_symb_bound                   200
% 2.78/0.98  --lt_threshold                          2000
% 2.78/0.98  --clause_weak_htbl                      true
% 2.78/0.98  --gc_record_bc_elim                     false
% 2.78/0.98  
% 2.78/0.98  ------ Preprocessing Options
% 2.78/0.98  
% 2.78/0.98  --preprocessing_flag                    true
% 2.78/0.98  --time_out_prep_mult                    0.1
% 2.78/0.98  --splitting_mode                        input
% 2.78/0.98  --splitting_grd                         true
% 2.78/0.98  --splitting_cvd                         false
% 2.78/0.98  --splitting_cvd_svl                     false
% 2.78/0.98  --splitting_nvd                         32
% 2.78/0.98  --sub_typing                            true
% 2.78/0.98  --prep_gs_sim                           true
% 2.78/0.98  --prep_unflatten                        true
% 2.78/0.98  --prep_res_sim                          true
% 2.78/0.98  --prep_upred                            true
% 2.78/0.98  --prep_sem_filter                       exhaustive
% 2.78/0.98  --prep_sem_filter_out                   false
% 2.78/0.98  --pred_elim                             true
% 2.78/0.98  --res_sim_input                         true
% 2.78/0.98  --eq_ax_congr_red                       true
% 2.78/0.98  --pure_diseq_elim                       true
% 2.78/0.98  --brand_transform                       false
% 2.78/0.98  --non_eq_to_eq                          false
% 2.78/0.98  --prep_def_merge                        true
% 2.78/0.98  --prep_def_merge_prop_impl              false
% 2.78/0.98  --prep_def_merge_mbd                    true
% 2.78/0.98  --prep_def_merge_tr_red                 false
% 2.78/0.98  --prep_def_merge_tr_cl                  false
% 2.78/0.98  --smt_preprocessing                     true
% 2.78/0.98  --smt_ac_axioms                         fast
% 2.78/0.98  --preprocessed_out                      false
% 2.78/0.98  --preprocessed_stats                    false
% 2.78/0.98  
% 2.78/0.98  ------ Abstraction refinement Options
% 2.78/0.98  
% 2.78/0.98  --abstr_ref                             []
% 2.78/0.98  --abstr_ref_prep                        false
% 2.78/0.98  --abstr_ref_until_sat                   false
% 2.78/0.98  --abstr_ref_sig_restrict                funpre
% 2.78/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.78/0.98  --abstr_ref_under                       []
% 2.78/0.98  
% 2.78/0.98  ------ SAT Options
% 2.78/0.98  
% 2.78/0.98  --sat_mode                              false
% 2.78/0.98  --sat_fm_restart_options                ""
% 2.78/0.98  --sat_gr_def                            false
% 2.78/0.98  --sat_epr_types                         true
% 2.78/0.98  --sat_non_cyclic_types                  false
% 2.78/0.98  --sat_finite_models                     false
% 2.78/0.98  --sat_fm_lemmas                         false
% 2.78/0.98  --sat_fm_prep                           false
% 2.78/0.98  --sat_fm_uc_incr                        true
% 2.78/0.98  --sat_out_model                         small
% 2.78/0.98  --sat_out_clauses                       false
% 2.78/0.98  
% 2.78/0.98  ------ QBF Options
% 2.78/0.98  
% 2.78/0.98  --qbf_mode                              false
% 2.78/0.98  --qbf_elim_univ                         false
% 2.78/0.98  --qbf_dom_inst                          none
% 2.78/0.98  --qbf_dom_pre_inst                      false
% 2.78/0.98  --qbf_sk_in                             false
% 2.78/0.98  --qbf_pred_elim                         true
% 2.78/0.98  --qbf_split                             512
% 2.78/0.98  
% 2.78/0.98  ------ BMC1 Options
% 2.78/0.98  
% 2.78/0.98  --bmc1_incremental                      false
% 2.78/0.98  --bmc1_axioms                           reachable_all
% 2.78/0.98  --bmc1_min_bound                        0
% 2.78/0.98  --bmc1_max_bound                        -1
% 2.78/0.98  --bmc1_max_bound_default                -1
% 2.78/0.98  --bmc1_symbol_reachability              true
% 2.78/0.98  --bmc1_property_lemmas                  false
% 2.78/0.98  --bmc1_k_induction                      false
% 2.78/0.98  --bmc1_non_equiv_states                 false
% 2.78/0.98  --bmc1_deadlock                         false
% 2.78/0.98  --bmc1_ucm                              false
% 2.78/0.98  --bmc1_add_unsat_core                   none
% 2.78/0.98  --bmc1_unsat_core_children              false
% 2.78/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.78/0.98  --bmc1_out_stat                         full
% 2.78/0.98  --bmc1_ground_init                      false
% 2.78/0.98  --bmc1_pre_inst_next_state              false
% 2.78/0.98  --bmc1_pre_inst_state                   false
% 2.78/0.98  --bmc1_pre_inst_reach_state             false
% 2.78/0.98  --bmc1_out_unsat_core                   false
% 2.78/0.98  --bmc1_aig_witness_out                  false
% 2.78/0.98  --bmc1_verbose                          false
% 2.78/0.98  --bmc1_dump_clauses_tptp                false
% 2.78/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.78/0.98  --bmc1_dump_file                        -
% 2.78/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.78/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.78/0.98  --bmc1_ucm_extend_mode                  1
% 2.78/0.98  --bmc1_ucm_init_mode                    2
% 2.78/0.98  --bmc1_ucm_cone_mode                    none
% 2.78/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.78/0.98  --bmc1_ucm_relax_model                  4
% 2.78/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.78/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.78/0.98  --bmc1_ucm_layered_model                none
% 2.78/0.98  --bmc1_ucm_max_lemma_size               10
% 2.78/0.98  
% 2.78/0.98  ------ AIG Options
% 2.78/0.98  
% 2.78/0.98  --aig_mode                              false
% 2.78/0.98  
% 2.78/0.98  ------ Instantiation Options
% 2.78/0.98  
% 2.78/0.98  --instantiation_flag                    true
% 2.78/0.98  --inst_sos_flag                         false
% 2.78/0.98  --inst_sos_phase                        true
% 2.78/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.78/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.78/0.98  --inst_lit_sel_side                     num_symb
% 2.78/0.98  --inst_solver_per_active                1400
% 2.78/0.98  --inst_solver_calls_frac                1.
% 2.78/0.98  --inst_passive_queue_type               priority_queues
% 2.78/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.78/0.98  --inst_passive_queues_freq              [25;2]
% 2.78/0.98  --inst_dismatching                      true
% 2.78/0.98  --inst_eager_unprocessed_to_passive     true
% 2.78/0.98  --inst_prop_sim_given                   true
% 2.78/0.98  --inst_prop_sim_new                     false
% 2.78/0.98  --inst_subs_new                         false
% 2.78/0.98  --inst_eq_res_simp                      false
% 2.78/0.98  --inst_subs_given                       false
% 2.78/0.98  --inst_orphan_elimination               true
% 2.78/0.98  --inst_learning_loop_flag               true
% 2.78/0.98  --inst_learning_start                   3000
% 2.78/0.98  --inst_learning_factor                  2
% 2.78/0.98  --inst_start_prop_sim_after_learn       3
% 2.78/0.98  --inst_sel_renew                        solver
% 2.78/0.98  --inst_lit_activity_flag                true
% 2.78/0.98  --inst_restr_to_given                   false
% 2.78/0.98  --inst_activity_threshold               500
% 2.78/0.98  --inst_out_proof                        true
% 2.78/0.98  
% 2.78/0.98  ------ Resolution Options
% 2.78/0.98  
% 2.78/0.98  --resolution_flag                       true
% 2.78/0.98  --res_lit_sel                           adaptive
% 2.78/0.98  --res_lit_sel_side                      none
% 2.78/0.98  --res_ordering                          kbo
% 2.78/0.98  --res_to_prop_solver                    active
% 2.78/0.98  --res_prop_simpl_new                    false
% 2.78/0.98  --res_prop_simpl_given                  true
% 2.78/0.98  --res_passive_queue_type                priority_queues
% 2.78/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.78/0.98  --res_passive_queues_freq               [15;5]
% 2.78/0.98  --res_forward_subs                      full
% 2.78/0.98  --res_backward_subs                     full
% 2.78/0.98  --res_forward_subs_resolution           true
% 2.78/0.98  --res_backward_subs_resolution          true
% 2.78/0.98  --res_orphan_elimination                true
% 2.78/0.98  --res_time_limit                        2.
% 2.78/0.98  --res_out_proof                         true
% 2.78/0.98  
% 2.78/0.98  ------ Superposition Options
% 2.78/0.98  
% 2.78/0.98  --superposition_flag                    true
% 2.78/0.98  --sup_passive_queue_type                priority_queues
% 2.78/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.78/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.78/0.98  --demod_completeness_check              fast
% 2.78/0.98  --demod_use_ground                      true
% 2.78/0.98  --sup_to_prop_solver                    passive
% 2.78/0.98  --sup_prop_simpl_new                    true
% 2.78/0.98  --sup_prop_simpl_given                  true
% 2.78/0.98  --sup_fun_splitting                     false
% 2.78/0.98  --sup_smt_interval                      50000
% 2.78/0.98  
% 2.78/0.98  ------ Superposition Simplification Setup
% 2.78/0.98  
% 2.78/0.98  --sup_indices_passive                   []
% 2.78/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.78/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/0.98  --sup_full_bw                           [BwDemod]
% 2.78/0.98  --sup_immed_triv                        [TrivRules]
% 2.78/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.78/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/0.98  --sup_immed_bw_main                     []
% 2.78/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.78/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/0.98  
% 2.78/0.98  ------ Combination Options
% 2.78/0.98  
% 2.78/0.98  --comb_res_mult                         3
% 2.78/0.98  --comb_sup_mult                         2
% 2.78/0.98  --comb_inst_mult                        10
% 2.78/0.98  
% 2.78/0.98  ------ Debug Options
% 2.78/0.98  
% 2.78/0.98  --dbg_backtrace                         false
% 2.78/0.98  --dbg_dump_prop_clauses                 false
% 2.78/0.98  --dbg_dump_prop_clauses_file            -
% 2.78/0.98  --dbg_out_stat                          false
% 2.78/0.98  ------ Parsing...
% 2.78/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.78/0.98  
% 2.78/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.78/0.98  
% 2.78/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.78/0.98  
% 2.78/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.78/0.98  ------ Proving...
% 2.78/0.98  ------ Problem Properties 
% 2.78/0.98  
% 2.78/0.98  
% 2.78/0.98  clauses                                 24
% 2.78/0.98  conjectures                             8
% 2.78/0.98  EPR                                     7
% 2.78/0.98  Horn                                    21
% 2.78/0.98  unary                                   10
% 2.78/0.98  binary                                  5
% 2.78/0.98  lits                                    60
% 2.78/0.98  lits eq                                 16
% 2.78/0.98  fd_pure                                 0
% 2.78/0.98  fd_pseudo                               0
% 2.78/0.98  fd_cond                                 2
% 2.78/0.98  fd_pseudo_cond                          0
% 2.78/0.98  AC symbols                              0
% 2.78/0.98  
% 2.78/0.98  ------ Schedule dynamic 5 is on 
% 2.78/0.98  
% 2.78/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.78/0.98  
% 2.78/0.98  
% 2.78/0.98  ------ 
% 2.78/0.98  Current options:
% 2.78/0.98  ------ 
% 2.78/0.98  
% 2.78/0.98  ------ Input Options
% 2.78/0.98  
% 2.78/0.98  --out_options                           all
% 2.78/0.98  --tptp_safe_out                         true
% 2.78/0.98  --problem_path                          ""
% 2.78/0.98  --include_path                          ""
% 2.78/0.98  --clausifier                            res/vclausify_rel
% 2.78/0.98  --clausifier_options                    --mode clausify
% 2.78/0.98  --stdin                                 false
% 2.78/0.98  --stats_out                             all
% 2.78/0.98  
% 2.78/0.98  ------ General Options
% 2.78/0.98  
% 2.78/0.98  --fof                                   false
% 2.78/0.98  --time_out_real                         305.
% 2.78/0.98  --time_out_virtual                      -1.
% 2.78/0.98  --symbol_type_check                     false
% 2.78/0.98  --clausify_out                          false
% 2.78/0.98  --sig_cnt_out                           false
% 2.78/0.98  --trig_cnt_out                          false
% 2.78/0.98  --trig_cnt_out_tolerance                1.
% 2.78/0.98  --trig_cnt_out_sk_spl                   false
% 2.78/0.98  --abstr_cl_out                          false
% 2.78/0.98  
% 2.78/0.98  ------ Global Options
% 2.78/0.98  
% 2.78/0.98  --schedule                              default
% 2.78/0.98  --add_important_lit                     false
% 2.78/0.98  --prop_solver_per_cl                    1000
% 2.78/0.98  --min_unsat_core                        false
% 2.78/0.98  --soft_assumptions                      false
% 2.78/0.98  --soft_lemma_size                       3
% 2.78/0.98  --prop_impl_unit_size                   0
% 2.78/0.98  --prop_impl_unit                        []
% 2.78/0.98  --share_sel_clauses                     true
% 2.78/0.98  --reset_solvers                         false
% 2.78/0.98  --bc_imp_inh                            [conj_cone]
% 2.78/0.98  --conj_cone_tolerance                   3.
% 2.78/0.98  --extra_neg_conj                        none
% 2.78/0.98  --large_theory_mode                     true
% 2.78/0.98  --prolific_symb_bound                   200
% 2.78/0.98  --lt_threshold                          2000
% 2.78/0.98  --clause_weak_htbl                      true
% 2.78/0.98  --gc_record_bc_elim                     false
% 2.78/0.98  
% 2.78/0.98  ------ Preprocessing Options
% 2.78/0.98  
% 2.78/0.98  --preprocessing_flag                    true
% 2.78/0.98  --time_out_prep_mult                    0.1
% 2.78/0.98  --splitting_mode                        input
% 2.78/0.98  --splitting_grd                         true
% 2.78/0.98  --splitting_cvd                         false
% 2.78/0.98  --splitting_cvd_svl                     false
% 2.78/0.98  --splitting_nvd                         32
% 2.78/0.98  --sub_typing                            true
% 2.78/0.98  --prep_gs_sim                           true
% 2.78/0.98  --prep_unflatten                        true
% 2.78/0.98  --prep_res_sim                          true
% 2.78/0.98  --prep_upred                            true
% 2.78/0.98  --prep_sem_filter                       exhaustive
% 2.78/0.98  --prep_sem_filter_out                   false
% 2.78/0.98  --pred_elim                             true
% 2.78/0.98  --res_sim_input                         true
% 2.78/0.98  --eq_ax_congr_red                       true
% 2.78/0.98  --pure_diseq_elim                       true
% 2.78/0.98  --brand_transform                       false
% 2.78/0.98  --non_eq_to_eq                          false
% 2.78/0.98  --prep_def_merge                        true
% 2.78/0.98  --prep_def_merge_prop_impl              false
% 2.78/0.98  --prep_def_merge_mbd                    true
% 2.78/0.98  --prep_def_merge_tr_red                 false
% 2.78/0.98  --prep_def_merge_tr_cl                  false
% 2.78/0.98  --smt_preprocessing                     true
% 2.78/0.98  --smt_ac_axioms                         fast
% 2.78/0.98  --preprocessed_out                      false
% 2.78/0.98  --preprocessed_stats                    false
% 2.78/0.98  
% 2.78/0.98  ------ Abstraction refinement Options
% 2.78/0.98  
% 2.78/0.98  --abstr_ref                             []
% 2.78/0.98  --abstr_ref_prep                        false
% 2.78/0.98  --abstr_ref_until_sat                   false
% 2.78/0.98  --abstr_ref_sig_restrict                funpre
% 2.78/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.78/0.98  --abstr_ref_under                       []
% 2.78/0.98  
% 2.78/0.98  ------ SAT Options
% 2.78/0.98  
% 2.78/0.98  --sat_mode                              false
% 2.78/0.98  --sat_fm_restart_options                ""
% 2.78/0.98  --sat_gr_def                            false
% 2.78/0.98  --sat_epr_types                         true
% 2.78/0.98  --sat_non_cyclic_types                  false
% 2.78/0.98  --sat_finite_models                     false
% 2.78/0.98  --sat_fm_lemmas                         false
% 2.78/0.98  --sat_fm_prep                           false
% 2.78/0.98  --sat_fm_uc_incr                        true
% 2.78/0.98  --sat_out_model                         small
% 2.78/0.98  --sat_out_clauses                       false
% 2.78/0.98  
% 2.78/0.98  ------ QBF Options
% 2.78/0.98  
% 2.78/0.98  --qbf_mode                              false
% 2.78/0.98  --qbf_elim_univ                         false
% 2.78/0.98  --qbf_dom_inst                          none
% 2.78/0.98  --qbf_dom_pre_inst                      false
% 2.78/0.98  --qbf_sk_in                             false
% 2.78/0.98  --qbf_pred_elim                         true
% 2.78/0.98  --qbf_split                             512
% 2.78/0.98  
% 2.78/0.98  ------ BMC1 Options
% 2.78/0.98  
% 2.78/0.98  --bmc1_incremental                      false
% 2.78/0.98  --bmc1_axioms                           reachable_all
% 2.78/0.98  --bmc1_min_bound                        0
% 2.78/0.98  --bmc1_max_bound                        -1
% 2.78/0.98  --bmc1_max_bound_default                -1
% 2.78/0.98  --bmc1_symbol_reachability              true
% 2.78/0.98  --bmc1_property_lemmas                  false
% 2.78/0.98  --bmc1_k_induction                      false
% 2.78/0.98  --bmc1_non_equiv_states                 false
% 2.78/0.98  --bmc1_deadlock                         false
% 2.78/0.98  --bmc1_ucm                              false
% 2.78/0.98  --bmc1_add_unsat_core                   none
% 2.78/0.98  --bmc1_unsat_core_children              false
% 2.78/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.78/0.98  --bmc1_out_stat                         full
% 2.78/0.98  --bmc1_ground_init                      false
% 2.78/0.98  --bmc1_pre_inst_next_state              false
% 2.78/0.98  --bmc1_pre_inst_state                   false
% 2.78/0.98  --bmc1_pre_inst_reach_state             false
% 2.78/0.98  --bmc1_out_unsat_core                   false
% 2.78/0.98  --bmc1_aig_witness_out                  false
% 2.78/0.98  --bmc1_verbose                          false
% 2.78/0.98  --bmc1_dump_clauses_tptp                false
% 2.78/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.78/0.98  --bmc1_dump_file                        -
% 2.78/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.78/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.78/0.98  --bmc1_ucm_extend_mode                  1
% 2.78/0.98  --bmc1_ucm_init_mode                    2
% 2.78/0.98  --bmc1_ucm_cone_mode                    none
% 2.78/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.78/0.98  --bmc1_ucm_relax_model                  4
% 2.78/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.78/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.78/0.98  --bmc1_ucm_layered_model                none
% 2.78/0.98  --bmc1_ucm_max_lemma_size               10
% 2.78/0.98  
% 2.78/0.98  ------ AIG Options
% 2.78/0.98  
% 2.78/0.98  --aig_mode                              false
% 2.78/0.98  
% 2.78/0.98  ------ Instantiation Options
% 2.78/0.98  
% 2.78/0.98  --instantiation_flag                    true
% 2.78/0.98  --inst_sos_flag                         false
% 2.78/0.98  --inst_sos_phase                        true
% 2.78/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.78/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.78/0.98  --inst_lit_sel_side                     none
% 2.78/0.98  --inst_solver_per_active                1400
% 2.78/0.98  --inst_solver_calls_frac                1.
% 2.78/0.98  --inst_passive_queue_type               priority_queues
% 2.78/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.78/0.98  --inst_passive_queues_freq              [25;2]
% 2.78/0.98  --inst_dismatching                      true
% 2.78/0.98  --inst_eager_unprocessed_to_passive     true
% 2.78/0.98  --inst_prop_sim_given                   true
% 2.78/0.98  --inst_prop_sim_new                     false
% 2.78/0.98  --inst_subs_new                         false
% 2.78/0.98  --inst_eq_res_simp                      false
% 2.78/0.98  --inst_subs_given                       false
% 2.78/0.98  --inst_orphan_elimination               true
% 2.78/0.98  --inst_learning_loop_flag               true
% 2.78/0.98  --inst_learning_start                   3000
% 2.78/0.98  --inst_learning_factor                  2
% 2.78/0.98  --inst_start_prop_sim_after_learn       3
% 2.78/0.98  --inst_sel_renew                        solver
% 2.78/0.98  --inst_lit_activity_flag                true
% 2.78/0.98  --inst_restr_to_given                   false
% 2.78/0.98  --inst_activity_threshold               500
% 2.78/0.98  --inst_out_proof                        true
% 2.78/0.98  
% 2.78/0.98  ------ Resolution Options
% 2.78/0.98  
% 2.78/0.98  --resolution_flag                       false
% 2.78/0.98  --res_lit_sel                           adaptive
% 2.78/0.98  --res_lit_sel_side                      none
% 2.78/0.98  --res_ordering                          kbo
% 2.78/0.98  --res_to_prop_solver                    active
% 2.78/0.98  --res_prop_simpl_new                    false
% 2.78/0.98  --res_prop_simpl_given                  true
% 2.78/0.98  --res_passive_queue_type                priority_queues
% 2.78/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.78/0.98  --res_passive_queues_freq               [15;5]
% 2.78/0.98  --res_forward_subs                      full
% 2.78/0.98  --res_backward_subs                     full
% 2.78/0.98  --res_forward_subs_resolution           true
% 2.78/0.98  --res_backward_subs_resolution          true
% 2.78/0.98  --res_orphan_elimination                true
% 2.78/0.98  --res_time_limit                        2.
% 2.78/0.98  --res_out_proof                         true
% 2.78/0.98  
% 2.78/0.98  ------ Superposition Options
% 2.78/0.98  
% 2.78/0.98  --superposition_flag                    true
% 2.78/0.98  --sup_passive_queue_type                priority_queues
% 2.78/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.78/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.78/0.98  --demod_completeness_check              fast
% 2.78/0.98  --demod_use_ground                      true
% 2.78/0.98  --sup_to_prop_solver                    passive
% 2.78/0.98  --sup_prop_simpl_new                    true
% 2.78/0.98  --sup_prop_simpl_given                  true
% 2.78/0.98  --sup_fun_splitting                     false
% 2.78/0.98  --sup_smt_interval                      50000
% 2.78/0.98  
% 2.78/0.98  ------ Superposition Simplification Setup
% 2.78/0.98  
% 2.78/0.98  --sup_indices_passive                   []
% 2.78/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.78/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/0.98  --sup_full_bw                           [BwDemod]
% 2.78/0.98  --sup_immed_triv                        [TrivRules]
% 2.78/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.78/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/0.98  --sup_immed_bw_main                     []
% 2.78/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.78/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/0.98  
% 2.78/0.98  ------ Combination Options
% 2.78/0.98  
% 2.78/0.98  --comb_res_mult                         3
% 2.78/0.98  --comb_sup_mult                         2
% 2.78/0.98  --comb_inst_mult                        10
% 2.78/0.98  
% 2.78/0.98  ------ Debug Options
% 2.78/0.98  
% 2.78/0.98  --dbg_backtrace                         false
% 2.78/0.98  --dbg_dump_prop_clauses                 false
% 2.78/0.98  --dbg_dump_prop_clauses_file            -
% 2.78/0.98  --dbg_out_stat                          false
% 2.78/0.98  
% 2.78/0.98  
% 2.78/0.98  
% 2.78/0.98  
% 2.78/0.98  ------ Proving...
% 2.78/0.98  
% 2.78/0.98  
% 2.78/0.98  % SZS status Theorem for theBenchmark.p
% 2.78/0.98  
% 2.78/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.78/0.98  
% 2.78/0.98  fof(f14,conjecture,(
% 2.78/0.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 2.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/0.98  
% 2.78/0.98  fof(f15,negated_conjecture,(
% 2.78/0.98    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 2.78/0.98    inference(negated_conjecture,[],[f14])).
% 2.78/0.98  
% 2.78/0.98  fof(f33,plain,(
% 2.78/0.98    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 2.78/0.98    inference(ennf_transformation,[],[f15])).
% 2.78/0.98  
% 2.78/0.98  fof(f34,plain,(
% 2.78/0.98    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 2.78/0.98    inference(flattening,[],[f33])).
% 2.78/0.98  
% 2.78/0.98  fof(f40,plain,(
% 2.78/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK5) != k7_partfun1(X0,X4,k1_funct_1(X3,sK5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK5,X1))) )),
% 2.78/0.98    introduced(choice_axiom,[])).
% 2.78/0.98  
% 2.78/0.98  fof(f39,plain,(
% 2.78/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK4),X5) != k7_partfun1(X0,sK4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK4)) & m1_subset_1(X5,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK4))) )),
% 2.78/0.98    introduced(choice_axiom,[])).
% 2.78/0.98  
% 2.78/0.98  fof(f38,plain,(
% 2.78/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,sK3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(sK3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK3,X1,X2) & v1_funct_1(sK3))) )),
% 2.78/0.98    introduced(choice_axiom,[])).
% 2.78/0.98  
% 2.78/0.98  fof(f37,plain,(
% 2.78/0.98    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & ~v1_xboole_0(sK2))),
% 2.78/0.98    introduced(choice_axiom,[])).
% 2.78/0.98  
% 2.78/0.98  fof(f41,plain,(
% 2.78/0.98    (((k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)),
% 2.78/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f34,f40,f39,f38,f37])).
% 2.78/0.98  
% 2.78/0.98  fof(f67,plain,(
% 2.78/0.98    m1_subset_1(sK5,sK1)),
% 2.78/0.98    inference(cnf_transformation,[],[f41])).
% 2.78/0.98  
% 2.78/0.98  fof(f2,axiom,(
% 2.78/0.98    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/0.98  
% 2.78/0.98  fof(f17,plain,(
% 2.78/0.98    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.78/0.98    inference(ennf_transformation,[],[f2])).
% 2.78/0.98  
% 2.78/0.98  fof(f43,plain,(
% 2.78/0.98    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.78/0.98    inference(cnf_transformation,[],[f17])).
% 2.78/0.98  
% 2.78/0.98  fof(f3,axiom,(
% 2.78/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/0.98  
% 2.78/0.98  fof(f18,plain,(
% 2.78/0.98    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.78/0.98    inference(ennf_transformation,[],[f3])).
% 2.78/0.98  
% 2.78/0.98  fof(f19,plain,(
% 2.78/0.98    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.78/0.98    inference(flattening,[],[f18])).
% 2.78/0.98  
% 2.78/0.98  fof(f44,plain,(
% 2.78/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.78/0.98    inference(cnf_transformation,[],[f19])).
% 2.78/0.98  
% 2.78/0.98  fof(f69,plain,(
% 2.78/0.98    k1_xboole_0 != sK1),
% 2.78/0.98    inference(cnf_transformation,[],[f41])).
% 2.78/0.98  
% 2.78/0.98  fof(f66,plain,(
% 2.78/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 2.78/0.98    inference(cnf_transformation,[],[f41])).
% 2.78/0.98  
% 2.78/0.98  fof(f8,axiom,(
% 2.78/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/0.98  
% 2.78/0.98  fof(f16,plain,(
% 2.78/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.78/0.98    inference(pure_predicate_removal,[],[f8])).
% 2.78/0.98  
% 2.78/0.98  fof(f24,plain,(
% 2.78/0.98    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.78/0.98    inference(ennf_transformation,[],[f16])).
% 2.78/0.98  
% 2.78/0.98  fof(f50,plain,(
% 2.78/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.78/0.98    inference(cnf_transformation,[],[f24])).
% 2.78/0.98  
% 2.78/0.98  fof(f64,plain,(
% 2.78/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.78/0.98    inference(cnf_transformation,[],[f41])).
% 2.78/0.98  
% 2.78/0.98  fof(f10,axiom,(
% 2.78/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/0.98  
% 2.78/0.98  fof(f26,plain,(
% 2.78/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.78/0.98    inference(ennf_transformation,[],[f10])).
% 2.78/0.98  
% 2.78/0.98  fof(f52,plain,(
% 2.78/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.78/0.98    inference(cnf_transformation,[],[f26])).
% 2.78/0.98  
% 2.78/0.98  fof(f68,plain,(
% 2.78/0.98    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 2.78/0.98    inference(cnf_transformation,[],[f41])).
% 2.78/0.98  
% 2.78/0.98  fof(f5,axiom,(
% 2.78/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/0.98  
% 2.78/0.98  fof(f21,plain,(
% 2.78/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.78/0.98    inference(ennf_transformation,[],[f5])).
% 2.78/0.98  
% 2.78/0.98  fof(f35,plain,(
% 2.78/0.98    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.78/0.98    inference(nnf_transformation,[],[f21])).
% 2.78/0.98  
% 2.78/0.98  fof(f47,plain,(
% 2.78/0.98    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.78/0.98    inference(cnf_transformation,[],[f35])).
% 2.78/0.98  
% 2.78/0.98  fof(f4,axiom,(
% 2.78/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/0.98  
% 2.78/0.98  fof(f20,plain,(
% 2.78/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.78/0.98    inference(ennf_transformation,[],[f4])).
% 2.78/0.98  
% 2.78/0.98  fof(f45,plain,(
% 2.78/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.78/0.98    inference(cnf_transformation,[],[f20])).
% 2.78/0.98  
% 2.78/0.98  fof(f6,axiom,(
% 2.78/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/0.98  
% 2.78/0.98  fof(f48,plain,(
% 2.78/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.78/0.98    inference(cnf_transformation,[],[f6])).
% 2.78/0.98  
% 2.78/0.98  fof(f9,axiom,(
% 2.78/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/0.98  
% 2.78/0.98  fof(f25,plain,(
% 2.78/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.78/0.98    inference(ennf_transformation,[],[f9])).
% 2.78/0.98  
% 2.78/0.98  fof(f51,plain,(
% 2.78/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.78/0.98    inference(cnf_transformation,[],[f25])).
% 2.78/0.98  
% 2.78/0.98  fof(f7,axiom,(
% 2.78/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 2.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/0.98  
% 2.78/0.98  fof(f22,plain,(
% 2.78/0.98    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.78/0.98    inference(ennf_transformation,[],[f7])).
% 2.78/0.98  
% 2.78/0.98  fof(f23,plain,(
% 2.78/0.98    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.78/0.98    inference(flattening,[],[f22])).
% 2.78/0.98  
% 2.78/0.98  fof(f49,plain,(
% 2.78/0.98    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.78/0.98    inference(cnf_transformation,[],[f23])).
% 2.78/0.98  
% 2.78/0.98  fof(f12,axiom,(
% 2.78/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)))),
% 2.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/0.98  
% 2.78/0.98  fof(f29,plain,(
% 2.78/0.98    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.78/0.98    inference(ennf_transformation,[],[f12])).
% 2.78/0.98  
% 2.78/0.98  fof(f30,plain,(
% 2.78/0.98    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.78/0.98    inference(flattening,[],[f29])).
% 2.78/0.98  
% 2.78/0.98  fof(f59,plain,(
% 2.78/0.98    ( ! [X2,X0,X1] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.78/0.98    inference(cnf_transformation,[],[f30])).
% 2.78/0.98  
% 2.78/0.98  fof(f11,axiom,(
% 2.78/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/0.98  
% 2.78/0.98  fof(f27,plain,(
% 2.78/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.78/0.98    inference(ennf_transformation,[],[f11])).
% 2.78/0.98  
% 2.78/0.98  fof(f28,plain,(
% 2.78/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.78/0.98    inference(flattening,[],[f27])).
% 2.78/0.98  
% 2.78/0.98  fof(f36,plain,(
% 2.78/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.78/0.98    inference(nnf_transformation,[],[f28])).
% 2.78/0.98  
% 2.78/0.98  fof(f53,plain,(
% 2.78/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.78/0.98    inference(cnf_transformation,[],[f36])).
% 2.78/0.98  
% 2.78/0.98  fof(f63,plain,(
% 2.78/0.98    v1_funct_2(sK3,sK1,sK2)),
% 2.78/0.98    inference(cnf_transformation,[],[f41])).
% 2.78/0.98  
% 2.78/0.98  fof(f1,axiom,(
% 2.78/0.98    v1_xboole_0(k1_xboole_0)),
% 2.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/0.98  
% 2.78/0.98  fof(f42,plain,(
% 2.78/0.98    v1_xboole_0(k1_xboole_0)),
% 2.78/0.98    inference(cnf_transformation,[],[f1])).
% 2.78/0.98  
% 2.78/0.98  fof(f61,plain,(
% 2.78/0.98    ~v1_xboole_0(sK2)),
% 2.78/0.98    inference(cnf_transformation,[],[f41])).
% 2.78/0.98  
% 2.78/0.98  fof(f62,plain,(
% 2.78/0.98    v1_funct_1(sK3)),
% 2.78/0.98    inference(cnf_transformation,[],[f41])).
% 2.78/0.98  
% 2.78/0.98  fof(f65,plain,(
% 2.78/0.98    v1_funct_1(sK4)),
% 2.78/0.98    inference(cnf_transformation,[],[f41])).
% 2.78/0.98  
% 2.78/0.98  fof(f13,axiom,(
% 2.78/0.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 2.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/0.98  
% 2.78/0.98  fof(f31,plain,(
% 2.78/0.98    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 2.78/0.98    inference(ennf_transformation,[],[f13])).
% 2.78/0.98  
% 2.78/0.98  fof(f32,plain,(
% 2.78/0.98    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 2.78/0.98    inference(flattening,[],[f31])).
% 2.78/0.98  
% 2.78/0.98  fof(f60,plain,(
% 2.78/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 2.78/0.98    inference(cnf_transformation,[],[f32])).
% 2.78/0.98  
% 2.78/0.98  fof(f70,plain,(
% 2.78/0.98    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 2.78/0.98    inference(cnf_transformation,[],[f41])).
% 2.78/0.98  
% 2.78/0.98  cnf(c_22,negated_conjecture,
% 2.78/0.98      ( m1_subset_1(sK5,sK1) ),
% 2.78/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1764,plain,
% 2.78/0.98      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 2.78/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1,plain,
% 2.78/0.98      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.78/0.98      inference(cnf_transformation,[],[f43]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2,plain,
% 2.78/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.78/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_784,plain,
% 2.78/0.98      ( ~ m1_subset_1(X0,X1)
% 2.78/0.98      | r2_hidden(X0,X1)
% 2.78/0.98      | X1 != X2
% 2.78/0.98      | k1_xboole_0 = X2 ),
% 2.78/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_2]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_785,plain,
% 2.78/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | k1_xboole_0 = X1 ),
% 2.78/0.98      inference(unflattening,[status(thm)],[c_784]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1759,plain,
% 2.78/0.98      ( k1_xboole_0 = X0
% 2.78/0.98      | m1_subset_1(X1,X0) != iProver_top
% 2.78/0.98      | r2_hidden(X1,X0) = iProver_top ),
% 2.78/0.98      inference(predicate_to_equality,[status(thm)],[c_785]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_3674,plain,
% 2.78/0.98      ( sK1 = k1_xboole_0 | r2_hidden(sK5,sK1) = iProver_top ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_1764,c_1759]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_35,plain,
% 2.78/0.98      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 2.78/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_20,negated_conjecture,
% 2.78/0.98      ( k1_xboole_0 != sK1 ),
% 2.78/0.98      inference(cnf_transformation,[],[f69]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1991,plain,
% 2.78/0.98      ( ~ m1_subset_1(X0,sK1) | r2_hidden(X0,sK1) | k1_xboole_0 = sK1 ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_785]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2083,plain,
% 2.78/0.98      ( ~ m1_subset_1(sK5,sK1) | r2_hidden(sK5,sK1) | k1_xboole_0 = sK1 ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_1991]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2084,plain,
% 2.78/0.98      ( k1_xboole_0 = sK1
% 2.78/0.98      | m1_subset_1(sK5,sK1) != iProver_top
% 2.78/0.98      | r2_hidden(sK5,sK1) = iProver_top ),
% 2.78/0.98      inference(predicate_to_equality,[status(thm)],[c_2083]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_3739,plain,
% 2.78/0.98      ( r2_hidden(sK5,sK1) = iProver_top ),
% 2.78/0.98      inference(global_propositional_subsumption,
% 2.78/0.98                [status(thm)],
% 2.78/0.98                [c_3674,c_35,c_20,c_2084]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_23,negated_conjecture,
% 2.78/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
% 2.78/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1763,plain,
% 2.78/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
% 2.78/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_8,plain,
% 2.78/0.98      ( v5_relat_1(X0,X1)
% 2.78/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.78/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1769,plain,
% 2.78/0.98      ( v5_relat_1(X0,X1) = iProver_top
% 2.78/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 2.78/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2201,plain,
% 2.78/0.98      ( v5_relat_1(sK4,sK0) = iProver_top ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_1763,c_1769]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_25,negated_conjecture,
% 2.78/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.78/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1761,plain,
% 2.78/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.78/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_10,plain,
% 2.78/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.78/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1767,plain,
% 2.78/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.78/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.78/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2274,plain,
% 2.78/0.98      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_1761,c_1767]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_21,negated_conjecture,
% 2.78/0.98      ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
% 2.78/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1765,plain,
% 2.78/0.98      ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) = iProver_top ),
% 2.78/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2442,plain,
% 2.78/0.98      ( r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4)) = iProver_top ),
% 2.78/0.98      inference(demodulation,[status(thm)],[c_2274,c_1765]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_4,plain,
% 2.78/0.98      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 2.78/0.98      | v5_relat_1(X0,X1)
% 2.78/0.98      | ~ v1_relat_1(X0) ),
% 2.78/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1773,plain,
% 2.78/0.98      ( r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 2.78/0.98      | v5_relat_1(X0,X1) = iProver_top
% 2.78/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.78/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2917,plain,
% 2.78/0.98      ( v5_relat_1(sK3,k1_relset_1(sK2,sK0,sK4)) = iProver_top
% 2.78/0.98      | v1_relat_1(sK3) != iProver_top ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_2442,c_1773]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_32,plain,
% 2.78/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.78/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_3,plain,
% 2.78/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.78/0.98      | ~ v1_relat_1(X1)
% 2.78/0.98      | v1_relat_1(X0) ),
% 2.78/0.98      inference(cnf_transformation,[],[f45]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1952,plain,
% 2.78/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/0.98      | v1_relat_1(X0)
% 2.78/0.98      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2142,plain,
% 2.78/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.78/0.98      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
% 2.78/0.98      | v1_relat_1(sK3) ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_1952]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2143,plain,
% 2.78/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.78/0.98      | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 2.78/0.98      | v1_relat_1(sK3) = iProver_top ),
% 2.78/0.98      inference(predicate_to_equality,[status(thm)],[c_2142]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_6,plain,
% 2.78/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.78/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2415,plain,
% 2.78/0.98      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2416,plain,
% 2.78/0.98      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 2.78/0.98      inference(predicate_to_equality,[status(thm)],[c_2415]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_3495,plain,
% 2.78/0.98      ( v5_relat_1(sK3,k1_relset_1(sK2,sK0,sK4)) = iProver_top ),
% 2.78/0.98      inference(global_propositional_subsumption,
% 2.78/0.98                [status(thm)],
% 2.78/0.98                [c_2917,c_32,c_2143,c_2416]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_9,plain,
% 2.78/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.78/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1768,plain,
% 2.78/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.78/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.78/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2724,plain,
% 2.78/0.98      ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_1763,c_1768]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_3499,plain,
% 2.78/0.98      ( v5_relat_1(sK3,k1_relat_1(sK4)) = iProver_top ),
% 2.78/0.98      inference(light_normalisation,[status(thm)],[c_3495,c_2724]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_7,plain,
% 2.78/0.98      ( ~ v5_relat_1(X0,X1)
% 2.78/0.98      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.78/0.98      | r2_hidden(k1_funct_1(X0,X2),X1)
% 2.78/0.98      | ~ v1_funct_1(X0)
% 2.78/0.98      | ~ v1_relat_1(X0) ),
% 2.78/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1770,plain,
% 2.78/0.98      ( v5_relat_1(X0,X1) != iProver_top
% 2.78/0.98      | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
% 2.78/0.98      | r2_hidden(k1_funct_1(X0,X2),X1) = iProver_top
% 2.78/0.98      | v1_funct_1(X0) != iProver_top
% 2.78/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.78/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_17,plain,
% 2.78/0.98      ( ~ v5_relat_1(X0,X1)
% 2.78/0.98      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.78/0.98      | ~ v1_funct_1(X0)
% 2.78/0.98      | ~ v1_relat_1(X0)
% 2.78/0.98      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 2.78/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1766,plain,
% 2.78/0.98      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
% 2.78/0.98      | v5_relat_1(X1,X0) != iProver_top
% 2.78/0.98      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 2.78/0.98      | v1_funct_1(X1) != iProver_top
% 2.78/0.98      | v1_relat_1(X1) != iProver_top ),
% 2.78/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_3704,plain,
% 2.78/0.98      ( k7_partfun1(X0,X1,k1_funct_1(X2,X3)) = k1_funct_1(X1,k1_funct_1(X2,X3))
% 2.78/0.98      | v5_relat_1(X1,X0) != iProver_top
% 2.78/0.98      | v5_relat_1(X2,k1_relat_1(X1)) != iProver_top
% 2.78/0.98      | r2_hidden(X3,k1_relat_1(X2)) != iProver_top
% 2.78/0.98      | v1_funct_1(X2) != iProver_top
% 2.78/0.98      | v1_funct_1(X1) != iProver_top
% 2.78/0.98      | v1_relat_1(X2) != iProver_top
% 2.78/0.98      | v1_relat_1(X1) != iProver_top ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_1770,c_1766]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_4186,plain,
% 2.78/0.98      ( k7_partfun1(X0,sK4,k1_funct_1(sK3,X1)) = k1_funct_1(sK4,k1_funct_1(sK3,X1))
% 2.78/0.98      | v5_relat_1(sK4,X0) != iProver_top
% 2.78/0.98      | r2_hidden(X1,k1_relat_1(sK3)) != iProver_top
% 2.78/0.98      | v1_funct_1(sK4) != iProver_top
% 2.78/0.98      | v1_funct_1(sK3) != iProver_top
% 2.78/0.98      | v1_relat_1(sK4) != iProver_top
% 2.78/0.98      | v1_relat_1(sK3) != iProver_top ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_3499,c_3704]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2725,plain,
% 2.78/0.98      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_1761,c_1768]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_16,plain,
% 2.78/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.78/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/0.98      | k1_relset_1(X1,X2,X0) = X1
% 2.78/0.98      | k1_xboole_0 = X2 ),
% 2.78/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_26,negated_conjecture,
% 2.78/0.98      ( v1_funct_2(sK3,sK1,sK2) ),
% 2.78/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_746,plain,
% 2.78/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/0.98      | k1_relset_1(X1,X2,X0) = X1
% 2.78/0.98      | sK3 != X0
% 2.78/0.98      | sK2 != X2
% 2.78/0.98      | sK1 != X1
% 2.78/0.98      | k1_xboole_0 = X2 ),
% 2.78/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_26]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_747,plain,
% 2.78/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.78/0.98      | k1_relset_1(sK1,sK2,sK3) = sK1
% 2.78/0.98      | k1_xboole_0 = sK2 ),
% 2.78/0.98      inference(unflattening,[status(thm)],[c_746]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_749,plain,
% 2.78/0.98      ( k1_relset_1(sK1,sK2,sK3) = sK1 | k1_xboole_0 = sK2 ),
% 2.78/0.98      inference(global_propositional_subsumption,
% 2.78/0.98                [status(thm)],
% 2.78/0.98                [c_747,c_25]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_3177,plain,
% 2.78/0.98      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_2725,c_749]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_0,plain,
% 2.78/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 2.78/0.98      inference(cnf_transformation,[],[f42]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_28,negated_conjecture,
% 2.78/0.98      ( ~ v1_xboole_0(sK2) ),
% 2.78/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_302,plain,
% 2.78/0.98      ( sK2 != k1_xboole_0 ),
% 2.78/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_28]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_3384,plain,
% 2.78/0.98      ( k1_relat_1(sK3) = sK1 ),
% 2.78/0.98      inference(global_propositional_subsumption,
% 2.78/0.98                [status(thm)],
% 2.78/0.98                [c_3177,c_302]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_4211,plain,
% 2.78/0.98      ( k7_partfun1(X0,sK4,k1_funct_1(sK3,X1)) = k1_funct_1(sK4,k1_funct_1(sK3,X1))
% 2.78/0.98      | v5_relat_1(sK4,X0) != iProver_top
% 2.78/0.98      | r2_hidden(X1,sK1) != iProver_top
% 2.78/0.98      | v1_funct_1(sK4) != iProver_top
% 2.78/0.98      | v1_funct_1(sK3) != iProver_top
% 2.78/0.98      | v1_relat_1(sK4) != iProver_top
% 2.78/0.98      | v1_relat_1(sK3) != iProver_top ),
% 2.78/0.98      inference(light_normalisation,[status(thm)],[c_4186,c_3384]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_27,negated_conjecture,
% 2.78/0.98      ( v1_funct_1(sK3) ),
% 2.78/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_30,plain,
% 2.78/0.98      ( v1_funct_1(sK3) = iProver_top ),
% 2.78/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_24,negated_conjecture,
% 2.78/0.98      ( v1_funct_1(sK4) ),
% 2.78/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_33,plain,
% 2.78/0.98      ( v1_funct_1(sK4) = iProver_top ),
% 2.78/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_34,plain,
% 2.78/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
% 2.78/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2139,plain,
% 2.78/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
% 2.78/0.98      | ~ v1_relat_1(k2_zfmisc_1(sK2,sK0))
% 2.78/0.98      | v1_relat_1(sK4) ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_1952]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2140,plain,
% 2.78/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top
% 2.78/0.98      | v1_relat_1(k2_zfmisc_1(sK2,sK0)) != iProver_top
% 2.78/0.98      | v1_relat_1(sK4) = iProver_top ),
% 2.78/0.98      inference(predicate_to_equality,[status(thm)],[c_2139]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2412,plain,
% 2.78/0.98      ( v1_relat_1(k2_zfmisc_1(sK2,sK0)) ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2413,plain,
% 2.78/0.98      ( v1_relat_1(k2_zfmisc_1(sK2,sK0)) = iProver_top ),
% 2.78/0.98      inference(predicate_to_equality,[status(thm)],[c_2412]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_4613,plain,
% 2.78/0.98      ( k7_partfun1(X0,sK4,k1_funct_1(sK3,X1)) = k1_funct_1(sK4,k1_funct_1(sK3,X1))
% 2.78/0.98      | v5_relat_1(sK4,X0) != iProver_top
% 2.78/0.98      | r2_hidden(X1,sK1) != iProver_top ),
% 2.78/0.98      inference(global_propositional_subsumption,
% 2.78/0.98                [status(thm)],
% 2.78/0.98                [c_4211,c_30,c_32,c_33,c_34,c_2140,c_2143,c_2413,c_2416]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_4622,plain,
% 2.78/0.98      ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,X0)) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
% 2.78/0.98      | r2_hidden(X0,sK1) != iProver_top ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_2201,c_4613]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_4762,plain,
% 2.78/0.98      ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.78/0.98      inference(superposition,[status(thm)],[c_3739,c_4622]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1375,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1996,plain,
% 2.78/0.98      ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != X0
% 2.78/0.98      | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != X0
% 2.78/0.98      | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_1375]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_3807,plain,
% 2.78/0.98      ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
% 2.78/0.98      | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))
% 2.78/0.98      | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_1996]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_18,plain,
% 2.78/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.78/0.98      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X3,X4))
% 2.78/0.98      | ~ m1_subset_1(X5,X1)
% 2.78/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.78/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/0.98      | ~ v1_funct_1(X4)
% 2.78/0.98      | ~ v1_funct_1(X0)
% 2.78/0.98      | v1_xboole_0(X2)
% 2.78/0.98      | k1_funct_1(k8_funct_2(X1,X2,X3,X0,X4),X5) = k1_funct_1(X4,k1_funct_1(X0,X5))
% 2.78/0.98      | k1_xboole_0 = X1 ),
% 2.78/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_719,plain,
% 2.78/0.98      ( ~ r1_tarski(k2_relset_1(X0,X1,X2),k1_relset_1(X1,X3,X4))
% 2.78/0.98      | ~ m1_subset_1(X5,X0)
% 2.78/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.78/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.78/0.98      | ~ v1_funct_1(X2)
% 2.78/0.98      | ~ v1_funct_1(X4)
% 2.78/0.98      | v1_xboole_0(X1)
% 2.78/0.98      | k1_funct_1(k8_funct_2(X0,X1,X3,X2,X4),X5) = k1_funct_1(X4,k1_funct_1(X2,X5))
% 2.78/0.98      | sK3 != X2
% 2.78/0.98      | sK2 != X1
% 2.78/0.98      | sK1 != X0
% 2.78/0.98      | k1_xboole_0 = X0 ),
% 2.78/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_26]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_720,plain,
% 2.78/0.98      ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
% 2.78/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 2.78/0.98      | ~ m1_subset_1(X2,sK1)
% 2.78/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.78/0.98      | ~ v1_funct_1(X1)
% 2.78/0.98      | ~ v1_funct_1(sK3)
% 2.78/0.98      | v1_xboole_0(sK2)
% 2.78/0.98      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
% 2.78/0.98      | k1_xboole_0 = sK1 ),
% 2.78/0.98      inference(unflattening,[status(thm)],[c_719]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_724,plain,
% 2.78/0.98      ( k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
% 2.78/0.98      | ~ v1_funct_1(X1)
% 2.78/0.98      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
% 2.78/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 2.78/0.98      | ~ m1_subset_1(X2,sK1) ),
% 2.78/0.98      inference(global_propositional_subsumption,
% 2.78/0.98                [status(thm)],
% 2.78/0.98                [c_720,c_28,c_27,c_25,c_20]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_725,plain,
% 2.78/0.98      ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
% 2.78/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 2.78/0.98      | ~ m1_subset_1(X2,sK1)
% 2.78/0.98      | ~ v1_funct_1(X1)
% 2.78/0.98      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2)) ),
% 2.78/0.98      inference(renaming,[status(thm)],[c_724]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1942,plain,
% 2.78/0.98      ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,sK4))
% 2.78/0.98      | ~ m1_subset_1(X1,sK1)
% 2.78/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 2.78/0.98      | ~ v1_funct_1(sK4)
% 2.78/0.98      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,sK4),X1) = k1_funct_1(sK4,k1_funct_1(sK3,X1)) ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_725]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2209,plain,
% 2.78/0.98      ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,sK4))
% 2.78/0.98      | ~ m1_subset_1(sK5,sK1)
% 2.78/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 2.78/0.98      | ~ v1_funct_1(sK4)
% 2.78/0.98      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_1942]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2418,plain,
% 2.78/0.98      ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
% 2.78/0.98      | ~ m1_subset_1(sK5,sK1)
% 2.78/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
% 2.78/0.98      | ~ v1_funct_1(sK4)
% 2.78/0.98      | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_2209]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_19,negated_conjecture,
% 2.78/0.98      ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
% 2.78/0.98      inference(cnf_transformation,[],[f70]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(contradiction,plain,
% 2.78/0.98      ( $false ),
% 2.78/0.98      inference(minisat,
% 2.78/0.98                [status(thm)],
% 2.78/0.98                [c_4762,c_3807,c_2418,c_19,c_21,c_22,c_23,c_24]) ).
% 2.78/0.98  
% 2.78/0.98  
% 2.78/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.78/0.98  
% 2.78/0.98  ------                               Statistics
% 2.78/0.98  
% 2.78/0.98  ------ General
% 2.78/0.98  
% 2.78/0.98  abstr_ref_over_cycles:                  0
% 2.78/0.98  abstr_ref_under_cycles:                 0
% 2.78/0.98  gc_basic_clause_elim:                   0
% 2.78/0.98  forced_gc_time:                         0
% 2.78/0.98  parsing_time:                           0.01
% 2.78/0.98  unif_index_cands_time:                  0.
% 2.78/0.98  unif_index_add_time:                    0.
% 2.78/0.98  orderings_time:                         0.
% 2.78/0.98  out_proof_time:                         0.009
% 2.78/0.98  total_time:                             0.278
% 2.78/0.98  num_of_symbols:                         55
% 2.78/0.98  num_of_terms:                           9532
% 2.78/0.98  
% 2.78/0.98  ------ Preprocessing
% 2.78/0.98  
% 2.78/0.98  num_of_splits:                          0
% 2.78/0.98  num_of_split_atoms:                     0
% 2.78/0.98  num_of_reused_defs:                     0
% 2.78/0.98  num_eq_ax_congr_red:                    12
% 2.78/0.98  num_of_sem_filtered_clauses:            1
% 2.78/0.98  num_of_subtypes:                        0
% 2.78/0.98  monotx_restored_types:                  0
% 2.78/0.98  sat_num_of_epr_types:                   0
% 2.78/0.98  sat_num_of_non_cyclic_types:            0
% 2.78/0.98  sat_guarded_non_collapsed_types:        0
% 2.78/0.98  num_pure_diseq_elim:                    0
% 2.78/0.98  simp_replaced_by:                       0
% 2.78/0.98  res_preprocessed:                       130
% 2.78/0.98  prep_upred:                             0
% 2.78/0.98  prep_unflattend:                        52
% 2.78/0.98  smt_new_axioms:                         0
% 2.78/0.98  pred_elim_cands:                        6
% 2.78/0.98  pred_elim:                              2
% 2.78/0.98  pred_elim_cl:                           5
% 2.78/0.98  pred_elim_cycles:                       8
% 2.78/0.98  merged_defs:                            0
% 2.78/0.98  merged_defs_ncl:                        0
% 2.78/0.98  bin_hyper_res:                          0
% 2.78/0.98  prep_cycles:                            4
% 2.78/0.98  pred_elim_time:                         0.037
% 2.78/0.98  splitting_time:                         0.
% 2.78/0.98  sem_filter_time:                        0.
% 2.78/0.98  monotx_time:                            0.001
% 2.78/0.98  subtype_inf_time:                       0.
% 2.78/0.98  
% 2.78/0.98  ------ Problem properties
% 2.78/0.98  
% 2.78/0.98  clauses:                                24
% 2.78/0.98  conjectures:                            8
% 2.78/0.98  epr:                                    7
% 2.78/0.98  horn:                                   21
% 2.78/0.98  ground:                                 11
% 2.78/0.98  unary:                                  10
% 2.78/0.98  binary:                                 5
% 2.78/0.98  lits:                                   60
% 2.78/0.98  lits_eq:                                16
% 2.78/0.98  fd_pure:                                0
% 2.78/0.98  fd_pseudo:                              0
% 2.78/0.98  fd_cond:                                2
% 2.78/0.98  fd_pseudo_cond:                         0
% 2.78/0.98  ac_symbols:                             0
% 2.78/0.98  
% 2.78/0.98  ------ Propositional Solver
% 2.78/0.98  
% 2.78/0.98  prop_solver_calls:                      27
% 2.78/0.98  prop_fast_solver_calls:                 1098
% 2.78/0.98  smt_solver_calls:                       0
% 2.78/0.98  smt_fast_solver_calls:                  0
% 2.78/0.98  prop_num_of_clauses:                    1599
% 2.78/0.98  prop_preprocess_simplified:             4858
% 2.78/0.98  prop_fo_subsumed:                       29
% 2.78/0.98  prop_solver_time:                       0.
% 2.78/0.98  smt_solver_time:                        0.
% 2.78/0.98  smt_fast_solver_time:                   0.
% 2.78/0.98  prop_fast_solver_time:                  0.
% 2.78/0.98  prop_unsat_core_time:                   0.
% 2.78/0.98  
% 2.78/0.98  ------ QBF
% 2.78/0.98  
% 2.78/0.98  qbf_q_res:                              0
% 2.78/0.98  qbf_num_tautologies:                    0
% 2.78/0.98  qbf_prep_cycles:                        0
% 2.78/0.98  
% 2.78/0.98  ------ BMC1
% 2.78/0.98  
% 2.78/0.98  bmc1_current_bound:                     -1
% 2.78/0.98  bmc1_last_solved_bound:                 -1
% 2.78/0.98  bmc1_unsat_core_size:                   -1
% 2.78/0.98  bmc1_unsat_core_parents_size:           -1
% 2.78/0.98  bmc1_merge_next_fun:                    0
% 2.78/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.78/0.98  
% 2.78/0.98  ------ Instantiation
% 2.78/0.98  
% 2.78/0.98  inst_num_of_clauses:                    458
% 2.78/0.98  inst_num_in_passive:                    71
% 2.78/0.98  inst_num_in_active:                     266
% 2.78/0.98  inst_num_in_unprocessed:                121
% 2.78/0.98  inst_num_of_loops:                      280
% 2.78/0.98  inst_num_of_learning_restarts:          0
% 2.78/0.98  inst_num_moves_active_passive:          11
% 2.78/0.98  inst_lit_activity:                      0
% 2.78/0.98  inst_lit_activity_moves:                0
% 2.78/0.98  inst_num_tautologies:                   0
% 2.78/0.98  inst_num_prop_implied:                  0
% 2.78/0.98  inst_num_existing_simplified:           0
% 2.78/0.98  inst_num_eq_res_simplified:             0
% 2.78/0.98  inst_num_child_elim:                    0
% 2.78/0.98  inst_num_of_dismatching_blockings:      69
% 2.78/0.98  inst_num_of_non_proper_insts:           333
% 2.78/0.98  inst_num_of_duplicates:                 0
% 2.78/0.98  inst_inst_num_from_inst_to_res:         0
% 2.78/0.98  inst_dismatching_checking_time:         0.
% 2.78/0.98  
% 2.78/0.98  ------ Resolution
% 2.78/0.98  
% 2.78/0.98  res_num_of_clauses:                     0
% 2.78/0.98  res_num_in_passive:                     0
% 2.78/0.98  res_num_in_active:                      0
% 2.78/0.98  res_num_of_loops:                       134
% 2.78/0.98  res_forward_subset_subsumed:            50
% 2.78/0.98  res_backward_subset_subsumed:           0
% 2.78/0.98  res_forward_subsumed:                   0
% 2.78/0.98  res_backward_subsumed:                  0
% 2.78/0.98  res_forward_subsumption_resolution:     1
% 2.78/0.98  res_backward_subsumption_resolution:    0
% 2.78/0.98  res_clause_to_clause_subsumption:       222
% 2.78/0.98  res_orphan_elimination:                 0
% 2.78/0.98  res_tautology_del:                      41
% 2.78/0.98  res_num_eq_res_simplified:              0
% 2.78/0.98  res_num_sel_changes:                    0
% 2.78/0.98  res_moves_from_active_to_pass:          0
% 2.78/0.98  
% 2.78/0.98  ------ Superposition
% 2.78/0.98  
% 2.78/0.98  sup_time_total:                         0.
% 2.78/0.98  sup_time_generating:                    0.
% 2.78/0.98  sup_time_sim_full:                      0.
% 2.78/0.98  sup_time_sim_immed:                     0.
% 2.78/0.98  
% 2.78/0.98  sup_num_of_clauses:                     58
% 2.78/0.98  sup_num_in_active:                      50
% 2.78/0.98  sup_num_in_passive:                     8
% 2.78/0.98  sup_num_of_loops:                       54
% 2.78/0.98  sup_fw_superposition:                   35
% 2.78/0.98  sup_bw_superposition:                   8
% 2.78/0.98  sup_immediate_simplified:               6
% 2.78/0.98  sup_given_eliminated:                   0
% 2.78/0.98  comparisons_done:                       0
% 2.78/0.98  comparisons_avoided:                    0
% 2.78/0.98  
% 2.78/0.98  ------ Simplifications
% 2.78/0.98  
% 2.78/0.98  
% 2.78/0.98  sim_fw_subset_subsumed:                 0
% 2.78/0.98  sim_bw_subset_subsumed:                 2
% 2.78/0.98  sim_fw_subsumed:                        3
% 2.78/0.98  sim_bw_subsumed:                        0
% 2.78/0.98  sim_fw_subsumption_res:                 1
% 2.78/0.98  sim_bw_subsumption_res:                 0
% 2.78/0.98  sim_tautology_del:                      1
% 2.78/0.98  sim_eq_tautology_del:                   0
% 2.78/0.98  sim_eq_res_simp:                        0
% 2.78/0.98  sim_fw_demodulated:                     0
% 2.78/0.98  sim_bw_demodulated:                     4
% 2.78/0.98  sim_light_normalised:                   6
% 2.78/0.98  sim_joinable_taut:                      0
% 2.78/0.98  sim_joinable_simp:                      0
% 2.78/0.98  sim_ac_normalised:                      0
% 2.78/0.98  sim_smt_subsumption:                    0
% 2.78/0.98  
%------------------------------------------------------------------------------
