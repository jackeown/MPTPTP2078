%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:45 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 473 expanded)
%              Number of clauses        :  100 ( 136 expanded)
%              Number of leaves         :   23 ( 151 expanded)
%              Depth                    :   19
%              Number of atoms          :  605 (3271 expanded)
%              Number of equality atoms :  219 ( 838 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
          & k1_xboole_0 != X1
          & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
          & m1_subset_1(X5,X1) )
     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK7) != k7_partfun1(X0,X4,k1_funct_1(X3,sK7))
        & k1_xboole_0 != X1
        & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
        & m1_subset_1(sK7,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
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
            ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK6),X5) != k7_partfun1(X0,sK6,k1_funct_1(X3,X5))
            & k1_xboole_0 != X1
            & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK6))
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
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
                ( k1_funct_1(k8_funct_2(X1,X2,X0,sK5,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(sK5,X5))
                & k1_xboole_0 != X1
                & r1_tarski(k2_relset_1(X1,X2,sK5),k1_relset_1(X2,X0,X4))
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK5,X1,X2)
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
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
                  ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,X3,X4),X5) != k7_partfun1(sK2,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != sK3
                  & r1_tarski(k2_relset_1(sK3,sK4,X3),k1_relset_1(sK4,sK2,X4))
                  & m1_subset_1(X5,sK3) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
          & v1_funct_2(X3,sK3,sK4)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7))
    & k1_xboole_0 != sK3
    & r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6))
    & m1_subset_1(sK7,sK3)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5)
    & ~ v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f41,f59,f58,f57,f56])).

fof(f100,plain,(
    m1_subset_1(sK7,sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f102,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f60])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f50])).

fof(f69,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f46])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f47,f48])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).

fof(f61,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f99,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f60])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f97,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f60])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f101,plain,(
    r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
    inference(cnf_transformation,[],[f60])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

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

fof(f55,plain,(
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

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f96,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f60])).

fof(f94,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f60])).

fof(f95,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f60])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f98,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f60])).

fof(f18,axiom,(
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

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f93,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f103,plain,(
    k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK7,sK3) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1776,plain,
    ( m1_subset_1(sK7,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1785,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4980,plain,
    ( r2_hidden(sK7,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1776,c_1785])).

cnf(c_34,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_115,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2095,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK3)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2096,plain,
    ( k1_xboole_0 = sK3
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2095])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2205,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | r2_hidden(sK1(sK3,k1_xboole_0),sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2206,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top
    | r2_hidden(sK1(sK3,k1_xboole_0),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2205])).

cnf(c_2319,plain,
    ( r1_tarski(k1_xboole_0,sK3)
    | r2_hidden(sK1(k1_xboole_0,sK3),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2320,plain,
    ( r1_tarski(k1_xboole_0,sK3) = iProver_top
    | r2_hidden(sK1(k1_xboole_0,sK3),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2319])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2863,plain,
    ( ~ r2_hidden(sK1(sK3,k1_xboole_0),sK3)
    | ~ v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2864,plain,
    ( r2_hidden(sK1(sK3,k1_xboole_0),sK3) != iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2863])).

cnf(c_5011,plain,
    ( ~ r2_hidden(sK1(k1_xboole_0,sK3),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_5012,plain,
    ( r2_hidden(sK1(k1_xboole_0,sK3),k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5011])).

cnf(c_5200,plain,
    ( r2_hidden(sK7,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4980,c_34,c_115,c_2096,c_2206,c_2320,c_2864,c_5012])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1780,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1775,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1779,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3759,plain,
    ( k1_relset_1(sK4,sK2,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1775,c_1779])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1773,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1778,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3119,plain,
    ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1773,c_1778])).

cnf(c_35,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1777,plain,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_3256,plain,
    ( r1_tarski(k2_relat_1(sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3119,c_1777])).

cnf(c_3867,plain,
    ( r1_tarski(k2_relat_1(sK5),k1_relat_1(sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3759,c_3256])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1789,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5089,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3867,c_1789])).

cnf(c_8190,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1780,c_5089])).

cnf(c_3760,plain,
    ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1773,c_1779])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_40,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_627,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X0
    | sK4 != X2
    | sK3 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_40])).

cnf(c_628,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_627])).

cnf(c_630,plain,
    ( k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_628,c_39])).

cnf(c_4115,plain,
    ( k1_relat_1(sK5) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3760,c_630])).

cnf(c_42,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_996,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2063,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_996])).

cnf(c_2065,plain,
    ( v1_xboole_0(sK4)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2063])).

cnf(c_4487,plain,
    ( k1_relat_1(sK5) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4115,c_42,c_5,c_2065])).

cnf(c_8195,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8190,c_4487])).

cnf(c_41,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_44,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1783,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2850,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1773,c_1783])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_13,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_286,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_287,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_286])).

cnf(c_362,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_15,c_287])).

cnf(c_1770,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_362])).

cnf(c_4869,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2850,c_1770])).

cnf(c_16,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1782,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5369,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4869,c_1782])).

cnf(c_8277,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8195,c_44,c_5369])).

cnf(c_19,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_31,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_485,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(resolution,[status(thm)],[c_19,c_31])).

cnf(c_1769,plain,
    ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_485])).

cnf(c_3617,plain,
    ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1775,c_1769])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_47,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_4141,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
    | v1_relat_1(sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3617,c_47])).

cnf(c_4142,plain,
    ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_4141])).

cnf(c_8287,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | r2_hidden(X0,sK3) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_8277,c_4142])).

cnf(c_2849,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(sK4,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1775,c_1783])).

cnf(c_4868,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK2)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2849,c_1770])).

cnf(c_5364,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4868,c_1782])).

cnf(c_8318,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8287,c_5364])).

cnf(c_8319,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_8318])).

cnf(c_8328,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) = k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
    inference(superposition,[status(thm)],[c_5200,c_8319])).

cnf(c_32,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X5,X4))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_600,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X5)))
    | ~ r1_tarski(k2_relset_1(X1,X3,X2),k1_relset_1(X3,X5,X4))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X4)
    | v1_xboole_0(X3)
    | k1_funct_1(k8_funct_2(X1,X3,X5,X2,X4),X0) = k1_funct_1(X4,k1_funct_1(X2,X0))
    | sK5 != X2
    | sK4 != X3
    | sK3 != X1
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_40])).

cnf(c_601,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
    | ~ m1_subset_1(X2,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X1,X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK4)
    | k1_funct_1(k8_funct_2(sK3,sK4,X1,sK5,X0),X2) = k1_funct_1(X0,k1_funct_1(sK5,X2))
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_600])).

cnf(c_605,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,X1,sK5,X0),X2) = k1_funct_1(X0,k1_funct_1(sK5,X2))
    | ~ v1_funct_1(X0)
    | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
    | ~ m1_subset_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_601,c_42,c_41,c_39,c_34])).

cnf(c_606,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
    | ~ m1_subset_1(X2,sK3)
    | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X1,X0))
    | ~ v1_funct_1(X0)
    | k1_funct_1(k8_funct_2(sK3,sK4,X1,sK5,X0),X2) = k1_funct_1(X0,k1_funct_1(sK5,X2)) ),
    inference(renaming,[status(thm)],[c_605])).

cnf(c_1765,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,X0,sK5,X1),X2) = k1_funct_1(X1,k1_funct_1(sK5,X2))
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
    | m1_subset_1(X2,sK3) != iProver_top
    | r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X0,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_606])).

cnf(c_2358,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | m1_subset_1(X0,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1777,c_1765])).

cnf(c_48,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_2422,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | m1_subset_1(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2358,c_47,c_48])).

cnf(c_2430,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) = k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
    inference(superposition,[status(thm)],[c_1776,c_2422])).

cnf(c_33,negated_conjecture,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_2432,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
    inference(demodulation,[status(thm)],[c_2430,c_33])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8328,c_2432])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:40:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.10/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/0.99  
% 3.10/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.10/0.99  
% 3.10/0.99  ------  iProver source info
% 3.10/0.99  
% 3.10/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.10/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.10/0.99  git: non_committed_changes: false
% 3.10/0.99  git: last_make_outside_of_git: false
% 3.10/0.99  
% 3.10/0.99  ------ 
% 3.10/0.99  
% 3.10/0.99  ------ Input Options
% 3.10/0.99  
% 3.10/0.99  --out_options                           all
% 3.10/0.99  --tptp_safe_out                         true
% 3.10/0.99  --problem_path                          ""
% 3.10/0.99  --include_path                          ""
% 3.10/0.99  --clausifier                            res/vclausify_rel
% 3.10/0.99  --clausifier_options                    --mode clausify
% 3.10/0.99  --stdin                                 false
% 3.10/0.99  --stats_out                             all
% 3.10/0.99  
% 3.10/0.99  ------ General Options
% 3.10/0.99  
% 3.10/0.99  --fof                                   false
% 3.10/0.99  --time_out_real                         305.
% 3.10/0.99  --time_out_virtual                      -1.
% 3.10/0.99  --symbol_type_check                     false
% 3.10/0.99  --clausify_out                          false
% 3.10/0.99  --sig_cnt_out                           false
% 3.10/0.99  --trig_cnt_out                          false
% 3.10/0.99  --trig_cnt_out_tolerance                1.
% 3.10/0.99  --trig_cnt_out_sk_spl                   false
% 3.10/0.99  --abstr_cl_out                          false
% 3.10/0.99  
% 3.10/0.99  ------ Global Options
% 3.10/0.99  
% 3.10/0.99  --schedule                              default
% 3.10/0.99  --add_important_lit                     false
% 3.10/0.99  --prop_solver_per_cl                    1000
% 3.10/0.99  --min_unsat_core                        false
% 3.10/0.99  --soft_assumptions                      false
% 3.10/0.99  --soft_lemma_size                       3
% 3.10/0.99  --prop_impl_unit_size                   0
% 3.10/0.99  --prop_impl_unit                        []
% 3.10/0.99  --share_sel_clauses                     true
% 3.10/0.99  --reset_solvers                         false
% 3.10/0.99  --bc_imp_inh                            [conj_cone]
% 3.10/0.99  --conj_cone_tolerance                   3.
% 3.10/0.99  --extra_neg_conj                        none
% 3.10/0.99  --large_theory_mode                     true
% 3.10/0.99  --prolific_symb_bound                   200
% 3.10/0.99  --lt_threshold                          2000
% 3.10/0.99  --clause_weak_htbl                      true
% 3.10/0.99  --gc_record_bc_elim                     false
% 3.10/0.99  
% 3.10/0.99  ------ Preprocessing Options
% 3.10/0.99  
% 3.10/0.99  --preprocessing_flag                    true
% 3.10/0.99  --time_out_prep_mult                    0.1
% 3.10/0.99  --splitting_mode                        input
% 3.10/0.99  --splitting_grd                         true
% 3.10/0.99  --splitting_cvd                         false
% 3.10/0.99  --splitting_cvd_svl                     false
% 3.10/0.99  --splitting_nvd                         32
% 3.10/0.99  --sub_typing                            true
% 3.10/0.99  --prep_gs_sim                           true
% 3.10/0.99  --prep_unflatten                        true
% 3.10/0.99  --prep_res_sim                          true
% 3.10/0.99  --prep_upred                            true
% 3.10/0.99  --prep_sem_filter                       exhaustive
% 3.10/0.99  --prep_sem_filter_out                   false
% 3.10/0.99  --pred_elim                             true
% 3.10/0.99  --res_sim_input                         true
% 3.10/0.99  --eq_ax_congr_red                       true
% 3.10/0.99  --pure_diseq_elim                       true
% 3.10/0.99  --brand_transform                       false
% 3.10/0.99  --non_eq_to_eq                          false
% 3.10/0.99  --prep_def_merge                        true
% 3.10/0.99  --prep_def_merge_prop_impl              false
% 3.10/0.99  --prep_def_merge_mbd                    true
% 3.10/0.99  --prep_def_merge_tr_red                 false
% 3.10/0.99  --prep_def_merge_tr_cl                  false
% 3.10/0.99  --smt_preprocessing                     true
% 3.10/0.99  --smt_ac_axioms                         fast
% 3.10/0.99  --preprocessed_out                      false
% 3.10/0.99  --preprocessed_stats                    false
% 3.10/0.99  
% 3.10/0.99  ------ Abstraction refinement Options
% 3.10/0.99  
% 3.10/0.99  --abstr_ref                             []
% 3.10/0.99  --abstr_ref_prep                        false
% 3.10/0.99  --abstr_ref_until_sat                   false
% 3.10/0.99  --abstr_ref_sig_restrict                funpre
% 3.10/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.10/0.99  --abstr_ref_under                       []
% 3.10/0.99  
% 3.10/0.99  ------ SAT Options
% 3.10/0.99  
% 3.10/0.99  --sat_mode                              false
% 3.10/0.99  --sat_fm_restart_options                ""
% 3.10/0.99  --sat_gr_def                            false
% 3.10/0.99  --sat_epr_types                         true
% 3.10/0.99  --sat_non_cyclic_types                  false
% 3.10/0.99  --sat_finite_models                     false
% 3.10/0.99  --sat_fm_lemmas                         false
% 3.10/0.99  --sat_fm_prep                           false
% 3.10/0.99  --sat_fm_uc_incr                        true
% 3.10/0.99  --sat_out_model                         small
% 3.10/0.99  --sat_out_clauses                       false
% 3.10/0.99  
% 3.10/0.99  ------ QBF Options
% 3.10/0.99  
% 3.10/0.99  --qbf_mode                              false
% 3.10/0.99  --qbf_elim_univ                         false
% 3.10/0.99  --qbf_dom_inst                          none
% 3.10/0.99  --qbf_dom_pre_inst                      false
% 3.10/0.99  --qbf_sk_in                             false
% 3.10/0.99  --qbf_pred_elim                         true
% 3.10/0.99  --qbf_split                             512
% 3.10/0.99  
% 3.10/0.99  ------ BMC1 Options
% 3.10/0.99  
% 3.10/0.99  --bmc1_incremental                      false
% 3.10/0.99  --bmc1_axioms                           reachable_all
% 3.10/0.99  --bmc1_min_bound                        0
% 3.10/0.99  --bmc1_max_bound                        -1
% 3.10/0.99  --bmc1_max_bound_default                -1
% 3.10/0.99  --bmc1_symbol_reachability              true
% 3.10/0.99  --bmc1_property_lemmas                  false
% 3.10/0.99  --bmc1_k_induction                      false
% 3.10/0.99  --bmc1_non_equiv_states                 false
% 3.10/0.99  --bmc1_deadlock                         false
% 3.10/0.99  --bmc1_ucm                              false
% 3.10/0.99  --bmc1_add_unsat_core                   none
% 3.10/0.99  --bmc1_unsat_core_children              false
% 3.10/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.10/0.99  --bmc1_out_stat                         full
% 3.10/0.99  --bmc1_ground_init                      false
% 3.10/0.99  --bmc1_pre_inst_next_state              false
% 3.10/0.99  --bmc1_pre_inst_state                   false
% 3.10/0.99  --bmc1_pre_inst_reach_state             false
% 3.10/0.99  --bmc1_out_unsat_core                   false
% 3.10/0.99  --bmc1_aig_witness_out                  false
% 3.10/0.99  --bmc1_verbose                          false
% 3.10/0.99  --bmc1_dump_clauses_tptp                false
% 3.10/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.10/0.99  --bmc1_dump_file                        -
% 3.10/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.10/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.10/0.99  --bmc1_ucm_extend_mode                  1
% 3.10/0.99  --bmc1_ucm_init_mode                    2
% 3.10/0.99  --bmc1_ucm_cone_mode                    none
% 3.10/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.10/0.99  --bmc1_ucm_relax_model                  4
% 3.10/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.10/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.10/0.99  --bmc1_ucm_layered_model                none
% 3.10/0.99  --bmc1_ucm_max_lemma_size               10
% 3.10/0.99  
% 3.10/0.99  ------ AIG Options
% 3.10/0.99  
% 3.10/0.99  --aig_mode                              false
% 3.10/0.99  
% 3.10/0.99  ------ Instantiation Options
% 3.10/0.99  
% 3.10/0.99  --instantiation_flag                    true
% 3.10/0.99  --inst_sos_flag                         false
% 3.10/0.99  --inst_sos_phase                        true
% 3.10/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.10/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.10/0.99  --inst_lit_sel_side                     num_symb
% 3.10/0.99  --inst_solver_per_active                1400
% 3.10/0.99  --inst_solver_calls_frac                1.
% 3.10/0.99  --inst_passive_queue_type               priority_queues
% 3.10/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.10/0.99  --inst_passive_queues_freq              [25;2]
% 3.10/0.99  --inst_dismatching                      true
% 3.10/0.99  --inst_eager_unprocessed_to_passive     true
% 3.10/0.99  --inst_prop_sim_given                   true
% 3.10/0.99  --inst_prop_sim_new                     false
% 3.10/0.99  --inst_subs_new                         false
% 3.10/0.99  --inst_eq_res_simp                      false
% 3.10/0.99  --inst_subs_given                       false
% 3.10/0.99  --inst_orphan_elimination               true
% 3.10/0.99  --inst_learning_loop_flag               true
% 3.10/0.99  --inst_learning_start                   3000
% 3.10/0.99  --inst_learning_factor                  2
% 3.10/0.99  --inst_start_prop_sim_after_learn       3
% 3.10/0.99  --inst_sel_renew                        solver
% 3.10/0.99  --inst_lit_activity_flag                true
% 3.10/0.99  --inst_restr_to_given                   false
% 3.10/0.99  --inst_activity_threshold               500
% 3.10/0.99  --inst_out_proof                        true
% 3.10/0.99  
% 3.10/0.99  ------ Resolution Options
% 3.10/0.99  
% 3.10/0.99  --resolution_flag                       true
% 3.10/0.99  --res_lit_sel                           adaptive
% 3.10/0.99  --res_lit_sel_side                      none
% 3.10/0.99  --res_ordering                          kbo
% 3.10/0.99  --res_to_prop_solver                    active
% 3.10/0.99  --res_prop_simpl_new                    false
% 3.10/0.99  --res_prop_simpl_given                  true
% 3.10/0.99  --res_passive_queue_type                priority_queues
% 3.10/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.10/0.99  --res_passive_queues_freq               [15;5]
% 3.10/0.99  --res_forward_subs                      full
% 3.10/0.99  --res_backward_subs                     full
% 3.10/0.99  --res_forward_subs_resolution           true
% 3.10/0.99  --res_backward_subs_resolution          true
% 3.10/0.99  --res_orphan_elimination                true
% 3.10/0.99  --res_time_limit                        2.
% 3.10/0.99  --res_out_proof                         true
% 3.10/0.99  
% 3.10/0.99  ------ Superposition Options
% 3.10/0.99  
% 3.10/0.99  --superposition_flag                    true
% 3.10/0.99  --sup_passive_queue_type                priority_queues
% 3.10/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.10/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.10/0.99  --demod_completeness_check              fast
% 3.10/0.99  --demod_use_ground                      true
% 3.10/0.99  --sup_to_prop_solver                    passive
% 3.10/0.99  --sup_prop_simpl_new                    true
% 3.10/0.99  --sup_prop_simpl_given                  true
% 3.10/0.99  --sup_fun_splitting                     false
% 3.10/0.99  --sup_smt_interval                      50000
% 3.10/0.99  
% 3.10/0.99  ------ Superposition Simplification Setup
% 3.10/0.99  
% 3.10/0.99  --sup_indices_passive                   []
% 3.10/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.10/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.99  --sup_full_bw                           [BwDemod]
% 3.10/0.99  --sup_immed_triv                        [TrivRules]
% 3.10/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.10/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.99  --sup_immed_bw_main                     []
% 3.10/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.10/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/0.99  
% 3.10/0.99  ------ Combination Options
% 3.10/0.99  
% 3.10/0.99  --comb_res_mult                         3
% 3.10/0.99  --comb_sup_mult                         2
% 3.10/0.99  --comb_inst_mult                        10
% 3.10/0.99  
% 3.10/0.99  ------ Debug Options
% 3.10/0.99  
% 3.10/0.99  --dbg_backtrace                         false
% 3.10/0.99  --dbg_dump_prop_clauses                 false
% 3.10/0.99  --dbg_dump_prop_clauses_file            -
% 3.10/0.99  --dbg_out_stat                          false
% 3.10/0.99  ------ Parsing...
% 3.10/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.10/0.99  
% 3.10/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.10/0.99  
% 3.10/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.10/0.99  
% 3.10/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.10/0.99  ------ Proving...
% 3.10/0.99  ------ Problem Properties 
% 3.10/0.99  
% 3.10/0.99  
% 3.10/0.99  clauses                                 37
% 3.10/0.99  conjectures                             9
% 3.10/0.99  EPR                                     14
% 3.10/0.99  Horn                                    30
% 3.10/0.99  unary                                   14
% 3.10/0.99  binary                                  11
% 3.10/0.99  lits                                    88
% 3.10/0.99  lits eq                                 24
% 3.10/0.99  fd_pure                                 0
% 3.10/0.99  fd_pseudo                               0
% 3.10/0.99  fd_cond                                 3
% 3.10/0.99  fd_pseudo_cond                          1
% 3.10/0.99  AC symbols                              0
% 3.10/0.99  
% 3.10/0.99  ------ Schedule dynamic 5 is on 
% 3.10/0.99  
% 3.10/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.10/0.99  
% 3.10/0.99  
% 3.10/0.99  ------ 
% 3.10/0.99  Current options:
% 3.10/0.99  ------ 
% 3.10/0.99  
% 3.10/0.99  ------ Input Options
% 3.10/0.99  
% 3.10/0.99  --out_options                           all
% 3.10/0.99  --tptp_safe_out                         true
% 3.10/0.99  --problem_path                          ""
% 3.10/0.99  --include_path                          ""
% 3.10/0.99  --clausifier                            res/vclausify_rel
% 3.10/0.99  --clausifier_options                    --mode clausify
% 3.10/0.99  --stdin                                 false
% 3.10/0.99  --stats_out                             all
% 3.10/0.99  
% 3.10/0.99  ------ General Options
% 3.10/0.99  
% 3.10/0.99  --fof                                   false
% 3.10/0.99  --time_out_real                         305.
% 3.10/0.99  --time_out_virtual                      -1.
% 3.10/0.99  --symbol_type_check                     false
% 3.10/0.99  --clausify_out                          false
% 3.10/0.99  --sig_cnt_out                           false
% 3.10/0.99  --trig_cnt_out                          false
% 3.10/0.99  --trig_cnt_out_tolerance                1.
% 3.10/0.99  --trig_cnt_out_sk_spl                   false
% 3.10/0.99  --abstr_cl_out                          false
% 3.10/0.99  
% 3.10/0.99  ------ Global Options
% 3.10/0.99  
% 3.10/0.99  --schedule                              default
% 3.10/0.99  --add_important_lit                     false
% 3.10/0.99  --prop_solver_per_cl                    1000
% 3.10/0.99  --min_unsat_core                        false
% 3.10/0.99  --soft_assumptions                      false
% 3.10/0.99  --soft_lemma_size                       3
% 3.10/0.99  --prop_impl_unit_size                   0
% 3.10/0.99  --prop_impl_unit                        []
% 3.10/0.99  --share_sel_clauses                     true
% 3.10/0.99  --reset_solvers                         false
% 3.10/0.99  --bc_imp_inh                            [conj_cone]
% 3.10/0.99  --conj_cone_tolerance                   3.
% 3.10/0.99  --extra_neg_conj                        none
% 3.10/0.99  --large_theory_mode                     true
% 3.10/0.99  --prolific_symb_bound                   200
% 3.10/0.99  --lt_threshold                          2000
% 3.10/0.99  --clause_weak_htbl                      true
% 3.10/0.99  --gc_record_bc_elim                     false
% 3.10/0.99  
% 3.10/0.99  ------ Preprocessing Options
% 3.10/0.99  
% 3.10/0.99  --preprocessing_flag                    true
% 3.10/0.99  --time_out_prep_mult                    0.1
% 3.10/0.99  --splitting_mode                        input
% 3.10/0.99  --splitting_grd                         true
% 3.10/0.99  --splitting_cvd                         false
% 3.10/0.99  --splitting_cvd_svl                     false
% 3.10/0.99  --splitting_nvd                         32
% 3.10/0.99  --sub_typing                            true
% 3.10/0.99  --prep_gs_sim                           true
% 3.10/0.99  --prep_unflatten                        true
% 3.10/0.99  --prep_res_sim                          true
% 3.10/0.99  --prep_upred                            true
% 3.10/0.99  --prep_sem_filter                       exhaustive
% 3.10/0.99  --prep_sem_filter_out                   false
% 3.10/0.99  --pred_elim                             true
% 3.10/0.99  --res_sim_input                         true
% 3.10/0.99  --eq_ax_congr_red                       true
% 3.10/0.99  --pure_diseq_elim                       true
% 3.10/0.99  --brand_transform                       false
% 3.10/0.99  --non_eq_to_eq                          false
% 3.10/0.99  --prep_def_merge                        true
% 3.10/0.99  --prep_def_merge_prop_impl              false
% 3.10/0.99  --prep_def_merge_mbd                    true
% 3.10/0.99  --prep_def_merge_tr_red                 false
% 3.10/0.99  --prep_def_merge_tr_cl                  false
% 3.10/0.99  --smt_preprocessing                     true
% 3.10/0.99  --smt_ac_axioms                         fast
% 3.10/0.99  --preprocessed_out                      false
% 3.10/0.99  --preprocessed_stats                    false
% 3.10/0.99  
% 3.10/0.99  ------ Abstraction refinement Options
% 3.10/0.99  
% 3.10/0.99  --abstr_ref                             []
% 3.10/0.99  --abstr_ref_prep                        false
% 3.10/0.99  --abstr_ref_until_sat                   false
% 3.10/0.99  --abstr_ref_sig_restrict                funpre
% 3.10/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.10/0.99  --abstr_ref_under                       []
% 3.10/0.99  
% 3.10/0.99  ------ SAT Options
% 3.10/0.99  
% 3.10/0.99  --sat_mode                              false
% 3.10/0.99  --sat_fm_restart_options                ""
% 3.10/0.99  --sat_gr_def                            false
% 3.10/0.99  --sat_epr_types                         true
% 3.10/0.99  --sat_non_cyclic_types                  false
% 3.10/0.99  --sat_finite_models                     false
% 3.10/0.99  --sat_fm_lemmas                         false
% 3.10/0.99  --sat_fm_prep                           false
% 3.10/0.99  --sat_fm_uc_incr                        true
% 3.10/0.99  --sat_out_model                         small
% 3.10/0.99  --sat_out_clauses                       false
% 3.10/0.99  
% 3.10/0.99  ------ QBF Options
% 3.10/0.99  
% 3.10/0.99  --qbf_mode                              false
% 3.10/0.99  --qbf_elim_univ                         false
% 3.10/0.99  --qbf_dom_inst                          none
% 3.10/0.99  --qbf_dom_pre_inst                      false
% 3.10/0.99  --qbf_sk_in                             false
% 3.10/0.99  --qbf_pred_elim                         true
% 3.10/0.99  --qbf_split                             512
% 3.10/0.99  
% 3.10/0.99  ------ BMC1 Options
% 3.10/0.99  
% 3.10/0.99  --bmc1_incremental                      false
% 3.10/0.99  --bmc1_axioms                           reachable_all
% 3.10/0.99  --bmc1_min_bound                        0
% 3.10/0.99  --bmc1_max_bound                        -1
% 3.10/0.99  --bmc1_max_bound_default                -1
% 3.10/0.99  --bmc1_symbol_reachability              true
% 3.10/0.99  --bmc1_property_lemmas                  false
% 3.10/0.99  --bmc1_k_induction                      false
% 3.10/0.99  --bmc1_non_equiv_states                 false
% 3.10/0.99  --bmc1_deadlock                         false
% 3.10/0.99  --bmc1_ucm                              false
% 3.10/0.99  --bmc1_add_unsat_core                   none
% 3.10/0.99  --bmc1_unsat_core_children              false
% 3.10/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.10/0.99  --bmc1_out_stat                         full
% 3.10/0.99  --bmc1_ground_init                      false
% 3.10/0.99  --bmc1_pre_inst_next_state              false
% 3.10/0.99  --bmc1_pre_inst_state                   false
% 3.10/0.99  --bmc1_pre_inst_reach_state             false
% 3.10/0.99  --bmc1_out_unsat_core                   false
% 3.10/0.99  --bmc1_aig_witness_out                  false
% 3.10/0.99  --bmc1_verbose                          false
% 3.10/0.99  --bmc1_dump_clauses_tptp                false
% 3.10/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.10/0.99  --bmc1_dump_file                        -
% 3.10/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.10/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.10/0.99  --bmc1_ucm_extend_mode                  1
% 3.10/0.99  --bmc1_ucm_init_mode                    2
% 3.10/0.99  --bmc1_ucm_cone_mode                    none
% 3.10/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.10/0.99  --bmc1_ucm_relax_model                  4
% 3.10/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.10/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.10/0.99  --bmc1_ucm_layered_model                none
% 3.10/0.99  --bmc1_ucm_max_lemma_size               10
% 3.10/0.99  
% 3.10/0.99  ------ AIG Options
% 3.10/0.99  
% 3.10/0.99  --aig_mode                              false
% 3.10/0.99  
% 3.10/0.99  ------ Instantiation Options
% 3.10/0.99  
% 3.10/0.99  --instantiation_flag                    true
% 3.10/0.99  --inst_sos_flag                         false
% 3.10/0.99  --inst_sos_phase                        true
% 3.10/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.10/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.10/0.99  --inst_lit_sel_side                     none
% 3.10/0.99  --inst_solver_per_active                1400
% 3.10/0.99  --inst_solver_calls_frac                1.
% 3.10/0.99  --inst_passive_queue_type               priority_queues
% 3.10/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.10/0.99  --inst_passive_queues_freq              [25;2]
% 3.10/0.99  --inst_dismatching                      true
% 3.10/0.99  --inst_eager_unprocessed_to_passive     true
% 3.10/0.99  --inst_prop_sim_given                   true
% 3.10/0.99  --inst_prop_sim_new                     false
% 3.10/0.99  --inst_subs_new                         false
% 3.10/0.99  --inst_eq_res_simp                      false
% 3.10/0.99  --inst_subs_given                       false
% 3.10/0.99  --inst_orphan_elimination               true
% 3.10/0.99  --inst_learning_loop_flag               true
% 3.10/0.99  --inst_learning_start                   3000
% 3.10/0.99  --inst_learning_factor                  2
% 3.10/0.99  --inst_start_prop_sim_after_learn       3
% 3.10/0.99  --inst_sel_renew                        solver
% 3.10/0.99  --inst_lit_activity_flag                true
% 3.10/0.99  --inst_restr_to_given                   false
% 3.10/0.99  --inst_activity_threshold               500
% 3.10/0.99  --inst_out_proof                        true
% 3.10/0.99  
% 3.10/0.99  ------ Resolution Options
% 3.10/0.99  
% 3.10/0.99  --resolution_flag                       false
% 3.10/0.99  --res_lit_sel                           adaptive
% 3.10/0.99  --res_lit_sel_side                      none
% 3.10/0.99  --res_ordering                          kbo
% 3.10/0.99  --res_to_prop_solver                    active
% 3.10/0.99  --res_prop_simpl_new                    false
% 3.10/0.99  --res_prop_simpl_given                  true
% 3.10/0.99  --res_passive_queue_type                priority_queues
% 3.10/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.10/0.99  --res_passive_queues_freq               [15;5]
% 3.10/0.99  --res_forward_subs                      full
% 3.10/0.99  --res_backward_subs                     full
% 3.10/0.99  --res_forward_subs_resolution           true
% 3.10/0.99  --res_backward_subs_resolution          true
% 3.10/0.99  --res_orphan_elimination                true
% 3.10/0.99  --res_time_limit                        2.
% 3.10/0.99  --res_out_proof                         true
% 3.10/0.99  
% 3.10/0.99  ------ Superposition Options
% 3.10/0.99  
% 3.10/0.99  --superposition_flag                    true
% 3.10/0.99  --sup_passive_queue_type                priority_queues
% 3.10/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.10/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.10/0.99  --demod_completeness_check              fast
% 3.10/0.99  --demod_use_ground                      true
% 3.10/0.99  --sup_to_prop_solver                    passive
% 3.10/0.99  --sup_prop_simpl_new                    true
% 3.10/0.99  --sup_prop_simpl_given                  true
% 3.10/0.99  --sup_fun_splitting                     false
% 3.10/0.99  --sup_smt_interval                      50000
% 3.10/0.99  
% 3.10/0.99  ------ Superposition Simplification Setup
% 3.10/0.99  
% 3.10/0.99  --sup_indices_passive                   []
% 3.10/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.10/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.99  --sup_full_bw                           [BwDemod]
% 3.10/0.99  --sup_immed_triv                        [TrivRules]
% 3.10/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.10/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.99  --sup_immed_bw_main                     []
% 3.10/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.10/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/0.99  
% 3.10/0.99  ------ Combination Options
% 3.10/0.99  
% 3.10/0.99  --comb_res_mult                         3
% 3.10/0.99  --comb_sup_mult                         2
% 3.10/0.99  --comb_inst_mult                        10
% 3.10/0.99  
% 3.10/0.99  ------ Debug Options
% 3.10/0.99  
% 3.10/0.99  --dbg_backtrace                         false
% 3.10/0.99  --dbg_dump_prop_clauses                 false
% 3.10/0.99  --dbg_dump_prop_clauses_file            -
% 3.10/0.99  --dbg_out_stat                          false
% 3.10/0.99  
% 3.10/0.99  
% 3.10/0.99  
% 3.10/0.99  
% 3.10/0.99  ------ Proving...
% 3.10/0.99  
% 3.10/0.99  
% 3.10/0.99  % SZS status Theorem for theBenchmark.p
% 3.10/0.99  
% 3.10/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.10/0.99  
% 3.10/0.99  fof(f19,conjecture,(
% 3.10/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 3.10/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f20,negated_conjecture,(
% 3.10/0.99    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 3.10/0.99    inference(negated_conjecture,[],[f19])).
% 3.10/0.99  
% 3.10/0.99  fof(f40,plain,(
% 3.10/0.99    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 3.10/0.99    inference(ennf_transformation,[],[f20])).
% 3.10/0.99  
% 3.10/0.99  fof(f41,plain,(
% 3.10/0.99    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 3.10/0.99    inference(flattening,[],[f40])).
% 3.10/0.99  
% 3.10/0.99  fof(f59,plain,(
% 3.10/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK7) != k7_partfun1(X0,X4,k1_funct_1(X3,sK7)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK7,X1))) )),
% 3.10/0.99    introduced(choice_axiom,[])).
% 3.10/0.99  
% 3.10/0.99  fof(f58,plain,(
% 3.10/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK6),X5) != k7_partfun1(X0,sK6,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK6)) & m1_subset_1(X5,X1)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK6))) )),
% 3.10/0.99    introduced(choice_axiom,[])).
% 3.10/0.99  
% 3.10/0.99  fof(f57,plain,(
% 3.10/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,sK5,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(sK5,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK5),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK5,X1,X2) & v1_funct_1(sK5))) )),
% 3.10/0.99    introduced(choice_axiom,[])).
% 3.10/0.99  
% 3.10/0.99  fof(f56,plain,(
% 3.10/0.99    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK3,sK4,sK2,X3,X4),X5) != k7_partfun1(sK2,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK3 & r1_tarski(k2_relset_1(sK3,sK4,X3),k1_relset_1(sK4,sK2,X4)) & m1_subset_1(X5,sK3)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) & ~v1_xboole_0(sK4))),
% 3.10/0.99    introduced(choice_axiom,[])).
% 3.10/0.99  
% 3.10/0.99  fof(f60,plain,(
% 3.10/0.99    (((k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) & k1_xboole_0 != sK3 & r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) & m1_subset_1(sK7,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)) & ~v1_xboole_0(sK4)),
% 3.10/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f41,f59,f58,f57,f56])).
% 3.10/0.99  
% 3.10/0.99  fof(f100,plain,(
% 3.10/0.99    m1_subset_1(sK7,sK3)),
% 3.10/0.99    inference(cnf_transformation,[],[f60])).
% 3.10/0.99  
% 3.10/0.99  fof(f6,axiom,(
% 3.10/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.10/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f23,plain,(
% 3.10/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.10/0.99    inference(ennf_transformation,[],[f6])).
% 3.10/0.99  
% 3.10/0.99  fof(f24,plain,(
% 3.10/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.10/0.99    inference(flattening,[],[f23])).
% 3.10/0.99  
% 3.10/0.99  fof(f73,plain,(
% 3.10/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.10/0.99    inference(cnf_transformation,[],[f24])).
% 3.10/0.99  
% 3.10/0.99  fof(f102,plain,(
% 3.10/0.99    k1_xboole_0 != sK3),
% 3.10/0.99    inference(cnf_transformation,[],[f60])).
% 3.10/0.99  
% 3.10/0.99  fof(f3,axiom,(
% 3.10/0.99    v1_xboole_0(k1_xboole_0)),
% 3.10/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f66,plain,(
% 3.10/0.99    v1_xboole_0(k1_xboole_0)),
% 3.10/0.99    inference(cnf_transformation,[],[f3])).
% 3.10/0.99  
% 3.10/0.99  fof(f4,axiom,(
% 3.10/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.10/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f50,plain,(
% 3.10/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.10/0.99    inference(nnf_transformation,[],[f4])).
% 3.10/0.99  
% 3.10/0.99  fof(f51,plain,(
% 3.10/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.10/0.99    inference(flattening,[],[f50])).
% 3.10/0.99  
% 3.10/0.99  fof(f69,plain,(
% 3.10/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.10/0.99    inference(cnf_transformation,[],[f51])).
% 3.10/0.99  
% 3.10/0.99  fof(f2,axiom,(
% 3.10/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.10/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f22,plain,(
% 3.10/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.10/0.99    inference(ennf_transformation,[],[f2])).
% 3.10/0.99  
% 3.10/0.99  fof(f46,plain,(
% 3.10/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.10/0.99    inference(nnf_transformation,[],[f22])).
% 3.10/0.99  
% 3.10/0.99  fof(f47,plain,(
% 3.10/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.10/0.99    inference(rectify,[],[f46])).
% 3.10/0.99  
% 3.10/0.99  fof(f48,plain,(
% 3.10/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.10/0.99    introduced(choice_axiom,[])).
% 3.10/0.99  
% 3.10/0.99  fof(f49,plain,(
% 3.10/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.10/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f47,f48])).
% 3.10/0.99  
% 3.10/0.99  fof(f64,plain,(
% 3.10/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.10/0.99    inference(cnf_transformation,[],[f49])).
% 3.10/0.99  
% 3.10/0.99  fof(f1,axiom,(
% 3.10/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.10/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f42,plain,(
% 3.10/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.10/0.99    inference(nnf_transformation,[],[f1])).
% 3.10/0.99  
% 3.10/0.99  fof(f43,plain,(
% 3.10/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.10/0.99    inference(rectify,[],[f42])).
% 3.10/0.99  
% 3.10/0.99  fof(f44,plain,(
% 3.10/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.10/0.99    introduced(choice_axiom,[])).
% 3.10/0.99  
% 3.10/0.99  fof(f45,plain,(
% 3.10/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.10/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).
% 3.10/0.99  
% 3.10/0.99  fof(f61,plain,(
% 3.10/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.10/0.99    inference(cnf_transformation,[],[f45])).
% 3.10/0.99  
% 3.10/0.99  fof(f11,axiom,(
% 3.10/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 3.10/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f27,plain,(
% 3.10/0.99    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.10/0.99    inference(ennf_transformation,[],[f11])).
% 3.10/0.99  
% 3.10/0.99  fof(f28,plain,(
% 3.10/0.99    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.10/0.99    inference(flattening,[],[f27])).
% 3.10/0.99  
% 3.10/0.99  fof(f79,plain,(
% 3.10/0.99    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.10/0.99    inference(cnf_transformation,[],[f28])).
% 3.10/0.99  
% 3.10/0.99  fof(f99,plain,(
% 3.10/0.99    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))),
% 3.10/0.99    inference(cnf_transformation,[],[f60])).
% 3.10/0.99  
% 3.10/0.99  fof(f13,axiom,(
% 3.10/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.10/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f30,plain,(
% 3.10/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/0.99    inference(ennf_transformation,[],[f13])).
% 3.10/0.99  
% 3.10/0.99  fof(f81,plain,(
% 3.10/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.10/0.99    inference(cnf_transformation,[],[f30])).
% 3.10/0.99  
% 3.10/0.99  fof(f97,plain,(
% 3.10/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.10/0.99    inference(cnf_transformation,[],[f60])).
% 3.10/0.99  
% 3.10/0.99  fof(f14,axiom,(
% 3.10/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.10/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f31,plain,(
% 3.10/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/0.99    inference(ennf_transformation,[],[f14])).
% 3.10/0.99  
% 3.10/0.99  fof(f82,plain,(
% 3.10/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.10/0.99    inference(cnf_transformation,[],[f31])).
% 3.10/0.99  
% 3.10/0.99  fof(f101,plain,(
% 3.10/0.99    r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6))),
% 3.10/0.99    inference(cnf_transformation,[],[f60])).
% 3.10/0.99  
% 3.10/0.99  fof(f63,plain,(
% 3.10/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.10/0.99    inference(cnf_transformation,[],[f49])).
% 3.10/0.99  
% 3.10/0.99  fof(f16,axiom,(
% 3.10/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.10/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f34,plain,(
% 3.10/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/0.99    inference(ennf_transformation,[],[f16])).
% 3.10/0.99  
% 3.10/0.99  fof(f35,plain,(
% 3.10/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/0.99    inference(flattening,[],[f34])).
% 3.10/0.99  
% 3.10/0.99  fof(f55,plain,(
% 3.10/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/0.99    inference(nnf_transformation,[],[f35])).
% 3.10/0.99  
% 3.10/0.99  fof(f86,plain,(
% 3.10/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.10/0.99    inference(cnf_transformation,[],[f55])).
% 3.10/0.99  
% 3.10/0.99  fof(f96,plain,(
% 3.10/0.99    v1_funct_2(sK5,sK3,sK4)),
% 3.10/0.99    inference(cnf_transformation,[],[f60])).
% 3.10/0.99  
% 3.10/0.99  fof(f94,plain,(
% 3.10/0.99    ~v1_xboole_0(sK4)),
% 3.10/0.99    inference(cnf_transformation,[],[f60])).
% 3.10/0.99  
% 3.10/0.99  fof(f95,plain,(
% 3.10/0.99    v1_funct_1(sK5)),
% 3.10/0.99    inference(cnf_transformation,[],[f60])).
% 3.10/0.99  
% 3.10/0.99  fof(f7,axiom,(
% 3.10/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.10/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f54,plain,(
% 3.10/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.10/0.99    inference(nnf_transformation,[],[f7])).
% 3.10/0.99  
% 3.10/0.99  fof(f74,plain,(
% 3.10/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.10/0.99    inference(cnf_transformation,[],[f54])).
% 3.10/0.99  
% 3.10/0.99  fof(f8,axiom,(
% 3.10/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.10/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f25,plain,(
% 3.10/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.10/0.99    inference(ennf_transformation,[],[f8])).
% 3.10/0.99  
% 3.10/0.99  fof(f76,plain,(
% 3.10/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.10/0.99    inference(cnf_transformation,[],[f25])).
% 3.10/0.99  
% 3.10/0.99  fof(f75,plain,(
% 3.10/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.10/0.99    inference(cnf_transformation,[],[f54])).
% 3.10/0.99  
% 3.10/0.99  fof(f9,axiom,(
% 3.10/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.10/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f77,plain,(
% 3.10/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.10/0.99    inference(cnf_transformation,[],[f9])).
% 3.10/0.99  
% 3.10/0.99  fof(f12,axiom,(
% 3.10/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.10/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f21,plain,(
% 3.10/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.10/0.99    inference(pure_predicate_removal,[],[f12])).
% 3.10/0.99  
% 3.10/0.99  fof(f29,plain,(
% 3.10/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/0.99    inference(ennf_transformation,[],[f21])).
% 3.10/0.99  
% 3.10/0.99  fof(f80,plain,(
% 3.10/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.10/0.99    inference(cnf_transformation,[],[f29])).
% 3.10/0.99  
% 3.10/0.99  fof(f17,axiom,(
% 3.10/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)))),
% 3.10/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f36,plain,(
% 3.10/0.99    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.10/0.99    inference(ennf_transformation,[],[f17])).
% 3.10/0.99  
% 3.10/0.99  fof(f37,plain,(
% 3.10/0.99    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.10/0.99    inference(flattening,[],[f36])).
% 3.10/0.99  
% 3.10/0.99  fof(f92,plain,(
% 3.10/0.99    ( ! [X2,X0,X1] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.10/0.99    inference(cnf_transformation,[],[f37])).
% 3.10/0.99  
% 3.10/0.99  fof(f98,plain,(
% 3.10/0.99    v1_funct_1(sK6)),
% 3.10/0.99    inference(cnf_transformation,[],[f60])).
% 3.10/0.99  
% 3.10/0.99  fof(f18,axiom,(
% 3.10/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 3.10/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f38,plain,(
% 3.10/0.99    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 3.10/0.99    inference(ennf_transformation,[],[f18])).
% 3.10/0.99  
% 3.10/0.99  fof(f39,plain,(
% 3.10/0.99    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 3.10/0.99    inference(flattening,[],[f38])).
% 3.10/0.99  
% 3.10/0.99  fof(f93,plain,(
% 3.10/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 3.10/0.99    inference(cnf_transformation,[],[f39])).
% 3.10/0.99  
% 3.10/0.99  fof(f103,plain,(
% 3.10/0.99    k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7))),
% 3.10/0.99    inference(cnf_transformation,[],[f60])).
% 3.10/0.99  
% 3.10/0.99  cnf(c_36,negated_conjecture,
% 3.10/0.99      ( m1_subset_1(sK7,sK3) ),
% 3.10/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1776,plain,
% 3.10/0.99      ( m1_subset_1(sK7,sK3) = iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_12,plain,
% 3.10/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.10/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1785,plain,
% 3.10/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 3.10/0.99      | r2_hidden(X0,X1) = iProver_top
% 3.10/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_4980,plain,
% 3.10/0.99      ( r2_hidden(sK7,sK3) = iProver_top
% 3.10/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_1776,c_1785]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_34,negated_conjecture,
% 3.10/0.99      ( k1_xboole_0 != sK3 ),
% 3.10/0.99      inference(cnf_transformation,[],[f102]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_5,plain,
% 3.10/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.10/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_115,plain,
% 3.10/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_6,plain,
% 3.10/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.10/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2095,plain,
% 3.10/0.99      ( ~ r1_tarski(sK3,k1_xboole_0)
% 3.10/0.99      | ~ r1_tarski(k1_xboole_0,sK3)
% 3.10/0.99      | k1_xboole_0 = sK3 ),
% 3.10/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2096,plain,
% 3.10/0.99      ( k1_xboole_0 = sK3
% 3.10/0.99      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 3.10/0.99      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_2095]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_3,plain,
% 3.10/0.99      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 3.10/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2205,plain,
% 3.10/0.99      ( r1_tarski(sK3,k1_xboole_0)
% 3.10/0.99      | r2_hidden(sK1(sK3,k1_xboole_0),sK3) ),
% 3.10/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2206,plain,
% 3.10/0.99      ( r1_tarski(sK3,k1_xboole_0) = iProver_top
% 3.10/0.99      | r2_hidden(sK1(sK3,k1_xboole_0),sK3) = iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_2205]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2319,plain,
% 3.10/0.99      ( r1_tarski(k1_xboole_0,sK3)
% 3.10/0.99      | r2_hidden(sK1(k1_xboole_0,sK3),k1_xboole_0) ),
% 3.10/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2320,plain,
% 3.10/0.99      ( r1_tarski(k1_xboole_0,sK3) = iProver_top
% 3.10/0.99      | r2_hidden(sK1(k1_xboole_0,sK3),k1_xboole_0) = iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_2319]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1,plain,
% 3.10/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.10/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2863,plain,
% 3.10/0.99      ( ~ r2_hidden(sK1(sK3,k1_xboole_0),sK3) | ~ v1_xboole_0(sK3) ),
% 3.10/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2864,plain,
% 3.10/0.99      ( r2_hidden(sK1(sK3,k1_xboole_0),sK3) != iProver_top
% 3.10/0.99      | v1_xboole_0(sK3) != iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_2863]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_5011,plain,
% 3.10/0.99      ( ~ r2_hidden(sK1(k1_xboole_0,sK3),k1_xboole_0)
% 3.10/0.99      | ~ v1_xboole_0(k1_xboole_0) ),
% 3.10/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_5012,plain,
% 3.10/0.99      ( r2_hidden(sK1(k1_xboole_0,sK3),k1_xboole_0) != iProver_top
% 3.10/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_5011]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_5200,plain,
% 3.10/0.99      ( r2_hidden(sK7,sK3) = iProver_top ),
% 3.10/0.99      inference(global_propositional_subsumption,
% 3.10/0.99                [status(thm)],
% 3.10/0.99                [c_4980,c_34,c_115,c_2096,c_2206,c_2320,c_2864,c_5012]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_18,plain,
% 3.10/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.10/0.99      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.10/0.99      | ~ v1_funct_1(X1)
% 3.10/0.99      | ~ v1_relat_1(X1) ),
% 3.10/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1780,plain,
% 3.10/0.99      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 3.10/0.99      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 3.10/0.99      | v1_funct_1(X1) != iProver_top
% 3.10/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_37,negated_conjecture,
% 3.10/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
% 3.10/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1775,plain,
% 3.10/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_20,plain,
% 3.10/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.10/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1779,plain,
% 3.10/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.10/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_3759,plain,
% 3.10/0.99      ( k1_relset_1(sK4,sK2,sK6) = k1_relat_1(sK6) ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_1775,c_1779]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_39,negated_conjecture,
% 3.10/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.10/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1773,plain,
% 3.10/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_21,plain,
% 3.10/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.10/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1778,plain,
% 3.10/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.10/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_3119,plain,
% 3.10/0.99      ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_1773,c_1778]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_35,negated_conjecture,
% 3.10/0.99      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
% 3.10/0.99      inference(cnf_transformation,[],[f101]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1777,plain,
% 3.10/0.99      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_3256,plain,
% 3.10/0.99      ( r1_tarski(k2_relat_1(sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
% 3.10/0.99      inference(demodulation,[status(thm)],[c_3119,c_1777]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_3867,plain,
% 3.10/0.99      ( r1_tarski(k2_relat_1(sK5),k1_relat_1(sK6)) = iProver_top ),
% 3.10/0.99      inference(demodulation,[status(thm)],[c_3759,c_3256]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_4,plain,
% 3.10/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.10/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1789,plain,
% 3.10/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.10/0.99      | r2_hidden(X2,X0) != iProver_top
% 3.10/0.99      | r2_hidden(X2,X1) = iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_5089,plain,
% 3.10/0.99      ( r2_hidden(X0,k1_relat_1(sK6)) = iProver_top
% 3.10/0.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_3867,c_1789]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_8190,plain,
% 3.10/0.99      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 3.10/0.99      | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top
% 3.10/0.99      | v1_funct_1(sK5) != iProver_top
% 3.10/0.99      | v1_relat_1(sK5) != iProver_top ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_1780,c_5089]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_3760,plain,
% 3.10/0.99      ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_1773,c_1779]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_30,plain,
% 3.10/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.10/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.10/0.99      | k1_xboole_0 = X2 ),
% 3.10/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_40,negated_conjecture,
% 3.10/0.99      ( v1_funct_2(sK5,sK3,sK4) ),
% 3.10/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_627,plain,
% 3.10/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.10/0.99      | sK5 != X0
% 3.10/0.99      | sK4 != X2
% 3.10/0.99      | sK3 != X1
% 3.10/0.99      | k1_xboole_0 = X2 ),
% 3.10/0.99      inference(resolution_lifted,[status(thm)],[c_30,c_40]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_628,plain,
% 3.10/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.10/0.99      | k1_relset_1(sK3,sK4,sK5) = sK3
% 3.10/0.99      | k1_xboole_0 = sK4 ),
% 3.10/0.99      inference(unflattening,[status(thm)],[c_627]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_630,plain,
% 3.10/0.99      ( k1_relset_1(sK3,sK4,sK5) = sK3 | k1_xboole_0 = sK4 ),
% 3.10/0.99      inference(global_propositional_subsumption,
% 3.10/0.99                [status(thm)],
% 3.10/0.99                [c_628,c_39]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_4115,plain,
% 3.10/0.99      ( k1_relat_1(sK5) = sK3 | sK4 = k1_xboole_0 ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_3760,c_630]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_42,negated_conjecture,
% 3.10/0.99      ( ~ v1_xboole_0(sK4) ),
% 3.10/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_996,plain,
% 3.10/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.10/0.99      theory(equality) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2063,plain,
% 3.10/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK4) | sK4 != X0 ),
% 3.10/0.99      inference(instantiation,[status(thm)],[c_996]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2065,plain,
% 3.10/0.99      ( v1_xboole_0(sK4)
% 3.10/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 3.10/0.99      | sK4 != k1_xboole_0 ),
% 3.10/0.99      inference(instantiation,[status(thm)],[c_2063]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_4487,plain,
% 3.10/0.99      ( k1_relat_1(sK5) = sK3 ),
% 3.10/0.99      inference(global_propositional_subsumption,
% 3.10/0.99                [status(thm)],
% 3.10/0.99                [c_4115,c_42,c_5,c_2065]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_8195,plain,
% 3.10/0.99      ( r2_hidden(X0,sK3) != iProver_top
% 3.10/0.99      | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top
% 3.10/0.99      | v1_funct_1(sK5) != iProver_top
% 3.10/0.99      | v1_relat_1(sK5) != iProver_top ),
% 3.10/0.99      inference(light_normalisation,[status(thm)],[c_8190,c_4487]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_41,negated_conjecture,
% 3.10/0.99      ( v1_funct_1(sK5) ),
% 3.10/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_44,plain,
% 3.10/0.99      ( v1_funct_1(sK5) = iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_14,plain,
% 3.10/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.10/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1783,plain,
% 3.10/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.10/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2850,plain,
% 3.10/0.99      ( r1_tarski(sK5,k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_1773,c_1783]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_15,plain,
% 3.10/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.10/0.99      | ~ v1_relat_1(X1)
% 3.10/0.99      | v1_relat_1(X0) ),
% 3.10/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_13,plain,
% 3.10/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.10/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_286,plain,
% 3.10/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.10/0.99      inference(prop_impl,[status(thm)],[c_13]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_287,plain,
% 3.10/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.10/0.99      inference(renaming,[status(thm)],[c_286]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_362,plain,
% 3.10/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.10/0.99      inference(bin_hyper_res,[status(thm)],[c_15,c_287]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1770,plain,
% 3.10/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.10/0.99      | v1_relat_1(X1) != iProver_top
% 3.10/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_362]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_4869,plain,
% 3.10/0.99      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
% 3.10/0.99      | v1_relat_1(sK5) = iProver_top ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_2850,c_1770]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_16,plain,
% 3.10/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.10/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1782,plain,
% 3.10/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_5369,plain,
% 3.10/0.99      ( v1_relat_1(sK5) = iProver_top ),
% 3.10/0.99      inference(forward_subsumption_resolution,
% 3.10/0.99                [status(thm)],
% 3.10/0.99                [c_4869,c_1782]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_8277,plain,
% 3.10/0.99      ( r2_hidden(X0,sK3) != iProver_top
% 3.10/0.99      | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top ),
% 3.10/0.99      inference(global_propositional_subsumption,
% 3.10/0.99                [status(thm)],
% 3.10/0.99                [c_8195,c_44,c_5369]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_19,plain,
% 3.10/0.99      ( v5_relat_1(X0,X1)
% 3.10/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.10/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_31,plain,
% 3.10/0.99      ( ~ v5_relat_1(X0,X1)
% 3.10/0.99      | ~ r2_hidden(X2,k1_relat_1(X0))
% 3.10/0.99      | ~ v1_funct_1(X0)
% 3.10/0.99      | ~ v1_relat_1(X0)
% 3.10/0.99      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 3.10/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_485,plain,
% 3.10/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/0.99      | ~ r2_hidden(X3,k1_relat_1(X0))
% 3.10/0.99      | ~ v1_funct_1(X0)
% 3.10/0.99      | ~ v1_relat_1(X0)
% 3.10/0.99      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.10/0.99      inference(resolution,[status(thm)],[c_19,c_31]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1769,plain,
% 3.10/0.99      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
% 3.10/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
% 3.10/0.99      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 3.10/0.99      | v1_funct_1(X1) != iProver_top
% 3.10/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_485]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_3617,plain,
% 3.10/0.99      ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
% 3.10/0.99      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 3.10/0.99      | v1_funct_1(sK6) != iProver_top
% 3.10/0.99      | v1_relat_1(sK6) != iProver_top ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_1775,c_1769]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_38,negated_conjecture,
% 3.10/0.99      ( v1_funct_1(sK6) ),
% 3.10/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_47,plain,
% 3.10/0.99      ( v1_funct_1(sK6) = iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_4141,plain,
% 3.10/0.99      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 3.10/0.99      | k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
% 3.10/0.99      | v1_relat_1(sK6) != iProver_top ),
% 3.10/0.99      inference(global_propositional_subsumption,
% 3.10/0.99                [status(thm)],
% 3.10/0.99                [c_3617,c_47]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_4142,plain,
% 3.10/0.99      ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
% 3.10/0.99      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 3.10/0.99      | v1_relat_1(sK6) != iProver_top ),
% 3.10/0.99      inference(renaming,[status(thm)],[c_4141]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_8287,plain,
% 3.10/0.99      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 3.10/0.99      | r2_hidden(X0,sK3) != iProver_top
% 3.10/0.99      | v1_relat_1(sK6) != iProver_top ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_8277,c_4142]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2849,plain,
% 3.10/0.99      ( r1_tarski(sK6,k2_zfmisc_1(sK4,sK2)) = iProver_top ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_1775,c_1783]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_4868,plain,
% 3.10/0.99      ( v1_relat_1(k2_zfmisc_1(sK4,sK2)) != iProver_top
% 3.10/0.99      | v1_relat_1(sK6) = iProver_top ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_2849,c_1770]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_5364,plain,
% 3.10/0.99      ( v1_relat_1(sK6) = iProver_top ),
% 3.10/0.99      inference(forward_subsumption_resolution,
% 3.10/0.99                [status(thm)],
% 3.10/0.99                [c_4868,c_1782]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_8318,plain,
% 3.10/0.99      ( r2_hidden(X0,sK3) != iProver_top
% 3.10/0.99      | k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0)) ),
% 3.10/0.99      inference(global_propositional_subsumption,
% 3.10/0.99                [status(thm)],
% 3.10/0.99                [c_8287,c_5364]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_8319,plain,
% 3.10/0.99      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 3.10/0.99      | r2_hidden(X0,sK3) != iProver_top ),
% 3.10/0.99      inference(renaming,[status(thm)],[c_8318]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_8328,plain,
% 3.10/0.99      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) = k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_5200,c_8319]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_32,plain,
% 3.10/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.10/0.99      | ~ m1_subset_1(X3,X1)
% 3.10/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 3.10/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/0.99      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X5,X4))
% 3.10/0.99      | ~ v1_funct_1(X4)
% 3.10/0.99      | ~ v1_funct_1(X0)
% 3.10/0.99      | v1_xboole_0(X2)
% 3.10/0.99      | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 3.10/0.99      | k1_xboole_0 = X1 ),
% 3.10/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_600,plain,
% 3.10/0.99      ( ~ m1_subset_1(X0,X1)
% 3.10/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.10/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X5)))
% 3.10/0.99      | ~ r1_tarski(k2_relset_1(X1,X3,X2),k1_relset_1(X3,X5,X4))
% 3.10/0.99      | ~ v1_funct_1(X2)
% 3.10/0.99      | ~ v1_funct_1(X4)
% 3.10/0.99      | v1_xboole_0(X3)
% 3.10/0.99      | k1_funct_1(k8_funct_2(X1,X3,X5,X2,X4),X0) = k1_funct_1(X4,k1_funct_1(X2,X0))
% 3.10/0.99      | sK5 != X2
% 3.10/0.99      | sK4 != X3
% 3.10/0.99      | sK3 != X1
% 3.10/0.99      | k1_xboole_0 = X1 ),
% 3.10/0.99      inference(resolution_lifted,[status(thm)],[c_32,c_40]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_601,plain,
% 3.10/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
% 3.10/0.99      | ~ m1_subset_1(X2,sK3)
% 3.10/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.10/0.99      | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X1,X0))
% 3.10/0.99      | ~ v1_funct_1(X0)
% 3.10/0.99      | ~ v1_funct_1(sK5)
% 3.10/0.99      | v1_xboole_0(sK4)
% 3.10/0.99      | k1_funct_1(k8_funct_2(sK3,sK4,X1,sK5,X0),X2) = k1_funct_1(X0,k1_funct_1(sK5,X2))
% 3.10/0.99      | k1_xboole_0 = sK3 ),
% 3.10/0.99      inference(unflattening,[status(thm)],[c_600]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_605,plain,
% 3.10/0.99      ( k1_funct_1(k8_funct_2(sK3,sK4,X1,sK5,X0),X2) = k1_funct_1(X0,k1_funct_1(sK5,X2))
% 3.10/0.99      | ~ v1_funct_1(X0)
% 3.10/0.99      | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X1,X0))
% 3.10/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
% 3.10/0.99      | ~ m1_subset_1(X2,sK3) ),
% 3.10/0.99      inference(global_propositional_subsumption,
% 3.10/0.99                [status(thm)],
% 3.10/0.99                [c_601,c_42,c_41,c_39,c_34]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_606,plain,
% 3.10/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
% 3.10/0.99      | ~ m1_subset_1(X2,sK3)
% 3.10/0.99      | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X1,X0))
% 3.10/0.99      | ~ v1_funct_1(X0)
% 3.10/0.99      | k1_funct_1(k8_funct_2(sK3,sK4,X1,sK5,X0),X2) = k1_funct_1(X0,k1_funct_1(sK5,X2)) ),
% 3.10/0.99      inference(renaming,[status(thm)],[c_605]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1765,plain,
% 3.10/0.99      ( k1_funct_1(k8_funct_2(sK3,sK4,X0,sK5,X1),X2) = k1_funct_1(X1,k1_funct_1(sK5,X2))
% 3.10/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
% 3.10/0.99      | m1_subset_1(X2,sK3) != iProver_top
% 3.10/0.99      | r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X0,X1)) != iProver_top
% 3.10/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_606]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2358,plain,
% 3.10/0.99      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 3.10/0.99      | m1_subset_1(X0,sK3) != iProver_top
% 3.10/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 3.10/0.99      | v1_funct_1(sK6) != iProver_top ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_1777,c_1765]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_48,plain,
% 3.10/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2422,plain,
% 3.10/0.99      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 3.10/0.99      | m1_subset_1(X0,sK3) != iProver_top ),
% 3.10/0.99      inference(global_propositional_subsumption,
% 3.10/0.99                [status(thm)],
% 3.10/0.99                [c_2358,c_47,c_48]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2430,plain,
% 3.10/0.99      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) = k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_1776,c_2422]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_33,negated_conjecture,
% 3.10/0.99      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) ),
% 3.10/0.99      inference(cnf_transformation,[],[f103]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2432,plain,
% 3.10/0.99      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
% 3.10/0.99      inference(demodulation,[status(thm)],[c_2430,c_33]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(contradiction,plain,
% 3.10/0.99      ( $false ),
% 3.10/0.99      inference(minisat,[status(thm)],[c_8328,c_2432]) ).
% 3.10/0.99  
% 3.10/0.99  
% 3.10/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.10/0.99  
% 3.10/0.99  ------                               Statistics
% 3.10/0.99  
% 3.10/0.99  ------ General
% 3.10/0.99  
% 3.10/0.99  abstr_ref_over_cycles:                  0
% 3.10/0.99  abstr_ref_under_cycles:                 0
% 3.10/0.99  gc_basic_clause_elim:                   0
% 3.10/0.99  forced_gc_time:                         0
% 3.10/0.99  parsing_time:                           0.012
% 3.10/0.99  unif_index_cands_time:                  0.
% 3.10/0.99  unif_index_add_time:                    0.
% 3.10/0.99  orderings_time:                         0.
% 3.10/0.99  out_proof_time:                         0.011
% 3.10/0.99  total_time:                             0.249
% 3.10/0.99  num_of_symbols:                         57
% 3.10/0.99  num_of_terms:                           8025
% 3.10/0.99  
% 3.10/0.99  ------ Preprocessing
% 3.10/0.99  
% 3.10/0.99  num_of_splits:                          0
% 3.10/0.99  num_of_split_atoms:                     0
% 3.10/0.99  num_of_reused_defs:                     0
% 3.10/0.99  num_eq_ax_congr_red:                    17
% 3.10/0.99  num_of_sem_filtered_clauses:            1
% 3.10/0.99  num_of_subtypes:                        0
% 3.10/0.99  monotx_restored_types:                  0
% 3.10/0.99  sat_num_of_epr_types:                   0
% 3.10/0.99  sat_num_of_non_cyclic_types:            0
% 3.10/0.99  sat_guarded_non_collapsed_types:        0
% 3.10/0.99  num_pure_diseq_elim:                    0
% 3.10/0.99  simp_replaced_by:                       0
% 3.10/0.99  res_preprocessed:                       182
% 3.10/0.99  prep_upred:                             0
% 3.10/0.99  prep_unflattend:                        45
% 3.10/0.99  smt_new_axioms:                         0
% 3.10/0.99  pred_elim_cands:                        6
% 3.10/0.99  pred_elim:                              2
% 3.10/0.99  pred_elim_cl:                           3
% 3.10/0.99  pred_elim_cycles:                       4
% 3.10/0.99  merged_defs:                            8
% 3.10/0.99  merged_defs_ncl:                        0
% 3.10/0.99  bin_hyper_res:                          9
% 3.10/0.99  prep_cycles:                            4
% 3.10/0.99  pred_elim_time:                         0.007
% 3.10/0.99  splitting_time:                         0.
% 3.10/0.99  sem_filter_time:                        0.
% 3.10/0.99  monotx_time:                            0.
% 3.10/0.99  subtype_inf_time:                       0.
% 3.10/0.99  
% 3.10/0.99  ------ Problem properties
% 3.10/0.99  
% 3.10/0.99  clauses:                                37
% 3.10/0.99  conjectures:                            9
% 3.10/0.99  epr:                                    14
% 3.10/0.99  horn:                                   30
% 3.10/0.99  ground:                                 14
% 3.10/0.99  unary:                                  14
% 3.10/0.99  binary:                                 11
% 3.10/0.99  lits:                                   88
% 3.10/0.99  lits_eq:                                24
% 3.10/0.99  fd_pure:                                0
% 3.10/0.99  fd_pseudo:                              0
% 3.10/0.99  fd_cond:                                3
% 3.10/0.99  fd_pseudo_cond:                         1
% 3.10/0.99  ac_symbols:                             0
% 3.10/0.99  
% 3.10/0.99  ------ Propositional Solver
% 3.10/0.99  
% 3.10/0.99  prop_solver_calls:                      28
% 3.10/0.99  prop_fast_solver_calls:                 1285
% 3.10/0.99  smt_solver_calls:                       0
% 3.10/0.99  smt_fast_solver_calls:                  0
% 3.10/0.99  prop_num_of_clauses:                    2840
% 3.10/0.99  prop_preprocess_simplified:             9512
% 3.10/0.99  prop_fo_subsumed:                       36
% 3.10/0.99  prop_solver_time:                       0.
% 3.10/0.99  smt_solver_time:                        0.
% 3.10/0.99  smt_fast_solver_time:                   0.
% 3.10/0.99  prop_fast_solver_time:                  0.
% 3.10/0.99  prop_unsat_core_time:                   0.
% 3.10/0.99  
% 3.10/0.99  ------ QBF
% 3.10/0.99  
% 3.10/0.99  qbf_q_res:                              0
% 3.10/0.99  qbf_num_tautologies:                    0
% 3.10/0.99  qbf_prep_cycles:                        0
% 3.10/0.99  
% 3.10/0.99  ------ BMC1
% 3.10/0.99  
% 3.10/0.99  bmc1_current_bound:                     -1
% 3.10/1.00  bmc1_last_solved_bound:                 -1
% 3.10/1.00  bmc1_unsat_core_size:                   -1
% 3.10/1.00  bmc1_unsat_core_parents_size:           -1
% 3.10/1.00  bmc1_merge_next_fun:                    0
% 3.10/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.10/1.00  
% 3.10/1.00  ------ Instantiation
% 3.10/1.00  
% 3.10/1.00  inst_num_of_clauses:                    962
% 3.10/1.00  inst_num_in_passive:                    499
% 3.10/1.00  inst_num_in_active:                     397
% 3.10/1.00  inst_num_in_unprocessed:                68
% 3.10/1.00  inst_num_of_loops:                      510
% 3.10/1.00  inst_num_of_learning_restarts:          0
% 3.10/1.00  inst_num_moves_active_passive:          109
% 3.10/1.00  inst_lit_activity:                      0
% 3.10/1.00  inst_lit_activity_moves:                0
% 3.10/1.00  inst_num_tautologies:                   0
% 3.10/1.00  inst_num_prop_implied:                  0
% 3.10/1.00  inst_num_existing_simplified:           0
% 3.10/1.00  inst_num_eq_res_simplified:             0
% 3.10/1.00  inst_num_child_elim:                    0
% 3.10/1.00  inst_num_of_dismatching_blockings:      243
% 3.10/1.00  inst_num_of_non_proper_insts:           850
% 3.10/1.00  inst_num_of_duplicates:                 0
% 3.10/1.00  inst_inst_num_from_inst_to_res:         0
% 3.10/1.00  inst_dismatching_checking_time:         0.
% 3.10/1.00  
% 3.10/1.00  ------ Resolution
% 3.10/1.00  
% 3.10/1.00  res_num_of_clauses:                     0
% 3.10/1.00  res_num_in_passive:                     0
% 3.10/1.00  res_num_in_active:                      0
% 3.10/1.00  res_num_of_loops:                       186
% 3.10/1.00  res_forward_subset_subsumed:            106
% 3.10/1.00  res_backward_subset_subsumed:           8
% 3.10/1.00  res_forward_subsumed:                   0
% 3.10/1.00  res_backward_subsumed:                  0
% 3.10/1.00  res_forward_subsumption_resolution:     0
% 3.10/1.00  res_backward_subsumption_resolution:    0
% 3.10/1.00  res_clause_to_clause_subsumption:       347
% 3.10/1.00  res_orphan_elimination:                 0
% 3.10/1.00  res_tautology_del:                      61
% 3.10/1.00  res_num_eq_res_simplified:              0
% 3.10/1.00  res_num_sel_changes:                    0
% 3.10/1.00  res_moves_from_active_to_pass:          0
% 3.10/1.00  
% 3.10/1.00  ------ Superposition
% 3.10/1.00  
% 3.10/1.00  sup_time_total:                         0.
% 3.10/1.00  sup_time_generating:                    0.
% 3.10/1.00  sup_time_sim_full:                      0.
% 3.10/1.00  sup_time_sim_immed:                     0.
% 3.10/1.00  
% 3.10/1.00  sup_num_of_clauses:                     151
% 3.10/1.00  sup_num_in_active:                      95
% 3.10/1.00  sup_num_in_passive:                     56
% 3.10/1.00  sup_num_of_loops:                       101
% 3.10/1.00  sup_fw_superposition:                   102
% 3.10/1.00  sup_bw_superposition:                   45
% 3.10/1.00  sup_immediate_simplified:               15
% 3.10/1.00  sup_given_eliminated:                   0
% 3.10/1.00  comparisons_done:                       0
% 3.10/1.00  comparisons_avoided:                    0
% 3.10/1.00  
% 3.10/1.00  ------ Simplifications
% 3.10/1.00  
% 3.10/1.00  
% 3.10/1.00  sim_fw_subset_subsumed:                 2
% 3.10/1.00  sim_bw_subset_subsumed:                 3
% 3.10/1.00  sim_fw_subsumed:                        6
% 3.10/1.00  sim_bw_subsumed:                        0
% 3.10/1.00  sim_fw_subsumption_res:                 5
% 3.10/1.00  sim_bw_subsumption_res:                 0
% 3.10/1.00  sim_tautology_del:                      8
% 3.10/1.00  sim_eq_tautology_del:                   6
% 3.10/1.00  sim_eq_res_simp:                        0
% 3.10/1.00  sim_fw_demodulated:                     3
% 3.10/1.00  sim_bw_demodulated:                     6
% 3.10/1.00  sim_light_normalised:                   7
% 3.10/1.00  sim_joinable_taut:                      0
% 3.10/1.00  sim_joinable_simp:                      0
% 3.10/1.00  sim_ac_normalised:                      0
% 3.10/1.00  sim_smt_subsumption:                    0
% 3.10/1.00  
%------------------------------------------------------------------------------
