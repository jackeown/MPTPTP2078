%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:53 EST 2020

% Result     : Theorem 11.57s
% Output     : CNFRefutation 11.57s
% Verified   : 
% Statistics : Number of formulae       :  196 ( 720 expanded)
%              Number of clauses        :  110 ( 202 expanded)
%              Number of leaves         :   28 ( 239 expanded)
%              Depth                    :   20
%              Number of atoms          :  706 (5086 expanded)
%              Number of equality atoms :  287 (1382 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f18])).

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
    inference(flattening,[],[f39])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
          & k1_xboole_0 != X1
          & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
          & m1_subset_1(X5,X1) )
     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK9) != k7_partfun1(X0,X4,k1_funct_1(X3,sK9))
        & k1_xboole_0 != X1
        & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
        & m1_subset_1(sK9,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
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
            ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK8),X5) != k7_partfun1(X0,sK8,k1_funct_1(X3,X5))
            & k1_xboole_0 != X1
            & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK8))
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        & v1_funct_1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
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
                ( k1_funct_1(k8_funct_2(X1,X2,X0,sK7,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(sK7,X5))
                & k1_xboole_0 != X1
                & r1_tarski(k2_relset_1(X1,X2,sK7),k1_relset_1(X2,X0,X4))
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK7,X1,X2)
        & v1_funct_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
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
                  ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,X3,X4),X5) != k7_partfun1(sK4,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != sK5
                  & r1_tarski(k2_relset_1(sK5,sK6,X3),k1_relset_1(sK6,sK4,X4))
                  & m1_subset_1(X5,sK5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
          & v1_funct_2(X3,sK5,sK6)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9))
    & k1_xboole_0 != sK5
    & r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8))
    & m1_subset_1(sK9,sK5)
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
    & v1_funct_1(sK8)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK7,sK5,sK6)
    & v1_funct_1(sK7)
    & ~ v1_xboole_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f40,f58,f57,f56,f55])).

fof(f91,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ),
    inference(cnf_transformation,[],[f59])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f92,plain,(
    m1_subset_1(sK9,sK5) ),
    inference(cnf_transformation,[],[f59])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f94,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f59])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f49])).

fof(f66,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).

fof(f60,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f89,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f59])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f93,plain,(
    r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) ),
    inference(cnf_transformation,[],[f59])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

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

fof(f33,plain,(
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
    inference(flattening,[],[f33])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f88,plain,(
    v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f59])).

fof(f86,plain,(
    ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f59])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v5_relat_1(X2,X0)
        & v1_relat_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => m1_subset_1(k1_funct_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f87,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f59])).

fof(f90,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f59])).

fof(f61,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f46,f47])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f13,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                  & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  & m1_subset_1(X3,X1) )
              | k1_xboole_0 = k1_relset_1(X0,X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  & m1_subset_1(X3,X1) )
              | k1_xboole_0 = k1_relset_1(X0,X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,k2_relset_1(X0,X1,X2))
          & m1_subset_1(X3,X1) )
     => ( r2_hidden(sK3(X0,X1,X2),k2_relset_1(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(sK3(X0,X1,X2),k2_relset_1(X0,X1,X2))
                & m1_subset_1(sK3(X0,X1,X2),X1) )
              | k1_xboole_0 = k1_relset_1(X0,X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f52])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),k2_relset_1(X0,X1,X2))
      | k1_xboole_0 = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f16,axiom,(
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

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f16])).

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
    inference(flattening,[],[f37])).

fof(f85,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f95,plain,(
    k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2516,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_13,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2524,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3343,plain,
    ( v5_relat_1(sK8,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2516,c_2524])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK9,sK5) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2517,plain,
    ( m1_subset_1(sK9,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2530,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3889,plain,
    ( r2_hidden(sK9,sK5) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2517,c_2530])).

cnf(c_42,plain,
    ( m1_subset_1(sK9,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_6,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2580,plain,
    ( r2_hidden(sK2(sK5),sK5)
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2581,plain,
    ( k1_xboole_0 = sK5
    | r2_hidden(sK2(sK5),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2580])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2621,plain,
    ( ~ r2_hidden(sK2(sK5),sK5)
    | ~ v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2622,plain,
    ( r2_hidden(sK2(sK5),sK5) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2621])).

cnf(c_2706,plain,
    ( ~ m1_subset_1(X0,sK5)
    | r2_hidden(X0,sK5)
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2890,plain,
    ( ~ m1_subset_1(sK9,sK5)
    | r2_hidden(sK9,sK5)
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_2706])).

cnf(c_2891,plain,
    ( m1_subset_1(sK9,sK5) != iProver_top
    | r2_hidden(sK9,sK5) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2890])).

cnf(c_4257,plain,
    ( r2_hidden(sK9,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3889,c_42,c_27,c_2581,c_2622,c_2891])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2514,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2522,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3607,plain,
    ( k2_relset_1(sK5,sK6,sK7) = k2_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_2514,c_2522])).

cnf(c_28,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2518,plain,
    ( r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4053,plain,
    ( r1_tarski(k2_relat_1(sK7),k1_relset_1(sK6,sK4,sK8)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3607,c_2518])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2523,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3801,plain,
    ( k1_relset_1(sK6,sK4,sK8) = k1_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_2516,c_2523])).

cnf(c_4054,plain,
    ( r1_tarski(k2_relat_1(sK7),k1_relat_1(sK8)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4053,c_3801])).

cnf(c_9,plain,
    ( v5_relat_1(X0,X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2528,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4682,plain,
    ( v5_relat_1(sK7,k1_relat_1(sK8)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_4054,c_2528])).

cnf(c_11,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2526,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2529,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3897,plain,
    ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2514,c_2529])).

cnf(c_4226,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2526,c_3897])).

cnf(c_4756,plain,
    ( v5_relat_1(sK7,k1_relat_1(sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4682,c_4226])).

cnf(c_3802,plain,
    ( k1_relset_1(sK5,sK6,sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_2514,c_2523])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_893,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK7 != X0
    | sK6 != X2
    | sK5 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_33])).

cnf(c_894,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | k1_relset_1(sK5,sK6,sK7) = sK5
    | k1_xboole_0 = sK6 ),
    inference(unflattening,[status(thm)],[c_893])).

cnf(c_896,plain,
    ( k1_relset_1(sK5,sK6,sK7) = sK5
    | k1_xboole_0 = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_894,c_32])).

cnf(c_4124,plain,
    ( k1_relat_1(sK7) = sK5
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3802,c_896])).

cnf(c_35,negated_conjecture,
    ( ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1992,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2590,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK6)
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_1992])).

cnf(c_2597,plain,
    ( v1_xboole_0(sK6)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK6 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2590])).

cnf(c_4228,plain,
    ( k1_relat_1(sK7) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4124,c_35,c_5,c_2597])).

cnf(c_12,plain,
    ( ~ v5_relat_1(X0,X1)
    | m1_subset_1(k1_funct_1(X0,X2),X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2525,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | m1_subset_1(k1_funct_1(X0,X2),X1) = iProver_top
    | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4406,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
    | r2_hidden(k1_funct_1(X0,X2),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2525,c_2530])).

cnf(c_24,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2519,plain,
    ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
    | v5_relat_1(X1,X0) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_6631,plain,
    ( k7_partfun1(X0,X1,k1_funct_1(X2,X3)) = k1_funct_1(X1,k1_funct_1(X2,X3))
    | v5_relat_1(X1,X0) != iProver_top
    | v5_relat_1(X2,k1_relat_1(X1)) != iProver_top
    | r2_hidden(X3,k1_relat_1(X2)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_xboole_0(k1_relat_1(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4406,c_2519])).

cnf(c_21671,plain,
    ( k7_partfun1(X0,X1,k1_funct_1(sK7,X2)) = k1_funct_1(X1,k1_funct_1(sK7,X2))
    | v5_relat_1(X1,X0) != iProver_top
    | v5_relat_1(sK7,k1_relat_1(X1)) != iProver_top
    | r2_hidden(X2,sK5) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_xboole_0(k1_relat_1(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4228,c_6631])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_37,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_22020,plain,
    ( v1_relat_1(X1) != iProver_top
    | k7_partfun1(X0,X1,k1_funct_1(sK7,X2)) = k1_funct_1(X1,k1_funct_1(sK7,X2))
    | v5_relat_1(X1,X0) != iProver_top
    | v5_relat_1(sK7,k1_relat_1(X1)) != iProver_top
    | r2_hidden(X2,sK5) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(k1_relat_1(X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21671,c_37,c_4226])).

cnf(c_22021,plain,
    ( k7_partfun1(X0,X1,k1_funct_1(sK7,X2)) = k1_funct_1(X1,k1_funct_1(sK7,X2))
    | v5_relat_1(X1,X0) != iProver_top
    | v5_relat_1(sK7,k1_relat_1(X1)) != iProver_top
    | r2_hidden(X2,sK5) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_xboole_0(k1_relat_1(X1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_22020])).

cnf(c_22027,plain,
    ( k7_partfun1(X0,sK8,k1_funct_1(sK7,X1)) = k1_funct_1(sK8,k1_funct_1(sK7,X1))
    | v5_relat_1(sK8,X0) != iProver_top
    | r2_hidden(X1,sK5) != iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top
    | v1_xboole_0(k1_relat_1(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4756,c_22021])).

cnf(c_36,plain,
    ( v1_xboole_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_40,plain,
    ( v1_funct_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1990,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2019,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1990])).

cnf(c_1991,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2583,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_1991])).

cnf(c_2584,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2583])).

cnf(c_3896,plain,
    ( v1_relat_1(k2_zfmisc_1(sK6,sK4)) != iProver_top
    | v1_relat_1(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2516,c_2529])).

cnf(c_4130,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2526,c_3896])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2537,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2533,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4681,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4054,c_2533])).

cnf(c_4820,plain,
    ( r2_hidden(sK0(k2_relat_1(sK7)),k1_relat_1(sK8)) = iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2537,c_4681])).

cnf(c_2536,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5423,plain,
    ( v1_xboole_0(k1_relat_1(sK8)) != iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4820,c_2536])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(sK3(X1,X2,X0),k2_relset_1(X1,X2,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | k1_relset_1(X1,X2,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2521,plain,
    ( k1_relset_1(X0,X1,X2) = k1_xboole_0
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(sK3(X0,X1,X2),k2_relset_1(X0,X1,X2)) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4436,plain,
    ( k1_relset_1(X0,X1,X2) = k1_xboole_0
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k2_relset_1(X0,X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2521,c_2536])).

cnf(c_12117,plain,
    ( k1_relset_1(sK5,sK6,sK7) = k1_xboole_0
    | v1_xboole_0(k2_relset_1(sK5,sK6,sK7)) != iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2514,c_4436])).

cnf(c_12120,plain,
    ( k1_relset_1(sK5,sK6,sK7) = k1_xboole_0
    | v1_xboole_0(k2_relat_1(sK7)) != iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12117,c_3607])).

cnf(c_4230,plain,
    ( k1_relset_1(sK5,sK6,sK7) = sK5 ),
    inference(demodulation,[status(thm)],[c_4228,c_3802])).

cnf(c_12121,plain,
    ( sK5 = k1_xboole_0
    | v1_xboole_0(k2_relat_1(sK7)) != iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12120,c_4230])).

cnf(c_28517,plain,
    ( r2_hidden(X1,sK5) != iProver_top
    | v5_relat_1(sK8,X0) != iProver_top
    | k7_partfun1(X0,sK8,k1_funct_1(sK7,X1)) = k1_funct_1(sK8,k1_funct_1(sK7,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22027,c_36,c_40,c_27,c_2019,c_2581,c_2584,c_2622,c_4130,c_5423,c_12121])).

cnf(c_28518,plain,
    ( k7_partfun1(X0,sK8,k1_funct_1(sK7,X1)) = k1_funct_1(sK8,k1_funct_1(sK7,X1))
    | v5_relat_1(sK8,X0) != iProver_top
    | r2_hidden(X1,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_28517])).

cnf(c_28526,plain,
    ( k7_partfun1(X0,sK8,k1_funct_1(sK7,sK9)) = k1_funct_1(sK8,k1_funct_1(sK7,sK9))
    | v5_relat_1(sK8,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4257,c_28518])).

cnf(c_28636,plain,
    ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) = k1_funct_1(sK8,k1_funct_1(sK7,sK9)) ),
    inference(superposition,[status(thm)],[c_3343,c_28526])).

cnf(c_25,plain,
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
    inference(cnf_transformation,[],[f85])).

cnf(c_866,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X5)))
    | ~ r1_tarski(k2_relset_1(X1,X3,X2),k1_relset_1(X3,X5,X4))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X4)
    | v1_xboole_0(X3)
    | k1_funct_1(k8_funct_2(X1,X3,X5,X2,X4),X0) = k1_funct_1(X4,k1_funct_1(X2,X0))
    | sK7 != X2
    | sK6 != X3
    | sK5 != X1
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_33])).

cnf(c_867,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,X1)))
    | ~ m1_subset_1(X2,sK5)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,X1,X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK7)
    | v1_xboole_0(sK6)
    | k1_funct_1(k8_funct_2(sK5,sK6,X1,sK7,X0),X2) = k1_funct_1(X0,k1_funct_1(sK7,X2))
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_866])).

cnf(c_871,plain,
    ( k1_funct_1(k8_funct_2(sK5,sK6,X1,sK7,X0),X2) = k1_funct_1(X0,k1_funct_1(sK7,X2))
    | ~ v1_funct_1(X0)
    | ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,X1)))
    | ~ m1_subset_1(X2,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_867,c_35,c_34,c_32,c_27])).

cnf(c_872,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,X1)))
    | ~ m1_subset_1(X2,sK5)
    | ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,X1,X0))
    | ~ v1_funct_1(X0)
    | k1_funct_1(k8_funct_2(sK5,sK6,X1,sK7,X0),X2) = k1_funct_1(X0,k1_funct_1(sK7,X2)) ),
    inference(renaming,[status(thm)],[c_871])).

cnf(c_2609,plain,
    ( ~ m1_subset_1(X0,sK5)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,X1)))
    | ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,X1,sK8))
    | ~ v1_funct_1(sK8)
    | k1_funct_1(k8_funct_2(sK5,sK6,X1,sK7,sK8),X0) = k1_funct_1(sK8,k1_funct_1(sK7,X0)) ),
    inference(instantiation,[status(thm)],[c_872])).

cnf(c_2647,plain,
    ( ~ m1_subset_1(sK9,sK5)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,X0)))
    | ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,X0,sK8))
    | ~ v1_funct_1(sK8)
    | k1_funct_1(k8_funct_2(sK5,sK6,X0,sK7,sK8),sK9) = k1_funct_1(sK8,k1_funct_1(sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_2609])).

cnf(c_2764,plain,
    ( ~ m1_subset_1(sK9,sK5)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
    | ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8))
    | ~ v1_funct_1(sK8)
    | k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) = k1_funct_1(sK8,k1_funct_1(sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_2647])).

cnf(c_2578,plain,
    ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != X0
    | k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != X0
    | k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) = k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_1991])).

cnf(c_2626,plain,
    ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(sK8,k1_funct_1(sK7,sK9))
    | k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) = k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9))
    | k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k1_funct_1(sK8,k1_funct_1(sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_2578])).

cnf(c_26,negated_conjecture,
    ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) ),
    inference(cnf_transformation,[],[f95])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_28636,c_2764,c_2626,c_26,c_28,c_29,c_30,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:30:49 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 11.57/1.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.57/1.98  
% 11.57/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.57/1.98  
% 11.57/1.98  ------  iProver source info
% 11.57/1.98  
% 11.57/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.57/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.57/1.98  git: non_committed_changes: false
% 11.57/1.98  git: last_make_outside_of_git: false
% 11.57/1.98  
% 11.57/1.98  ------ 
% 11.57/1.98  
% 11.57/1.98  ------ Input Options
% 11.57/1.98  
% 11.57/1.98  --out_options                           all
% 11.57/1.98  --tptp_safe_out                         true
% 11.57/1.98  --problem_path                          ""
% 11.57/1.98  --include_path                          ""
% 11.57/1.98  --clausifier                            res/vclausify_rel
% 11.57/1.98  --clausifier_options                    ""
% 11.57/1.98  --stdin                                 false
% 11.57/1.98  --stats_out                             all
% 11.57/1.98  
% 11.57/1.98  ------ General Options
% 11.57/1.98  
% 11.57/1.98  --fof                                   false
% 11.57/1.98  --time_out_real                         305.
% 11.57/1.98  --time_out_virtual                      -1.
% 11.57/1.98  --symbol_type_check                     false
% 11.57/1.98  --clausify_out                          false
% 11.57/1.98  --sig_cnt_out                           false
% 11.57/1.98  --trig_cnt_out                          false
% 11.57/1.98  --trig_cnt_out_tolerance                1.
% 11.57/1.98  --trig_cnt_out_sk_spl                   false
% 11.57/1.98  --abstr_cl_out                          false
% 11.57/1.98  
% 11.57/1.98  ------ Global Options
% 11.57/1.98  
% 11.57/1.98  --schedule                              default
% 11.57/1.98  --add_important_lit                     false
% 11.57/1.98  --prop_solver_per_cl                    1000
% 11.57/1.98  --min_unsat_core                        false
% 11.57/1.98  --soft_assumptions                      false
% 11.57/1.98  --soft_lemma_size                       3
% 11.57/1.98  --prop_impl_unit_size                   0
% 11.57/1.98  --prop_impl_unit                        []
% 11.57/1.98  --share_sel_clauses                     true
% 11.57/1.98  --reset_solvers                         false
% 11.57/1.98  --bc_imp_inh                            [conj_cone]
% 11.57/1.98  --conj_cone_tolerance                   3.
% 11.57/1.98  --extra_neg_conj                        none
% 11.57/1.98  --large_theory_mode                     true
% 11.57/1.98  --prolific_symb_bound                   200
% 11.57/1.98  --lt_threshold                          2000
% 11.57/1.98  --clause_weak_htbl                      true
% 11.57/1.98  --gc_record_bc_elim                     false
% 11.57/1.98  
% 11.57/1.98  ------ Preprocessing Options
% 11.57/1.98  
% 11.57/1.98  --preprocessing_flag                    true
% 11.57/1.98  --time_out_prep_mult                    0.1
% 11.57/1.98  --splitting_mode                        input
% 11.57/1.98  --splitting_grd                         true
% 11.57/1.98  --splitting_cvd                         false
% 11.57/1.98  --splitting_cvd_svl                     false
% 11.57/1.98  --splitting_nvd                         32
% 11.57/1.98  --sub_typing                            true
% 11.57/1.98  --prep_gs_sim                           true
% 11.57/1.98  --prep_unflatten                        true
% 11.57/1.98  --prep_res_sim                          true
% 11.57/1.98  --prep_upred                            true
% 11.57/1.98  --prep_sem_filter                       exhaustive
% 11.57/1.98  --prep_sem_filter_out                   false
% 11.57/1.98  --pred_elim                             true
% 11.57/1.98  --res_sim_input                         true
% 11.57/1.98  --eq_ax_congr_red                       true
% 11.57/1.98  --pure_diseq_elim                       true
% 11.57/1.98  --brand_transform                       false
% 11.57/1.98  --non_eq_to_eq                          false
% 11.57/1.98  --prep_def_merge                        true
% 11.57/1.98  --prep_def_merge_prop_impl              false
% 11.57/1.98  --prep_def_merge_mbd                    true
% 11.57/1.98  --prep_def_merge_tr_red                 false
% 11.57/1.98  --prep_def_merge_tr_cl                  false
% 11.57/1.98  --smt_preprocessing                     true
% 11.57/1.98  --smt_ac_axioms                         fast
% 11.57/1.98  --preprocessed_out                      false
% 11.57/1.98  --preprocessed_stats                    false
% 11.57/1.98  
% 11.57/1.98  ------ Abstraction refinement Options
% 11.57/1.98  
% 11.57/1.98  --abstr_ref                             []
% 11.57/1.98  --abstr_ref_prep                        false
% 11.57/1.98  --abstr_ref_until_sat                   false
% 11.57/1.98  --abstr_ref_sig_restrict                funpre
% 11.57/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.57/1.98  --abstr_ref_under                       []
% 11.57/1.98  
% 11.57/1.98  ------ SAT Options
% 11.57/1.98  
% 11.57/1.98  --sat_mode                              false
% 11.57/1.98  --sat_fm_restart_options                ""
% 11.57/1.98  --sat_gr_def                            false
% 11.57/1.98  --sat_epr_types                         true
% 11.57/1.98  --sat_non_cyclic_types                  false
% 11.57/1.98  --sat_finite_models                     false
% 11.57/1.98  --sat_fm_lemmas                         false
% 11.57/1.98  --sat_fm_prep                           false
% 11.57/1.98  --sat_fm_uc_incr                        true
% 11.57/1.98  --sat_out_model                         small
% 11.57/1.98  --sat_out_clauses                       false
% 11.57/1.98  
% 11.57/1.98  ------ QBF Options
% 11.57/1.98  
% 11.57/1.98  --qbf_mode                              false
% 11.57/1.98  --qbf_elim_univ                         false
% 11.57/1.98  --qbf_dom_inst                          none
% 11.57/1.98  --qbf_dom_pre_inst                      false
% 11.57/1.98  --qbf_sk_in                             false
% 11.57/1.98  --qbf_pred_elim                         true
% 11.57/1.98  --qbf_split                             512
% 11.57/1.98  
% 11.57/1.98  ------ BMC1 Options
% 11.57/1.98  
% 11.57/1.98  --bmc1_incremental                      false
% 11.57/1.98  --bmc1_axioms                           reachable_all
% 11.57/1.98  --bmc1_min_bound                        0
% 11.57/1.98  --bmc1_max_bound                        -1
% 11.57/1.98  --bmc1_max_bound_default                -1
% 11.57/1.98  --bmc1_symbol_reachability              true
% 11.57/1.98  --bmc1_property_lemmas                  false
% 11.57/1.98  --bmc1_k_induction                      false
% 11.57/1.98  --bmc1_non_equiv_states                 false
% 11.57/1.98  --bmc1_deadlock                         false
% 11.57/1.98  --bmc1_ucm                              false
% 11.57/1.98  --bmc1_add_unsat_core                   none
% 11.57/1.98  --bmc1_unsat_core_children              false
% 11.57/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.57/1.98  --bmc1_out_stat                         full
% 11.57/1.98  --bmc1_ground_init                      false
% 11.57/1.98  --bmc1_pre_inst_next_state              false
% 11.57/1.98  --bmc1_pre_inst_state                   false
% 11.57/1.98  --bmc1_pre_inst_reach_state             false
% 11.57/1.98  --bmc1_out_unsat_core                   false
% 11.57/1.98  --bmc1_aig_witness_out                  false
% 11.57/1.98  --bmc1_verbose                          false
% 11.57/1.98  --bmc1_dump_clauses_tptp                false
% 11.57/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.57/1.98  --bmc1_dump_file                        -
% 11.57/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.57/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.57/1.98  --bmc1_ucm_extend_mode                  1
% 11.57/1.98  --bmc1_ucm_init_mode                    2
% 11.57/1.98  --bmc1_ucm_cone_mode                    none
% 11.57/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.57/1.98  --bmc1_ucm_relax_model                  4
% 11.57/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.57/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.57/1.98  --bmc1_ucm_layered_model                none
% 11.57/1.98  --bmc1_ucm_max_lemma_size               10
% 11.57/1.98  
% 11.57/1.98  ------ AIG Options
% 11.57/1.98  
% 11.57/1.98  --aig_mode                              false
% 11.57/1.98  
% 11.57/1.98  ------ Instantiation Options
% 11.57/1.98  
% 11.57/1.98  --instantiation_flag                    true
% 11.57/1.98  --inst_sos_flag                         true
% 11.57/1.98  --inst_sos_phase                        true
% 11.57/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.57/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.57/1.98  --inst_lit_sel_side                     num_symb
% 11.57/1.98  --inst_solver_per_active                1400
% 11.57/1.98  --inst_solver_calls_frac                1.
% 11.57/1.98  --inst_passive_queue_type               priority_queues
% 11.57/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.57/1.98  --inst_passive_queues_freq              [25;2]
% 11.57/1.98  --inst_dismatching                      true
% 11.57/1.98  --inst_eager_unprocessed_to_passive     true
% 11.57/1.98  --inst_prop_sim_given                   true
% 11.57/1.98  --inst_prop_sim_new                     false
% 11.57/1.98  --inst_subs_new                         false
% 11.57/1.98  --inst_eq_res_simp                      false
% 11.57/1.98  --inst_subs_given                       false
% 11.57/1.98  --inst_orphan_elimination               true
% 11.57/1.98  --inst_learning_loop_flag               true
% 11.57/1.98  --inst_learning_start                   3000
% 11.57/1.98  --inst_learning_factor                  2
% 11.57/1.98  --inst_start_prop_sim_after_learn       3
% 11.57/1.98  --inst_sel_renew                        solver
% 11.57/1.98  --inst_lit_activity_flag                true
% 11.57/1.98  --inst_restr_to_given                   false
% 11.57/1.98  --inst_activity_threshold               500
% 11.57/1.98  --inst_out_proof                        true
% 11.57/1.98  
% 11.57/1.98  ------ Resolution Options
% 11.57/1.98  
% 11.57/1.98  --resolution_flag                       true
% 11.57/1.98  --res_lit_sel                           adaptive
% 11.57/1.98  --res_lit_sel_side                      none
% 11.57/1.98  --res_ordering                          kbo
% 11.57/1.98  --res_to_prop_solver                    active
% 11.57/1.98  --res_prop_simpl_new                    false
% 11.57/1.98  --res_prop_simpl_given                  true
% 11.57/1.98  --res_passive_queue_type                priority_queues
% 11.57/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.57/1.98  --res_passive_queues_freq               [15;5]
% 11.57/1.98  --res_forward_subs                      full
% 11.57/1.98  --res_backward_subs                     full
% 11.57/1.98  --res_forward_subs_resolution           true
% 11.57/1.98  --res_backward_subs_resolution          true
% 11.57/1.98  --res_orphan_elimination                true
% 11.57/1.98  --res_time_limit                        2.
% 11.57/1.98  --res_out_proof                         true
% 11.57/1.98  
% 11.57/1.98  ------ Superposition Options
% 11.57/1.98  
% 11.57/1.98  --superposition_flag                    true
% 11.57/1.98  --sup_passive_queue_type                priority_queues
% 11.57/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.57/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.57/1.98  --demod_completeness_check              fast
% 11.57/1.98  --demod_use_ground                      true
% 11.57/1.98  --sup_to_prop_solver                    passive
% 11.57/1.98  --sup_prop_simpl_new                    true
% 11.57/1.98  --sup_prop_simpl_given                  true
% 11.57/1.98  --sup_fun_splitting                     true
% 11.57/1.98  --sup_smt_interval                      50000
% 11.57/1.98  
% 11.57/1.98  ------ Superposition Simplification Setup
% 11.57/1.98  
% 11.57/1.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.57/1.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.57/1.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.57/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.57/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.57/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.57/1.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.57/1.98  --sup_immed_triv                        [TrivRules]
% 11.57/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.57/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.57/1.98  --sup_immed_bw_main                     []
% 11.57/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.57/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.57/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.57/1.98  --sup_input_bw                          []
% 11.57/1.98  
% 11.57/1.98  ------ Combination Options
% 11.57/1.98  
% 11.57/1.98  --comb_res_mult                         3
% 11.57/1.98  --comb_sup_mult                         2
% 11.57/1.98  --comb_inst_mult                        10
% 11.57/1.98  
% 11.57/1.98  ------ Debug Options
% 11.57/1.98  
% 11.57/1.98  --dbg_backtrace                         false
% 11.57/1.98  --dbg_dump_prop_clauses                 false
% 11.57/1.98  --dbg_dump_prop_clauses_file            -
% 11.57/1.98  --dbg_out_stat                          false
% 11.57/1.98  ------ Parsing...
% 11.57/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.57/1.98  
% 11.57/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.57/1.98  
% 11.57/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.57/1.98  
% 11.57/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.57/1.98  ------ Proving...
% 11.57/1.98  ------ Problem Properties 
% 11.57/1.98  
% 11.57/1.98  
% 11.57/1.98  clauses                                 33
% 11.57/1.98  conjectures                             9
% 11.57/1.98  EPR                                     9
% 11.57/1.98  Horn                                    25
% 11.57/1.98  unary                                   11
% 11.57/1.98  binary                                  9
% 11.57/1.98  lits                                    86
% 11.57/1.98  lits eq                                 19
% 11.57/1.98  fd_pure                                 0
% 11.57/1.98  fd_pseudo                               0
% 11.57/1.98  fd_cond                                 2
% 11.57/1.98  fd_pseudo_cond                          0
% 11.57/1.98  AC symbols                              0
% 11.57/1.98  
% 11.57/1.98  ------ Schedule dynamic 5 is on 
% 11.57/1.98  
% 11.57/1.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.57/1.98  
% 11.57/1.98  
% 11.57/1.98  ------ 
% 11.57/1.98  Current options:
% 11.57/1.98  ------ 
% 11.57/1.98  
% 11.57/1.98  ------ Input Options
% 11.57/1.98  
% 11.57/1.98  --out_options                           all
% 11.57/1.98  --tptp_safe_out                         true
% 11.57/1.98  --problem_path                          ""
% 11.57/1.98  --include_path                          ""
% 11.57/1.98  --clausifier                            res/vclausify_rel
% 11.57/1.98  --clausifier_options                    ""
% 11.57/1.98  --stdin                                 false
% 11.57/1.98  --stats_out                             all
% 11.57/1.98  
% 11.57/1.98  ------ General Options
% 11.57/1.98  
% 11.57/1.98  --fof                                   false
% 11.57/1.98  --time_out_real                         305.
% 11.57/1.98  --time_out_virtual                      -1.
% 11.57/1.98  --symbol_type_check                     false
% 11.57/1.98  --clausify_out                          false
% 11.57/1.98  --sig_cnt_out                           false
% 11.57/1.98  --trig_cnt_out                          false
% 11.57/1.98  --trig_cnt_out_tolerance                1.
% 11.57/1.98  --trig_cnt_out_sk_spl                   false
% 11.57/1.98  --abstr_cl_out                          false
% 11.57/1.98  
% 11.57/1.98  ------ Global Options
% 11.57/1.98  
% 11.57/1.98  --schedule                              default
% 11.57/1.98  --add_important_lit                     false
% 11.57/1.98  --prop_solver_per_cl                    1000
% 11.57/1.98  --min_unsat_core                        false
% 11.57/1.98  --soft_assumptions                      false
% 11.57/1.98  --soft_lemma_size                       3
% 11.57/1.98  --prop_impl_unit_size                   0
% 11.57/1.98  --prop_impl_unit                        []
% 11.57/1.98  --share_sel_clauses                     true
% 11.57/1.98  --reset_solvers                         false
% 11.57/1.98  --bc_imp_inh                            [conj_cone]
% 11.57/1.98  --conj_cone_tolerance                   3.
% 11.57/1.98  --extra_neg_conj                        none
% 11.57/1.98  --large_theory_mode                     true
% 11.57/1.98  --prolific_symb_bound                   200
% 11.57/1.98  --lt_threshold                          2000
% 11.57/1.98  --clause_weak_htbl                      true
% 11.57/1.98  --gc_record_bc_elim                     false
% 11.57/1.98  
% 11.57/1.98  ------ Preprocessing Options
% 11.57/1.98  
% 11.57/1.98  --preprocessing_flag                    true
% 11.57/1.98  --time_out_prep_mult                    0.1
% 11.57/1.98  --splitting_mode                        input
% 11.57/1.98  --splitting_grd                         true
% 11.57/1.98  --splitting_cvd                         false
% 11.57/1.98  --splitting_cvd_svl                     false
% 11.57/1.98  --splitting_nvd                         32
% 11.57/1.98  --sub_typing                            true
% 11.57/1.98  --prep_gs_sim                           true
% 11.57/1.98  --prep_unflatten                        true
% 11.57/1.98  --prep_res_sim                          true
% 11.57/1.98  --prep_upred                            true
% 11.57/1.98  --prep_sem_filter                       exhaustive
% 11.57/1.98  --prep_sem_filter_out                   false
% 11.57/1.98  --pred_elim                             true
% 11.57/1.98  --res_sim_input                         true
% 11.57/1.98  --eq_ax_congr_red                       true
% 11.57/1.98  --pure_diseq_elim                       true
% 11.57/1.98  --brand_transform                       false
% 11.57/1.98  --non_eq_to_eq                          false
% 11.57/1.98  --prep_def_merge                        true
% 11.57/1.98  --prep_def_merge_prop_impl              false
% 11.57/1.98  --prep_def_merge_mbd                    true
% 11.57/1.98  --prep_def_merge_tr_red                 false
% 11.57/1.98  --prep_def_merge_tr_cl                  false
% 11.57/1.98  --smt_preprocessing                     true
% 11.57/1.98  --smt_ac_axioms                         fast
% 11.57/1.98  --preprocessed_out                      false
% 11.57/1.98  --preprocessed_stats                    false
% 11.57/1.98  
% 11.57/1.98  ------ Abstraction refinement Options
% 11.57/1.98  
% 11.57/1.98  --abstr_ref                             []
% 11.57/1.98  --abstr_ref_prep                        false
% 11.57/1.98  --abstr_ref_until_sat                   false
% 11.57/1.98  --abstr_ref_sig_restrict                funpre
% 11.57/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.57/1.98  --abstr_ref_under                       []
% 11.57/1.98  
% 11.57/1.98  ------ SAT Options
% 11.57/1.98  
% 11.57/1.98  --sat_mode                              false
% 11.57/1.98  --sat_fm_restart_options                ""
% 11.57/1.98  --sat_gr_def                            false
% 11.57/1.98  --sat_epr_types                         true
% 11.57/1.98  --sat_non_cyclic_types                  false
% 11.57/1.98  --sat_finite_models                     false
% 11.57/1.98  --sat_fm_lemmas                         false
% 11.57/1.98  --sat_fm_prep                           false
% 11.57/1.98  --sat_fm_uc_incr                        true
% 11.57/1.98  --sat_out_model                         small
% 11.57/1.98  --sat_out_clauses                       false
% 11.57/1.98  
% 11.57/1.98  ------ QBF Options
% 11.57/1.98  
% 11.57/1.98  --qbf_mode                              false
% 11.57/1.98  --qbf_elim_univ                         false
% 11.57/1.98  --qbf_dom_inst                          none
% 11.57/1.98  --qbf_dom_pre_inst                      false
% 11.57/1.98  --qbf_sk_in                             false
% 11.57/1.98  --qbf_pred_elim                         true
% 11.57/1.98  --qbf_split                             512
% 11.57/1.98  
% 11.57/1.98  ------ BMC1 Options
% 11.57/1.98  
% 11.57/1.98  --bmc1_incremental                      false
% 11.57/1.98  --bmc1_axioms                           reachable_all
% 11.57/1.98  --bmc1_min_bound                        0
% 11.57/1.98  --bmc1_max_bound                        -1
% 11.57/1.98  --bmc1_max_bound_default                -1
% 11.57/1.98  --bmc1_symbol_reachability              true
% 11.57/1.98  --bmc1_property_lemmas                  false
% 11.57/1.98  --bmc1_k_induction                      false
% 11.57/1.98  --bmc1_non_equiv_states                 false
% 11.57/1.98  --bmc1_deadlock                         false
% 11.57/1.98  --bmc1_ucm                              false
% 11.57/1.98  --bmc1_add_unsat_core                   none
% 11.57/1.98  --bmc1_unsat_core_children              false
% 11.57/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.57/1.98  --bmc1_out_stat                         full
% 11.57/1.98  --bmc1_ground_init                      false
% 11.57/1.98  --bmc1_pre_inst_next_state              false
% 11.57/1.98  --bmc1_pre_inst_state                   false
% 11.57/1.98  --bmc1_pre_inst_reach_state             false
% 11.57/1.98  --bmc1_out_unsat_core                   false
% 11.57/1.98  --bmc1_aig_witness_out                  false
% 11.57/1.98  --bmc1_verbose                          false
% 11.57/1.98  --bmc1_dump_clauses_tptp                false
% 11.57/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.57/1.98  --bmc1_dump_file                        -
% 11.57/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.57/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.57/1.98  --bmc1_ucm_extend_mode                  1
% 11.57/1.98  --bmc1_ucm_init_mode                    2
% 11.57/1.98  --bmc1_ucm_cone_mode                    none
% 11.57/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.57/1.98  --bmc1_ucm_relax_model                  4
% 11.57/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.57/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.57/1.98  --bmc1_ucm_layered_model                none
% 11.57/1.98  --bmc1_ucm_max_lemma_size               10
% 11.57/1.98  
% 11.57/1.98  ------ AIG Options
% 11.57/1.98  
% 11.57/1.98  --aig_mode                              false
% 11.57/1.98  
% 11.57/1.98  ------ Instantiation Options
% 11.57/1.98  
% 11.57/1.98  --instantiation_flag                    true
% 11.57/1.98  --inst_sos_flag                         true
% 11.57/1.98  --inst_sos_phase                        true
% 11.57/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.57/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.57/1.98  --inst_lit_sel_side                     none
% 11.57/1.98  --inst_solver_per_active                1400
% 11.57/1.98  --inst_solver_calls_frac                1.
% 11.57/1.98  --inst_passive_queue_type               priority_queues
% 11.57/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.57/1.98  --inst_passive_queues_freq              [25;2]
% 11.57/1.98  --inst_dismatching                      true
% 11.57/1.98  --inst_eager_unprocessed_to_passive     true
% 11.57/1.98  --inst_prop_sim_given                   true
% 11.57/1.98  --inst_prop_sim_new                     false
% 11.57/1.98  --inst_subs_new                         false
% 11.57/1.98  --inst_eq_res_simp                      false
% 11.57/1.98  --inst_subs_given                       false
% 11.57/1.98  --inst_orphan_elimination               true
% 11.57/1.98  --inst_learning_loop_flag               true
% 11.57/1.98  --inst_learning_start                   3000
% 11.57/1.98  --inst_learning_factor                  2
% 11.57/1.98  --inst_start_prop_sim_after_learn       3
% 11.57/1.98  --inst_sel_renew                        solver
% 11.57/1.98  --inst_lit_activity_flag                true
% 11.57/1.98  --inst_restr_to_given                   false
% 11.57/1.98  --inst_activity_threshold               500
% 11.57/1.98  --inst_out_proof                        true
% 11.57/1.98  
% 11.57/1.98  ------ Resolution Options
% 11.57/1.98  
% 11.57/1.98  --resolution_flag                       false
% 11.57/1.98  --res_lit_sel                           adaptive
% 11.57/1.98  --res_lit_sel_side                      none
% 11.57/1.98  --res_ordering                          kbo
% 11.57/1.98  --res_to_prop_solver                    active
% 11.57/1.98  --res_prop_simpl_new                    false
% 11.57/1.98  --res_prop_simpl_given                  true
% 11.57/1.98  --res_passive_queue_type                priority_queues
% 11.57/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.57/1.98  --res_passive_queues_freq               [15;5]
% 11.57/1.98  --res_forward_subs                      full
% 11.57/1.98  --res_backward_subs                     full
% 11.57/1.98  --res_forward_subs_resolution           true
% 11.57/1.98  --res_backward_subs_resolution          true
% 11.57/1.98  --res_orphan_elimination                true
% 11.57/1.98  --res_time_limit                        2.
% 11.57/1.98  --res_out_proof                         true
% 11.57/1.98  
% 11.57/1.98  ------ Superposition Options
% 11.57/1.98  
% 11.57/1.98  --superposition_flag                    true
% 11.57/1.98  --sup_passive_queue_type                priority_queues
% 11.57/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.57/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.57/1.98  --demod_completeness_check              fast
% 11.57/1.98  --demod_use_ground                      true
% 11.57/1.98  --sup_to_prop_solver                    passive
% 11.57/1.98  --sup_prop_simpl_new                    true
% 11.57/1.98  --sup_prop_simpl_given                  true
% 11.57/1.98  --sup_fun_splitting                     true
% 11.57/1.98  --sup_smt_interval                      50000
% 11.57/1.98  
% 11.57/1.98  ------ Superposition Simplification Setup
% 11.57/1.98  
% 11.57/1.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.57/1.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.57/1.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.57/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.57/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.57/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.57/1.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.57/1.98  --sup_immed_triv                        [TrivRules]
% 11.57/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.57/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.57/1.98  --sup_immed_bw_main                     []
% 11.57/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.57/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.57/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.57/1.98  --sup_input_bw                          []
% 11.57/1.98  
% 11.57/1.98  ------ Combination Options
% 11.57/1.98  
% 11.57/1.98  --comb_res_mult                         3
% 11.57/1.98  --comb_sup_mult                         2
% 11.57/1.98  --comb_inst_mult                        10
% 11.57/1.98  
% 11.57/1.98  ------ Debug Options
% 11.57/1.98  
% 11.57/1.98  --dbg_backtrace                         false
% 11.57/1.98  --dbg_dump_prop_clauses                 false
% 11.57/1.98  --dbg_dump_prop_clauses_file            -
% 11.57/1.98  --dbg_out_stat                          false
% 11.57/1.98  
% 11.57/1.98  
% 11.57/1.98  
% 11.57/1.98  
% 11.57/1.98  ------ Proving...
% 11.57/1.98  
% 11.57/1.98  
% 11.57/1.98  % SZS status Theorem for theBenchmark.p
% 11.57/1.98  
% 11.57/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.57/1.98  
% 11.57/1.98  fof(f17,conjecture,(
% 11.57/1.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 11.57/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.57/1.98  
% 11.57/1.98  fof(f18,negated_conjecture,(
% 11.57/1.98    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 11.57/1.98    inference(negated_conjecture,[],[f17])).
% 11.57/1.98  
% 11.57/1.98  fof(f39,plain,(
% 11.57/1.98    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 11.57/1.98    inference(ennf_transformation,[],[f18])).
% 11.57/1.98  
% 11.57/1.98  fof(f40,plain,(
% 11.57/1.98    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 11.57/1.98    inference(flattening,[],[f39])).
% 11.57/1.98  
% 11.57/1.98  fof(f58,plain,(
% 11.57/1.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK9) != k7_partfun1(X0,X4,k1_funct_1(X3,sK9)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK9,X1))) )),
% 11.57/1.98    introduced(choice_axiom,[])).
% 11.57/1.98  
% 11.57/1.98  fof(f57,plain,(
% 11.57/1.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK8),X5) != k7_partfun1(X0,sK8,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK8)) & m1_subset_1(X5,X1)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK8))) )),
% 11.57/1.98    introduced(choice_axiom,[])).
% 11.57/1.98  
% 11.57/1.98  fof(f56,plain,(
% 11.57/1.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,sK7,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(sK7,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK7),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK7,X1,X2) & v1_funct_1(sK7))) )),
% 11.57/1.98    introduced(choice_axiom,[])).
% 11.57/1.98  
% 11.57/1.98  fof(f55,plain,(
% 11.57/1.98    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK5,sK6,sK4,X3,X4),X5) != k7_partfun1(sK4,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK5 & r1_tarski(k2_relset_1(sK5,sK6,X3),k1_relset_1(sK6,sK4,X4)) & m1_subset_1(X5,sK5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(X3,sK5,sK6) & v1_funct_1(X3)) & ~v1_xboole_0(sK6))),
% 11.57/1.98    introduced(choice_axiom,[])).
% 11.57/1.98  
% 11.57/1.98  fof(f59,plain,(
% 11.57/1.98    (((k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) & k1_xboole_0 != sK5 & r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) & m1_subset_1(sK9,sK5)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_1(sK8)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7)) & ~v1_xboole_0(sK6)),
% 11.57/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f40,f58,f57,f56,f55])).
% 11.57/1.98  
% 11.57/1.98  fof(f91,plain,(
% 11.57/1.98    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))),
% 11.57/1.98    inference(cnf_transformation,[],[f59])).
% 11.57/1.98  
% 11.57/1.98  fof(f10,axiom,(
% 11.57/1.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.57/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.57/1.98  
% 11.57/1.98  fof(f19,plain,(
% 11.57/1.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 11.57/1.98    inference(pure_predicate_removal,[],[f10])).
% 11.57/1.98  
% 11.57/1.98  fof(f28,plain,(
% 11.57/1.98    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.57/1.98    inference(ennf_transformation,[],[f19])).
% 11.57/1.98  
% 11.57/1.98  fof(f73,plain,(
% 11.57/1.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.57/1.98    inference(cnf_transformation,[],[f28])).
% 11.57/1.98  
% 11.57/1.98  fof(f92,plain,(
% 11.57/1.98    m1_subset_1(sK9,sK5)),
% 11.57/1.98    inference(cnf_transformation,[],[f59])).
% 11.57/1.98  
% 11.57/1.98  fof(f5,axiom,(
% 11.57/1.98    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 11.57/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.57/1.98  
% 11.57/1.98  fof(f22,plain,(
% 11.57/1.98    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 11.57/1.98    inference(ennf_transformation,[],[f5])).
% 11.57/1.98  
% 11.57/1.98  fof(f23,plain,(
% 11.57/1.98    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 11.57/1.98    inference(flattening,[],[f22])).
% 11.57/1.98  
% 11.57/1.98  fof(f67,plain,(
% 11.57/1.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 11.57/1.98    inference(cnf_transformation,[],[f23])).
% 11.57/1.98  
% 11.57/1.98  fof(f94,plain,(
% 11.57/1.98    k1_xboole_0 != sK5),
% 11.57/1.98    inference(cnf_transformation,[],[f59])).
% 11.57/1.98  
% 11.57/1.98  fof(f4,axiom,(
% 11.57/1.98    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 11.57/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.57/1.98  
% 11.57/1.98  fof(f21,plain,(
% 11.57/1.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 11.57/1.98    inference(ennf_transformation,[],[f4])).
% 11.57/1.98  
% 11.57/1.98  fof(f49,plain,(
% 11.57/1.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 11.57/1.98    introduced(choice_axiom,[])).
% 11.57/1.98  
% 11.57/1.98  fof(f50,plain,(
% 11.57/1.98    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 11.57/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f49])).
% 11.57/1.98  
% 11.57/1.98  fof(f66,plain,(
% 11.57/1.98    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 11.57/1.98    inference(cnf_transformation,[],[f50])).
% 11.57/1.98  
% 11.57/1.98  fof(f1,axiom,(
% 11.57/1.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 11.57/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.57/1.98  
% 11.57/1.98  fof(f41,plain,(
% 11.57/1.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 11.57/1.98    inference(nnf_transformation,[],[f1])).
% 11.57/1.98  
% 11.57/1.98  fof(f42,plain,(
% 11.57/1.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 11.57/1.98    inference(rectify,[],[f41])).
% 11.57/1.98  
% 11.57/1.98  fof(f43,plain,(
% 11.57/1.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 11.57/1.98    introduced(choice_axiom,[])).
% 11.57/1.98  
% 11.57/1.98  fof(f44,plain,(
% 11.57/1.98    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 11.57/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).
% 11.57/1.98  
% 11.57/1.98  fof(f60,plain,(
% 11.57/1.98    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 11.57/1.98    inference(cnf_transformation,[],[f44])).
% 11.57/1.98  
% 11.57/1.98  fof(f89,plain,(
% 11.57/1.98    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 11.57/1.98    inference(cnf_transformation,[],[f59])).
% 11.57/1.98  
% 11.57/1.98  fof(f12,axiom,(
% 11.57/1.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 11.57/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.57/1.98  
% 11.57/1.98  fof(f30,plain,(
% 11.57/1.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.57/1.98    inference(ennf_transformation,[],[f12])).
% 11.57/1.98  
% 11.57/1.98  fof(f75,plain,(
% 11.57/1.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.57/1.98    inference(cnf_transformation,[],[f30])).
% 11.57/1.98  
% 11.57/1.98  fof(f93,plain,(
% 11.57/1.98    r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8))),
% 11.57/1.98    inference(cnf_transformation,[],[f59])).
% 11.57/1.98  
% 11.57/1.98  fof(f11,axiom,(
% 11.57/1.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 11.57/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.57/1.98  
% 11.57/1.98  fof(f29,plain,(
% 11.57/1.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.57/1.98    inference(ennf_transformation,[],[f11])).
% 11.57/1.98  
% 11.57/1.98  fof(f74,plain,(
% 11.57/1.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.57/1.98    inference(cnf_transformation,[],[f29])).
% 11.57/1.98  
% 11.57/1.98  fof(f7,axiom,(
% 11.57/1.98    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 11.57/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.57/1.98  
% 11.57/1.98  fof(f25,plain,(
% 11.57/1.98    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.57/1.98    inference(ennf_transformation,[],[f7])).
% 11.57/1.98  
% 11.57/1.98  fof(f51,plain,(
% 11.57/1.98    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.57/1.98    inference(nnf_transformation,[],[f25])).
% 11.57/1.98  
% 11.57/1.98  fof(f70,plain,(
% 11.57/1.98    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 11.57/1.98    inference(cnf_transformation,[],[f51])).
% 11.57/1.98  
% 11.57/1.98  fof(f8,axiom,(
% 11.57/1.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 11.57/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.57/1.98  
% 11.57/1.98  fof(f71,plain,(
% 11.57/1.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 11.57/1.98    inference(cnf_transformation,[],[f8])).
% 11.57/1.98  
% 11.57/1.98  fof(f6,axiom,(
% 11.57/1.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 11.57/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.57/1.98  
% 11.57/1.98  fof(f24,plain,(
% 11.57/1.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 11.57/1.98    inference(ennf_transformation,[],[f6])).
% 11.57/1.98  
% 11.57/1.98  fof(f68,plain,(
% 11.57/1.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 11.57/1.98    inference(cnf_transformation,[],[f24])).
% 11.57/1.98  
% 11.57/1.98  fof(f14,axiom,(
% 11.57/1.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 11.57/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.57/1.98  
% 11.57/1.98  fof(f33,plain,(
% 11.57/1.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.57/1.98    inference(ennf_transformation,[],[f14])).
% 11.57/1.98  
% 11.57/1.98  fof(f34,plain,(
% 11.57/1.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.57/1.98    inference(flattening,[],[f33])).
% 11.57/1.98  
% 11.57/1.98  fof(f54,plain,(
% 11.57/1.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.57/1.98    inference(nnf_transformation,[],[f34])).
% 11.57/1.98  
% 11.57/1.98  fof(f78,plain,(
% 11.57/1.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.57/1.98    inference(cnf_transformation,[],[f54])).
% 11.57/1.98  
% 11.57/1.98  fof(f88,plain,(
% 11.57/1.98    v1_funct_2(sK7,sK5,sK6)),
% 11.57/1.98    inference(cnf_transformation,[],[f59])).
% 11.57/1.98  
% 11.57/1.98  fof(f86,plain,(
% 11.57/1.98    ~v1_xboole_0(sK6)),
% 11.57/1.98    inference(cnf_transformation,[],[f59])).
% 11.57/1.98  
% 11.57/1.98  fof(f3,axiom,(
% 11.57/1.98    v1_xboole_0(k1_xboole_0)),
% 11.57/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.57/1.98  
% 11.57/1.98  fof(f65,plain,(
% 11.57/1.98    v1_xboole_0(k1_xboole_0)),
% 11.57/1.98    inference(cnf_transformation,[],[f3])).
% 11.57/1.98  
% 11.57/1.98  fof(f9,axiom,(
% 11.57/1.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (r2_hidden(X1,k1_relat_1(X2)) => m1_subset_1(k1_funct_1(X2,X1),X0)))),
% 11.57/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.57/1.98  
% 11.57/1.98  fof(f26,plain,(
% 11.57/1.98    ! [X0,X1,X2] : ((m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2))) | (~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)))),
% 11.57/1.98    inference(ennf_transformation,[],[f9])).
% 11.57/1.98  
% 11.57/1.98  fof(f27,plain,(
% 11.57/1.98    ! [X0,X1,X2] : (m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2))),
% 11.57/1.98    inference(flattening,[],[f26])).
% 11.57/1.98  
% 11.57/1.98  fof(f72,plain,(
% 11.57/1.98    ( ! [X2,X0,X1] : (m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)) )),
% 11.57/1.98    inference(cnf_transformation,[],[f27])).
% 11.57/1.98  
% 11.57/1.98  fof(f15,axiom,(
% 11.57/1.98    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)))),
% 11.57/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.57/1.98  
% 11.57/1.98  fof(f35,plain,(
% 11.57/1.98    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 11.57/1.98    inference(ennf_transformation,[],[f15])).
% 11.57/1.98  
% 11.57/1.98  fof(f36,plain,(
% 11.57/1.98    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.57/1.98    inference(flattening,[],[f35])).
% 11.57/1.98  
% 11.57/1.98  fof(f84,plain,(
% 11.57/1.98    ( ! [X2,X0,X1] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.57/1.98    inference(cnf_transformation,[],[f36])).
% 11.57/1.98  
% 11.57/1.98  fof(f87,plain,(
% 11.57/1.98    v1_funct_1(sK7)),
% 11.57/1.98    inference(cnf_transformation,[],[f59])).
% 11.57/1.98  
% 11.57/1.98  fof(f90,plain,(
% 11.57/1.98    v1_funct_1(sK8)),
% 11.57/1.98    inference(cnf_transformation,[],[f59])).
% 11.57/1.98  
% 11.57/1.98  fof(f61,plain,(
% 11.57/1.98    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 11.57/1.98    inference(cnf_transformation,[],[f44])).
% 11.57/1.98  
% 11.57/1.98  fof(f2,axiom,(
% 11.57/1.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.57/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.57/1.98  
% 11.57/1.98  fof(f20,plain,(
% 11.57/1.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 11.57/1.98    inference(ennf_transformation,[],[f2])).
% 11.57/1.98  
% 11.57/1.98  fof(f45,plain,(
% 11.57/1.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 11.57/1.98    inference(nnf_transformation,[],[f20])).
% 11.57/1.98  
% 11.57/1.98  fof(f46,plain,(
% 11.57/1.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.57/1.98    inference(rectify,[],[f45])).
% 11.57/1.98  
% 11.57/1.98  fof(f47,plain,(
% 11.57/1.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 11.57/1.98    introduced(choice_axiom,[])).
% 11.57/1.98  
% 11.57/1.98  fof(f48,plain,(
% 11.57/1.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.57/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f46,f47])).
% 11.57/1.98  
% 11.57/1.98  fof(f62,plain,(
% 11.57/1.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 11.57/1.98    inference(cnf_transformation,[],[f48])).
% 11.57/1.98  
% 11.57/1.98  fof(f13,axiom,(
% 11.57/1.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 11.57/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.57/1.98  
% 11.57/1.98  fof(f31,plain,(
% 11.57/1.98    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : (r2_hidden(X3,k2_relset_1(X0,X1,X2)) & m1_subset_1(X3,X1)) | k1_xboole_0 = k1_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 11.57/1.98    inference(ennf_transformation,[],[f13])).
% 11.57/1.98  
% 11.57/1.98  fof(f32,plain,(
% 11.57/1.98    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r2_hidden(X3,k2_relset_1(X0,X1,X2)) & m1_subset_1(X3,X1)) | k1_xboole_0 = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 11.57/1.98    inference(flattening,[],[f31])).
% 11.57/1.98  
% 11.57/1.98  fof(f52,plain,(
% 11.57/1.98    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X3,k2_relset_1(X0,X1,X2)) & m1_subset_1(X3,X1)) => (r2_hidden(sK3(X0,X1,X2),k2_relset_1(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),X1)))),
% 11.57/1.98    introduced(choice_axiom,[])).
% 11.57/1.98  
% 11.57/1.98  fof(f53,plain,(
% 11.57/1.98    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(sK3(X0,X1,X2),k2_relset_1(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),X1)) | k1_xboole_0 = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 11.57/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f52])).
% 11.57/1.98  
% 11.57/1.98  fof(f77,plain,(
% 11.57/1.98    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),k2_relset_1(X0,X1,X2)) | k1_xboole_0 = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.57/1.98    inference(cnf_transformation,[],[f53])).
% 11.57/1.98  
% 11.57/1.98  fof(f16,axiom,(
% 11.57/1.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 11.57/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.57/1.98  
% 11.57/1.98  fof(f37,plain,(
% 11.57/1.98    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 11.57/1.98    inference(ennf_transformation,[],[f16])).
% 11.57/1.98  
% 11.57/1.98  fof(f38,plain,(
% 11.57/1.98    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 11.57/1.98    inference(flattening,[],[f37])).
% 11.57/1.98  
% 11.57/1.98  fof(f85,plain,(
% 11.57/1.98    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 11.57/1.98    inference(cnf_transformation,[],[f38])).
% 11.57/1.98  
% 11.57/1.98  fof(f95,plain,(
% 11.57/1.98    k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9))),
% 11.57/1.98    inference(cnf_transformation,[],[f59])).
% 11.57/1.98  
% 11.57/1.98  cnf(c_30,negated_conjecture,
% 11.57/1.98      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ),
% 11.57/1.98      inference(cnf_transformation,[],[f91]) ).
% 11.57/1.98  
% 11.57/1.98  cnf(c_2516,plain,
% 11.57/1.98      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) = iProver_top ),
% 11.57/1.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.57/1.98  
% 11.57/1.98  cnf(c_13,plain,
% 11.57/1.98      ( v5_relat_1(X0,X1)
% 11.57/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 11.57/1.98      inference(cnf_transformation,[],[f73]) ).
% 11.57/1.98  
% 11.57/1.98  cnf(c_2524,plain,
% 11.57/1.98      ( v5_relat_1(X0,X1) = iProver_top
% 11.57/1.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 11.57/1.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.57/1.98  
% 11.57/1.98  cnf(c_3343,plain,
% 11.57/1.98      ( v5_relat_1(sK8,sK4) = iProver_top ),
% 11.57/1.98      inference(superposition,[status(thm)],[c_2516,c_2524]) ).
% 11.57/1.98  
% 11.57/1.98  cnf(c_29,negated_conjecture,
% 11.57/1.98      ( m1_subset_1(sK9,sK5) ),
% 11.57/1.98      inference(cnf_transformation,[],[f92]) ).
% 11.57/1.98  
% 11.57/1.98  cnf(c_2517,plain,
% 11.57/1.98      ( m1_subset_1(sK9,sK5) = iProver_top ),
% 11.57/1.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.57/1.98  
% 11.57/1.98  cnf(c_7,plain,
% 11.57/1.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 11.57/1.98      inference(cnf_transformation,[],[f67]) ).
% 11.57/1.98  
% 11.57/1.98  cnf(c_2530,plain,
% 11.57/1.98      ( m1_subset_1(X0,X1) != iProver_top
% 11.57/1.98      | r2_hidden(X0,X1) = iProver_top
% 11.57/1.98      | v1_xboole_0(X1) = iProver_top ),
% 11.57/1.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.57/1.98  
% 11.57/1.98  cnf(c_3889,plain,
% 11.57/1.98      ( r2_hidden(sK9,sK5) = iProver_top
% 11.57/1.98      | v1_xboole_0(sK5) = iProver_top ),
% 11.57/1.98      inference(superposition,[status(thm)],[c_2517,c_2530]) ).
% 11.57/1.98  
% 11.57/1.98  cnf(c_42,plain,
% 11.57/1.98      ( m1_subset_1(sK9,sK5) = iProver_top ),
% 11.57/1.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.57/1.98  
% 11.57/1.98  cnf(c_27,negated_conjecture,
% 11.57/1.98      ( k1_xboole_0 != sK5 ),
% 11.57/1.98      inference(cnf_transformation,[],[f94]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_6,plain,
% 11.57/1.99      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 11.57/1.99      inference(cnf_transformation,[],[f66]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_2580,plain,
% 11.57/1.99      ( r2_hidden(sK2(sK5),sK5) | k1_xboole_0 = sK5 ),
% 11.57/1.99      inference(instantiation,[status(thm)],[c_6]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_2581,plain,
% 11.57/1.99      ( k1_xboole_0 = sK5 | r2_hidden(sK2(sK5),sK5) = iProver_top ),
% 11.57/1.99      inference(predicate_to_equality,[status(thm)],[c_2580]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_1,plain,
% 11.57/1.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 11.57/1.99      inference(cnf_transformation,[],[f60]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_2621,plain,
% 11.57/1.99      ( ~ r2_hidden(sK2(sK5),sK5) | ~ v1_xboole_0(sK5) ),
% 11.57/1.99      inference(instantiation,[status(thm)],[c_1]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_2622,plain,
% 11.57/1.99      ( r2_hidden(sK2(sK5),sK5) != iProver_top
% 11.57/1.99      | v1_xboole_0(sK5) != iProver_top ),
% 11.57/1.99      inference(predicate_to_equality,[status(thm)],[c_2621]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_2706,plain,
% 11.57/1.99      ( ~ m1_subset_1(X0,sK5) | r2_hidden(X0,sK5) | v1_xboole_0(sK5) ),
% 11.57/1.99      inference(instantiation,[status(thm)],[c_7]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_2890,plain,
% 11.57/1.99      ( ~ m1_subset_1(sK9,sK5) | r2_hidden(sK9,sK5) | v1_xboole_0(sK5) ),
% 11.57/1.99      inference(instantiation,[status(thm)],[c_2706]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_2891,plain,
% 11.57/1.99      ( m1_subset_1(sK9,sK5) != iProver_top
% 11.57/1.99      | r2_hidden(sK9,sK5) = iProver_top
% 11.57/1.99      | v1_xboole_0(sK5) = iProver_top ),
% 11.57/1.99      inference(predicate_to_equality,[status(thm)],[c_2890]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_4257,plain,
% 11.57/1.99      ( r2_hidden(sK9,sK5) = iProver_top ),
% 11.57/1.99      inference(global_propositional_subsumption,
% 11.57/1.99                [status(thm)],
% 11.57/1.99                [c_3889,c_42,c_27,c_2581,c_2622,c_2891]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_32,negated_conjecture,
% 11.57/1.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 11.57/1.99      inference(cnf_transformation,[],[f89]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_2514,plain,
% 11.57/1.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 11.57/1.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_15,plain,
% 11.57/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.57/1.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 11.57/1.99      inference(cnf_transformation,[],[f75]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_2522,plain,
% 11.57/1.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 11.57/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.57/1.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_3607,plain,
% 11.57/1.99      ( k2_relset_1(sK5,sK6,sK7) = k2_relat_1(sK7) ),
% 11.57/1.99      inference(superposition,[status(thm)],[c_2514,c_2522]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_28,negated_conjecture,
% 11.57/1.99      ( r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) ),
% 11.57/1.99      inference(cnf_transformation,[],[f93]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_2518,plain,
% 11.57/1.99      ( r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) = iProver_top ),
% 11.57/1.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_4053,plain,
% 11.57/1.99      ( r1_tarski(k2_relat_1(sK7),k1_relset_1(sK6,sK4,sK8)) = iProver_top ),
% 11.57/1.99      inference(demodulation,[status(thm)],[c_3607,c_2518]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_14,plain,
% 11.57/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.57/1.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 11.57/1.99      inference(cnf_transformation,[],[f74]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_2523,plain,
% 11.57/1.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 11.57/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.57/1.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_3801,plain,
% 11.57/1.99      ( k1_relset_1(sK6,sK4,sK8) = k1_relat_1(sK8) ),
% 11.57/1.99      inference(superposition,[status(thm)],[c_2516,c_2523]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_4054,plain,
% 11.57/1.99      ( r1_tarski(k2_relat_1(sK7),k1_relat_1(sK8)) = iProver_top ),
% 11.57/1.99      inference(light_normalisation,[status(thm)],[c_4053,c_3801]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_9,plain,
% 11.57/1.99      ( v5_relat_1(X0,X1)
% 11.57/1.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 11.57/1.99      | ~ v1_relat_1(X0) ),
% 11.57/1.99      inference(cnf_transformation,[],[f70]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_2528,plain,
% 11.57/1.99      ( v5_relat_1(X0,X1) = iProver_top
% 11.57/1.99      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 11.57/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.57/1.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_4682,plain,
% 11.57/1.99      ( v5_relat_1(sK7,k1_relat_1(sK8)) = iProver_top
% 11.57/1.99      | v1_relat_1(sK7) != iProver_top ),
% 11.57/1.99      inference(superposition,[status(thm)],[c_4054,c_2528]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_11,plain,
% 11.57/1.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 11.57/1.99      inference(cnf_transformation,[],[f71]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_2526,plain,
% 11.57/1.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 11.57/1.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_8,plain,
% 11.57/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.57/1.99      | ~ v1_relat_1(X1)
% 11.57/1.99      | v1_relat_1(X0) ),
% 11.57/1.99      inference(cnf_transformation,[],[f68]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_2529,plain,
% 11.57/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.57/1.99      | v1_relat_1(X1) != iProver_top
% 11.57/1.99      | v1_relat_1(X0) = iProver_top ),
% 11.57/1.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_3897,plain,
% 11.57/1.99      ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) != iProver_top
% 11.57/1.99      | v1_relat_1(sK7) = iProver_top ),
% 11.57/1.99      inference(superposition,[status(thm)],[c_2514,c_2529]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_4226,plain,
% 11.57/1.99      ( v1_relat_1(sK7) = iProver_top ),
% 11.57/1.99      inference(superposition,[status(thm)],[c_2526,c_3897]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_4756,plain,
% 11.57/1.99      ( v5_relat_1(sK7,k1_relat_1(sK8)) = iProver_top ),
% 11.57/1.99      inference(global_propositional_subsumption,
% 11.57/1.99                [status(thm)],
% 11.57/1.99                [c_4682,c_4226]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_3802,plain,
% 11.57/1.99      ( k1_relset_1(sK5,sK6,sK7) = k1_relat_1(sK7) ),
% 11.57/1.99      inference(superposition,[status(thm)],[c_2514,c_2523]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_23,plain,
% 11.57/1.99      ( ~ v1_funct_2(X0,X1,X2)
% 11.57/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.57/1.99      | k1_relset_1(X1,X2,X0) = X1
% 11.57/1.99      | k1_xboole_0 = X2 ),
% 11.57/1.99      inference(cnf_transformation,[],[f78]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_33,negated_conjecture,
% 11.57/1.99      ( v1_funct_2(sK7,sK5,sK6) ),
% 11.57/1.99      inference(cnf_transformation,[],[f88]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_893,plain,
% 11.57/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.57/1.99      | k1_relset_1(X1,X2,X0) = X1
% 11.57/1.99      | sK7 != X0
% 11.57/1.99      | sK6 != X2
% 11.57/1.99      | sK5 != X1
% 11.57/1.99      | k1_xboole_0 = X2 ),
% 11.57/1.99      inference(resolution_lifted,[status(thm)],[c_23,c_33]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_894,plain,
% 11.57/1.99      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 11.57/1.99      | k1_relset_1(sK5,sK6,sK7) = sK5
% 11.57/1.99      | k1_xboole_0 = sK6 ),
% 11.57/1.99      inference(unflattening,[status(thm)],[c_893]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_896,plain,
% 11.57/1.99      ( k1_relset_1(sK5,sK6,sK7) = sK5 | k1_xboole_0 = sK6 ),
% 11.57/1.99      inference(global_propositional_subsumption,
% 11.57/1.99                [status(thm)],
% 11.57/1.99                [c_894,c_32]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_4124,plain,
% 11.57/1.99      ( k1_relat_1(sK7) = sK5 | sK6 = k1_xboole_0 ),
% 11.57/1.99      inference(superposition,[status(thm)],[c_3802,c_896]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_35,negated_conjecture,
% 11.57/1.99      ( ~ v1_xboole_0(sK6) ),
% 11.57/1.99      inference(cnf_transformation,[],[f86]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_5,plain,
% 11.57/1.99      ( v1_xboole_0(k1_xboole_0) ),
% 11.57/1.99      inference(cnf_transformation,[],[f65]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_1992,plain,
% 11.57/1.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 11.57/1.99      theory(equality) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_2590,plain,
% 11.57/1.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK6) | sK6 != X0 ),
% 11.57/1.99      inference(instantiation,[status(thm)],[c_1992]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_2597,plain,
% 11.57/1.99      ( v1_xboole_0(sK6)
% 11.57/1.99      | ~ v1_xboole_0(k1_xboole_0)
% 11.57/1.99      | sK6 != k1_xboole_0 ),
% 11.57/1.99      inference(instantiation,[status(thm)],[c_2590]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_4228,plain,
% 11.57/1.99      ( k1_relat_1(sK7) = sK5 ),
% 11.57/1.99      inference(global_propositional_subsumption,
% 11.57/1.99                [status(thm)],
% 11.57/1.99                [c_4124,c_35,c_5,c_2597]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_12,plain,
% 11.57/1.99      ( ~ v5_relat_1(X0,X1)
% 11.57/1.99      | m1_subset_1(k1_funct_1(X0,X2),X1)
% 11.57/1.99      | ~ r2_hidden(X2,k1_relat_1(X0))
% 11.57/1.99      | ~ v1_funct_1(X0)
% 11.57/1.99      | ~ v1_relat_1(X0) ),
% 11.57/1.99      inference(cnf_transformation,[],[f72]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_2525,plain,
% 11.57/1.99      ( v5_relat_1(X0,X1) != iProver_top
% 11.57/1.99      | m1_subset_1(k1_funct_1(X0,X2),X1) = iProver_top
% 11.57/1.99      | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
% 11.57/1.99      | v1_funct_1(X0) != iProver_top
% 11.57/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.57/1.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_4406,plain,
% 11.57/1.99      ( v5_relat_1(X0,X1) != iProver_top
% 11.57/1.99      | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
% 11.57/1.99      | r2_hidden(k1_funct_1(X0,X2),X1) = iProver_top
% 11.57/1.99      | v1_funct_1(X0) != iProver_top
% 11.57/1.99      | v1_relat_1(X0) != iProver_top
% 11.57/1.99      | v1_xboole_0(X1) = iProver_top ),
% 11.57/1.99      inference(superposition,[status(thm)],[c_2525,c_2530]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_24,plain,
% 11.57/1.99      ( ~ v5_relat_1(X0,X1)
% 11.57/1.99      | ~ r2_hidden(X2,k1_relat_1(X0))
% 11.57/1.99      | ~ v1_funct_1(X0)
% 11.57/1.99      | ~ v1_relat_1(X0)
% 11.57/1.99      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 11.57/1.99      inference(cnf_transformation,[],[f84]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_2519,plain,
% 11.57/1.99      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
% 11.57/1.99      | v5_relat_1(X1,X0) != iProver_top
% 11.57/1.99      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 11.57/1.99      | v1_funct_1(X1) != iProver_top
% 11.57/1.99      | v1_relat_1(X1) != iProver_top ),
% 11.57/1.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_6631,plain,
% 11.57/1.99      ( k7_partfun1(X0,X1,k1_funct_1(X2,X3)) = k1_funct_1(X1,k1_funct_1(X2,X3))
% 11.57/1.99      | v5_relat_1(X1,X0) != iProver_top
% 11.57/1.99      | v5_relat_1(X2,k1_relat_1(X1)) != iProver_top
% 11.57/1.99      | r2_hidden(X3,k1_relat_1(X2)) != iProver_top
% 11.57/1.99      | v1_funct_1(X2) != iProver_top
% 11.57/1.99      | v1_funct_1(X1) != iProver_top
% 11.57/1.99      | v1_relat_1(X2) != iProver_top
% 11.57/1.99      | v1_relat_1(X1) != iProver_top
% 11.57/1.99      | v1_xboole_0(k1_relat_1(X1)) = iProver_top ),
% 11.57/1.99      inference(superposition,[status(thm)],[c_4406,c_2519]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_21671,plain,
% 11.57/1.99      ( k7_partfun1(X0,X1,k1_funct_1(sK7,X2)) = k1_funct_1(X1,k1_funct_1(sK7,X2))
% 11.57/1.99      | v5_relat_1(X1,X0) != iProver_top
% 11.57/1.99      | v5_relat_1(sK7,k1_relat_1(X1)) != iProver_top
% 11.57/1.99      | r2_hidden(X2,sK5) != iProver_top
% 11.57/1.99      | v1_funct_1(X1) != iProver_top
% 11.57/1.99      | v1_funct_1(sK7) != iProver_top
% 11.57/1.99      | v1_relat_1(X1) != iProver_top
% 11.57/1.99      | v1_relat_1(sK7) != iProver_top
% 11.57/1.99      | v1_xboole_0(k1_relat_1(X1)) = iProver_top ),
% 11.57/1.99      inference(superposition,[status(thm)],[c_4228,c_6631]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_34,negated_conjecture,
% 11.57/1.99      ( v1_funct_1(sK7) ),
% 11.57/1.99      inference(cnf_transformation,[],[f87]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_37,plain,
% 11.57/1.99      ( v1_funct_1(sK7) = iProver_top ),
% 11.57/1.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_22020,plain,
% 11.57/1.99      ( v1_relat_1(X1) != iProver_top
% 11.57/1.99      | k7_partfun1(X0,X1,k1_funct_1(sK7,X2)) = k1_funct_1(X1,k1_funct_1(sK7,X2))
% 11.57/1.99      | v5_relat_1(X1,X0) != iProver_top
% 11.57/1.99      | v5_relat_1(sK7,k1_relat_1(X1)) != iProver_top
% 11.57/1.99      | r2_hidden(X2,sK5) != iProver_top
% 11.57/1.99      | v1_funct_1(X1) != iProver_top
% 11.57/1.99      | v1_xboole_0(k1_relat_1(X1)) = iProver_top ),
% 11.57/1.99      inference(global_propositional_subsumption,
% 11.57/1.99                [status(thm)],
% 11.57/1.99                [c_21671,c_37,c_4226]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_22021,plain,
% 11.57/1.99      ( k7_partfun1(X0,X1,k1_funct_1(sK7,X2)) = k1_funct_1(X1,k1_funct_1(sK7,X2))
% 11.57/1.99      | v5_relat_1(X1,X0) != iProver_top
% 11.57/1.99      | v5_relat_1(sK7,k1_relat_1(X1)) != iProver_top
% 11.57/1.99      | r2_hidden(X2,sK5) != iProver_top
% 11.57/1.99      | v1_funct_1(X1) != iProver_top
% 11.57/1.99      | v1_relat_1(X1) != iProver_top
% 11.57/1.99      | v1_xboole_0(k1_relat_1(X1)) = iProver_top ),
% 11.57/1.99      inference(renaming,[status(thm)],[c_22020]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_22027,plain,
% 11.57/1.99      ( k7_partfun1(X0,sK8,k1_funct_1(sK7,X1)) = k1_funct_1(sK8,k1_funct_1(sK7,X1))
% 11.57/1.99      | v5_relat_1(sK8,X0) != iProver_top
% 11.57/1.99      | r2_hidden(X1,sK5) != iProver_top
% 11.57/1.99      | v1_funct_1(sK8) != iProver_top
% 11.57/1.99      | v1_relat_1(sK8) != iProver_top
% 11.57/1.99      | v1_xboole_0(k1_relat_1(sK8)) = iProver_top ),
% 11.57/1.99      inference(superposition,[status(thm)],[c_4756,c_22021]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_36,plain,
% 11.57/1.99      ( v1_xboole_0(sK6) != iProver_top ),
% 11.57/1.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_31,negated_conjecture,
% 11.57/1.99      ( v1_funct_1(sK8) ),
% 11.57/1.99      inference(cnf_transformation,[],[f90]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_40,plain,
% 11.57/1.99      ( v1_funct_1(sK8) = iProver_top ),
% 11.57/1.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_1990,plain,( X0 = X0 ),theory(equality) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_2019,plain,
% 11.57/1.99      ( k1_xboole_0 = k1_xboole_0 ),
% 11.57/1.99      inference(instantiation,[status(thm)],[c_1990]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_1991,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_2583,plain,
% 11.57/1.99      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 11.57/1.99      inference(instantiation,[status(thm)],[c_1991]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_2584,plain,
% 11.57/1.99      ( sK5 != k1_xboole_0
% 11.57/1.99      | k1_xboole_0 = sK5
% 11.57/1.99      | k1_xboole_0 != k1_xboole_0 ),
% 11.57/1.99      inference(instantiation,[status(thm)],[c_2583]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_3896,plain,
% 11.57/1.99      ( v1_relat_1(k2_zfmisc_1(sK6,sK4)) != iProver_top
% 11.57/1.99      | v1_relat_1(sK8) = iProver_top ),
% 11.57/1.99      inference(superposition,[status(thm)],[c_2516,c_2529]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_4130,plain,
% 11.57/1.99      ( v1_relat_1(sK8) = iProver_top ),
% 11.57/1.99      inference(superposition,[status(thm)],[c_2526,c_3896]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_0,plain,
% 11.57/1.99      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 11.57/1.99      inference(cnf_transformation,[],[f61]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_2537,plain,
% 11.57/1.99      ( r2_hidden(sK0(X0),X0) = iProver_top
% 11.57/1.99      | v1_xboole_0(X0) = iProver_top ),
% 11.57/1.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_4,plain,
% 11.57/1.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 11.57/1.99      inference(cnf_transformation,[],[f62]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_2533,plain,
% 11.57/1.99      ( r1_tarski(X0,X1) != iProver_top
% 11.57/1.99      | r2_hidden(X2,X0) != iProver_top
% 11.57/1.99      | r2_hidden(X2,X1) = iProver_top ),
% 11.57/1.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_4681,plain,
% 11.57/1.99      ( r2_hidden(X0,k1_relat_1(sK8)) = iProver_top
% 11.57/1.99      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 11.57/1.99      inference(superposition,[status(thm)],[c_4054,c_2533]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_4820,plain,
% 11.57/1.99      ( r2_hidden(sK0(k2_relat_1(sK7)),k1_relat_1(sK8)) = iProver_top
% 11.57/1.99      | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
% 11.57/1.99      inference(superposition,[status(thm)],[c_2537,c_4681]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_2536,plain,
% 11.57/1.99      ( r2_hidden(X0,X1) != iProver_top
% 11.57/1.99      | v1_xboole_0(X1) != iProver_top ),
% 11.57/1.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_5423,plain,
% 11.57/1.99      ( v1_xboole_0(k1_relat_1(sK8)) != iProver_top
% 11.57/1.99      | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
% 11.57/1.99      inference(superposition,[status(thm)],[c_4820,c_2536]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_16,plain,
% 11.57/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.57/1.99      | r2_hidden(sK3(X1,X2,X0),k2_relset_1(X1,X2,X0))
% 11.57/1.99      | v1_xboole_0(X1)
% 11.57/1.99      | v1_xboole_0(X2)
% 11.57/1.99      | k1_relset_1(X1,X2,X0) = k1_xboole_0 ),
% 11.57/1.99      inference(cnf_transformation,[],[f77]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_2521,plain,
% 11.57/1.99      ( k1_relset_1(X0,X1,X2) = k1_xboole_0
% 11.57/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.57/1.99      | r2_hidden(sK3(X0,X1,X2),k2_relset_1(X0,X1,X2)) = iProver_top
% 11.57/1.99      | v1_xboole_0(X1) = iProver_top
% 11.57/1.99      | v1_xboole_0(X0) = iProver_top ),
% 11.57/1.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_4436,plain,
% 11.57/1.99      ( k1_relset_1(X0,X1,X2) = k1_xboole_0
% 11.57/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.57/1.99      | v1_xboole_0(X1) = iProver_top
% 11.57/1.99      | v1_xboole_0(X0) = iProver_top
% 11.57/1.99      | v1_xboole_0(k2_relset_1(X0,X1,X2)) != iProver_top ),
% 11.57/1.99      inference(superposition,[status(thm)],[c_2521,c_2536]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_12117,plain,
% 11.57/1.99      ( k1_relset_1(sK5,sK6,sK7) = k1_xboole_0
% 11.57/1.99      | v1_xboole_0(k2_relset_1(sK5,sK6,sK7)) != iProver_top
% 11.57/1.99      | v1_xboole_0(sK6) = iProver_top
% 11.57/1.99      | v1_xboole_0(sK5) = iProver_top ),
% 11.57/1.99      inference(superposition,[status(thm)],[c_2514,c_4436]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_12120,plain,
% 11.57/1.99      ( k1_relset_1(sK5,sK6,sK7) = k1_xboole_0
% 11.57/1.99      | v1_xboole_0(k2_relat_1(sK7)) != iProver_top
% 11.57/1.99      | v1_xboole_0(sK6) = iProver_top
% 11.57/1.99      | v1_xboole_0(sK5) = iProver_top ),
% 11.57/1.99      inference(light_normalisation,[status(thm)],[c_12117,c_3607]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_4230,plain,
% 11.57/1.99      ( k1_relset_1(sK5,sK6,sK7) = sK5 ),
% 11.57/1.99      inference(demodulation,[status(thm)],[c_4228,c_3802]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_12121,plain,
% 11.57/1.99      ( sK5 = k1_xboole_0
% 11.57/1.99      | v1_xboole_0(k2_relat_1(sK7)) != iProver_top
% 11.57/1.99      | v1_xboole_0(sK6) = iProver_top
% 11.57/1.99      | v1_xboole_0(sK5) = iProver_top ),
% 11.57/1.99      inference(demodulation,[status(thm)],[c_12120,c_4230]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_28517,plain,
% 11.57/1.99      ( r2_hidden(X1,sK5) != iProver_top
% 11.57/1.99      | v5_relat_1(sK8,X0) != iProver_top
% 11.57/1.99      | k7_partfun1(X0,sK8,k1_funct_1(sK7,X1)) = k1_funct_1(sK8,k1_funct_1(sK7,X1)) ),
% 11.57/1.99      inference(global_propositional_subsumption,
% 11.57/1.99                [status(thm)],
% 11.57/1.99                [c_22027,c_36,c_40,c_27,c_2019,c_2581,c_2584,c_2622,
% 11.57/1.99                 c_4130,c_5423,c_12121]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_28518,plain,
% 11.57/1.99      ( k7_partfun1(X0,sK8,k1_funct_1(sK7,X1)) = k1_funct_1(sK8,k1_funct_1(sK7,X1))
% 11.57/1.99      | v5_relat_1(sK8,X0) != iProver_top
% 11.57/1.99      | r2_hidden(X1,sK5) != iProver_top ),
% 11.57/1.99      inference(renaming,[status(thm)],[c_28517]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_28526,plain,
% 11.57/1.99      ( k7_partfun1(X0,sK8,k1_funct_1(sK7,sK9)) = k1_funct_1(sK8,k1_funct_1(sK7,sK9))
% 11.57/1.99      | v5_relat_1(sK8,X0) != iProver_top ),
% 11.57/1.99      inference(superposition,[status(thm)],[c_4257,c_28518]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_28636,plain,
% 11.57/1.99      ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) = k1_funct_1(sK8,k1_funct_1(sK7,sK9)) ),
% 11.57/1.99      inference(superposition,[status(thm)],[c_3343,c_28526]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_25,plain,
% 11.57/1.99      ( ~ v1_funct_2(X0,X1,X2)
% 11.57/1.99      | ~ m1_subset_1(X3,X1)
% 11.57/1.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 11.57/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.57/1.99      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X5,X4))
% 11.57/1.99      | ~ v1_funct_1(X4)
% 11.57/1.99      | ~ v1_funct_1(X0)
% 11.57/1.99      | v1_xboole_0(X2)
% 11.57/1.99      | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 11.57/1.99      | k1_xboole_0 = X1 ),
% 11.57/1.99      inference(cnf_transformation,[],[f85]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_866,plain,
% 11.57/1.99      ( ~ m1_subset_1(X0,X1)
% 11.57/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 11.57/1.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X5)))
% 11.57/1.99      | ~ r1_tarski(k2_relset_1(X1,X3,X2),k1_relset_1(X3,X5,X4))
% 11.57/1.99      | ~ v1_funct_1(X2)
% 11.57/1.99      | ~ v1_funct_1(X4)
% 11.57/1.99      | v1_xboole_0(X3)
% 11.57/1.99      | k1_funct_1(k8_funct_2(X1,X3,X5,X2,X4),X0) = k1_funct_1(X4,k1_funct_1(X2,X0))
% 11.57/1.99      | sK7 != X2
% 11.57/1.99      | sK6 != X3
% 11.57/1.99      | sK5 != X1
% 11.57/1.99      | k1_xboole_0 = X1 ),
% 11.57/1.99      inference(resolution_lifted,[status(thm)],[c_25,c_33]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_867,plain,
% 11.57/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,X1)))
% 11.57/1.99      | ~ m1_subset_1(X2,sK5)
% 11.57/1.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 11.57/1.99      | ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,X1,X0))
% 11.57/1.99      | ~ v1_funct_1(X0)
% 11.57/1.99      | ~ v1_funct_1(sK7)
% 11.57/1.99      | v1_xboole_0(sK6)
% 11.57/1.99      | k1_funct_1(k8_funct_2(sK5,sK6,X1,sK7,X0),X2) = k1_funct_1(X0,k1_funct_1(sK7,X2))
% 11.57/1.99      | k1_xboole_0 = sK5 ),
% 11.57/1.99      inference(unflattening,[status(thm)],[c_866]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_871,plain,
% 11.57/1.99      ( k1_funct_1(k8_funct_2(sK5,sK6,X1,sK7,X0),X2) = k1_funct_1(X0,k1_funct_1(sK7,X2))
% 11.57/1.99      | ~ v1_funct_1(X0)
% 11.57/1.99      | ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,X1,X0))
% 11.57/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,X1)))
% 11.57/1.99      | ~ m1_subset_1(X2,sK5) ),
% 11.57/1.99      inference(global_propositional_subsumption,
% 11.57/1.99                [status(thm)],
% 11.57/1.99                [c_867,c_35,c_34,c_32,c_27]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_872,plain,
% 11.57/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,X1)))
% 11.57/1.99      | ~ m1_subset_1(X2,sK5)
% 11.57/1.99      | ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,X1,X0))
% 11.57/1.99      | ~ v1_funct_1(X0)
% 11.57/1.99      | k1_funct_1(k8_funct_2(sK5,sK6,X1,sK7,X0),X2) = k1_funct_1(X0,k1_funct_1(sK7,X2)) ),
% 11.57/1.99      inference(renaming,[status(thm)],[c_871]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_2609,plain,
% 11.57/1.99      ( ~ m1_subset_1(X0,sK5)
% 11.57/1.99      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,X1)))
% 11.57/1.99      | ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,X1,sK8))
% 11.57/1.99      | ~ v1_funct_1(sK8)
% 11.57/1.99      | k1_funct_1(k8_funct_2(sK5,sK6,X1,sK7,sK8),X0) = k1_funct_1(sK8,k1_funct_1(sK7,X0)) ),
% 11.57/1.99      inference(instantiation,[status(thm)],[c_872]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_2647,plain,
% 11.57/1.99      ( ~ m1_subset_1(sK9,sK5)
% 11.57/1.99      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,X0)))
% 11.57/1.99      | ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,X0,sK8))
% 11.57/1.99      | ~ v1_funct_1(sK8)
% 11.57/1.99      | k1_funct_1(k8_funct_2(sK5,sK6,X0,sK7,sK8),sK9) = k1_funct_1(sK8,k1_funct_1(sK7,sK9)) ),
% 11.57/1.99      inference(instantiation,[status(thm)],[c_2609]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_2764,plain,
% 11.57/1.99      ( ~ m1_subset_1(sK9,sK5)
% 11.57/1.99      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
% 11.57/1.99      | ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8))
% 11.57/1.99      | ~ v1_funct_1(sK8)
% 11.57/1.99      | k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) = k1_funct_1(sK8,k1_funct_1(sK7,sK9)) ),
% 11.57/1.99      inference(instantiation,[status(thm)],[c_2647]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_2578,plain,
% 11.57/1.99      ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != X0
% 11.57/1.99      | k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != X0
% 11.57/1.99      | k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) = k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) ),
% 11.57/1.99      inference(instantiation,[status(thm)],[c_1991]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_2626,plain,
% 11.57/1.99      ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(sK8,k1_funct_1(sK7,sK9))
% 11.57/1.99      | k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) = k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9))
% 11.57/1.99      | k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k1_funct_1(sK8,k1_funct_1(sK7,sK9)) ),
% 11.57/1.99      inference(instantiation,[status(thm)],[c_2578]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(c_26,negated_conjecture,
% 11.57/1.99      ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) ),
% 11.57/1.99      inference(cnf_transformation,[],[f95]) ).
% 11.57/1.99  
% 11.57/1.99  cnf(contradiction,plain,
% 11.57/1.99      ( $false ),
% 11.57/1.99      inference(minisat,
% 11.57/1.99                [status(thm)],
% 11.57/1.99                [c_28636,c_2764,c_2626,c_26,c_28,c_29,c_30,c_31]) ).
% 11.57/1.99  
% 11.57/1.99  
% 11.57/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.57/1.99  
% 11.57/1.99  ------                               Statistics
% 11.57/1.99  
% 11.57/1.99  ------ General
% 11.57/1.99  
% 11.57/1.99  abstr_ref_over_cycles:                  0
% 11.57/1.99  abstr_ref_under_cycles:                 0
% 11.57/1.99  gc_basic_clause_elim:                   0
% 11.57/1.99  forced_gc_time:                         0
% 11.57/1.99  parsing_time:                           0.01
% 11.57/1.99  unif_index_cands_time:                  0.
% 11.57/1.99  unif_index_add_time:                    0.
% 11.57/1.99  orderings_time:                         0.
% 11.57/1.99  out_proof_time:                         0.014
% 11.57/1.99  total_time:                             1.022
% 11.57/1.99  num_of_symbols:                         59
% 11.57/1.99  num_of_terms:                           28541
% 11.57/1.99  
% 11.57/1.99  ------ Preprocessing
% 11.57/1.99  
% 11.57/1.99  num_of_splits:                          0
% 11.57/1.99  num_of_split_atoms:                     0
% 11.57/1.99  num_of_reused_defs:                     0
% 11.57/1.99  num_eq_ax_congr_red:                    33
% 11.57/1.99  num_of_sem_filtered_clauses:            1
% 11.57/1.99  num_of_subtypes:                        0
% 11.57/1.99  monotx_restored_types:                  0
% 11.57/1.99  sat_num_of_epr_types:                   0
% 11.57/1.99  sat_num_of_non_cyclic_types:            0
% 11.57/1.99  sat_guarded_non_collapsed_types:        0
% 11.57/1.99  num_pure_diseq_elim:                    0
% 11.57/1.99  simp_replaced_by:                       0
% 11.57/1.99  res_preprocessed:                       166
% 11.57/1.99  prep_upred:                             0
% 11.57/1.99  prep_unflattend:                        88
% 11.57/1.99  smt_new_axioms:                         0
% 11.57/1.99  pred_elim_cands:                        7
% 11.57/1.99  pred_elim:                              1
% 11.57/1.99  pred_elim_cl:                           3
% 11.57/1.99  pred_elim_cycles:                       6
% 11.57/1.99  merged_defs:                            0
% 11.57/1.99  merged_defs_ncl:                        0
% 11.57/1.99  bin_hyper_res:                          0
% 11.57/1.99  prep_cycles:                            4
% 11.57/1.99  pred_elim_time:                         0.032
% 11.57/1.99  splitting_time:                         0.
% 11.57/1.99  sem_filter_time:                        0.
% 11.57/1.99  monotx_time:                            0.001
% 11.57/1.99  subtype_inf_time:                       0.
% 11.57/1.99  
% 11.57/1.99  ------ Problem properties
% 11.57/1.99  
% 11.57/1.99  clauses:                                33
% 11.57/1.99  conjectures:                            9
% 11.57/1.99  epr:                                    9
% 11.57/1.99  horn:                                   25
% 11.57/1.99  ground:                                 13
% 11.57/1.99  unary:                                  11
% 11.57/1.99  binary:                                 9
% 11.57/1.99  lits:                                   86
% 11.57/1.99  lits_eq:                                19
% 11.57/1.99  fd_pure:                                0
% 11.57/1.99  fd_pseudo:                              0
% 11.57/1.99  fd_cond:                                2
% 11.57/1.99  fd_pseudo_cond:                         0
% 11.57/1.99  ac_symbols:                             0
% 11.57/1.99  
% 11.57/1.99  ------ Propositional Solver
% 11.57/1.99  
% 11.57/1.99  prop_solver_calls:                      34
% 11.57/1.99  prop_fast_solver_calls:                 3023
% 11.57/1.99  smt_solver_calls:                       0
% 11.57/1.99  smt_fast_solver_calls:                  0
% 11.57/1.99  prop_num_of_clauses:                    13214
% 11.57/1.99  prop_preprocess_simplified:             16986
% 11.57/1.99  prop_fo_subsumed:                       241
% 11.57/1.99  prop_solver_time:                       0.
% 11.57/1.99  smt_solver_time:                        0.
% 11.57/1.99  smt_fast_solver_time:                   0.
% 11.57/1.99  prop_fast_solver_time:                  0.
% 11.57/1.99  prop_unsat_core_time:                   0.001
% 11.57/1.99  
% 11.57/1.99  ------ QBF
% 11.57/1.99  
% 11.57/1.99  qbf_q_res:                              0
% 11.57/1.99  qbf_num_tautologies:                    0
% 11.57/1.99  qbf_prep_cycles:                        0
% 11.57/1.99  
% 11.57/1.99  ------ BMC1
% 11.57/1.99  
% 11.57/1.99  bmc1_current_bound:                     -1
% 11.57/1.99  bmc1_last_solved_bound:                 -1
% 11.57/1.99  bmc1_unsat_core_size:                   -1
% 11.57/1.99  bmc1_unsat_core_parents_size:           -1
% 11.57/1.99  bmc1_merge_next_fun:                    0
% 11.57/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.57/1.99  
% 11.57/1.99  ------ Instantiation
% 11.57/1.99  
% 11.57/1.99  inst_num_of_clauses:                    3398
% 11.57/1.99  inst_num_in_passive:                    562
% 11.57/1.99  inst_num_in_active:                     1562
% 11.57/1.99  inst_num_in_unprocessed:                1274
% 11.57/1.99  inst_num_of_loops:                      1920
% 11.57/1.99  inst_num_of_learning_restarts:          0
% 11.57/1.99  inst_num_moves_active_passive:          351
% 11.57/1.99  inst_lit_activity:                      0
% 11.57/1.99  inst_lit_activity_moves:                0
% 11.57/1.99  inst_num_tautologies:                   0
% 11.57/1.99  inst_num_prop_implied:                  0
% 11.57/1.99  inst_num_existing_simplified:           0
% 11.57/1.99  inst_num_eq_res_simplified:             0
% 11.57/1.99  inst_num_child_elim:                    0
% 11.57/1.99  inst_num_of_dismatching_blockings:      1185
% 11.57/1.99  inst_num_of_non_proper_insts:           2946
% 11.57/1.99  inst_num_of_duplicates:                 0
% 11.57/1.99  inst_inst_num_from_inst_to_res:         0
% 11.57/1.99  inst_dismatching_checking_time:         0.
% 11.57/1.99  
% 11.57/1.99  ------ Resolution
% 11.57/1.99  
% 11.57/1.99  res_num_of_clauses:                     0
% 11.57/1.99  res_num_in_passive:                     0
% 11.57/1.99  res_num_in_active:                      0
% 11.57/1.99  res_num_of_loops:                       170
% 11.57/1.99  res_forward_subset_subsumed:            262
% 11.57/1.99  res_backward_subset_subsumed:           2
% 11.57/1.99  res_forward_subsumed:                   0
% 11.57/1.99  res_backward_subsumed:                  0
% 11.57/1.99  res_forward_subsumption_resolution:     0
% 11.57/1.99  res_backward_subsumption_resolution:    0
% 11.57/1.99  res_clause_to_clause_subsumption:       5926
% 11.57/1.99  res_orphan_elimination:                 0
% 11.57/1.99  res_tautology_del:                      463
% 11.57/1.99  res_num_eq_res_simplified:              0
% 11.57/1.99  res_num_sel_changes:                    0
% 11.57/1.99  res_moves_from_active_to_pass:          0
% 11.57/1.99  
% 11.57/1.99  ------ Superposition
% 11.57/1.99  
% 11.57/1.99  sup_time_total:                         0.
% 11.57/1.99  sup_time_generating:                    0.
% 11.57/1.99  sup_time_sim_full:                      0.
% 11.57/1.99  sup_time_sim_immed:                     0.
% 11.57/1.99  
% 11.57/1.99  sup_num_of_clauses:                     1499
% 11.57/1.99  sup_num_in_active:                      328
% 11.57/1.99  sup_num_in_passive:                     1171
% 11.57/1.99  sup_num_of_loops:                       383
% 11.57/1.99  sup_fw_superposition:                   1199
% 11.57/1.99  sup_bw_superposition:                   1015
% 11.57/1.99  sup_immediate_simplified:               590
% 11.57/1.99  sup_given_eliminated:                   0
% 11.57/1.99  comparisons_done:                       0
% 11.57/1.99  comparisons_avoided:                    444
% 11.57/1.99  
% 11.57/1.99  ------ Simplifications
% 11.57/1.99  
% 11.57/1.99  
% 11.57/1.99  sim_fw_subset_subsumed:                 173
% 11.57/1.99  sim_bw_subset_subsumed:                 110
% 11.57/1.99  sim_fw_subsumed:                        225
% 11.57/1.99  sim_bw_subsumed:                        162
% 11.57/1.99  sim_fw_subsumption_res:                 0
% 11.57/1.99  sim_bw_subsumption_res:                 0
% 11.57/1.99  sim_tautology_del:                      12
% 11.57/1.99  sim_eq_tautology_del:                   9
% 11.57/1.99  sim_eq_res_simp:                        0
% 11.57/1.99  sim_fw_demodulated:                     16
% 11.57/1.99  sim_bw_demodulated:                     7
% 11.57/1.99  sim_light_normalised:                   52
% 11.57/1.99  sim_joinable_taut:                      0
% 11.57/1.99  sim_joinable_simp:                      0
% 11.57/1.99  sim_ac_normalised:                      0
% 11.57/1.99  sim_smt_subsumption:                    0
% 11.57/1.99  
%------------------------------------------------------------------------------
