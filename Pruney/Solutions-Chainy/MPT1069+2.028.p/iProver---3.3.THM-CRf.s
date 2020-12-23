%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:47 EST 2020

% Result     : Theorem 7.24s
% Output     : CNFRefutation 7.24s
% Verified   : 
% Statistics : Number of formulae       :  252 (4781 expanded)
%              Number of clauses        :  159 (1387 expanded)
%              Number of leaves         :   27 (1537 expanded)
%              Depth                    :   23
%              Number of atoms          :  840 (33763 expanded)
%              Number of equality atoms :  367 (9271 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
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

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

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
    inference(ennf_transformation,[],[f19])).

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

fof(f58,plain,(
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
            ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK6),X5) != k7_partfun1(X0,sK6,k1_funct_1(X3,X5))
            & k1_xboole_0 != X1
            & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK6))
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        & v1_funct_1(sK6) ) ) ),
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

fof(f59,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f41,f58,f57,f56,f55])).

fof(f96,plain,(
    m1_subset_1(sK7,sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f98,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f59])).

fof(f3,axiom,(
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
    inference(nnf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f50])).

fof(f67,plain,(
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

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f20])).

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

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

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

fof(f60,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f93,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f59])).

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

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

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
    inference(nnf_transformation,[],[f31])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f92,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f95,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f59])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f97,plain,(
    r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
    inference(cnf_transformation,[],[f59])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f91,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f59])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f94,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f59])).

fof(f17,axiom,(
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
    inference(ennf_transformation,[],[f17])).

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

fof(f89,plain,(
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

fof(f90,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f99,plain,(
    k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) ),
    inference(cnf_transformation,[],[f59])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f104,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f84])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f100,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f66])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK7,sK3) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2977,plain,
    ( m1_subset_1(sK7,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2994,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4750,plain,
    ( r2_hidden(sK7,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2977,c_2994])).

cnf(c_46,plain,
    ( m1_subset_1(sK7,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_31,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3305,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK3)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3306,plain,
    ( k1_xboole_0 = sK3
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3305])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_3432,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | r2_hidden(sK1(sK3,k1_xboole_0),sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3439,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top
    | r2_hidden(sK1(sK3,k1_xboole_0),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3432])).

cnf(c_8,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3704,plain,
    ( r1_tarski(k1_xboole_0,sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3705,plain,
    ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3704])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_4006,plain,
    ( ~ r2_hidden(sK1(sK3,k1_xboole_0),sK3)
    | ~ v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4007,plain,
    ( r2_hidden(sK1(sK3,k1_xboole_0),sK3) != iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4006])).

cnf(c_4715,plain,
    ( ~ m1_subset_1(sK7,sK3)
    | r2_hidden(sK7,sK3)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_4716,plain,
    ( m1_subset_1(sK7,sK3) != iProver_top
    | r2_hidden(sK7,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4715])).

cnf(c_5218,plain,
    ( r2_hidden(sK7,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4750,c_46,c_31,c_3306,c_3439,c_3705,c_4007,c_4716])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2974,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2982,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_6427,plain,
    ( k1_relset_1(sK3,sK4,sK5) = sK3
    | sK4 = k1_xboole_0
    | v1_funct_2(sK5,sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2974,c_2982])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2989,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4649,plain,
    ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_2974,c_2989])).

cnf(c_6431,plain,
    ( k1_relat_1(sK5) = sK3
    | sK4 = k1_xboole_0
    | v1_funct_2(sK5,sK3,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6427,c_4649])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_42,plain,
    ( v1_funct_2(sK5,sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_6830,plain,
    ( sK4 = k1_xboole_0
    | k1_relat_1(sK5) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6431,c_42])).

cnf(c_6831,plain,
    ( k1_relat_1(sK5) = sK3
    | sK4 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_6830])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2991,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2976,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_4648,plain,
    ( k1_relset_1(sK4,sK2,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_2976,c_2989])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2988,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4063,plain,
    ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_2974,c_2988])).

cnf(c_32,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2978,plain,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_4293,plain,
    ( r1_tarski(k2_relat_1(sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4063,c_2978])).

cnf(c_5044,plain,
    ( r1_tarski(k2_relat_1(sK5),k1_relat_1(sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4648,c_4293])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2998,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5417,plain,
    ( r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5044,c_2998])).

cnf(c_10037,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2991,c_5417])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_41,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_43,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3277,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_3278,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3277])).

cnf(c_25361,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10037,c_41,c_43,c_3278])).

cnf(c_16,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_26,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_495,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(resolution,[status(thm)],[c_16,c_26])).

cnf(c_499,plain,
    ( ~ v1_funct_1(X0)
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_495,c_15])).

cnf(c_500,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(renaming,[status(thm)],[c_499])).

cnf(c_2970,plain,
    ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_500])).

cnf(c_3960,plain,
    ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2976,c_2970])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_44,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_4379,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3960,c_44])).

cnf(c_4380,plain,
    ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4379])).

cnf(c_25372,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_25361,c_4380])).

cnf(c_25802,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | sK4 = k1_xboole_0
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6831,c_25372])).

cnf(c_26295,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) = k1_funct_1(sK6,k1_funct_1(sK5,sK7))
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5218,c_25802])).

cnf(c_29,plain,
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
    inference(cnf_transformation,[],[f89])).

cnf(c_2979,plain,
    ( k1_funct_1(k8_funct_2(X0,X1,X2,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
    | k1_xboole_0 = X0
    | v1_funct_2(X3,X0,X1) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4596,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,X0,sK5,X1),X2) = k1_funct_1(X1,k1_funct_1(sK5,X2))
    | sK3 = k1_xboole_0
    | v1_funct_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
    | m1_subset_1(X2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | r1_tarski(k2_relat_1(sK5),k1_relset_1(sK4,X0,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4063,c_2979])).

cnf(c_39,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_40,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_112,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_117,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2169,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3325,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_2169])).

cnf(c_3326,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3325])).

cnf(c_8681,plain,
    ( m1_subset_1(X2,sK3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
    | k1_funct_1(k8_funct_2(sK3,sK4,X0,sK5,X1),X2) = k1_funct_1(X1,k1_funct_1(sK5,X2))
    | r1_tarski(k2_relat_1(sK5),k1_relset_1(sK4,X0,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4596,c_40,c_41,c_42,c_43,c_31,c_112,c_117,c_3326])).

cnf(c_8682,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,X0,sK5,X1),X2) = k1_funct_1(X1,k1_funct_1(sK5,X2))
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
    | m1_subset_1(X2,sK3) != iProver_top
    | r1_tarski(k2_relat_1(sK5),k1_relset_1(sK4,X0,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_8681])).

cnf(c_8693,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | m1_subset_1(X0,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | r1_tarski(k2_relat_1(sK5),k1_relat_1(sK6)) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4648,c_8682])).

cnf(c_45,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_8721,plain,
    ( m1_subset_1(X0,sK3) != iProver_top
    | k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8693,c_44,c_45,c_5044])).

cnf(c_8722,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | m1_subset_1(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_8721])).

cnf(c_8730,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) = k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
    inference(superposition,[status(thm)],[c_2977,c_8722])).

cnf(c_30,negated_conjecture,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_8970,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
    inference(demodulation,[status(thm)],[c_8730,c_30])).

cnf(c_26419,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_26295,c_8970])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2980,plain,
    ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5716,plain,
    ( k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0)
    | v1_funct_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(X0,sK3) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2974,c_2980])).

cnf(c_1109,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X2)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
    | sK5 != X2
    | sK4 != X3
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_37])).

cnf(c_1110,plain,
    ( ~ m1_subset_1(X0,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK3)
    | k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0) ),
    inference(unflattening,[status(thm)],[c_1109])).

cnf(c_1114,plain,
    ( ~ m1_subset_1(X0,sK3)
    | v1_xboole_0(sK3)
    | k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1110,c_38,c_36])).

cnf(c_1116,plain,
    ( k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0)
    | m1_subset_1(X0,sK3) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1114])).

cnf(c_5897,plain,
    ( k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0)
    | m1_subset_1(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5716,c_31,c_1116,c_3306,c_3439,c_3705,c_4007])).

cnf(c_5905,plain,
    ( k3_funct_2(sK3,sK4,sK5,sK7) = k1_funct_1(sK5,sK7) ),
    inference(superposition,[status(thm)],[c_2977,c_5897])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2981,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X3,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_6211,plain,
    ( v1_funct_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(k1_funct_1(sK5,sK7),sK4) = iProver_top
    | m1_subset_1(sK7,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5905,c_2981])).

cnf(c_7651,plain,
    ( m1_subset_1(k1_funct_1(sK5,sK7),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6211,c_41,c_42,c_43,c_46,c_31,c_3306,c_3439,c_3705,c_4007])).

cnf(c_7656,plain,
    ( r2_hidden(k1_funct_1(sK5,sK7),sK4) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_7651,c_2994])).

cnf(c_9729,plain,
    ( r2_hidden(k1_funct_1(sK5,sK7),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7656,c_40])).

cnf(c_26479,plain,
    ( r2_hidden(k1_funct_1(sK5,sK7),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_26419,c_9729])).

cnf(c_26513,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_26419,c_2974])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_2986,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_27415,plain,
    ( sK5 = k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_funct_2(sK5,sK3,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_26513,c_2986])).

cnf(c_3315,plain,
    ( ~ v1_funct_2(X0,sK3,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_3563,plain,
    ( ~ v1_funct_2(sK5,sK3,k1_xboole_0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_3315])).

cnf(c_3567,plain,
    ( k1_xboole_0 = sK5
    | k1_xboole_0 = sK3
    | v1_funct_2(sK5,sK3,k1_xboole_0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3563])).

cnf(c_2168,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3572,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_2168])).

cnf(c_3892,plain,
    ( X0 != X1
    | X0 = sK4
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_2169])).

cnf(c_3893,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3892])).

cnf(c_3521,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4222,plain,
    ( ~ r1_tarski(sK3,sK3)
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_3521])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_4223,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3927,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_2169])).

cnf(c_5266,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_3927])).

cnf(c_5267,plain,
    ( sK5 != sK5
    | sK5 = k1_xboole_0
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_5266])).

cnf(c_2180,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_3385,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK5,sK3,sK4)
    | X0 != sK5
    | X2 != sK4
    | X1 != sK3 ),
    inference(instantiation,[status(thm)],[c_2180])).

cnf(c_3571,plain,
    ( v1_funct_2(sK5,X0,X1)
    | ~ v1_funct_2(sK5,sK3,sK4)
    | X1 != sK4
    | X0 != sK3
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_3385])).

cnf(c_6519,plain,
    ( v1_funct_2(sK5,sK3,X0)
    | ~ v1_funct_2(sK5,sK3,sK4)
    | X0 != sK4
    | sK5 != sK5
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3571])).

cnf(c_6521,plain,
    ( X0 != sK4
    | sK5 != sK5
    | sK3 != sK3
    | v1_funct_2(sK5,sK3,X0) = iProver_top
    | v1_funct_2(sK5,sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6519])).

cnf(c_6523,plain,
    ( sK5 != sK5
    | sK3 != sK3
    | k1_xboole_0 != sK4
    | v1_funct_2(sK5,sK3,sK4) != iProver_top
    | v1_funct_2(sK5,sK3,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6521])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_3269,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_19407,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
    | ~ r1_tarski(sK5,k2_zfmisc_1(sK3,X0)) ),
    inference(instantiation,[status(thm)],[c_3269])).

cnf(c_19408,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r1_tarski(sK5,k2_zfmisc_1(sK3,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19407])).

cnf(c_19410,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top
    | r1_tarski(sK5,k2_zfmisc_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_19408])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2992,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3712,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2974,c_2992])).

cnf(c_26509,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK3,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_26419,c_3712])).

cnf(c_27874,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_27415,c_42,c_31,c_112,c_117,c_3567,c_3572,c_3893,c_4222,c_4223,c_5267,c_6523,c_8970,c_19410,c_26295,c_26509])).

cnf(c_32535,plain,
    ( r2_hidden(k1_funct_1(k1_xboole_0,sK7),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_26479,c_27874])).

cnf(c_17,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_13,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_523,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_17,c_13])).

cnf(c_527,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_523,c_15])).

cnf(c_528,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_527])).

cnf(c_2969,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_528])).

cnf(c_3450,plain,
    ( r1_tarski(k1_relat_1(sK6),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2976,c_2969])).

cnf(c_26511,plain,
    ( r1_tarski(k1_relat_1(sK6),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_26419,c_3450])).

cnf(c_2995,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2997,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4782,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2995,c_2997])).

cnf(c_28342,plain,
    ( k1_relat_1(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_26511,c_4782])).

cnf(c_32220,plain,
    ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_28342,c_4380])).

cnf(c_32539,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(k1_xboole_0,sK7)) = k1_funct_1(sK6,k1_funct_1(k1_xboole_0,sK7)) ),
    inference(superposition,[status(thm)],[c_32535,c_32220])).

cnf(c_27911,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(k1_xboole_0,sK7)) != k1_funct_1(sK6,k1_funct_1(k1_xboole_0,sK7)) ),
    inference(demodulation,[status(thm)],[c_27874,c_8970])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_32539,c_27911])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:15:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.24/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.24/1.49  
% 7.24/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.24/1.49  
% 7.24/1.49  ------  iProver source info
% 7.24/1.49  
% 7.24/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.24/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.24/1.49  git: non_committed_changes: false
% 7.24/1.49  git: last_make_outside_of_git: false
% 7.24/1.49  
% 7.24/1.49  ------ 
% 7.24/1.49  
% 7.24/1.49  ------ Input Options
% 7.24/1.49  
% 7.24/1.49  --out_options                           all
% 7.24/1.49  --tptp_safe_out                         true
% 7.24/1.49  --problem_path                          ""
% 7.24/1.49  --include_path                          ""
% 7.24/1.49  --clausifier                            res/vclausify_rel
% 7.24/1.49  --clausifier_options                    --mode clausify
% 7.24/1.49  --stdin                                 false
% 7.24/1.49  --stats_out                             all
% 7.24/1.49  
% 7.24/1.49  ------ General Options
% 7.24/1.49  
% 7.24/1.49  --fof                                   false
% 7.24/1.49  --time_out_real                         305.
% 7.24/1.49  --time_out_virtual                      -1.
% 7.24/1.49  --symbol_type_check                     false
% 7.24/1.49  --clausify_out                          false
% 7.24/1.49  --sig_cnt_out                           false
% 7.24/1.49  --trig_cnt_out                          false
% 7.24/1.49  --trig_cnt_out_tolerance                1.
% 7.24/1.49  --trig_cnt_out_sk_spl                   false
% 7.24/1.49  --abstr_cl_out                          false
% 7.24/1.49  
% 7.24/1.49  ------ Global Options
% 7.24/1.49  
% 7.24/1.49  --schedule                              default
% 7.24/1.49  --add_important_lit                     false
% 7.24/1.49  --prop_solver_per_cl                    1000
% 7.24/1.49  --min_unsat_core                        false
% 7.24/1.49  --soft_assumptions                      false
% 7.24/1.49  --soft_lemma_size                       3
% 7.24/1.49  --prop_impl_unit_size                   0
% 7.24/1.49  --prop_impl_unit                        []
% 7.24/1.49  --share_sel_clauses                     true
% 7.24/1.49  --reset_solvers                         false
% 7.24/1.49  --bc_imp_inh                            [conj_cone]
% 7.24/1.49  --conj_cone_tolerance                   3.
% 7.24/1.49  --extra_neg_conj                        none
% 7.24/1.49  --large_theory_mode                     true
% 7.24/1.49  --prolific_symb_bound                   200
% 7.24/1.49  --lt_threshold                          2000
% 7.24/1.49  --clause_weak_htbl                      true
% 7.24/1.49  --gc_record_bc_elim                     false
% 7.24/1.49  
% 7.24/1.49  ------ Preprocessing Options
% 7.24/1.49  
% 7.24/1.49  --preprocessing_flag                    true
% 7.24/1.49  --time_out_prep_mult                    0.1
% 7.24/1.49  --splitting_mode                        input
% 7.24/1.49  --splitting_grd                         true
% 7.24/1.49  --splitting_cvd                         false
% 7.24/1.49  --splitting_cvd_svl                     false
% 7.24/1.49  --splitting_nvd                         32
% 7.24/1.49  --sub_typing                            true
% 7.24/1.49  --prep_gs_sim                           true
% 7.24/1.49  --prep_unflatten                        true
% 7.24/1.49  --prep_res_sim                          true
% 7.24/1.49  --prep_upred                            true
% 7.24/1.49  --prep_sem_filter                       exhaustive
% 7.24/1.49  --prep_sem_filter_out                   false
% 7.24/1.49  --pred_elim                             true
% 7.24/1.49  --res_sim_input                         true
% 7.24/1.49  --eq_ax_congr_red                       true
% 7.24/1.49  --pure_diseq_elim                       true
% 7.24/1.49  --brand_transform                       false
% 7.24/1.49  --non_eq_to_eq                          false
% 7.24/1.49  --prep_def_merge                        true
% 7.24/1.49  --prep_def_merge_prop_impl              false
% 7.24/1.49  --prep_def_merge_mbd                    true
% 7.24/1.49  --prep_def_merge_tr_red                 false
% 7.24/1.49  --prep_def_merge_tr_cl                  false
% 7.24/1.49  --smt_preprocessing                     true
% 7.24/1.49  --smt_ac_axioms                         fast
% 7.24/1.49  --preprocessed_out                      false
% 7.24/1.49  --preprocessed_stats                    false
% 7.24/1.49  
% 7.24/1.49  ------ Abstraction refinement Options
% 7.24/1.49  
% 7.24/1.49  --abstr_ref                             []
% 7.24/1.49  --abstr_ref_prep                        false
% 7.24/1.49  --abstr_ref_until_sat                   false
% 7.24/1.49  --abstr_ref_sig_restrict                funpre
% 7.24/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.24/1.49  --abstr_ref_under                       []
% 7.24/1.49  
% 7.24/1.49  ------ SAT Options
% 7.24/1.49  
% 7.24/1.49  --sat_mode                              false
% 7.24/1.49  --sat_fm_restart_options                ""
% 7.24/1.49  --sat_gr_def                            false
% 7.24/1.49  --sat_epr_types                         true
% 7.24/1.49  --sat_non_cyclic_types                  false
% 7.24/1.49  --sat_finite_models                     false
% 7.24/1.49  --sat_fm_lemmas                         false
% 7.24/1.49  --sat_fm_prep                           false
% 7.24/1.49  --sat_fm_uc_incr                        true
% 7.24/1.49  --sat_out_model                         small
% 7.24/1.49  --sat_out_clauses                       false
% 7.24/1.49  
% 7.24/1.49  ------ QBF Options
% 7.24/1.49  
% 7.24/1.49  --qbf_mode                              false
% 7.24/1.49  --qbf_elim_univ                         false
% 7.24/1.49  --qbf_dom_inst                          none
% 7.24/1.49  --qbf_dom_pre_inst                      false
% 7.24/1.49  --qbf_sk_in                             false
% 7.24/1.49  --qbf_pred_elim                         true
% 7.24/1.49  --qbf_split                             512
% 7.24/1.49  
% 7.24/1.49  ------ BMC1 Options
% 7.24/1.49  
% 7.24/1.49  --bmc1_incremental                      false
% 7.24/1.49  --bmc1_axioms                           reachable_all
% 7.24/1.49  --bmc1_min_bound                        0
% 7.24/1.49  --bmc1_max_bound                        -1
% 7.24/1.49  --bmc1_max_bound_default                -1
% 7.24/1.49  --bmc1_symbol_reachability              true
% 7.24/1.49  --bmc1_property_lemmas                  false
% 7.24/1.49  --bmc1_k_induction                      false
% 7.24/1.49  --bmc1_non_equiv_states                 false
% 7.24/1.49  --bmc1_deadlock                         false
% 7.24/1.49  --bmc1_ucm                              false
% 7.24/1.49  --bmc1_add_unsat_core                   none
% 7.24/1.49  --bmc1_unsat_core_children              false
% 7.24/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.24/1.49  --bmc1_out_stat                         full
% 7.24/1.49  --bmc1_ground_init                      false
% 7.24/1.49  --bmc1_pre_inst_next_state              false
% 7.24/1.49  --bmc1_pre_inst_state                   false
% 7.24/1.49  --bmc1_pre_inst_reach_state             false
% 7.24/1.49  --bmc1_out_unsat_core                   false
% 7.24/1.49  --bmc1_aig_witness_out                  false
% 7.24/1.49  --bmc1_verbose                          false
% 7.24/1.49  --bmc1_dump_clauses_tptp                false
% 7.24/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.24/1.49  --bmc1_dump_file                        -
% 7.24/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.24/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.24/1.49  --bmc1_ucm_extend_mode                  1
% 7.24/1.49  --bmc1_ucm_init_mode                    2
% 7.24/1.49  --bmc1_ucm_cone_mode                    none
% 7.24/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.24/1.49  --bmc1_ucm_relax_model                  4
% 7.24/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.24/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.24/1.49  --bmc1_ucm_layered_model                none
% 7.24/1.49  --bmc1_ucm_max_lemma_size               10
% 7.24/1.49  
% 7.24/1.49  ------ AIG Options
% 7.24/1.49  
% 7.24/1.49  --aig_mode                              false
% 7.24/1.49  
% 7.24/1.49  ------ Instantiation Options
% 7.24/1.49  
% 7.24/1.49  --instantiation_flag                    true
% 7.24/1.49  --inst_sos_flag                         false
% 7.24/1.49  --inst_sos_phase                        true
% 7.24/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.24/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.24/1.49  --inst_lit_sel_side                     num_symb
% 7.24/1.49  --inst_solver_per_active                1400
% 7.24/1.49  --inst_solver_calls_frac                1.
% 7.24/1.49  --inst_passive_queue_type               priority_queues
% 7.24/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.24/1.49  --inst_passive_queues_freq              [25;2]
% 7.24/1.49  --inst_dismatching                      true
% 7.24/1.49  --inst_eager_unprocessed_to_passive     true
% 7.24/1.49  --inst_prop_sim_given                   true
% 7.24/1.49  --inst_prop_sim_new                     false
% 7.24/1.49  --inst_subs_new                         false
% 7.24/1.49  --inst_eq_res_simp                      false
% 7.24/1.49  --inst_subs_given                       false
% 7.24/1.49  --inst_orphan_elimination               true
% 7.24/1.49  --inst_learning_loop_flag               true
% 7.24/1.49  --inst_learning_start                   3000
% 7.24/1.49  --inst_learning_factor                  2
% 7.24/1.49  --inst_start_prop_sim_after_learn       3
% 7.24/1.49  --inst_sel_renew                        solver
% 7.24/1.49  --inst_lit_activity_flag                true
% 7.24/1.49  --inst_restr_to_given                   false
% 7.24/1.49  --inst_activity_threshold               500
% 7.24/1.49  --inst_out_proof                        true
% 7.24/1.49  
% 7.24/1.49  ------ Resolution Options
% 7.24/1.49  
% 7.24/1.49  --resolution_flag                       true
% 7.24/1.49  --res_lit_sel                           adaptive
% 7.24/1.49  --res_lit_sel_side                      none
% 7.24/1.49  --res_ordering                          kbo
% 7.24/1.49  --res_to_prop_solver                    active
% 7.24/1.49  --res_prop_simpl_new                    false
% 7.24/1.49  --res_prop_simpl_given                  true
% 7.24/1.49  --res_passive_queue_type                priority_queues
% 7.24/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.24/1.49  --res_passive_queues_freq               [15;5]
% 7.24/1.49  --res_forward_subs                      full
% 7.24/1.49  --res_backward_subs                     full
% 7.24/1.49  --res_forward_subs_resolution           true
% 7.24/1.49  --res_backward_subs_resolution          true
% 7.24/1.49  --res_orphan_elimination                true
% 7.24/1.49  --res_time_limit                        2.
% 7.24/1.49  --res_out_proof                         true
% 7.24/1.49  
% 7.24/1.49  ------ Superposition Options
% 7.24/1.49  
% 7.24/1.49  --superposition_flag                    true
% 7.24/1.49  --sup_passive_queue_type                priority_queues
% 7.24/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.24/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.24/1.49  --demod_completeness_check              fast
% 7.24/1.49  --demod_use_ground                      true
% 7.24/1.49  --sup_to_prop_solver                    passive
% 7.24/1.49  --sup_prop_simpl_new                    true
% 7.24/1.49  --sup_prop_simpl_given                  true
% 7.24/1.49  --sup_fun_splitting                     false
% 7.24/1.49  --sup_smt_interval                      50000
% 7.24/1.49  
% 7.24/1.49  ------ Superposition Simplification Setup
% 7.24/1.49  
% 7.24/1.49  --sup_indices_passive                   []
% 7.24/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.24/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.24/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.24/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.24/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.24/1.49  --sup_full_bw                           [BwDemod]
% 7.24/1.49  --sup_immed_triv                        [TrivRules]
% 7.24/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.24/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.24/1.49  --sup_immed_bw_main                     []
% 7.24/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.24/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.24/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.24/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.24/1.49  
% 7.24/1.49  ------ Combination Options
% 7.24/1.49  
% 7.24/1.49  --comb_res_mult                         3
% 7.24/1.49  --comb_sup_mult                         2
% 7.24/1.49  --comb_inst_mult                        10
% 7.24/1.49  
% 7.24/1.49  ------ Debug Options
% 7.24/1.49  
% 7.24/1.49  --dbg_backtrace                         false
% 7.24/1.49  --dbg_dump_prop_clauses                 false
% 7.24/1.49  --dbg_dump_prop_clauses_file            -
% 7.24/1.49  --dbg_out_stat                          false
% 7.24/1.49  ------ Parsing...
% 7.24/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.24/1.49  
% 7.24/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.24/1.49  
% 7.24/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.24/1.49  
% 7.24/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.24/1.49  ------ Proving...
% 7.24/1.49  ------ Problem Properties 
% 7.24/1.49  
% 7.24/1.49  
% 7.24/1.49  clauses                                 36
% 7.24/1.49  conjectures                             10
% 7.24/1.49  EPR                                     12
% 7.24/1.49  Horn                                    26
% 7.24/1.49  unary                                   12
% 7.24/1.49  binary                                  10
% 7.24/1.49  lits                                    92
% 7.24/1.49  lits eq                                 18
% 7.24/1.49  fd_pure                                 0
% 7.24/1.49  fd_pseudo                               0
% 7.24/1.49  fd_cond                                 4
% 7.24/1.49  fd_pseudo_cond                          1
% 7.24/1.49  AC symbols                              0
% 7.24/1.49  
% 7.24/1.49  ------ Schedule dynamic 5 is on 
% 7.24/1.49  
% 7.24/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.24/1.49  
% 7.24/1.49  
% 7.24/1.49  ------ 
% 7.24/1.49  Current options:
% 7.24/1.49  ------ 
% 7.24/1.49  
% 7.24/1.49  ------ Input Options
% 7.24/1.49  
% 7.24/1.49  --out_options                           all
% 7.24/1.49  --tptp_safe_out                         true
% 7.24/1.49  --problem_path                          ""
% 7.24/1.49  --include_path                          ""
% 7.24/1.49  --clausifier                            res/vclausify_rel
% 7.24/1.49  --clausifier_options                    --mode clausify
% 7.24/1.49  --stdin                                 false
% 7.24/1.49  --stats_out                             all
% 7.24/1.49  
% 7.24/1.49  ------ General Options
% 7.24/1.49  
% 7.24/1.49  --fof                                   false
% 7.24/1.49  --time_out_real                         305.
% 7.24/1.49  --time_out_virtual                      -1.
% 7.24/1.49  --symbol_type_check                     false
% 7.24/1.49  --clausify_out                          false
% 7.24/1.49  --sig_cnt_out                           false
% 7.24/1.49  --trig_cnt_out                          false
% 7.24/1.49  --trig_cnt_out_tolerance                1.
% 7.24/1.49  --trig_cnt_out_sk_spl                   false
% 7.24/1.49  --abstr_cl_out                          false
% 7.24/1.49  
% 7.24/1.49  ------ Global Options
% 7.24/1.49  
% 7.24/1.49  --schedule                              default
% 7.24/1.49  --add_important_lit                     false
% 7.24/1.49  --prop_solver_per_cl                    1000
% 7.24/1.49  --min_unsat_core                        false
% 7.24/1.49  --soft_assumptions                      false
% 7.24/1.49  --soft_lemma_size                       3
% 7.24/1.49  --prop_impl_unit_size                   0
% 7.24/1.49  --prop_impl_unit                        []
% 7.24/1.49  --share_sel_clauses                     true
% 7.24/1.49  --reset_solvers                         false
% 7.24/1.49  --bc_imp_inh                            [conj_cone]
% 7.24/1.49  --conj_cone_tolerance                   3.
% 7.24/1.49  --extra_neg_conj                        none
% 7.24/1.49  --large_theory_mode                     true
% 7.24/1.49  --prolific_symb_bound                   200
% 7.24/1.49  --lt_threshold                          2000
% 7.24/1.49  --clause_weak_htbl                      true
% 7.24/1.49  --gc_record_bc_elim                     false
% 7.24/1.49  
% 7.24/1.49  ------ Preprocessing Options
% 7.24/1.49  
% 7.24/1.49  --preprocessing_flag                    true
% 7.24/1.49  --time_out_prep_mult                    0.1
% 7.24/1.49  --splitting_mode                        input
% 7.24/1.49  --splitting_grd                         true
% 7.24/1.49  --splitting_cvd                         false
% 7.24/1.49  --splitting_cvd_svl                     false
% 7.24/1.49  --splitting_nvd                         32
% 7.24/1.49  --sub_typing                            true
% 7.24/1.49  --prep_gs_sim                           true
% 7.24/1.49  --prep_unflatten                        true
% 7.24/1.49  --prep_res_sim                          true
% 7.24/1.49  --prep_upred                            true
% 7.24/1.49  --prep_sem_filter                       exhaustive
% 7.24/1.49  --prep_sem_filter_out                   false
% 7.24/1.49  --pred_elim                             true
% 7.24/1.49  --res_sim_input                         true
% 7.24/1.49  --eq_ax_congr_red                       true
% 7.24/1.49  --pure_diseq_elim                       true
% 7.24/1.49  --brand_transform                       false
% 7.24/1.49  --non_eq_to_eq                          false
% 7.24/1.49  --prep_def_merge                        true
% 7.24/1.49  --prep_def_merge_prop_impl              false
% 7.24/1.49  --prep_def_merge_mbd                    true
% 7.24/1.49  --prep_def_merge_tr_red                 false
% 7.24/1.49  --prep_def_merge_tr_cl                  false
% 7.24/1.49  --smt_preprocessing                     true
% 7.24/1.49  --smt_ac_axioms                         fast
% 7.24/1.49  --preprocessed_out                      false
% 7.24/1.49  --preprocessed_stats                    false
% 7.24/1.49  
% 7.24/1.49  ------ Abstraction refinement Options
% 7.24/1.49  
% 7.24/1.49  --abstr_ref                             []
% 7.24/1.49  --abstr_ref_prep                        false
% 7.24/1.49  --abstr_ref_until_sat                   false
% 7.24/1.49  --abstr_ref_sig_restrict                funpre
% 7.24/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.24/1.49  --abstr_ref_under                       []
% 7.24/1.49  
% 7.24/1.49  ------ SAT Options
% 7.24/1.49  
% 7.24/1.49  --sat_mode                              false
% 7.24/1.49  --sat_fm_restart_options                ""
% 7.24/1.49  --sat_gr_def                            false
% 7.24/1.49  --sat_epr_types                         true
% 7.24/1.49  --sat_non_cyclic_types                  false
% 7.24/1.49  --sat_finite_models                     false
% 7.24/1.49  --sat_fm_lemmas                         false
% 7.24/1.49  --sat_fm_prep                           false
% 7.24/1.49  --sat_fm_uc_incr                        true
% 7.24/1.49  --sat_out_model                         small
% 7.24/1.49  --sat_out_clauses                       false
% 7.24/1.49  
% 7.24/1.49  ------ QBF Options
% 7.24/1.49  
% 7.24/1.49  --qbf_mode                              false
% 7.24/1.49  --qbf_elim_univ                         false
% 7.24/1.49  --qbf_dom_inst                          none
% 7.24/1.49  --qbf_dom_pre_inst                      false
% 7.24/1.49  --qbf_sk_in                             false
% 7.24/1.49  --qbf_pred_elim                         true
% 7.24/1.49  --qbf_split                             512
% 7.24/1.49  
% 7.24/1.49  ------ BMC1 Options
% 7.24/1.49  
% 7.24/1.49  --bmc1_incremental                      false
% 7.24/1.49  --bmc1_axioms                           reachable_all
% 7.24/1.49  --bmc1_min_bound                        0
% 7.24/1.49  --bmc1_max_bound                        -1
% 7.24/1.49  --bmc1_max_bound_default                -1
% 7.24/1.49  --bmc1_symbol_reachability              true
% 7.24/1.49  --bmc1_property_lemmas                  false
% 7.24/1.49  --bmc1_k_induction                      false
% 7.24/1.49  --bmc1_non_equiv_states                 false
% 7.24/1.49  --bmc1_deadlock                         false
% 7.24/1.49  --bmc1_ucm                              false
% 7.24/1.49  --bmc1_add_unsat_core                   none
% 7.24/1.49  --bmc1_unsat_core_children              false
% 7.24/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.24/1.49  --bmc1_out_stat                         full
% 7.24/1.49  --bmc1_ground_init                      false
% 7.24/1.49  --bmc1_pre_inst_next_state              false
% 7.24/1.49  --bmc1_pre_inst_state                   false
% 7.24/1.49  --bmc1_pre_inst_reach_state             false
% 7.24/1.49  --bmc1_out_unsat_core                   false
% 7.24/1.49  --bmc1_aig_witness_out                  false
% 7.24/1.49  --bmc1_verbose                          false
% 7.24/1.49  --bmc1_dump_clauses_tptp                false
% 7.24/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.24/1.49  --bmc1_dump_file                        -
% 7.24/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.24/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.24/1.49  --bmc1_ucm_extend_mode                  1
% 7.24/1.49  --bmc1_ucm_init_mode                    2
% 7.24/1.49  --bmc1_ucm_cone_mode                    none
% 7.24/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.24/1.49  --bmc1_ucm_relax_model                  4
% 7.24/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.24/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.24/1.49  --bmc1_ucm_layered_model                none
% 7.24/1.49  --bmc1_ucm_max_lemma_size               10
% 7.24/1.49  
% 7.24/1.49  ------ AIG Options
% 7.24/1.49  
% 7.24/1.49  --aig_mode                              false
% 7.24/1.49  
% 7.24/1.49  ------ Instantiation Options
% 7.24/1.49  
% 7.24/1.49  --instantiation_flag                    true
% 7.24/1.49  --inst_sos_flag                         false
% 7.24/1.49  --inst_sos_phase                        true
% 7.24/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.24/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.24/1.49  --inst_lit_sel_side                     none
% 7.24/1.49  --inst_solver_per_active                1400
% 7.24/1.49  --inst_solver_calls_frac                1.
% 7.24/1.49  --inst_passive_queue_type               priority_queues
% 7.24/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.24/1.49  --inst_passive_queues_freq              [25;2]
% 7.24/1.49  --inst_dismatching                      true
% 7.24/1.49  --inst_eager_unprocessed_to_passive     true
% 7.24/1.49  --inst_prop_sim_given                   true
% 7.24/1.49  --inst_prop_sim_new                     false
% 7.24/1.49  --inst_subs_new                         false
% 7.24/1.49  --inst_eq_res_simp                      false
% 7.24/1.49  --inst_subs_given                       false
% 7.24/1.49  --inst_orphan_elimination               true
% 7.24/1.49  --inst_learning_loop_flag               true
% 7.24/1.49  --inst_learning_start                   3000
% 7.24/1.49  --inst_learning_factor                  2
% 7.24/1.49  --inst_start_prop_sim_after_learn       3
% 7.24/1.49  --inst_sel_renew                        solver
% 7.24/1.49  --inst_lit_activity_flag                true
% 7.24/1.49  --inst_restr_to_given                   false
% 7.24/1.49  --inst_activity_threshold               500
% 7.24/1.49  --inst_out_proof                        true
% 7.24/1.49  
% 7.24/1.49  ------ Resolution Options
% 7.24/1.49  
% 7.24/1.49  --resolution_flag                       false
% 7.24/1.49  --res_lit_sel                           adaptive
% 7.24/1.49  --res_lit_sel_side                      none
% 7.24/1.49  --res_ordering                          kbo
% 7.24/1.49  --res_to_prop_solver                    active
% 7.24/1.49  --res_prop_simpl_new                    false
% 7.24/1.49  --res_prop_simpl_given                  true
% 7.24/1.49  --res_passive_queue_type                priority_queues
% 7.24/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.24/1.49  --res_passive_queues_freq               [15;5]
% 7.24/1.49  --res_forward_subs                      full
% 7.24/1.49  --res_backward_subs                     full
% 7.24/1.49  --res_forward_subs_resolution           true
% 7.24/1.49  --res_backward_subs_resolution          true
% 7.24/1.49  --res_orphan_elimination                true
% 7.24/1.49  --res_time_limit                        2.
% 7.24/1.49  --res_out_proof                         true
% 7.24/1.49  
% 7.24/1.49  ------ Superposition Options
% 7.24/1.49  
% 7.24/1.49  --superposition_flag                    true
% 7.24/1.49  --sup_passive_queue_type                priority_queues
% 7.24/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.24/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.24/1.49  --demod_completeness_check              fast
% 7.24/1.49  --demod_use_ground                      true
% 7.24/1.49  --sup_to_prop_solver                    passive
% 7.24/1.49  --sup_prop_simpl_new                    true
% 7.24/1.49  --sup_prop_simpl_given                  true
% 7.24/1.49  --sup_fun_splitting                     false
% 7.24/1.49  --sup_smt_interval                      50000
% 7.24/1.49  
% 7.24/1.49  ------ Superposition Simplification Setup
% 7.24/1.49  
% 7.24/1.49  --sup_indices_passive                   []
% 7.24/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.24/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.24/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.24/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.24/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.24/1.49  --sup_full_bw                           [BwDemod]
% 7.24/1.49  --sup_immed_triv                        [TrivRules]
% 7.24/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.24/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.24/1.49  --sup_immed_bw_main                     []
% 7.24/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.24/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.24/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.24/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.24/1.49  
% 7.24/1.49  ------ Combination Options
% 7.24/1.49  
% 7.24/1.49  --comb_res_mult                         3
% 7.24/1.49  --comb_sup_mult                         2
% 7.24/1.49  --comb_inst_mult                        10
% 7.24/1.49  
% 7.24/1.49  ------ Debug Options
% 7.24/1.49  
% 7.24/1.49  --dbg_backtrace                         false
% 7.24/1.49  --dbg_dump_prop_clauses                 false
% 7.24/1.49  --dbg_dump_prop_clauses_file            -
% 7.24/1.49  --dbg_out_stat                          false
% 7.24/1.49  
% 7.24/1.49  
% 7.24/1.49  
% 7.24/1.49  
% 7.24/1.49  ------ Proving...
% 7.24/1.49  
% 7.24/1.49  
% 7.24/1.49  % SZS status Theorem for theBenchmark.p
% 7.24/1.49  
% 7.24/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.24/1.49  
% 7.24/1.49  fof(f18,conjecture,(
% 7.24/1.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 7.24/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.49  
% 7.24/1.49  fof(f19,negated_conjecture,(
% 7.24/1.49    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 7.24/1.49    inference(negated_conjecture,[],[f18])).
% 7.24/1.49  
% 7.24/1.49  fof(f40,plain,(
% 7.24/1.49    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 7.24/1.49    inference(ennf_transformation,[],[f19])).
% 7.24/1.49  
% 7.24/1.49  fof(f41,plain,(
% 7.24/1.49    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 7.24/1.49    inference(flattening,[],[f40])).
% 7.24/1.49  
% 7.24/1.49  fof(f58,plain,(
% 7.24/1.49    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK7) != k7_partfun1(X0,X4,k1_funct_1(X3,sK7)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK7,X1))) )),
% 7.24/1.49    introduced(choice_axiom,[])).
% 7.24/1.49  
% 7.24/1.49  fof(f57,plain,(
% 7.24/1.49    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK6),X5) != k7_partfun1(X0,sK6,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK6)) & m1_subset_1(X5,X1)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK6))) )),
% 7.24/1.49    introduced(choice_axiom,[])).
% 7.24/1.49  
% 7.24/1.49  fof(f56,plain,(
% 7.24/1.49    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,sK5,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(sK5,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK5),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK5,X1,X2) & v1_funct_1(sK5))) )),
% 7.24/1.49    introduced(choice_axiom,[])).
% 7.24/1.49  
% 7.24/1.49  fof(f55,plain,(
% 7.24/1.49    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK3,sK4,sK2,X3,X4),X5) != k7_partfun1(sK2,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK3 & r1_tarski(k2_relset_1(sK3,sK4,X3),k1_relset_1(sK4,sK2,X4)) & m1_subset_1(X5,sK3)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) & ~v1_xboole_0(sK4))),
% 7.24/1.49    introduced(choice_axiom,[])).
% 7.24/1.49  
% 7.24/1.49  fof(f59,plain,(
% 7.24/1.49    (((k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) & k1_xboole_0 != sK3 & r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) & m1_subset_1(sK7,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)) & ~v1_xboole_0(sK4)),
% 7.24/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f41,f58,f57,f56,f55])).
% 7.24/1.49  
% 7.24/1.49  fof(f96,plain,(
% 7.24/1.49    m1_subset_1(sK7,sK3)),
% 7.24/1.49    inference(cnf_transformation,[],[f59])).
% 7.24/1.49  
% 7.24/1.49  fof(f5,axiom,(
% 7.24/1.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 7.24/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.49  
% 7.24/1.49  fof(f21,plain,(
% 7.24/1.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 7.24/1.49    inference(ennf_transformation,[],[f5])).
% 7.24/1.49  
% 7.24/1.49  fof(f22,plain,(
% 7.24/1.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 7.24/1.49    inference(flattening,[],[f21])).
% 7.24/1.49  
% 7.24/1.49  fof(f69,plain,(
% 7.24/1.49    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 7.24/1.49    inference(cnf_transformation,[],[f22])).
% 7.24/1.49  
% 7.24/1.49  fof(f98,plain,(
% 7.24/1.49    k1_xboole_0 != sK3),
% 7.24/1.49    inference(cnf_transformation,[],[f59])).
% 7.24/1.49  
% 7.24/1.49  fof(f3,axiom,(
% 7.24/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.24/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.49  
% 7.24/1.49  fof(f50,plain,(
% 7.24/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.24/1.49    inference(nnf_transformation,[],[f3])).
% 7.24/1.49  
% 7.24/1.49  fof(f51,plain,(
% 7.24/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.24/1.49    inference(flattening,[],[f50])).
% 7.24/1.49  
% 7.24/1.49  fof(f67,plain,(
% 7.24/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.24/1.49    inference(cnf_transformation,[],[f51])).
% 7.24/1.49  
% 7.24/1.49  fof(f2,axiom,(
% 7.24/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.24/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.49  
% 7.24/1.49  fof(f20,plain,(
% 7.24/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.24/1.49    inference(ennf_transformation,[],[f2])).
% 7.24/1.49  
% 7.24/1.49  fof(f46,plain,(
% 7.24/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.24/1.49    inference(nnf_transformation,[],[f20])).
% 7.24/1.49  
% 7.24/1.49  fof(f47,plain,(
% 7.24/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.24/1.49    inference(rectify,[],[f46])).
% 7.24/1.49  
% 7.24/1.49  fof(f48,plain,(
% 7.24/1.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 7.24/1.49    introduced(choice_axiom,[])).
% 7.24/1.49  
% 7.24/1.49  fof(f49,plain,(
% 7.24/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.24/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f47,f48])).
% 7.24/1.49  
% 7.24/1.49  fof(f63,plain,(
% 7.24/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 7.24/1.49    inference(cnf_transformation,[],[f49])).
% 7.24/1.49  
% 7.24/1.49  fof(f4,axiom,(
% 7.24/1.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.24/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.49  
% 7.24/1.49  fof(f68,plain,(
% 7.24/1.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.24/1.49    inference(cnf_transformation,[],[f4])).
% 7.24/1.49  
% 7.24/1.49  fof(f1,axiom,(
% 7.24/1.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.24/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.49  
% 7.24/1.49  fof(f42,plain,(
% 7.24/1.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 7.24/1.49    inference(nnf_transformation,[],[f1])).
% 7.24/1.49  
% 7.24/1.49  fof(f43,plain,(
% 7.24/1.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.24/1.49    inference(rectify,[],[f42])).
% 7.24/1.49  
% 7.24/1.49  fof(f44,plain,(
% 7.24/1.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 7.24/1.49    introduced(choice_axiom,[])).
% 7.24/1.49  
% 7.24/1.49  fof(f45,plain,(
% 7.24/1.49    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.24/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).
% 7.24/1.49  
% 7.24/1.49  fof(f60,plain,(
% 7.24/1.49    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 7.24/1.49    inference(cnf_transformation,[],[f45])).
% 7.24/1.49  
% 7.24/1.49  fof(f93,plain,(
% 7.24/1.49    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 7.24/1.49    inference(cnf_transformation,[],[f59])).
% 7.24/1.49  
% 7.24/1.49  fof(f13,axiom,(
% 7.24/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.24/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.49  
% 7.24/1.49  fof(f30,plain,(
% 7.24/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.24/1.49    inference(ennf_transformation,[],[f13])).
% 7.24/1.49  
% 7.24/1.49  fof(f31,plain,(
% 7.24/1.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.24/1.49    inference(flattening,[],[f30])).
% 7.24/1.49  
% 7.24/1.49  fof(f54,plain,(
% 7.24/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.24/1.49    inference(nnf_transformation,[],[f31])).
% 7.24/1.49  
% 7.24/1.49  fof(f80,plain,(
% 7.24/1.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.24/1.49    inference(cnf_transformation,[],[f54])).
% 7.24/1.49  
% 7.24/1.49  fof(f11,axiom,(
% 7.24/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.24/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.49  
% 7.24/1.49  fof(f28,plain,(
% 7.24/1.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.24/1.49    inference(ennf_transformation,[],[f11])).
% 7.24/1.49  
% 7.24/1.49  fof(f78,plain,(
% 7.24/1.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.24/1.49    inference(cnf_transformation,[],[f28])).
% 7.24/1.49  
% 7.24/1.49  fof(f92,plain,(
% 7.24/1.49    v1_funct_2(sK5,sK3,sK4)),
% 7.24/1.49    inference(cnf_transformation,[],[f59])).
% 7.24/1.49  
% 7.24/1.49  fof(f8,axiom,(
% 7.24/1.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 7.24/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.49  
% 7.24/1.49  fof(f24,plain,(
% 7.24/1.49    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.24/1.49    inference(ennf_transformation,[],[f8])).
% 7.24/1.49  
% 7.24/1.49  fof(f25,plain,(
% 7.24/1.49    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.24/1.49    inference(flattening,[],[f24])).
% 7.24/1.49  
% 7.24/1.49  fof(f74,plain,(
% 7.24/1.49    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.24/1.49    inference(cnf_transformation,[],[f25])).
% 7.24/1.49  
% 7.24/1.49  fof(f95,plain,(
% 7.24/1.49    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))),
% 7.24/1.49    inference(cnf_transformation,[],[f59])).
% 7.24/1.49  
% 7.24/1.49  fof(f12,axiom,(
% 7.24/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.24/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.49  
% 7.24/1.49  fof(f29,plain,(
% 7.24/1.49    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.24/1.49    inference(ennf_transformation,[],[f12])).
% 7.24/1.49  
% 7.24/1.49  fof(f79,plain,(
% 7.24/1.49    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.24/1.49    inference(cnf_transformation,[],[f29])).
% 7.24/1.49  
% 7.24/1.49  fof(f97,plain,(
% 7.24/1.49    r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6))),
% 7.24/1.49    inference(cnf_transformation,[],[f59])).
% 7.24/1.49  
% 7.24/1.49  fof(f62,plain,(
% 7.24/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.24/1.49    inference(cnf_transformation,[],[f49])).
% 7.24/1.49  
% 7.24/1.49  fof(f91,plain,(
% 7.24/1.49    v1_funct_1(sK5)),
% 7.24/1.49    inference(cnf_transformation,[],[f59])).
% 7.24/1.49  
% 7.24/1.49  fof(f9,axiom,(
% 7.24/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.24/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.50  
% 7.24/1.50  fof(f26,plain,(
% 7.24/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.24/1.50    inference(ennf_transformation,[],[f9])).
% 7.24/1.50  
% 7.24/1.50  fof(f75,plain,(
% 7.24/1.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.24/1.50    inference(cnf_transformation,[],[f26])).
% 7.24/1.50  
% 7.24/1.50  fof(f10,axiom,(
% 7.24/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.24/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.50  
% 7.24/1.50  fof(f27,plain,(
% 7.24/1.50    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.24/1.50    inference(ennf_transformation,[],[f10])).
% 7.24/1.50  
% 7.24/1.50  fof(f77,plain,(
% 7.24/1.50    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.24/1.50    inference(cnf_transformation,[],[f27])).
% 7.24/1.50  
% 7.24/1.50  fof(f14,axiom,(
% 7.24/1.50    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)))),
% 7.24/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.50  
% 7.24/1.50  fof(f32,plain,(
% 7.24/1.50    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.24/1.50    inference(ennf_transformation,[],[f14])).
% 7.24/1.50  
% 7.24/1.50  fof(f33,plain,(
% 7.24/1.50    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.24/1.50    inference(flattening,[],[f32])).
% 7.24/1.50  
% 7.24/1.50  fof(f86,plain,(
% 7.24/1.50    ( ! [X2,X0,X1] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.24/1.50    inference(cnf_transformation,[],[f33])).
% 7.24/1.50  
% 7.24/1.50  fof(f94,plain,(
% 7.24/1.50    v1_funct_1(sK6)),
% 7.24/1.50    inference(cnf_transformation,[],[f59])).
% 7.24/1.50  
% 7.24/1.50  fof(f17,axiom,(
% 7.24/1.50    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 7.24/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.50  
% 7.24/1.50  fof(f38,plain,(
% 7.24/1.50    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 7.24/1.50    inference(ennf_transformation,[],[f17])).
% 7.24/1.50  
% 7.24/1.50  fof(f39,plain,(
% 7.24/1.50    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 7.24/1.50    inference(flattening,[],[f38])).
% 7.24/1.50  
% 7.24/1.50  fof(f89,plain,(
% 7.24/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 7.24/1.50    inference(cnf_transformation,[],[f39])).
% 7.24/1.50  
% 7.24/1.50  fof(f90,plain,(
% 7.24/1.50    ~v1_xboole_0(sK4)),
% 7.24/1.50    inference(cnf_transformation,[],[f59])).
% 7.24/1.50  
% 7.24/1.50  fof(f99,plain,(
% 7.24/1.50    k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7))),
% 7.24/1.50    inference(cnf_transformation,[],[f59])).
% 7.24/1.50  
% 7.24/1.50  fof(f16,axiom,(
% 7.24/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3))),
% 7.24/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.50  
% 7.24/1.50  fof(f36,plain,(
% 7.24/1.50    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 7.24/1.50    inference(ennf_transformation,[],[f16])).
% 7.24/1.50  
% 7.24/1.50  fof(f37,plain,(
% 7.24/1.50    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 7.24/1.50    inference(flattening,[],[f36])).
% 7.24/1.50  
% 7.24/1.50  fof(f88,plain,(
% 7.24/1.50    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 7.24/1.50    inference(cnf_transformation,[],[f37])).
% 7.24/1.50  
% 7.24/1.50  fof(f15,axiom,(
% 7.24/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1))),
% 7.24/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.50  
% 7.24/1.50  fof(f34,plain,(
% 7.24/1.50    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 7.24/1.50    inference(ennf_transformation,[],[f15])).
% 7.24/1.50  
% 7.24/1.50  fof(f35,plain,(
% 7.24/1.50    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 7.24/1.50    inference(flattening,[],[f34])).
% 7.24/1.50  
% 7.24/1.50  fof(f87,plain,(
% 7.24/1.50    ( ! [X2,X0,X3,X1] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 7.24/1.50    inference(cnf_transformation,[],[f35])).
% 7.24/1.50  
% 7.24/1.50  fof(f84,plain,(
% 7.24/1.50    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.24/1.50    inference(cnf_transformation,[],[f54])).
% 7.24/1.50  
% 7.24/1.50  fof(f104,plain,(
% 7.24/1.50    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 7.24/1.50    inference(equality_resolution,[],[f84])).
% 7.24/1.50  
% 7.24/1.50  fof(f66,plain,(
% 7.24/1.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.24/1.50    inference(cnf_transformation,[],[f51])).
% 7.24/1.50  
% 7.24/1.50  fof(f100,plain,(
% 7.24/1.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.24/1.50    inference(equality_resolution,[],[f66])).
% 7.24/1.50  
% 7.24/1.50  fof(f6,axiom,(
% 7.24/1.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.24/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.50  
% 7.24/1.50  fof(f52,plain,(
% 7.24/1.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.24/1.50    inference(nnf_transformation,[],[f6])).
% 7.24/1.50  
% 7.24/1.50  fof(f71,plain,(
% 7.24/1.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.24/1.50    inference(cnf_transformation,[],[f52])).
% 7.24/1.50  
% 7.24/1.50  fof(f70,plain,(
% 7.24/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.24/1.50    inference(cnf_transformation,[],[f52])).
% 7.24/1.50  
% 7.24/1.50  fof(f76,plain,(
% 7.24/1.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.24/1.50    inference(cnf_transformation,[],[f27])).
% 7.24/1.50  
% 7.24/1.50  fof(f7,axiom,(
% 7.24/1.50    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.24/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.50  
% 7.24/1.50  fof(f23,plain,(
% 7.24/1.50    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.24/1.50    inference(ennf_transformation,[],[f7])).
% 7.24/1.50  
% 7.24/1.50  fof(f53,plain,(
% 7.24/1.50    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.24/1.50    inference(nnf_transformation,[],[f23])).
% 7.24/1.50  
% 7.24/1.50  fof(f72,plain,(
% 7.24/1.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.24/1.50    inference(cnf_transformation,[],[f53])).
% 7.24/1.50  
% 7.24/1.50  cnf(c_33,negated_conjecture,
% 7.24/1.50      ( m1_subset_1(sK7,sK3) ),
% 7.24/1.50      inference(cnf_transformation,[],[f96]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_2977,plain,
% 7.24/1.50      ( m1_subset_1(sK7,sK3) = iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_9,plain,
% 7.24/1.50      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.24/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_2994,plain,
% 7.24/1.50      ( m1_subset_1(X0,X1) != iProver_top
% 7.24/1.50      | r2_hidden(X0,X1) = iProver_top
% 7.24/1.50      | v1_xboole_0(X1) = iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_4750,plain,
% 7.24/1.50      ( r2_hidden(sK7,sK3) = iProver_top
% 7.24/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.24/1.50      inference(superposition,[status(thm)],[c_2977,c_2994]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_46,plain,
% 7.24/1.50      ( m1_subset_1(sK7,sK3) = iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_31,negated_conjecture,
% 7.24/1.50      ( k1_xboole_0 != sK3 ),
% 7.24/1.50      inference(cnf_transformation,[],[f98]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_5,plain,
% 7.24/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 7.24/1.50      inference(cnf_transformation,[],[f67]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_3305,plain,
% 7.24/1.50      ( ~ r1_tarski(sK3,k1_xboole_0)
% 7.24/1.50      | ~ r1_tarski(k1_xboole_0,sK3)
% 7.24/1.50      | k1_xboole_0 = sK3 ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_5]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_3306,plain,
% 7.24/1.50      ( k1_xboole_0 = sK3
% 7.24/1.50      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 7.24/1.50      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_3305]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_3,plain,
% 7.24/1.50      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 7.24/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_3432,plain,
% 7.24/1.50      ( r1_tarski(sK3,k1_xboole_0)
% 7.24/1.50      | r2_hidden(sK1(sK3,k1_xboole_0),sK3) ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_3]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_3439,plain,
% 7.24/1.50      ( r1_tarski(sK3,k1_xboole_0) = iProver_top
% 7.24/1.50      | r2_hidden(sK1(sK3,k1_xboole_0),sK3) = iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_3432]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_8,plain,
% 7.24/1.50      ( r1_tarski(k1_xboole_0,X0) ),
% 7.24/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_3704,plain,
% 7.24/1.50      ( r1_tarski(k1_xboole_0,sK3) ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_8]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_3705,plain,
% 7.24/1.50      ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_3704]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_1,plain,
% 7.24/1.50      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 7.24/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_4006,plain,
% 7.24/1.50      ( ~ r2_hidden(sK1(sK3,k1_xboole_0),sK3) | ~ v1_xboole_0(sK3) ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_1]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_4007,plain,
% 7.24/1.50      ( r2_hidden(sK1(sK3,k1_xboole_0),sK3) != iProver_top
% 7.24/1.50      | v1_xboole_0(sK3) != iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_4006]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_4715,plain,
% 7.24/1.50      ( ~ m1_subset_1(sK7,sK3) | r2_hidden(sK7,sK3) | v1_xboole_0(sK3) ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_9]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_4716,plain,
% 7.24/1.50      ( m1_subset_1(sK7,sK3) != iProver_top
% 7.24/1.50      | r2_hidden(sK7,sK3) = iProver_top
% 7.24/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_4715]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_5218,plain,
% 7.24/1.50      ( r2_hidden(sK7,sK3) = iProver_top ),
% 7.24/1.50      inference(global_propositional_subsumption,
% 7.24/1.50                [status(thm)],
% 7.24/1.50                [c_4750,c_46,c_31,c_3306,c_3439,c_3705,c_4007,c_4716]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_36,negated_conjecture,
% 7.24/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 7.24/1.50      inference(cnf_transformation,[],[f93]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_2974,plain,
% 7.24/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_25,plain,
% 7.24/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.24/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.24/1.50      | k1_relset_1(X1,X2,X0) = X1
% 7.24/1.50      | k1_xboole_0 = X2 ),
% 7.24/1.50      inference(cnf_transformation,[],[f80]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_2982,plain,
% 7.24/1.50      ( k1_relset_1(X0,X1,X2) = X0
% 7.24/1.50      | k1_xboole_0 = X1
% 7.24/1.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.24/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_6427,plain,
% 7.24/1.50      ( k1_relset_1(sK3,sK4,sK5) = sK3
% 7.24/1.50      | sK4 = k1_xboole_0
% 7.24/1.50      | v1_funct_2(sK5,sK3,sK4) != iProver_top ),
% 7.24/1.50      inference(superposition,[status(thm)],[c_2974,c_2982]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_18,plain,
% 7.24/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.24/1.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.24/1.50      inference(cnf_transformation,[],[f78]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_2989,plain,
% 7.24/1.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.24/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_4649,plain,
% 7.24/1.50      ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
% 7.24/1.50      inference(superposition,[status(thm)],[c_2974,c_2989]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_6431,plain,
% 7.24/1.50      ( k1_relat_1(sK5) = sK3
% 7.24/1.50      | sK4 = k1_xboole_0
% 7.24/1.50      | v1_funct_2(sK5,sK3,sK4) != iProver_top ),
% 7.24/1.50      inference(demodulation,[status(thm)],[c_6427,c_4649]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_37,negated_conjecture,
% 7.24/1.50      ( v1_funct_2(sK5,sK3,sK4) ),
% 7.24/1.50      inference(cnf_transformation,[],[f92]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_42,plain,
% 7.24/1.50      ( v1_funct_2(sK5,sK3,sK4) = iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_6830,plain,
% 7.24/1.50      ( sK4 = k1_xboole_0 | k1_relat_1(sK5) = sK3 ),
% 7.24/1.50      inference(global_propositional_subsumption,
% 7.24/1.50                [status(thm)],
% 7.24/1.50                [c_6431,c_42]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_6831,plain,
% 7.24/1.50      ( k1_relat_1(sK5) = sK3 | sK4 = k1_xboole_0 ),
% 7.24/1.50      inference(renaming,[status(thm)],[c_6830]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_14,plain,
% 7.24/1.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.24/1.50      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 7.24/1.50      | ~ v1_funct_1(X1)
% 7.24/1.50      | ~ v1_relat_1(X1) ),
% 7.24/1.50      inference(cnf_transformation,[],[f74]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_2991,plain,
% 7.24/1.50      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 7.24/1.50      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 7.24/1.50      | v1_funct_1(X1) != iProver_top
% 7.24/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_34,negated_conjecture,
% 7.24/1.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
% 7.24/1.50      inference(cnf_transformation,[],[f95]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_2976,plain,
% 7.24/1.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_4648,plain,
% 7.24/1.50      ( k1_relset_1(sK4,sK2,sK6) = k1_relat_1(sK6) ),
% 7.24/1.50      inference(superposition,[status(thm)],[c_2976,c_2989]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_19,plain,
% 7.24/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.24/1.50      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.24/1.50      inference(cnf_transformation,[],[f79]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_2988,plain,
% 7.24/1.50      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.24/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_4063,plain,
% 7.24/1.50      ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
% 7.24/1.50      inference(superposition,[status(thm)],[c_2974,c_2988]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_32,negated_conjecture,
% 7.24/1.50      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
% 7.24/1.50      inference(cnf_transformation,[],[f97]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_2978,plain,
% 7.24/1.50      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_4293,plain,
% 7.24/1.50      ( r1_tarski(k2_relat_1(sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
% 7.24/1.50      inference(demodulation,[status(thm)],[c_4063,c_2978]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_5044,plain,
% 7.24/1.50      ( r1_tarski(k2_relat_1(sK5),k1_relat_1(sK6)) = iProver_top ),
% 7.24/1.50      inference(demodulation,[status(thm)],[c_4648,c_4293]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_4,plain,
% 7.24/1.50      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 7.24/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_2998,plain,
% 7.24/1.50      ( r1_tarski(X0,X1) != iProver_top
% 7.24/1.50      | r2_hidden(X2,X0) != iProver_top
% 7.24/1.50      | r2_hidden(X2,X1) = iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_5417,plain,
% 7.24/1.50      ( r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
% 7.24/1.50      | r2_hidden(X0,k1_relat_1(sK6)) = iProver_top ),
% 7.24/1.50      inference(superposition,[status(thm)],[c_5044,c_2998]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_10037,plain,
% 7.24/1.50      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 7.24/1.50      | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top
% 7.24/1.50      | v1_funct_1(sK5) != iProver_top
% 7.24/1.50      | v1_relat_1(sK5) != iProver_top ),
% 7.24/1.50      inference(superposition,[status(thm)],[c_2991,c_5417]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_38,negated_conjecture,
% 7.24/1.50      ( v1_funct_1(sK5) ),
% 7.24/1.50      inference(cnf_transformation,[],[f91]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_41,plain,
% 7.24/1.50      ( v1_funct_1(sK5) = iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_43,plain,
% 7.24/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_15,plain,
% 7.24/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.24/1.50      | v1_relat_1(X0) ),
% 7.24/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_3277,plain,
% 7.24/1.50      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 7.24/1.50      | v1_relat_1(sK5) ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_15]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_3278,plain,
% 7.24/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 7.24/1.50      | v1_relat_1(sK5) = iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_3277]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_25361,plain,
% 7.24/1.50      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 7.24/1.50      | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top ),
% 7.24/1.50      inference(global_propositional_subsumption,
% 7.24/1.50                [status(thm)],
% 7.24/1.50                [c_10037,c_41,c_43,c_3278]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_16,plain,
% 7.24/1.50      ( v5_relat_1(X0,X1)
% 7.24/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 7.24/1.50      inference(cnf_transformation,[],[f77]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_26,plain,
% 7.24/1.50      ( ~ v5_relat_1(X0,X1)
% 7.24/1.50      | ~ r2_hidden(X2,k1_relat_1(X0))
% 7.24/1.50      | ~ v1_funct_1(X0)
% 7.24/1.50      | ~ v1_relat_1(X0)
% 7.24/1.50      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 7.24/1.50      inference(cnf_transformation,[],[f86]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_495,plain,
% 7.24/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.24/1.50      | ~ r2_hidden(X3,k1_relat_1(X0))
% 7.24/1.50      | ~ v1_funct_1(X0)
% 7.24/1.50      | ~ v1_relat_1(X0)
% 7.24/1.50      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 7.24/1.50      inference(resolution,[status(thm)],[c_16,c_26]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_499,plain,
% 7.24/1.50      ( ~ v1_funct_1(X0)
% 7.24/1.50      | ~ r2_hidden(X3,k1_relat_1(X0))
% 7.24/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.24/1.50      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 7.24/1.50      inference(global_propositional_subsumption,
% 7.24/1.50                [status(thm)],
% 7.24/1.50                [c_495,c_15]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_500,plain,
% 7.24/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.24/1.50      | ~ r2_hidden(X3,k1_relat_1(X0))
% 7.24/1.50      | ~ v1_funct_1(X0)
% 7.24/1.50      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 7.24/1.50      inference(renaming,[status(thm)],[c_499]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_2970,plain,
% 7.24/1.50      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
% 7.24/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
% 7.24/1.50      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 7.24/1.50      | v1_funct_1(X1) != iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_500]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_3960,plain,
% 7.24/1.50      ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
% 7.24/1.50      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 7.24/1.50      | v1_funct_1(sK6) != iProver_top ),
% 7.24/1.50      inference(superposition,[status(thm)],[c_2976,c_2970]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_35,negated_conjecture,
% 7.24/1.50      ( v1_funct_1(sK6) ),
% 7.24/1.50      inference(cnf_transformation,[],[f94]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_44,plain,
% 7.24/1.50      ( v1_funct_1(sK6) = iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_4379,plain,
% 7.24/1.50      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 7.24/1.50      | k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0) ),
% 7.24/1.50      inference(global_propositional_subsumption,
% 7.24/1.50                [status(thm)],
% 7.24/1.50                [c_3960,c_44]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_4380,plain,
% 7.24/1.50      ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
% 7.24/1.50      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 7.24/1.50      inference(renaming,[status(thm)],[c_4379]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_25372,plain,
% 7.24/1.50      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 7.24/1.50      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 7.24/1.50      inference(superposition,[status(thm)],[c_25361,c_4380]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_25802,plain,
% 7.24/1.50      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 7.24/1.50      | sK4 = k1_xboole_0
% 7.24/1.50      | r2_hidden(X0,sK3) != iProver_top ),
% 7.24/1.50      inference(superposition,[status(thm)],[c_6831,c_25372]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_26295,plain,
% 7.24/1.50      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) = k1_funct_1(sK6,k1_funct_1(sK5,sK7))
% 7.24/1.50      | sK4 = k1_xboole_0 ),
% 7.24/1.50      inference(superposition,[status(thm)],[c_5218,c_25802]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_29,plain,
% 7.24/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.24/1.50      | ~ m1_subset_1(X3,X1)
% 7.24/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 7.24/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.24/1.50      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X5,X4))
% 7.24/1.50      | ~ v1_funct_1(X4)
% 7.24/1.50      | ~ v1_funct_1(X0)
% 7.24/1.50      | v1_xboole_0(X2)
% 7.24/1.50      | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 7.24/1.50      | k1_xboole_0 = X1 ),
% 7.24/1.50      inference(cnf_transformation,[],[f89]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_2979,plain,
% 7.24/1.50      ( k1_funct_1(k8_funct_2(X0,X1,X2,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
% 7.24/1.50      | k1_xboole_0 = X0
% 7.24/1.50      | v1_funct_2(X3,X0,X1) != iProver_top
% 7.24/1.50      | m1_subset_1(X5,X0) != iProver_top
% 7.24/1.50      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.24/1.50      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.24/1.50      | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
% 7.24/1.50      | v1_funct_1(X4) != iProver_top
% 7.24/1.50      | v1_funct_1(X3) != iProver_top
% 7.24/1.50      | v1_xboole_0(X1) = iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_4596,plain,
% 7.24/1.50      ( k1_funct_1(k8_funct_2(sK3,sK4,X0,sK5,X1),X2) = k1_funct_1(X1,k1_funct_1(sK5,X2))
% 7.24/1.50      | sK3 = k1_xboole_0
% 7.24/1.50      | v1_funct_2(sK5,sK3,sK4) != iProver_top
% 7.24/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
% 7.24/1.50      | m1_subset_1(X2,sK3) != iProver_top
% 7.24/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 7.24/1.50      | r1_tarski(k2_relat_1(sK5),k1_relset_1(sK4,X0,X1)) != iProver_top
% 7.24/1.50      | v1_funct_1(X1) != iProver_top
% 7.24/1.50      | v1_funct_1(sK5) != iProver_top
% 7.24/1.50      | v1_xboole_0(sK4) = iProver_top ),
% 7.24/1.50      inference(superposition,[status(thm)],[c_4063,c_2979]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_39,negated_conjecture,
% 7.24/1.50      ( ~ v1_xboole_0(sK4) ),
% 7.24/1.50      inference(cnf_transformation,[],[f90]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_40,plain,
% 7.24/1.50      ( v1_xboole_0(sK4) != iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_112,plain,
% 7.24/1.50      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_8]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_117,plain,
% 7.24/1.50      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 7.24/1.50      | k1_xboole_0 = k1_xboole_0 ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_5]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_2169,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_3325,plain,
% 7.24/1.50      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_2169]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_3326,plain,
% 7.24/1.50      ( sK3 != k1_xboole_0
% 7.24/1.50      | k1_xboole_0 = sK3
% 7.24/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_3325]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_8681,plain,
% 7.24/1.50      ( m1_subset_1(X2,sK3) != iProver_top
% 7.24/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
% 7.24/1.50      | k1_funct_1(k8_funct_2(sK3,sK4,X0,sK5,X1),X2) = k1_funct_1(X1,k1_funct_1(sK5,X2))
% 7.24/1.50      | r1_tarski(k2_relat_1(sK5),k1_relset_1(sK4,X0,X1)) != iProver_top
% 7.24/1.50      | v1_funct_1(X1) != iProver_top ),
% 7.24/1.50      inference(global_propositional_subsumption,
% 7.24/1.50                [status(thm)],
% 7.24/1.50                [c_4596,c_40,c_41,c_42,c_43,c_31,c_112,c_117,c_3326]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_8682,plain,
% 7.24/1.50      ( k1_funct_1(k8_funct_2(sK3,sK4,X0,sK5,X1),X2) = k1_funct_1(X1,k1_funct_1(sK5,X2))
% 7.24/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
% 7.24/1.50      | m1_subset_1(X2,sK3) != iProver_top
% 7.24/1.50      | r1_tarski(k2_relat_1(sK5),k1_relset_1(sK4,X0,X1)) != iProver_top
% 7.24/1.50      | v1_funct_1(X1) != iProver_top ),
% 7.24/1.50      inference(renaming,[status(thm)],[c_8681]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_8693,plain,
% 7.24/1.50      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 7.24/1.50      | m1_subset_1(X0,sK3) != iProver_top
% 7.24/1.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 7.24/1.50      | r1_tarski(k2_relat_1(sK5),k1_relat_1(sK6)) != iProver_top
% 7.24/1.50      | v1_funct_1(sK6) != iProver_top ),
% 7.24/1.50      inference(superposition,[status(thm)],[c_4648,c_8682]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_45,plain,
% 7.24/1.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_8721,plain,
% 7.24/1.50      ( m1_subset_1(X0,sK3) != iProver_top
% 7.24/1.50      | k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0)) ),
% 7.24/1.50      inference(global_propositional_subsumption,
% 7.24/1.50                [status(thm)],
% 7.24/1.50                [c_8693,c_44,c_45,c_5044]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_8722,plain,
% 7.24/1.50      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 7.24/1.50      | m1_subset_1(X0,sK3) != iProver_top ),
% 7.24/1.50      inference(renaming,[status(thm)],[c_8721]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_8730,plain,
% 7.24/1.50      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) = k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
% 7.24/1.50      inference(superposition,[status(thm)],[c_2977,c_8722]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_30,negated_conjecture,
% 7.24/1.50      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) ),
% 7.24/1.50      inference(cnf_transformation,[],[f99]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_8970,plain,
% 7.24/1.50      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
% 7.24/1.50      inference(demodulation,[status(thm)],[c_8730,c_30]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_26419,plain,
% 7.24/1.50      ( sK4 = k1_xboole_0 ),
% 7.24/1.50      inference(global_propositional_subsumption,
% 7.24/1.50                [status(thm)],
% 7.24/1.50                [c_26295,c_8970]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_28,plain,
% 7.24/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.24/1.50      | ~ m1_subset_1(X3,X1)
% 7.24/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.24/1.50      | ~ v1_funct_1(X0)
% 7.24/1.50      | v1_xboole_0(X1)
% 7.24/1.50      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 7.24/1.50      inference(cnf_transformation,[],[f88]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_2980,plain,
% 7.24/1.50      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
% 7.24/1.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.24/1.50      | m1_subset_1(X3,X0) != iProver_top
% 7.24/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.24/1.50      | v1_funct_1(X2) != iProver_top
% 7.24/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_5716,plain,
% 7.24/1.50      ( k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0)
% 7.24/1.50      | v1_funct_2(sK5,sK3,sK4) != iProver_top
% 7.24/1.50      | m1_subset_1(X0,sK3) != iProver_top
% 7.24/1.50      | v1_funct_1(sK5) != iProver_top
% 7.24/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.24/1.50      inference(superposition,[status(thm)],[c_2974,c_2980]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_1109,plain,
% 7.24/1.50      ( ~ m1_subset_1(X0,X1)
% 7.24/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 7.24/1.50      | ~ v1_funct_1(X2)
% 7.24/1.50      | v1_xboole_0(X1)
% 7.24/1.50      | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
% 7.24/1.50      | sK5 != X2
% 7.24/1.50      | sK4 != X3
% 7.24/1.50      | sK3 != X1 ),
% 7.24/1.50      inference(resolution_lifted,[status(thm)],[c_28,c_37]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_1110,plain,
% 7.24/1.50      ( ~ m1_subset_1(X0,sK3)
% 7.24/1.50      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 7.24/1.50      | ~ v1_funct_1(sK5)
% 7.24/1.50      | v1_xboole_0(sK3)
% 7.24/1.50      | k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0) ),
% 7.24/1.50      inference(unflattening,[status(thm)],[c_1109]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_1114,plain,
% 7.24/1.50      ( ~ m1_subset_1(X0,sK3)
% 7.24/1.50      | v1_xboole_0(sK3)
% 7.24/1.50      | k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0) ),
% 7.24/1.50      inference(global_propositional_subsumption,
% 7.24/1.50                [status(thm)],
% 7.24/1.50                [c_1110,c_38,c_36]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_1116,plain,
% 7.24/1.50      ( k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0)
% 7.24/1.50      | m1_subset_1(X0,sK3) != iProver_top
% 7.24/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_1114]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_5897,plain,
% 7.24/1.50      ( k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0)
% 7.24/1.50      | m1_subset_1(X0,sK3) != iProver_top ),
% 7.24/1.50      inference(global_propositional_subsumption,
% 7.24/1.50                [status(thm)],
% 7.24/1.50                [c_5716,c_31,c_1116,c_3306,c_3439,c_3705,c_4007]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_5905,plain,
% 7.24/1.50      ( k3_funct_2(sK3,sK4,sK5,sK7) = k1_funct_1(sK5,sK7) ),
% 7.24/1.50      inference(superposition,[status(thm)],[c_2977,c_5897]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_27,plain,
% 7.24/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.24/1.50      | ~ m1_subset_1(X3,X1)
% 7.24/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.24/1.50      | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2)
% 7.24/1.50      | ~ v1_funct_1(X0)
% 7.24/1.50      | v1_xboole_0(X1) ),
% 7.24/1.50      inference(cnf_transformation,[],[f87]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_2981,plain,
% 7.24/1.50      ( v1_funct_2(X0,X1,X2) != iProver_top
% 7.24/1.50      | m1_subset_1(X3,X1) != iProver_top
% 7.24/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.24/1.50      | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2) = iProver_top
% 7.24/1.50      | v1_funct_1(X0) != iProver_top
% 7.24/1.50      | v1_xboole_0(X1) = iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_6211,plain,
% 7.24/1.50      ( v1_funct_2(sK5,sK3,sK4) != iProver_top
% 7.24/1.50      | m1_subset_1(k1_funct_1(sK5,sK7),sK4) = iProver_top
% 7.24/1.50      | m1_subset_1(sK7,sK3) != iProver_top
% 7.24/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 7.24/1.50      | v1_funct_1(sK5) != iProver_top
% 7.24/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.24/1.50      inference(superposition,[status(thm)],[c_5905,c_2981]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_7651,plain,
% 7.24/1.50      ( m1_subset_1(k1_funct_1(sK5,sK7),sK4) = iProver_top ),
% 7.24/1.50      inference(global_propositional_subsumption,
% 7.24/1.50                [status(thm)],
% 7.24/1.50                [c_6211,c_41,c_42,c_43,c_46,c_31,c_3306,c_3439,c_3705,
% 7.24/1.50                 c_4007]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_7656,plain,
% 7.24/1.50      ( r2_hidden(k1_funct_1(sK5,sK7),sK4) = iProver_top
% 7.24/1.50      | v1_xboole_0(sK4) = iProver_top ),
% 7.24/1.50      inference(superposition,[status(thm)],[c_7651,c_2994]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_9729,plain,
% 7.24/1.50      ( r2_hidden(k1_funct_1(sK5,sK7),sK4) = iProver_top ),
% 7.24/1.50      inference(global_propositional_subsumption,
% 7.24/1.50                [status(thm)],
% 7.24/1.50                [c_7656,c_40]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_26479,plain,
% 7.24/1.50      ( r2_hidden(k1_funct_1(sK5,sK7),k1_xboole_0) = iProver_top ),
% 7.24/1.50      inference(demodulation,[status(thm)],[c_26419,c_9729]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_26513,plain,
% 7.24/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
% 7.24/1.50      inference(demodulation,[status(thm)],[c_26419,c_2974]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_21,plain,
% 7.24/1.50      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 7.24/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 7.24/1.50      | k1_xboole_0 = X1
% 7.24/1.50      | k1_xboole_0 = X0 ),
% 7.24/1.50      inference(cnf_transformation,[],[f104]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_2986,plain,
% 7.24/1.50      ( k1_xboole_0 = X0
% 7.24/1.50      | k1_xboole_0 = X1
% 7.24/1.50      | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
% 7.24/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_27415,plain,
% 7.24/1.50      ( sK5 = k1_xboole_0
% 7.24/1.50      | sK3 = k1_xboole_0
% 7.24/1.50      | v1_funct_2(sK5,sK3,k1_xboole_0) != iProver_top ),
% 7.24/1.50      inference(superposition,[status(thm)],[c_26513,c_2986]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_3315,plain,
% 7.24/1.50      ( ~ v1_funct_2(X0,sK3,k1_xboole_0)
% 7.24/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))
% 7.24/1.50      | k1_xboole_0 = X0
% 7.24/1.50      | k1_xboole_0 = sK3 ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_21]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_3563,plain,
% 7.24/1.50      ( ~ v1_funct_2(sK5,sK3,k1_xboole_0)
% 7.24/1.50      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))
% 7.24/1.50      | k1_xboole_0 = sK5
% 7.24/1.50      | k1_xboole_0 = sK3 ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_3315]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_3567,plain,
% 7.24/1.50      ( k1_xboole_0 = sK5
% 7.24/1.50      | k1_xboole_0 = sK3
% 7.24/1.50      | v1_funct_2(sK5,sK3,k1_xboole_0) != iProver_top
% 7.24/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) != iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_3563]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_2168,plain,( X0 = X0 ),theory(equality) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_3572,plain,
% 7.24/1.50      ( sK5 = sK5 ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_2168]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_3892,plain,
% 7.24/1.50      ( X0 != X1 | X0 = sK4 | sK4 != X1 ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_2169]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_3893,plain,
% 7.24/1.50      ( sK4 != k1_xboole_0
% 7.24/1.50      | k1_xboole_0 = sK4
% 7.24/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_3892]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_3521,plain,
% 7.24/1.50      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | sK3 = X0 ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_5]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_4222,plain,
% 7.24/1.50      ( ~ r1_tarski(sK3,sK3) | sK3 = sK3 ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_3521]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_6,plain,
% 7.24/1.50      ( r1_tarski(X0,X0) ),
% 7.24/1.50      inference(cnf_transformation,[],[f100]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_4223,plain,
% 7.24/1.50      ( r1_tarski(sK3,sK3) ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_6]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_3927,plain,
% 7.24/1.50      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_2169]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_5266,plain,
% 7.24/1.50      ( X0 != sK5 | sK5 = X0 | sK5 != sK5 ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_3927]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_5267,plain,
% 7.24/1.50      ( sK5 != sK5 | sK5 = k1_xboole_0 | k1_xboole_0 != sK5 ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_5266]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_2180,plain,
% 7.24/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.24/1.50      | v1_funct_2(X3,X4,X5)
% 7.24/1.50      | X3 != X0
% 7.24/1.50      | X4 != X1
% 7.24/1.50      | X5 != X2 ),
% 7.24/1.50      theory(equality) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_3385,plain,
% 7.24/1.50      ( v1_funct_2(X0,X1,X2)
% 7.24/1.50      | ~ v1_funct_2(sK5,sK3,sK4)
% 7.24/1.50      | X0 != sK5
% 7.24/1.50      | X2 != sK4
% 7.24/1.50      | X1 != sK3 ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_2180]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_3571,plain,
% 7.24/1.50      ( v1_funct_2(sK5,X0,X1)
% 7.24/1.50      | ~ v1_funct_2(sK5,sK3,sK4)
% 7.24/1.50      | X1 != sK4
% 7.24/1.50      | X0 != sK3
% 7.24/1.50      | sK5 != sK5 ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_3385]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_6519,plain,
% 7.24/1.50      ( v1_funct_2(sK5,sK3,X0)
% 7.24/1.50      | ~ v1_funct_2(sK5,sK3,sK4)
% 7.24/1.50      | X0 != sK4
% 7.24/1.50      | sK5 != sK5
% 7.24/1.50      | sK3 != sK3 ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_3571]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_6521,plain,
% 7.24/1.50      ( X0 != sK4
% 7.24/1.50      | sK5 != sK5
% 7.24/1.50      | sK3 != sK3
% 7.24/1.50      | v1_funct_2(sK5,sK3,X0) = iProver_top
% 7.24/1.50      | v1_funct_2(sK5,sK3,sK4) != iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_6519]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_6523,plain,
% 7.24/1.50      ( sK5 != sK5
% 7.24/1.50      | sK3 != sK3
% 7.24/1.50      | k1_xboole_0 != sK4
% 7.24/1.50      | v1_funct_2(sK5,sK3,sK4) != iProver_top
% 7.24/1.50      | v1_funct_2(sK5,sK3,k1_xboole_0) = iProver_top ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_6521]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_10,plain,
% 7.24/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.24/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_3269,plain,
% 7.24/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.24/1.50      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_10]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_19407,plain,
% 7.24/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
% 7.24/1.50      | ~ r1_tarski(sK5,k2_zfmisc_1(sK3,X0)) ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_3269]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_19408,plain,
% 7.24/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 7.24/1.50      | r1_tarski(sK5,k2_zfmisc_1(sK3,X0)) != iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_19407]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_19410,plain,
% 7.24/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top
% 7.24/1.50      | r1_tarski(sK5,k2_zfmisc_1(sK3,k1_xboole_0)) != iProver_top ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_19408]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_11,plain,
% 7.24/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.24/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_2992,plain,
% 7.24/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.24/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_3712,plain,
% 7.24/1.50      ( r1_tarski(sK5,k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 7.24/1.50      inference(superposition,[status(thm)],[c_2974,c_2992]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_26509,plain,
% 7.24/1.50      ( r1_tarski(sK5,k2_zfmisc_1(sK3,k1_xboole_0)) = iProver_top ),
% 7.24/1.50      inference(demodulation,[status(thm)],[c_26419,c_3712]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_27874,plain,
% 7.24/1.50      ( sK5 = k1_xboole_0 ),
% 7.24/1.50      inference(global_propositional_subsumption,
% 7.24/1.50                [status(thm)],
% 7.24/1.50                [c_27415,c_42,c_31,c_112,c_117,c_3567,c_3572,c_3893,
% 7.24/1.50                 c_4222,c_4223,c_5267,c_6523,c_8970,c_19410,c_26295,
% 7.24/1.50                 c_26509]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_32535,plain,
% 7.24/1.50      ( r2_hidden(k1_funct_1(k1_xboole_0,sK7),k1_xboole_0) = iProver_top ),
% 7.24/1.50      inference(light_normalisation,[status(thm)],[c_26479,c_27874]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_17,plain,
% 7.24/1.50      ( v4_relat_1(X0,X1)
% 7.24/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.24/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_13,plain,
% 7.24/1.50      ( ~ v4_relat_1(X0,X1)
% 7.24/1.50      | r1_tarski(k1_relat_1(X0),X1)
% 7.24/1.50      | ~ v1_relat_1(X0) ),
% 7.24/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_523,plain,
% 7.24/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.24/1.50      | r1_tarski(k1_relat_1(X0),X1)
% 7.24/1.50      | ~ v1_relat_1(X0) ),
% 7.24/1.50      inference(resolution,[status(thm)],[c_17,c_13]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_527,plain,
% 7.24/1.50      ( r1_tarski(k1_relat_1(X0),X1)
% 7.24/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.24/1.50      inference(global_propositional_subsumption,
% 7.24/1.50                [status(thm)],
% 7.24/1.50                [c_523,c_15]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_528,plain,
% 7.24/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.24/1.50      | r1_tarski(k1_relat_1(X0),X1) ),
% 7.24/1.50      inference(renaming,[status(thm)],[c_527]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_2969,plain,
% 7.24/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.24/1.50      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_528]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_3450,plain,
% 7.24/1.50      ( r1_tarski(k1_relat_1(sK6),sK4) = iProver_top ),
% 7.24/1.50      inference(superposition,[status(thm)],[c_2976,c_2969]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_26511,plain,
% 7.24/1.50      ( r1_tarski(k1_relat_1(sK6),k1_xboole_0) = iProver_top ),
% 7.24/1.50      inference(demodulation,[status(thm)],[c_26419,c_3450]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_2995,plain,
% 7.24/1.50      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_2997,plain,
% 7.24/1.50      ( X0 = X1
% 7.24/1.50      | r1_tarski(X1,X0) != iProver_top
% 7.24/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_4782,plain,
% 7.24/1.50      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.24/1.50      inference(superposition,[status(thm)],[c_2995,c_2997]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_28342,plain,
% 7.24/1.50      ( k1_relat_1(sK6) = k1_xboole_0 ),
% 7.24/1.50      inference(superposition,[status(thm)],[c_26511,c_4782]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_32220,plain,
% 7.24/1.50      ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
% 7.24/1.50      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.24/1.50      inference(demodulation,[status(thm)],[c_28342,c_4380]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_32539,plain,
% 7.24/1.50      ( k7_partfun1(sK2,sK6,k1_funct_1(k1_xboole_0,sK7)) = k1_funct_1(sK6,k1_funct_1(k1_xboole_0,sK7)) ),
% 7.24/1.50      inference(superposition,[status(thm)],[c_32535,c_32220]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_27911,plain,
% 7.24/1.50      ( k7_partfun1(sK2,sK6,k1_funct_1(k1_xboole_0,sK7)) != k1_funct_1(sK6,k1_funct_1(k1_xboole_0,sK7)) ),
% 7.24/1.50      inference(demodulation,[status(thm)],[c_27874,c_8970]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(contradiction,plain,
% 7.24/1.50      ( $false ),
% 7.24/1.50      inference(minisat,[status(thm)],[c_32539,c_27911]) ).
% 7.24/1.50  
% 7.24/1.50  
% 7.24/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.24/1.50  
% 7.24/1.50  ------                               Statistics
% 7.24/1.50  
% 7.24/1.50  ------ General
% 7.24/1.50  
% 7.24/1.50  abstr_ref_over_cycles:                  0
% 7.24/1.50  abstr_ref_under_cycles:                 0
% 7.24/1.50  gc_basic_clause_elim:                   0
% 7.24/1.50  forced_gc_time:                         0
% 7.24/1.50  parsing_time:                           0.015
% 7.24/1.50  unif_index_cands_time:                  0.
% 7.24/1.50  unif_index_add_time:                    0.
% 7.24/1.50  orderings_time:                         0.
% 7.24/1.50  out_proof_time:                         0.021
% 7.24/1.50  total_time:                             0.808
% 7.24/1.50  num_of_symbols:                         59
% 7.24/1.50  num_of_terms:                           30336
% 7.24/1.50  
% 7.24/1.50  ------ Preprocessing
% 7.24/1.50  
% 7.24/1.50  num_of_splits:                          0
% 7.24/1.50  num_of_split_atoms:                     0
% 7.24/1.50  num_of_reused_defs:                     0
% 7.24/1.50  num_eq_ax_congr_red:                    34
% 7.24/1.50  num_of_sem_filtered_clauses:            1
% 7.24/1.50  num_of_subtypes:                        0
% 7.24/1.50  monotx_restored_types:                  0
% 7.24/1.50  sat_num_of_epr_types:                   0
% 7.24/1.50  sat_num_of_non_cyclic_types:            0
% 7.24/1.50  sat_guarded_non_collapsed_types:        0
% 7.24/1.50  num_pure_diseq_elim:                    0
% 7.24/1.50  simp_replaced_by:                       0
% 7.24/1.50  res_preprocessed:                       178
% 7.24/1.50  prep_upred:                             0
% 7.24/1.50  prep_unflattend:                        124
% 7.24/1.50  smt_new_axioms:                         0
% 7.24/1.50  pred_elim_cands:                        7
% 7.24/1.50  pred_elim:                              2
% 7.24/1.50  pred_elim_cl:                           3
% 7.24/1.50  pred_elim_cycles:                       8
% 7.24/1.50  merged_defs:                            8
% 7.24/1.50  merged_defs_ncl:                        0
% 7.24/1.50  bin_hyper_res:                          8
% 7.24/1.50  prep_cycles:                            4
% 7.24/1.50  pred_elim_time:                         0.039
% 7.24/1.50  splitting_time:                         0.
% 7.24/1.50  sem_filter_time:                        0.
% 7.24/1.50  monotx_time:                            0.001
% 7.24/1.50  subtype_inf_time:                       0.
% 7.24/1.50  
% 7.24/1.50  ------ Problem properties
% 7.24/1.50  
% 7.24/1.50  clauses:                                36
% 7.24/1.50  conjectures:                            10
% 7.24/1.50  epr:                                    12
% 7.24/1.50  horn:                                   26
% 7.24/1.50  ground:                                 10
% 7.24/1.50  unary:                                  12
% 7.24/1.50  binary:                                 10
% 7.24/1.50  lits:                                   92
% 7.24/1.50  lits_eq:                                18
% 7.24/1.50  fd_pure:                                0
% 7.24/1.50  fd_pseudo:                              0
% 7.24/1.50  fd_cond:                                4
% 7.24/1.50  fd_pseudo_cond:                         1
% 7.24/1.50  ac_symbols:                             0
% 7.24/1.50  
% 7.24/1.50  ------ Propositional Solver
% 7.24/1.50  
% 7.24/1.50  prop_solver_calls:                      29
% 7.24/1.50  prop_fast_solver_calls:                 2220
% 7.24/1.50  smt_solver_calls:                       0
% 7.24/1.50  smt_fast_solver_calls:                  0
% 7.24/1.50  prop_num_of_clauses:                    11477
% 7.24/1.50  prop_preprocess_simplified:             21239
% 7.24/1.50  prop_fo_subsumed:                       96
% 7.24/1.50  prop_solver_time:                       0.
% 7.24/1.50  smt_solver_time:                        0.
% 7.24/1.50  smt_fast_solver_time:                   0.
% 7.24/1.50  prop_fast_solver_time:                  0.
% 7.24/1.50  prop_unsat_core_time:                   0.001
% 7.24/1.50  
% 7.24/1.50  ------ QBF
% 7.24/1.50  
% 7.24/1.50  qbf_q_res:                              0
% 7.24/1.50  qbf_num_tautologies:                    0
% 7.24/1.50  qbf_prep_cycles:                        0
% 7.24/1.50  
% 7.24/1.50  ------ BMC1
% 7.24/1.50  
% 7.24/1.50  bmc1_current_bound:                     -1
% 7.24/1.50  bmc1_last_solved_bound:                 -1
% 7.24/1.50  bmc1_unsat_core_size:                   -1
% 7.24/1.50  bmc1_unsat_core_parents_size:           -1
% 7.24/1.50  bmc1_merge_next_fun:                    0
% 7.24/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.24/1.50  
% 7.24/1.50  ------ Instantiation
% 7.24/1.50  
% 7.24/1.50  inst_num_of_clauses:                    2952
% 7.24/1.50  inst_num_in_passive:                    603
% 7.24/1.50  inst_num_in_active:                     1135
% 7.24/1.50  inst_num_in_unprocessed:                1250
% 7.24/1.50  inst_num_of_loops:                      1510
% 7.24/1.50  inst_num_of_learning_restarts:          0
% 7.24/1.50  inst_num_moves_active_passive:          373
% 7.24/1.50  inst_lit_activity:                      0
% 7.24/1.50  inst_lit_activity_moves:                0
% 7.24/1.50  inst_num_tautologies:                   0
% 7.24/1.50  inst_num_prop_implied:                  0
% 7.24/1.50  inst_num_existing_simplified:           0
% 7.24/1.50  inst_num_eq_res_simplified:             0
% 7.24/1.50  inst_num_child_elim:                    0
% 7.24/1.50  inst_num_of_dismatching_blockings:      1340
% 7.24/1.50  inst_num_of_non_proper_insts:           3213
% 7.24/1.50  inst_num_of_duplicates:                 0
% 7.24/1.50  inst_inst_num_from_inst_to_res:         0
% 7.24/1.50  inst_dismatching_checking_time:         0.
% 7.24/1.50  
% 7.24/1.50  ------ Resolution
% 7.24/1.50  
% 7.24/1.50  res_num_of_clauses:                     0
% 7.24/1.50  res_num_in_passive:                     0
% 7.24/1.50  res_num_in_active:                      0
% 7.24/1.50  res_num_of_loops:                       182
% 7.24/1.50  res_forward_subset_subsumed:            186
% 7.24/1.50  res_backward_subset_subsumed:           76
% 7.24/1.50  res_forward_subsumed:                   0
% 7.24/1.50  res_backward_subsumed:                  0
% 7.24/1.50  res_forward_subsumption_resolution:     0
% 7.24/1.50  res_backward_subsumption_resolution:    0
% 7.24/1.50  res_clause_to_clause_subsumption:       2322
% 7.24/1.50  res_orphan_elimination:                 0
% 7.24/1.50  res_tautology_del:                      196
% 7.24/1.50  res_num_eq_res_simplified:              0
% 7.24/1.50  res_num_sel_changes:                    0
% 7.24/1.50  res_moves_from_active_to_pass:          0
% 7.24/1.50  
% 7.24/1.50  ------ Superposition
% 7.24/1.50  
% 7.24/1.50  sup_time_total:                         0.
% 7.24/1.50  sup_time_generating:                    0.
% 7.24/1.50  sup_time_sim_full:                      0.
% 7.24/1.50  sup_time_sim_immed:                     0.
% 7.24/1.50  
% 7.24/1.50  sup_num_of_clauses:                     675
% 7.24/1.50  sup_num_in_active:                      114
% 7.24/1.50  sup_num_in_passive:                     561
% 7.24/1.50  sup_num_of_loops:                       300
% 7.24/1.50  sup_fw_superposition:                   590
% 7.24/1.50  sup_bw_superposition:                   541
% 7.24/1.50  sup_immediate_simplified:               192
% 7.24/1.50  sup_given_eliminated:                   3
% 7.24/1.50  comparisons_done:                       0
% 7.24/1.50  comparisons_avoided:                    115
% 7.24/1.50  
% 7.24/1.50  ------ Simplifications
% 7.24/1.50  
% 7.24/1.50  
% 7.24/1.50  sim_fw_subset_subsumed:                 97
% 7.24/1.50  sim_bw_subset_subsumed:                 56
% 7.24/1.50  sim_fw_subsumed:                        85
% 7.24/1.50  sim_bw_subsumed:                        4
% 7.24/1.50  sim_fw_subsumption_res:                 9
% 7.24/1.50  sim_bw_subsumption_res:                 1
% 7.24/1.50  sim_tautology_del:                      9
% 7.24/1.50  sim_eq_tautology_del:                   42
% 7.24/1.50  sim_eq_res_simp:                        0
% 7.24/1.50  sim_fw_demodulated:                     6
% 7.24/1.50  sim_bw_demodulated:                     160
% 7.24/1.50  sim_light_normalised:                   19
% 7.24/1.50  sim_joinable_taut:                      0
% 7.24/1.50  sim_joinable_simp:                      0
% 7.24/1.50  sim_ac_normalised:                      0
% 7.24/1.50  sim_smt_subsumption:                    0
% 7.24/1.50  
%------------------------------------------------------------------------------
