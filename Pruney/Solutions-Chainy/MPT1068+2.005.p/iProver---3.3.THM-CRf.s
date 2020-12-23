%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:36 EST 2020

% Result     : Theorem 3.74s
% Output     : CNFRefutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 551 expanded)
%              Number of clauses        :   96 ( 157 expanded)
%              Number of leaves         :   23 ( 182 expanded)
%              Depth                    :   18
%              Number of atoms          :  594 (4002 expanded)
%              Number of equality atoms :  194 (1015 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f28,conjecture,(
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

fof(f29,negated_conjecture,(
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
                     => ( k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f64,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f65,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f64])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
          & k1_xboole_0 != X1
          & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
          & m1_subset_1(X5,X1) )
     => ( k1_funct_1(X4,k1_funct_1(X3,sK7)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK7)
        & k1_xboole_0 != X1
        & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
        & m1_subset_1(sK7,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
              & k1_xboole_0 != X1
              & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( k1_funct_1(sK6,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK6),X5)
            & k1_xboole_0 != X1
            & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK6))
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
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
                ( k1_funct_1(X4,k1_funct_1(sK5,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK5,X4),X5)
                & k1_xboole_0 != X1
                & r1_tarski(k2_relset_1(X1,X2,sK5),k1_relset_1(X2,X0,X4))
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK5,X1,X2)
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
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
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,X3,X4),X5)
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

fof(f80,plain,
    ( k1_funct_1(sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7)
    & k1_xboole_0 != sK3
    & r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6))
    & m1_subset_1(sK7,sK3)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5)
    & ~ v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f65,f79,f78,f77,f76])).

fof(f122,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f80])).

fof(f124,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f80])).

fof(f26,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f61,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f60])).

fof(f116,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f123,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f80])).

fof(f120,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f80])).

fof(f126,plain,(
    r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
    inference(cnf_transformation,[],[f80])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_1(X4) )
         => ( r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
           => ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
              | k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
          | k1_xboole_0 = X1
          | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
          | k1_xboole_0 = X1
          | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f58])).

fof(f115,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f121,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f80])).

fof(f119,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f80])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f67,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f66])).

fof(f68,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f67,f68])).

fof(f82,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f92,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f19,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f128,plain,(
    k1_funct_1(sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f80])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f49])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f70])).

fof(f72,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f71,f72])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f62])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f111,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f102,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f96,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f94,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f99,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f86,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f127,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f80])).

fof(f125,plain,(
    m1_subset_1(sK7,sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_44,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_3306,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_3308,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_35,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_3311,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_5278,plain,
    ( k1_partfun1(X0,X1,sK4,sK2,X2,sK6) = k5_relat_1(X2,sK6)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3308,c_3311])).

cnf(c_43,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_52,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_6264,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK4,sK2,X2,sK6) = k5_relat_1(X2,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5278,c_52])).

cnf(c_6265,plain,
    ( k1_partfun1(X0,X1,sK4,sK2,X2,sK6) = k5_relat_1(X2,sK6)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_6264])).

cnf(c_6277,plain,
    ( k1_partfun1(sK3,sK4,sK4,sK2,sK5,sK6) = k5_relat_1(sK5,sK6)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3306,c_6265])).

cnf(c_46,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_3825,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK6)
    | k1_partfun1(X1,X2,sK4,sK2,X0,sK6) = k5_relat_1(X0,sK6) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_3894,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK6)
    | k1_partfun1(X0,X1,sK4,sK2,sK5,sK6) = k5_relat_1(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_3825])).

cnf(c_3953,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK6)
    | k1_partfun1(sK3,sK4,sK4,sK2,sK5,sK6) = k5_relat_1(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_3894])).

cnf(c_6399,plain,
    ( k1_partfun1(sK3,sK4,sK4,sK2,sK5,sK6) = k5_relat_1(sK5,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6277,c_46,c_44,c_43,c_42,c_3953])).

cnf(c_40,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_3310,plain,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_34,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X4,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X4,X0,X3) = k8_funct_2(X1,X2,X4,X0,X3)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f115])).

cnf(c_45,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_629,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X4,X3))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X1,X2,X2,X4,X0,X3) = k8_funct_2(X1,X2,X4,X0,X3)
    | sK4 != X2
    | sK3 != X1
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_45])).

cnf(c_630,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X1,X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK5)
    | k1_partfun1(sK3,sK4,sK4,X1,sK5,X0) = k8_funct_2(sK3,sK4,X1,sK5,X0)
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_629])).

cnf(c_634,plain,
    ( ~ v1_funct_1(X0)
    | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
    | k1_partfun1(sK3,sK4,sK4,X1,sK5,X0) = k8_funct_2(sK3,sK4,X1,sK5,X0)
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_630,c_46,c_44])).

cnf(c_635,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
    | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X1,X0))
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK3,sK4,sK4,X1,sK5,X0) = k8_funct_2(sK3,sK4,X1,sK5,X0)
    | k1_xboole_0 = sK4 ),
    inference(renaming,[status(thm)],[c_634])).

cnf(c_3299,plain,
    ( k1_partfun1(sK3,sK4,sK4,X0,sK5,X1) = k8_funct_2(sK3,sK4,X0,sK5,X1)
    | k1_xboole_0 = sK4
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
    | r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X0,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_635])).

cnf(c_3996,plain,
    ( k1_partfun1(sK3,sK4,sK4,sK2,sK5,sK6) = k8_funct_2(sK3,sK4,sK2,sK5,sK6)
    | sK4 = k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3310,c_3299])).

cnf(c_3997,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | ~ v1_funct_1(sK6)
    | k1_partfun1(sK3,sK4,sK4,sK2,sK5,sK6) = k8_funct_2(sK3,sK4,sK2,sK5,sK6)
    | sK4 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3996])).

cnf(c_3999,plain,
    ( k1_partfun1(sK3,sK4,sK4,sK2,sK5,sK6) = k8_funct_2(sK3,sK4,sK2,sK5,sK6)
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3996,c_43,c_42,c_3997])).

cnf(c_6402,plain,
    ( k8_funct_2(sK3,sK4,sK2,sK5,sK6) = k5_relat_1(sK5,sK6)
    | sK4 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6399,c_3999])).

cnf(c_47,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_48,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_2395,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3692,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_2395])).

cnf(c_3693,plain,
    ( sK4 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3692])).

cnf(c_3695,plain,
    ( sK4 != k1_xboole_0
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3693])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_3337,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_11,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_3328,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_3326,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4196,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3328,c_3326])).

cnf(c_26,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_3315,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4691,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4196,c_3315])).

cnf(c_7620,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3337,c_4691])).

cnf(c_9486,plain,
    ( k8_funct_2(sK3,sK4,sK2,sK5,sK6) = k5_relat_1(sK5,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6402,c_48,c_3695,c_7620])).

cnf(c_38,negated_conjecture,
    ( k1_funct_1(sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_9489,plain,
    ( k1_funct_1(k5_relat_1(sK5,sK6),sK7) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
    inference(demodulation,[status(thm)],[c_9486,c_38])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_6378,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(sK6)
    | k1_funct_1(k5_relat_1(X1,sK6),X0) = k1_funct_1(sK6,k1_funct_1(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_6554,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK6)
    | k1_funct_1(k5_relat_1(sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0)) ),
    inference(instantiation,[status(thm)],[c_6378])).

cnf(c_7485,plain,
    ( ~ r2_hidden(sK7,k1_relat_1(sK5))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK6)
    | k1_funct_1(k5_relat_1(sK5,sK6),sK7) = k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
    inference(instantiation,[status(thm)],[c_6554])).

cnf(c_7488,plain,
    ( k1_funct_1(k5_relat_1(sK5,sK6),sK7) = k1_funct_1(sK6,k1_funct_1(sK5,sK7))
    | r2_hidden(sK7,k1_relat_1(sK5)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7485])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_4462,plain,
    ( ~ r1_tarski(sK3,X0)
    | r2_hidden(sK7,X0)
    | ~ r2_hidden(sK7,sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_7482,plain,
    ( ~ r1_tarski(sK3,k1_relat_1(sK5))
    | r2_hidden(sK7,k1_relat_1(sK5))
    | ~ r2_hidden(sK7,sK3) ),
    inference(instantiation,[status(thm)],[c_4462])).

cnf(c_7486,plain,
    ( r1_tarski(sK3,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(sK7,k1_relat_1(sK5)) = iProver_top
    | r2_hidden(sK7,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7482])).

cnf(c_37,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k8_relset_1(X1,X2,X0,X2) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f117])).

cnf(c_618,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k8_relset_1(X1,X2,X0,X2) = X1
    | sK4 != X2
    | sK3 != X1
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_45])).

cnf(c_619,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(sK5)
    | k8_relset_1(sK3,sK4,sK5,sK4) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_618])).

cnf(c_621,plain,
    ( k8_relset_1(sK3,sK4,sK5,sK4) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_619,c_46,c_44])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_3312,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_6410,plain,
    ( k8_relset_1(sK3,sK4,sK5,X0) = k10_relat_1(sK5,X0) ),
    inference(superposition,[status(thm)],[c_3306,c_3312])).

cnf(c_6645,plain,
    ( k10_relat_1(sK5,sK4) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_621,c_6410])).

cnf(c_21,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_3319,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_6937,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(sK3,k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6645,c_3319])).

cnf(c_4198,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3306,c_3326])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_12,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_363,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_364,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_363])).

cnf(c_437,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_15,c_364])).

cnf(c_3302,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_437])).

cnf(c_4722,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4198,c_3302])).

cnf(c_18,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_3322,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5222,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4722,c_3322])).

cnf(c_4197,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(sK4,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3308,c_3326])).

cnf(c_4721,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK2)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_4197,c_3302])).

cnf(c_5094,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4721,c_3322])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_3849,plain,
    ( ~ m1_subset_1(X0,sK3)
    | r2_hidden(X0,sK3)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_4005,plain,
    ( ~ m1_subset_1(sK7,sK3)
    | r2_hidden(sK7,sK3)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3849])).

cnf(c_4006,plain,
    ( m1_subset_1(sK7,sK3) != iProver_top
    | r2_hidden(sK7,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4005])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_3631,plain,
    ( ~ v1_xboole_0(sK3)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3632,plain,
    ( k1_xboole_0 = sK3
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3631])).

cnf(c_39,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f127])).

cnf(c_41,negated_conjecture,
    ( m1_subset_1(sK7,sK3) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_54,plain,
    ( m1_subset_1(sK7,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_49,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9489,c_7620,c_7488,c_7486,c_6937,c_5222,c_5094,c_4006,c_3695,c_3632,c_39,c_54,c_52,c_49,c_48])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:01:47 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.74/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/0.99  
% 3.74/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.74/0.99  
% 3.74/0.99  ------  iProver source info
% 3.74/0.99  
% 3.74/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.74/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.74/0.99  git: non_committed_changes: false
% 3.74/0.99  git: last_make_outside_of_git: false
% 3.74/0.99  
% 3.74/0.99  ------ 
% 3.74/0.99  
% 3.74/0.99  ------ Input Options
% 3.74/0.99  
% 3.74/0.99  --out_options                           all
% 3.74/0.99  --tptp_safe_out                         true
% 3.74/0.99  --problem_path                          ""
% 3.74/0.99  --include_path                          ""
% 3.74/0.99  --clausifier                            res/vclausify_rel
% 3.74/0.99  --clausifier_options                    --mode clausify
% 3.74/0.99  --stdin                                 false
% 3.74/0.99  --stats_out                             all
% 3.74/0.99  
% 3.74/0.99  ------ General Options
% 3.74/0.99  
% 3.74/0.99  --fof                                   false
% 3.74/0.99  --time_out_real                         305.
% 3.74/0.99  --time_out_virtual                      -1.
% 3.74/0.99  --symbol_type_check                     false
% 3.74/0.99  --clausify_out                          false
% 3.74/0.99  --sig_cnt_out                           false
% 3.74/0.99  --trig_cnt_out                          false
% 3.74/0.99  --trig_cnt_out_tolerance                1.
% 3.74/0.99  --trig_cnt_out_sk_spl                   false
% 3.74/0.99  --abstr_cl_out                          false
% 3.74/0.99  
% 3.74/0.99  ------ Global Options
% 3.74/0.99  
% 3.74/0.99  --schedule                              default
% 3.74/0.99  --add_important_lit                     false
% 3.74/0.99  --prop_solver_per_cl                    1000
% 3.74/0.99  --min_unsat_core                        false
% 3.74/0.99  --soft_assumptions                      false
% 3.74/0.99  --soft_lemma_size                       3
% 3.74/0.99  --prop_impl_unit_size                   0
% 3.74/0.99  --prop_impl_unit                        []
% 3.74/0.99  --share_sel_clauses                     true
% 3.74/0.99  --reset_solvers                         false
% 3.74/0.99  --bc_imp_inh                            [conj_cone]
% 3.74/0.99  --conj_cone_tolerance                   3.
% 3.74/0.99  --extra_neg_conj                        none
% 3.74/0.99  --large_theory_mode                     true
% 3.74/0.99  --prolific_symb_bound                   200
% 3.74/0.99  --lt_threshold                          2000
% 3.74/0.99  --clause_weak_htbl                      true
% 3.74/0.99  --gc_record_bc_elim                     false
% 3.74/0.99  
% 3.74/0.99  ------ Preprocessing Options
% 3.74/0.99  
% 3.74/0.99  --preprocessing_flag                    true
% 3.74/0.99  --time_out_prep_mult                    0.1
% 3.74/0.99  --splitting_mode                        input
% 3.74/0.99  --splitting_grd                         true
% 3.74/0.99  --splitting_cvd                         false
% 3.74/0.99  --splitting_cvd_svl                     false
% 3.74/0.99  --splitting_nvd                         32
% 3.74/0.99  --sub_typing                            true
% 3.74/0.99  --prep_gs_sim                           true
% 3.74/0.99  --prep_unflatten                        true
% 3.74/0.99  --prep_res_sim                          true
% 3.74/0.99  --prep_upred                            true
% 3.74/0.99  --prep_sem_filter                       exhaustive
% 3.74/0.99  --prep_sem_filter_out                   false
% 3.74/0.99  --pred_elim                             true
% 3.74/0.99  --res_sim_input                         true
% 3.74/0.99  --eq_ax_congr_red                       true
% 3.74/0.99  --pure_diseq_elim                       true
% 3.74/0.99  --brand_transform                       false
% 3.74/0.99  --non_eq_to_eq                          false
% 3.74/0.99  --prep_def_merge                        true
% 3.74/0.99  --prep_def_merge_prop_impl              false
% 3.74/0.99  --prep_def_merge_mbd                    true
% 3.74/0.99  --prep_def_merge_tr_red                 false
% 3.74/0.99  --prep_def_merge_tr_cl                  false
% 3.74/0.99  --smt_preprocessing                     true
% 3.74/0.99  --smt_ac_axioms                         fast
% 3.74/0.99  --preprocessed_out                      false
% 3.74/0.99  --preprocessed_stats                    false
% 3.74/0.99  
% 3.74/0.99  ------ Abstraction refinement Options
% 3.74/0.99  
% 3.74/0.99  --abstr_ref                             []
% 3.74/0.99  --abstr_ref_prep                        false
% 3.74/0.99  --abstr_ref_until_sat                   false
% 3.74/0.99  --abstr_ref_sig_restrict                funpre
% 3.74/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.74/0.99  --abstr_ref_under                       []
% 3.74/0.99  
% 3.74/0.99  ------ SAT Options
% 3.74/0.99  
% 3.74/0.99  --sat_mode                              false
% 3.74/0.99  --sat_fm_restart_options                ""
% 3.74/0.99  --sat_gr_def                            false
% 3.74/0.99  --sat_epr_types                         true
% 3.74/0.99  --sat_non_cyclic_types                  false
% 3.74/0.99  --sat_finite_models                     false
% 3.74/0.99  --sat_fm_lemmas                         false
% 3.74/0.99  --sat_fm_prep                           false
% 3.74/0.99  --sat_fm_uc_incr                        true
% 3.74/0.99  --sat_out_model                         small
% 3.74/0.99  --sat_out_clauses                       false
% 3.74/0.99  
% 3.74/0.99  ------ QBF Options
% 3.74/0.99  
% 3.74/0.99  --qbf_mode                              false
% 3.74/0.99  --qbf_elim_univ                         false
% 3.74/0.99  --qbf_dom_inst                          none
% 3.74/0.99  --qbf_dom_pre_inst                      false
% 3.74/0.99  --qbf_sk_in                             false
% 3.74/0.99  --qbf_pred_elim                         true
% 3.74/0.99  --qbf_split                             512
% 3.74/0.99  
% 3.74/0.99  ------ BMC1 Options
% 3.74/0.99  
% 3.74/0.99  --bmc1_incremental                      false
% 3.74/0.99  --bmc1_axioms                           reachable_all
% 3.74/0.99  --bmc1_min_bound                        0
% 3.74/0.99  --bmc1_max_bound                        -1
% 3.74/0.99  --bmc1_max_bound_default                -1
% 3.74/0.99  --bmc1_symbol_reachability              true
% 3.74/0.99  --bmc1_property_lemmas                  false
% 3.74/0.99  --bmc1_k_induction                      false
% 3.74/0.99  --bmc1_non_equiv_states                 false
% 3.74/0.99  --bmc1_deadlock                         false
% 3.74/0.99  --bmc1_ucm                              false
% 3.74/0.99  --bmc1_add_unsat_core                   none
% 3.74/0.99  --bmc1_unsat_core_children              false
% 3.74/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.74/0.99  --bmc1_out_stat                         full
% 3.74/0.99  --bmc1_ground_init                      false
% 3.74/0.99  --bmc1_pre_inst_next_state              false
% 3.74/0.99  --bmc1_pre_inst_state                   false
% 3.74/0.99  --bmc1_pre_inst_reach_state             false
% 3.74/0.99  --bmc1_out_unsat_core                   false
% 3.74/0.99  --bmc1_aig_witness_out                  false
% 3.74/0.99  --bmc1_verbose                          false
% 3.74/0.99  --bmc1_dump_clauses_tptp                false
% 3.74/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.74/0.99  --bmc1_dump_file                        -
% 3.74/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.74/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.74/0.99  --bmc1_ucm_extend_mode                  1
% 3.74/0.99  --bmc1_ucm_init_mode                    2
% 3.74/0.99  --bmc1_ucm_cone_mode                    none
% 3.74/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.74/0.99  --bmc1_ucm_relax_model                  4
% 3.74/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.74/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.74/0.99  --bmc1_ucm_layered_model                none
% 3.74/0.99  --bmc1_ucm_max_lemma_size               10
% 3.74/0.99  
% 3.74/0.99  ------ AIG Options
% 3.74/0.99  
% 3.74/0.99  --aig_mode                              false
% 3.74/0.99  
% 3.74/0.99  ------ Instantiation Options
% 3.74/0.99  
% 3.74/0.99  --instantiation_flag                    true
% 3.74/0.99  --inst_sos_flag                         false
% 3.74/0.99  --inst_sos_phase                        true
% 3.74/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.74/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.74/0.99  --inst_lit_sel_side                     num_symb
% 3.74/0.99  --inst_solver_per_active                1400
% 3.74/0.99  --inst_solver_calls_frac                1.
% 3.74/0.99  --inst_passive_queue_type               priority_queues
% 3.74/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.74/0.99  --inst_passive_queues_freq              [25;2]
% 3.74/0.99  --inst_dismatching                      true
% 3.74/0.99  --inst_eager_unprocessed_to_passive     true
% 3.74/0.99  --inst_prop_sim_given                   true
% 3.74/0.99  --inst_prop_sim_new                     false
% 3.74/0.99  --inst_subs_new                         false
% 3.74/0.99  --inst_eq_res_simp                      false
% 3.74/0.99  --inst_subs_given                       false
% 3.74/0.99  --inst_orphan_elimination               true
% 3.74/0.99  --inst_learning_loop_flag               true
% 3.74/0.99  --inst_learning_start                   3000
% 3.74/0.99  --inst_learning_factor                  2
% 3.74/0.99  --inst_start_prop_sim_after_learn       3
% 3.74/0.99  --inst_sel_renew                        solver
% 3.74/0.99  --inst_lit_activity_flag                true
% 3.74/0.99  --inst_restr_to_given                   false
% 3.74/0.99  --inst_activity_threshold               500
% 3.74/0.99  --inst_out_proof                        true
% 3.74/0.99  
% 3.74/0.99  ------ Resolution Options
% 3.74/0.99  
% 3.74/0.99  --resolution_flag                       true
% 3.74/0.99  --res_lit_sel                           adaptive
% 3.74/0.99  --res_lit_sel_side                      none
% 3.74/0.99  --res_ordering                          kbo
% 3.74/0.99  --res_to_prop_solver                    active
% 3.74/0.99  --res_prop_simpl_new                    false
% 3.74/0.99  --res_prop_simpl_given                  true
% 3.74/0.99  --res_passive_queue_type                priority_queues
% 3.74/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.74/0.99  --res_passive_queues_freq               [15;5]
% 3.74/0.99  --res_forward_subs                      full
% 3.74/0.99  --res_backward_subs                     full
% 3.74/0.99  --res_forward_subs_resolution           true
% 3.74/0.99  --res_backward_subs_resolution          true
% 3.74/0.99  --res_orphan_elimination                true
% 3.74/0.99  --res_time_limit                        2.
% 3.74/0.99  --res_out_proof                         true
% 3.74/0.99  
% 3.74/0.99  ------ Superposition Options
% 3.74/0.99  
% 3.74/0.99  --superposition_flag                    true
% 3.74/0.99  --sup_passive_queue_type                priority_queues
% 3.74/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.74/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.74/0.99  --demod_completeness_check              fast
% 3.74/0.99  --demod_use_ground                      true
% 3.74/0.99  --sup_to_prop_solver                    passive
% 3.74/0.99  --sup_prop_simpl_new                    true
% 3.74/0.99  --sup_prop_simpl_given                  true
% 3.74/0.99  --sup_fun_splitting                     false
% 3.74/0.99  --sup_smt_interval                      50000
% 3.74/0.99  
% 3.74/0.99  ------ Superposition Simplification Setup
% 3.74/0.99  
% 3.74/0.99  --sup_indices_passive                   []
% 3.74/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.74/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.74/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.74/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.74/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.74/0.99  --sup_full_bw                           [BwDemod]
% 3.74/0.99  --sup_immed_triv                        [TrivRules]
% 3.74/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.74/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.74/0.99  --sup_immed_bw_main                     []
% 3.74/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.74/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.74/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.74/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.74/0.99  
% 3.74/0.99  ------ Combination Options
% 3.74/0.99  
% 3.74/0.99  --comb_res_mult                         3
% 3.74/0.99  --comb_sup_mult                         2
% 3.74/0.99  --comb_inst_mult                        10
% 3.74/0.99  
% 3.74/0.99  ------ Debug Options
% 3.74/0.99  
% 3.74/0.99  --dbg_backtrace                         false
% 3.74/0.99  --dbg_dump_prop_clauses                 false
% 3.74/0.99  --dbg_dump_prop_clauses_file            -
% 3.74/0.99  --dbg_out_stat                          false
% 3.74/0.99  ------ Parsing...
% 3.74/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.74/0.99  
% 3.74/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.74/0.99  
% 3.74/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.74/0.99  
% 3.74/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/0.99  ------ Proving...
% 3.74/0.99  ------ Problem Properties 
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  clauses                                 43
% 3.74/0.99  conjectures                             9
% 3.74/0.99  EPR                                     16
% 3.74/0.99  Horn                                    38
% 3.74/0.99  unary                                   11
% 3.74/0.99  binary                                  17
% 3.74/0.99  lits                                    97
% 3.74/0.99  lits eq                                 17
% 3.74/0.99  fd_pure                                 0
% 3.74/0.99  fd_pseudo                               0
% 3.74/0.99  fd_cond                                 1
% 3.74/0.99  fd_pseudo_cond                          0
% 3.74/0.99  AC symbols                              0
% 3.74/0.99  
% 3.74/0.99  ------ Schedule dynamic 5 is on 
% 3.74/0.99  
% 3.74/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  ------ 
% 3.74/0.99  Current options:
% 3.74/0.99  ------ 
% 3.74/0.99  
% 3.74/0.99  ------ Input Options
% 3.74/0.99  
% 3.74/0.99  --out_options                           all
% 3.74/0.99  --tptp_safe_out                         true
% 3.74/0.99  --problem_path                          ""
% 3.74/0.99  --include_path                          ""
% 3.74/0.99  --clausifier                            res/vclausify_rel
% 3.74/0.99  --clausifier_options                    --mode clausify
% 3.74/0.99  --stdin                                 false
% 3.74/0.99  --stats_out                             all
% 3.74/0.99  
% 3.74/0.99  ------ General Options
% 3.74/0.99  
% 3.74/0.99  --fof                                   false
% 3.74/0.99  --time_out_real                         305.
% 3.74/0.99  --time_out_virtual                      -1.
% 3.74/0.99  --symbol_type_check                     false
% 3.74/0.99  --clausify_out                          false
% 3.74/0.99  --sig_cnt_out                           false
% 3.74/0.99  --trig_cnt_out                          false
% 3.74/0.99  --trig_cnt_out_tolerance                1.
% 3.74/0.99  --trig_cnt_out_sk_spl                   false
% 3.74/0.99  --abstr_cl_out                          false
% 3.74/0.99  
% 3.74/0.99  ------ Global Options
% 3.74/0.99  
% 3.74/0.99  --schedule                              default
% 3.74/0.99  --add_important_lit                     false
% 3.74/0.99  --prop_solver_per_cl                    1000
% 3.74/0.99  --min_unsat_core                        false
% 3.74/0.99  --soft_assumptions                      false
% 3.74/0.99  --soft_lemma_size                       3
% 3.74/0.99  --prop_impl_unit_size                   0
% 3.74/0.99  --prop_impl_unit                        []
% 3.74/0.99  --share_sel_clauses                     true
% 3.74/0.99  --reset_solvers                         false
% 3.74/0.99  --bc_imp_inh                            [conj_cone]
% 3.74/0.99  --conj_cone_tolerance                   3.
% 3.74/0.99  --extra_neg_conj                        none
% 3.74/0.99  --large_theory_mode                     true
% 3.74/0.99  --prolific_symb_bound                   200
% 3.74/0.99  --lt_threshold                          2000
% 3.74/0.99  --clause_weak_htbl                      true
% 3.74/0.99  --gc_record_bc_elim                     false
% 3.74/0.99  
% 3.74/0.99  ------ Preprocessing Options
% 3.74/0.99  
% 3.74/0.99  --preprocessing_flag                    true
% 3.74/0.99  --time_out_prep_mult                    0.1
% 3.74/0.99  --splitting_mode                        input
% 3.74/0.99  --splitting_grd                         true
% 3.74/0.99  --splitting_cvd                         false
% 3.74/0.99  --splitting_cvd_svl                     false
% 3.74/0.99  --splitting_nvd                         32
% 3.74/0.99  --sub_typing                            true
% 3.74/0.99  --prep_gs_sim                           true
% 3.74/0.99  --prep_unflatten                        true
% 3.74/0.99  --prep_res_sim                          true
% 3.74/0.99  --prep_upred                            true
% 3.74/0.99  --prep_sem_filter                       exhaustive
% 3.74/0.99  --prep_sem_filter_out                   false
% 3.74/0.99  --pred_elim                             true
% 3.74/0.99  --res_sim_input                         true
% 3.74/0.99  --eq_ax_congr_red                       true
% 3.74/0.99  --pure_diseq_elim                       true
% 3.74/0.99  --brand_transform                       false
% 3.74/0.99  --non_eq_to_eq                          false
% 3.74/0.99  --prep_def_merge                        true
% 3.74/0.99  --prep_def_merge_prop_impl              false
% 3.74/0.99  --prep_def_merge_mbd                    true
% 3.74/0.99  --prep_def_merge_tr_red                 false
% 3.74/0.99  --prep_def_merge_tr_cl                  false
% 3.74/0.99  --smt_preprocessing                     true
% 3.74/0.99  --smt_ac_axioms                         fast
% 3.74/0.99  --preprocessed_out                      false
% 3.74/0.99  --preprocessed_stats                    false
% 3.74/0.99  
% 3.74/0.99  ------ Abstraction refinement Options
% 3.74/0.99  
% 3.74/0.99  --abstr_ref                             []
% 3.74/0.99  --abstr_ref_prep                        false
% 3.74/0.99  --abstr_ref_until_sat                   false
% 3.74/0.99  --abstr_ref_sig_restrict                funpre
% 3.74/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.74/0.99  --abstr_ref_under                       []
% 3.74/0.99  
% 3.74/0.99  ------ SAT Options
% 3.74/0.99  
% 3.74/0.99  --sat_mode                              false
% 3.74/0.99  --sat_fm_restart_options                ""
% 3.74/0.99  --sat_gr_def                            false
% 3.74/0.99  --sat_epr_types                         true
% 3.74/0.99  --sat_non_cyclic_types                  false
% 3.74/0.99  --sat_finite_models                     false
% 3.74/0.99  --sat_fm_lemmas                         false
% 3.74/0.99  --sat_fm_prep                           false
% 3.74/0.99  --sat_fm_uc_incr                        true
% 3.74/0.99  --sat_out_model                         small
% 3.74/0.99  --sat_out_clauses                       false
% 3.74/0.99  
% 3.74/0.99  ------ QBF Options
% 3.74/0.99  
% 3.74/0.99  --qbf_mode                              false
% 3.74/0.99  --qbf_elim_univ                         false
% 3.74/0.99  --qbf_dom_inst                          none
% 3.74/0.99  --qbf_dom_pre_inst                      false
% 3.74/0.99  --qbf_sk_in                             false
% 3.74/0.99  --qbf_pred_elim                         true
% 3.74/0.99  --qbf_split                             512
% 3.74/0.99  
% 3.74/0.99  ------ BMC1 Options
% 3.74/0.99  
% 3.74/0.99  --bmc1_incremental                      false
% 3.74/0.99  --bmc1_axioms                           reachable_all
% 3.74/0.99  --bmc1_min_bound                        0
% 3.74/0.99  --bmc1_max_bound                        -1
% 3.74/0.99  --bmc1_max_bound_default                -1
% 3.74/0.99  --bmc1_symbol_reachability              true
% 3.74/0.99  --bmc1_property_lemmas                  false
% 3.74/0.99  --bmc1_k_induction                      false
% 3.74/0.99  --bmc1_non_equiv_states                 false
% 3.74/0.99  --bmc1_deadlock                         false
% 3.74/0.99  --bmc1_ucm                              false
% 3.74/0.99  --bmc1_add_unsat_core                   none
% 3.74/0.99  --bmc1_unsat_core_children              false
% 3.74/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.74/0.99  --bmc1_out_stat                         full
% 3.74/0.99  --bmc1_ground_init                      false
% 3.74/0.99  --bmc1_pre_inst_next_state              false
% 3.74/0.99  --bmc1_pre_inst_state                   false
% 3.74/0.99  --bmc1_pre_inst_reach_state             false
% 3.74/0.99  --bmc1_out_unsat_core                   false
% 3.74/0.99  --bmc1_aig_witness_out                  false
% 3.74/0.99  --bmc1_verbose                          false
% 3.74/0.99  --bmc1_dump_clauses_tptp                false
% 3.74/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.74/0.99  --bmc1_dump_file                        -
% 3.74/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.74/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.74/0.99  --bmc1_ucm_extend_mode                  1
% 3.74/0.99  --bmc1_ucm_init_mode                    2
% 3.74/0.99  --bmc1_ucm_cone_mode                    none
% 3.74/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.74/0.99  --bmc1_ucm_relax_model                  4
% 3.74/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.74/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.74/0.99  --bmc1_ucm_layered_model                none
% 3.74/0.99  --bmc1_ucm_max_lemma_size               10
% 3.74/0.99  
% 3.74/0.99  ------ AIG Options
% 3.74/0.99  
% 3.74/0.99  --aig_mode                              false
% 3.74/0.99  
% 3.74/0.99  ------ Instantiation Options
% 3.74/0.99  
% 3.74/0.99  --instantiation_flag                    true
% 3.74/0.99  --inst_sos_flag                         false
% 3.74/0.99  --inst_sos_phase                        true
% 3.74/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.74/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.74/0.99  --inst_lit_sel_side                     none
% 3.74/0.99  --inst_solver_per_active                1400
% 3.74/0.99  --inst_solver_calls_frac                1.
% 3.74/0.99  --inst_passive_queue_type               priority_queues
% 3.74/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.74/0.99  --inst_passive_queues_freq              [25;2]
% 3.74/0.99  --inst_dismatching                      true
% 3.74/0.99  --inst_eager_unprocessed_to_passive     true
% 3.74/0.99  --inst_prop_sim_given                   true
% 3.74/0.99  --inst_prop_sim_new                     false
% 3.74/0.99  --inst_subs_new                         false
% 3.74/0.99  --inst_eq_res_simp                      false
% 3.74/0.99  --inst_subs_given                       false
% 3.74/0.99  --inst_orphan_elimination               true
% 3.74/0.99  --inst_learning_loop_flag               true
% 3.74/0.99  --inst_learning_start                   3000
% 3.74/0.99  --inst_learning_factor                  2
% 3.74/0.99  --inst_start_prop_sim_after_learn       3
% 3.74/0.99  --inst_sel_renew                        solver
% 3.74/0.99  --inst_lit_activity_flag                true
% 3.74/0.99  --inst_restr_to_given                   false
% 3.74/0.99  --inst_activity_threshold               500
% 3.74/0.99  --inst_out_proof                        true
% 3.74/0.99  
% 3.74/0.99  ------ Resolution Options
% 3.74/0.99  
% 3.74/0.99  --resolution_flag                       false
% 3.74/0.99  --res_lit_sel                           adaptive
% 3.74/0.99  --res_lit_sel_side                      none
% 3.74/0.99  --res_ordering                          kbo
% 3.74/0.99  --res_to_prop_solver                    active
% 3.74/0.99  --res_prop_simpl_new                    false
% 3.74/0.99  --res_prop_simpl_given                  true
% 3.74/0.99  --res_passive_queue_type                priority_queues
% 3.74/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.74/0.99  --res_passive_queues_freq               [15;5]
% 3.74/0.99  --res_forward_subs                      full
% 3.74/0.99  --res_backward_subs                     full
% 3.74/0.99  --res_forward_subs_resolution           true
% 3.74/0.99  --res_backward_subs_resolution          true
% 3.74/0.99  --res_orphan_elimination                true
% 3.74/0.99  --res_time_limit                        2.
% 3.74/0.99  --res_out_proof                         true
% 3.74/0.99  
% 3.74/0.99  ------ Superposition Options
% 3.74/0.99  
% 3.74/0.99  --superposition_flag                    true
% 3.74/0.99  --sup_passive_queue_type                priority_queues
% 3.74/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.74/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.74/0.99  --demod_completeness_check              fast
% 3.74/0.99  --demod_use_ground                      true
% 3.74/0.99  --sup_to_prop_solver                    passive
% 3.74/0.99  --sup_prop_simpl_new                    true
% 3.74/0.99  --sup_prop_simpl_given                  true
% 3.74/0.99  --sup_fun_splitting                     false
% 3.74/0.99  --sup_smt_interval                      50000
% 3.74/0.99  
% 3.74/0.99  ------ Superposition Simplification Setup
% 3.74/0.99  
% 3.74/0.99  --sup_indices_passive                   []
% 3.74/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.74/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.74/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.74/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.74/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.74/0.99  --sup_full_bw                           [BwDemod]
% 3.74/0.99  --sup_immed_triv                        [TrivRules]
% 3.74/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.74/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.74/0.99  --sup_immed_bw_main                     []
% 3.74/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.74/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.74/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.74/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.74/0.99  
% 3.74/0.99  ------ Combination Options
% 3.74/0.99  
% 3.74/0.99  --comb_res_mult                         3
% 3.74/0.99  --comb_sup_mult                         2
% 3.74/0.99  --comb_inst_mult                        10
% 3.74/0.99  
% 3.74/0.99  ------ Debug Options
% 3.74/0.99  
% 3.74/0.99  --dbg_backtrace                         false
% 3.74/0.99  --dbg_dump_prop_clauses                 false
% 3.74/0.99  --dbg_dump_prop_clauses_file            -
% 3.74/0.99  --dbg_out_stat                          false
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  ------ Proving...
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  % SZS status Theorem for theBenchmark.p
% 3.74/0.99  
% 3.74/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.74/0.99  
% 3.74/0.99  fof(f28,conjecture,(
% 3.74/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 3.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f29,negated_conjecture,(
% 3.74/0.99    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 3.74/0.99    inference(negated_conjecture,[],[f28])).
% 3.74/0.99  
% 3.74/0.99  fof(f64,plain,(
% 3.74/0.99    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 3.74/0.99    inference(ennf_transformation,[],[f29])).
% 3.74/0.99  
% 3.74/0.99  fof(f65,plain,(
% 3.74/0.99    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 3.74/0.99    inference(flattening,[],[f64])).
% 3.74/0.99  
% 3.74/0.99  fof(f79,plain,(
% 3.74/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k1_funct_1(X4,k1_funct_1(X3,sK7)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK7) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK7,X1))) )),
% 3.74/0.99    introduced(choice_axiom,[])).
% 3.74/0.99  
% 3.74/0.99  fof(f78,plain,(
% 3.74/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(sK6,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK6),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK6)) & m1_subset_1(X5,X1)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK6))) )),
% 3.74/0.99    introduced(choice_axiom,[])).
% 3.74/0.99  
% 3.74/0.99  fof(f77,plain,(
% 3.74/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(sK5,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK5,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK5),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK5,X1,X2) & v1_funct_1(sK5))) )),
% 3.74/0.99    introduced(choice_axiom,[])).
% 3.74/0.99  
% 3.74/0.99  fof(f76,plain,(
% 3.74/0.99    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,X3,X4),X5) & k1_xboole_0 != sK3 & r1_tarski(k2_relset_1(sK3,sK4,X3),k1_relset_1(sK4,sK2,X4)) & m1_subset_1(X5,sK3)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) & ~v1_xboole_0(sK4))),
% 3.74/0.99    introduced(choice_axiom,[])).
% 3.74/0.99  
% 3.74/0.99  fof(f80,plain,(
% 3.74/0.99    (((k1_funct_1(sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) & k1_xboole_0 != sK3 & r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) & m1_subset_1(sK7,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)) & ~v1_xboole_0(sK4)),
% 3.74/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f65,f79,f78,f77,f76])).
% 3.74/0.99  
% 3.74/0.99  fof(f122,plain,(
% 3.74/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.74/0.99    inference(cnf_transformation,[],[f80])).
% 3.74/0.99  
% 3.74/0.99  fof(f124,plain,(
% 3.74/0.99    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))),
% 3.74/0.99    inference(cnf_transformation,[],[f80])).
% 3.74/0.99  
% 3.74/0.99  fof(f26,axiom,(
% 3.74/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f60,plain,(
% 3.74/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.74/0.99    inference(ennf_transformation,[],[f26])).
% 3.74/0.99  
% 3.74/0.99  fof(f61,plain,(
% 3.74/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.74/0.99    inference(flattening,[],[f60])).
% 3.74/0.99  
% 3.74/0.99  fof(f116,plain,(
% 3.74/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.74/0.99    inference(cnf_transformation,[],[f61])).
% 3.74/0.99  
% 3.74/0.99  fof(f123,plain,(
% 3.74/0.99    v1_funct_1(sK6)),
% 3.74/0.99    inference(cnf_transformation,[],[f80])).
% 3.74/0.99  
% 3.74/0.99  fof(f120,plain,(
% 3.74/0.99    v1_funct_1(sK5)),
% 3.74/0.99    inference(cnf_transformation,[],[f80])).
% 3.74/0.99  
% 3.74/0.99  fof(f126,plain,(
% 3.74/0.99    r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6))),
% 3.74/0.99    inference(cnf_transformation,[],[f80])).
% 3.74/0.99  
% 3.74/0.99  fof(f25,axiom,(
% 3.74/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) => (r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) => (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1))))),
% 3.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f58,plain,(
% 3.74/0.99    ! [X0,X1,X2,X3] : (! [X4] : (((k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.74/0.99    inference(ennf_transformation,[],[f25])).
% 3.74/0.99  
% 3.74/0.99  fof(f59,plain,(
% 3.74/0.99    ! [X0,X1,X2,X3] : (! [X4] : (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.74/0.99    inference(flattening,[],[f58])).
% 3.74/0.99  
% 3.74/0.99  fof(f115,plain,(
% 3.74/0.99    ( ! [X4,X2,X0,X3,X1] : (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.74/0.99    inference(cnf_transformation,[],[f59])).
% 3.74/0.99  
% 3.74/0.99  fof(f121,plain,(
% 3.74/0.99    v1_funct_2(sK5,sK3,sK4)),
% 3.74/0.99    inference(cnf_transformation,[],[f80])).
% 3.74/0.99  
% 3.74/0.99  fof(f119,plain,(
% 3.74/0.99    ~v1_xboole_0(sK4)),
% 3.74/0.99    inference(cnf_transformation,[],[f80])).
% 3.74/0.99  
% 3.74/0.99  fof(f1,axiom,(
% 3.74/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f66,plain,(
% 3.74/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.74/0.99    inference(nnf_transformation,[],[f1])).
% 3.74/0.99  
% 3.74/0.99  fof(f67,plain,(
% 3.74/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.74/0.99    inference(rectify,[],[f66])).
% 3.74/0.99  
% 3.74/0.99  fof(f68,plain,(
% 3.74/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.74/0.99    introduced(choice_axiom,[])).
% 3.74/0.99  
% 3.74/0.99  fof(f69,plain,(
% 3.74/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.74/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f67,f68])).
% 3.74/0.99  
% 3.74/0.99  fof(f82,plain,(
% 3.74/0.99    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.74/0.99    inference(cnf_transformation,[],[f69])).
% 3.74/0.99  
% 3.74/0.99  fof(f6,axiom,(
% 3.74/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f92,plain,(
% 3.74/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.74/0.99    inference(cnf_transformation,[],[f6])).
% 3.74/0.99  
% 3.74/0.99  fof(f7,axiom,(
% 3.74/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f75,plain,(
% 3.74/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.74/0.99    inference(nnf_transformation,[],[f7])).
% 3.74/0.99  
% 3.74/0.99  fof(f93,plain,(
% 3.74/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.74/0.99    inference(cnf_transformation,[],[f75])).
% 3.74/0.99  
% 3.74/0.99  fof(f19,axiom,(
% 3.74/0.99    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f51,plain,(
% 3.74/0.99    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.74/0.99    inference(ennf_transformation,[],[f19])).
% 3.74/0.99  
% 3.74/0.99  fof(f107,plain,(
% 3.74/0.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.74/0.99    inference(cnf_transformation,[],[f51])).
% 3.74/0.99  
% 3.74/0.99  fof(f128,plain,(
% 3.74/0.99    k1_funct_1(sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7)),
% 3.74/0.99    inference(cnf_transformation,[],[f80])).
% 3.74/0.99  
% 3.74/0.99  fof(f18,axiom,(
% 3.74/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0))))),
% 3.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f49,plain,(
% 3.74/0.99    ! [X0,X1] : (! [X2] : ((k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.74/0.99    inference(ennf_transformation,[],[f18])).
% 3.74/0.99  
% 3.74/0.99  fof(f50,plain,(
% 3.74/0.99    ! [X0,X1] : (! [X2] : (k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.74/0.99    inference(flattening,[],[f49])).
% 3.74/0.99  
% 3.74/0.99  fof(f106,plain,(
% 3.74/0.99    ( ! [X2,X0,X1] : (k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.74/0.99    inference(cnf_transformation,[],[f50])).
% 3.74/0.99  
% 3.74/0.99  fof(f2,axiom,(
% 3.74/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f31,plain,(
% 3.74/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.74/0.99    inference(ennf_transformation,[],[f2])).
% 3.74/0.99  
% 3.74/0.99  fof(f70,plain,(
% 3.74/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.74/0.99    inference(nnf_transformation,[],[f31])).
% 3.74/0.99  
% 3.74/0.99  fof(f71,plain,(
% 3.74/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.74/0.99    inference(rectify,[],[f70])).
% 3.74/0.99  
% 3.74/0.99  fof(f72,plain,(
% 3.74/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.74/0.99    introduced(choice_axiom,[])).
% 3.74/0.99  
% 3.74/0.99  fof(f73,plain,(
% 3.74/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.74/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f71,f72])).
% 3.74/0.99  
% 3.74/0.99  fof(f83,plain,(
% 3.74/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.74/0.99    inference(cnf_transformation,[],[f73])).
% 3.74/0.99  
% 3.74/0.99  fof(f27,axiom,(
% 3.74/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 3.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f62,plain,(
% 3.74/0.99    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.74/0.99    inference(ennf_transformation,[],[f27])).
% 3.74/0.99  
% 3.74/0.99  fof(f63,plain,(
% 3.74/0.99    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.74/0.99    inference(flattening,[],[f62])).
% 3.74/0.99  
% 3.74/0.99  fof(f117,plain,(
% 3.74/0.99    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.74/0.99    inference(cnf_transformation,[],[f63])).
% 3.74/0.99  
% 3.74/0.99  fof(f23,axiom,(
% 3.74/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 3.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f55,plain,(
% 3.74/0.99    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.74/0.99    inference(ennf_transformation,[],[f23])).
% 3.74/0.99  
% 3.74/0.99  fof(f111,plain,(
% 3.74/0.99    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.74/0.99    inference(cnf_transformation,[],[f55])).
% 3.74/0.99  
% 3.74/0.99  fof(f14,axiom,(
% 3.74/0.99    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 3.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f44,plain,(
% 3.74/0.99    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.74/0.99    inference(ennf_transformation,[],[f14])).
% 3.74/0.99  
% 3.74/0.99  fof(f102,plain,(
% 3.74/0.99    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.74/0.99    inference(cnf_transformation,[],[f44])).
% 3.74/0.99  
% 3.74/0.99  fof(f9,axiom,(
% 3.74/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f37,plain,(
% 3.74/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.74/0.99    inference(ennf_transformation,[],[f9])).
% 3.74/0.99  
% 3.74/0.99  fof(f96,plain,(
% 3.74/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.74/0.99    inference(cnf_transformation,[],[f37])).
% 3.74/0.99  
% 3.74/0.99  fof(f94,plain,(
% 3.74/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.74/0.99    inference(cnf_transformation,[],[f75])).
% 3.74/0.99  
% 3.74/0.99  fof(f11,axiom,(
% 3.74/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f99,plain,(
% 3.74/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.74/0.99    inference(cnf_transformation,[],[f11])).
% 3.74/0.99  
% 3.74/0.99  fof(f5,axiom,(
% 3.74/0.99    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f34,plain,(
% 3.74/0.99    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.74/0.99    inference(ennf_transformation,[],[f5])).
% 3.74/0.99  
% 3.74/0.99  fof(f74,plain,(
% 3.74/0.99    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.74/0.99    inference(nnf_transformation,[],[f34])).
% 3.74/0.99  
% 3.74/0.99  fof(f88,plain,(
% 3.74/0.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.74/0.99    inference(cnf_transformation,[],[f74])).
% 3.74/0.99  
% 3.74/0.99  fof(f3,axiom,(
% 3.74/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f32,plain,(
% 3.74/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.74/0.99    inference(ennf_transformation,[],[f3])).
% 3.74/0.99  
% 3.74/0.99  fof(f86,plain,(
% 3.74/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.74/0.99    inference(cnf_transformation,[],[f32])).
% 3.74/0.99  
% 3.74/0.99  fof(f127,plain,(
% 3.74/0.99    k1_xboole_0 != sK3),
% 3.74/0.99    inference(cnf_transformation,[],[f80])).
% 3.74/0.99  
% 3.74/0.99  fof(f125,plain,(
% 3.74/0.99    m1_subset_1(sK7,sK3)),
% 3.74/0.99    inference(cnf_transformation,[],[f80])).
% 3.74/0.99  
% 3.74/0.99  cnf(c_44,negated_conjecture,
% 3.74/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.74/0.99      inference(cnf_transformation,[],[f122]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_3306,plain,
% 3.74/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_42,negated_conjecture,
% 3.74/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
% 3.74/0.99      inference(cnf_transformation,[],[f124]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_3308,plain,
% 3.74/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_35,plain,
% 3.74/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.74/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.74/0.99      | ~ v1_funct_1(X3)
% 3.74/0.99      | ~ v1_funct_1(X0)
% 3.74/0.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.74/0.99      inference(cnf_transformation,[],[f116]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_3311,plain,
% 3.74/0.99      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.74/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.74/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.74/0.99      | v1_funct_1(X5) != iProver_top
% 3.74/0.99      | v1_funct_1(X4) != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_5278,plain,
% 3.74/0.99      ( k1_partfun1(X0,X1,sK4,sK2,X2,sK6) = k5_relat_1(X2,sK6)
% 3.74/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.74/0.99      | v1_funct_1(X2) != iProver_top
% 3.74/0.99      | v1_funct_1(sK6) != iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_3308,c_3311]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_43,negated_conjecture,
% 3.74/0.99      ( v1_funct_1(sK6) ),
% 3.74/0.99      inference(cnf_transformation,[],[f123]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_52,plain,
% 3.74/0.99      ( v1_funct_1(sK6) = iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_6264,plain,
% 3.74/0.99      ( v1_funct_1(X2) != iProver_top
% 3.74/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.74/0.99      | k1_partfun1(X0,X1,sK4,sK2,X2,sK6) = k5_relat_1(X2,sK6) ),
% 3.74/0.99      inference(global_propositional_subsumption,
% 3.74/0.99                [status(thm)],
% 3.74/0.99                [c_5278,c_52]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_6265,plain,
% 3.74/0.99      ( k1_partfun1(X0,X1,sK4,sK2,X2,sK6) = k5_relat_1(X2,sK6)
% 3.74/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.74/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.74/0.99      inference(renaming,[status(thm)],[c_6264]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_6277,plain,
% 3.74/0.99      ( k1_partfun1(sK3,sK4,sK4,sK2,sK5,sK6) = k5_relat_1(sK5,sK6)
% 3.74/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_3306,c_6265]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_46,negated_conjecture,
% 3.74/0.99      ( v1_funct_1(sK5) ),
% 3.74/0.99      inference(cnf_transformation,[],[f120]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_3825,plain,
% 3.74/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.74/0.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
% 3.74/0.99      | ~ v1_funct_1(X0)
% 3.74/0.99      | ~ v1_funct_1(sK6)
% 3.74/0.99      | k1_partfun1(X1,X2,sK4,sK2,X0,sK6) = k5_relat_1(X0,sK6) ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_35]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_3894,plain,
% 3.74/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.74/0.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
% 3.74/0.99      | ~ v1_funct_1(sK5)
% 3.74/0.99      | ~ v1_funct_1(sK6)
% 3.74/0.99      | k1_partfun1(X0,X1,sK4,sK2,sK5,sK6) = k5_relat_1(sK5,sK6) ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_3825]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_3953,plain,
% 3.74/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.74/0.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
% 3.74/0.99      | ~ v1_funct_1(sK5)
% 3.74/0.99      | ~ v1_funct_1(sK6)
% 3.74/0.99      | k1_partfun1(sK3,sK4,sK4,sK2,sK5,sK6) = k5_relat_1(sK5,sK6) ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_3894]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_6399,plain,
% 3.74/0.99      ( k1_partfun1(sK3,sK4,sK4,sK2,sK5,sK6) = k5_relat_1(sK5,sK6) ),
% 3.74/0.99      inference(global_propositional_subsumption,
% 3.74/0.99                [status(thm)],
% 3.74/0.99                [c_6277,c_46,c_44,c_43,c_42,c_3953]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_40,negated_conjecture,
% 3.74/0.99      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
% 3.74/0.99      inference(cnf_transformation,[],[f126]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_3310,plain,
% 3.74/0.99      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_34,plain,
% 3.74/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.74/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 3.74/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.74/0.99      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X4,X3))
% 3.74/0.99      | ~ v1_funct_1(X3)
% 3.74/0.99      | ~ v1_funct_1(X0)
% 3.74/0.99      | k1_partfun1(X1,X2,X2,X4,X0,X3) = k8_funct_2(X1,X2,X4,X0,X3)
% 3.74/0.99      | k1_xboole_0 = X2 ),
% 3.74/0.99      inference(cnf_transformation,[],[f115]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_45,negated_conjecture,
% 3.74/0.99      ( v1_funct_2(sK5,sK3,sK4) ),
% 3.74/0.99      inference(cnf_transformation,[],[f121]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_629,plain,
% 3.74/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.74/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 3.74/0.99      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X4,X3))
% 3.74/0.99      | ~ v1_funct_1(X0)
% 3.74/0.99      | ~ v1_funct_1(X3)
% 3.74/0.99      | k1_partfun1(X1,X2,X2,X4,X0,X3) = k8_funct_2(X1,X2,X4,X0,X3)
% 3.74/0.99      | sK4 != X2
% 3.74/0.99      | sK3 != X1
% 3.74/0.99      | sK5 != X0
% 3.74/0.99      | k1_xboole_0 = X2 ),
% 3.74/0.99      inference(resolution_lifted,[status(thm)],[c_34,c_45]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_630,plain,
% 3.74/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
% 3.74/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.74/0.99      | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X1,X0))
% 3.74/0.99      | ~ v1_funct_1(X0)
% 3.74/0.99      | ~ v1_funct_1(sK5)
% 3.74/0.99      | k1_partfun1(sK3,sK4,sK4,X1,sK5,X0) = k8_funct_2(sK3,sK4,X1,sK5,X0)
% 3.74/0.99      | k1_xboole_0 = sK4 ),
% 3.74/0.99      inference(unflattening,[status(thm)],[c_629]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_634,plain,
% 3.74/0.99      ( ~ v1_funct_1(X0)
% 3.74/0.99      | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X1,X0))
% 3.74/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
% 3.74/0.99      | k1_partfun1(sK3,sK4,sK4,X1,sK5,X0) = k8_funct_2(sK3,sK4,X1,sK5,X0)
% 3.74/0.99      | k1_xboole_0 = sK4 ),
% 3.74/0.99      inference(global_propositional_subsumption,
% 3.74/0.99                [status(thm)],
% 3.74/0.99                [c_630,c_46,c_44]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_635,plain,
% 3.74/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
% 3.74/0.99      | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X1,X0))
% 3.74/0.99      | ~ v1_funct_1(X0)
% 3.74/0.99      | k1_partfun1(sK3,sK4,sK4,X1,sK5,X0) = k8_funct_2(sK3,sK4,X1,sK5,X0)
% 3.74/0.99      | k1_xboole_0 = sK4 ),
% 3.74/0.99      inference(renaming,[status(thm)],[c_634]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_3299,plain,
% 3.74/0.99      ( k1_partfun1(sK3,sK4,sK4,X0,sK5,X1) = k8_funct_2(sK3,sK4,X0,sK5,X1)
% 3.74/0.99      | k1_xboole_0 = sK4
% 3.74/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
% 3.74/0.99      | r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X0,X1)) != iProver_top
% 3.74/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_635]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_3996,plain,
% 3.74/0.99      ( k1_partfun1(sK3,sK4,sK4,sK2,sK5,sK6) = k8_funct_2(sK3,sK4,sK2,sK5,sK6)
% 3.74/0.99      | sK4 = k1_xboole_0
% 3.74/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 3.74/0.99      | v1_funct_1(sK6) != iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_3310,c_3299]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_3997,plain,
% 3.74/0.99      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
% 3.74/0.99      | ~ v1_funct_1(sK6)
% 3.74/0.99      | k1_partfun1(sK3,sK4,sK4,sK2,sK5,sK6) = k8_funct_2(sK3,sK4,sK2,sK5,sK6)
% 3.74/0.99      | sK4 = k1_xboole_0 ),
% 3.74/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3996]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_3999,plain,
% 3.74/0.99      ( k1_partfun1(sK3,sK4,sK4,sK2,sK5,sK6) = k8_funct_2(sK3,sK4,sK2,sK5,sK6)
% 3.74/0.99      | sK4 = k1_xboole_0 ),
% 3.74/0.99      inference(global_propositional_subsumption,
% 3.74/0.99                [status(thm)],
% 3.74/0.99                [c_3996,c_43,c_42,c_3997]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_6402,plain,
% 3.74/0.99      ( k8_funct_2(sK3,sK4,sK2,sK5,sK6) = k5_relat_1(sK5,sK6)
% 3.74/0.99      | sK4 = k1_xboole_0 ),
% 3.74/0.99      inference(demodulation,[status(thm)],[c_6399,c_3999]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_47,negated_conjecture,
% 3.74/0.99      ( ~ v1_xboole_0(sK4) ),
% 3.74/0.99      inference(cnf_transformation,[],[f119]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_48,plain,
% 3.74/0.99      ( v1_xboole_0(sK4) != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_2395,plain,
% 3.74/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.74/0.99      theory(equality) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_3692,plain,
% 3.74/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK4) | sK4 != X0 ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_2395]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_3693,plain,
% 3.74/0.99      ( sK4 != X0
% 3.74/0.99      | v1_xboole_0(X0) != iProver_top
% 3.74/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_3692]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_3695,plain,
% 3.74/0.99      ( sK4 != k1_xboole_0
% 3.74/0.99      | v1_xboole_0(sK4) = iProver_top
% 3.74/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_3693]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_0,plain,
% 3.74/0.99      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.74/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_3337,plain,
% 3.74/0.99      ( r2_hidden(sK0(X0),X0) = iProver_top
% 3.74/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_11,plain,
% 3.74/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.74/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_3328,plain,
% 3.74/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_13,plain,
% 3.74/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.74/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_3326,plain,
% 3.74/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.74/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_4196,plain,
% 3.74/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_3328,c_3326]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_26,plain,
% 3.74/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.74/0.99      inference(cnf_transformation,[],[f107]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_3315,plain,
% 3.74/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.74/0.99      | r2_hidden(X1,X0) != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_4691,plain,
% 3.74/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_4196,c_3315]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_7620,plain,
% 3.74/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_3337,c_4691]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_9486,plain,
% 3.74/0.99      ( k8_funct_2(sK3,sK4,sK2,sK5,sK6) = k5_relat_1(sK5,sK6) ),
% 3.74/0.99      inference(global_propositional_subsumption,
% 3.74/0.99                [status(thm)],
% 3.74/0.99                [c_6402,c_48,c_3695,c_7620]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_38,negated_conjecture,
% 3.74/0.99      ( k1_funct_1(sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) ),
% 3.74/0.99      inference(cnf_transformation,[],[f128]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_9489,plain,
% 3.74/0.99      ( k1_funct_1(k5_relat_1(sK5,sK6),sK7) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
% 3.74/0.99      inference(demodulation,[status(thm)],[c_9486,c_38]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_25,plain,
% 3.74/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.74/0.99      | ~ v1_funct_1(X2)
% 3.74/0.99      | ~ v1_funct_1(X1)
% 3.74/0.99      | ~ v1_relat_1(X2)
% 3.74/0.99      | ~ v1_relat_1(X1)
% 3.74/0.99      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
% 3.74/0.99      inference(cnf_transformation,[],[f106]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_6378,plain,
% 3.74/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.74/0.99      | ~ v1_funct_1(X1)
% 3.74/0.99      | ~ v1_funct_1(sK6)
% 3.74/0.99      | ~ v1_relat_1(X1)
% 3.74/0.99      | ~ v1_relat_1(sK6)
% 3.74/0.99      | k1_funct_1(k5_relat_1(X1,sK6),X0) = k1_funct_1(sK6,k1_funct_1(X1,X0)) ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_25]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_6554,plain,
% 3.74/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK5))
% 3.74/0.99      | ~ v1_funct_1(sK5)
% 3.74/0.99      | ~ v1_funct_1(sK6)
% 3.74/0.99      | ~ v1_relat_1(sK5)
% 3.74/0.99      | ~ v1_relat_1(sK6)
% 3.74/0.99      | k1_funct_1(k5_relat_1(sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0)) ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_6378]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_7485,plain,
% 3.74/0.99      ( ~ r2_hidden(sK7,k1_relat_1(sK5))
% 3.74/0.99      | ~ v1_funct_1(sK5)
% 3.74/0.99      | ~ v1_funct_1(sK6)
% 3.74/0.99      | ~ v1_relat_1(sK5)
% 3.74/0.99      | ~ v1_relat_1(sK6)
% 3.74/0.99      | k1_funct_1(k5_relat_1(sK5,sK6),sK7) = k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_6554]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_7488,plain,
% 3.74/0.99      ( k1_funct_1(k5_relat_1(sK5,sK6),sK7) = k1_funct_1(sK6,k1_funct_1(sK5,sK7))
% 3.74/0.99      | r2_hidden(sK7,k1_relat_1(sK5)) != iProver_top
% 3.74/0.99      | v1_funct_1(sK5) != iProver_top
% 3.74/0.99      | v1_funct_1(sK6) != iProver_top
% 3.74/0.99      | v1_relat_1(sK5) != iProver_top
% 3.74/0.99      | v1_relat_1(sK6) != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_7485]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_4,plain,
% 3.74/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.74/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_4462,plain,
% 3.74/0.99      ( ~ r1_tarski(sK3,X0) | r2_hidden(sK7,X0) | ~ r2_hidden(sK7,sK3) ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_7482,plain,
% 3.74/0.99      ( ~ r1_tarski(sK3,k1_relat_1(sK5))
% 3.74/0.99      | r2_hidden(sK7,k1_relat_1(sK5))
% 3.74/0.99      | ~ r2_hidden(sK7,sK3) ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_4462]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_7486,plain,
% 3.74/0.99      ( r1_tarski(sK3,k1_relat_1(sK5)) != iProver_top
% 3.74/0.99      | r2_hidden(sK7,k1_relat_1(sK5)) = iProver_top
% 3.74/0.99      | r2_hidden(sK7,sK3) != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_7482]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_37,plain,
% 3.74/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.74/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.74/0.99      | ~ v1_funct_1(X0)
% 3.74/0.99      | k8_relset_1(X1,X2,X0,X2) = X1
% 3.74/0.99      | k1_xboole_0 = X2 ),
% 3.74/0.99      inference(cnf_transformation,[],[f117]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_618,plain,
% 3.74/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.74/0.99      | ~ v1_funct_1(X0)
% 3.74/0.99      | k8_relset_1(X1,X2,X0,X2) = X1
% 3.74/0.99      | sK4 != X2
% 3.74/0.99      | sK3 != X1
% 3.74/0.99      | sK5 != X0
% 3.74/0.99      | k1_xboole_0 = X2 ),
% 3.74/0.99      inference(resolution_lifted,[status(thm)],[c_37,c_45]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_619,plain,
% 3.74/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.74/0.99      | ~ v1_funct_1(sK5)
% 3.74/0.99      | k8_relset_1(sK3,sK4,sK5,sK4) = sK3
% 3.74/0.99      | k1_xboole_0 = sK4 ),
% 3.74/0.99      inference(unflattening,[status(thm)],[c_618]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_621,plain,
% 3.74/0.99      ( k8_relset_1(sK3,sK4,sK5,sK4) = sK3 | k1_xboole_0 = sK4 ),
% 3.74/0.99      inference(global_propositional_subsumption,
% 3.74/0.99                [status(thm)],
% 3.74/0.99                [c_619,c_46,c_44]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_30,plain,
% 3.74/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.74/0.99      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 3.74/0.99      inference(cnf_transformation,[],[f111]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_3312,plain,
% 3.74/0.99      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 3.74/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_6410,plain,
% 3.74/0.99      ( k8_relset_1(sK3,sK4,sK5,X0) = k10_relat_1(sK5,X0) ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_3306,c_3312]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_6645,plain,
% 3.74/0.99      ( k10_relat_1(sK5,sK4) = sK3 | sK4 = k1_xboole_0 ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_621,c_6410]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_21,plain,
% 3.74/0.99      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 3.74/0.99      inference(cnf_transformation,[],[f102]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_3319,plain,
% 3.74/0.99      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
% 3.74/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_6937,plain,
% 3.74/0.99      ( sK4 = k1_xboole_0
% 3.74/0.99      | r1_tarski(sK3,k1_relat_1(sK5)) = iProver_top
% 3.74/0.99      | v1_relat_1(sK5) != iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_6645,c_3319]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_4198,plain,
% 3.74/0.99      ( r1_tarski(sK5,k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_3306,c_3326]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_15,plain,
% 3.74/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.74/0.99      | ~ v1_relat_1(X1)
% 3.74/0.99      | v1_relat_1(X0) ),
% 3.74/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_12,plain,
% 3.74/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.74/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_363,plain,
% 3.74/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.74/0.99      inference(prop_impl,[status(thm)],[c_12]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_364,plain,
% 3.74/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.74/0.99      inference(renaming,[status(thm)],[c_363]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_437,plain,
% 3.74/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.74/0.99      inference(bin_hyper_res,[status(thm)],[c_15,c_364]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_3302,plain,
% 3.74/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.74/0.99      | v1_relat_1(X1) != iProver_top
% 3.74/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_437]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_4722,plain,
% 3.74/0.99      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
% 3.74/0.99      | v1_relat_1(sK5) = iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_4198,c_3302]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_18,plain,
% 3.74/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.74/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_3322,plain,
% 3.74/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_5222,plain,
% 3.74/0.99      ( v1_relat_1(sK5) = iProver_top ),
% 3.74/0.99      inference(forward_subsumption_resolution,
% 3.74/0.99                [status(thm)],
% 3.74/0.99                [c_4722,c_3322]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_4197,plain,
% 3.74/0.99      ( r1_tarski(sK6,k2_zfmisc_1(sK4,sK2)) = iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_3308,c_3326]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_4721,plain,
% 3.74/0.99      ( v1_relat_1(k2_zfmisc_1(sK4,sK2)) != iProver_top
% 3.74/0.99      | v1_relat_1(sK6) = iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_4197,c_3302]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_5094,plain,
% 3.74/0.99      ( v1_relat_1(sK6) = iProver_top ),
% 3.74/0.99      inference(forward_subsumption_resolution,
% 3.74/0.99                [status(thm)],
% 3.74/0.99                [c_4721,c_3322]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_10,plain,
% 3.74/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.74/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_3849,plain,
% 3.74/0.99      ( ~ m1_subset_1(X0,sK3) | r2_hidden(X0,sK3) | v1_xboole_0(sK3) ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_4005,plain,
% 3.74/0.99      ( ~ m1_subset_1(sK7,sK3) | r2_hidden(sK7,sK3) | v1_xboole_0(sK3) ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_3849]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_4006,plain,
% 3.74/0.99      ( m1_subset_1(sK7,sK3) != iProver_top
% 3.74/0.99      | r2_hidden(sK7,sK3) = iProver_top
% 3.74/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_4005]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_5,plain,
% 3.74/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.74/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_3631,plain,
% 3.74/0.99      ( ~ v1_xboole_0(sK3) | k1_xboole_0 = sK3 ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_3632,plain,
% 3.74/0.99      ( k1_xboole_0 = sK3 | v1_xboole_0(sK3) != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_3631]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_39,negated_conjecture,
% 3.74/0.99      ( k1_xboole_0 != sK3 ),
% 3.74/0.99      inference(cnf_transformation,[],[f127]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_41,negated_conjecture,
% 3.74/0.99      ( m1_subset_1(sK7,sK3) ),
% 3.74/0.99      inference(cnf_transformation,[],[f125]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_54,plain,
% 3.74/0.99      ( m1_subset_1(sK7,sK3) = iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_49,plain,
% 3.74/0.99      ( v1_funct_1(sK5) = iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(contradiction,plain,
% 3.74/0.99      ( $false ),
% 3.74/0.99      inference(minisat,
% 3.74/0.99                [status(thm)],
% 3.74/0.99                [c_9489,c_7620,c_7488,c_7486,c_6937,c_5222,c_5094,c_4006,
% 3.74/0.99                 c_3695,c_3632,c_39,c_54,c_52,c_49,c_48]) ).
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.74/0.99  
% 3.74/0.99  ------                               Statistics
% 3.74/0.99  
% 3.74/0.99  ------ General
% 3.74/0.99  
% 3.74/0.99  abstr_ref_over_cycles:                  0
% 3.74/0.99  abstr_ref_under_cycles:                 0
% 3.74/0.99  gc_basic_clause_elim:                   0
% 3.74/0.99  forced_gc_time:                         0
% 3.74/0.99  parsing_time:                           0.009
% 3.74/0.99  unif_index_cands_time:                  0.
% 3.74/0.99  unif_index_add_time:                    0.
% 3.74/0.99  orderings_time:                         0.
% 3.74/0.99  out_proof_time:                         0.014
% 3.74/0.99  total_time:                             0.245
% 3.74/0.99  num_of_symbols:                         62
% 3.74/0.99  num_of_terms:                           8434
% 3.74/0.99  
% 3.74/0.99  ------ Preprocessing
% 3.74/0.99  
% 3.74/0.99  num_of_splits:                          0
% 3.74/0.99  num_of_split_atoms:                     0
% 3.74/0.99  num_of_reused_defs:                     0
% 3.74/0.99  num_eq_ax_congr_red:                    48
% 3.74/0.99  num_of_sem_filtered_clauses:            1
% 3.74/0.99  num_of_subtypes:                        0
% 3.74/0.99  monotx_restored_types:                  0
% 3.74/0.99  sat_num_of_epr_types:                   0
% 3.74/0.99  sat_num_of_non_cyclic_types:            0
% 3.74/0.99  sat_guarded_non_collapsed_types:        0
% 3.74/0.99  num_pure_diseq_elim:                    0
% 3.74/0.99  simp_replaced_by:                       0
% 3.74/0.99  res_preprocessed:                       211
% 3.74/0.99  prep_upred:                             0
% 3.74/0.99  prep_unflattend:                        103
% 3.74/0.99  smt_new_axioms:                         0
% 3.74/0.99  pred_elim_cands:                        6
% 3.74/0.99  pred_elim:                              2
% 3.74/0.99  pred_elim_cl:                           2
% 3.74/0.99  pred_elim_cycles:                       4
% 3.74/0.99  merged_defs:                            8
% 3.74/0.99  merged_defs_ncl:                        0
% 3.74/0.99  bin_hyper_res:                          9
% 3.74/0.99  prep_cycles:                            4
% 3.74/0.99  pred_elim_time:                         0.026
% 3.74/0.99  splitting_time:                         0.
% 3.74/0.99  sem_filter_time:                        0.
% 3.74/0.99  monotx_time:                            0.001
% 3.74/0.99  subtype_inf_time:                       0.
% 3.74/0.99  
% 3.74/0.99  ------ Problem properties
% 3.74/0.99  
% 3.74/0.99  clauses:                                43
% 3.74/0.99  conjectures:                            9
% 3.74/0.99  epr:                                    16
% 3.74/0.99  horn:                                   38
% 3.74/0.99  ground:                                 12
% 3.74/0.99  unary:                                  11
% 3.74/0.99  binary:                                 17
% 3.74/0.99  lits:                                   97
% 3.74/0.99  lits_eq:                                17
% 3.74/0.99  fd_pure:                                0
% 3.74/0.99  fd_pseudo:                              0
% 3.74/0.99  fd_cond:                                1
% 3.74/0.99  fd_pseudo_cond:                         0
% 3.74/0.99  ac_symbols:                             0
% 3.74/0.99  
% 3.74/0.99  ------ Propositional Solver
% 3.74/0.99  
% 3.74/0.99  prop_solver_calls:                      28
% 3.74/0.99  prop_fast_solver_calls:                 1579
% 3.74/0.99  smt_solver_calls:                       0
% 3.74/0.99  smt_fast_solver_calls:                  0
% 3.74/0.99  prop_num_of_clauses:                    3301
% 3.74/0.99  prop_preprocess_simplified:             9568
% 3.74/0.99  prop_fo_subsumed:                       31
% 3.74/0.99  prop_solver_time:                       0.
% 3.74/0.99  smt_solver_time:                        0.
% 3.74/0.99  smt_fast_solver_time:                   0.
% 3.74/0.99  prop_fast_solver_time:                  0.
% 3.74/0.99  prop_unsat_core_time:                   0.
% 3.74/0.99  
% 3.74/0.99  ------ QBF
% 3.74/0.99  
% 3.74/0.99  qbf_q_res:                              0
% 3.74/0.99  qbf_num_tautologies:                    0
% 3.74/0.99  qbf_prep_cycles:                        0
% 3.74/0.99  
% 3.74/0.99  ------ BMC1
% 3.74/0.99  
% 3.74/0.99  bmc1_current_bound:                     -1
% 3.74/0.99  bmc1_last_solved_bound:                 -1
% 3.74/0.99  bmc1_unsat_core_size:                   -1
% 3.74/0.99  bmc1_unsat_core_parents_size:           -1
% 3.74/0.99  bmc1_merge_next_fun:                    0
% 3.74/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.74/0.99  
% 3.74/0.99  ------ Instantiation
% 3.74/0.99  
% 3.74/0.99  inst_num_of_clauses:                    888
% 3.74/0.99  inst_num_in_passive:                    81
% 3.74/0.99  inst_num_in_active:                     424
% 3.74/0.99  inst_num_in_unprocessed:                383
% 3.74/0.99  inst_num_of_loops:                      510
% 3.74/0.99  inst_num_of_learning_restarts:          0
% 3.74/0.99  inst_num_moves_active_passive:          83
% 3.74/0.99  inst_lit_activity:                      0
% 3.74/0.99  inst_lit_activity_moves:                0
% 3.74/0.99  inst_num_tautologies:                   0
% 3.74/0.99  inst_num_prop_implied:                  0
% 3.74/0.99  inst_num_existing_simplified:           0
% 3.74/0.99  inst_num_eq_res_simplified:             0
% 3.74/0.99  inst_num_child_elim:                    0
% 3.74/0.99  inst_num_of_dismatching_blockings:      260
% 3.74/0.99  inst_num_of_non_proper_insts:           671
% 3.74/0.99  inst_num_of_duplicates:                 0
% 3.74/0.99  inst_inst_num_from_inst_to_res:         0
% 3.74/0.99  inst_dismatching_checking_time:         0.
% 3.74/0.99  
% 3.74/0.99  ------ Resolution
% 3.74/0.99  
% 3.74/0.99  res_num_of_clauses:                     0
% 3.74/0.99  res_num_in_passive:                     0
% 3.74/0.99  res_num_in_active:                      0
% 3.74/0.99  res_num_of_loops:                       215
% 3.74/0.99  res_forward_subset_subsumed:            58
% 3.74/0.99  res_backward_subset_subsumed:           0
% 3.74/0.99  res_forward_subsumed:                   0
% 3.74/0.99  res_backward_subsumed:                  0
% 3.74/0.99  res_forward_subsumption_resolution:     0
% 3.74/0.99  res_backward_subsumption_resolution:    0
% 3.74/0.99  res_clause_to_clause_subsumption:       381
% 3.74/0.99  res_orphan_elimination:                 0
% 3.74/0.99  res_tautology_del:                      45
% 3.74/0.99  res_num_eq_res_simplified:              0
% 3.74/0.99  res_num_sel_changes:                    0
% 3.74/0.99  res_moves_from_active_to_pass:          0
% 3.74/0.99  
% 3.74/0.99  ------ Superposition
% 3.74/0.99  
% 3.74/0.99  sup_time_total:                         0.
% 3.74/0.99  sup_time_generating:                    0.
% 3.74/0.99  sup_time_sim_full:                      0.
% 3.74/0.99  sup_time_sim_immed:                     0.
% 3.74/0.99  
% 3.74/0.99  sup_num_of_clauses:                     166
% 3.74/0.99  sup_num_in_active:                      91
% 3.74/0.99  sup_num_in_passive:                     75
% 3.74/0.99  sup_num_of_loops:                       100
% 3.74/0.99  sup_fw_superposition:                   90
% 3.74/0.99  sup_bw_superposition:                   77
% 3.74/0.99  sup_immediate_simplified:               8
% 3.74/0.99  sup_given_eliminated:                   0
% 3.74/0.99  comparisons_done:                       0
% 3.74/0.99  comparisons_avoided:                    8
% 3.74/0.99  
% 3.74/0.99  ------ Simplifications
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  sim_fw_subset_subsumed:                 6
% 3.74/0.99  sim_bw_subset_subsumed:                 4
% 3.74/0.99  sim_fw_subsumed:                        2
% 3.74/0.99  sim_bw_subsumed:                        0
% 3.74/0.99  sim_fw_subsumption_res:                 2
% 3.74/0.99  sim_bw_subsumption_res:                 0
% 3.74/0.99  sim_tautology_del:                      8
% 3.74/0.99  sim_eq_tautology_del:                   1
% 3.74/0.99  sim_eq_res_simp:                        0
% 3.74/0.99  sim_fw_demodulated:                     0
% 3.74/0.99  sim_bw_demodulated:                     7
% 3.74/0.99  sim_light_normalised:                   2
% 3.74/0.99  sim_joinable_taut:                      0
% 3.74/0.99  sim_joinable_simp:                      0
% 3.74/0.99  sim_ac_normalised:                      0
% 3.74/0.99  sim_smt_subsumption:                    0
% 3.74/0.99  
%------------------------------------------------------------------------------
