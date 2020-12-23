%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:46 EST 2020

% Result     : Theorem 11.63s
% Output     : CNFRefutation 11.63s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 521 expanded)
%              Number of clauses        :   91 ( 149 expanded)
%              Number of leaves         :   27 ( 172 expanded)
%              Depth                    :   19
%              Number of atoms          :  643 (3712 expanded)
%              Number of equality atoms :  271 (1033 expanded)
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

fof(f45,plain,(
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

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
          & k1_xboole_0 != X1
          & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
          & m1_subset_1(X5,X1) )
     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK10) != k7_partfun1(X0,X4,k1_funct_1(X3,sK10))
        & k1_xboole_0 != X1
        & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
        & m1_subset_1(sK10,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
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
            ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK9),X5) != k7_partfun1(X0,sK9,k1_funct_1(X3,X5))
            & k1_xboole_0 != X1
            & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK9))
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        & v1_funct_1(sK9) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
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
                ( k1_funct_1(k8_funct_2(X1,X2,X0,sK8,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(sK8,X5))
                & k1_xboole_0 != X1
                & r1_tarski(k2_relset_1(X1,X2,sK8),k1_relset_1(X2,X0,X4))
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK8,X1,X2)
        & v1_funct_1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
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
                  ( k1_funct_1(k8_funct_2(sK6,sK7,sK5,X3,X4),X5) != k7_partfun1(sK5,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != sK6
                  & r1_tarski(k2_relset_1(sK6,sK7,X3),k1_relset_1(sK7,sK5,X4))
                  & m1_subset_1(X5,sK6) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK7,sK5)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
          & v1_funct_2(X3,sK6,sK7)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,
    ( k1_funct_1(k8_funct_2(sK6,sK7,sK5,sK8,sK9),sK10) != k7_partfun1(sK5,sK9,k1_funct_1(sK8,sK10))
    & k1_xboole_0 != sK6
    & r1_tarski(k2_relset_1(sK6,sK7,sK8),k1_relset_1(sK7,sK5,sK9))
    & m1_subset_1(sK10,sK6)
    & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK5)))
    & v1_funct_1(sK9)
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    & v1_funct_2(sK8,sK6,sK7)
    & v1_funct_1(sK8)
    & ~ v1_xboole_0(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9,sK10])],[f46,f66,f65,f64,f63])).

fof(f110,plain,(
    m1_subset_1(sK10,sK6) ),
    inference(cnf_transformation,[],[f67])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f112,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f67])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f48,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f49])).

fof(f69,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f109,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK5))) ),
    inference(cnf_transformation,[],[f67])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f56])).

fof(f60,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X5)) = X5
        & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1)) = X2
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK2(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK2(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK2(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK2(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK3(X0,X1)) = sK2(X0,X1)
                  & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK2(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK4(X0,X5)) = X5
                    & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f57,f60,f59,f58])).

fof(f80,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f114,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f115,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f114])).

fof(f107,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f67])).

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

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f111,plain,(
    r1_tarski(k2_relset_1(sK6,sK7,sK8),k1_relset_1(sK7,sK5,sK9)) ),
    inference(cnf_transformation,[],[f67])).

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

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

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

fof(f51,plain,(
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

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f51])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f52,f53])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f15,axiom,(
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

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f62,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f104,plain,(
    ~ v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f67])).

fof(f106,plain,(
    v1_funct_2(sK8,sK6,sK7) ),
    inference(cnf_transformation,[],[f67])).

fof(f105,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f67])).

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

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f108,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f67])).

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

fof(f41,plain,(
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

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f100,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f113,plain,(
    k1_funct_1(k8_funct_2(sK6,sK7,sK5,sK8,sK9),sK10) != k7_partfun1(sK5,sK9,k1_funct_1(sK8,sK10)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK10,sK6) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_4116,plain,
    ( m1_subset_1(sK10,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_4143,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5869,plain,
    ( r2_hidden(sK10,sK6) = iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_4116,c_4143])).

cnf(c_37,negated_conjecture,
    ( k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_4500,plain,
    ( ~ v1_xboole_0(sK6)
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4501,plain,
    ( k1_xboole_0 = sK6
    | v1_xboole_0(sK6) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4500])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_4150,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_4145,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_4134,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4811,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4145,c_4134])).

cnf(c_4873,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4150,c_4811])).

cnf(c_6391,plain,
    ( r2_hidden(sK10,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5869,c_37,c_4501,c_4873])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK5))) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_4115,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_18,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_4132,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5289,plain,
    ( v5_relat_1(sK9,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4115,c_4132])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_4137,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_4113,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_4129,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5619,plain,
    ( k2_relset_1(sK6,sK7,sK8) = k2_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_4113,c_4129])).

cnf(c_38,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK6,sK7,sK8),k1_relset_1(sK7,sK5,sK9)) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_4117,plain,
    ( r1_tarski(k2_relset_1(sK6,sK7,sK8),k1_relset_1(sK7,sK5,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_6106,plain,
    ( r1_tarski(k2_relat_1(sK8),k1_relset_1(sK7,sK5,sK9)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5619,c_4117])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_4130,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5745,plain,
    ( k1_relset_1(sK7,sK5,sK9) = k1_relat_1(sK9) ),
    inference(superposition,[status(thm)],[c_4115,c_4130])).

cnf(c_6223,plain,
    ( r1_tarski(k2_relat_1(sK8),k1_relat_1(sK9)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6106,c_5745])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_4146,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_7268,plain,
    ( r2_hidden(X0,k1_relat_1(sK9)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6223,c_4146])).

cnf(c_8909,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k1_funct_1(sK8,X0),k1_relat_1(sK9)) = iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_4137,c_7268])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_4122,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_7684,plain,
    ( k1_relset_1(sK6,sK7,sK8) = sK6
    | sK7 = k1_xboole_0
    | v1_funct_2(sK8,sK6,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_4113,c_4122])).

cnf(c_5746,plain,
    ( k1_relset_1(sK6,sK7,sK8) = k1_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_4113,c_4130])).

cnf(c_7688,plain,
    ( k1_relat_1(sK8) = sK6
    | sK7 = k1_xboole_0
    | v1_funct_2(sK8,sK6,sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7684,c_5746])).

cnf(c_45,negated_conjecture,
    ( ~ v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_46,plain,
    ( v1_xboole_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_43,negated_conjecture,
    ( v1_funct_2(sK8,sK6,sK7) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_48,plain,
    ( v1_funct_2(sK8,sK6,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_3412,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_4509,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK7)
    | sK7 != X0 ),
    inference(instantiation,[status(thm)],[c_3412])).

cnf(c_4510,plain,
    ( sK7 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4509])).

cnf(c_4512,plain,
    ( sK7 != k1_xboole_0
    | v1_xboole_0(sK7) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4510])).

cnf(c_7715,plain,
    ( k1_relat_1(sK8) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7688,c_46,c_48,c_4512,c_4873])).

cnf(c_8914,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(k1_funct_1(sK8,X0),k1_relat_1(sK9)) = iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8909,c_7715])).

cnf(c_44,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_47,plain,
    ( v1_funct_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_49,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_4506,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_4507,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
    | v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4506])).

cnf(c_9095,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(k1_funct_1(sK8,X0),k1_relat_1(sK9)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8914,c_47,c_49,c_4507])).

cnf(c_31,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_4121,plain,
    ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
    | v5_relat_1(X1,X0) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_9104,plain,
    ( k7_partfun1(X0,sK9,k1_funct_1(sK8,X1)) = k1_funct_1(sK9,k1_funct_1(sK8,X1))
    | v5_relat_1(sK9,X0) != iProver_top
    | r2_hidden(X1,sK6) != iProver_top
    | v1_funct_1(sK9) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_9095,c_4121])).

cnf(c_41,negated_conjecture,
    ( v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_50,plain,
    ( v1_funct_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_51,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_4503,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK5)))
    | v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_4504,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK5))) != iProver_top
    | v1_relat_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4503])).

cnf(c_58955,plain,
    ( k7_partfun1(X0,sK9,k1_funct_1(sK8,X1)) = k1_funct_1(sK9,k1_funct_1(sK8,X1))
    | v5_relat_1(sK9,X0) != iProver_top
    | r2_hidden(X1,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9104,c_50,c_51,c_4504])).

cnf(c_58962,plain,
    ( k7_partfun1(sK5,sK9,k1_funct_1(sK8,X0)) = k1_funct_1(sK9,k1_funct_1(sK8,X0))
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5289,c_58955])).

cnf(c_59430,plain,
    ( k7_partfun1(sK5,sK9,k1_funct_1(sK8,sK10)) = k1_funct_1(sK9,k1_funct_1(sK8,sK10)) ),
    inference(superposition,[status(thm)],[c_6391,c_58962])).

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
    inference(cnf_transformation,[],[f100])).

cnf(c_4120,plain,
    ( k1_funct_1(k8_funct_2(X0,X1,X2,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
    | k1_xboole_0 = X0
    | v1_funct_2(X3,X0,X1) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_6785,plain,
    ( k1_funct_1(k8_funct_2(sK6,sK7,X0,sK8,X1),X2) = k1_funct_1(X1,k1_funct_1(sK8,X2))
    | sK6 = k1_xboole_0
    | v1_funct_2(sK8,sK6,sK7) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK7,X0))) != iProver_top
    | m1_subset_1(X2,sK6) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
    | r1_tarski(k2_relat_1(sK8),k1_relset_1(sK7,X0,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_5619,c_4120])).

cnf(c_3410,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3439,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3410])).

cnf(c_3411,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4553,plain,
    ( sK6 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_3411])).

cnf(c_4554,plain,
    ( sK6 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4553])).

cnf(c_7377,plain,
    ( m1_subset_1(X2,sK6) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK7,X0))) != iProver_top
    | k1_funct_1(k8_funct_2(sK6,sK7,X0,sK8,X1),X2) = k1_funct_1(X1,k1_funct_1(sK8,X2))
    | r1_tarski(k2_relat_1(sK8),k1_relset_1(sK7,X0,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6785,c_46,c_47,c_48,c_49,c_37,c_3439,c_4554])).

cnf(c_7378,plain,
    ( k1_funct_1(k8_funct_2(sK6,sK7,X0,sK8,X1),X2) = k1_funct_1(X1,k1_funct_1(sK8,X2))
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK7,X0))) != iProver_top
    | m1_subset_1(X2,sK6) != iProver_top
    | r1_tarski(k2_relat_1(sK8),k1_relset_1(sK7,X0,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_7377])).

cnf(c_7390,plain,
    ( k1_funct_1(k8_funct_2(sK6,sK7,sK5,sK8,sK9),X0) = k1_funct_1(sK9,k1_funct_1(sK8,X0))
    | m1_subset_1(X0,sK6) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK5))) != iProver_top
    | r1_tarski(k2_relat_1(sK8),k1_relat_1(sK9)) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_5745,c_7378])).

cnf(c_7456,plain,
    ( m1_subset_1(X0,sK6) != iProver_top
    | k1_funct_1(k8_funct_2(sK6,sK7,sK5,sK8,sK9),X0) = k1_funct_1(sK9,k1_funct_1(sK8,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7390,c_50,c_51,c_6223])).

cnf(c_7457,plain,
    ( k1_funct_1(k8_funct_2(sK6,sK7,sK5,sK8,sK9),X0) = k1_funct_1(sK9,k1_funct_1(sK8,X0))
    | m1_subset_1(X0,sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_7456])).

cnf(c_7464,plain,
    ( k1_funct_1(k8_funct_2(sK6,sK7,sK5,sK8,sK9),sK10) = k1_funct_1(sK9,k1_funct_1(sK8,sK10)) ),
    inference(superposition,[status(thm)],[c_4116,c_7457])).

cnf(c_36,negated_conjecture,
    ( k1_funct_1(k8_funct_2(sK6,sK7,sK5,sK8,sK9),sK10) != k7_partfun1(sK5,sK9,k1_funct_1(sK8,sK10)) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_7466,plain,
    ( k7_partfun1(sK5,sK9,k1_funct_1(sK8,sK10)) != k1_funct_1(sK9,k1_funct_1(sK8,sK10)) ),
    inference(demodulation,[status(thm)],[c_7464,c_36])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_59430,c_7466])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:47:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 11.63/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.63/2.00  
% 11.63/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.63/2.00  
% 11.63/2.00  ------  iProver source info
% 11.63/2.00  
% 11.63/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.63/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.63/2.00  git: non_committed_changes: false
% 11.63/2.00  git: last_make_outside_of_git: false
% 11.63/2.00  
% 11.63/2.00  ------ 
% 11.63/2.00  
% 11.63/2.00  ------ Input Options
% 11.63/2.00  
% 11.63/2.00  --out_options                           all
% 11.63/2.00  --tptp_safe_out                         true
% 11.63/2.00  --problem_path                          ""
% 11.63/2.00  --include_path                          ""
% 11.63/2.00  --clausifier                            res/vclausify_rel
% 11.63/2.00  --clausifier_options                    --mode clausify
% 11.63/2.00  --stdin                                 false
% 11.63/2.00  --stats_out                             all
% 11.63/2.00  
% 11.63/2.00  ------ General Options
% 11.63/2.00  
% 11.63/2.00  --fof                                   false
% 11.63/2.00  --time_out_real                         305.
% 11.63/2.00  --time_out_virtual                      -1.
% 11.63/2.00  --symbol_type_check                     false
% 11.63/2.00  --clausify_out                          false
% 11.63/2.00  --sig_cnt_out                           false
% 11.63/2.00  --trig_cnt_out                          false
% 11.63/2.00  --trig_cnt_out_tolerance                1.
% 11.63/2.00  --trig_cnt_out_sk_spl                   false
% 11.63/2.00  --abstr_cl_out                          false
% 11.63/2.00  
% 11.63/2.00  ------ Global Options
% 11.63/2.00  
% 11.63/2.00  --schedule                              default
% 11.63/2.00  --add_important_lit                     false
% 11.63/2.00  --prop_solver_per_cl                    1000
% 11.63/2.00  --min_unsat_core                        false
% 11.63/2.00  --soft_assumptions                      false
% 11.63/2.00  --soft_lemma_size                       3
% 11.63/2.00  --prop_impl_unit_size                   0
% 11.63/2.00  --prop_impl_unit                        []
% 11.63/2.00  --share_sel_clauses                     true
% 11.63/2.00  --reset_solvers                         false
% 11.63/2.00  --bc_imp_inh                            [conj_cone]
% 11.63/2.00  --conj_cone_tolerance                   3.
% 11.63/2.00  --extra_neg_conj                        none
% 11.63/2.00  --large_theory_mode                     true
% 11.63/2.00  --prolific_symb_bound                   200
% 11.63/2.00  --lt_threshold                          2000
% 11.63/2.00  --clause_weak_htbl                      true
% 11.63/2.00  --gc_record_bc_elim                     false
% 11.63/2.00  
% 11.63/2.00  ------ Preprocessing Options
% 11.63/2.00  
% 11.63/2.00  --preprocessing_flag                    true
% 11.63/2.00  --time_out_prep_mult                    0.1
% 11.63/2.00  --splitting_mode                        input
% 11.63/2.00  --splitting_grd                         true
% 11.63/2.00  --splitting_cvd                         false
% 11.63/2.00  --splitting_cvd_svl                     false
% 11.63/2.00  --splitting_nvd                         32
% 11.63/2.00  --sub_typing                            true
% 11.63/2.00  --prep_gs_sim                           true
% 11.63/2.00  --prep_unflatten                        true
% 11.63/2.00  --prep_res_sim                          true
% 11.63/2.00  --prep_upred                            true
% 11.63/2.00  --prep_sem_filter                       exhaustive
% 11.63/2.00  --prep_sem_filter_out                   false
% 11.63/2.00  --pred_elim                             true
% 11.63/2.00  --res_sim_input                         true
% 11.63/2.00  --eq_ax_congr_red                       true
% 11.63/2.00  --pure_diseq_elim                       true
% 11.63/2.00  --brand_transform                       false
% 11.63/2.00  --non_eq_to_eq                          false
% 11.63/2.00  --prep_def_merge                        true
% 11.63/2.00  --prep_def_merge_prop_impl              false
% 11.63/2.00  --prep_def_merge_mbd                    true
% 11.63/2.00  --prep_def_merge_tr_red                 false
% 11.63/2.00  --prep_def_merge_tr_cl                  false
% 11.63/2.00  --smt_preprocessing                     true
% 11.63/2.00  --smt_ac_axioms                         fast
% 11.63/2.00  --preprocessed_out                      false
% 11.63/2.00  --preprocessed_stats                    false
% 11.63/2.00  
% 11.63/2.00  ------ Abstraction refinement Options
% 11.63/2.00  
% 11.63/2.00  --abstr_ref                             []
% 11.63/2.00  --abstr_ref_prep                        false
% 11.63/2.00  --abstr_ref_until_sat                   false
% 11.63/2.00  --abstr_ref_sig_restrict                funpre
% 11.63/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.63/2.00  --abstr_ref_under                       []
% 11.63/2.00  
% 11.63/2.00  ------ SAT Options
% 11.63/2.00  
% 11.63/2.00  --sat_mode                              false
% 11.63/2.00  --sat_fm_restart_options                ""
% 11.63/2.00  --sat_gr_def                            false
% 11.63/2.00  --sat_epr_types                         true
% 11.63/2.00  --sat_non_cyclic_types                  false
% 11.63/2.00  --sat_finite_models                     false
% 11.63/2.00  --sat_fm_lemmas                         false
% 11.63/2.00  --sat_fm_prep                           false
% 11.63/2.00  --sat_fm_uc_incr                        true
% 11.63/2.00  --sat_out_model                         small
% 11.63/2.00  --sat_out_clauses                       false
% 11.63/2.00  
% 11.63/2.00  ------ QBF Options
% 11.63/2.00  
% 11.63/2.00  --qbf_mode                              false
% 11.63/2.00  --qbf_elim_univ                         false
% 11.63/2.00  --qbf_dom_inst                          none
% 11.63/2.00  --qbf_dom_pre_inst                      false
% 11.63/2.00  --qbf_sk_in                             false
% 11.63/2.00  --qbf_pred_elim                         true
% 11.63/2.00  --qbf_split                             512
% 11.63/2.00  
% 11.63/2.00  ------ BMC1 Options
% 11.63/2.00  
% 11.63/2.00  --bmc1_incremental                      false
% 11.63/2.00  --bmc1_axioms                           reachable_all
% 11.63/2.00  --bmc1_min_bound                        0
% 11.63/2.00  --bmc1_max_bound                        -1
% 11.63/2.00  --bmc1_max_bound_default                -1
% 11.63/2.00  --bmc1_symbol_reachability              true
% 11.63/2.00  --bmc1_property_lemmas                  false
% 11.63/2.00  --bmc1_k_induction                      false
% 11.63/2.00  --bmc1_non_equiv_states                 false
% 11.63/2.00  --bmc1_deadlock                         false
% 11.63/2.00  --bmc1_ucm                              false
% 11.63/2.00  --bmc1_add_unsat_core                   none
% 11.63/2.00  --bmc1_unsat_core_children              false
% 11.63/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.63/2.00  --bmc1_out_stat                         full
% 11.63/2.00  --bmc1_ground_init                      false
% 11.63/2.00  --bmc1_pre_inst_next_state              false
% 11.63/2.00  --bmc1_pre_inst_state                   false
% 11.63/2.00  --bmc1_pre_inst_reach_state             false
% 11.63/2.00  --bmc1_out_unsat_core                   false
% 11.63/2.00  --bmc1_aig_witness_out                  false
% 11.63/2.00  --bmc1_verbose                          false
% 11.63/2.00  --bmc1_dump_clauses_tptp                false
% 11.63/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.63/2.00  --bmc1_dump_file                        -
% 11.63/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.63/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.63/2.00  --bmc1_ucm_extend_mode                  1
% 11.63/2.00  --bmc1_ucm_init_mode                    2
% 11.63/2.00  --bmc1_ucm_cone_mode                    none
% 11.63/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.63/2.00  --bmc1_ucm_relax_model                  4
% 11.63/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.63/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.63/2.00  --bmc1_ucm_layered_model                none
% 11.63/2.00  --bmc1_ucm_max_lemma_size               10
% 11.63/2.00  
% 11.63/2.00  ------ AIG Options
% 11.63/2.00  
% 11.63/2.00  --aig_mode                              false
% 11.63/2.00  
% 11.63/2.00  ------ Instantiation Options
% 11.63/2.00  
% 11.63/2.00  --instantiation_flag                    true
% 11.63/2.00  --inst_sos_flag                         false
% 11.63/2.00  --inst_sos_phase                        true
% 11.63/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.63/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.63/2.00  --inst_lit_sel_side                     num_symb
% 11.63/2.00  --inst_solver_per_active                1400
% 11.63/2.00  --inst_solver_calls_frac                1.
% 11.63/2.00  --inst_passive_queue_type               priority_queues
% 11.63/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.63/2.00  --inst_passive_queues_freq              [25;2]
% 11.63/2.00  --inst_dismatching                      true
% 11.63/2.00  --inst_eager_unprocessed_to_passive     true
% 11.63/2.00  --inst_prop_sim_given                   true
% 11.63/2.00  --inst_prop_sim_new                     false
% 11.63/2.00  --inst_subs_new                         false
% 11.63/2.00  --inst_eq_res_simp                      false
% 11.63/2.00  --inst_subs_given                       false
% 11.63/2.00  --inst_orphan_elimination               true
% 11.63/2.00  --inst_learning_loop_flag               true
% 11.63/2.00  --inst_learning_start                   3000
% 11.63/2.00  --inst_learning_factor                  2
% 11.63/2.00  --inst_start_prop_sim_after_learn       3
% 11.63/2.00  --inst_sel_renew                        solver
% 11.63/2.00  --inst_lit_activity_flag                true
% 11.63/2.00  --inst_restr_to_given                   false
% 11.63/2.00  --inst_activity_threshold               500
% 11.63/2.00  --inst_out_proof                        true
% 11.63/2.00  
% 11.63/2.00  ------ Resolution Options
% 11.63/2.00  
% 11.63/2.00  --resolution_flag                       true
% 11.63/2.00  --res_lit_sel                           adaptive
% 11.63/2.00  --res_lit_sel_side                      none
% 11.63/2.00  --res_ordering                          kbo
% 11.63/2.00  --res_to_prop_solver                    active
% 11.63/2.00  --res_prop_simpl_new                    false
% 11.63/2.00  --res_prop_simpl_given                  true
% 11.63/2.00  --res_passive_queue_type                priority_queues
% 11.63/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.63/2.00  --res_passive_queues_freq               [15;5]
% 11.63/2.00  --res_forward_subs                      full
% 11.63/2.00  --res_backward_subs                     full
% 11.63/2.00  --res_forward_subs_resolution           true
% 11.63/2.00  --res_backward_subs_resolution          true
% 11.63/2.00  --res_orphan_elimination                true
% 11.63/2.00  --res_time_limit                        2.
% 11.63/2.00  --res_out_proof                         true
% 11.63/2.00  
% 11.63/2.00  ------ Superposition Options
% 11.63/2.00  
% 11.63/2.00  --superposition_flag                    true
% 11.63/2.00  --sup_passive_queue_type                priority_queues
% 11.63/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.63/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.63/2.00  --demod_completeness_check              fast
% 11.63/2.00  --demod_use_ground                      true
% 11.63/2.00  --sup_to_prop_solver                    passive
% 11.63/2.00  --sup_prop_simpl_new                    true
% 11.63/2.00  --sup_prop_simpl_given                  true
% 11.63/2.00  --sup_fun_splitting                     false
% 11.63/2.00  --sup_smt_interval                      50000
% 11.63/2.00  
% 11.63/2.00  ------ Superposition Simplification Setup
% 11.63/2.00  
% 11.63/2.00  --sup_indices_passive                   []
% 11.63/2.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.63/2.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.63/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.63/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.63/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.63/2.00  --sup_full_bw                           [BwDemod]
% 11.63/2.00  --sup_immed_triv                        [TrivRules]
% 11.63/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.63/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.63/2.00  --sup_immed_bw_main                     []
% 11.63/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.63/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.63/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.63/2.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.63/2.00  
% 11.63/2.00  ------ Combination Options
% 11.63/2.00  
% 11.63/2.00  --comb_res_mult                         3
% 11.63/2.00  --comb_sup_mult                         2
% 11.63/2.00  --comb_inst_mult                        10
% 11.63/2.00  
% 11.63/2.00  ------ Debug Options
% 11.63/2.00  
% 11.63/2.00  --dbg_backtrace                         false
% 11.63/2.00  --dbg_dump_prop_clauses                 false
% 11.63/2.00  --dbg_dump_prop_clauses_file            -
% 11.63/2.00  --dbg_out_stat                          false
% 11.63/2.00  ------ Parsing...
% 11.63/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.63/2.00  
% 11.63/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.63/2.00  
% 11.63/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.63/2.00  
% 11.63/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.63/2.00  ------ Proving...
% 11.63/2.00  ------ Problem Properties 
% 11.63/2.00  
% 11.63/2.00  
% 11.63/2.00  clauses                                 43
% 11.63/2.00  conjectures                             10
% 11.63/2.00  EPR                                     12
% 11.63/2.00  Horn                                    32
% 11.63/2.00  unary                                   11
% 11.63/2.00  binary                                  9
% 11.63/2.00  lits                                    125
% 11.63/2.00  lits eq                                 23
% 11.63/2.00  fd_pure                                 0
% 11.63/2.00  fd_pseudo                               0
% 11.63/2.00  fd_cond                                 4
% 11.63/2.00  fd_pseudo_cond                          4
% 11.63/2.00  AC symbols                              0
% 11.63/2.00  
% 11.63/2.00  ------ Schedule dynamic 5 is on 
% 11.63/2.00  
% 11.63/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.63/2.00  
% 11.63/2.00  
% 11.63/2.00  ------ 
% 11.63/2.00  Current options:
% 11.63/2.00  ------ 
% 11.63/2.00  
% 11.63/2.00  ------ Input Options
% 11.63/2.00  
% 11.63/2.00  --out_options                           all
% 11.63/2.00  --tptp_safe_out                         true
% 11.63/2.00  --problem_path                          ""
% 11.63/2.00  --include_path                          ""
% 11.63/2.00  --clausifier                            res/vclausify_rel
% 11.63/2.00  --clausifier_options                    --mode clausify
% 11.63/2.00  --stdin                                 false
% 11.63/2.00  --stats_out                             all
% 11.63/2.00  
% 11.63/2.00  ------ General Options
% 11.63/2.00  
% 11.63/2.00  --fof                                   false
% 11.63/2.00  --time_out_real                         305.
% 11.63/2.00  --time_out_virtual                      -1.
% 11.63/2.00  --symbol_type_check                     false
% 11.63/2.00  --clausify_out                          false
% 11.63/2.00  --sig_cnt_out                           false
% 11.63/2.00  --trig_cnt_out                          false
% 11.63/2.00  --trig_cnt_out_tolerance                1.
% 11.63/2.00  --trig_cnt_out_sk_spl                   false
% 11.63/2.00  --abstr_cl_out                          false
% 11.63/2.00  
% 11.63/2.00  ------ Global Options
% 11.63/2.00  
% 11.63/2.00  --schedule                              default
% 11.63/2.00  --add_important_lit                     false
% 11.63/2.00  --prop_solver_per_cl                    1000
% 11.63/2.00  --min_unsat_core                        false
% 11.63/2.00  --soft_assumptions                      false
% 11.63/2.00  --soft_lemma_size                       3
% 11.63/2.00  --prop_impl_unit_size                   0
% 11.63/2.00  --prop_impl_unit                        []
% 11.63/2.00  --share_sel_clauses                     true
% 11.63/2.00  --reset_solvers                         false
% 11.63/2.00  --bc_imp_inh                            [conj_cone]
% 11.63/2.00  --conj_cone_tolerance                   3.
% 11.63/2.00  --extra_neg_conj                        none
% 11.63/2.00  --large_theory_mode                     true
% 11.63/2.00  --prolific_symb_bound                   200
% 11.63/2.00  --lt_threshold                          2000
% 11.63/2.00  --clause_weak_htbl                      true
% 11.63/2.00  --gc_record_bc_elim                     false
% 11.63/2.00  
% 11.63/2.00  ------ Preprocessing Options
% 11.63/2.00  
% 11.63/2.00  --preprocessing_flag                    true
% 11.63/2.00  --time_out_prep_mult                    0.1
% 11.63/2.00  --splitting_mode                        input
% 11.63/2.00  --splitting_grd                         true
% 11.63/2.00  --splitting_cvd                         false
% 11.63/2.00  --splitting_cvd_svl                     false
% 11.63/2.00  --splitting_nvd                         32
% 11.63/2.00  --sub_typing                            true
% 11.63/2.00  --prep_gs_sim                           true
% 11.63/2.00  --prep_unflatten                        true
% 11.63/2.00  --prep_res_sim                          true
% 11.63/2.00  --prep_upred                            true
% 11.63/2.00  --prep_sem_filter                       exhaustive
% 11.63/2.00  --prep_sem_filter_out                   false
% 11.63/2.00  --pred_elim                             true
% 11.63/2.00  --res_sim_input                         true
% 11.63/2.00  --eq_ax_congr_red                       true
% 11.63/2.00  --pure_diseq_elim                       true
% 11.63/2.00  --brand_transform                       false
% 11.63/2.00  --non_eq_to_eq                          false
% 11.63/2.00  --prep_def_merge                        true
% 11.63/2.00  --prep_def_merge_prop_impl              false
% 11.63/2.00  --prep_def_merge_mbd                    true
% 11.63/2.00  --prep_def_merge_tr_red                 false
% 11.63/2.00  --prep_def_merge_tr_cl                  false
% 11.63/2.00  --smt_preprocessing                     true
% 11.63/2.00  --smt_ac_axioms                         fast
% 11.63/2.00  --preprocessed_out                      false
% 11.63/2.00  --preprocessed_stats                    false
% 11.63/2.00  
% 11.63/2.00  ------ Abstraction refinement Options
% 11.63/2.00  
% 11.63/2.00  --abstr_ref                             []
% 11.63/2.00  --abstr_ref_prep                        false
% 11.63/2.00  --abstr_ref_until_sat                   false
% 11.63/2.00  --abstr_ref_sig_restrict                funpre
% 11.63/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.63/2.00  --abstr_ref_under                       []
% 11.63/2.00  
% 11.63/2.00  ------ SAT Options
% 11.63/2.00  
% 11.63/2.00  --sat_mode                              false
% 11.63/2.00  --sat_fm_restart_options                ""
% 11.63/2.00  --sat_gr_def                            false
% 11.63/2.00  --sat_epr_types                         true
% 11.63/2.00  --sat_non_cyclic_types                  false
% 11.63/2.00  --sat_finite_models                     false
% 11.63/2.00  --sat_fm_lemmas                         false
% 11.63/2.00  --sat_fm_prep                           false
% 11.63/2.00  --sat_fm_uc_incr                        true
% 11.63/2.00  --sat_out_model                         small
% 11.63/2.00  --sat_out_clauses                       false
% 11.63/2.00  
% 11.63/2.00  ------ QBF Options
% 11.63/2.00  
% 11.63/2.00  --qbf_mode                              false
% 11.63/2.00  --qbf_elim_univ                         false
% 11.63/2.00  --qbf_dom_inst                          none
% 11.63/2.00  --qbf_dom_pre_inst                      false
% 11.63/2.00  --qbf_sk_in                             false
% 11.63/2.00  --qbf_pred_elim                         true
% 11.63/2.00  --qbf_split                             512
% 11.63/2.00  
% 11.63/2.00  ------ BMC1 Options
% 11.63/2.00  
% 11.63/2.00  --bmc1_incremental                      false
% 11.63/2.00  --bmc1_axioms                           reachable_all
% 11.63/2.00  --bmc1_min_bound                        0
% 11.63/2.00  --bmc1_max_bound                        -1
% 11.63/2.00  --bmc1_max_bound_default                -1
% 11.63/2.00  --bmc1_symbol_reachability              true
% 11.63/2.00  --bmc1_property_lemmas                  false
% 11.63/2.00  --bmc1_k_induction                      false
% 11.63/2.00  --bmc1_non_equiv_states                 false
% 11.63/2.00  --bmc1_deadlock                         false
% 11.63/2.00  --bmc1_ucm                              false
% 11.63/2.00  --bmc1_add_unsat_core                   none
% 11.63/2.00  --bmc1_unsat_core_children              false
% 11.63/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.63/2.00  --bmc1_out_stat                         full
% 11.63/2.00  --bmc1_ground_init                      false
% 11.63/2.00  --bmc1_pre_inst_next_state              false
% 11.63/2.00  --bmc1_pre_inst_state                   false
% 11.63/2.00  --bmc1_pre_inst_reach_state             false
% 11.63/2.00  --bmc1_out_unsat_core                   false
% 11.63/2.00  --bmc1_aig_witness_out                  false
% 11.63/2.00  --bmc1_verbose                          false
% 11.63/2.00  --bmc1_dump_clauses_tptp                false
% 11.63/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.63/2.00  --bmc1_dump_file                        -
% 11.63/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.63/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.63/2.00  --bmc1_ucm_extend_mode                  1
% 11.63/2.00  --bmc1_ucm_init_mode                    2
% 11.63/2.00  --bmc1_ucm_cone_mode                    none
% 11.63/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.63/2.00  --bmc1_ucm_relax_model                  4
% 11.63/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.63/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.63/2.00  --bmc1_ucm_layered_model                none
% 11.63/2.00  --bmc1_ucm_max_lemma_size               10
% 11.63/2.00  
% 11.63/2.00  ------ AIG Options
% 11.63/2.00  
% 11.63/2.00  --aig_mode                              false
% 11.63/2.00  
% 11.63/2.00  ------ Instantiation Options
% 11.63/2.00  
% 11.63/2.00  --instantiation_flag                    true
% 11.63/2.00  --inst_sos_flag                         false
% 11.63/2.00  --inst_sos_phase                        true
% 11.63/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.63/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.63/2.00  --inst_lit_sel_side                     none
% 11.63/2.00  --inst_solver_per_active                1400
% 11.63/2.00  --inst_solver_calls_frac                1.
% 11.63/2.00  --inst_passive_queue_type               priority_queues
% 11.63/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.63/2.00  --inst_passive_queues_freq              [25;2]
% 11.63/2.00  --inst_dismatching                      true
% 11.63/2.00  --inst_eager_unprocessed_to_passive     true
% 11.63/2.00  --inst_prop_sim_given                   true
% 11.63/2.00  --inst_prop_sim_new                     false
% 11.63/2.00  --inst_subs_new                         false
% 11.63/2.00  --inst_eq_res_simp                      false
% 11.63/2.00  --inst_subs_given                       false
% 11.63/2.00  --inst_orphan_elimination               true
% 11.63/2.00  --inst_learning_loop_flag               true
% 11.63/2.00  --inst_learning_start                   3000
% 11.63/2.00  --inst_learning_factor                  2
% 11.63/2.00  --inst_start_prop_sim_after_learn       3
% 11.63/2.00  --inst_sel_renew                        solver
% 11.63/2.00  --inst_lit_activity_flag                true
% 11.63/2.00  --inst_restr_to_given                   false
% 11.63/2.00  --inst_activity_threshold               500
% 11.63/2.00  --inst_out_proof                        true
% 11.63/2.00  
% 11.63/2.00  ------ Resolution Options
% 11.63/2.00  
% 11.63/2.00  --resolution_flag                       false
% 11.63/2.00  --res_lit_sel                           adaptive
% 11.63/2.00  --res_lit_sel_side                      none
% 11.63/2.00  --res_ordering                          kbo
% 11.63/2.00  --res_to_prop_solver                    active
% 11.63/2.00  --res_prop_simpl_new                    false
% 11.63/2.00  --res_prop_simpl_given                  true
% 11.63/2.00  --res_passive_queue_type                priority_queues
% 11.63/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.63/2.00  --res_passive_queues_freq               [15;5]
% 11.63/2.00  --res_forward_subs                      full
% 11.63/2.00  --res_backward_subs                     full
% 11.63/2.00  --res_forward_subs_resolution           true
% 11.63/2.00  --res_backward_subs_resolution          true
% 11.63/2.00  --res_orphan_elimination                true
% 11.63/2.00  --res_time_limit                        2.
% 11.63/2.00  --res_out_proof                         true
% 11.63/2.00  
% 11.63/2.00  ------ Superposition Options
% 11.63/2.00  
% 11.63/2.00  --superposition_flag                    true
% 11.63/2.00  --sup_passive_queue_type                priority_queues
% 11.63/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.63/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.63/2.00  --demod_completeness_check              fast
% 11.63/2.00  --demod_use_ground                      true
% 11.63/2.00  --sup_to_prop_solver                    passive
% 11.63/2.00  --sup_prop_simpl_new                    true
% 11.63/2.00  --sup_prop_simpl_given                  true
% 11.63/2.00  --sup_fun_splitting                     false
% 11.63/2.00  --sup_smt_interval                      50000
% 11.63/2.00  
% 11.63/2.00  ------ Superposition Simplification Setup
% 11.63/2.00  
% 11.63/2.00  --sup_indices_passive                   []
% 11.63/2.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.63/2.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.63/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.63/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.63/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.63/2.00  --sup_full_bw                           [BwDemod]
% 11.63/2.00  --sup_immed_triv                        [TrivRules]
% 11.63/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.63/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.63/2.00  --sup_immed_bw_main                     []
% 11.63/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.63/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.63/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.63/2.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.63/2.00  
% 11.63/2.00  ------ Combination Options
% 11.63/2.00  
% 11.63/2.00  --comb_res_mult                         3
% 11.63/2.00  --comb_sup_mult                         2
% 11.63/2.00  --comb_inst_mult                        10
% 11.63/2.00  
% 11.63/2.00  ------ Debug Options
% 11.63/2.00  
% 11.63/2.00  --dbg_backtrace                         false
% 11.63/2.00  --dbg_dump_prop_clauses                 false
% 11.63/2.00  --dbg_dump_prop_clauses_file            -
% 11.63/2.00  --dbg_out_stat                          false
% 11.63/2.00  
% 11.63/2.00  
% 11.63/2.00  
% 11.63/2.00  
% 11.63/2.00  ------ Proving...
% 11.63/2.00  
% 11.63/2.00  
% 11.63/2.00  % SZS status Theorem for theBenchmark.p
% 11.63/2.00  
% 11.63/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.63/2.00  
% 11.63/2.00  fof(f19,conjecture,(
% 11.63/2.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 11.63/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/2.00  
% 11.63/2.00  fof(f20,negated_conjecture,(
% 11.63/2.00    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 11.63/2.00    inference(negated_conjecture,[],[f19])).
% 11.63/2.00  
% 11.63/2.00  fof(f45,plain,(
% 11.63/2.00    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 11.63/2.00    inference(ennf_transformation,[],[f20])).
% 11.63/2.00  
% 11.63/2.00  fof(f46,plain,(
% 11.63/2.00    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 11.63/2.00    inference(flattening,[],[f45])).
% 11.63/2.00  
% 11.63/2.00  fof(f66,plain,(
% 11.63/2.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK10) != k7_partfun1(X0,X4,k1_funct_1(X3,sK10)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK10,X1))) )),
% 11.63/2.00    introduced(choice_axiom,[])).
% 11.63/2.00  
% 11.63/2.00  fof(f65,plain,(
% 11.63/2.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK9),X5) != k7_partfun1(X0,sK9,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK9)) & m1_subset_1(X5,X1)) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK9))) )),
% 11.63/2.00    introduced(choice_axiom,[])).
% 11.63/2.00  
% 11.63/2.00  fof(f64,plain,(
% 11.63/2.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,sK8,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(sK8,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK8),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK8,X1,X2) & v1_funct_1(sK8))) )),
% 11.63/2.00    introduced(choice_axiom,[])).
% 11.63/2.00  
% 11.63/2.00  fof(f63,plain,(
% 11.63/2.00    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK6,sK7,sK5,X3,X4),X5) != k7_partfun1(sK5,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK6 & r1_tarski(k2_relset_1(sK6,sK7,X3),k1_relset_1(sK7,sK5,X4)) & m1_subset_1(X5,sK6)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK7,sK5))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_2(X3,sK6,sK7) & v1_funct_1(X3)) & ~v1_xboole_0(sK7))),
% 11.63/2.00    introduced(choice_axiom,[])).
% 11.63/2.00  
% 11.63/2.00  fof(f67,plain,(
% 11.63/2.00    (((k1_funct_1(k8_funct_2(sK6,sK7,sK5,sK8,sK9),sK10) != k7_partfun1(sK5,sK9,k1_funct_1(sK8,sK10)) & k1_xboole_0 != sK6 & r1_tarski(k2_relset_1(sK6,sK7,sK8),k1_relset_1(sK7,sK5,sK9)) & m1_subset_1(sK10,sK6)) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK5))) & v1_funct_1(sK9)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_2(sK8,sK6,sK7) & v1_funct_1(sK8)) & ~v1_xboole_0(sK7)),
% 11.63/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9,sK10])],[f46,f66,f65,f64,f63])).
% 11.63/2.00  
% 11.63/2.00  fof(f110,plain,(
% 11.63/2.00    m1_subset_1(sK10,sK6)),
% 11.63/2.00    inference(cnf_transformation,[],[f67])).
% 11.63/2.00  
% 11.63/2.00  fof(f5,axiom,(
% 11.63/2.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 11.63/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/2.00  
% 11.63/2.00  fof(f24,plain,(
% 11.63/2.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 11.63/2.00    inference(ennf_transformation,[],[f5])).
% 11.63/2.00  
% 11.63/2.00  fof(f25,plain,(
% 11.63/2.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 11.63/2.00    inference(flattening,[],[f24])).
% 11.63/2.00  
% 11.63/2.00  fof(f75,plain,(
% 11.63/2.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 11.63/2.00    inference(cnf_transformation,[],[f25])).
% 11.63/2.00  
% 11.63/2.00  fof(f112,plain,(
% 11.63/2.00    k1_xboole_0 != sK6),
% 11.63/2.00    inference(cnf_transformation,[],[f67])).
% 11.63/2.00  
% 11.63/2.00  fof(f4,axiom,(
% 11.63/2.00    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 11.63/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/2.00  
% 11.63/2.00  fof(f23,plain,(
% 11.63/2.00    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 11.63/2.00    inference(ennf_transformation,[],[f4])).
% 11.63/2.00  
% 11.63/2.00  fof(f74,plain,(
% 11.63/2.00    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 11.63/2.00    inference(cnf_transformation,[],[f23])).
% 11.63/2.00  
% 11.63/2.00  fof(f1,axiom,(
% 11.63/2.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 11.63/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/2.00  
% 11.63/2.00  fof(f47,plain,(
% 11.63/2.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 11.63/2.00    inference(nnf_transformation,[],[f1])).
% 11.63/2.00  
% 11.63/2.00  fof(f48,plain,(
% 11.63/2.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 11.63/2.00    inference(rectify,[],[f47])).
% 11.63/2.00  
% 11.63/2.00  fof(f49,plain,(
% 11.63/2.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 11.63/2.00    introduced(choice_axiom,[])).
% 11.63/2.00  
% 11.63/2.00  fof(f50,plain,(
% 11.63/2.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 11.63/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f49])).
% 11.63/2.00  
% 11.63/2.00  fof(f69,plain,(
% 11.63/2.00    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 11.63/2.00    inference(cnf_transformation,[],[f50])).
% 11.63/2.00  
% 11.63/2.00  fof(f3,axiom,(
% 11.63/2.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 11.63/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/2.00  
% 11.63/2.00  fof(f73,plain,(
% 11.63/2.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 11.63/2.00    inference(cnf_transformation,[],[f3])).
% 11.63/2.00  
% 11.63/2.00  fof(f8,axiom,(
% 11.63/2.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 11.63/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/2.00  
% 11.63/2.00  fof(f29,plain,(
% 11.63/2.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 11.63/2.00    inference(ennf_transformation,[],[f8])).
% 11.63/2.00  
% 11.63/2.00  fof(f84,plain,(
% 11.63/2.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 11.63/2.00    inference(cnf_transformation,[],[f29])).
% 11.63/2.00  
% 11.63/2.00  fof(f109,plain,(
% 11.63/2.00    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK5)))),
% 11.63/2.00    inference(cnf_transformation,[],[f67])).
% 11.63/2.00  
% 11.63/2.00  fof(f10,axiom,(
% 11.63/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.63/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/2.00  
% 11.63/2.00  fof(f21,plain,(
% 11.63/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 11.63/2.00    inference(pure_predicate_removal,[],[f10])).
% 11.63/2.00  
% 11.63/2.00  fof(f31,plain,(
% 11.63/2.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.63/2.00    inference(ennf_transformation,[],[f21])).
% 11.63/2.00  
% 11.63/2.00  fof(f86,plain,(
% 11.63/2.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.63/2.00    inference(cnf_transformation,[],[f31])).
% 11.63/2.00  
% 11.63/2.00  fof(f7,axiom,(
% 11.63/2.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 11.63/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/2.00  
% 11.63/2.00  fof(f27,plain,(
% 11.63/2.00    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.63/2.00    inference(ennf_transformation,[],[f7])).
% 11.63/2.00  
% 11.63/2.00  fof(f28,plain,(
% 11.63/2.00    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.63/2.00    inference(flattening,[],[f27])).
% 11.63/2.00  
% 11.63/2.00  fof(f56,plain,(
% 11.63/2.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.63/2.00    inference(nnf_transformation,[],[f28])).
% 11.63/2.00  
% 11.63/2.00  fof(f57,plain,(
% 11.63/2.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.63/2.00    inference(rectify,[],[f56])).
% 11.63/2.00  
% 11.63/2.00  fof(f60,plain,(
% 11.63/2.00    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))))),
% 11.63/2.00    introduced(choice_axiom,[])).
% 11.63/2.00  
% 11.63/2.00  fof(f59,plain,(
% 11.63/2.00    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1)) = X2 & r2_hidden(sK3(X0,X1),k1_relat_1(X0))))) )),
% 11.63/2.00    introduced(choice_axiom,[])).
% 11.63/2.00  
% 11.63/2.00  fof(f58,plain,(
% 11.63/2.00    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK2(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1))))),
% 11.63/2.00    introduced(choice_axiom,[])).
% 11.63/2.00  
% 11.63/2.00  fof(f61,plain,(
% 11.63/2.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & ((k1_funct_1(X0,sK3(X0,X1)) = sK2(X0,X1) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.63/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f57,f60,f59,f58])).
% 11.63/2.00  
% 11.63/2.00  fof(f80,plain,(
% 11.63/2.00    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.63/2.00    inference(cnf_transformation,[],[f61])).
% 11.63/2.00  
% 11.63/2.00  fof(f114,plain,(
% 11.63/2.00    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.63/2.00    inference(equality_resolution,[],[f80])).
% 11.63/2.00  
% 11.63/2.00  fof(f115,plain,(
% 11.63/2.00    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.63/2.00    inference(equality_resolution,[],[f114])).
% 11.63/2.00  
% 11.63/2.00  fof(f107,plain,(
% 11.63/2.00    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))),
% 11.63/2.00    inference(cnf_transformation,[],[f67])).
% 11.63/2.00  
% 11.63/2.00  fof(f13,axiom,(
% 11.63/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 11.63/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/2.00  
% 11.63/2.00  fof(f34,plain,(
% 11.63/2.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.63/2.00    inference(ennf_transformation,[],[f13])).
% 11.63/2.00  
% 11.63/2.00  fof(f89,plain,(
% 11.63/2.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.63/2.00    inference(cnf_transformation,[],[f34])).
% 11.63/2.00  
% 11.63/2.00  fof(f111,plain,(
% 11.63/2.00    r1_tarski(k2_relset_1(sK6,sK7,sK8),k1_relset_1(sK7,sK5,sK9))),
% 11.63/2.00    inference(cnf_transformation,[],[f67])).
% 11.63/2.00  
% 11.63/2.00  fof(f12,axiom,(
% 11.63/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 11.63/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/2.00  
% 11.63/2.00  fof(f33,plain,(
% 11.63/2.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.63/2.00    inference(ennf_transformation,[],[f12])).
% 11.63/2.00  
% 11.63/2.00  fof(f88,plain,(
% 11.63/2.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.63/2.00    inference(cnf_transformation,[],[f33])).
% 11.63/2.00  
% 11.63/2.00  fof(f2,axiom,(
% 11.63/2.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.63/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/2.00  
% 11.63/2.00  fof(f22,plain,(
% 11.63/2.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 11.63/2.00    inference(ennf_transformation,[],[f2])).
% 11.63/2.00  
% 11.63/2.00  fof(f51,plain,(
% 11.63/2.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 11.63/2.00    inference(nnf_transformation,[],[f22])).
% 11.63/2.00  
% 11.63/2.00  fof(f52,plain,(
% 11.63/2.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.63/2.00    inference(rectify,[],[f51])).
% 11.63/2.00  
% 11.63/2.00  fof(f53,plain,(
% 11.63/2.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 11.63/2.00    introduced(choice_axiom,[])).
% 11.63/2.00  
% 11.63/2.00  fof(f54,plain,(
% 11.63/2.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.63/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f52,f53])).
% 11.63/2.00  
% 11.63/2.00  fof(f70,plain,(
% 11.63/2.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 11.63/2.00    inference(cnf_transformation,[],[f54])).
% 11.63/2.00  
% 11.63/2.00  fof(f15,axiom,(
% 11.63/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 11.63/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/2.00  
% 11.63/2.00  fof(f37,plain,(
% 11.63/2.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.63/2.00    inference(ennf_transformation,[],[f15])).
% 11.63/2.00  
% 11.63/2.00  fof(f38,plain,(
% 11.63/2.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.63/2.00    inference(flattening,[],[f37])).
% 11.63/2.00  
% 11.63/2.00  fof(f62,plain,(
% 11.63/2.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.63/2.00    inference(nnf_transformation,[],[f38])).
% 11.63/2.00  
% 11.63/2.00  fof(f93,plain,(
% 11.63/2.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.63/2.00    inference(cnf_transformation,[],[f62])).
% 11.63/2.00  
% 11.63/2.00  fof(f104,plain,(
% 11.63/2.00    ~v1_xboole_0(sK7)),
% 11.63/2.00    inference(cnf_transformation,[],[f67])).
% 11.63/2.00  
% 11.63/2.00  fof(f106,plain,(
% 11.63/2.00    v1_funct_2(sK8,sK6,sK7)),
% 11.63/2.00    inference(cnf_transformation,[],[f67])).
% 11.63/2.00  
% 11.63/2.00  fof(f105,plain,(
% 11.63/2.00    v1_funct_1(sK8)),
% 11.63/2.00    inference(cnf_transformation,[],[f67])).
% 11.63/2.00  
% 11.63/2.00  fof(f9,axiom,(
% 11.63/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 11.63/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/2.00  
% 11.63/2.00  fof(f30,plain,(
% 11.63/2.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.63/2.00    inference(ennf_transformation,[],[f9])).
% 11.63/2.00  
% 11.63/2.00  fof(f85,plain,(
% 11.63/2.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.63/2.00    inference(cnf_transformation,[],[f30])).
% 11.63/2.00  
% 11.63/2.00  fof(f16,axiom,(
% 11.63/2.00    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)))),
% 11.63/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/2.00  
% 11.63/2.00  fof(f39,plain,(
% 11.63/2.00    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 11.63/2.00    inference(ennf_transformation,[],[f16])).
% 11.63/2.00  
% 11.63/2.00  fof(f40,plain,(
% 11.63/2.00    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.63/2.00    inference(flattening,[],[f39])).
% 11.63/2.00  
% 11.63/2.00  fof(f99,plain,(
% 11.63/2.00    ( ! [X2,X0,X1] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.63/2.00    inference(cnf_transformation,[],[f40])).
% 11.63/2.00  
% 11.63/2.00  fof(f108,plain,(
% 11.63/2.00    v1_funct_1(sK9)),
% 11.63/2.00    inference(cnf_transformation,[],[f67])).
% 11.63/2.00  
% 11.63/2.00  fof(f17,axiom,(
% 11.63/2.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 11.63/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/2.00  
% 11.63/2.00  fof(f41,plain,(
% 11.63/2.00    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 11.63/2.00    inference(ennf_transformation,[],[f17])).
% 11.63/2.00  
% 11.63/2.00  fof(f42,plain,(
% 11.63/2.00    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 11.63/2.00    inference(flattening,[],[f41])).
% 11.63/2.00  
% 11.63/2.00  fof(f100,plain,(
% 11.63/2.00    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 11.63/2.00    inference(cnf_transformation,[],[f42])).
% 11.63/2.00  
% 11.63/2.00  fof(f113,plain,(
% 11.63/2.00    k1_funct_1(k8_funct_2(sK6,sK7,sK5,sK8,sK9),sK10) != k7_partfun1(sK5,sK9,k1_funct_1(sK8,sK10))),
% 11.63/2.00    inference(cnf_transformation,[],[f67])).
% 11.63/2.00  
% 11.63/2.00  cnf(c_39,negated_conjecture,
% 11.63/2.00      ( m1_subset_1(sK10,sK6) ),
% 11.63/2.00      inference(cnf_transformation,[],[f110]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_4116,plain,
% 11.63/2.00      ( m1_subset_1(sK10,sK6) = iProver_top ),
% 11.63/2.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_7,plain,
% 11.63/2.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 11.63/2.00      inference(cnf_transformation,[],[f75]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_4143,plain,
% 11.63/2.00      ( m1_subset_1(X0,X1) != iProver_top
% 11.63/2.00      | r2_hidden(X0,X1) = iProver_top
% 11.63/2.00      | v1_xboole_0(X1) = iProver_top ),
% 11.63/2.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_5869,plain,
% 11.63/2.00      ( r2_hidden(sK10,sK6) = iProver_top
% 11.63/2.00      | v1_xboole_0(sK6) = iProver_top ),
% 11.63/2.00      inference(superposition,[status(thm)],[c_4116,c_4143]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_37,negated_conjecture,
% 11.63/2.00      ( k1_xboole_0 != sK6 ),
% 11.63/2.00      inference(cnf_transformation,[],[f112]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_6,plain,
% 11.63/2.00      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 11.63/2.00      inference(cnf_transformation,[],[f74]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_4500,plain,
% 11.63/2.00      ( ~ v1_xboole_0(sK6)
% 11.63/2.00      | ~ v1_xboole_0(k1_xboole_0)
% 11.63/2.00      | k1_xboole_0 = sK6 ),
% 11.63/2.00      inference(instantiation,[status(thm)],[c_6]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_4501,plain,
% 11.63/2.00      ( k1_xboole_0 = sK6
% 11.63/2.00      | v1_xboole_0(sK6) != iProver_top
% 11.63/2.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 11.63/2.00      inference(predicate_to_equality,[status(thm)],[c_4500]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_0,plain,
% 11.63/2.00      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 11.63/2.00      inference(cnf_transformation,[],[f69]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_4150,plain,
% 11.63/2.00      ( r2_hidden(sK0(X0),X0) = iProver_top
% 11.63/2.00      | v1_xboole_0(X0) = iProver_top ),
% 11.63/2.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_5,plain,
% 11.63/2.00      ( r1_tarski(k1_xboole_0,X0) ),
% 11.63/2.00      inference(cnf_transformation,[],[f73]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_4145,plain,
% 11.63/2.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 11.63/2.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_16,plain,
% 11.63/2.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 11.63/2.00      inference(cnf_transformation,[],[f84]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_4134,plain,
% 11.63/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.63/2.00      | r2_hidden(X1,X0) != iProver_top ),
% 11.63/2.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_4811,plain,
% 11.63/2.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 11.63/2.00      inference(superposition,[status(thm)],[c_4145,c_4134]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_4873,plain,
% 11.63/2.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 11.63/2.00      inference(superposition,[status(thm)],[c_4150,c_4811]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_6391,plain,
% 11.63/2.00      ( r2_hidden(sK10,sK6) = iProver_top ),
% 11.63/2.00      inference(global_propositional_subsumption,
% 11.63/2.00                [status(thm)],
% 11.63/2.00                [c_5869,c_37,c_4501,c_4873]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_40,negated_conjecture,
% 11.63/2.00      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK5))) ),
% 11.63/2.00      inference(cnf_transformation,[],[f109]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_4115,plain,
% 11.63/2.00      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK5))) = iProver_top ),
% 11.63/2.00      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_18,plain,
% 11.63/2.00      ( v5_relat_1(X0,X1)
% 11.63/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 11.63/2.00      inference(cnf_transformation,[],[f86]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_4132,plain,
% 11.63/2.00      ( v5_relat_1(X0,X1) = iProver_top
% 11.63/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 11.63/2.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_5289,plain,
% 11.63/2.00      ( v5_relat_1(sK9,sK5) = iProver_top ),
% 11.63/2.00      inference(superposition,[status(thm)],[c_4115,c_4132]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_13,plain,
% 11.63/2.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 11.63/2.00      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 11.63/2.00      | ~ v1_funct_1(X1)
% 11.63/2.00      | ~ v1_relat_1(X1) ),
% 11.63/2.00      inference(cnf_transformation,[],[f115]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_4137,plain,
% 11.63/2.00      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 11.63/2.00      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 11.63/2.00      | v1_funct_1(X1) != iProver_top
% 11.63/2.00      | v1_relat_1(X1) != iProver_top ),
% 11.63/2.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_42,negated_conjecture,
% 11.63/2.00      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
% 11.63/2.00      inference(cnf_transformation,[],[f107]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_4113,plain,
% 11.63/2.00      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
% 11.63/2.00      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_21,plain,
% 11.63/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.63/2.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 11.63/2.00      inference(cnf_transformation,[],[f89]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_4129,plain,
% 11.63/2.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 11.63/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.63/2.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_5619,plain,
% 11.63/2.00      ( k2_relset_1(sK6,sK7,sK8) = k2_relat_1(sK8) ),
% 11.63/2.00      inference(superposition,[status(thm)],[c_4113,c_4129]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_38,negated_conjecture,
% 11.63/2.00      ( r1_tarski(k2_relset_1(sK6,sK7,sK8),k1_relset_1(sK7,sK5,sK9)) ),
% 11.63/2.00      inference(cnf_transformation,[],[f111]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_4117,plain,
% 11.63/2.00      ( r1_tarski(k2_relset_1(sK6,sK7,sK8),k1_relset_1(sK7,sK5,sK9)) = iProver_top ),
% 11.63/2.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_6106,plain,
% 11.63/2.00      ( r1_tarski(k2_relat_1(sK8),k1_relset_1(sK7,sK5,sK9)) = iProver_top ),
% 11.63/2.00      inference(demodulation,[status(thm)],[c_5619,c_4117]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_20,plain,
% 11.63/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.63/2.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 11.63/2.00      inference(cnf_transformation,[],[f88]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_4130,plain,
% 11.63/2.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 11.63/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.63/2.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_5745,plain,
% 11.63/2.00      ( k1_relset_1(sK7,sK5,sK9) = k1_relat_1(sK9) ),
% 11.63/2.00      inference(superposition,[status(thm)],[c_4115,c_4130]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_6223,plain,
% 11.63/2.00      ( r1_tarski(k2_relat_1(sK8),k1_relat_1(sK9)) = iProver_top ),
% 11.63/2.00      inference(light_normalisation,[status(thm)],[c_6106,c_5745]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_4,plain,
% 11.63/2.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 11.63/2.00      inference(cnf_transformation,[],[f70]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_4146,plain,
% 11.63/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.63/2.00      | r2_hidden(X2,X0) != iProver_top
% 11.63/2.00      | r2_hidden(X2,X1) = iProver_top ),
% 11.63/2.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_7268,plain,
% 11.63/2.00      ( r2_hidden(X0,k1_relat_1(sK9)) = iProver_top
% 11.63/2.00      | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top ),
% 11.63/2.00      inference(superposition,[status(thm)],[c_6223,c_4146]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_8909,plain,
% 11.63/2.00      ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 11.63/2.00      | r2_hidden(k1_funct_1(sK8,X0),k1_relat_1(sK9)) = iProver_top
% 11.63/2.00      | v1_funct_1(sK8) != iProver_top
% 11.63/2.00      | v1_relat_1(sK8) != iProver_top ),
% 11.63/2.00      inference(superposition,[status(thm)],[c_4137,c_7268]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_30,plain,
% 11.63/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.63/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.63/2.00      | k1_relset_1(X1,X2,X0) = X1
% 11.63/2.00      | k1_xboole_0 = X2 ),
% 11.63/2.00      inference(cnf_transformation,[],[f93]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_4122,plain,
% 11.63/2.00      ( k1_relset_1(X0,X1,X2) = X0
% 11.63/2.00      | k1_xboole_0 = X1
% 11.63/2.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 11.63/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.63/2.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_7684,plain,
% 11.63/2.00      ( k1_relset_1(sK6,sK7,sK8) = sK6
% 11.63/2.00      | sK7 = k1_xboole_0
% 11.63/2.00      | v1_funct_2(sK8,sK6,sK7) != iProver_top ),
% 11.63/2.00      inference(superposition,[status(thm)],[c_4113,c_4122]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_5746,plain,
% 11.63/2.00      ( k1_relset_1(sK6,sK7,sK8) = k1_relat_1(sK8) ),
% 11.63/2.00      inference(superposition,[status(thm)],[c_4113,c_4130]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_7688,plain,
% 11.63/2.00      ( k1_relat_1(sK8) = sK6
% 11.63/2.00      | sK7 = k1_xboole_0
% 11.63/2.00      | v1_funct_2(sK8,sK6,sK7) != iProver_top ),
% 11.63/2.00      inference(demodulation,[status(thm)],[c_7684,c_5746]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_45,negated_conjecture,
% 11.63/2.00      ( ~ v1_xboole_0(sK7) ),
% 11.63/2.00      inference(cnf_transformation,[],[f104]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_46,plain,
% 11.63/2.00      ( v1_xboole_0(sK7) != iProver_top ),
% 11.63/2.00      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_43,negated_conjecture,
% 11.63/2.00      ( v1_funct_2(sK8,sK6,sK7) ),
% 11.63/2.00      inference(cnf_transformation,[],[f106]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_48,plain,
% 11.63/2.00      ( v1_funct_2(sK8,sK6,sK7) = iProver_top ),
% 11.63/2.00      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_3412,plain,
% 11.63/2.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 11.63/2.00      theory(equality) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_4509,plain,
% 11.63/2.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK7) | sK7 != X0 ),
% 11.63/2.00      inference(instantiation,[status(thm)],[c_3412]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_4510,plain,
% 11.63/2.00      ( sK7 != X0
% 11.63/2.00      | v1_xboole_0(X0) != iProver_top
% 11.63/2.00      | v1_xboole_0(sK7) = iProver_top ),
% 11.63/2.00      inference(predicate_to_equality,[status(thm)],[c_4509]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_4512,plain,
% 11.63/2.00      ( sK7 != k1_xboole_0
% 11.63/2.00      | v1_xboole_0(sK7) = iProver_top
% 11.63/2.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 11.63/2.00      inference(instantiation,[status(thm)],[c_4510]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_7715,plain,
% 11.63/2.00      ( k1_relat_1(sK8) = sK6 ),
% 11.63/2.00      inference(global_propositional_subsumption,
% 11.63/2.00                [status(thm)],
% 11.63/2.00                [c_7688,c_46,c_48,c_4512,c_4873]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_8914,plain,
% 11.63/2.00      ( r2_hidden(X0,sK6) != iProver_top
% 11.63/2.00      | r2_hidden(k1_funct_1(sK8,X0),k1_relat_1(sK9)) = iProver_top
% 11.63/2.00      | v1_funct_1(sK8) != iProver_top
% 11.63/2.00      | v1_relat_1(sK8) != iProver_top ),
% 11.63/2.00      inference(light_normalisation,[status(thm)],[c_8909,c_7715]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_44,negated_conjecture,
% 11.63/2.00      ( v1_funct_1(sK8) ),
% 11.63/2.00      inference(cnf_transformation,[],[f105]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_47,plain,
% 11.63/2.00      ( v1_funct_1(sK8) = iProver_top ),
% 11.63/2.00      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_49,plain,
% 11.63/2.00      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
% 11.63/2.00      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_17,plain,
% 11.63/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.63/2.00      | v1_relat_1(X0) ),
% 11.63/2.00      inference(cnf_transformation,[],[f85]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_4506,plain,
% 11.63/2.00      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
% 11.63/2.00      | v1_relat_1(sK8) ),
% 11.63/2.00      inference(instantiation,[status(thm)],[c_17]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_4507,plain,
% 11.63/2.00      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
% 11.63/2.00      | v1_relat_1(sK8) = iProver_top ),
% 11.63/2.00      inference(predicate_to_equality,[status(thm)],[c_4506]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_9095,plain,
% 11.63/2.00      ( r2_hidden(X0,sK6) != iProver_top
% 11.63/2.00      | r2_hidden(k1_funct_1(sK8,X0),k1_relat_1(sK9)) = iProver_top ),
% 11.63/2.00      inference(global_propositional_subsumption,
% 11.63/2.00                [status(thm)],
% 11.63/2.00                [c_8914,c_47,c_49,c_4507]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_31,plain,
% 11.63/2.00      ( ~ v5_relat_1(X0,X1)
% 11.63/2.00      | ~ r2_hidden(X2,k1_relat_1(X0))
% 11.63/2.00      | ~ v1_funct_1(X0)
% 11.63/2.00      | ~ v1_relat_1(X0)
% 11.63/2.00      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 11.63/2.00      inference(cnf_transformation,[],[f99]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_4121,plain,
% 11.63/2.00      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
% 11.63/2.00      | v5_relat_1(X1,X0) != iProver_top
% 11.63/2.00      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 11.63/2.00      | v1_funct_1(X1) != iProver_top
% 11.63/2.00      | v1_relat_1(X1) != iProver_top ),
% 11.63/2.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_9104,plain,
% 11.63/2.00      ( k7_partfun1(X0,sK9,k1_funct_1(sK8,X1)) = k1_funct_1(sK9,k1_funct_1(sK8,X1))
% 11.63/2.00      | v5_relat_1(sK9,X0) != iProver_top
% 11.63/2.00      | r2_hidden(X1,sK6) != iProver_top
% 11.63/2.00      | v1_funct_1(sK9) != iProver_top
% 11.63/2.00      | v1_relat_1(sK9) != iProver_top ),
% 11.63/2.00      inference(superposition,[status(thm)],[c_9095,c_4121]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_41,negated_conjecture,
% 11.63/2.00      ( v1_funct_1(sK9) ),
% 11.63/2.00      inference(cnf_transformation,[],[f108]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_50,plain,
% 11.63/2.00      ( v1_funct_1(sK9) = iProver_top ),
% 11.63/2.00      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_51,plain,
% 11.63/2.00      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK5))) = iProver_top ),
% 11.63/2.00      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_4503,plain,
% 11.63/2.00      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK5)))
% 11.63/2.00      | v1_relat_1(sK9) ),
% 11.63/2.00      inference(instantiation,[status(thm)],[c_17]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_4504,plain,
% 11.63/2.00      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK5))) != iProver_top
% 11.63/2.00      | v1_relat_1(sK9) = iProver_top ),
% 11.63/2.00      inference(predicate_to_equality,[status(thm)],[c_4503]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_58955,plain,
% 11.63/2.00      ( k7_partfun1(X0,sK9,k1_funct_1(sK8,X1)) = k1_funct_1(sK9,k1_funct_1(sK8,X1))
% 11.63/2.00      | v5_relat_1(sK9,X0) != iProver_top
% 11.63/2.00      | r2_hidden(X1,sK6) != iProver_top ),
% 11.63/2.00      inference(global_propositional_subsumption,
% 11.63/2.00                [status(thm)],
% 11.63/2.00                [c_9104,c_50,c_51,c_4504]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_58962,plain,
% 11.63/2.00      ( k7_partfun1(sK5,sK9,k1_funct_1(sK8,X0)) = k1_funct_1(sK9,k1_funct_1(sK8,X0))
% 11.63/2.00      | r2_hidden(X0,sK6) != iProver_top ),
% 11.63/2.00      inference(superposition,[status(thm)],[c_5289,c_58955]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_59430,plain,
% 11.63/2.00      ( k7_partfun1(sK5,sK9,k1_funct_1(sK8,sK10)) = k1_funct_1(sK9,k1_funct_1(sK8,sK10)) ),
% 11.63/2.00      inference(superposition,[status(thm)],[c_6391,c_58962]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_32,plain,
% 11.63/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.63/2.00      | ~ m1_subset_1(X3,X1)
% 11.63/2.00      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 11.63/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.63/2.00      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X5,X4))
% 11.63/2.00      | ~ v1_funct_1(X4)
% 11.63/2.00      | ~ v1_funct_1(X0)
% 11.63/2.00      | v1_xboole_0(X2)
% 11.63/2.00      | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 11.63/2.00      | k1_xboole_0 = X1 ),
% 11.63/2.00      inference(cnf_transformation,[],[f100]) ).
% 11.63/2.00  
% 11.63/2.00  cnf(c_4120,plain,
% 11.63/2.00      ( k1_funct_1(k8_funct_2(X0,X1,X2,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
% 11.63/2.00      | k1_xboole_0 = X0
% 11.63/2.00      | v1_funct_2(X3,X0,X1) != iProver_top
% 11.63/2.00      | m1_subset_1(X5,X0) != iProver_top
% 11.63/2.00      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.63/2.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.63/2.00      | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
% 11.63/2.00      | v1_funct_1(X3) != iProver_top
% 11.63/2.00      | v1_funct_1(X4) != iProver_top
% 11.63/2.01      | v1_xboole_0(X1) = iProver_top ),
% 11.63/2.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.63/2.01  
% 11.63/2.01  cnf(c_6785,plain,
% 11.63/2.01      ( k1_funct_1(k8_funct_2(sK6,sK7,X0,sK8,X1),X2) = k1_funct_1(X1,k1_funct_1(sK8,X2))
% 11.63/2.01      | sK6 = k1_xboole_0
% 11.63/2.01      | v1_funct_2(sK8,sK6,sK7) != iProver_top
% 11.63/2.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK7,X0))) != iProver_top
% 11.63/2.01      | m1_subset_1(X2,sK6) != iProver_top
% 11.63/2.01      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
% 11.63/2.01      | r1_tarski(k2_relat_1(sK8),k1_relset_1(sK7,X0,X1)) != iProver_top
% 11.63/2.01      | v1_funct_1(X1) != iProver_top
% 11.63/2.01      | v1_funct_1(sK8) != iProver_top
% 11.63/2.01      | v1_xboole_0(sK7) = iProver_top ),
% 11.63/2.01      inference(superposition,[status(thm)],[c_5619,c_4120]) ).
% 11.63/2.01  
% 11.63/2.01  cnf(c_3410,plain,( X0 = X0 ),theory(equality) ).
% 11.63/2.01  
% 11.63/2.01  cnf(c_3439,plain,
% 11.63/2.01      ( k1_xboole_0 = k1_xboole_0 ),
% 11.63/2.01      inference(instantiation,[status(thm)],[c_3410]) ).
% 11.63/2.01  
% 11.63/2.01  cnf(c_3411,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.63/2.01  
% 11.63/2.01  cnf(c_4553,plain,
% 11.63/2.01      ( sK6 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK6 ),
% 11.63/2.01      inference(instantiation,[status(thm)],[c_3411]) ).
% 11.63/2.01  
% 11.63/2.01  cnf(c_4554,plain,
% 11.63/2.01      ( sK6 != k1_xboole_0
% 11.63/2.01      | k1_xboole_0 = sK6
% 11.63/2.01      | k1_xboole_0 != k1_xboole_0 ),
% 11.63/2.01      inference(instantiation,[status(thm)],[c_4553]) ).
% 11.63/2.01  
% 11.63/2.01  cnf(c_7377,plain,
% 11.63/2.01      ( m1_subset_1(X2,sK6) != iProver_top
% 11.63/2.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK7,X0))) != iProver_top
% 11.63/2.01      | k1_funct_1(k8_funct_2(sK6,sK7,X0,sK8,X1),X2) = k1_funct_1(X1,k1_funct_1(sK8,X2))
% 11.63/2.01      | r1_tarski(k2_relat_1(sK8),k1_relset_1(sK7,X0,X1)) != iProver_top
% 11.63/2.01      | v1_funct_1(X1) != iProver_top ),
% 11.63/2.01      inference(global_propositional_subsumption,
% 11.63/2.01                [status(thm)],
% 11.63/2.01                [c_6785,c_46,c_47,c_48,c_49,c_37,c_3439,c_4554]) ).
% 11.63/2.01  
% 11.63/2.01  cnf(c_7378,plain,
% 11.63/2.01      ( k1_funct_1(k8_funct_2(sK6,sK7,X0,sK8,X1),X2) = k1_funct_1(X1,k1_funct_1(sK8,X2))
% 11.63/2.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK7,X0))) != iProver_top
% 11.63/2.01      | m1_subset_1(X2,sK6) != iProver_top
% 11.63/2.01      | r1_tarski(k2_relat_1(sK8),k1_relset_1(sK7,X0,X1)) != iProver_top
% 11.63/2.01      | v1_funct_1(X1) != iProver_top ),
% 11.63/2.01      inference(renaming,[status(thm)],[c_7377]) ).
% 11.63/2.01  
% 11.63/2.01  cnf(c_7390,plain,
% 11.63/2.01      ( k1_funct_1(k8_funct_2(sK6,sK7,sK5,sK8,sK9),X0) = k1_funct_1(sK9,k1_funct_1(sK8,X0))
% 11.63/2.01      | m1_subset_1(X0,sK6) != iProver_top
% 11.63/2.01      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK5))) != iProver_top
% 11.63/2.01      | r1_tarski(k2_relat_1(sK8),k1_relat_1(sK9)) != iProver_top
% 11.63/2.01      | v1_funct_1(sK9) != iProver_top ),
% 11.63/2.01      inference(superposition,[status(thm)],[c_5745,c_7378]) ).
% 11.63/2.01  
% 11.63/2.01  cnf(c_7456,plain,
% 11.63/2.01      ( m1_subset_1(X0,sK6) != iProver_top
% 11.63/2.01      | k1_funct_1(k8_funct_2(sK6,sK7,sK5,sK8,sK9),X0) = k1_funct_1(sK9,k1_funct_1(sK8,X0)) ),
% 11.63/2.01      inference(global_propositional_subsumption,
% 11.63/2.01                [status(thm)],
% 11.63/2.01                [c_7390,c_50,c_51,c_6223]) ).
% 11.63/2.01  
% 11.63/2.01  cnf(c_7457,plain,
% 11.63/2.01      ( k1_funct_1(k8_funct_2(sK6,sK7,sK5,sK8,sK9),X0) = k1_funct_1(sK9,k1_funct_1(sK8,X0))
% 11.63/2.01      | m1_subset_1(X0,sK6) != iProver_top ),
% 11.63/2.01      inference(renaming,[status(thm)],[c_7456]) ).
% 11.63/2.01  
% 11.63/2.01  cnf(c_7464,plain,
% 11.63/2.01      ( k1_funct_1(k8_funct_2(sK6,sK7,sK5,sK8,sK9),sK10) = k1_funct_1(sK9,k1_funct_1(sK8,sK10)) ),
% 11.63/2.01      inference(superposition,[status(thm)],[c_4116,c_7457]) ).
% 11.63/2.01  
% 11.63/2.01  cnf(c_36,negated_conjecture,
% 11.63/2.01      ( k1_funct_1(k8_funct_2(sK6,sK7,sK5,sK8,sK9),sK10) != k7_partfun1(sK5,sK9,k1_funct_1(sK8,sK10)) ),
% 11.63/2.01      inference(cnf_transformation,[],[f113]) ).
% 11.63/2.01  
% 11.63/2.01  cnf(c_7466,plain,
% 11.63/2.01      ( k7_partfun1(sK5,sK9,k1_funct_1(sK8,sK10)) != k1_funct_1(sK9,k1_funct_1(sK8,sK10)) ),
% 11.63/2.01      inference(demodulation,[status(thm)],[c_7464,c_36]) ).
% 11.63/2.01  
% 11.63/2.01  cnf(contradiction,plain,
% 11.63/2.01      ( $false ),
% 11.63/2.01      inference(minisat,[status(thm)],[c_59430,c_7466]) ).
% 11.63/2.01  
% 11.63/2.01  
% 11.63/2.01  % SZS output end CNFRefutation for theBenchmark.p
% 11.63/2.01  
% 11.63/2.01  ------                               Statistics
% 11.63/2.01  
% 11.63/2.01  ------ General
% 11.63/2.01  
% 11.63/2.01  abstr_ref_over_cycles:                  0
% 11.63/2.01  abstr_ref_under_cycles:                 0
% 11.63/2.01  gc_basic_clause_elim:                   0
% 11.63/2.01  forced_gc_time:                         0
% 11.63/2.01  parsing_time:                           0.017
% 11.63/2.01  unif_index_cands_time:                  0.
% 11.63/2.01  unif_index_add_time:                    0.
% 11.63/2.01  orderings_time:                         0.
% 11.63/2.01  out_proof_time:                         0.013
% 11.63/2.01  total_time:                             1.401
% 11.63/2.01  num_of_symbols:                         60
% 11.63/2.01  num_of_terms:                           35617
% 11.63/2.01  
% 11.63/2.01  ------ Preprocessing
% 11.63/2.01  
% 11.63/2.01  num_of_splits:                          0
% 11.63/2.01  num_of_split_atoms:                     0
% 11.63/2.01  num_of_reused_defs:                     0
% 11.63/2.01  num_eq_ax_congr_red:                    42
% 11.63/2.01  num_of_sem_filtered_clauses:            1
% 11.63/2.01  num_of_subtypes:                        0
% 11.63/2.01  monotx_restored_types:                  0
% 11.63/2.01  sat_num_of_epr_types:                   0
% 11.63/2.01  sat_num_of_non_cyclic_types:            0
% 11.63/2.01  sat_guarded_non_collapsed_types:        0
% 11.63/2.01  num_pure_diseq_elim:                    0
% 11.63/2.01  simp_replaced_by:                       0
% 11.63/2.01  res_preprocessed:                       203
% 11.63/2.01  prep_upred:                             0
% 11.63/2.01  prep_unflattend:                        198
% 11.63/2.01  smt_new_axioms:                         0
% 11.63/2.01  pred_elim_cands:                        8
% 11.63/2.01  pred_elim:                              0
% 11.63/2.01  pred_elim_cl:                           0
% 11.63/2.01  pred_elim_cycles:                       8
% 11.63/2.01  merged_defs:                            0
% 11.63/2.01  merged_defs_ncl:                        0
% 11.63/2.01  bin_hyper_res:                          0
% 11.63/2.01  prep_cycles:                            4
% 11.63/2.01  pred_elim_time:                         0.059
% 11.63/2.01  splitting_time:                         0.
% 11.63/2.01  sem_filter_time:                        0.
% 11.63/2.01  monotx_time:                            0.001
% 11.63/2.01  subtype_inf_time:                       0.
% 11.63/2.01  
% 11.63/2.01  ------ Problem properties
% 11.63/2.01  
% 11.63/2.01  clauses:                                43
% 11.63/2.01  conjectures:                            10
% 11.63/2.01  epr:                                    12
% 11.63/2.01  horn:                                   32
% 11.63/2.01  ground:                                 10
% 11.63/2.01  unary:                                  11
% 11.63/2.01  binary:                                 9
% 11.63/2.01  lits:                                   125
% 11.63/2.01  lits_eq:                                23
% 11.63/2.01  fd_pure:                                0
% 11.63/2.01  fd_pseudo:                              0
% 11.63/2.01  fd_cond:                                4
% 11.63/2.01  fd_pseudo_cond:                         4
% 11.63/2.01  ac_symbols:                             0
% 11.63/2.01  
% 11.63/2.01  ------ Propositional Solver
% 11.63/2.01  
% 11.63/2.01  prop_solver_calls:                      30
% 11.63/2.01  prop_fast_solver_calls:                 3537
% 11.63/2.01  smt_solver_calls:                       0
% 11.63/2.01  smt_fast_solver_calls:                  0
% 11.63/2.01  prop_num_of_clauses:                    13713
% 11.63/2.01  prop_preprocess_simplified:             24297
% 11.63/2.01  prop_fo_subsumed:                       275
% 11.63/2.01  prop_solver_time:                       0.
% 11.63/2.01  smt_solver_time:                        0.
% 11.63/2.01  smt_fast_solver_time:                   0.
% 11.63/2.01  prop_fast_solver_time:                  0.
% 11.63/2.01  prop_unsat_core_time:                   0.001
% 11.63/2.01  
% 11.63/2.01  ------ QBF
% 11.63/2.01  
% 11.63/2.01  qbf_q_res:                              0
% 11.63/2.01  qbf_num_tautologies:                    0
% 11.63/2.01  qbf_prep_cycles:                        0
% 11.63/2.01  
% 11.63/2.01  ------ BMC1
% 11.63/2.01  
% 11.63/2.01  bmc1_current_bound:                     -1
% 11.63/2.01  bmc1_last_solved_bound:                 -1
% 11.63/2.01  bmc1_unsat_core_size:                   -1
% 11.63/2.01  bmc1_unsat_core_parents_size:           -1
% 11.63/2.01  bmc1_merge_next_fun:                    0
% 11.63/2.01  bmc1_unsat_core_clauses_time:           0.
% 11.63/2.01  
% 11.63/2.01  ------ Instantiation
% 11.63/2.01  
% 11.63/2.01  inst_num_of_clauses:                    3566
% 11.63/2.01  inst_num_in_passive:                    166
% 11.63/2.01  inst_num_in_active:                     1832
% 11.63/2.01  inst_num_in_unprocessed:                1568
% 11.63/2.01  inst_num_of_loops:                      2130
% 11.63/2.01  inst_num_of_learning_restarts:          0
% 11.63/2.01  inst_num_moves_active_passive:          296
% 11.63/2.01  inst_lit_activity:                      0
% 11.63/2.01  inst_lit_activity_moves:                0
% 11.63/2.01  inst_num_tautologies:                   0
% 11.63/2.01  inst_num_prop_implied:                  0
% 11.63/2.01  inst_num_existing_simplified:           0
% 11.63/2.01  inst_num_eq_res_simplified:             0
% 11.63/2.01  inst_num_child_elim:                    0
% 11.63/2.01  inst_num_of_dismatching_blockings:      968
% 11.63/2.01  inst_num_of_non_proper_insts:           3978
% 11.63/2.01  inst_num_of_duplicates:                 0
% 11.63/2.01  inst_inst_num_from_inst_to_res:         0
% 11.63/2.01  inst_dismatching_checking_time:         0.
% 11.63/2.01  
% 11.63/2.01  ------ Resolution
% 11.63/2.01  
% 11.63/2.01  res_num_of_clauses:                     0
% 11.63/2.01  res_num_in_passive:                     0
% 11.63/2.01  res_num_in_active:                      0
% 11.63/2.01  res_num_of_loops:                       207
% 11.63/2.01  res_forward_subset_subsumed:            229
% 11.63/2.01  res_backward_subset_subsumed:           0
% 11.63/2.01  res_forward_subsumed:                   0
% 11.63/2.01  res_backward_subsumed:                  0
% 11.63/2.01  res_forward_subsumption_resolution:     4
% 11.63/2.01  res_backward_subsumption_resolution:    0
% 11.63/2.01  res_clause_to_clause_subsumption:       4298
% 11.63/2.01  res_orphan_elimination:                 0
% 11.63/2.01  res_tautology_del:                      2394
% 11.63/2.01  res_num_eq_res_simplified:              0
% 11.63/2.01  res_num_sel_changes:                    0
% 11.63/2.01  res_moves_from_active_to_pass:          0
% 11.63/2.01  
% 11.63/2.01  ------ Superposition
% 11.63/2.01  
% 11.63/2.01  sup_time_total:                         0.
% 11.63/2.01  sup_time_generating:                    0.
% 11.63/2.01  sup_time_sim_full:                      0.
% 11.63/2.01  sup_time_sim_immed:                     0.
% 11.63/2.01  
% 11.63/2.01  sup_num_of_clauses:                     1564
% 11.63/2.01  sup_num_in_active:                      407
% 11.63/2.01  sup_num_in_passive:                     1157
% 11.63/2.01  sup_num_of_loops:                       425
% 11.63/2.01  sup_fw_superposition:                   958
% 11.63/2.01  sup_bw_superposition:                   1120
% 11.63/2.01  sup_immediate_simplified:               472
% 11.63/2.01  sup_given_eliminated:                   2
% 11.63/2.01  comparisons_done:                       0
% 11.63/2.01  comparisons_avoided:                    184
% 11.63/2.01  
% 11.63/2.01  ------ Simplifications
% 11.63/2.01  
% 11.63/2.01  
% 11.63/2.01  sim_fw_subset_subsumed:                 254
% 11.63/2.01  sim_bw_subset_subsumed:                 26
% 11.63/2.01  sim_fw_subsumed:                        81
% 11.63/2.01  sim_bw_subsumed:                        51
% 11.63/2.01  sim_fw_subsumption_res:                 4
% 11.63/2.01  sim_bw_subsumption_res:                 0
% 11.63/2.01  sim_tautology_del:                      10
% 11.63/2.01  sim_eq_tautology_del:                   39
% 11.63/2.01  sim_eq_res_simp:                        0
% 11.63/2.01  sim_fw_demodulated:                     4
% 11.63/2.01  sim_bw_demodulated:                     17
% 11.63/2.01  sim_light_normalised:                   102
% 11.63/2.01  sim_joinable_taut:                      0
% 11.63/2.01  sim_joinable_simp:                      0
% 11.63/2.01  sim_ac_normalised:                      0
% 11.63/2.01  sim_smt_subsumption:                    0
% 11.63/2.01  
%------------------------------------------------------------------------------
