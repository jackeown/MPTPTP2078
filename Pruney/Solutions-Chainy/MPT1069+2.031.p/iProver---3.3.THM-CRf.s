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
% DateTime   : Thu Dec  3 12:09:48 EST 2020

% Result     : Theorem 9.26s
% Output     : CNFRefutation 9.26s
% Verified   : 
% Statistics : Number of formulae       :  196 (2112 expanded)
%              Number of clauses        :  112 ( 591 expanded)
%              Number of leaves         :   26 ( 690 expanded)
%              Depth                    :   23
%              Number of atoms          :  753 (15130 expanded)
%              Number of equality atoms :  309 (4203 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f53,plain,(
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
    inference(rectify,[],[f52])).

fof(f56,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK7(X0,X5)) = X5
        & r2_hidden(sK7(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X1)) = X2
        & r2_hidden(sK6(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
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
              ( k1_funct_1(X0,X3) != sK5(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK5(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK5(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK5(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK6(X0,X1)) = sK5(X0,X1)
                  & r2_hidden(sK6(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK5(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK7(X0,X5)) = X5
                    & r2_hidden(sK7(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f53,f56,f55,f54])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(sK6(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK5(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f44])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
          & k1_xboole_0 != X1
          & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
          & m1_subset_1(X5,X1) )
     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK13) != k7_partfun1(X0,X4,k1_funct_1(X3,sK13))
        & k1_xboole_0 != X1
        & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
        & m1_subset_1(sK13,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
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
            ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK12),X5) != k7_partfun1(X0,sK12,k1_funct_1(X3,X5))
            & k1_xboole_0 != X1
            & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK12))
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        & v1_funct_1(sK12) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
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
                ( k1_funct_1(k8_funct_2(X1,X2,X0,sK11,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(sK11,X5))
                & k1_xboole_0 != X1
                & r1_tarski(k2_relset_1(X1,X2,sK11),k1_relset_1(X2,X0,X4))
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK11,X1,X2)
        & v1_funct_1(sK11) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
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
                  ( k1_funct_1(k8_funct_2(sK9,sK10,sK8,X3,X4),X5) != k7_partfun1(sK8,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != sK9
                  & r1_tarski(k2_relset_1(sK9,sK10,X3),k1_relset_1(sK10,sK8,X4))
                  & m1_subset_1(X5,sK9) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK10,sK8)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
          & v1_funct_2(X3,sK9,sK10)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK10) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( k1_funct_1(k8_funct_2(sK9,sK10,sK8,sK11,sK12),sK13) != k7_partfun1(sK8,sK12,k1_funct_1(sK11,sK13))
    & k1_xboole_0 != sK9
    & r1_tarski(k2_relset_1(sK9,sK10,sK11),k1_relset_1(sK10,sK8,sK12))
    & m1_subset_1(sK13,sK9)
    & m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK8)))
    & v1_funct_1(sK12)
    & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
    & v1_funct_2(sK11,sK9,sK10)
    & v1_funct_1(sK11)
    & ~ v1_xboole_0(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11,sK12,sK13])],[f37,f62,f61,f60,f59])).

fof(f101,plain,(
    m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) ),
    inference(cnf_transformation,[],[f63])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

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

fof(f58,plain,(
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

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f100,plain,(
    v1_funct_2(sK11,sK9,sK10) ),
    inference(cnf_transformation,[],[f63])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f81,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f113,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f114,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f113])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f105,plain,(
    r1_tarski(k2_relset_1(sK9,sK10,sK11),k1_relset_1(sK10,sK8,sK12)) ),
    inference(cnf_transformation,[],[f63])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f103,plain,(
    m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK8))) ),
    inference(cnf_transformation,[],[f63])).

fof(f99,plain,(
    v1_funct_1(sK11) ),
    inference(cnf_transformation,[],[f63])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f102,plain,(
    v1_funct_1(sK12) ),
    inference(cnf_transformation,[],[f63])).

fof(f98,plain,(
    ~ v1_xboole_0(sK10) ),
    inference(cnf_transformation,[],[f63])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).

fof(f65,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f104,plain,(
    m1_subset_1(sK13,sK9) ),
    inference(cnf_transformation,[],[f63])).

fof(f106,plain,(
    k1_xboole_0 != sK9 ),
    inference(cnf_transformation,[],[f63])).

fof(f107,plain,(
    k1_funct_1(k8_funct_2(sK9,sK10,sK8,sK11,sK12),sK13) != k7_partfun1(sK8,sK12,k1_funct_1(sK11,sK13)) ),
    inference(cnf_transformation,[],[f63])).

fof(f14,axiom,(
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

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f97,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f79,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK7(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f116,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK7(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f79])).

fof(f64,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_17,plain,
    ( r2_hidden(sK6(X0,X1),k1_relat_1(X0))
    | r2_hidden(sK5(X0,X1),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_3246,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(sK6(X0,X1),k1_relat_1(X0)) = iProver_top
    | r2_hidden(sK5(X0,X1),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3260,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_3227,plain,
    ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3233,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_4843,plain,
    ( k1_relset_1(sK9,sK10,sK11) = sK9
    | sK10 = k1_xboole_0
    | v1_funct_2(sK11,sK9,sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_3227,c_3233])).

cnf(c_41,negated_conjecture,
    ( v1_funct_2(sK11,sK9,sK10) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_46,plain,
    ( v1_funct_2(sK11,sK9,sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_5440,plain,
    ( sK10 = k1_xboole_0
    | k1_relset_1(sK9,sK10,sK11) = sK9 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4843,c_46])).

cnf(c_5441,plain,
    ( k1_relset_1(sK9,sK10,sK11) = sK9
    | sK10 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5440])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_3240,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4917,plain,
    ( k1_relset_1(sK9,sK10,sK11) = k1_relat_1(sK11) ),
    inference(superposition,[status(thm)],[c_3227,c_3240])).

cnf(c_5442,plain,
    ( k1_relat_1(sK11) = sK9
    | sK10 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5441,c_4917])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_3245,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_3239,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4539,plain,
    ( k2_relset_1(sK9,sK10,sK11) = k2_relat_1(sK11) ),
    inference(superposition,[status(thm)],[c_3227,c_3239])).

cnf(c_36,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK9,sK10,sK11),k1_relset_1(sK10,sK8,sK12)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_3231,plain,
    ( r1_tarski(k2_relset_1(sK9,sK10,sK11),k1_relset_1(sK10,sK8,sK12)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_4679,plain,
    ( r1_tarski(k2_relat_1(sK11),k1_relset_1(sK10,sK8,sK12)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4539,c_3231])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_3259,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5041,plain,
    ( r2_hidden(X0,k1_relset_1(sK10,sK8,sK12)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK11)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4679,c_3259])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK8))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_3229,plain,
    ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_4916,plain,
    ( k1_relset_1(sK10,sK8,sK12) = k1_relat_1(sK12) ),
    inference(superposition,[status(thm)],[c_3229,c_3240])).

cnf(c_5042,plain,
    ( r2_hidden(X0,k2_relat_1(sK11)) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK12)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5041,c_4916])).

cnf(c_6579,plain,
    ( r2_hidden(X0,k1_relat_1(sK11)) != iProver_top
    | r2_hidden(k1_funct_1(sK11,X0),k1_relat_1(sK12)) = iProver_top
    | v1_relat_1(sK11) != iProver_top
    | v1_funct_1(sK11) != iProver_top ),
    inference(superposition,[status(thm)],[c_3245,c_5042])).

cnf(c_42,negated_conjecture,
    ( v1_funct_1(sK11) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_45,plain,
    ( v1_funct_1(sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_3241,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4504,plain,
    ( v1_relat_1(sK11) = iProver_top ),
    inference(superposition,[status(thm)],[c_3227,c_3241])).

cnf(c_14192,plain,
    ( r2_hidden(X0,k1_relat_1(sK11)) != iProver_top
    | r2_hidden(k1_funct_1(sK11,X0),k1_relat_1(sK12)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6579,c_45,c_4504])).

cnf(c_23,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_32,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_467,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(resolution,[status(thm)],[c_23,c_32])).

cnf(c_471,plain,
    ( ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_467,c_22])).

cnf(c_472,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(renaming,[status(thm)],[c_471])).

cnf(c_3223,plain,
    ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_472])).

cnf(c_3827,plain,
    ( k7_partfun1(sK8,sK12,X0) = k1_funct_1(sK12,X0)
    | r2_hidden(X0,k1_relat_1(sK12)) != iProver_top
    | v1_funct_1(sK12) != iProver_top ),
    inference(superposition,[status(thm)],[c_3229,c_3223])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK12) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_48,plain,
    ( v1_funct_1(sK12) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_3969,plain,
    ( r2_hidden(X0,k1_relat_1(sK12)) != iProver_top
    | k7_partfun1(sK8,sK12,X0) = k1_funct_1(sK12,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3827,c_48])).

cnf(c_3970,plain,
    ( k7_partfun1(sK8,sK12,X0) = k1_funct_1(sK12,X0)
    | r2_hidden(X0,k1_relat_1(sK12)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3969])).

cnf(c_14200,plain,
    ( k7_partfun1(sK8,sK12,k1_funct_1(sK11,X0)) = k1_funct_1(sK12,k1_funct_1(sK11,X0))
    | r2_hidden(X0,k1_relat_1(sK11)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14192,c_3970])).

cnf(c_14304,plain,
    ( k7_partfun1(sK8,sK12,k1_funct_1(sK11,X0)) = k1_funct_1(sK12,k1_funct_1(sK11,X0))
    | sK10 = k1_xboole_0
    | r2_hidden(X0,sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_5442,c_14200])).

cnf(c_43,negated_conjecture,
    ( ~ v1_xboole_0(sK10) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_44,plain,
    ( v1_xboole_0(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_2566,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3339,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK10)
    | sK10 != X0 ),
    inference(instantiation,[status(thm)],[c_2566])).

cnf(c_3343,plain,
    ( sK10 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3339])).

cnf(c_3345,plain,
    ( sK10 != k1_xboole_0
    | v1_xboole_0(sK10) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3343])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3263,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3258,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_21,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_3242,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4151,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3258,c_3242])).

cnf(c_8560,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3263,c_4151])).

cnf(c_22393,plain,
    ( k7_partfun1(sK8,sK12,k1_funct_1(sK11,X0)) = k1_funct_1(sK12,k1_funct_1(sK11,X0))
    | r2_hidden(X0,sK9) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14304,c_44,c_3345,c_8560])).

cnf(c_22400,plain,
    ( k7_partfun1(sK8,sK12,k1_funct_1(sK11,sK1(sK9,X0))) = k1_funct_1(sK12,k1_funct_1(sK11,sK1(sK9,X0)))
    | r1_tarski(sK9,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3260,c_22393])).

cnf(c_22601,plain,
    ( k7_partfun1(sK8,sK12,k1_funct_1(sK11,sK1(sK9,X0))) = k1_funct_1(sK12,k1_funct_1(sK11,sK1(sK9,X0)))
    | r2_hidden(X0,sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_22400,c_3242])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK13,sK9) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_35,negated_conjecture,
    ( k1_xboole_0 != sK9 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_34,negated_conjecture,
    ( k1_funct_1(k8_funct_2(sK9,sK10,sK8,sK11,sK12),sK13) != k7_partfun1(sK8,sK12,k1_funct_1(sK11,sK13)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_2565,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3313,plain,
    ( k7_partfun1(sK8,sK12,k1_funct_1(sK11,sK13)) != X0
    | k1_funct_1(k8_funct_2(sK9,sK10,sK8,sK11,sK12),sK13) != X0
    | k1_funct_1(k8_funct_2(sK9,sK10,sK8,sK11,sK12),sK13) = k7_partfun1(sK8,sK12,k1_funct_1(sK11,sK13)) ),
    inference(instantiation,[status(thm)],[c_2565])).

cnf(c_3368,plain,
    ( k7_partfun1(sK8,sK12,k1_funct_1(sK11,sK13)) != k1_funct_1(sK12,k1_funct_1(sK11,sK13))
    | k1_funct_1(k8_funct_2(sK9,sK10,sK8,sK11,sK12),sK13) = k7_partfun1(sK8,sK12,k1_funct_1(sK11,sK13))
    | k1_funct_1(k8_funct_2(sK9,sK10,sK8,sK11,sK12),sK13) != k1_funct_1(sK12,k1_funct_1(sK11,sK13)) ),
    inference(instantiation,[status(thm)],[c_3313])).

cnf(c_33,plain,
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
    inference(cnf_transformation,[],[f97])).

cnf(c_3347,plain,
    ( ~ v1_funct_2(X0,X1,sK10)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK10)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK10,X4)))
    | ~ r1_tarski(k2_relset_1(X1,sK10,X0),k1_relset_1(sK10,X4,X3))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_xboole_0(sK10)
    | k1_funct_1(k8_funct_2(X1,sK10,X4,X0,X3),X2) = k1_funct_1(X3,k1_funct_1(X0,X2))
    | k1_xboole_0 = X1 ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_3396,plain,
    ( ~ v1_funct_2(X0,sK9,sK10)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK10,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
    | ~ m1_subset_1(X3,sK9)
    | ~ r1_tarski(k2_relset_1(sK9,sK10,X0),k1_relset_1(sK10,X2,X1))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v1_xboole_0(sK10)
    | k1_funct_1(k8_funct_2(sK9,sK10,X2,X0,X1),X3) = k1_funct_1(X1,k1_funct_1(X0,X3))
    | k1_xboole_0 = sK9 ),
    inference(instantiation,[status(thm)],[c_3347])).

cnf(c_3445,plain,
    ( ~ v1_funct_2(sK11,sK9,sK10)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK10,X1)))
    | ~ m1_subset_1(X2,sK9)
    | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
    | ~ r1_tarski(k2_relset_1(sK9,sK10,sK11),k1_relset_1(sK10,X1,X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK11)
    | v1_xboole_0(sK10)
    | k1_funct_1(k8_funct_2(sK9,sK10,X1,sK11,X0),X2) = k1_funct_1(X0,k1_funct_1(sK11,X2))
    | k1_xboole_0 = sK9 ),
    inference(instantiation,[status(thm)],[c_3396])).

cnf(c_3478,plain,
    ( ~ v1_funct_2(sK11,sK9,sK10)
    | ~ m1_subset_1(X0,sK9)
    | ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,X1)))
    | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
    | ~ r1_tarski(k2_relset_1(sK9,sK10,sK11),k1_relset_1(sK10,X1,sK12))
    | ~ v1_funct_1(sK12)
    | ~ v1_funct_1(sK11)
    | v1_xboole_0(sK10)
    | k1_funct_1(k8_funct_2(sK9,sK10,X1,sK11,sK12),X0) = k1_funct_1(sK12,k1_funct_1(sK11,X0))
    | k1_xboole_0 = sK9 ),
    inference(instantiation,[status(thm)],[c_3445])).

cnf(c_3821,plain,
    ( ~ v1_funct_2(sK11,sK9,sK10)
    | ~ m1_subset_1(sK13,sK9)
    | ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,X0)))
    | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
    | ~ r1_tarski(k2_relset_1(sK9,sK10,sK11),k1_relset_1(sK10,X0,sK12))
    | ~ v1_funct_1(sK12)
    | ~ v1_funct_1(sK11)
    | v1_xboole_0(sK10)
    | k1_funct_1(k8_funct_2(sK9,sK10,X0,sK11,sK12),sK13) = k1_funct_1(sK12,k1_funct_1(sK11,sK13))
    | k1_xboole_0 = sK9 ),
    inference(instantiation,[status(thm)],[c_3478])).

cnf(c_4238,plain,
    ( ~ v1_funct_2(sK11,sK9,sK10)
    | ~ m1_subset_1(sK13,sK9)
    | ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK8)))
    | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
    | ~ r1_tarski(k2_relset_1(sK9,sK10,sK11),k1_relset_1(sK10,sK8,sK12))
    | ~ v1_funct_1(sK12)
    | ~ v1_funct_1(sK11)
    | v1_xboole_0(sK10)
    | k1_funct_1(k8_funct_2(sK9,sK10,sK8,sK11,sK12),sK13) = k1_funct_1(sK12,k1_funct_1(sK11,sK13))
    | k1_xboole_0 = sK9 ),
    inference(instantiation,[status(thm)],[c_3821])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK7(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_3243,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK7(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_6312,plain,
    ( sK10 = k1_xboole_0
    | r2_hidden(X0,k2_relat_1(sK11)) != iProver_top
    | r2_hidden(sK7(sK11,X0),sK9) = iProver_top
    | v1_relat_1(sK11) != iProver_top
    | v1_funct_1(sK11) != iProver_top ),
    inference(superposition,[status(thm)],[c_5442,c_3243])).

cnf(c_19706,plain,
    ( r2_hidden(X0,k2_relat_1(sK11)) != iProver_top
    | r2_hidden(sK7(sK11,X0),sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6312,c_44,c_45,c_3345,c_4504,c_8560])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3262,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_19712,plain,
    ( r2_hidden(X0,k2_relat_1(sK11)) != iProver_top
    | v1_xboole_0(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_19706,c_3262])).

cnf(c_20064,plain,
    ( v1_xboole_0(k2_relat_1(sK11)) = iProver_top
    | v1_xboole_0(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_3263,c_19712])).

cnf(c_3230,plain,
    ( m1_subset_1(sK13,sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3257,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4919,plain,
    ( r2_hidden(sK13,sK9) = iProver_top
    | v1_xboole_0(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_3230,c_3257])).

cnf(c_22408,plain,
    ( k7_partfun1(sK8,sK12,k1_funct_1(sK11,sK13)) = k1_funct_1(sK12,k1_funct_1(sK11,sK13))
    | v1_xboole_0(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_4919,c_22393])).

cnf(c_6577,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(k2_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3245,c_3262])).

cnf(c_22493,plain,
    ( sK10 = k1_xboole_0
    | r2_hidden(X0,sK9) != iProver_top
    | v1_relat_1(sK11) != iProver_top
    | v1_funct_1(sK11) != iProver_top
    | v1_xboole_0(k2_relat_1(sK11)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5442,c_6577])).

cnf(c_22690,plain,
    ( r2_hidden(X0,sK9) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22601,c_43,c_44,c_42,c_45,c_41,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_3345,c_3368,c_4238,c_4504,c_8560,c_20064,c_22408,c_22493])).

cnf(c_22704,plain,
    ( k2_relat_1(X0) = sK9
    | r2_hidden(sK6(X0,sK9),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3246,c_22690])).

cnf(c_20073,plain,
    ( r2_hidden(X0,k1_relat_1(sK11)) != iProver_top
    | v1_relat_1(sK11) != iProver_top
    | v1_funct_1(sK11) != iProver_top
    | v1_xboole_0(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_3245,c_19712])).

cnf(c_23958,plain,
    ( r2_hidden(X0,k1_relat_1(sK11)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20073,c_43,c_42,c_45,c_41,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_3368,c_4238,c_4504,c_22408])).

cnf(c_26369,plain,
    ( k2_relat_1(sK11) = sK9
    | v1_relat_1(sK11) != iProver_top
    | v1_funct_1(sK11) != iProver_top ),
    inference(superposition,[status(thm)],[c_22704,c_23958])).

cnf(c_8568,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | r2_hidden(sK6(X0,k1_xboole_0),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3246,c_4151])).

cnf(c_20201,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(k1_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8568,c_3262])).

cnf(c_21379,plain,
    ( k2_relat_1(sK11) = k1_xboole_0
    | sK10 = k1_xboole_0
    | v1_relat_1(sK11) != iProver_top
    | v1_funct_1(sK11) != iProver_top
    | v1_xboole_0(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_5442,c_20201])).

cnf(c_23521,plain,
    ( k2_relat_1(sK11) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_21379,c_43,c_44,c_42,c_45,c_41,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_3345,c_3368,c_4238,c_4504,c_8560,c_22408])).

cnf(c_26377,plain,
    ( sK9 = k1_xboole_0
    | v1_relat_1(sK11) != iProver_top
    | v1_funct_1(sK11) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_26369,c_23521])).

cnf(c_3331,plain,
    ( sK9 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK9 ),
    inference(instantiation,[status(thm)],[c_2565])).

cnf(c_3332,plain,
    ( sK9 != k1_xboole_0
    | k1_xboole_0 = sK9
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3331])).

cnf(c_2564,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2593,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2564])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_26377,c_4504,c_3332,c_2593,c_35,c_45])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:28:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 9.26/2.04  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.26/2.04  
% 9.26/2.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 9.26/2.04  
% 9.26/2.04  ------  iProver source info
% 9.26/2.04  
% 9.26/2.04  git: date: 2020-06-30 10:37:57 +0100
% 9.26/2.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 9.26/2.04  git: non_committed_changes: false
% 9.26/2.04  git: last_make_outside_of_git: false
% 9.26/2.04  
% 9.26/2.04  ------ 
% 9.26/2.04  
% 9.26/2.04  ------ Input Options
% 9.26/2.04  
% 9.26/2.04  --out_options                           all
% 9.26/2.04  --tptp_safe_out                         true
% 9.26/2.04  --problem_path                          ""
% 9.26/2.04  --include_path                          ""
% 9.26/2.04  --clausifier                            res/vclausify_rel
% 9.26/2.04  --clausifier_options                    ""
% 9.26/2.04  --stdin                                 false
% 9.26/2.04  --stats_out                             all
% 9.26/2.04  
% 9.26/2.04  ------ General Options
% 9.26/2.04  
% 9.26/2.04  --fof                                   false
% 9.26/2.04  --time_out_real                         305.
% 9.26/2.04  --time_out_virtual                      -1.
% 9.26/2.04  --symbol_type_check                     false
% 9.26/2.04  --clausify_out                          false
% 9.26/2.04  --sig_cnt_out                           false
% 9.26/2.04  --trig_cnt_out                          false
% 9.26/2.04  --trig_cnt_out_tolerance                1.
% 9.26/2.04  --trig_cnt_out_sk_spl                   false
% 9.26/2.04  --abstr_cl_out                          false
% 9.26/2.04  
% 9.26/2.04  ------ Global Options
% 9.26/2.04  
% 9.26/2.04  --schedule                              default
% 9.26/2.04  --add_important_lit                     false
% 9.26/2.04  --prop_solver_per_cl                    1000
% 9.26/2.04  --min_unsat_core                        false
% 9.26/2.04  --soft_assumptions                      false
% 9.26/2.04  --soft_lemma_size                       3
% 9.26/2.04  --prop_impl_unit_size                   0
% 9.26/2.04  --prop_impl_unit                        []
% 9.26/2.04  --share_sel_clauses                     true
% 9.26/2.04  --reset_solvers                         false
% 9.26/2.04  --bc_imp_inh                            [conj_cone]
% 9.26/2.04  --conj_cone_tolerance                   3.
% 9.26/2.04  --extra_neg_conj                        none
% 9.26/2.04  --large_theory_mode                     true
% 9.26/2.04  --prolific_symb_bound                   200
% 9.26/2.04  --lt_threshold                          2000
% 9.26/2.04  --clause_weak_htbl                      true
% 9.26/2.04  --gc_record_bc_elim                     false
% 9.26/2.04  
% 9.26/2.04  ------ Preprocessing Options
% 9.26/2.04  
% 9.26/2.04  --preprocessing_flag                    true
% 9.26/2.04  --time_out_prep_mult                    0.1
% 9.26/2.04  --splitting_mode                        input
% 9.26/2.04  --splitting_grd                         true
% 9.26/2.04  --splitting_cvd                         false
% 9.26/2.04  --splitting_cvd_svl                     false
% 9.26/2.04  --splitting_nvd                         32
% 9.26/2.04  --sub_typing                            true
% 9.26/2.04  --prep_gs_sim                           true
% 9.26/2.04  --prep_unflatten                        true
% 9.26/2.04  --prep_res_sim                          true
% 9.26/2.04  --prep_upred                            true
% 9.26/2.04  --prep_sem_filter                       exhaustive
% 9.26/2.04  --prep_sem_filter_out                   false
% 9.26/2.04  --pred_elim                             true
% 9.26/2.04  --res_sim_input                         true
% 9.26/2.04  --eq_ax_congr_red                       true
% 9.26/2.04  --pure_diseq_elim                       true
% 9.26/2.04  --brand_transform                       false
% 9.26/2.04  --non_eq_to_eq                          false
% 9.26/2.04  --prep_def_merge                        true
% 9.26/2.04  --prep_def_merge_prop_impl              false
% 9.26/2.04  --prep_def_merge_mbd                    true
% 9.26/2.04  --prep_def_merge_tr_red                 false
% 9.26/2.04  --prep_def_merge_tr_cl                  false
% 9.26/2.04  --smt_preprocessing                     true
% 9.26/2.04  --smt_ac_axioms                         fast
% 9.26/2.04  --preprocessed_out                      false
% 9.26/2.04  --preprocessed_stats                    false
% 9.26/2.04  
% 9.26/2.04  ------ Abstraction refinement Options
% 9.26/2.04  
% 9.26/2.04  --abstr_ref                             []
% 9.26/2.04  --abstr_ref_prep                        false
% 9.26/2.04  --abstr_ref_until_sat                   false
% 9.26/2.04  --abstr_ref_sig_restrict                funpre
% 9.26/2.04  --abstr_ref_af_restrict_to_split_sk     false
% 9.26/2.04  --abstr_ref_under                       []
% 9.26/2.04  
% 9.26/2.04  ------ SAT Options
% 9.26/2.04  
% 9.26/2.04  --sat_mode                              false
% 9.26/2.04  --sat_fm_restart_options                ""
% 9.26/2.04  --sat_gr_def                            false
% 9.26/2.04  --sat_epr_types                         true
% 9.26/2.04  --sat_non_cyclic_types                  false
% 9.26/2.04  --sat_finite_models                     false
% 9.26/2.04  --sat_fm_lemmas                         false
% 9.26/2.04  --sat_fm_prep                           false
% 9.26/2.04  --sat_fm_uc_incr                        true
% 9.26/2.04  --sat_out_model                         small
% 9.26/2.04  --sat_out_clauses                       false
% 9.26/2.04  
% 9.26/2.04  ------ QBF Options
% 9.26/2.04  
% 9.26/2.04  --qbf_mode                              false
% 9.26/2.04  --qbf_elim_univ                         false
% 9.26/2.04  --qbf_dom_inst                          none
% 9.26/2.04  --qbf_dom_pre_inst                      false
% 9.26/2.04  --qbf_sk_in                             false
% 9.26/2.04  --qbf_pred_elim                         true
% 9.26/2.04  --qbf_split                             512
% 9.26/2.04  
% 9.26/2.04  ------ BMC1 Options
% 9.26/2.04  
% 9.26/2.04  --bmc1_incremental                      false
% 9.26/2.04  --bmc1_axioms                           reachable_all
% 9.26/2.04  --bmc1_min_bound                        0
% 9.26/2.04  --bmc1_max_bound                        -1
% 9.26/2.04  --bmc1_max_bound_default                -1
% 9.26/2.04  --bmc1_symbol_reachability              true
% 9.26/2.04  --bmc1_property_lemmas                  false
% 9.26/2.04  --bmc1_k_induction                      false
% 9.26/2.04  --bmc1_non_equiv_states                 false
% 9.26/2.04  --bmc1_deadlock                         false
% 9.26/2.04  --bmc1_ucm                              false
% 9.26/2.04  --bmc1_add_unsat_core                   none
% 9.26/2.04  --bmc1_unsat_core_children              false
% 9.26/2.04  --bmc1_unsat_core_extrapolate_axioms    false
% 9.26/2.04  --bmc1_out_stat                         full
% 9.26/2.04  --bmc1_ground_init                      false
% 9.26/2.04  --bmc1_pre_inst_next_state              false
% 9.26/2.04  --bmc1_pre_inst_state                   false
% 9.26/2.04  --bmc1_pre_inst_reach_state             false
% 9.26/2.04  --bmc1_out_unsat_core                   false
% 9.26/2.04  --bmc1_aig_witness_out                  false
% 9.26/2.04  --bmc1_verbose                          false
% 9.26/2.04  --bmc1_dump_clauses_tptp                false
% 9.26/2.04  --bmc1_dump_unsat_core_tptp             false
% 9.26/2.04  --bmc1_dump_file                        -
% 9.26/2.04  --bmc1_ucm_expand_uc_limit              128
% 9.26/2.04  --bmc1_ucm_n_expand_iterations          6
% 9.26/2.04  --bmc1_ucm_extend_mode                  1
% 9.26/2.04  --bmc1_ucm_init_mode                    2
% 9.26/2.04  --bmc1_ucm_cone_mode                    none
% 9.26/2.04  --bmc1_ucm_reduced_relation_type        0
% 9.26/2.04  --bmc1_ucm_relax_model                  4
% 9.26/2.04  --bmc1_ucm_full_tr_after_sat            true
% 9.26/2.04  --bmc1_ucm_expand_neg_assumptions       false
% 9.26/2.04  --bmc1_ucm_layered_model                none
% 9.26/2.04  --bmc1_ucm_max_lemma_size               10
% 9.26/2.04  
% 9.26/2.04  ------ AIG Options
% 9.26/2.04  
% 9.26/2.04  --aig_mode                              false
% 9.26/2.04  
% 9.26/2.04  ------ Instantiation Options
% 9.26/2.04  
% 9.26/2.04  --instantiation_flag                    true
% 9.26/2.04  --inst_sos_flag                         true
% 9.26/2.04  --inst_sos_phase                        true
% 9.26/2.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 9.26/2.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 9.26/2.04  --inst_lit_sel_side                     num_symb
% 9.26/2.04  --inst_solver_per_active                1400
% 9.26/2.04  --inst_solver_calls_frac                1.
% 9.26/2.04  --inst_passive_queue_type               priority_queues
% 9.26/2.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 9.26/2.04  --inst_passive_queues_freq              [25;2]
% 9.26/2.04  --inst_dismatching                      true
% 9.26/2.04  --inst_eager_unprocessed_to_passive     true
% 9.26/2.04  --inst_prop_sim_given                   true
% 9.26/2.04  --inst_prop_sim_new                     false
% 9.26/2.04  --inst_subs_new                         false
% 9.26/2.04  --inst_eq_res_simp                      false
% 9.26/2.04  --inst_subs_given                       false
% 9.26/2.04  --inst_orphan_elimination               true
% 9.26/2.04  --inst_learning_loop_flag               true
% 9.26/2.04  --inst_learning_start                   3000
% 9.26/2.04  --inst_learning_factor                  2
% 9.26/2.04  --inst_start_prop_sim_after_learn       3
% 9.26/2.04  --inst_sel_renew                        solver
% 9.26/2.04  --inst_lit_activity_flag                true
% 9.26/2.04  --inst_restr_to_given                   false
% 9.26/2.04  --inst_activity_threshold               500
% 9.26/2.04  --inst_out_proof                        true
% 9.26/2.04  
% 9.26/2.04  ------ Resolution Options
% 9.26/2.04  
% 9.26/2.04  --resolution_flag                       true
% 9.26/2.04  --res_lit_sel                           adaptive
% 9.26/2.04  --res_lit_sel_side                      none
% 9.26/2.04  --res_ordering                          kbo
% 9.26/2.04  --res_to_prop_solver                    active
% 9.26/2.04  --res_prop_simpl_new                    false
% 9.26/2.04  --res_prop_simpl_given                  true
% 9.26/2.04  --res_passive_queue_type                priority_queues
% 9.26/2.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 9.26/2.04  --res_passive_queues_freq               [15;5]
% 9.26/2.04  --res_forward_subs                      full
% 9.26/2.04  --res_backward_subs                     full
% 9.26/2.04  --res_forward_subs_resolution           true
% 9.26/2.04  --res_backward_subs_resolution          true
% 9.26/2.04  --res_orphan_elimination                true
% 9.26/2.04  --res_time_limit                        2.
% 9.26/2.04  --res_out_proof                         true
% 9.26/2.04  
% 9.26/2.04  ------ Superposition Options
% 9.26/2.04  
% 9.26/2.04  --superposition_flag                    true
% 9.26/2.04  --sup_passive_queue_type                priority_queues
% 9.26/2.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 9.26/2.04  --sup_passive_queues_freq               [8;1;4]
% 9.26/2.04  --demod_completeness_check              fast
% 9.26/2.04  --demod_use_ground                      true
% 9.26/2.04  --sup_to_prop_solver                    passive
% 9.26/2.04  --sup_prop_simpl_new                    true
% 9.26/2.04  --sup_prop_simpl_given                  true
% 9.26/2.04  --sup_fun_splitting                     true
% 9.26/2.04  --sup_smt_interval                      50000
% 9.26/2.04  
% 9.26/2.04  ------ Superposition Simplification Setup
% 9.26/2.04  
% 9.26/2.04  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 9.26/2.04  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 9.26/2.04  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 9.26/2.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 9.26/2.04  --sup_full_triv                         [TrivRules;PropSubs]
% 9.26/2.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 9.26/2.04  --sup_full_bw                           [BwDemod;BwSubsumption]
% 9.26/2.04  --sup_immed_triv                        [TrivRules]
% 9.26/2.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 9.26/2.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 9.26/2.04  --sup_immed_bw_main                     []
% 9.26/2.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 9.26/2.04  --sup_input_triv                        [Unflattening;TrivRules]
% 9.26/2.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 9.26/2.04  --sup_input_bw                          []
% 9.26/2.04  
% 9.26/2.04  ------ Combination Options
% 9.26/2.04  
% 9.26/2.04  --comb_res_mult                         3
% 9.26/2.04  --comb_sup_mult                         2
% 9.26/2.04  --comb_inst_mult                        10
% 9.26/2.04  
% 9.26/2.04  ------ Debug Options
% 9.26/2.04  
% 9.26/2.04  --dbg_backtrace                         false
% 9.26/2.04  --dbg_dump_prop_clauses                 false
% 9.26/2.04  --dbg_dump_prop_clauses_file            -
% 9.26/2.04  --dbg_out_stat                          false
% 9.26/2.04  ------ Parsing...
% 9.26/2.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 9.26/2.04  
% 9.26/2.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 9.26/2.04  
% 9.26/2.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 9.26/2.04  
% 9.26/2.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 9.26/2.04  ------ Proving...
% 9.26/2.04  ------ Problem Properties 
% 9.26/2.04  
% 9.26/2.04  
% 9.26/2.04  clauses                                 43
% 9.26/2.04  conjectures                             10
% 9.26/2.04  EPR                                     11
% 9.26/2.04  Horn                                    30
% 9.26/2.04  unary                                   11
% 9.26/2.04  binary                                  8
% 9.26/2.04  lits                                    135
% 9.26/2.04  lits eq                                 29
% 9.26/2.04  fd_pure                                 0
% 9.26/2.04  fd_pseudo                               0
% 9.26/2.04  fd_cond                                 4
% 9.26/2.04  fd_pseudo_cond                          7
% 9.26/2.04  AC symbols                              0
% 9.26/2.04  
% 9.26/2.04  ------ Schedule dynamic 5 is on 
% 9.26/2.04  
% 9.26/2.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 9.26/2.04  
% 9.26/2.04  
% 9.26/2.04  ------ 
% 9.26/2.04  Current options:
% 9.26/2.04  ------ 
% 9.26/2.04  
% 9.26/2.04  ------ Input Options
% 9.26/2.04  
% 9.26/2.04  --out_options                           all
% 9.26/2.04  --tptp_safe_out                         true
% 9.26/2.04  --problem_path                          ""
% 9.26/2.04  --include_path                          ""
% 9.26/2.04  --clausifier                            res/vclausify_rel
% 9.26/2.04  --clausifier_options                    ""
% 9.26/2.04  --stdin                                 false
% 9.26/2.04  --stats_out                             all
% 9.26/2.04  
% 9.26/2.04  ------ General Options
% 9.26/2.04  
% 9.26/2.04  --fof                                   false
% 9.26/2.04  --time_out_real                         305.
% 9.26/2.04  --time_out_virtual                      -1.
% 9.26/2.04  --symbol_type_check                     false
% 9.26/2.04  --clausify_out                          false
% 9.26/2.04  --sig_cnt_out                           false
% 9.26/2.04  --trig_cnt_out                          false
% 9.26/2.04  --trig_cnt_out_tolerance                1.
% 9.26/2.04  --trig_cnt_out_sk_spl                   false
% 9.26/2.04  --abstr_cl_out                          false
% 9.26/2.04  
% 9.26/2.04  ------ Global Options
% 9.26/2.04  
% 9.26/2.04  --schedule                              default
% 9.26/2.04  --add_important_lit                     false
% 9.26/2.04  --prop_solver_per_cl                    1000
% 9.26/2.04  --min_unsat_core                        false
% 9.26/2.04  --soft_assumptions                      false
% 9.26/2.04  --soft_lemma_size                       3
% 9.26/2.04  --prop_impl_unit_size                   0
% 9.26/2.04  --prop_impl_unit                        []
% 9.26/2.04  --share_sel_clauses                     true
% 9.26/2.04  --reset_solvers                         false
% 9.26/2.04  --bc_imp_inh                            [conj_cone]
% 9.26/2.04  --conj_cone_tolerance                   3.
% 9.26/2.04  --extra_neg_conj                        none
% 9.26/2.04  --large_theory_mode                     true
% 9.26/2.04  --prolific_symb_bound                   200
% 9.26/2.04  --lt_threshold                          2000
% 9.26/2.04  --clause_weak_htbl                      true
% 9.26/2.04  --gc_record_bc_elim                     false
% 9.26/2.04  
% 9.26/2.04  ------ Preprocessing Options
% 9.26/2.04  
% 9.26/2.04  --preprocessing_flag                    true
% 9.26/2.04  --time_out_prep_mult                    0.1
% 9.26/2.04  --splitting_mode                        input
% 9.26/2.04  --splitting_grd                         true
% 9.26/2.04  --splitting_cvd                         false
% 9.26/2.04  --splitting_cvd_svl                     false
% 9.26/2.04  --splitting_nvd                         32
% 9.26/2.04  --sub_typing                            true
% 9.26/2.04  --prep_gs_sim                           true
% 9.26/2.04  --prep_unflatten                        true
% 9.26/2.04  --prep_res_sim                          true
% 9.26/2.04  --prep_upred                            true
% 9.26/2.04  --prep_sem_filter                       exhaustive
% 9.26/2.04  --prep_sem_filter_out                   false
% 9.26/2.04  --pred_elim                             true
% 9.26/2.04  --res_sim_input                         true
% 9.26/2.04  --eq_ax_congr_red                       true
% 9.26/2.04  --pure_diseq_elim                       true
% 9.26/2.04  --brand_transform                       false
% 9.26/2.04  --non_eq_to_eq                          false
% 9.26/2.04  --prep_def_merge                        true
% 9.26/2.04  --prep_def_merge_prop_impl              false
% 9.26/2.04  --prep_def_merge_mbd                    true
% 9.26/2.04  --prep_def_merge_tr_red                 false
% 9.26/2.04  --prep_def_merge_tr_cl                  false
% 9.26/2.04  --smt_preprocessing                     true
% 9.26/2.04  --smt_ac_axioms                         fast
% 9.26/2.04  --preprocessed_out                      false
% 9.26/2.04  --preprocessed_stats                    false
% 9.26/2.04  
% 9.26/2.04  ------ Abstraction refinement Options
% 9.26/2.04  
% 9.26/2.04  --abstr_ref                             []
% 9.26/2.04  --abstr_ref_prep                        false
% 9.26/2.04  --abstr_ref_until_sat                   false
% 9.26/2.04  --abstr_ref_sig_restrict                funpre
% 9.26/2.04  --abstr_ref_af_restrict_to_split_sk     false
% 9.26/2.04  --abstr_ref_under                       []
% 9.26/2.04  
% 9.26/2.04  ------ SAT Options
% 9.26/2.04  
% 9.26/2.04  --sat_mode                              false
% 9.26/2.04  --sat_fm_restart_options                ""
% 9.26/2.04  --sat_gr_def                            false
% 9.26/2.04  --sat_epr_types                         true
% 9.26/2.04  --sat_non_cyclic_types                  false
% 9.26/2.04  --sat_finite_models                     false
% 9.26/2.04  --sat_fm_lemmas                         false
% 9.26/2.04  --sat_fm_prep                           false
% 9.26/2.04  --sat_fm_uc_incr                        true
% 9.26/2.04  --sat_out_model                         small
% 9.26/2.04  --sat_out_clauses                       false
% 9.26/2.04  
% 9.26/2.04  ------ QBF Options
% 9.26/2.04  
% 9.26/2.04  --qbf_mode                              false
% 9.26/2.04  --qbf_elim_univ                         false
% 9.26/2.04  --qbf_dom_inst                          none
% 9.26/2.04  --qbf_dom_pre_inst                      false
% 9.26/2.04  --qbf_sk_in                             false
% 9.26/2.04  --qbf_pred_elim                         true
% 9.26/2.04  --qbf_split                             512
% 9.26/2.04  
% 9.26/2.04  ------ BMC1 Options
% 9.26/2.04  
% 9.26/2.04  --bmc1_incremental                      false
% 9.26/2.04  --bmc1_axioms                           reachable_all
% 9.26/2.04  --bmc1_min_bound                        0
% 9.26/2.04  --bmc1_max_bound                        -1
% 9.26/2.04  --bmc1_max_bound_default                -1
% 9.26/2.04  --bmc1_symbol_reachability              true
% 9.26/2.04  --bmc1_property_lemmas                  false
% 9.26/2.04  --bmc1_k_induction                      false
% 9.26/2.04  --bmc1_non_equiv_states                 false
% 9.26/2.04  --bmc1_deadlock                         false
% 9.26/2.04  --bmc1_ucm                              false
% 9.26/2.04  --bmc1_add_unsat_core                   none
% 9.26/2.04  --bmc1_unsat_core_children              false
% 9.26/2.04  --bmc1_unsat_core_extrapolate_axioms    false
% 9.26/2.04  --bmc1_out_stat                         full
% 9.26/2.04  --bmc1_ground_init                      false
% 9.26/2.04  --bmc1_pre_inst_next_state              false
% 9.26/2.04  --bmc1_pre_inst_state                   false
% 9.26/2.04  --bmc1_pre_inst_reach_state             false
% 9.26/2.04  --bmc1_out_unsat_core                   false
% 9.26/2.04  --bmc1_aig_witness_out                  false
% 9.26/2.04  --bmc1_verbose                          false
% 9.26/2.04  --bmc1_dump_clauses_tptp                false
% 9.26/2.04  --bmc1_dump_unsat_core_tptp             false
% 9.26/2.04  --bmc1_dump_file                        -
% 9.26/2.04  --bmc1_ucm_expand_uc_limit              128
% 9.26/2.04  --bmc1_ucm_n_expand_iterations          6
% 9.26/2.04  --bmc1_ucm_extend_mode                  1
% 9.26/2.04  --bmc1_ucm_init_mode                    2
% 9.26/2.04  --bmc1_ucm_cone_mode                    none
% 9.26/2.04  --bmc1_ucm_reduced_relation_type        0
% 9.26/2.04  --bmc1_ucm_relax_model                  4
% 9.26/2.04  --bmc1_ucm_full_tr_after_sat            true
% 9.26/2.04  --bmc1_ucm_expand_neg_assumptions       false
% 9.26/2.04  --bmc1_ucm_layered_model                none
% 9.26/2.04  --bmc1_ucm_max_lemma_size               10
% 9.26/2.04  
% 9.26/2.04  ------ AIG Options
% 9.26/2.04  
% 9.26/2.04  --aig_mode                              false
% 9.26/2.04  
% 9.26/2.04  ------ Instantiation Options
% 9.26/2.04  
% 9.26/2.04  --instantiation_flag                    true
% 9.26/2.04  --inst_sos_flag                         true
% 9.26/2.04  --inst_sos_phase                        true
% 9.26/2.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 9.26/2.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 9.26/2.04  --inst_lit_sel_side                     none
% 9.26/2.04  --inst_solver_per_active                1400
% 9.26/2.04  --inst_solver_calls_frac                1.
% 9.26/2.04  --inst_passive_queue_type               priority_queues
% 9.26/2.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 9.26/2.04  --inst_passive_queues_freq              [25;2]
% 9.26/2.04  --inst_dismatching                      true
% 9.26/2.04  --inst_eager_unprocessed_to_passive     true
% 9.26/2.04  --inst_prop_sim_given                   true
% 9.26/2.04  --inst_prop_sim_new                     false
% 9.26/2.04  --inst_subs_new                         false
% 9.26/2.04  --inst_eq_res_simp                      false
% 9.26/2.04  --inst_subs_given                       false
% 9.26/2.04  --inst_orphan_elimination               true
% 9.26/2.04  --inst_learning_loop_flag               true
% 9.26/2.04  --inst_learning_start                   3000
% 9.26/2.04  --inst_learning_factor                  2
% 9.26/2.04  --inst_start_prop_sim_after_learn       3
% 9.26/2.04  --inst_sel_renew                        solver
% 9.26/2.04  --inst_lit_activity_flag                true
% 9.26/2.04  --inst_restr_to_given                   false
% 9.26/2.04  --inst_activity_threshold               500
% 9.26/2.04  --inst_out_proof                        true
% 9.26/2.04  
% 9.26/2.04  ------ Resolution Options
% 9.26/2.04  
% 9.26/2.04  --resolution_flag                       false
% 9.26/2.04  --res_lit_sel                           adaptive
% 9.26/2.04  --res_lit_sel_side                      none
% 9.26/2.04  --res_ordering                          kbo
% 9.26/2.04  --res_to_prop_solver                    active
% 9.26/2.04  --res_prop_simpl_new                    false
% 9.26/2.04  --res_prop_simpl_given                  true
% 9.26/2.04  --res_passive_queue_type                priority_queues
% 9.26/2.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 9.26/2.04  --res_passive_queues_freq               [15;5]
% 9.26/2.04  --res_forward_subs                      full
% 9.26/2.04  --res_backward_subs                     full
% 9.26/2.04  --res_forward_subs_resolution           true
% 9.26/2.04  --res_backward_subs_resolution          true
% 9.26/2.04  --res_orphan_elimination                true
% 9.26/2.04  --res_time_limit                        2.
% 9.26/2.04  --res_out_proof                         true
% 9.26/2.04  
% 9.26/2.04  ------ Superposition Options
% 9.26/2.04  
% 9.26/2.04  --superposition_flag                    true
% 9.26/2.04  --sup_passive_queue_type                priority_queues
% 9.26/2.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 9.26/2.04  --sup_passive_queues_freq               [8;1;4]
% 9.26/2.04  --demod_completeness_check              fast
% 9.26/2.04  --demod_use_ground                      true
% 9.26/2.04  --sup_to_prop_solver                    passive
% 9.26/2.04  --sup_prop_simpl_new                    true
% 9.26/2.04  --sup_prop_simpl_given                  true
% 9.26/2.04  --sup_fun_splitting                     true
% 9.26/2.04  --sup_smt_interval                      50000
% 9.26/2.04  
% 9.26/2.04  ------ Superposition Simplification Setup
% 9.26/2.04  
% 9.26/2.04  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 9.26/2.04  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 9.26/2.04  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 9.26/2.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 9.26/2.04  --sup_full_triv                         [TrivRules;PropSubs]
% 9.26/2.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 9.26/2.04  --sup_full_bw                           [BwDemod;BwSubsumption]
% 9.26/2.04  --sup_immed_triv                        [TrivRules]
% 9.26/2.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 9.26/2.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 9.26/2.04  --sup_immed_bw_main                     []
% 9.26/2.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 9.26/2.04  --sup_input_triv                        [Unflattening;TrivRules]
% 9.26/2.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 9.26/2.04  --sup_input_bw                          []
% 9.26/2.04  
% 9.26/2.04  ------ Combination Options
% 9.26/2.04  
% 9.26/2.04  --comb_res_mult                         3
% 9.26/2.04  --comb_sup_mult                         2
% 9.26/2.04  --comb_inst_mult                        10
% 9.26/2.04  
% 9.26/2.04  ------ Debug Options
% 9.26/2.04  
% 9.26/2.04  --dbg_backtrace                         false
% 9.26/2.04  --dbg_dump_prop_clauses                 false
% 9.26/2.04  --dbg_dump_prop_clauses_file            -
% 9.26/2.04  --dbg_out_stat                          false
% 9.26/2.04  
% 9.26/2.04  
% 9.26/2.04  
% 9.26/2.04  
% 9.26/2.04  ------ Proving...
% 9.26/2.04  
% 9.26/2.04  
% 9.26/2.04  % SZS status Theorem for theBenchmark.p
% 9.26/2.04  
% 9.26/2.04  % SZS output start CNFRefutation for theBenchmark.p
% 9.26/2.04  
% 9.26/2.04  fof(f6,axiom,(
% 9.26/2.04    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 9.26/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 9.26/2.04  
% 9.26/2.04  fof(f23,plain,(
% 9.26/2.04    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 9.26/2.04    inference(ennf_transformation,[],[f6])).
% 9.26/2.04  
% 9.26/2.04  fof(f24,plain,(
% 9.26/2.04    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 9.26/2.04    inference(flattening,[],[f23])).
% 9.26/2.04  
% 9.26/2.04  fof(f52,plain,(
% 9.26/2.04    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 9.26/2.04    inference(nnf_transformation,[],[f24])).
% 9.26/2.04  
% 9.26/2.04  fof(f53,plain,(
% 9.26/2.04    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 9.26/2.04    inference(rectify,[],[f52])).
% 9.26/2.04  
% 9.26/2.04  fof(f56,plain,(
% 9.26/2.04    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK7(X0,X5)) = X5 & r2_hidden(sK7(X0,X5),k1_relat_1(X0))))),
% 9.26/2.04    introduced(choice_axiom,[])).
% 9.26/2.04  
% 9.26/2.04  fof(f55,plain,(
% 9.26/2.04    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK6(X0,X1)) = X2 & r2_hidden(sK6(X0,X1),k1_relat_1(X0))))) )),
% 9.26/2.04    introduced(choice_axiom,[])).
% 9.26/2.04  
% 9.26/2.04  fof(f54,plain,(
% 9.26/2.04    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK5(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK5(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK5(X0,X1),X1))))),
% 9.26/2.04    introduced(choice_axiom,[])).
% 9.26/2.04  
% 9.26/2.04  fof(f57,plain,(
% 9.26/2.04    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK5(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK5(X0,X1),X1)) & ((k1_funct_1(X0,sK6(X0,X1)) = sK5(X0,X1) & r2_hidden(sK6(X0,X1),k1_relat_1(X0))) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK7(X0,X5)) = X5 & r2_hidden(sK7(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 9.26/2.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f53,f56,f55,f54])).
% 9.26/2.04  
% 9.26/2.04  fof(f82,plain,(
% 9.26/2.04    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(sK6(X0,X1),k1_relat_1(X0)) | r2_hidden(sK5(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 9.26/2.04    inference(cnf_transformation,[],[f57])).
% 9.26/2.04  
% 9.26/2.04  fof(f2,axiom,(
% 9.26/2.04    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 9.26/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 9.26/2.04  
% 9.26/2.04  fof(f18,plain,(
% 9.26/2.04    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 9.26/2.04    inference(ennf_transformation,[],[f2])).
% 9.26/2.04  
% 9.26/2.04  fof(f42,plain,(
% 9.26/2.04    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 9.26/2.04    inference(nnf_transformation,[],[f18])).
% 9.26/2.04  
% 9.26/2.04  fof(f43,plain,(
% 9.26/2.04    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 9.26/2.04    inference(rectify,[],[f42])).
% 9.26/2.04  
% 9.26/2.04  fof(f44,plain,(
% 9.26/2.04    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 9.26/2.04    introduced(choice_axiom,[])).
% 9.26/2.04  
% 9.26/2.04  fof(f45,plain,(
% 9.26/2.04    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 9.26/2.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f44])).
% 9.26/2.04  
% 9.26/2.04  fof(f67,plain,(
% 9.26/2.04    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 9.26/2.04    inference(cnf_transformation,[],[f45])).
% 9.26/2.04  
% 9.26/2.04  fof(f15,conjecture,(
% 9.26/2.04    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 9.26/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 9.26/2.04  
% 9.26/2.04  fof(f16,negated_conjecture,(
% 9.26/2.04    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 9.26/2.04    inference(negated_conjecture,[],[f15])).
% 9.26/2.04  
% 9.26/2.04  fof(f36,plain,(
% 9.26/2.04    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 9.26/2.04    inference(ennf_transformation,[],[f16])).
% 9.26/2.04  
% 9.26/2.04  fof(f37,plain,(
% 9.26/2.04    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 9.26/2.04    inference(flattening,[],[f36])).
% 9.26/2.04  
% 9.26/2.04  fof(f62,plain,(
% 9.26/2.04    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK13) != k7_partfun1(X0,X4,k1_funct_1(X3,sK13)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK13,X1))) )),
% 9.26/2.04    introduced(choice_axiom,[])).
% 9.26/2.04  
% 9.26/2.04  fof(f61,plain,(
% 9.26/2.04    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK12),X5) != k7_partfun1(X0,sK12,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK12)) & m1_subset_1(X5,X1)) & m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK12))) )),
% 9.26/2.04    introduced(choice_axiom,[])).
% 9.26/2.04  
% 9.26/2.04  fof(f60,plain,(
% 9.26/2.04    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,sK11,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(sK11,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK11),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK11,X1,X2) & v1_funct_1(sK11))) )),
% 9.26/2.04    introduced(choice_axiom,[])).
% 9.26/2.04  
% 9.26/2.04  fof(f59,plain,(
% 9.26/2.04    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK9,sK10,sK8,X3,X4),X5) != k7_partfun1(sK8,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK9 & r1_tarski(k2_relset_1(sK9,sK10,X3),k1_relset_1(sK10,sK8,X4)) & m1_subset_1(X5,sK9)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK10,sK8))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) & v1_funct_2(X3,sK9,sK10) & v1_funct_1(X3)) & ~v1_xboole_0(sK10))),
% 9.26/2.04    introduced(choice_axiom,[])).
% 9.26/2.04  
% 9.26/2.04  fof(f63,plain,(
% 9.26/2.04    (((k1_funct_1(k8_funct_2(sK9,sK10,sK8,sK11,sK12),sK13) != k7_partfun1(sK8,sK12,k1_funct_1(sK11,sK13)) & k1_xboole_0 != sK9 & r1_tarski(k2_relset_1(sK9,sK10,sK11),k1_relset_1(sK10,sK8,sK12)) & m1_subset_1(sK13,sK9)) & m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK8))) & v1_funct_1(sK12)) & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) & v1_funct_2(sK11,sK9,sK10) & v1_funct_1(sK11)) & ~v1_xboole_0(sK10)),
% 9.26/2.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11,sK12,sK13])],[f37,f62,f61,f60,f59])).
% 9.26/2.04  
% 9.26/2.04  fof(f101,plain,(
% 9.26/2.04    m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))),
% 9.26/2.04    inference(cnf_transformation,[],[f63])).
% 9.26/2.04  
% 9.26/2.04  fof(f12,axiom,(
% 9.26/2.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 9.26/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 9.26/2.04  
% 9.26/2.04  fof(f30,plain,(
% 9.26/2.04    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 9.26/2.04    inference(ennf_transformation,[],[f12])).
% 9.26/2.04  
% 9.26/2.04  fof(f31,plain,(
% 9.26/2.04    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 9.26/2.04    inference(flattening,[],[f30])).
% 9.26/2.04  
% 9.26/2.04  fof(f58,plain,(
% 9.26/2.04    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 9.26/2.04    inference(nnf_transformation,[],[f31])).
% 9.26/2.04  
% 9.26/2.04  fof(f90,plain,(
% 9.26/2.04    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 9.26/2.04    inference(cnf_transformation,[],[f58])).
% 9.26/2.04  
% 9.26/2.04  fof(f100,plain,(
% 9.26/2.04    v1_funct_2(sK11,sK9,sK10)),
% 9.26/2.04    inference(cnf_transformation,[],[f63])).
% 9.26/2.04  
% 9.26/2.04  fof(f10,axiom,(
% 9.26/2.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 9.26/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 9.26/2.04  
% 9.26/2.04  fof(f28,plain,(
% 9.26/2.04    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 9.26/2.04    inference(ennf_transformation,[],[f10])).
% 9.26/2.04  
% 9.26/2.04  fof(f88,plain,(
% 9.26/2.04    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 9.26/2.04    inference(cnf_transformation,[],[f28])).
% 9.26/2.04  
% 9.26/2.04  fof(f81,plain,(
% 9.26/2.04    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 9.26/2.04    inference(cnf_transformation,[],[f57])).
% 9.26/2.04  
% 9.26/2.04  fof(f113,plain,(
% 9.26/2.04    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 9.26/2.04    inference(equality_resolution,[],[f81])).
% 9.26/2.04  
% 9.26/2.04  fof(f114,plain,(
% 9.26/2.04    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 9.26/2.04    inference(equality_resolution,[],[f113])).
% 9.26/2.04  
% 9.26/2.04  fof(f11,axiom,(
% 9.26/2.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 9.26/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 9.26/2.04  
% 9.26/2.04  fof(f29,plain,(
% 9.26/2.04    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 9.26/2.04    inference(ennf_transformation,[],[f11])).
% 9.26/2.04  
% 9.26/2.04  fof(f89,plain,(
% 9.26/2.04    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 9.26/2.04    inference(cnf_transformation,[],[f29])).
% 9.26/2.04  
% 9.26/2.04  fof(f105,plain,(
% 9.26/2.04    r1_tarski(k2_relset_1(sK9,sK10,sK11),k1_relset_1(sK10,sK8,sK12))),
% 9.26/2.04    inference(cnf_transformation,[],[f63])).
% 9.26/2.04  
% 9.26/2.04  fof(f66,plain,(
% 9.26/2.04    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 9.26/2.04    inference(cnf_transformation,[],[f45])).
% 9.26/2.04  
% 9.26/2.04  fof(f103,plain,(
% 9.26/2.04    m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK8)))),
% 9.26/2.04    inference(cnf_transformation,[],[f63])).
% 9.26/2.04  
% 9.26/2.04  fof(f99,plain,(
% 9.26/2.04    v1_funct_1(sK11)),
% 9.26/2.04    inference(cnf_transformation,[],[f63])).
% 9.26/2.04  
% 9.26/2.04  fof(f8,axiom,(
% 9.26/2.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 9.26/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 9.26/2.04  
% 9.26/2.04  fof(f26,plain,(
% 9.26/2.04    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 9.26/2.04    inference(ennf_transformation,[],[f8])).
% 9.26/2.04  
% 9.26/2.04  fof(f86,plain,(
% 9.26/2.04    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 9.26/2.04    inference(cnf_transformation,[],[f26])).
% 9.26/2.04  
% 9.26/2.04  fof(f9,axiom,(
% 9.26/2.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 9.26/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 9.26/2.04  
% 9.26/2.04  fof(f17,plain,(
% 9.26/2.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 9.26/2.04    inference(pure_predicate_removal,[],[f9])).
% 9.26/2.04  
% 9.26/2.04  fof(f27,plain,(
% 9.26/2.04    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 9.26/2.04    inference(ennf_transformation,[],[f17])).
% 9.26/2.04  
% 9.26/2.04  fof(f87,plain,(
% 9.26/2.04    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 9.26/2.04    inference(cnf_transformation,[],[f27])).
% 9.26/2.04  
% 9.26/2.04  fof(f13,axiom,(
% 9.26/2.04    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)))),
% 9.26/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 9.26/2.04  
% 9.26/2.04  fof(f32,plain,(
% 9.26/2.04    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 9.26/2.04    inference(ennf_transformation,[],[f13])).
% 9.26/2.04  
% 9.26/2.04  fof(f33,plain,(
% 9.26/2.04    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 9.26/2.04    inference(flattening,[],[f32])).
% 9.26/2.04  
% 9.26/2.04  fof(f96,plain,(
% 9.26/2.04    ( ! [X2,X0,X1] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 9.26/2.04    inference(cnf_transformation,[],[f33])).
% 9.26/2.04  
% 9.26/2.04  fof(f102,plain,(
% 9.26/2.04    v1_funct_1(sK12)),
% 9.26/2.04    inference(cnf_transformation,[],[f63])).
% 9.26/2.04  
% 9.26/2.04  fof(f98,plain,(
% 9.26/2.04    ~v1_xboole_0(sK10)),
% 9.26/2.04    inference(cnf_transformation,[],[f63])).
% 9.26/2.04  
% 9.26/2.04  fof(f1,axiom,(
% 9.26/2.04    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 9.26/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 9.26/2.04  
% 9.26/2.04  fof(f38,plain,(
% 9.26/2.04    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 9.26/2.04    inference(nnf_transformation,[],[f1])).
% 9.26/2.04  
% 9.26/2.04  fof(f39,plain,(
% 9.26/2.04    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 9.26/2.04    inference(rectify,[],[f38])).
% 9.26/2.04  
% 9.26/2.04  fof(f40,plain,(
% 9.26/2.04    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 9.26/2.04    introduced(choice_axiom,[])).
% 9.26/2.04  
% 9.26/2.04  fof(f41,plain,(
% 9.26/2.04    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 9.26/2.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).
% 9.26/2.04  
% 9.26/2.04  fof(f65,plain,(
% 9.26/2.04    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 9.26/2.04    inference(cnf_transformation,[],[f41])).
% 9.26/2.04  
% 9.26/2.04  fof(f3,axiom,(
% 9.26/2.04    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 9.26/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 9.26/2.04  
% 9.26/2.04  fof(f69,plain,(
% 9.26/2.04    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 9.26/2.04    inference(cnf_transformation,[],[f3])).
% 9.26/2.04  
% 9.26/2.04  fof(f7,axiom,(
% 9.26/2.04    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 9.26/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 9.26/2.04  
% 9.26/2.04  fof(f25,plain,(
% 9.26/2.04    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 9.26/2.04    inference(ennf_transformation,[],[f7])).
% 9.26/2.04  
% 9.26/2.04  fof(f85,plain,(
% 9.26/2.04    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 9.26/2.04    inference(cnf_transformation,[],[f25])).
% 9.26/2.04  
% 9.26/2.04  fof(f104,plain,(
% 9.26/2.04    m1_subset_1(sK13,sK9)),
% 9.26/2.04    inference(cnf_transformation,[],[f63])).
% 9.26/2.04  
% 9.26/2.04  fof(f106,plain,(
% 9.26/2.04    k1_xboole_0 != sK9),
% 9.26/2.04    inference(cnf_transformation,[],[f63])).
% 9.26/2.04  
% 9.26/2.04  fof(f107,plain,(
% 9.26/2.04    k1_funct_1(k8_funct_2(sK9,sK10,sK8,sK11,sK12),sK13) != k7_partfun1(sK8,sK12,k1_funct_1(sK11,sK13))),
% 9.26/2.04    inference(cnf_transformation,[],[f63])).
% 9.26/2.04  
% 9.26/2.04  fof(f14,axiom,(
% 9.26/2.04    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 9.26/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 9.26/2.04  
% 9.26/2.04  fof(f34,plain,(
% 9.26/2.04    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 9.26/2.04    inference(ennf_transformation,[],[f14])).
% 9.26/2.04  
% 9.26/2.04  fof(f35,plain,(
% 9.26/2.04    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 9.26/2.04    inference(flattening,[],[f34])).
% 9.26/2.04  
% 9.26/2.04  fof(f97,plain,(
% 9.26/2.04    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 9.26/2.04    inference(cnf_transformation,[],[f35])).
% 9.26/2.04  
% 9.26/2.04  fof(f79,plain,(
% 9.26/2.04    ( ! [X0,X5,X1] : (r2_hidden(sK7(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 9.26/2.04    inference(cnf_transformation,[],[f57])).
% 9.26/2.04  
% 9.26/2.04  fof(f116,plain,(
% 9.26/2.04    ( ! [X0,X5] : (r2_hidden(sK7(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 9.26/2.04    inference(equality_resolution,[],[f79])).
% 9.26/2.04  
% 9.26/2.04  fof(f64,plain,(
% 9.26/2.04    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 9.26/2.04    inference(cnf_transformation,[],[f41])).
% 9.26/2.04  
% 9.26/2.04  fof(f4,axiom,(
% 9.26/2.04    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 9.26/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 9.26/2.04  
% 9.26/2.04  fof(f19,plain,(
% 9.26/2.04    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 9.26/2.04    inference(ennf_transformation,[],[f4])).
% 9.26/2.04  
% 9.26/2.04  fof(f20,plain,(
% 9.26/2.04    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 9.26/2.04    inference(flattening,[],[f19])).
% 9.26/2.04  
% 9.26/2.04  fof(f70,plain,(
% 9.26/2.04    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 9.26/2.04    inference(cnf_transformation,[],[f20])).
% 9.26/2.04  
% 9.26/2.04  cnf(c_17,plain,
% 9.26/2.04      ( r2_hidden(sK6(X0,X1),k1_relat_1(X0))
% 9.26/2.04      | r2_hidden(sK5(X0,X1),X1)
% 9.26/2.04      | ~ v1_relat_1(X0)
% 9.26/2.04      | ~ v1_funct_1(X0)
% 9.26/2.04      | k2_relat_1(X0) = X1 ),
% 9.26/2.04      inference(cnf_transformation,[],[f82]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_3246,plain,
% 9.26/2.04      ( k2_relat_1(X0) = X1
% 9.26/2.04      | r2_hidden(sK6(X0,X1),k1_relat_1(X0)) = iProver_top
% 9.26/2.04      | r2_hidden(sK5(X0,X1),X1) = iProver_top
% 9.26/2.04      | v1_relat_1(X0) != iProver_top
% 9.26/2.04      | v1_funct_1(X0) != iProver_top ),
% 9.26/2.04      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_3,plain,
% 9.26/2.04      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 9.26/2.04      inference(cnf_transformation,[],[f67]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_3260,plain,
% 9.26/2.04      ( r1_tarski(X0,X1) = iProver_top
% 9.26/2.04      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 9.26/2.04      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_40,negated_conjecture,
% 9.26/2.04      ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) ),
% 9.26/2.04      inference(cnf_transformation,[],[f101]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_3227,plain,
% 9.26/2.04      ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) = iProver_top ),
% 9.26/2.04      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_31,plain,
% 9.26/2.04      ( ~ v1_funct_2(X0,X1,X2)
% 9.26/2.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 9.26/2.04      | k1_relset_1(X1,X2,X0) = X1
% 9.26/2.04      | k1_xboole_0 = X2 ),
% 9.26/2.04      inference(cnf_transformation,[],[f90]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_3233,plain,
% 9.26/2.04      ( k1_relset_1(X0,X1,X2) = X0
% 9.26/2.04      | k1_xboole_0 = X1
% 9.26/2.04      | v1_funct_2(X2,X0,X1) != iProver_top
% 9.26/2.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 9.26/2.04      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_4843,plain,
% 9.26/2.04      ( k1_relset_1(sK9,sK10,sK11) = sK9
% 9.26/2.04      | sK10 = k1_xboole_0
% 9.26/2.04      | v1_funct_2(sK11,sK9,sK10) != iProver_top ),
% 9.26/2.04      inference(superposition,[status(thm)],[c_3227,c_3233]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_41,negated_conjecture,
% 9.26/2.04      ( v1_funct_2(sK11,sK9,sK10) ),
% 9.26/2.04      inference(cnf_transformation,[],[f100]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_46,plain,
% 9.26/2.04      ( v1_funct_2(sK11,sK9,sK10) = iProver_top ),
% 9.26/2.04      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_5440,plain,
% 9.26/2.04      ( sK10 = k1_xboole_0 | k1_relset_1(sK9,sK10,sK11) = sK9 ),
% 9.26/2.04      inference(global_propositional_subsumption,
% 9.26/2.04                [status(thm)],
% 9.26/2.04                [c_4843,c_46]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_5441,plain,
% 9.26/2.04      ( k1_relset_1(sK9,sK10,sK11) = sK9 | sK10 = k1_xboole_0 ),
% 9.26/2.04      inference(renaming,[status(thm)],[c_5440]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_24,plain,
% 9.26/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 9.26/2.04      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 9.26/2.04      inference(cnf_transformation,[],[f88]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_3240,plain,
% 9.26/2.04      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 9.26/2.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 9.26/2.04      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_4917,plain,
% 9.26/2.04      ( k1_relset_1(sK9,sK10,sK11) = k1_relat_1(sK11) ),
% 9.26/2.04      inference(superposition,[status(thm)],[c_3227,c_3240]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_5442,plain,
% 9.26/2.04      ( k1_relat_1(sK11) = sK9 | sK10 = k1_xboole_0 ),
% 9.26/2.04      inference(demodulation,[status(thm)],[c_5441,c_4917]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_18,plain,
% 9.26/2.04      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 9.26/2.04      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 9.26/2.04      | ~ v1_relat_1(X1)
% 9.26/2.04      | ~ v1_funct_1(X1) ),
% 9.26/2.04      inference(cnf_transformation,[],[f114]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_3245,plain,
% 9.26/2.04      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 9.26/2.04      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 9.26/2.04      | v1_relat_1(X1) != iProver_top
% 9.26/2.04      | v1_funct_1(X1) != iProver_top ),
% 9.26/2.04      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_25,plain,
% 9.26/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 9.26/2.04      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 9.26/2.04      inference(cnf_transformation,[],[f89]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_3239,plain,
% 9.26/2.04      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 9.26/2.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 9.26/2.04      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_4539,plain,
% 9.26/2.04      ( k2_relset_1(sK9,sK10,sK11) = k2_relat_1(sK11) ),
% 9.26/2.04      inference(superposition,[status(thm)],[c_3227,c_3239]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_36,negated_conjecture,
% 9.26/2.04      ( r1_tarski(k2_relset_1(sK9,sK10,sK11),k1_relset_1(sK10,sK8,sK12)) ),
% 9.26/2.04      inference(cnf_transformation,[],[f105]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_3231,plain,
% 9.26/2.04      ( r1_tarski(k2_relset_1(sK9,sK10,sK11),k1_relset_1(sK10,sK8,sK12)) = iProver_top ),
% 9.26/2.04      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_4679,plain,
% 9.26/2.04      ( r1_tarski(k2_relat_1(sK11),k1_relset_1(sK10,sK8,sK12)) = iProver_top ),
% 9.26/2.04      inference(demodulation,[status(thm)],[c_4539,c_3231]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_4,plain,
% 9.26/2.04      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 9.26/2.04      inference(cnf_transformation,[],[f66]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_3259,plain,
% 9.26/2.04      ( r1_tarski(X0,X1) != iProver_top
% 9.26/2.04      | r2_hidden(X2,X0) != iProver_top
% 9.26/2.04      | r2_hidden(X2,X1) = iProver_top ),
% 9.26/2.04      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_5041,plain,
% 9.26/2.04      ( r2_hidden(X0,k1_relset_1(sK10,sK8,sK12)) = iProver_top
% 9.26/2.04      | r2_hidden(X0,k2_relat_1(sK11)) != iProver_top ),
% 9.26/2.04      inference(superposition,[status(thm)],[c_4679,c_3259]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_38,negated_conjecture,
% 9.26/2.04      ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK8))) ),
% 9.26/2.04      inference(cnf_transformation,[],[f103]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_3229,plain,
% 9.26/2.04      ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK8))) = iProver_top ),
% 9.26/2.04      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_4916,plain,
% 9.26/2.04      ( k1_relset_1(sK10,sK8,sK12) = k1_relat_1(sK12) ),
% 9.26/2.04      inference(superposition,[status(thm)],[c_3229,c_3240]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_5042,plain,
% 9.26/2.04      ( r2_hidden(X0,k2_relat_1(sK11)) != iProver_top
% 9.26/2.04      | r2_hidden(X0,k1_relat_1(sK12)) = iProver_top ),
% 9.26/2.04      inference(light_normalisation,[status(thm)],[c_5041,c_4916]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_6579,plain,
% 9.26/2.04      ( r2_hidden(X0,k1_relat_1(sK11)) != iProver_top
% 9.26/2.04      | r2_hidden(k1_funct_1(sK11,X0),k1_relat_1(sK12)) = iProver_top
% 9.26/2.04      | v1_relat_1(sK11) != iProver_top
% 9.26/2.04      | v1_funct_1(sK11) != iProver_top ),
% 9.26/2.04      inference(superposition,[status(thm)],[c_3245,c_5042]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_42,negated_conjecture,
% 9.26/2.04      ( v1_funct_1(sK11) ),
% 9.26/2.04      inference(cnf_transformation,[],[f99]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_45,plain,
% 9.26/2.04      ( v1_funct_1(sK11) = iProver_top ),
% 9.26/2.04      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_22,plain,
% 9.26/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 9.26/2.04      | v1_relat_1(X0) ),
% 9.26/2.04      inference(cnf_transformation,[],[f86]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_3241,plain,
% 9.26/2.04      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 9.26/2.04      | v1_relat_1(X0) = iProver_top ),
% 9.26/2.04      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_4504,plain,
% 9.26/2.04      ( v1_relat_1(sK11) = iProver_top ),
% 9.26/2.04      inference(superposition,[status(thm)],[c_3227,c_3241]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_14192,plain,
% 9.26/2.04      ( r2_hidden(X0,k1_relat_1(sK11)) != iProver_top
% 9.26/2.04      | r2_hidden(k1_funct_1(sK11,X0),k1_relat_1(sK12)) = iProver_top ),
% 9.26/2.04      inference(global_propositional_subsumption,
% 9.26/2.04                [status(thm)],
% 9.26/2.04                [c_6579,c_45,c_4504]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_23,plain,
% 9.26/2.04      ( v5_relat_1(X0,X1)
% 9.26/2.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 9.26/2.04      inference(cnf_transformation,[],[f87]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_32,plain,
% 9.26/2.04      ( ~ v5_relat_1(X0,X1)
% 9.26/2.04      | ~ r2_hidden(X2,k1_relat_1(X0))
% 9.26/2.04      | ~ v1_relat_1(X0)
% 9.26/2.04      | ~ v1_funct_1(X0)
% 9.26/2.04      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 9.26/2.04      inference(cnf_transformation,[],[f96]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_467,plain,
% 9.26/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 9.26/2.04      | ~ r2_hidden(X3,k1_relat_1(X0))
% 9.26/2.04      | ~ v1_relat_1(X0)
% 9.26/2.04      | ~ v1_funct_1(X0)
% 9.26/2.04      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 9.26/2.04      inference(resolution,[status(thm)],[c_23,c_32]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_471,plain,
% 9.26/2.04      ( ~ r2_hidden(X3,k1_relat_1(X0))
% 9.26/2.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 9.26/2.04      | ~ v1_funct_1(X0)
% 9.26/2.04      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 9.26/2.04      inference(global_propositional_subsumption,
% 9.26/2.04                [status(thm)],
% 9.26/2.04                [c_467,c_22]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_472,plain,
% 9.26/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 9.26/2.04      | ~ r2_hidden(X3,k1_relat_1(X0))
% 9.26/2.04      | ~ v1_funct_1(X0)
% 9.26/2.04      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 9.26/2.04      inference(renaming,[status(thm)],[c_471]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_3223,plain,
% 9.26/2.04      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
% 9.26/2.04      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
% 9.26/2.04      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 9.26/2.04      | v1_funct_1(X1) != iProver_top ),
% 9.26/2.04      inference(predicate_to_equality,[status(thm)],[c_472]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_3827,plain,
% 9.26/2.04      ( k7_partfun1(sK8,sK12,X0) = k1_funct_1(sK12,X0)
% 9.26/2.04      | r2_hidden(X0,k1_relat_1(sK12)) != iProver_top
% 9.26/2.04      | v1_funct_1(sK12) != iProver_top ),
% 9.26/2.04      inference(superposition,[status(thm)],[c_3229,c_3223]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_39,negated_conjecture,
% 9.26/2.04      ( v1_funct_1(sK12) ),
% 9.26/2.04      inference(cnf_transformation,[],[f102]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_48,plain,
% 9.26/2.04      ( v1_funct_1(sK12) = iProver_top ),
% 9.26/2.04      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_3969,plain,
% 9.26/2.04      ( r2_hidden(X0,k1_relat_1(sK12)) != iProver_top
% 9.26/2.04      | k7_partfun1(sK8,sK12,X0) = k1_funct_1(sK12,X0) ),
% 9.26/2.04      inference(global_propositional_subsumption,
% 9.26/2.04                [status(thm)],
% 9.26/2.04                [c_3827,c_48]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_3970,plain,
% 9.26/2.04      ( k7_partfun1(sK8,sK12,X0) = k1_funct_1(sK12,X0)
% 9.26/2.04      | r2_hidden(X0,k1_relat_1(sK12)) != iProver_top ),
% 9.26/2.04      inference(renaming,[status(thm)],[c_3969]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_14200,plain,
% 9.26/2.04      ( k7_partfun1(sK8,sK12,k1_funct_1(sK11,X0)) = k1_funct_1(sK12,k1_funct_1(sK11,X0))
% 9.26/2.04      | r2_hidden(X0,k1_relat_1(sK11)) != iProver_top ),
% 9.26/2.04      inference(superposition,[status(thm)],[c_14192,c_3970]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_14304,plain,
% 9.26/2.04      ( k7_partfun1(sK8,sK12,k1_funct_1(sK11,X0)) = k1_funct_1(sK12,k1_funct_1(sK11,X0))
% 9.26/2.04      | sK10 = k1_xboole_0
% 9.26/2.04      | r2_hidden(X0,sK9) != iProver_top ),
% 9.26/2.04      inference(superposition,[status(thm)],[c_5442,c_14200]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_43,negated_conjecture,
% 9.26/2.04      ( ~ v1_xboole_0(sK10) ),
% 9.26/2.04      inference(cnf_transformation,[],[f98]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_44,plain,
% 9.26/2.04      ( v1_xboole_0(sK10) != iProver_top ),
% 9.26/2.04      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_2566,plain,
% 9.26/2.04      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 9.26/2.04      theory(equality) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_3339,plain,
% 9.26/2.04      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK10) | sK10 != X0 ),
% 9.26/2.04      inference(instantiation,[status(thm)],[c_2566]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_3343,plain,
% 9.26/2.04      ( sK10 != X0
% 9.26/2.04      | v1_xboole_0(X0) != iProver_top
% 9.26/2.04      | v1_xboole_0(sK10) = iProver_top ),
% 9.26/2.04      inference(predicate_to_equality,[status(thm)],[c_3339]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_3345,plain,
% 9.26/2.04      ( sK10 != k1_xboole_0
% 9.26/2.04      | v1_xboole_0(sK10) = iProver_top
% 9.26/2.04      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 9.26/2.04      inference(instantiation,[status(thm)],[c_3343]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_0,plain,
% 9.26/2.04      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 9.26/2.04      inference(cnf_transformation,[],[f65]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_3263,plain,
% 9.26/2.04      ( r2_hidden(sK0(X0),X0) = iProver_top
% 9.26/2.04      | v1_xboole_0(X0) = iProver_top ),
% 9.26/2.04      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_5,plain,
% 9.26/2.04      ( r1_tarski(k1_xboole_0,X0) ),
% 9.26/2.04      inference(cnf_transformation,[],[f69]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_3258,plain,
% 9.26/2.04      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 9.26/2.04      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_21,plain,
% 9.26/2.04      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 9.26/2.04      inference(cnf_transformation,[],[f85]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_3242,plain,
% 9.26/2.04      ( r1_tarski(X0,X1) != iProver_top
% 9.26/2.04      | r2_hidden(X1,X0) != iProver_top ),
% 9.26/2.04      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_4151,plain,
% 9.26/2.04      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 9.26/2.04      inference(superposition,[status(thm)],[c_3258,c_3242]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_8560,plain,
% 9.26/2.04      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 9.26/2.04      inference(superposition,[status(thm)],[c_3263,c_4151]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_22393,plain,
% 9.26/2.04      ( k7_partfun1(sK8,sK12,k1_funct_1(sK11,X0)) = k1_funct_1(sK12,k1_funct_1(sK11,X0))
% 9.26/2.04      | r2_hidden(X0,sK9) != iProver_top ),
% 9.26/2.04      inference(global_propositional_subsumption,
% 9.26/2.04                [status(thm)],
% 9.26/2.04                [c_14304,c_44,c_3345,c_8560]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_22400,plain,
% 9.26/2.04      ( k7_partfun1(sK8,sK12,k1_funct_1(sK11,sK1(sK9,X0))) = k1_funct_1(sK12,k1_funct_1(sK11,sK1(sK9,X0)))
% 9.26/2.04      | r1_tarski(sK9,X0) = iProver_top ),
% 9.26/2.04      inference(superposition,[status(thm)],[c_3260,c_22393]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_22601,plain,
% 9.26/2.04      ( k7_partfun1(sK8,sK12,k1_funct_1(sK11,sK1(sK9,X0))) = k1_funct_1(sK12,k1_funct_1(sK11,sK1(sK9,X0)))
% 9.26/2.04      | r2_hidden(X0,sK9) != iProver_top ),
% 9.26/2.04      inference(superposition,[status(thm)],[c_22400,c_3242]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_37,negated_conjecture,
% 9.26/2.04      ( m1_subset_1(sK13,sK9) ),
% 9.26/2.04      inference(cnf_transformation,[],[f104]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_35,negated_conjecture,
% 9.26/2.04      ( k1_xboole_0 != sK9 ),
% 9.26/2.04      inference(cnf_transformation,[],[f106]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_34,negated_conjecture,
% 9.26/2.04      ( k1_funct_1(k8_funct_2(sK9,sK10,sK8,sK11,sK12),sK13) != k7_partfun1(sK8,sK12,k1_funct_1(sK11,sK13)) ),
% 9.26/2.04      inference(cnf_transformation,[],[f107]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_2565,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_3313,plain,
% 9.26/2.04      ( k7_partfun1(sK8,sK12,k1_funct_1(sK11,sK13)) != X0
% 9.26/2.04      | k1_funct_1(k8_funct_2(sK9,sK10,sK8,sK11,sK12),sK13) != X0
% 9.26/2.04      | k1_funct_1(k8_funct_2(sK9,sK10,sK8,sK11,sK12),sK13) = k7_partfun1(sK8,sK12,k1_funct_1(sK11,sK13)) ),
% 9.26/2.04      inference(instantiation,[status(thm)],[c_2565]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_3368,plain,
% 9.26/2.04      ( k7_partfun1(sK8,sK12,k1_funct_1(sK11,sK13)) != k1_funct_1(sK12,k1_funct_1(sK11,sK13))
% 9.26/2.04      | k1_funct_1(k8_funct_2(sK9,sK10,sK8,sK11,sK12),sK13) = k7_partfun1(sK8,sK12,k1_funct_1(sK11,sK13))
% 9.26/2.04      | k1_funct_1(k8_funct_2(sK9,sK10,sK8,sK11,sK12),sK13) != k1_funct_1(sK12,k1_funct_1(sK11,sK13)) ),
% 9.26/2.04      inference(instantiation,[status(thm)],[c_3313]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_33,plain,
% 9.26/2.04      ( ~ v1_funct_2(X0,X1,X2)
% 9.26/2.04      | ~ m1_subset_1(X3,X1)
% 9.26/2.04      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 9.26/2.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 9.26/2.04      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X5,X4))
% 9.26/2.04      | ~ v1_funct_1(X4)
% 9.26/2.04      | ~ v1_funct_1(X0)
% 9.26/2.04      | v1_xboole_0(X2)
% 9.26/2.04      | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 9.26/2.04      | k1_xboole_0 = X1 ),
% 9.26/2.04      inference(cnf_transformation,[],[f97]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_3347,plain,
% 9.26/2.04      ( ~ v1_funct_2(X0,X1,sK10)
% 9.26/2.04      | ~ m1_subset_1(X2,X1)
% 9.26/2.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK10)))
% 9.26/2.04      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK10,X4)))
% 9.26/2.04      | ~ r1_tarski(k2_relset_1(X1,sK10,X0),k1_relset_1(sK10,X4,X3))
% 9.26/2.04      | ~ v1_funct_1(X0)
% 9.26/2.04      | ~ v1_funct_1(X3)
% 9.26/2.04      | v1_xboole_0(sK10)
% 9.26/2.04      | k1_funct_1(k8_funct_2(X1,sK10,X4,X0,X3),X2) = k1_funct_1(X3,k1_funct_1(X0,X2))
% 9.26/2.04      | k1_xboole_0 = X1 ),
% 9.26/2.04      inference(instantiation,[status(thm)],[c_33]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_3396,plain,
% 9.26/2.04      ( ~ v1_funct_2(X0,sK9,sK10)
% 9.26/2.04      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK10,X2)))
% 9.26/2.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
% 9.26/2.04      | ~ m1_subset_1(X3,sK9)
% 9.26/2.04      | ~ r1_tarski(k2_relset_1(sK9,sK10,X0),k1_relset_1(sK10,X2,X1))
% 9.26/2.04      | ~ v1_funct_1(X0)
% 9.26/2.04      | ~ v1_funct_1(X1)
% 9.26/2.04      | v1_xboole_0(sK10)
% 9.26/2.04      | k1_funct_1(k8_funct_2(sK9,sK10,X2,X0,X1),X3) = k1_funct_1(X1,k1_funct_1(X0,X3))
% 9.26/2.04      | k1_xboole_0 = sK9 ),
% 9.26/2.04      inference(instantiation,[status(thm)],[c_3347]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_3445,plain,
% 9.26/2.04      ( ~ v1_funct_2(sK11,sK9,sK10)
% 9.26/2.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK10,X1)))
% 9.26/2.04      | ~ m1_subset_1(X2,sK9)
% 9.26/2.04      | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
% 9.26/2.04      | ~ r1_tarski(k2_relset_1(sK9,sK10,sK11),k1_relset_1(sK10,X1,X0))
% 9.26/2.04      | ~ v1_funct_1(X0)
% 9.26/2.04      | ~ v1_funct_1(sK11)
% 9.26/2.04      | v1_xboole_0(sK10)
% 9.26/2.04      | k1_funct_1(k8_funct_2(sK9,sK10,X1,sK11,X0),X2) = k1_funct_1(X0,k1_funct_1(sK11,X2))
% 9.26/2.04      | k1_xboole_0 = sK9 ),
% 9.26/2.04      inference(instantiation,[status(thm)],[c_3396]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_3478,plain,
% 9.26/2.04      ( ~ v1_funct_2(sK11,sK9,sK10)
% 9.26/2.04      | ~ m1_subset_1(X0,sK9)
% 9.26/2.04      | ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,X1)))
% 9.26/2.04      | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
% 9.26/2.04      | ~ r1_tarski(k2_relset_1(sK9,sK10,sK11),k1_relset_1(sK10,X1,sK12))
% 9.26/2.04      | ~ v1_funct_1(sK12)
% 9.26/2.04      | ~ v1_funct_1(sK11)
% 9.26/2.04      | v1_xboole_0(sK10)
% 9.26/2.04      | k1_funct_1(k8_funct_2(sK9,sK10,X1,sK11,sK12),X0) = k1_funct_1(sK12,k1_funct_1(sK11,X0))
% 9.26/2.04      | k1_xboole_0 = sK9 ),
% 9.26/2.04      inference(instantiation,[status(thm)],[c_3445]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_3821,plain,
% 9.26/2.04      ( ~ v1_funct_2(sK11,sK9,sK10)
% 9.26/2.04      | ~ m1_subset_1(sK13,sK9)
% 9.26/2.04      | ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,X0)))
% 9.26/2.04      | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
% 9.26/2.04      | ~ r1_tarski(k2_relset_1(sK9,sK10,sK11),k1_relset_1(sK10,X0,sK12))
% 9.26/2.04      | ~ v1_funct_1(sK12)
% 9.26/2.04      | ~ v1_funct_1(sK11)
% 9.26/2.04      | v1_xboole_0(sK10)
% 9.26/2.04      | k1_funct_1(k8_funct_2(sK9,sK10,X0,sK11,sK12),sK13) = k1_funct_1(sK12,k1_funct_1(sK11,sK13))
% 9.26/2.04      | k1_xboole_0 = sK9 ),
% 9.26/2.04      inference(instantiation,[status(thm)],[c_3478]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_4238,plain,
% 9.26/2.04      ( ~ v1_funct_2(sK11,sK9,sK10)
% 9.26/2.04      | ~ m1_subset_1(sK13,sK9)
% 9.26/2.04      | ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK8)))
% 9.26/2.04      | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
% 9.26/2.04      | ~ r1_tarski(k2_relset_1(sK9,sK10,sK11),k1_relset_1(sK10,sK8,sK12))
% 9.26/2.04      | ~ v1_funct_1(sK12)
% 9.26/2.04      | ~ v1_funct_1(sK11)
% 9.26/2.04      | v1_xboole_0(sK10)
% 9.26/2.04      | k1_funct_1(k8_funct_2(sK9,sK10,sK8,sK11,sK12),sK13) = k1_funct_1(sK12,k1_funct_1(sK11,sK13))
% 9.26/2.04      | k1_xboole_0 = sK9 ),
% 9.26/2.04      inference(instantiation,[status(thm)],[c_3821]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_20,plain,
% 9.26/2.04      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 9.26/2.04      | r2_hidden(sK7(X1,X0),k1_relat_1(X1))
% 9.26/2.04      | ~ v1_relat_1(X1)
% 9.26/2.04      | ~ v1_funct_1(X1) ),
% 9.26/2.04      inference(cnf_transformation,[],[f116]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_3243,plain,
% 9.26/2.04      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 9.26/2.04      | r2_hidden(sK7(X1,X0),k1_relat_1(X1)) = iProver_top
% 9.26/2.04      | v1_relat_1(X1) != iProver_top
% 9.26/2.04      | v1_funct_1(X1) != iProver_top ),
% 9.26/2.04      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_6312,plain,
% 9.26/2.04      ( sK10 = k1_xboole_0
% 9.26/2.04      | r2_hidden(X0,k2_relat_1(sK11)) != iProver_top
% 9.26/2.04      | r2_hidden(sK7(sK11,X0),sK9) = iProver_top
% 9.26/2.04      | v1_relat_1(sK11) != iProver_top
% 9.26/2.04      | v1_funct_1(sK11) != iProver_top ),
% 9.26/2.04      inference(superposition,[status(thm)],[c_5442,c_3243]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_19706,plain,
% 9.26/2.04      ( r2_hidden(X0,k2_relat_1(sK11)) != iProver_top
% 9.26/2.04      | r2_hidden(sK7(sK11,X0),sK9) = iProver_top ),
% 9.26/2.04      inference(global_propositional_subsumption,
% 9.26/2.04                [status(thm)],
% 9.26/2.04                [c_6312,c_44,c_45,c_3345,c_4504,c_8560]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_1,plain,
% 9.26/2.04      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 9.26/2.04      inference(cnf_transformation,[],[f64]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_3262,plain,
% 9.26/2.04      ( r2_hidden(X0,X1) != iProver_top
% 9.26/2.04      | v1_xboole_0(X1) != iProver_top ),
% 9.26/2.04      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_19712,plain,
% 9.26/2.04      ( r2_hidden(X0,k2_relat_1(sK11)) != iProver_top
% 9.26/2.04      | v1_xboole_0(sK9) != iProver_top ),
% 9.26/2.04      inference(superposition,[status(thm)],[c_19706,c_3262]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_20064,plain,
% 9.26/2.04      ( v1_xboole_0(k2_relat_1(sK11)) = iProver_top
% 9.26/2.04      | v1_xboole_0(sK9) != iProver_top ),
% 9.26/2.04      inference(superposition,[status(thm)],[c_3263,c_19712]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_3230,plain,
% 9.26/2.04      ( m1_subset_1(sK13,sK9) = iProver_top ),
% 9.26/2.04      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_6,plain,
% 9.26/2.04      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 9.26/2.04      inference(cnf_transformation,[],[f70]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_3257,plain,
% 9.26/2.04      ( m1_subset_1(X0,X1) != iProver_top
% 9.26/2.04      | r2_hidden(X0,X1) = iProver_top
% 9.26/2.04      | v1_xboole_0(X1) = iProver_top ),
% 9.26/2.04      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_4919,plain,
% 9.26/2.04      ( r2_hidden(sK13,sK9) = iProver_top
% 9.26/2.04      | v1_xboole_0(sK9) = iProver_top ),
% 9.26/2.04      inference(superposition,[status(thm)],[c_3230,c_3257]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_22408,plain,
% 9.26/2.04      ( k7_partfun1(sK8,sK12,k1_funct_1(sK11,sK13)) = k1_funct_1(sK12,k1_funct_1(sK11,sK13))
% 9.26/2.04      | v1_xboole_0(sK9) = iProver_top ),
% 9.26/2.04      inference(superposition,[status(thm)],[c_4919,c_22393]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_6577,plain,
% 9.26/2.04      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 9.26/2.04      | v1_relat_1(X1) != iProver_top
% 9.26/2.04      | v1_funct_1(X1) != iProver_top
% 9.26/2.04      | v1_xboole_0(k2_relat_1(X1)) != iProver_top ),
% 9.26/2.04      inference(superposition,[status(thm)],[c_3245,c_3262]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_22493,plain,
% 9.26/2.04      ( sK10 = k1_xboole_0
% 9.26/2.04      | r2_hidden(X0,sK9) != iProver_top
% 9.26/2.04      | v1_relat_1(sK11) != iProver_top
% 9.26/2.04      | v1_funct_1(sK11) != iProver_top
% 9.26/2.04      | v1_xboole_0(k2_relat_1(sK11)) != iProver_top ),
% 9.26/2.04      inference(superposition,[status(thm)],[c_5442,c_6577]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_22690,plain,
% 9.26/2.04      ( r2_hidden(X0,sK9) != iProver_top ),
% 9.26/2.04      inference(global_propositional_subsumption,
% 9.26/2.04                [status(thm)],
% 9.26/2.04                [c_22601,c_43,c_44,c_42,c_45,c_41,c_40,c_39,c_38,c_37,
% 9.26/2.04                 c_36,c_35,c_34,c_3345,c_3368,c_4238,c_4504,c_8560,
% 9.26/2.04                 c_20064,c_22408,c_22493]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_22704,plain,
% 9.26/2.04      ( k2_relat_1(X0) = sK9
% 9.26/2.04      | r2_hidden(sK6(X0,sK9),k1_relat_1(X0)) = iProver_top
% 9.26/2.04      | v1_relat_1(X0) != iProver_top
% 9.26/2.04      | v1_funct_1(X0) != iProver_top ),
% 9.26/2.04      inference(superposition,[status(thm)],[c_3246,c_22690]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_20073,plain,
% 9.26/2.04      ( r2_hidden(X0,k1_relat_1(sK11)) != iProver_top
% 9.26/2.04      | v1_relat_1(sK11) != iProver_top
% 9.26/2.04      | v1_funct_1(sK11) != iProver_top
% 9.26/2.04      | v1_xboole_0(sK9) != iProver_top ),
% 9.26/2.04      inference(superposition,[status(thm)],[c_3245,c_19712]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_23958,plain,
% 9.26/2.04      ( r2_hidden(X0,k1_relat_1(sK11)) != iProver_top ),
% 9.26/2.04      inference(global_propositional_subsumption,
% 9.26/2.04                [status(thm)],
% 9.26/2.04                [c_20073,c_43,c_42,c_45,c_41,c_40,c_39,c_38,c_37,c_36,
% 9.26/2.04                 c_35,c_34,c_3368,c_4238,c_4504,c_22408]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_26369,plain,
% 9.26/2.04      ( k2_relat_1(sK11) = sK9
% 9.26/2.04      | v1_relat_1(sK11) != iProver_top
% 9.26/2.04      | v1_funct_1(sK11) != iProver_top ),
% 9.26/2.04      inference(superposition,[status(thm)],[c_22704,c_23958]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_8568,plain,
% 9.26/2.04      ( k2_relat_1(X0) = k1_xboole_0
% 9.26/2.04      | r2_hidden(sK6(X0,k1_xboole_0),k1_relat_1(X0)) = iProver_top
% 9.26/2.04      | v1_relat_1(X0) != iProver_top
% 9.26/2.04      | v1_funct_1(X0) != iProver_top ),
% 9.26/2.04      inference(superposition,[status(thm)],[c_3246,c_4151]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_20201,plain,
% 9.26/2.04      ( k2_relat_1(X0) = k1_xboole_0
% 9.26/2.04      | v1_relat_1(X0) != iProver_top
% 9.26/2.04      | v1_funct_1(X0) != iProver_top
% 9.26/2.04      | v1_xboole_0(k1_relat_1(X0)) != iProver_top ),
% 9.26/2.04      inference(superposition,[status(thm)],[c_8568,c_3262]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_21379,plain,
% 9.26/2.04      ( k2_relat_1(sK11) = k1_xboole_0
% 9.26/2.04      | sK10 = k1_xboole_0
% 9.26/2.04      | v1_relat_1(sK11) != iProver_top
% 9.26/2.04      | v1_funct_1(sK11) != iProver_top
% 9.26/2.04      | v1_xboole_0(sK9) != iProver_top ),
% 9.26/2.04      inference(superposition,[status(thm)],[c_5442,c_20201]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_23521,plain,
% 9.26/2.04      ( k2_relat_1(sK11) = k1_xboole_0 ),
% 9.26/2.04      inference(global_propositional_subsumption,
% 9.26/2.04                [status(thm)],
% 9.26/2.04                [c_21379,c_43,c_44,c_42,c_45,c_41,c_40,c_39,c_38,c_37,
% 9.26/2.04                 c_36,c_35,c_34,c_3345,c_3368,c_4238,c_4504,c_8560,
% 9.26/2.04                 c_22408]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_26377,plain,
% 9.26/2.04      ( sK9 = k1_xboole_0
% 9.26/2.04      | v1_relat_1(sK11) != iProver_top
% 9.26/2.04      | v1_funct_1(sK11) != iProver_top ),
% 9.26/2.04      inference(light_normalisation,[status(thm)],[c_26369,c_23521]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_3331,plain,
% 9.26/2.04      ( sK9 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK9 ),
% 9.26/2.04      inference(instantiation,[status(thm)],[c_2565]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_3332,plain,
% 9.26/2.04      ( sK9 != k1_xboole_0
% 9.26/2.04      | k1_xboole_0 = sK9
% 9.26/2.04      | k1_xboole_0 != k1_xboole_0 ),
% 9.26/2.04      inference(instantiation,[status(thm)],[c_3331]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_2564,plain,( X0 = X0 ),theory(equality) ).
% 9.26/2.04  
% 9.26/2.04  cnf(c_2593,plain,
% 9.26/2.04      ( k1_xboole_0 = k1_xboole_0 ),
% 9.26/2.04      inference(instantiation,[status(thm)],[c_2564]) ).
% 9.26/2.04  
% 9.26/2.04  cnf(contradiction,plain,
% 9.26/2.04      ( $false ),
% 9.26/2.04      inference(minisat,
% 9.26/2.04                [status(thm)],
% 9.26/2.04                [c_26377,c_4504,c_3332,c_2593,c_35,c_45]) ).
% 9.26/2.04  
% 9.26/2.04  
% 9.26/2.04  % SZS output end CNFRefutation for theBenchmark.p
% 9.26/2.04  
% 9.26/2.04  ------                               Statistics
% 9.26/2.04  
% 9.26/2.04  ------ General
% 9.26/2.04  
% 9.26/2.04  abstr_ref_over_cycles:                  0
% 9.26/2.04  abstr_ref_under_cycles:                 0
% 9.26/2.04  gc_basic_clause_elim:                   0
% 9.26/2.04  forced_gc_time:                         0
% 9.26/2.04  parsing_time:                           0.027
% 9.26/2.04  unif_index_cands_time:                  0.
% 9.26/2.04  unif_index_add_time:                    0.
% 9.26/2.04  orderings_time:                         0.
% 9.26/2.04  out_proof_time:                         0.016
% 9.26/2.04  total_time:                             1.285
% 9.26/2.04  num_of_symbols:                         64
% 9.26/2.04  num_of_terms:                           39705
% 9.26/2.04  
% 9.26/2.04  ------ Preprocessing
% 9.26/2.04  
% 9.26/2.04  num_of_splits:                          0
% 9.26/2.04  num_of_split_atoms:                     0
% 9.26/2.04  num_of_reused_defs:                     0
% 9.26/2.04  num_eq_ax_congr_red:                    71
% 9.26/2.04  num_of_sem_filtered_clauses:            1
% 9.26/2.04  num_of_subtypes:                        0
% 9.26/2.04  monotx_restored_types:                  0
% 9.26/2.04  sat_num_of_epr_types:                   0
% 9.26/2.04  sat_num_of_non_cyclic_types:            0
% 9.26/2.04  sat_guarded_non_collapsed_types:        0
% 9.26/2.04  num_pure_diseq_elim:                    0
% 9.26/2.04  simp_replaced_by:                       0
% 9.26/2.04  res_preprocessed:                       204
% 9.26/2.04  prep_upred:                             0
% 9.26/2.04  prep_unflattend:                        126
% 9.26/2.04  smt_new_axioms:                         0
% 9.26/2.04  pred_elim_cands:                        7
% 9.26/2.04  pred_elim:                              1
% 9.26/2.04  pred_elim_cl:                           1
% 9.26/2.04  pred_elim_cycles:                       9
% 9.26/2.04  merged_defs:                            0
% 9.26/2.04  merged_defs_ncl:                        0
% 9.26/2.04  bin_hyper_res:                          0
% 9.26/2.04  prep_cycles:                            4
% 9.26/2.04  pred_elim_time:                         0.039
% 9.26/2.04  splitting_time:                         0.
% 9.26/2.04  sem_filter_time:                        0.
% 9.26/2.04  monotx_time:                            0.
% 9.26/2.04  subtype_inf_time:                       0.
% 9.26/2.04  
% 9.26/2.04  ------ Problem properties
% 9.26/2.04  
% 9.26/2.04  clauses:                                43
% 9.26/2.04  conjectures:                            10
% 9.26/2.04  epr:                                    11
% 9.26/2.04  horn:                                   30
% 9.26/2.04  ground:                                 10
% 9.26/2.04  unary:                                  11
% 9.26/2.04  binary:                                 8
% 9.26/2.04  lits:                                   135
% 9.26/2.04  lits_eq:                                29
% 9.26/2.04  fd_pure:                                0
% 9.26/2.04  fd_pseudo:                              0
% 9.26/2.04  fd_cond:                                4
% 9.26/2.04  fd_pseudo_cond:                         7
% 9.26/2.04  ac_symbols:                             0
% 9.26/2.04  
% 9.26/2.04  ------ Propositional Solver
% 9.26/2.04  
% 9.26/2.04  prop_solver_calls:                      32
% 9.26/2.04  prop_fast_solver_calls:                 2917
% 9.26/2.04  smt_solver_calls:                       0
% 9.26/2.04  smt_fast_solver_calls:                  0
% 9.26/2.04  prop_num_of_clauses:                    13719
% 9.26/2.04  prop_preprocess_simplified:             19386
% 9.26/2.04  prop_fo_subsumed:                       140
% 9.26/2.04  prop_solver_time:                       0.
% 9.26/2.04  smt_solver_time:                        0.
% 9.26/2.04  smt_fast_solver_time:                   0.
% 9.26/2.04  prop_fast_solver_time:                  0.
% 9.26/2.04  prop_unsat_core_time:                   0.001
% 9.26/2.04  
% 9.26/2.04  ------ QBF
% 9.26/2.04  
% 9.26/2.04  qbf_q_res:                              0
% 9.26/2.04  qbf_num_tautologies:                    0
% 9.26/2.04  qbf_prep_cycles:                        0
% 9.26/2.04  
% 9.26/2.04  ------ BMC1
% 9.26/2.04  
% 9.26/2.04  bmc1_current_bound:                     -1
% 9.26/2.04  bmc1_last_solved_bound:                 -1
% 9.26/2.04  bmc1_unsat_core_size:                   -1
% 9.26/2.04  bmc1_unsat_core_parents_size:           -1
% 9.26/2.04  bmc1_merge_next_fun:                    0
% 9.26/2.04  bmc1_unsat_core_clauses_time:           0.
% 9.26/2.04  
% 9.26/2.04  ------ Instantiation
% 9.26/2.04  
% 9.26/2.04  inst_num_of_clauses:                    2708
% 9.26/2.04  inst_num_in_passive:                    243
% 9.26/2.04  inst_num_in_active:                     1359
% 9.26/2.04  inst_num_in_unprocessed:                1106
% 9.26/2.04  inst_num_of_loops:                      1470
% 9.26/2.04  inst_num_of_learning_restarts:          0
% 9.26/2.04  inst_num_moves_active_passive:          107
% 9.26/2.04  inst_lit_activity:                      0
% 9.26/2.04  inst_lit_activity_moves:                0
% 9.26/2.04  inst_num_tautologies:                   0
% 9.26/2.04  inst_num_prop_implied:                  0
% 9.26/2.04  inst_num_existing_simplified:           0
% 9.26/2.04  inst_num_eq_res_simplified:             0
% 9.26/2.04  inst_num_child_elim:                    0
% 9.26/2.04  inst_num_of_dismatching_blockings:      1062
% 9.26/2.04  inst_num_of_non_proper_insts:           2596
% 9.26/2.04  inst_num_of_duplicates:                 0
% 9.26/2.04  inst_inst_num_from_inst_to_res:         0
% 9.26/2.04  inst_dismatching_checking_time:         0.
% 9.26/2.04  
% 9.26/2.04  ------ Resolution
% 9.26/2.04  
% 9.26/2.04  res_num_of_clauses:                     0
% 9.26/2.04  res_num_in_passive:                     0
% 9.26/2.04  res_num_in_active:                      0
% 9.26/2.04  res_num_of_loops:                       208
% 9.26/2.04  res_forward_subset_subsumed:            160
% 9.26/2.04  res_backward_subset_subsumed:           0
% 9.26/2.04  res_forward_subsumed:                   0
% 9.26/2.04  res_backward_subsumed:                  0
% 9.26/2.04  res_forward_subsumption_resolution:     0
% 9.26/2.04  res_backward_subsumption_resolution:    0
% 9.26/2.04  res_clause_to_clause_subsumption:       3329
% 9.26/2.04  res_orphan_elimination:                 0
% 9.26/2.04  res_tautology_del:                      171
% 9.26/2.04  res_num_eq_res_simplified:              0
% 9.26/2.04  res_num_sel_changes:                    0
% 9.26/2.04  res_moves_from_active_to_pass:          0
% 9.26/2.04  
% 9.26/2.04  ------ Superposition
% 9.26/2.04  
% 9.26/2.04  sup_time_total:                         0.
% 9.26/2.04  sup_time_generating:                    0.
% 9.26/2.04  sup_time_sim_full:                      0.
% 9.26/2.04  sup_time_sim_immed:                     0.
% 9.26/2.04  
% 9.26/2.04  sup_num_of_clauses:                     1484
% 9.26/2.04  sup_num_in_active:                      184
% 9.26/2.04  sup_num_in_passive:                     1300
% 9.26/2.04  sup_num_of_loops:                       292
% 9.26/2.04  sup_fw_superposition:                   1211
% 9.26/2.04  sup_bw_superposition:                   579
% 9.26/2.04  sup_immediate_simplified:               122
% 9.26/2.04  sup_given_eliminated:                   0
% 9.26/2.04  comparisons_done:                       0
% 9.26/2.04  comparisons_avoided:                    297
% 9.26/2.04  
% 9.26/2.04  ------ Simplifications
% 9.26/2.04  
% 9.26/2.04  
% 9.26/2.04  sim_fw_subset_subsumed:                 63
% 9.26/2.04  sim_bw_subset_subsumed:                 56
% 9.26/2.04  sim_fw_subsumed:                        53
% 9.26/2.04  sim_bw_subsumed:                        61
% 9.26/2.04  sim_fw_subsumption_res:                 0
% 9.26/2.04  sim_bw_subsumption_res:                 0
% 9.26/2.04  sim_tautology_del:                      7
% 9.26/2.04  sim_eq_tautology_del:                   14
% 9.26/2.04  sim_eq_res_simp:                        0
% 9.26/2.04  sim_fw_demodulated:                     3
% 9.26/2.04  sim_bw_demodulated:                     39
% 9.26/2.04  sim_light_normalised:                   12
% 9.26/2.04  sim_joinable_taut:                      0
% 9.26/2.04  sim_joinable_simp:                      0
% 9.26/2.04  sim_ac_normalised:                      0
% 9.26/2.04  sim_smt_subsumption:                    0
% 9.26/2.04  
%------------------------------------------------------------------------------
