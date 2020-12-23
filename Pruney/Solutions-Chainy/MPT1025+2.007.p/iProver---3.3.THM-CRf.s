%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:01 EST 2020

% Result     : Theorem 3.87s
% Output     : CNFRefutation 3.87s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 446 expanded)
%              Number of clauses        :   70 ( 141 expanded)
%              Number of leaves         :   19 ( 103 expanded)
%              Depth                    :   20
%              Number of atoms          :  528 (2184 expanded)
%              Number of equality atoms :  223 ( 517 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2) ) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f33,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f34,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f33])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
     => ( ! [X5] :
            ( k1_funct_1(X3,X5) != sK8
            | ~ r2_hidden(X5,X2)
            | ~ m1_subset_1(X5,X0) )
        & r2_hidden(sK8,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK7,X5) != X4
              | ~ r2_hidden(X5,sK6)
              | ~ m1_subset_1(X5,sK4) )
          & r2_hidden(X4,k7_relset_1(sK4,sK5,sK7,sK6)) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK7,sK4,sK5)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ! [X5] :
        ( k1_funct_1(sK7,X5) != sK8
        | ~ r2_hidden(X5,sK6)
        | ~ m1_subset_1(X5,sK4) )
    & r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK7,sK4,sK5)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f34,f52,f51])).

fof(f88,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f53])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f89,plain,(
    r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(cnf_transformation,[],[f53])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK0(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
        & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
            & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f48])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f86,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f53])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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
    inference(flattening,[],[f22])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f46,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) = X2
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
              ( k1_funct_1(X0,X3) != sK1(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK1(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK1(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK1(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
                  & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK1(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK3(X0,X5)) = X5
                    & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f43,f46,f45,f44])).

fof(f68,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f93,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f94,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f93])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

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
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f87,plain,(
    v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f90,plain,(
    ! [X5] :
      ( k1_funct_1(sK7,X5) != sK8
      | ~ r2_hidden(X5,sK6)
      | ~ m1_subset_1(X5,sK4) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f35])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f91,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f56])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f92,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f55])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_879,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_888,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2400,plain,
    ( k7_relset_1(sK4,sK5,sK7,X0) = k9_relat_1(sK7,X0) ),
    inference(superposition,[status(thm)],[c_879,c_888])).

cnf(c_33,negated_conjecture,
    ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_880,plain,
    ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_2420,plain,
    ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2400,c_880])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_903,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_19,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_894,plain,
    ( k1_funct_1(X0,X1) = X2
    | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3098,plain,
    ( k1_funct_1(X0,sK0(X1,X2,X0)) = X1
    | r2_hidden(X1,k9_relat_1(X0,X2)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_903,c_894])).

cnf(c_8211,plain,
    ( k1_funct_1(sK7,sK0(sK8,sK6,sK7)) = sK8
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2420,c_3098])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_37,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_39,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1247,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1248,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1247])).

cnf(c_8966,plain,
    ( k1_funct_1(sK7,sK0(sK8,sK6,sK7)) = sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8211,c_37,c_39,c_1248])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_898,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_907,plain,
    ( r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | v5_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_21,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_892,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2631,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_907,c_892])).

cnf(c_4417,plain,
    ( v5_relat_1(X0,k1_funct_1(X0,X1)) != iProver_top
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_898,c_2631])).

cnf(c_8974,plain,
    ( v5_relat_1(sK7,sK8) != iProver_top
    | r2_hidden(sK0(sK8,sK6,sK7),k1_relat_1(sK7)) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_8966,c_4417])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_9611,plain,
    ( r2_hidden(sK0(sK8,sK6,sK7),k1_relat_1(sK7))
    | ~ r2_hidden(sK8,k9_relat_1(sK7,sK6))
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_9615,plain,
    ( r2_hidden(sK0(sK8,sK6,sK7),k1_relat_1(sK7)) = iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9611])).

cnf(c_10390,plain,
    ( v5_relat_1(sK7,sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8974,c_37,c_39,c_1248,c_2420,c_9615])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_882,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3527,plain,
    ( k1_relset_1(sK4,sK5,sK7) = sK4
    | sK5 = k1_xboole_0
    | v1_funct_2(sK7,sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_879,c_882])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_889,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1959,plain,
    ( k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_879,c_889])).

cnf(c_3548,plain,
    ( k1_relat_1(sK7) = sK4
    | sK5 = k1_xboole_0
    | v1_funct_2(sK7,sK4,sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3527,c_1959])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_38,plain,
    ( v1_funct_2(sK7,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_3627,plain,
    ( sK5 = k1_xboole_0
    | k1_relat_1(sK7) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3548,c_38])).

cnf(c_3628,plain,
    ( k1_relat_1(sK7) = sK4
    | sK5 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3627])).

cnf(c_902,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_910,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3045,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | m1_subset_1(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_902,c_910])).

cnf(c_3631,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | m1_subset_1(sK0(X0,X1,sK7),sK4) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3628,c_3045])).

cnf(c_3656,plain,
    ( m1_subset_1(sK0(X0,X1,sK7),sK4) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3631,c_39,c_1248])).

cnf(c_3657,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | m1_subset_1(sK0(X0,X1,sK7),sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_3656])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK0(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_904,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_32,negated_conjecture,
    ( ~ r2_hidden(X0,sK6)
    | ~ m1_subset_1(X0,sK4)
    | k1_funct_1(sK7,X0) != sK8 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_881,plain,
    ( k1_funct_1(sK7,X0) != sK8
    | r2_hidden(X0,sK6) != iProver_top
    | m1_subset_1(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_8973,plain,
    ( r2_hidden(sK0(sK8,sK6,sK7),sK6) != iProver_top
    | m1_subset_1(sK0(sK8,sK6,sK7),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8966,c_881])).

cnf(c_9044,plain,
    ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top
    | m1_subset_1(sK0(sK8,sK6,sK7),sK4) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_904,c_8973])).

cnf(c_9144,plain,
    ( m1_subset_1(sK0(sK8,sK6,sK7),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9044,c_39,c_1248,c_2420])).

cnf(c_9149,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3657,c_9144])).

cnf(c_9152,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9149,c_2420])).

cnf(c_9185,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9152,c_879])).

cnf(c_0,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_9190,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9185,c_0])).

cnf(c_1,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_23,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_890,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1363,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_890])).

cnf(c_9432,plain,
    ( v5_relat_1(sK7,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9190,c_1363])).

cnf(c_10395,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10390,c_9432])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:34:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.87/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.87/0.98  
% 3.87/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.87/0.98  
% 3.87/0.98  ------  iProver source info
% 3.87/0.98  
% 3.87/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.87/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.87/0.98  git: non_committed_changes: false
% 3.87/0.98  git: last_make_outside_of_git: false
% 3.87/0.98  
% 3.87/0.98  ------ 
% 3.87/0.98  ------ Parsing...
% 3.87/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.87/0.98  
% 3.87/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.87/0.98  
% 3.87/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.87/0.98  
% 3.87/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.87/0.98  ------ Proving...
% 3.87/0.98  ------ Problem Properties 
% 3.87/0.98  
% 3.87/0.98  
% 3.87/0.98  clauses                                 37
% 3.87/0.98  conjectures                             5
% 3.87/0.98  EPR                                     4
% 3.87/0.98  Horn                                    30
% 3.87/0.98  unary                                   7
% 3.87/0.98  binary                                  6
% 3.87/0.98  lits                                    109
% 3.87/0.98  lits eq                                 24
% 3.87/0.98  fd_pure                                 0
% 3.87/0.98  fd_pseudo                               0
% 3.87/0.98  fd_cond                                 4
% 3.87/0.98  fd_pseudo_cond                          4
% 3.87/0.98  AC symbols                              0
% 3.87/0.98  
% 3.87/0.98  ------ Input Options Time Limit: Unbounded
% 3.87/0.98  
% 3.87/0.98  
% 3.87/0.98  ------ 
% 3.87/0.98  Current options:
% 3.87/0.98  ------ 
% 3.87/0.98  
% 3.87/0.98  
% 3.87/0.98  
% 3.87/0.98  
% 3.87/0.98  ------ Proving...
% 3.87/0.98  
% 3.87/0.98  
% 3.87/0.98  % SZS status Theorem for theBenchmark.p
% 3.87/0.98  
% 3.87/0.98   Resolution empty clause
% 3.87/0.98  
% 3.87/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.87/0.98  
% 3.87/0.98  fof(f15,conjecture,(
% 3.87/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.87/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f16,negated_conjecture,(
% 3.87/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.87/0.98    inference(negated_conjecture,[],[f15])).
% 3.87/0.98  
% 3.87/0.98  fof(f33,plain,(
% 3.87/0.98    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.87/0.98    inference(ennf_transformation,[],[f16])).
% 3.87/0.98  
% 3.87/0.98  fof(f34,plain,(
% 3.87/0.98    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.87/0.98    inference(flattening,[],[f33])).
% 3.87/0.98  
% 3.87/0.98  fof(f52,plain,(
% 3.87/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK8 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(sK8,k7_relset_1(X0,X1,X3,X2)))) )),
% 3.87/0.98    introduced(choice_axiom,[])).
% 3.87/0.98  
% 3.87/0.98  fof(f51,plain,(
% 3.87/0.98    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK7,X5) != X4 | ~r2_hidden(X5,sK6) | ~m1_subset_1(X5,sK4)) & r2_hidden(X4,k7_relset_1(sK4,sK5,sK7,sK6))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7))),
% 3.87/0.98    introduced(choice_axiom,[])).
% 3.87/0.98  
% 3.87/0.98  fof(f53,plain,(
% 3.87/0.98    (! [X5] : (k1_funct_1(sK7,X5) != sK8 | ~r2_hidden(X5,sK6) | ~m1_subset_1(X5,sK4)) & r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7)),
% 3.87/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f34,f52,f51])).
% 3.87/0.98  
% 3.87/0.98  fof(f88,plain,(
% 3.87/0.98    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 3.87/0.98    inference(cnf_transformation,[],[f53])).
% 3.87/0.98  
% 3.87/0.98  fof(f13,axiom,(
% 3.87/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.87/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f30,plain,(
% 3.87/0.98    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.87/0.98    inference(ennf_transformation,[],[f13])).
% 3.87/0.98  
% 3.87/0.98  fof(f79,plain,(
% 3.87/0.98    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.87/0.98    inference(cnf_transformation,[],[f30])).
% 3.87/0.98  
% 3.87/0.98  fof(f89,plain,(
% 3.87/0.98    r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))),
% 3.87/0.98    inference(cnf_transformation,[],[f53])).
% 3.87/0.98  
% 3.87/0.98  fof(f6,axiom,(
% 3.87/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 3.87/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f21,plain,(
% 3.87/0.98    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.87/0.98    inference(ennf_transformation,[],[f6])).
% 3.87/0.98  
% 3.87/0.98  fof(f38,plain,(
% 3.87/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.87/0.98    inference(nnf_transformation,[],[f21])).
% 3.87/0.98  
% 3.87/0.98  fof(f39,plain,(
% 3.87/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.87/0.98    inference(rectify,[],[f38])).
% 3.87/0.98  
% 3.87/0.98  fof(f40,plain,(
% 3.87/0.98    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))))),
% 3.87/0.98    introduced(choice_axiom,[])).
% 3.87/0.98  
% 3.87/0.98  fof(f41,plain,(
% 3.87/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.87/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).
% 3.87/0.98  
% 3.87/0.98  fof(f63,plain,(
% 3.87/0.98    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.87/0.98    inference(cnf_transformation,[],[f41])).
% 3.87/0.98  
% 3.87/0.98  fof(f8,axiom,(
% 3.87/0.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.87/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f24,plain,(
% 3.87/0.98    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.87/0.98    inference(ennf_transformation,[],[f8])).
% 3.87/0.98  
% 3.87/0.98  fof(f25,plain,(
% 3.87/0.98    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.87/0.98    inference(flattening,[],[f24])).
% 3.87/0.98  
% 3.87/0.98  fof(f48,plain,(
% 3.87/0.98    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.87/0.98    inference(nnf_transformation,[],[f25])).
% 3.87/0.98  
% 3.87/0.98  fof(f49,plain,(
% 3.87/0.98    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.87/0.98    inference(flattening,[],[f48])).
% 3.87/0.98  
% 3.87/0.98  fof(f73,plain,(
% 3.87/0.98    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.87/0.98    inference(cnf_transformation,[],[f49])).
% 3.87/0.98  
% 3.87/0.98  fof(f86,plain,(
% 3.87/0.98    v1_funct_1(sK7)),
% 3.87/0.98    inference(cnf_transformation,[],[f53])).
% 3.87/0.98  
% 3.87/0.98  fof(f10,axiom,(
% 3.87/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.87/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f27,plain,(
% 3.87/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.87/0.98    inference(ennf_transformation,[],[f10])).
% 3.87/0.98  
% 3.87/0.98  fof(f76,plain,(
% 3.87/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.87/0.98    inference(cnf_transformation,[],[f27])).
% 3.87/0.98  
% 3.87/0.98  fof(f7,axiom,(
% 3.87/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.87/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f22,plain,(
% 3.87/0.98    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.87/0.98    inference(ennf_transformation,[],[f7])).
% 3.87/0.98  
% 3.87/0.98  fof(f23,plain,(
% 3.87/0.98    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.87/0.98    inference(flattening,[],[f22])).
% 3.87/0.98  
% 3.87/0.98  fof(f42,plain,(
% 3.87/0.98    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.87/0.98    inference(nnf_transformation,[],[f23])).
% 3.87/0.98  
% 3.87/0.98  fof(f43,plain,(
% 3.87/0.98    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.87/0.98    inference(rectify,[],[f42])).
% 3.87/0.98  
% 3.87/0.98  fof(f46,plain,(
% 3.87/0.98    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))))),
% 3.87/0.98    introduced(choice_axiom,[])).
% 3.87/0.98  
% 3.87/0.98  fof(f45,plain,(
% 3.87/0.98    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) = X2 & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))) )),
% 3.87/0.98    introduced(choice_axiom,[])).
% 3.87/0.98  
% 3.87/0.98  fof(f44,plain,(
% 3.87/0.98    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1))))),
% 3.87/0.98    introduced(choice_axiom,[])).
% 3.87/0.98  
% 3.87/0.98  fof(f47,plain,(
% 3.87/0.98    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & ((k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.87/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f43,f46,f45,f44])).
% 3.87/0.98  
% 3.87/0.98  fof(f68,plain,(
% 3.87/0.98    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.87/0.98    inference(cnf_transformation,[],[f47])).
% 3.87/0.98  
% 3.87/0.98  fof(f93,plain,(
% 3.87/0.98    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.87/0.98    inference(equality_resolution,[],[f68])).
% 3.87/0.98  
% 3.87/0.98  fof(f94,plain,(
% 3.87/0.98    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.87/0.98    inference(equality_resolution,[],[f93])).
% 3.87/0.98  
% 3.87/0.98  fof(f4,axiom,(
% 3.87/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.87/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f20,plain,(
% 3.87/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.87/0.98    inference(ennf_transformation,[],[f4])).
% 3.87/0.98  
% 3.87/0.98  fof(f37,plain,(
% 3.87/0.98    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.87/0.98    inference(nnf_transformation,[],[f20])).
% 3.87/0.98  
% 3.87/0.98  fof(f59,plain,(
% 3.87/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.87/0.98    inference(cnf_transformation,[],[f37])).
% 3.87/0.98  
% 3.87/0.98  fof(f9,axiom,(
% 3.87/0.98    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.87/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f26,plain,(
% 3.87/0.98    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.87/0.98    inference(ennf_transformation,[],[f9])).
% 3.87/0.98  
% 3.87/0.98  fof(f75,plain,(
% 3.87/0.98    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.87/0.98    inference(cnf_transformation,[],[f26])).
% 3.87/0.98  
% 3.87/0.98  fof(f62,plain,(
% 3.87/0.98    ( ! [X2,X0,X1] : (r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.87/0.98    inference(cnf_transformation,[],[f41])).
% 3.87/0.98  
% 3.87/0.98  fof(f14,axiom,(
% 3.87/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.87/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f31,plain,(
% 3.87/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.87/0.98    inference(ennf_transformation,[],[f14])).
% 3.87/0.98  
% 3.87/0.98  fof(f32,plain,(
% 3.87/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.87/0.98    inference(flattening,[],[f31])).
% 3.87/0.98  
% 3.87/0.98  fof(f50,plain,(
% 3.87/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.87/0.98    inference(nnf_transformation,[],[f32])).
% 3.87/0.98  
% 3.87/0.98  fof(f80,plain,(
% 3.87/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.87/0.98    inference(cnf_transformation,[],[f50])).
% 3.87/0.98  
% 3.87/0.98  fof(f12,axiom,(
% 3.87/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.87/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f29,plain,(
% 3.87/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.87/0.98    inference(ennf_transformation,[],[f12])).
% 3.87/0.98  
% 3.87/0.98  fof(f78,plain,(
% 3.87/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.87/0.98    inference(cnf_transformation,[],[f29])).
% 3.87/0.98  
% 3.87/0.98  fof(f87,plain,(
% 3.87/0.98    v1_funct_2(sK7,sK4,sK5)),
% 3.87/0.98    inference(cnf_transformation,[],[f53])).
% 3.87/0.98  
% 3.87/0.98  fof(f2,axiom,(
% 3.87/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.87/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f18,plain,(
% 3.87/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.87/0.98    inference(ennf_transformation,[],[f2])).
% 3.87/0.98  
% 3.87/0.98  fof(f57,plain,(
% 3.87/0.98    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.87/0.98    inference(cnf_transformation,[],[f18])).
% 3.87/0.98  
% 3.87/0.98  fof(f64,plain,(
% 3.87/0.98    ( ! [X2,X0,X1] : (r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.87/0.98    inference(cnf_transformation,[],[f41])).
% 3.87/0.98  
% 3.87/0.98  fof(f90,plain,(
% 3.87/0.98    ( ! [X5] : (k1_funct_1(sK7,X5) != sK8 | ~r2_hidden(X5,sK6) | ~m1_subset_1(X5,sK4)) )),
% 3.87/0.98    inference(cnf_transformation,[],[f53])).
% 3.87/0.98  
% 3.87/0.98  fof(f1,axiom,(
% 3.87/0.98    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.87/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f35,plain,(
% 3.87/0.98    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.87/0.98    inference(nnf_transformation,[],[f1])).
% 3.87/0.98  
% 3.87/0.98  fof(f36,plain,(
% 3.87/0.98    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.87/0.98    inference(flattening,[],[f35])).
% 3.87/0.98  
% 3.87/0.98  fof(f56,plain,(
% 3.87/0.98    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 3.87/0.98    inference(cnf_transformation,[],[f36])).
% 3.87/0.98  
% 3.87/0.98  fof(f91,plain,(
% 3.87/0.98    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.87/0.98    inference(equality_resolution,[],[f56])).
% 3.87/0.98  
% 3.87/0.98  fof(f55,plain,(
% 3.87/0.98    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 3.87/0.98    inference(cnf_transformation,[],[f36])).
% 3.87/0.98  
% 3.87/0.98  fof(f92,plain,(
% 3.87/0.98    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 3.87/0.98    inference(equality_resolution,[],[f55])).
% 3.87/0.98  
% 3.87/0.98  fof(f11,axiom,(
% 3.87/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.87/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f17,plain,(
% 3.87/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.87/0.98    inference(pure_predicate_removal,[],[f11])).
% 3.87/0.98  
% 3.87/0.98  fof(f28,plain,(
% 3.87/0.98    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.87/0.98    inference(ennf_transformation,[],[f17])).
% 3.87/0.98  
% 3.87/0.98  fof(f77,plain,(
% 3.87/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.87/0.98    inference(cnf_transformation,[],[f28])).
% 3.87/0.98  
% 3.87/0.98  cnf(c_34,negated_conjecture,
% 3.87/0.98      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 3.87/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_879,plain,
% 3.87/0.98      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.87/0.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_25,plain,
% 3.87/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.87/0.98      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.87/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_888,plain,
% 3.87/0.98      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.87/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.87/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_2400,plain,
% 3.87/0.98      ( k7_relset_1(sK4,sK5,sK7,X0) = k9_relat_1(sK7,X0) ),
% 3.87/0.98      inference(superposition,[status(thm)],[c_879,c_888]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_33,negated_conjecture,
% 3.87/0.98      ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
% 3.87/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_880,plain,
% 3.87/0.98      ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
% 3.87/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_2420,plain,
% 3.87/0.98      ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) = iProver_top ),
% 3.87/0.98      inference(demodulation,[status(thm)],[c_2400,c_880]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_10,plain,
% 3.87/0.98      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.87/0.98      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
% 3.87/0.98      | ~ v1_relat_1(X1) ),
% 3.87/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_903,plain,
% 3.87/0.98      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.87/0.98      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
% 3.87/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.87/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_19,plain,
% 3.87/0.98      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.87/0.98      | ~ v1_funct_1(X2)
% 3.87/0.98      | ~ v1_relat_1(X2)
% 3.87/0.98      | k1_funct_1(X2,X0) = X1 ),
% 3.87/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_894,plain,
% 3.87/0.98      ( k1_funct_1(X0,X1) = X2
% 3.87/0.98      | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
% 3.87/0.98      | v1_funct_1(X0) != iProver_top
% 3.87/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.87/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_3098,plain,
% 3.87/0.98      ( k1_funct_1(X0,sK0(X1,X2,X0)) = X1
% 3.87/0.98      | r2_hidden(X1,k9_relat_1(X0,X2)) != iProver_top
% 3.87/0.98      | v1_funct_1(X0) != iProver_top
% 3.87/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.87/0.98      inference(superposition,[status(thm)],[c_903,c_894]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_8211,plain,
% 3.87/0.98      ( k1_funct_1(sK7,sK0(sK8,sK6,sK7)) = sK8
% 3.87/0.98      | v1_funct_1(sK7) != iProver_top
% 3.87/0.98      | v1_relat_1(sK7) != iProver_top ),
% 3.87/0.98      inference(superposition,[status(thm)],[c_2420,c_3098]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_36,negated_conjecture,
% 3.87/0.98      ( v1_funct_1(sK7) ),
% 3.87/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_37,plain,
% 3.87/0.98      ( v1_funct_1(sK7) = iProver_top ),
% 3.87/0.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_39,plain,
% 3.87/0.98      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.87/0.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_22,plain,
% 3.87/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.87/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_1247,plain,
% 3.87/0.98      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.87/0.98      | v1_relat_1(sK7) ),
% 3.87/0.98      inference(instantiation,[status(thm)],[c_22]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_1248,plain,
% 3.87/0.98      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 3.87/0.98      | v1_relat_1(sK7) = iProver_top ),
% 3.87/0.98      inference(predicate_to_equality,[status(thm)],[c_1247]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_8966,plain,
% 3.87/0.98      ( k1_funct_1(sK7,sK0(sK8,sK6,sK7)) = sK8 ),
% 3.87/0.98      inference(global_propositional_subsumption,
% 3.87/0.98                [status(thm)],
% 3.87/0.98                [c_8211,c_37,c_39,c_1248]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_15,plain,
% 3.87/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.87/0.98      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.87/0.98      | ~ v1_funct_1(X1)
% 3.87/0.98      | ~ v1_relat_1(X1) ),
% 3.87/0.98      inference(cnf_transformation,[],[f94]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_898,plain,
% 3.87/0.98      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 3.87/0.98      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 3.87/0.98      | v1_funct_1(X1) != iProver_top
% 3.87/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.87/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_6,plain,
% 3.87/0.98      ( r1_tarski(k2_relat_1(X0),X1) | ~ v5_relat_1(X0,X1) | ~ v1_relat_1(X0) ),
% 3.87/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_907,plain,
% 3.87/0.98      ( r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 3.87/0.98      | v5_relat_1(X0,X1) != iProver_top
% 3.87/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.87/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_21,plain,
% 3.87/0.98      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.87/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_892,plain,
% 3.87/0.98      ( r1_tarski(X0,X1) != iProver_top | r2_hidden(X1,X0) != iProver_top ),
% 3.87/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_2631,plain,
% 3.87/0.98      ( v5_relat_1(X0,X1) != iProver_top
% 3.87/0.98      | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
% 3.87/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.87/0.98      inference(superposition,[status(thm)],[c_907,c_892]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_4417,plain,
% 3.87/0.98      ( v5_relat_1(X0,k1_funct_1(X0,X1)) != iProver_top
% 3.87/0.98      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 3.87/0.98      | v1_funct_1(X0) != iProver_top
% 3.87/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.87/0.98      inference(superposition,[status(thm)],[c_898,c_2631]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_8974,plain,
% 3.87/0.98      ( v5_relat_1(sK7,sK8) != iProver_top
% 3.87/0.98      | r2_hidden(sK0(sK8,sK6,sK7),k1_relat_1(sK7)) != iProver_top
% 3.87/0.98      | v1_funct_1(sK7) != iProver_top
% 3.87/0.98      | v1_relat_1(sK7) != iProver_top ),
% 3.87/0.98      inference(superposition,[status(thm)],[c_8966,c_4417]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_11,plain,
% 3.87/0.98      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.87/0.98      | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1))
% 3.87/0.98      | ~ v1_relat_1(X1) ),
% 3.87/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_9611,plain,
% 3.87/0.98      ( r2_hidden(sK0(sK8,sK6,sK7),k1_relat_1(sK7))
% 3.87/0.98      | ~ r2_hidden(sK8,k9_relat_1(sK7,sK6))
% 3.87/0.98      | ~ v1_relat_1(sK7) ),
% 3.87/0.98      inference(instantiation,[status(thm)],[c_11]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_9615,plain,
% 3.87/0.98      ( r2_hidden(sK0(sK8,sK6,sK7),k1_relat_1(sK7)) = iProver_top
% 3.87/0.98      | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top
% 3.87/0.98      | v1_relat_1(sK7) != iProver_top ),
% 3.87/0.98      inference(predicate_to_equality,[status(thm)],[c_9611]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_10390,plain,
% 3.87/0.98      ( v5_relat_1(sK7,sK8) != iProver_top ),
% 3.87/0.98      inference(global_propositional_subsumption,
% 3.87/0.98                [status(thm)],
% 3.87/0.98                [c_8974,c_37,c_39,c_1248,c_2420,c_9615]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_31,plain,
% 3.87/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.87/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.87/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.87/0.98      | k1_xboole_0 = X2 ),
% 3.87/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_882,plain,
% 3.87/0.98      ( k1_relset_1(X0,X1,X2) = X0
% 3.87/0.98      | k1_xboole_0 = X1
% 3.87/0.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.87/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.87/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_3527,plain,
% 3.87/0.98      ( k1_relset_1(sK4,sK5,sK7) = sK4
% 3.87/0.98      | sK5 = k1_xboole_0
% 3.87/0.98      | v1_funct_2(sK7,sK4,sK5) != iProver_top ),
% 3.87/0.98      inference(superposition,[status(thm)],[c_879,c_882]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_24,plain,
% 3.87/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.87/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.87/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_889,plain,
% 3.87/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.87/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.87/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_1959,plain,
% 3.87/0.98      ( k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7) ),
% 3.87/0.98      inference(superposition,[status(thm)],[c_879,c_889]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_3548,plain,
% 3.87/0.98      ( k1_relat_1(sK7) = sK4
% 3.87/0.98      | sK5 = k1_xboole_0
% 3.87/0.98      | v1_funct_2(sK7,sK4,sK5) != iProver_top ),
% 3.87/0.98      inference(demodulation,[status(thm)],[c_3527,c_1959]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_35,negated_conjecture,
% 3.87/0.98      ( v1_funct_2(sK7,sK4,sK5) ),
% 3.87/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_38,plain,
% 3.87/0.98      ( v1_funct_2(sK7,sK4,sK5) = iProver_top ),
% 3.87/0.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_3627,plain,
% 3.87/0.98      ( sK5 = k1_xboole_0 | k1_relat_1(sK7) = sK4 ),
% 3.87/0.98      inference(global_propositional_subsumption,[status(thm)],[c_3548,c_38]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_3628,plain,
% 3.87/0.98      ( k1_relat_1(sK7) = sK4 | sK5 = k1_xboole_0 ),
% 3.87/0.98      inference(renaming,[status(thm)],[c_3627]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_902,plain,
% 3.87/0.98      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.87/0.98      | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 3.87/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.87/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_3,plain,
% 3.87/0.98      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 3.87/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_910,plain,
% 3.87/0.98      ( r2_hidden(X0,X1) != iProver_top | m1_subset_1(X0,X1) = iProver_top ),
% 3.87/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_3045,plain,
% 3.87/0.98      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.87/0.98      | m1_subset_1(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 3.87/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.87/0.98      inference(superposition,[status(thm)],[c_902,c_910]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_3631,plain,
% 3.87/0.98      ( sK5 = k1_xboole_0
% 3.87/0.98      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.87/0.98      | m1_subset_1(sK0(X0,X1,sK7),sK4) = iProver_top
% 3.87/0.98      | v1_relat_1(sK7) != iProver_top ),
% 3.87/0.98      inference(superposition,[status(thm)],[c_3628,c_3045]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_3656,plain,
% 3.87/0.98      ( m1_subset_1(sK0(X0,X1,sK7),sK4) = iProver_top
% 3.87/0.98      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.87/0.98      | sK5 = k1_xboole_0 ),
% 3.87/0.98      inference(global_propositional_subsumption,
% 3.87/0.98                [status(thm)],
% 3.87/0.98                [c_3631,c_39,c_1248]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_3657,plain,
% 3.87/0.98      ( sK5 = k1_xboole_0
% 3.87/0.98      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.87/0.98      | m1_subset_1(sK0(X0,X1,sK7),sK4) = iProver_top ),
% 3.87/0.98      inference(renaming,[status(thm)],[c_3656]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_9,plain,
% 3.87/0.98      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.87/0.98      | r2_hidden(sK0(X0,X2,X1),X2)
% 3.87/0.98      | ~ v1_relat_1(X1) ),
% 3.87/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_904,plain,
% 3.87/0.98      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.87/0.98      | r2_hidden(sK0(X0,X2,X1),X2) = iProver_top
% 3.87/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.87/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_32,negated_conjecture,
% 3.87/0.98      ( ~ r2_hidden(X0,sK6)
% 3.87/0.98      | ~ m1_subset_1(X0,sK4)
% 3.87/0.98      | k1_funct_1(sK7,X0) != sK8 ),
% 3.87/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_881,plain,
% 3.87/0.98      ( k1_funct_1(sK7,X0) != sK8
% 3.87/0.98      | r2_hidden(X0,sK6) != iProver_top
% 3.87/0.98      | m1_subset_1(X0,sK4) != iProver_top ),
% 3.87/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_8973,plain,
% 3.87/0.98      ( r2_hidden(sK0(sK8,sK6,sK7),sK6) != iProver_top
% 3.87/0.98      | m1_subset_1(sK0(sK8,sK6,sK7),sK4) != iProver_top ),
% 3.87/0.98      inference(superposition,[status(thm)],[c_8966,c_881]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_9044,plain,
% 3.87/0.98      ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top
% 3.87/0.98      | m1_subset_1(sK0(sK8,sK6,sK7),sK4) != iProver_top
% 3.87/0.98      | v1_relat_1(sK7) != iProver_top ),
% 3.87/0.98      inference(superposition,[status(thm)],[c_904,c_8973]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_9144,plain,
% 3.87/0.98      ( m1_subset_1(sK0(sK8,sK6,sK7),sK4) != iProver_top ),
% 3.87/0.98      inference(global_propositional_subsumption,
% 3.87/0.98                [status(thm)],
% 3.87/0.98                [c_9044,c_39,c_1248,c_2420]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_9149,plain,
% 3.87/0.98      ( sK5 = k1_xboole_0 | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top ),
% 3.87/0.98      inference(superposition,[status(thm)],[c_3657,c_9144]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_9152,plain,
% 3.87/0.98      ( sK5 = k1_xboole_0 ),
% 3.87/0.98      inference(global_propositional_subsumption,[status(thm)],[c_9149,c_2420]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_9185,plain,
% 3.87/0.98      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) = iProver_top ),
% 3.87/0.98      inference(demodulation,[status(thm)],[c_9152,c_879]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_0,plain,
% 3.87/0.98      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.87/0.98      inference(cnf_transformation,[],[f91]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_9190,plain,
% 3.87/0.98      ( m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.87/0.98      inference(demodulation,[status(thm)],[c_9185,c_0]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_1,plain,
% 3.87/0.98      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.87/0.98      inference(cnf_transformation,[],[f92]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_23,plain,
% 3.87/0.98      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.87/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_890,plain,
% 3.87/0.98      ( v5_relat_1(X0,X1) = iProver_top
% 3.87/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 3.87/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_1363,plain,
% 3.87/0.98      ( v5_relat_1(X0,X1) = iProver_top
% 3.87/0.98      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.87/0.98      inference(superposition,[status(thm)],[c_1,c_890]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_9432,plain,
% 3.87/0.98      ( v5_relat_1(sK7,X0) = iProver_top ),
% 3.87/0.98      inference(superposition,[status(thm)],[c_9190,c_1363]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_10395,plain,
% 3.87/0.98      ( $false ),
% 3.87/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_10390,c_9432]) ).
% 3.87/0.98  
% 3.87/0.98  
% 3.87/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.87/0.98  
% 3.87/0.98  ------                               Statistics
% 3.87/0.98  
% 3.87/0.98  ------ Selected
% 3.87/0.98  
% 3.87/0.98  total_time:                             0.301
% 3.87/0.98  
%------------------------------------------------------------------------------
