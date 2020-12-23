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
% DateTime   : Thu Dec  3 12:07:55 EST 2020

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :  172 (1058 expanded)
%              Number of clauses        :  107 ( 387 expanded)
%              Number of leaves         :   22 ( 251 expanded)
%              Depth                    :   27
%              Number of atoms          :  607 (5183 expanded)
%              Number of equality atoms :  218 (1142 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( k1_funct_1(X0,X5) = X3
                      & r2_hidden(X5,X1)
                      & r2_hidden(X5,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ? [X8] :
                      ( k1_funct_1(X0,X8) = X6
                      & r2_hidden(X8,X1)
                      & r2_hidden(X8,k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f43])).

fof(f47,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
        & r2_hidden(sK3(X0,X1,X6),X1)
        & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1,X2)) = X3
        & r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != X3
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( k1_funct_1(X0,X5) = X3
                & r2_hidden(X5,X1)
                & r2_hidden(X5,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( k1_funct_1(X0,X4) != sK1(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK1(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK1(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK1(X0,X1,X2),X2) )
              & ( ( k1_funct_1(X0,sK2(X0,X1,X2)) = sK1(X0,X1,X2)
                  & r2_hidden(sK2(X0,X1,X2),X1)
                  & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
                    & r2_hidden(sK3(X0,X1,X6),X1)
                    & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f44,f47,f46,f45])).

fof(f68,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f95,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ~ ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f34,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f35,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f34])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
     => ( ! [X5] :
            ( k1_funct_1(X3,X5) != sK8
            | ~ r2_hidden(X5,X2)
            | ~ r2_hidden(X5,X0) )
        & r2_hidden(sK8,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK7,X5) != X4
              | ~ r2_hidden(X5,sK6)
              | ~ r2_hidden(X5,sK4) )
          & r2_hidden(X4,k7_relset_1(sK4,sK5,sK7,sK6)) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK7,sK4,sK5)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ! [X5] :
        ( k1_funct_1(sK7,X5) != sK8
        | ~ r2_hidden(X5,sK6)
        | ~ r2_hidden(X5,sK4) )
    & r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK7,sK4,sK5)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f35,f51,f50])).

fof(f85,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f52])).

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
    inference(ennf_transformation,[],[f15])).

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
    inference(flattening,[],[f32])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f86,plain,(
    v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f87,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f52])).

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

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f88,plain,(
    r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(cnf_transformation,[],[f52])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f42])).

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

fof(f36,plain,(
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

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f67,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f96,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f67])).

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

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f70,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | k1_funct_1(X0,X7) != X6
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f92,plain,(
    ! [X2,X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f93,plain,(
    ! [X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f69,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f94,plain,(
    ! [X6,X0,X1] :
      ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f89,plain,(
    ! [X5] :
      ( k1_funct_1(sK7,X5) != sK8
      | ~ r2_hidden(X5,sK6)
      | ~ r2_hidden(X5,sK4) ) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_513,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),X2)
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_36])).

cnf(c_514,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
    | r2_hidden(sK3(sK7,X1,X0),X1)
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_513])).

cnf(c_1737,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(sK7,X1,X0),X1) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_514])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_723,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X2
    | sK4 != X1
    | sK7 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_35])).

cnf(c_724,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | k1_relset_1(sK4,sK5,sK7) = sK4
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_723])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_726,plain,
    ( k1_relset_1(sK4,sK5,sK7) = sK4
    | k1_xboole_0 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_724,c_34])).

cnf(c_1740,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1744,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3691,plain,
    ( k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_1740,c_1744])).

cnf(c_4008,plain,
    ( k1_relat_1(sK7) = sK4
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_726,c_3691])).

cnf(c_33,negated_conjecture,
    ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_7,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_115,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2039,plain,
    ( m1_subset_1(k7_relset_1(sK4,sK5,sK7,X0),k1_zfmisc_1(sK5))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_2133,plain,
    ( m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(instantiation,[status(thm)],[c_2039])).

cnf(c_1033,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_2216,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | r1_tarski(sK5,k1_xboole_0)
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_1033])).

cnf(c_2218,plain,
    ( r1_tarski(sK5,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2216])).

cnf(c_2346,plain,
    ( r1_tarski(k1_xboole_0,sK8) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_22,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2393,plain,
    ( ~ r1_tarski(X0,sK8)
    | ~ r2_hidden(sK8,X0) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2395,plain,
    ( ~ r1_tarski(k1_xboole_0,sK8)
    | ~ r2_hidden(sK8,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2393])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2108,plain,
    ( ~ m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(X0))
    | r1_tarski(k7_relset_1(sK4,sK5,sK7,sK6),X0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2945,plain,
    ( ~ m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5))
    | r1_tarski(k7_relset_1(sK4,sK5,sK7,sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_2108])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2390,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(sK8,X0)
    | r2_hidden(sK8,X1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3157,plain,
    ( ~ r1_tarski(sK5,X0)
    | r2_hidden(sK8,X0)
    | ~ r2_hidden(sK8,sK5) ),
    inference(instantiation,[status(thm)],[c_2390])).

cnf(c_3162,plain,
    ( ~ r1_tarski(sK5,k1_xboole_0)
    | ~ r2_hidden(sK8,sK5)
    | r2_hidden(sK8,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3157])).

cnf(c_2004,plain,
    ( ~ r1_tarski(k7_relset_1(sK4,sK5,sK7,sK6),X0)
    | r2_hidden(sK8,X0)
    | ~ r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3464,plain,
    ( ~ r1_tarski(k7_relset_1(sK4,sK5,sK7,sK6),sK5)
    | ~ r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))
    | r2_hidden(sK8,sK5) ),
    inference(instantiation,[status(thm)],[c_2004])).

cnf(c_4072,plain,
    ( k1_relat_1(sK7) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4008,c_34,c_33,c_115,c_2133,c_2218,c_2346,c_2395,c_2945,c_3162,c_3464])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_498,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_36])).

cnf(c_499,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
    | r2_hidden(sK3(sK7,X1,X0),k1_relat_1(sK7))
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_498])).

cnf(c_1738,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(sK7,X1,X0),k1_relat_1(sK7)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_499])).

cnf(c_4081,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(sK7,X1,X0),sK4) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4072,c_1738])).

cnf(c_1749,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3011,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1740,c_1749])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_286,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_287,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_286])).

cnf(c_360,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_12,c_287])).

cnf(c_2073,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_360])).

cnf(c_2637,plain,
    ( ~ r1_tarski(sK7,k2_zfmisc_1(X0,X1))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_2073])).

cnf(c_4334,plain,
    ( ~ r1_tarski(sK7,k2_zfmisc_1(sK4,sK5))
    | ~ v1_relat_1(k2_zfmisc_1(sK4,sK5))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_2637])).

cnf(c_4335,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(sK4,sK5)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK4,sK5)) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4334])).

cnf(c_13,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_4817,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_4818,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4817])).

cnf(c_5854,plain,
    ( r2_hidden(sK3(sK7,X1,X0),sK4) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4081,c_3011,c_4335,c_4818])).

cnf(c_5855,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(sK7,X1,X0),sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_5854])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1743,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2882,plain,
    ( k7_relset_1(sK4,sK5,sK7,X0) = k9_relat_1(sK7,X0) ),
    inference(superposition,[status(thm)],[c_1740,c_1743])).

cnf(c_1741,plain,
    ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_3298,plain,
    ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2882,c_1741])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_543,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2)
    | sK7 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_36])).

cnf(c_544,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(sK7))
    | r2_hidden(k1_funct_1(sK7,X0),k9_relat_1(sK7,X1))
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_543])).

cnf(c_1735,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k9_relat_1(sK7,X1)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_544])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK3(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_528,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK3(X1,X2,X0)) = X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_36])).

cnf(c_529,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
    | ~ v1_relat_1(sK7)
    | k1_funct_1(sK7,sK3(sK7,X1,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_528])).

cnf(c_1736,plain,
    ( k1_funct_1(sK7,sK3(sK7,X0,X1)) = X1
    | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_529])).

cnf(c_2464,plain,
    ( k1_funct_1(sK7,sK3(sK7,X0,k1_funct_1(sK7,X1))) = k1_funct_1(sK7,X1)
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK7)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1735,c_1736])).

cnf(c_6707,plain,
    ( r2_hidden(X1,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | k1_funct_1(sK7,sK3(sK7,X0,k1_funct_1(sK7,X1))) = k1_funct_1(sK7,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2464,c_3011,c_4335,c_4818])).

cnf(c_6708,plain,
    ( k1_funct_1(sK7,sK3(sK7,X0,k1_funct_1(sK7,X1))) = k1_funct_1(sK7,X1)
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6707])).

cnf(c_6711,plain,
    ( k1_funct_1(sK7,sK3(sK7,X0,k1_funct_1(sK7,X1))) = k1_funct_1(sK7,X1)
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(X1,sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6708,c_4072])).

cnf(c_6717,plain,
    ( k1_funct_1(sK7,sK3(sK7,X0,k1_funct_1(sK7,sK3(sK7,X0,X1)))) = k1_funct_1(sK7,sK3(sK7,X0,X1))
    | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top
    | r2_hidden(sK3(sK7,X0,X1),sK4) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1737,c_6711])).

cnf(c_10846,plain,
    ( r2_hidden(sK3(sK7,X0,X1),sK4) != iProver_top
    | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top
    | k1_funct_1(sK7,sK3(sK7,X0,k1_funct_1(sK7,sK3(sK7,X0,X1)))) = k1_funct_1(sK7,sK3(sK7,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6717,c_3011,c_4335,c_4818])).

cnf(c_10847,plain,
    ( k1_funct_1(sK7,sK3(sK7,X0,k1_funct_1(sK7,sK3(sK7,X0,X1)))) = k1_funct_1(sK7,sK3(sK7,X0,X1))
    | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top
    | r2_hidden(sK3(sK7,X0,X1),sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_10846])).

cnf(c_10853,plain,
    ( k1_funct_1(sK7,sK3(sK7,X0,k1_funct_1(sK7,sK3(sK7,X0,X1)))) = k1_funct_1(sK7,sK3(sK7,X0,X1))
    | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10847,c_5855])).

cnf(c_10863,plain,
    ( k1_funct_1(sK7,sK3(sK7,sK6,k1_funct_1(sK7,sK3(sK7,sK6,sK8)))) = k1_funct_1(sK7,sK3(sK7,sK6,sK8)) ),
    inference(superposition,[status(thm)],[c_3298,c_10853])).

cnf(c_32,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | ~ r2_hidden(X0,sK6)
    | k1_funct_1(sK7,X0) != sK8 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1742,plain,
    ( k1_funct_1(sK7,X0) != sK8
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_10980,plain,
    ( k1_funct_1(sK7,sK3(sK7,sK6,sK8)) != sK8
    | r2_hidden(sK3(sK7,sK6,k1_funct_1(sK7,sK3(sK7,sK6,sK8))),sK4) != iProver_top
    | r2_hidden(sK3(sK7,sK6,k1_funct_1(sK7,sK3(sK7,sK6,sK8))),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_10863,c_1742])).

cnf(c_3012,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(sK4,sK5)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3011])).

cnf(c_3377,plain,
    ( k1_funct_1(sK7,sK3(sK7,sK6,sK8)) = sK8
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3298,c_1736])).

cnf(c_3392,plain,
    ( ~ v1_relat_1(sK7)
    | k1_funct_1(sK7,sK3(sK7,sK6,sK8)) = sK8 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3377])).

cnf(c_10998,plain,
    ( r2_hidden(sK3(sK7,sK6,k1_funct_1(sK7,sK3(sK7,sK6,sK8))),sK4) != iProver_top
    | r2_hidden(sK3(sK7,sK6,k1_funct_1(sK7,sK3(sK7,sK6,sK8))),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10980,c_3012,c_3392,c_4334,c_4817])).

cnf(c_11004,plain,
    ( r2_hidden(sK3(sK7,sK6,k1_funct_1(sK7,sK3(sK7,sK6,sK8))),sK6) != iProver_top
    | r2_hidden(k1_funct_1(sK7,sK3(sK7,sK6,sK8)),k9_relat_1(sK7,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5855,c_10998])).

cnf(c_40,plain,
    ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_2068,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | k7_relset_1(sK4,sK5,sK7,X0) = k9_relat_1(sK7,X0) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_3054,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | k7_relset_1(sK4,sK5,sK7,sK6) = k9_relat_1(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_2068])).

cnf(c_1031,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2978,plain,
    ( X0 != X1
    | X0 = k7_relset_1(sK4,sK5,sK7,sK6)
    | k7_relset_1(sK4,sK5,sK7,sK6) != X1 ),
    inference(instantiation,[status(thm)],[c_1031])).

cnf(c_3971,plain,
    ( X0 = k7_relset_1(sK4,sK5,sK7,sK6)
    | X0 != k9_relat_1(sK7,sK6)
    | k7_relset_1(sK4,sK5,sK7,sK6) != k9_relat_1(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_2978])).

cnf(c_4734,plain,
    ( k7_relset_1(sK4,sK5,sK7,sK6) != k9_relat_1(sK7,sK6)
    | k9_relat_1(sK7,sK6) = k7_relset_1(sK4,sK5,sK7,sK6)
    | k9_relat_1(sK7,sK6) != k9_relat_1(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_3971])).

cnf(c_1030,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4735,plain,
    ( k9_relat_1(sK7,sK6) = k9_relat_1(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_1030])).

cnf(c_1032,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2044,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))
    | X1 != k7_relset_1(sK4,sK5,sK7,sK6)
    | X0 != sK8 ),
    inference(instantiation,[status(thm)],[c_1032])).

cnf(c_9138,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,sK6))
    | ~ r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))
    | X0 != sK8
    | k9_relat_1(sK7,sK6) != k7_relset_1(sK4,sK5,sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_2044])).

cnf(c_10763,plain,
    ( r2_hidden(k1_funct_1(sK7,sK3(sK7,sK6,sK8)),k9_relat_1(sK7,sK6))
    | ~ r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))
    | k1_funct_1(sK7,sK3(sK7,sK6,sK8)) != sK8
    | k9_relat_1(sK7,sK6) != k7_relset_1(sK4,sK5,sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_9138])).

cnf(c_10764,plain,
    ( k1_funct_1(sK7,sK3(sK7,sK6,sK8)) != sK8
    | k9_relat_1(sK7,sK6) != k7_relset_1(sK4,sK5,sK7,sK6)
    | r2_hidden(k1_funct_1(sK7,sK3(sK7,sK6,sK8)),k9_relat_1(sK7,sK6)) = iProver_top
    | r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10763])).

cnf(c_11201,plain,
    ( r2_hidden(sK3(sK7,sK6,k1_funct_1(sK7,sK3(sK7,sK6,sK8))),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11004,c_34,c_40,c_3012,c_3054,c_3392,c_4334,c_4734,c_4735,c_4817,c_10764])).

cnf(c_11206,plain,
    ( r2_hidden(k1_funct_1(sK7,sK3(sK7,sK6,sK8)),k9_relat_1(sK7,sK6)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1737,c_11201])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11206,c_10764,c_4818,c_4817,c_4735,c_4734,c_4335,c_4334,c_3392,c_3054,c_3012,c_3011,c_40,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:06:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.57/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/0.99  
% 3.57/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.57/0.99  
% 3.57/0.99  ------  iProver source info
% 3.57/0.99  
% 3.57/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.57/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.57/0.99  git: non_committed_changes: false
% 3.57/0.99  git: last_make_outside_of_git: false
% 3.57/0.99  
% 3.57/0.99  ------ 
% 3.57/0.99  
% 3.57/0.99  ------ Input Options
% 3.57/0.99  
% 3.57/0.99  --out_options                           all
% 3.57/0.99  --tptp_safe_out                         true
% 3.57/0.99  --problem_path                          ""
% 3.57/0.99  --include_path                          ""
% 3.57/0.99  --clausifier                            res/vclausify_rel
% 3.57/0.99  --clausifier_options                    --mode clausify
% 3.57/0.99  --stdin                                 false
% 3.57/0.99  --stats_out                             all
% 3.57/0.99  
% 3.57/0.99  ------ General Options
% 3.57/0.99  
% 3.57/0.99  --fof                                   false
% 3.57/0.99  --time_out_real                         305.
% 3.57/0.99  --time_out_virtual                      -1.
% 3.57/0.99  --symbol_type_check                     false
% 3.57/0.99  --clausify_out                          false
% 3.57/0.99  --sig_cnt_out                           false
% 3.57/0.99  --trig_cnt_out                          false
% 3.57/0.99  --trig_cnt_out_tolerance                1.
% 3.57/0.99  --trig_cnt_out_sk_spl                   false
% 3.57/0.99  --abstr_cl_out                          false
% 3.57/0.99  
% 3.57/0.99  ------ Global Options
% 3.57/0.99  
% 3.57/0.99  --schedule                              default
% 3.57/0.99  --add_important_lit                     false
% 3.57/0.99  --prop_solver_per_cl                    1000
% 3.57/0.99  --min_unsat_core                        false
% 3.57/0.99  --soft_assumptions                      false
% 3.57/0.99  --soft_lemma_size                       3
% 3.57/0.99  --prop_impl_unit_size                   0
% 3.57/0.99  --prop_impl_unit                        []
% 3.57/0.99  --share_sel_clauses                     true
% 3.57/0.99  --reset_solvers                         false
% 3.57/0.99  --bc_imp_inh                            [conj_cone]
% 3.57/0.99  --conj_cone_tolerance                   3.
% 3.57/0.99  --extra_neg_conj                        none
% 3.57/0.99  --large_theory_mode                     true
% 3.57/0.99  --prolific_symb_bound                   200
% 3.57/0.99  --lt_threshold                          2000
% 3.57/0.99  --clause_weak_htbl                      true
% 3.57/0.99  --gc_record_bc_elim                     false
% 3.57/0.99  
% 3.57/0.99  ------ Preprocessing Options
% 3.57/0.99  
% 3.57/0.99  --preprocessing_flag                    true
% 3.57/0.99  --time_out_prep_mult                    0.1
% 3.57/0.99  --splitting_mode                        input
% 3.57/0.99  --splitting_grd                         true
% 3.57/0.99  --splitting_cvd                         false
% 3.57/0.99  --splitting_cvd_svl                     false
% 3.57/0.99  --splitting_nvd                         32
% 3.57/0.99  --sub_typing                            true
% 3.57/0.99  --prep_gs_sim                           true
% 3.57/0.99  --prep_unflatten                        true
% 3.57/0.99  --prep_res_sim                          true
% 3.57/0.99  --prep_upred                            true
% 3.57/0.99  --prep_sem_filter                       exhaustive
% 3.57/0.99  --prep_sem_filter_out                   false
% 3.57/0.99  --pred_elim                             true
% 3.57/0.99  --res_sim_input                         true
% 3.57/0.99  --eq_ax_congr_red                       true
% 3.57/0.99  --pure_diseq_elim                       true
% 3.57/0.99  --brand_transform                       false
% 3.57/0.99  --non_eq_to_eq                          false
% 3.57/0.99  --prep_def_merge                        true
% 3.57/0.99  --prep_def_merge_prop_impl              false
% 3.57/0.99  --prep_def_merge_mbd                    true
% 3.57/0.99  --prep_def_merge_tr_red                 false
% 3.57/0.99  --prep_def_merge_tr_cl                  false
% 3.57/0.99  --smt_preprocessing                     true
% 3.57/0.99  --smt_ac_axioms                         fast
% 3.57/0.99  --preprocessed_out                      false
% 3.57/0.99  --preprocessed_stats                    false
% 3.57/0.99  
% 3.57/0.99  ------ Abstraction refinement Options
% 3.57/0.99  
% 3.57/0.99  --abstr_ref                             []
% 3.57/0.99  --abstr_ref_prep                        false
% 3.57/0.99  --abstr_ref_until_sat                   false
% 3.57/0.99  --abstr_ref_sig_restrict                funpre
% 3.57/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.57/0.99  --abstr_ref_under                       []
% 3.57/0.99  
% 3.57/0.99  ------ SAT Options
% 3.57/0.99  
% 3.57/0.99  --sat_mode                              false
% 3.57/0.99  --sat_fm_restart_options                ""
% 3.57/0.99  --sat_gr_def                            false
% 3.57/0.99  --sat_epr_types                         true
% 3.57/0.99  --sat_non_cyclic_types                  false
% 3.57/0.99  --sat_finite_models                     false
% 3.57/0.99  --sat_fm_lemmas                         false
% 3.57/0.99  --sat_fm_prep                           false
% 3.57/0.99  --sat_fm_uc_incr                        true
% 3.57/0.99  --sat_out_model                         small
% 3.57/0.99  --sat_out_clauses                       false
% 3.57/0.99  
% 3.57/0.99  ------ QBF Options
% 3.57/0.99  
% 3.57/0.99  --qbf_mode                              false
% 3.57/0.99  --qbf_elim_univ                         false
% 3.57/0.99  --qbf_dom_inst                          none
% 3.57/0.99  --qbf_dom_pre_inst                      false
% 3.57/0.99  --qbf_sk_in                             false
% 3.57/0.99  --qbf_pred_elim                         true
% 3.57/0.99  --qbf_split                             512
% 3.57/0.99  
% 3.57/0.99  ------ BMC1 Options
% 3.57/0.99  
% 3.57/0.99  --bmc1_incremental                      false
% 3.57/0.99  --bmc1_axioms                           reachable_all
% 3.57/0.99  --bmc1_min_bound                        0
% 3.57/0.99  --bmc1_max_bound                        -1
% 3.57/0.99  --bmc1_max_bound_default                -1
% 3.57/0.99  --bmc1_symbol_reachability              true
% 3.57/0.99  --bmc1_property_lemmas                  false
% 3.57/0.99  --bmc1_k_induction                      false
% 3.57/0.99  --bmc1_non_equiv_states                 false
% 3.57/0.99  --bmc1_deadlock                         false
% 3.57/0.99  --bmc1_ucm                              false
% 3.57/0.99  --bmc1_add_unsat_core                   none
% 3.57/0.99  --bmc1_unsat_core_children              false
% 3.57/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.57/0.99  --bmc1_out_stat                         full
% 3.57/0.99  --bmc1_ground_init                      false
% 3.57/0.99  --bmc1_pre_inst_next_state              false
% 3.57/0.99  --bmc1_pre_inst_state                   false
% 3.57/0.99  --bmc1_pre_inst_reach_state             false
% 3.57/0.99  --bmc1_out_unsat_core                   false
% 3.57/0.99  --bmc1_aig_witness_out                  false
% 3.57/0.99  --bmc1_verbose                          false
% 3.57/0.99  --bmc1_dump_clauses_tptp                false
% 3.57/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.57/0.99  --bmc1_dump_file                        -
% 3.57/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.57/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.57/0.99  --bmc1_ucm_extend_mode                  1
% 3.57/0.99  --bmc1_ucm_init_mode                    2
% 3.57/0.99  --bmc1_ucm_cone_mode                    none
% 3.57/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.57/0.99  --bmc1_ucm_relax_model                  4
% 3.57/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.57/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.57/0.99  --bmc1_ucm_layered_model                none
% 3.57/0.99  --bmc1_ucm_max_lemma_size               10
% 3.57/0.99  
% 3.57/0.99  ------ AIG Options
% 3.57/0.99  
% 3.57/0.99  --aig_mode                              false
% 3.57/0.99  
% 3.57/0.99  ------ Instantiation Options
% 3.57/0.99  
% 3.57/0.99  --instantiation_flag                    true
% 3.57/0.99  --inst_sos_flag                         false
% 3.57/0.99  --inst_sos_phase                        true
% 3.57/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.57/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.57/0.99  --inst_lit_sel_side                     num_symb
% 3.57/0.99  --inst_solver_per_active                1400
% 3.57/0.99  --inst_solver_calls_frac                1.
% 3.57/0.99  --inst_passive_queue_type               priority_queues
% 3.57/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.57/0.99  --inst_passive_queues_freq              [25;2]
% 3.57/0.99  --inst_dismatching                      true
% 3.57/0.99  --inst_eager_unprocessed_to_passive     true
% 3.57/0.99  --inst_prop_sim_given                   true
% 3.57/0.99  --inst_prop_sim_new                     false
% 3.57/0.99  --inst_subs_new                         false
% 3.57/0.99  --inst_eq_res_simp                      false
% 3.57/0.99  --inst_subs_given                       false
% 3.57/0.99  --inst_orphan_elimination               true
% 3.57/0.99  --inst_learning_loop_flag               true
% 3.57/0.99  --inst_learning_start                   3000
% 3.57/0.99  --inst_learning_factor                  2
% 3.57/0.99  --inst_start_prop_sim_after_learn       3
% 3.57/0.99  --inst_sel_renew                        solver
% 3.57/0.99  --inst_lit_activity_flag                true
% 3.57/0.99  --inst_restr_to_given                   false
% 3.57/0.99  --inst_activity_threshold               500
% 3.57/0.99  --inst_out_proof                        true
% 3.57/0.99  
% 3.57/0.99  ------ Resolution Options
% 3.57/0.99  
% 3.57/0.99  --resolution_flag                       true
% 3.57/0.99  --res_lit_sel                           adaptive
% 3.57/0.99  --res_lit_sel_side                      none
% 3.57/0.99  --res_ordering                          kbo
% 3.57/0.99  --res_to_prop_solver                    active
% 3.57/0.99  --res_prop_simpl_new                    false
% 3.57/0.99  --res_prop_simpl_given                  true
% 3.57/0.99  --res_passive_queue_type                priority_queues
% 3.57/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.57/0.99  --res_passive_queues_freq               [15;5]
% 3.57/0.99  --res_forward_subs                      full
% 3.57/0.99  --res_backward_subs                     full
% 3.57/0.99  --res_forward_subs_resolution           true
% 3.57/0.99  --res_backward_subs_resolution          true
% 3.57/0.99  --res_orphan_elimination                true
% 3.57/0.99  --res_time_limit                        2.
% 3.57/0.99  --res_out_proof                         true
% 3.57/0.99  
% 3.57/0.99  ------ Superposition Options
% 3.57/0.99  
% 3.57/0.99  --superposition_flag                    true
% 3.57/0.99  --sup_passive_queue_type                priority_queues
% 3.57/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.57/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.57/0.99  --demod_completeness_check              fast
% 3.57/0.99  --demod_use_ground                      true
% 3.57/0.99  --sup_to_prop_solver                    passive
% 3.57/0.99  --sup_prop_simpl_new                    true
% 3.57/0.99  --sup_prop_simpl_given                  true
% 3.57/0.99  --sup_fun_splitting                     false
% 3.57/0.99  --sup_smt_interval                      50000
% 3.57/0.99  
% 3.57/0.99  ------ Superposition Simplification Setup
% 3.57/0.99  
% 3.57/0.99  --sup_indices_passive                   []
% 3.57/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.57/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/0.99  --sup_full_bw                           [BwDemod]
% 3.57/0.99  --sup_immed_triv                        [TrivRules]
% 3.57/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.57/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/0.99  --sup_immed_bw_main                     []
% 3.57/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.57/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.57/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.57/0.99  
% 3.57/0.99  ------ Combination Options
% 3.57/0.99  
% 3.57/0.99  --comb_res_mult                         3
% 3.57/0.99  --comb_sup_mult                         2
% 3.57/0.99  --comb_inst_mult                        10
% 3.57/0.99  
% 3.57/0.99  ------ Debug Options
% 3.57/0.99  
% 3.57/0.99  --dbg_backtrace                         false
% 3.57/0.99  --dbg_dump_prop_clauses                 false
% 3.57/0.99  --dbg_dump_prop_clauses_file            -
% 3.57/0.99  --dbg_out_stat                          false
% 3.57/0.99  ------ Parsing...
% 3.57/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.57/0.99  
% 3.57/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.57/0.99  
% 3.57/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.57/0.99  
% 3.57/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.57/0.99  ------ Proving...
% 3.57/0.99  ------ Problem Properties 
% 3.57/0.99  
% 3.57/0.99  
% 3.57/0.99  clauses                                 31
% 3.57/0.99  conjectures                             3
% 3.57/0.99  EPR                                     8
% 3.57/0.99  Horn                                    24
% 3.57/0.99  unary                                   5
% 3.57/0.99  binary                                  10
% 3.57/0.99  lits                                    81
% 3.57/0.99  lits eq                                 18
% 3.57/0.99  fd_pure                                 0
% 3.57/0.99  fd_pseudo                               0
% 3.57/0.99  fd_cond                                 0
% 3.57/0.99  fd_pseudo_cond                          5
% 3.57/0.99  AC symbols                              0
% 3.57/0.99  
% 3.57/0.99  ------ Schedule dynamic 5 is on 
% 3.57/0.99  
% 3.57/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.57/0.99  
% 3.57/0.99  
% 3.57/0.99  ------ 
% 3.57/0.99  Current options:
% 3.57/0.99  ------ 
% 3.57/0.99  
% 3.57/0.99  ------ Input Options
% 3.57/0.99  
% 3.57/0.99  --out_options                           all
% 3.57/0.99  --tptp_safe_out                         true
% 3.57/0.99  --problem_path                          ""
% 3.57/0.99  --include_path                          ""
% 3.57/0.99  --clausifier                            res/vclausify_rel
% 3.57/0.99  --clausifier_options                    --mode clausify
% 3.57/0.99  --stdin                                 false
% 3.57/0.99  --stats_out                             all
% 3.57/0.99  
% 3.57/0.99  ------ General Options
% 3.57/0.99  
% 3.57/0.99  --fof                                   false
% 3.57/0.99  --time_out_real                         305.
% 3.57/0.99  --time_out_virtual                      -1.
% 3.57/0.99  --symbol_type_check                     false
% 3.57/0.99  --clausify_out                          false
% 3.57/0.99  --sig_cnt_out                           false
% 3.57/0.99  --trig_cnt_out                          false
% 3.57/0.99  --trig_cnt_out_tolerance                1.
% 3.57/0.99  --trig_cnt_out_sk_spl                   false
% 3.57/0.99  --abstr_cl_out                          false
% 3.57/0.99  
% 3.57/0.99  ------ Global Options
% 3.57/0.99  
% 3.57/0.99  --schedule                              default
% 3.57/0.99  --add_important_lit                     false
% 3.57/0.99  --prop_solver_per_cl                    1000
% 3.57/0.99  --min_unsat_core                        false
% 3.57/0.99  --soft_assumptions                      false
% 3.57/0.99  --soft_lemma_size                       3
% 3.57/0.99  --prop_impl_unit_size                   0
% 3.57/0.99  --prop_impl_unit                        []
% 3.57/0.99  --share_sel_clauses                     true
% 3.57/0.99  --reset_solvers                         false
% 3.57/0.99  --bc_imp_inh                            [conj_cone]
% 3.57/0.99  --conj_cone_tolerance                   3.
% 3.57/0.99  --extra_neg_conj                        none
% 3.57/0.99  --large_theory_mode                     true
% 3.57/0.99  --prolific_symb_bound                   200
% 3.57/0.99  --lt_threshold                          2000
% 3.57/0.99  --clause_weak_htbl                      true
% 3.57/0.99  --gc_record_bc_elim                     false
% 3.57/0.99  
% 3.57/0.99  ------ Preprocessing Options
% 3.57/0.99  
% 3.57/0.99  --preprocessing_flag                    true
% 3.57/0.99  --time_out_prep_mult                    0.1
% 3.57/0.99  --splitting_mode                        input
% 3.57/0.99  --splitting_grd                         true
% 3.57/0.99  --splitting_cvd                         false
% 3.57/0.99  --splitting_cvd_svl                     false
% 3.57/0.99  --splitting_nvd                         32
% 3.57/0.99  --sub_typing                            true
% 3.57/0.99  --prep_gs_sim                           true
% 3.57/0.99  --prep_unflatten                        true
% 3.57/0.99  --prep_res_sim                          true
% 3.57/0.99  --prep_upred                            true
% 3.57/0.99  --prep_sem_filter                       exhaustive
% 3.57/0.99  --prep_sem_filter_out                   false
% 3.57/0.99  --pred_elim                             true
% 3.57/0.99  --res_sim_input                         true
% 3.57/0.99  --eq_ax_congr_red                       true
% 3.57/0.99  --pure_diseq_elim                       true
% 3.57/0.99  --brand_transform                       false
% 3.57/0.99  --non_eq_to_eq                          false
% 3.57/0.99  --prep_def_merge                        true
% 3.57/0.99  --prep_def_merge_prop_impl              false
% 3.57/0.99  --prep_def_merge_mbd                    true
% 3.57/0.99  --prep_def_merge_tr_red                 false
% 3.57/0.99  --prep_def_merge_tr_cl                  false
% 3.57/0.99  --smt_preprocessing                     true
% 3.57/0.99  --smt_ac_axioms                         fast
% 3.57/0.99  --preprocessed_out                      false
% 3.57/0.99  --preprocessed_stats                    false
% 3.57/0.99  
% 3.57/0.99  ------ Abstraction refinement Options
% 3.57/0.99  
% 3.57/0.99  --abstr_ref                             []
% 3.57/0.99  --abstr_ref_prep                        false
% 3.57/0.99  --abstr_ref_until_sat                   false
% 3.57/0.99  --abstr_ref_sig_restrict                funpre
% 3.57/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.57/0.99  --abstr_ref_under                       []
% 3.57/0.99  
% 3.57/0.99  ------ SAT Options
% 3.57/0.99  
% 3.57/0.99  --sat_mode                              false
% 3.57/0.99  --sat_fm_restart_options                ""
% 3.57/0.99  --sat_gr_def                            false
% 3.57/0.99  --sat_epr_types                         true
% 3.57/0.99  --sat_non_cyclic_types                  false
% 3.57/0.99  --sat_finite_models                     false
% 3.57/0.99  --sat_fm_lemmas                         false
% 3.57/0.99  --sat_fm_prep                           false
% 3.57/0.99  --sat_fm_uc_incr                        true
% 3.57/0.99  --sat_out_model                         small
% 3.57/0.99  --sat_out_clauses                       false
% 3.57/0.99  
% 3.57/0.99  ------ QBF Options
% 3.57/0.99  
% 3.57/0.99  --qbf_mode                              false
% 3.57/0.99  --qbf_elim_univ                         false
% 3.57/0.99  --qbf_dom_inst                          none
% 3.57/0.99  --qbf_dom_pre_inst                      false
% 3.57/0.99  --qbf_sk_in                             false
% 3.57/0.99  --qbf_pred_elim                         true
% 3.57/0.99  --qbf_split                             512
% 3.57/0.99  
% 3.57/0.99  ------ BMC1 Options
% 3.57/0.99  
% 3.57/0.99  --bmc1_incremental                      false
% 3.57/0.99  --bmc1_axioms                           reachable_all
% 3.57/0.99  --bmc1_min_bound                        0
% 3.57/0.99  --bmc1_max_bound                        -1
% 3.57/0.99  --bmc1_max_bound_default                -1
% 3.57/0.99  --bmc1_symbol_reachability              true
% 3.57/0.99  --bmc1_property_lemmas                  false
% 3.57/0.99  --bmc1_k_induction                      false
% 3.57/0.99  --bmc1_non_equiv_states                 false
% 3.57/0.99  --bmc1_deadlock                         false
% 3.57/0.99  --bmc1_ucm                              false
% 3.57/0.99  --bmc1_add_unsat_core                   none
% 3.57/0.99  --bmc1_unsat_core_children              false
% 3.57/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.57/0.99  --bmc1_out_stat                         full
% 3.57/0.99  --bmc1_ground_init                      false
% 3.57/0.99  --bmc1_pre_inst_next_state              false
% 3.57/0.99  --bmc1_pre_inst_state                   false
% 3.57/0.99  --bmc1_pre_inst_reach_state             false
% 3.57/0.99  --bmc1_out_unsat_core                   false
% 3.57/0.99  --bmc1_aig_witness_out                  false
% 3.57/0.99  --bmc1_verbose                          false
% 3.57/0.99  --bmc1_dump_clauses_tptp                false
% 3.57/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.57/0.99  --bmc1_dump_file                        -
% 3.57/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.57/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.57/0.99  --bmc1_ucm_extend_mode                  1
% 3.57/0.99  --bmc1_ucm_init_mode                    2
% 3.57/0.99  --bmc1_ucm_cone_mode                    none
% 3.57/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.57/0.99  --bmc1_ucm_relax_model                  4
% 3.57/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.57/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.57/0.99  --bmc1_ucm_layered_model                none
% 3.57/0.99  --bmc1_ucm_max_lemma_size               10
% 3.57/0.99  
% 3.57/0.99  ------ AIG Options
% 3.57/0.99  
% 3.57/0.99  --aig_mode                              false
% 3.57/0.99  
% 3.57/0.99  ------ Instantiation Options
% 3.57/0.99  
% 3.57/0.99  --instantiation_flag                    true
% 3.57/0.99  --inst_sos_flag                         false
% 3.57/0.99  --inst_sos_phase                        true
% 3.57/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.57/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.57/0.99  --inst_lit_sel_side                     none
% 3.57/0.99  --inst_solver_per_active                1400
% 3.57/0.99  --inst_solver_calls_frac                1.
% 3.57/0.99  --inst_passive_queue_type               priority_queues
% 3.57/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.57/0.99  --inst_passive_queues_freq              [25;2]
% 3.57/0.99  --inst_dismatching                      true
% 3.57/0.99  --inst_eager_unprocessed_to_passive     true
% 3.57/0.99  --inst_prop_sim_given                   true
% 3.57/0.99  --inst_prop_sim_new                     false
% 3.57/0.99  --inst_subs_new                         false
% 3.57/0.99  --inst_eq_res_simp                      false
% 3.57/0.99  --inst_subs_given                       false
% 3.57/0.99  --inst_orphan_elimination               true
% 3.57/0.99  --inst_learning_loop_flag               true
% 3.57/0.99  --inst_learning_start                   3000
% 3.57/0.99  --inst_learning_factor                  2
% 3.57/0.99  --inst_start_prop_sim_after_learn       3
% 3.57/0.99  --inst_sel_renew                        solver
% 3.57/0.99  --inst_lit_activity_flag                true
% 3.57/0.99  --inst_restr_to_given                   false
% 3.57/0.99  --inst_activity_threshold               500
% 3.57/0.99  --inst_out_proof                        true
% 3.57/0.99  
% 3.57/0.99  ------ Resolution Options
% 3.57/0.99  
% 3.57/0.99  --resolution_flag                       false
% 3.57/0.99  --res_lit_sel                           adaptive
% 3.57/0.99  --res_lit_sel_side                      none
% 3.57/0.99  --res_ordering                          kbo
% 3.57/0.99  --res_to_prop_solver                    active
% 3.57/0.99  --res_prop_simpl_new                    false
% 3.57/0.99  --res_prop_simpl_given                  true
% 3.57/0.99  --res_passive_queue_type                priority_queues
% 3.57/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.57/0.99  --res_passive_queues_freq               [15;5]
% 3.57/0.99  --res_forward_subs                      full
% 3.57/0.99  --res_backward_subs                     full
% 3.57/0.99  --res_forward_subs_resolution           true
% 3.57/0.99  --res_backward_subs_resolution          true
% 3.57/0.99  --res_orphan_elimination                true
% 3.57/0.99  --res_time_limit                        2.
% 3.57/0.99  --res_out_proof                         true
% 3.57/0.99  
% 3.57/0.99  ------ Superposition Options
% 3.57/0.99  
% 3.57/0.99  --superposition_flag                    true
% 3.57/0.99  --sup_passive_queue_type                priority_queues
% 3.57/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.57/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.57/0.99  --demod_completeness_check              fast
% 3.57/0.99  --demod_use_ground                      true
% 3.57/0.99  --sup_to_prop_solver                    passive
% 3.57/0.99  --sup_prop_simpl_new                    true
% 3.57/0.99  --sup_prop_simpl_given                  true
% 3.57/0.99  --sup_fun_splitting                     false
% 3.57/0.99  --sup_smt_interval                      50000
% 3.57/0.99  
% 3.57/0.99  ------ Superposition Simplification Setup
% 3.57/0.99  
% 3.57/0.99  --sup_indices_passive                   []
% 3.57/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.57/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/0.99  --sup_full_bw                           [BwDemod]
% 3.57/0.99  --sup_immed_triv                        [TrivRules]
% 3.57/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.57/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/0.99  --sup_immed_bw_main                     []
% 3.57/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.57/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.57/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.57/0.99  
% 3.57/0.99  ------ Combination Options
% 3.57/0.99  
% 3.57/0.99  --comb_res_mult                         3
% 3.57/0.99  --comb_sup_mult                         2
% 3.57/0.99  --comb_inst_mult                        10
% 3.57/0.99  
% 3.57/0.99  ------ Debug Options
% 3.57/0.99  
% 3.57/0.99  --dbg_backtrace                         false
% 3.57/0.99  --dbg_dump_prop_clauses                 false
% 3.57/0.99  --dbg_dump_prop_clauses_file            -
% 3.57/0.99  --dbg_out_stat                          false
% 3.57/0.99  
% 3.57/0.99  
% 3.57/0.99  
% 3.57/0.99  
% 3.57/0.99  ------ Proving...
% 3.57/0.99  
% 3.57/0.99  
% 3.57/0.99  % SZS status Theorem for theBenchmark.p
% 3.57/0.99  
% 3.57/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.57/0.99  
% 3.57/0.99  fof(f10,axiom,(
% 3.57/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f26,plain,(
% 3.57/0.99    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.57/0.99    inference(ennf_transformation,[],[f10])).
% 3.57/0.99  
% 3.57/0.99  fof(f27,plain,(
% 3.57/0.99    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.57/0.99    inference(flattening,[],[f26])).
% 3.57/0.99  
% 3.57/0.99  fof(f43,plain,(
% 3.57/0.99    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.57/0.99    inference(nnf_transformation,[],[f27])).
% 3.57/0.99  
% 3.57/0.99  fof(f44,plain,(
% 3.57/0.99    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.57/0.99    inference(rectify,[],[f43])).
% 3.57/0.99  
% 3.57/0.99  fof(f47,plain,(
% 3.57/0.99    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1,X6)) = X6 & r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))))),
% 3.57/0.99    introduced(choice_axiom,[])).
% 3.57/0.99  
% 3.57/0.99  fof(f46,plain,(
% 3.57/0.99    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1,X2)) = X3 & r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))))) )),
% 3.57/0.99    introduced(choice_axiom,[])).
% 3.57/0.99  
% 3.57/0.99  fof(f45,plain,(
% 3.57/0.99    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK1(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK1(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.57/0.99    introduced(choice_axiom,[])).
% 3.57/0.99  
% 3.57/0.99  fof(f48,plain,(
% 3.57/0.99    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK1(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((k1_funct_1(X0,sK2(X0,X1,X2)) = sK1(X0,X1,X2) & r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X1,X6)) = X6 & r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.57/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f44,f47,f46,f45])).
% 3.57/0.99  
% 3.57/0.99  fof(f68,plain,(
% 3.57/0.99    ( ! [X6,X2,X0,X1] : (r2_hidden(sK3(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f48])).
% 3.57/0.99  
% 3.57/0.99  fof(f95,plain,(
% 3.57/0.99    ( ! [X6,X0,X1] : (r2_hidden(sK3(X0,X1,X6),X1) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.57/0.99    inference(equality_resolution,[],[f68])).
% 3.57/0.99  
% 3.57/0.99  fof(f16,conjecture,(
% 3.57/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f17,negated_conjecture,(
% 3.57/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.57/0.99    inference(negated_conjecture,[],[f16])).
% 3.57/0.99  
% 3.57/0.99  fof(f34,plain,(
% 3.57/0.99    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.57/0.99    inference(ennf_transformation,[],[f17])).
% 3.57/0.99  
% 3.57/0.99  fof(f35,plain,(
% 3.57/0.99    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.57/0.99    inference(flattening,[],[f34])).
% 3.57/0.99  
% 3.57/0.99  fof(f51,plain,(
% 3.57/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK8 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(sK8,k7_relset_1(X0,X1,X3,X2)))) )),
% 3.57/0.99    introduced(choice_axiom,[])).
% 3.57/0.99  
% 3.57/0.99  fof(f50,plain,(
% 3.57/0.99    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK7,X5) != X4 | ~r2_hidden(X5,sK6) | ~r2_hidden(X5,sK4)) & r2_hidden(X4,k7_relset_1(sK4,sK5,sK7,sK6))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7))),
% 3.57/0.99    introduced(choice_axiom,[])).
% 3.57/0.99  
% 3.57/0.99  fof(f52,plain,(
% 3.57/0.99    (! [X5] : (k1_funct_1(sK7,X5) != sK8 | ~r2_hidden(X5,sK6) | ~r2_hidden(X5,sK4)) & r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7)),
% 3.57/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f35,f51,f50])).
% 3.57/0.99  
% 3.57/0.99  fof(f85,plain,(
% 3.57/0.99    v1_funct_1(sK7)),
% 3.57/0.99    inference(cnf_transformation,[],[f52])).
% 3.57/0.99  
% 3.57/0.99  fof(f15,axiom,(
% 3.57/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f32,plain,(
% 3.57/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.57/0.99    inference(ennf_transformation,[],[f15])).
% 3.57/0.99  
% 3.57/0.99  fof(f33,plain,(
% 3.57/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.57/0.99    inference(flattening,[],[f32])).
% 3.57/0.99  
% 3.57/0.99  fof(f49,plain,(
% 3.57/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.57/0.99    inference(nnf_transformation,[],[f33])).
% 3.57/0.99  
% 3.57/0.99  fof(f79,plain,(
% 3.57/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.57/0.99    inference(cnf_transformation,[],[f49])).
% 3.57/0.99  
% 3.57/0.99  fof(f86,plain,(
% 3.57/0.99    v1_funct_2(sK7,sK4,sK5)),
% 3.57/0.99    inference(cnf_transformation,[],[f52])).
% 3.57/0.99  
% 3.57/0.99  fof(f87,plain,(
% 3.57/0.99    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 3.57/0.99    inference(cnf_transformation,[],[f52])).
% 3.57/0.99  
% 3.57/0.99  fof(f13,axiom,(
% 3.57/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f30,plain,(
% 3.57/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.57/0.99    inference(ennf_transformation,[],[f13])).
% 3.57/0.99  
% 3.57/0.99  fof(f77,plain,(
% 3.57/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.57/0.99    inference(cnf_transformation,[],[f30])).
% 3.57/0.99  
% 3.57/0.99  fof(f88,plain,(
% 3.57/0.99    r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))),
% 3.57/0.99    inference(cnf_transformation,[],[f52])).
% 3.57/0.99  
% 3.57/0.99  fof(f4,axiom,(
% 3.57/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f60,plain,(
% 3.57/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f4])).
% 3.57/0.99  
% 3.57/0.99  fof(f12,axiom,(
% 3.57/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f29,plain,(
% 3.57/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.57/0.99    inference(ennf_transformation,[],[f12])).
% 3.57/0.99  
% 3.57/0.99  fof(f76,plain,(
% 3.57/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.57/0.99    inference(cnf_transformation,[],[f29])).
% 3.57/0.99  
% 3.57/0.99  fof(f11,axiom,(
% 3.57/0.99    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f28,plain,(
% 3.57/0.99    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.57/0.99    inference(ennf_transformation,[],[f11])).
% 3.57/0.99  
% 3.57/0.99  fof(f75,plain,(
% 3.57/0.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f28])).
% 3.57/0.99  
% 3.57/0.99  fof(f6,axiom,(
% 3.57/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f42,plain,(
% 3.57/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.57/0.99    inference(nnf_transformation,[],[f6])).
% 3.57/0.99  
% 3.57/0.99  fof(f62,plain,(
% 3.57/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.57/0.99    inference(cnf_transformation,[],[f42])).
% 3.57/0.99  
% 3.57/0.99  fof(f2,axiom,(
% 3.57/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f20,plain,(
% 3.57/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.57/0.99    inference(ennf_transformation,[],[f2])).
% 3.57/0.99  
% 3.57/0.99  fof(f36,plain,(
% 3.57/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.57/0.99    inference(nnf_transformation,[],[f20])).
% 3.57/0.99  
% 3.57/0.99  fof(f37,plain,(
% 3.57/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.57/0.99    inference(rectify,[],[f36])).
% 3.57/0.99  
% 3.57/0.99  fof(f38,plain,(
% 3.57/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.57/0.99    introduced(choice_axiom,[])).
% 3.57/0.99  
% 3.57/0.99  fof(f39,plain,(
% 3.57/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.57/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 3.57/0.99  
% 3.57/0.99  fof(f54,plain,(
% 3.57/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f39])).
% 3.57/0.99  
% 3.57/0.99  fof(f67,plain,(
% 3.57/0.99    ( ! [X6,X2,X0,X1] : (r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f48])).
% 3.57/0.99  
% 3.57/0.99  fof(f96,plain,(
% 3.57/0.99    ( ! [X6,X0,X1] : (r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.57/0.99    inference(equality_resolution,[],[f67])).
% 3.57/0.99  
% 3.57/0.99  fof(f8,axiom,(
% 3.57/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f25,plain,(
% 3.57/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.57/0.99    inference(ennf_transformation,[],[f8])).
% 3.57/0.99  
% 3.57/0.99  fof(f65,plain,(
% 3.57/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f25])).
% 3.57/0.99  
% 3.57/0.99  fof(f63,plain,(
% 3.57/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f42])).
% 3.57/0.99  
% 3.57/0.99  fof(f9,axiom,(
% 3.57/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f66,plain,(
% 3.57/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.57/0.99    inference(cnf_transformation,[],[f9])).
% 3.57/0.99  
% 3.57/0.99  fof(f14,axiom,(
% 3.57/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f31,plain,(
% 3.57/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.57/0.99    inference(ennf_transformation,[],[f14])).
% 3.57/0.99  
% 3.57/0.99  fof(f78,plain,(
% 3.57/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.57/0.99    inference(cnf_transformation,[],[f31])).
% 3.57/0.99  
% 3.57/0.99  fof(f70,plain,(
% 3.57/0.99    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f48])).
% 3.57/0.99  
% 3.57/0.99  fof(f92,plain,(
% 3.57/0.99    ( ! [X2,X0,X7,X1] : (r2_hidden(k1_funct_1(X0,X7),X2) | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.57/0.99    inference(equality_resolution,[],[f70])).
% 3.57/0.99  
% 3.57/0.99  fof(f93,plain,(
% 3.57/0.99    ( ! [X0,X7,X1] : (r2_hidden(k1_funct_1(X0,X7),k9_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.57/0.99    inference(equality_resolution,[],[f92])).
% 3.57/0.99  
% 3.57/0.99  fof(f69,plain,(
% 3.57/0.99    ( ! [X6,X2,X0,X1] : (k1_funct_1(X0,sK3(X0,X1,X6)) = X6 | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f48])).
% 3.57/0.99  
% 3.57/0.99  fof(f94,plain,(
% 3.57/0.99    ( ! [X6,X0,X1] : (k1_funct_1(X0,sK3(X0,X1,X6)) = X6 | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.57/0.99    inference(equality_resolution,[],[f69])).
% 3.57/0.99  
% 3.57/0.99  fof(f89,plain,(
% 3.57/0.99    ( ! [X5] : (k1_funct_1(sK7,X5) != sK8 | ~r2_hidden(X5,sK6) | ~r2_hidden(X5,sK4)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f52])).
% 3.57/0.99  
% 3.57/0.99  cnf(c_20,plain,
% 3.57/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.57/0.99      | r2_hidden(sK3(X1,X2,X0),X2)
% 3.57/0.99      | ~ v1_funct_1(X1)
% 3.57/0.99      | ~ v1_relat_1(X1) ),
% 3.57/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_36,negated_conjecture,
% 3.57/0.99      ( v1_funct_1(sK7) ),
% 3.57/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_513,plain,
% 3.57/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.57/0.99      | r2_hidden(sK3(X1,X2,X0),X2)
% 3.57/0.99      | ~ v1_relat_1(X1)
% 3.57/0.99      | sK7 != X1 ),
% 3.57/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_36]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_514,plain,
% 3.57/0.99      ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
% 3.57/0.99      | r2_hidden(sK3(sK7,X1,X0),X1)
% 3.57/0.99      | ~ v1_relat_1(sK7) ),
% 3.57/0.99      inference(unflattening,[status(thm)],[c_513]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1737,plain,
% 3.57/0.99      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.57/0.99      | r2_hidden(sK3(sK7,X1,X0),X1) = iProver_top
% 3.57/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_514]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_31,plain,
% 3.57/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.57/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.57/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.57/0.99      | k1_xboole_0 = X2 ),
% 3.57/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_35,negated_conjecture,
% 3.57/0.99      ( v1_funct_2(sK7,sK4,sK5) ),
% 3.57/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_723,plain,
% 3.57/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.57/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.57/0.99      | sK5 != X2
% 3.57/0.99      | sK4 != X1
% 3.57/0.99      | sK7 != X0
% 3.57/0.99      | k1_xboole_0 = X2 ),
% 3.57/0.99      inference(resolution_lifted,[status(thm)],[c_31,c_35]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_724,plain,
% 3.57/0.99      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.57/0.99      | k1_relset_1(sK4,sK5,sK7) = sK4
% 3.57/0.99      | k1_xboole_0 = sK5 ),
% 3.57/0.99      inference(unflattening,[status(thm)],[c_723]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_34,negated_conjecture,
% 3.57/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 3.57/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_726,plain,
% 3.57/0.99      ( k1_relset_1(sK4,sK5,sK7) = sK4 | k1_xboole_0 = sK5 ),
% 3.57/0.99      inference(global_propositional_subsumption,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_724,c_34]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1740,plain,
% 3.57/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_24,plain,
% 3.57/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.57/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.57/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1744,plain,
% 3.57/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.57/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3691,plain,
% 3.57/0.99      ( k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7) ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_1740,c_1744]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_4008,plain,
% 3.57/0.99      ( k1_relat_1(sK7) = sK4 | sK5 = k1_xboole_0 ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_726,c_3691]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_33,negated_conjecture,
% 3.57/0.99      ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
% 3.57/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_7,plain,
% 3.57/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.57/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_115,plain,
% 3.57/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_23,plain,
% 3.57/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.57/0.99      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
% 3.57/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_2039,plain,
% 3.57/0.99      ( m1_subset_1(k7_relset_1(sK4,sK5,sK7,X0),k1_zfmisc_1(sK5))
% 3.57/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_23]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_2133,plain,
% 3.57/0.99      ( m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5))
% 3.57/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_2039]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1033,plain,
% 3.57/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 3.57/0.99      theory(equality) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_2216,plain,
% 3.57/0.99      ( ~ r1_tarski(X0,k1_xboole_0)
% 3.57/0.99      | r1_tarski(sK5,k1_xboole_0)
% 3.57/0.99      | sK5 != X0 ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_1033]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_2218,plain,
% 3.57/0.99      ( r1_tarski(sK5,k1_xboole_0)
% 3.57/0.99      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.57/0.99      | sK5 != k1_xboole_0 ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_2216]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_2346,plain,
% 3.57/0.99      ( r1_tarski(k1_xboole_0,sK8) ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_22,plain,
% 3.57/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.57/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_2393,plain,
% 3.57/0.99      ( ~ r1_tarski(X0,sK8) | ~ r2_hidden(sK8,X0) ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_22]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_2395,plain,
% 3.57/0.99      ( ~ r1_tarski(k1_xboole_0,sK8) | ~ r2_hidden(sK8,k1_xboole_0) ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_2393]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_10,plain,
% 3.57/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.57/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_2108,plain,
% 3.57/0.99      ( ~ m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(X0))
% 3.57/0.99      | r1_tarski(k7_relset_1(sK4,sK5,sK7,sK6),X0) ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_2945,plain,
% 3.57/0.99      ( ~ m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5))
% 3.57/0.99      | r1_tarski(k7_relset_1(sK4,sK5,sK7,sK6),sK5) ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_2108]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3,plain,
% 3.57/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.57/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_2390,plain,
% 3.57/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(sK8,X0) | r2_hidden(sK8,X1) ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3157,plain,
% 3.57/0.99      ( ~ r1_tarski(sK5,X0) | r2_hidden(sK8,X0) | ~ r2_hidden(sK8,sK5) ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_2390]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3162,plain,
% 3.57/0.99      ( ~ r1_tarski(sK5,k1_xboole_0)
% 3.57/0.99      | ~ r2_hidden(sK8,sK5)
% 3.57/0.99      | r2_hidden(sK8,k1_xboole_0) ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_3157]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_2004,plain,
% 3.57/0.99      ( ~ r1_tarski(k7_relset_1(sK4,sK5,sK7,sK6),X0)
% 3.57/0.99      | r2_hidden(sK8,X0)
% 3.57/0.99      | ~ r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3464,plain,
% 3.57/0.99      ( ~ r1_tarski(k7_relset_1(sK4,sK5,sK7,sK6),sK5)
% 3.57/0.99      | ~ r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))
% 3.57/0.99      | r2_hidden(sK8,sK5) ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_2004]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_4072,plain,
% 3.57/0.99      ( k1_relat_1(sK7) = sK4 ),
% 3.57/0.99      inference(global_propositional_subsumption,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_4008,c_34,c_33,c_115,c_2133,c_2218,c_2346,c_2395,
% 3.57/0.99                 c_2945,c_3162,c_3464]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_21,plain,
% 3.57/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.57/0.99      | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1))
% 3.57/0.99      | ~ v1_funct_1(X1)
% 3.57/0.99      | ~ v1_relat_1(X1) ),
% 3.57/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_498,plain,
% 3.57/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.57/0.99      | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1))
% 3.57/0.99      | ~ v1_relat_1(X1)
% 3.57/0.99      | sK7 != X1 ),
% 3.57/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_36]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_499,plain,
% 3.57/0.99      ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
% 3.57/0.99      | r2_hidden(sK3(sK7,X1,X0),k1_relat_1(sK7))
% 3.57/0.99      | ~ v1_relat_1(sK7) ),
% 3.57/0.99      inference(unflattening,[status(thm)],[c_498]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1738,plain,
% 3.57/0.99      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.57/0.99      | r2_hidden(sK3(sK7,X1,X0),k1_relat_1(sK7)) = iProver_top
% 3.57/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_499]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_4081,plain,
% 3.57/0.99      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.57/0.99      | r2_hidden(sK3(sK7,X1,X0),sK4) = iProver_top
% 3.57/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.57/0.99      inference(demodulation,[status(thm)],[c_4072,c_1738]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1749,plain,
% 3.57/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.57/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3011,plain,
% 3.57/0.99      ( r1_tarski(sK7,k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_1740,c_1749]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_12,plain,
% 3.57/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.57/0.99      | ~ v1_relat_1(X1)
% 3.57/0.99      | v1_relat_1(X0) ),
% 3.57/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_9,plain,
% 3.57/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.57/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_286,plain,
% 3.57/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.57/0.99      inference(prop_impl,[status(thm)],[c_9]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_287,plain,
% 3.57/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.57/0.99      inference(renaming,[status(thm)],[c_286]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_360,plain,
% 3.57/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.57/0.99      inference(bin_hyper_res,[status(thm)],[c_12,c_287]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_2073,plain,
% 3.57/0.99      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 3.57/0.99      | v1_relat_1(X0)
% 3.57/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_360]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_2637,plain,
% 3.57/0.99      ( ~ r1_tarski(sK7,k2_zfmisc_1(X0,X1))
% 3.57/0.99      | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 3.57/0.99      | v1_relat_1(sK7) ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_2073]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_4334,plain,
% 3.57/0.99      ( ~ r1_tarski(sK7,k2_zfmisc_1(sK4,sK5))
% 3.57/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK4,sK5))
% 3.57/0.99      | v1_relat_1(sK7) ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_2637]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_4335,plain,
% 3.57/0.99      ( r1_tarski(sK7,k2_zfmisc_1(sK4,sK5)) != iProver_top
% 3.57/0.99      | v1_relat_1(k2_zfmisc_1(sK4,sK5)) != iProver_top
% 3.57/0.99      | v1_relat_1(sK7) = iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_4334]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_13,plain,
% 3.57/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.57/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_4817,plain,
% 3.57/0.99      ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_4818,plain,
% 3.57/0.99      ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_4817]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_5854,plain,
% 3.57/0.99      ( r2_hidden(sK3(sK7,X1,X0),sK4) = iProver_top
% 3.57/0.99      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
% 3.57/0.99      inference(global_propositional_subsumption,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_4081,c_3011,c_4335,c_4818]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_5855,plain,
% 3.57/0.99      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.57/0.99      | r2_hidden(sK3(sK7,X1,X0),sK4) = iProver_top ),
% 3.57/0.99      inference(renaming,[status(thm)],[c_5854]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_25,plain,
% 3.57/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.57/0.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.57/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1743,plain,
% 3.57/0.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.57/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_2882,plain,
% 3.57/0.99      ( k7_relset_1(sK4,sK5,sK7,X0) = k9_relat_1(sK7,X0) ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_1740,c_1743]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1741,plain,
% 3.57/0.99      ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3298,plain,
% 3.57/0.99      ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) = iProver_top ),
% 3.57/0.99      inference(demodulation,[status(thm)],[c_2882,c_1741]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_18,plain,
% 3.57/0.99      ( ~ r2_hidden(X0,X1)
% 3.57/0.99      | ~ r2_hidden(X0,k1_relat_1(X2))
% 3.57/0.99      | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1))
% 3.57/0.99      | ~ v1_funct_1(X2)
% 3.57/0.99      | ~ v1_relat_1(X2) ),
% 3.57/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_543,plain,
% 3.57/0.99      ( ~ r2_hidden(X0,X1)
% 3.57/0.99      | ~ r2_hidden(X0,k1_relat_1(X2))
% 3.57/0.99      | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1))
% 3.57/0.99      | ~ v1_relat_1(X2)
% 3.57/0.99      | sK7 != X2 ),
% 3.57/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_36]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_544,plain,
% 3.57/0.99      ( ~ r2_hidden(X0,X1)
% 3.57/0.99      | ~ r2_hidden(X0,k1_relat_1(sK7))
% 3.57/0.99      | r2_hidden(k1_funct_1(sK7,X0),k9_relat_1(sK7,X1))
% 3.57/0.99      | ~ v1_relat_1(sK7) ),
% 3.57/0.99      inference(unflattening,[status(thm)],[c_543]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1735,plain,
% 3.57/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.57/0.99      | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 3.57/0.99      | r2_hidden(k1_funct_1(sK7,X0),k9_relat_1(sK7,X1)) = iProver_top
% 3.57/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_544]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_19,plain,
% 3.57/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.57/0.99      | ~ v1_funct_1(X1)
% 3.57/0.99      | ~ v1_relat_1(X1)
% 3.57/0.99      | k1_funct_1(X1,sK3(X1,X2,X0)) = X0 ),
% 3.57/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_528,plain,
% 3.57/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.57/0.99      | ~ v1_relat_1(X1)
% 3.57/0.99      | k1_funct_1(X1,sK3(X1,X2,X0)) = X0
% 3.57/0.99      | sK7 != X1 ),
% 3.57/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_36]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_529,plain,
% 3.57/0.99      ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
% 3.57/0.99      | ~ v1_relat_1(sK7)
% 3.57/0.99      | k1_funct_1(sK7,sK3(sK7,X1,X0)) = X0 ),
% 3.57/0.99      inference(unflattening,[status(thm)],[c_528]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1736,plain,
% 3.57/0.99      ( k1_funct_1(sK7,sK3(sK7,X0,X1)) = X1
% 3.57/0.99      | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top
% 3.57/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_529]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_2464,plain,
% 3.57/0.99      ( k1_funct_1(sK7,sK3(sK7,X0,k1_funct_1(sK7,X1))) = k1_funct_1(sK7,X1)
% 3.57/0.99      | r2_hidden(X1,X0) != iProver_top
% 3.57/0.99      | r2_hidden(X1,k1_relat_1(sK7)) != iProver_top
% 3.57/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_1735,c_1736]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_6707,plain,
% 3.57/0.99      ( r2_hidden(X1,k1_relat_1(sK7)) != iProver_top
% 3.57/0.99      | r2_hidden(X1,X0) != iProver_top
% 3.57/0.99      | k1_funct_1(sK7,sK3(sK7,X0,k1_funct_1(sK7,X1))) = k1_funct_1(sK7,X1) ),
% 3.57/0.99      inference(global_propositional_subsumption,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_2464,c_3011,c_4335,c_4818]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_6708,plain,
% 3.57/0.99      ( k1_funct_1(sK7,sK3(sK7,X0,k1_funct_1(sK7,X1))) = k1_funct_1(sK7,X1)
% 3.57/0.99      | r2_hidden(X1,X0) != iProver_top
% 3.57/0.99      | r2_hidden(X1,k1_relat_1(sK7)) != iProver_top ),
% 3.57/0.99      inference(renaming,[status(thm)],[c_6707]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_6711,plain,
% 3.57/0.99      ( k1_funct_1(sK7,sK3(sK7,X0,k1_funct_1(sK7,X1))) = k1_funct_1(sK7,X1)
% 3.57/0.99      | r2_hidden(X1,X0) != iProver_top
% 3.57/0.99      | r2_hidden(X1,sK4) != iProver_top ),
% 3.57/0.99      inference(light_normalisation,[status(thm)],[c_6708,c_4072]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_6717,plain,
% 3.57/0.99      ( k1_funct_1(sK7,sK3(sK7,X0,k1_funct_1(sK7,sK3(sK7,X0,X1)))) = k1_funct_1(sK7,sK3(sK7,X0,X1))
% 3.57/0.99      | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top
% 3.57/0.99      | r2_hidden(sK3(sK7,X0,X1),sK4) != iProver_top
% 3.57/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_1737,c_6711]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_10846,plain,
% 3.57/0.99      ( r2_hidden(sK3(sK7,X0,X1),sK4) != iProver_top
% 3.57/0.99      | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top
% 3.57/0.99      | k1_funct_1(sK7,sK3(sK7,X0,k1_funct_1(sK7,sK3(sK7,X0,X1)))) = k1_funct_1(sK7,sK3(sK7,X0,X1)) ),
% 3.57/0.99      inference(global_propositional_subsumption,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_6717,c_3011,c_4335,c_4818]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_10847,plain,
% 3.57/0.99      ( k1_funct_1(sK7,sK3(sK7,X0,k1_funct_1(sK7,sK3(sK7,X0,X1)))) = k1_funct_1(sK7,sK3(sK7,X0,X1))
% 3.57/0.99      | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top
% 3.57/0.99      | r2_hidden(sK3(sK7,X0,X1),sK4) != iProver_top ),
% 3.57/0.99      inference(renaming,[status(thm)],[c_10846]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_10853,plain,
% 3.57/0.99      ( k1_funct_1(sK7,sK3(sK7,X0,k1_funct_1(sK7,sK3(sK7,X0,X1)))) = k1_funct_1(sK7,sK3(sK7,X0,X1))
% 3.57/0.99      | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top ),
% 3.57/0.99      inference(forward_subsumption_resolution,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_10847,c_5855]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_10863,plain,
% 3.57/0.99      ( k1_funct_1(sK7,sK3(sK7,sK6,k1_funct_1(sK7,sK3(sK7,sK6,sK8)))) = k1_funct_1(sK7,sK3(sK7,sK6,sK8)) ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_3298,c_10853]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_32,negated_conjecture,
% 3.57/0.99      ( ~ r2_hidden(X0,sK4)
% 3.57/0.99      | ~ r2_hidden(X0,sK6)
% 3.57/0.99      | k1_funct_1(sK7,X0) != sK8 ),
% 3.57/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1742,plain,
% 3.57/0.99      ( k1_funct_1(sK7,X0) != sK8
% 3.57/0.99      | r2_hidden(X0,sK4) != iProver_top
% 3.57/0.99      | r2_hidden(X0,sK6) != iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_10980,plain,
% 3.57/0.99      ( k1_funct_1(sK7,sK3(sK7,sK6,sK8)) != sK8
% 3.57/0.99      | r2_hidden(sK3(sK7,sK6,k1_funct_1(sK7,sK3(sK7,sK6,sK8))),sK4) != iProver_top
% 3.57/0.99      | r2_hidden(sK3(sK7,sK6,k1_funct_1(sK7,sK3(sK7,sK6,sK8))),sK6) != iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_10863,c_1742]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3012,plain,
% 3.57/0.99      ( r1_tarski(sK7,k2_zfmisc_1(sK4,sK5)) ),
% 3.57/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3011]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3377,plain,
% 3.57/0.99      ( k1_funct_1(sK7,sK3(sK7,sK6,sK8)) = sK8
% 3.57/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_3298,c_1736]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3392,plain,
% 3.57/0.99      ( ~ v1_relat_1(sK7) | k1_funct_1(sK7,sK3(sK7,sK6,sK8)) = sK8 ),
% 3.57/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3377]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_10998,plain,
% 3.57/0.99      ( r2_hidden(sK3(sK7,sK6,k1_funct_1(sK7,sK3(sK7,sK6,sK8))),sK4) != iProver_top
% 3.57/0.99      | r2_hidden(sK3(sK7,sK6,k1_funct_1(sK7,sK3(sK7,sK6,sK8))),sK6) != iProver_top ),
% 3.57/0.99      inference(global_propositional_subsumption,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_10980,c_3012,c_3392,c_4334,c_4817]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_11004,plain,
% 3.57/0.99      ( r2_hidden(sK3(sK7,sK6,k1_funct_1(sK7,sK3(sK7,sK6,sK8))),sK6) != iProver_top
% 3.57/0.99      | r2_hidden(k1_funct_1(sK7,sK3(sK7,sK6,sK8)),k9_relat_1(sK7,sK6)) != iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_5855,c_10998]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_40,plain,
% 3.57/0.99      ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_2068,plain,
% 3.57/0.99      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.57/0.99      | k7_relset_1(sK4,sK5,sK7,X0) = k9_relat_1(sK7,X0) ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_25]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3054,plain,
% 3.57/0.99      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.57/0.99      | k7_relset_1(sK4,sK5,sK7,sK6) = k9_relat_1(sK7,sK6) ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_2068]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1031,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_2978,plain,
% 3.57/0.99      ( X0 != X1
% 3.57/0.99      | X0 = k7_relset_1(sK4,sK5,sK7,sK6)
% 3.57/0.99      | k7_relset_1(sK4,sK5,sK7,sK6) != X1 ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_1031]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3971,plain,
% 3.57/0.99      ( X0 = k7_relset_1(sK4,sK5,sK7,sK6)
% 3.57/0.99      | X0 != k9_relat_1(sK7,sK6)
% 3.57/0.99      | k7_relset_1(sK4,sK5,sK7,sK6) != k9_relat_1(sK7,sK6) ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_2978]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_4734,plain,
% 3.57/0.99      ( k7_relset_1(sK4,sK5,sK7,sK6) != k9_relat_1(sK7,sK6)
% 3.57/0.99      | k9_relat_1(sK7,sK6) = k7_relset_1(sK4,sK5,sK7,sK6)
% 3.57/0.99      | k9_relat_1(sK7,sK6) != k9_relat_1(sK7,sK6) ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_3971]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1030,plain,( X0 = X0 ),theory(equality) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_4735,plain,
% 3.57/0.99      ( k9_relat_1(sK7,sK6) = k9_relat_1(sK7,sK6) ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_1030]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1032,plain,
% 3.57/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.57/0.99      theory(equality) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_2044,plain,
% 3.57/0.99      ( r2_hidden(X0,X1)
% 3.57/0.99      | ~ r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))
% 3.57/0.99      | X1 != k7_relset_1(sK4,sK5,sK7,sK6)
% 3.57/0.99      | X0 != sK8 ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_1032]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_9138,plain,
% 3.57/0.99      ( r2_hidden(X0,k9_relat_1(sK7,sK6))
% 3.57/0.99      | ~ r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))
% 3.57/0.99      | X0 != sK8
% 3.57/0.99      | k9_relat_1(sK7,sK6) != k7_relset_1(sK4,sK5,sK7,sK6) ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_2044]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_10763,plain,
% 3.57/0.99      ( r2_hidden(k1_funct_1(sK7,sK3(sK7,sK6,sK8)),k9_relat_1(sK7,sK6))
% 3.57/0.99      | ~ r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))
% 3.57/0.99      | k1_funct_1(sK7,sK3(sK7,sK6,sK8)) != sK8
% 3.57/0.99      | k9_relat_1(sK7,sK6) != k7_relset_1(sK4,sK5,sK7,sK6) ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_9138]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_10764,plain,
% 3.57/0.99      ( k1_funct_1(sK7,sK3(sK7,sK6,sK8)) != sK8
% 3.57/0.99      | k9_relat_1(sK7,sK6) != k7_relset_1(sK4,sK5,sK7,sK6)
% 3.57/0.99      | r2_hidden(k1_funct_1(sK7,sK3(sK7,sK6,sK8)),k9_relat_1(sK7,sK6)) = iProver_top
% 3.57/0.99      | r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) != iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_10763]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_11201,plain,
% 3.57/0.99      ( r2_hidden(sK3(sK7,sK6,k1_funct_1(sK7,sK3(sK7,sK6,sK8))),sK6) != iProver_top ),
% 3.57/0.99      inference(global_propositional_subsumption,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_11004,c_34,c_40,c_3012,c_3054,c_3392,c_4334,c_4734,
% 3.57/0.99                 c_4735,c_4817,c_10764]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_11206,plain,
% 3.57/0.99      ( r2_hidden(k1_funct_1(sK7,sK3(sK7,sK6,sK8)),k9_relat_1(sK7,sK6)) != iProver_top
% 3.57/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_1737,c_11201]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(contradiction,plain,
% 3.57/0.99      ( $false ),
% 3.57/0.99      inference(minisat,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_11206,c_10764,c_4818,c_4817,c_4735,c_4734,c_4335,
% 3.57/0.99                 c_4334,c_3392,c_3054,c_3012,c_3011,c_40,c_34]) ).
% 3.57/0.99  
% 3.57/0.99  
% 3.57/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.57/0.99  
% 3.57/0.99  ------                               Statistics
% 3.57/0.99  
% 3.57/0.99  ------ General
% 3.57/0.99  
% 3.57/0.99  abstr_ref_over_cycles:                  0
% 3.57/0.99  abstr_ref_under_cycles:                 0
% 3.57/0.99  gc_basic_clause_elim:                   0
% 3.57/0.99  forced_gc_time:                         0
% 3.57/0.99  parsing_time:                           0.011
% 3.57/0.99  unif_index_cands_time:                  0.
% 3.57/0.99  unif_index_add_time:                    0.
% 3.57/0.99  orderings_time:                         0.
% 3.57/0.99  out_proof_time:                         0.012
% 3.57/0.99  total_time:                             0.303
% 3.57/0.99  num_of_symbols:                         55
% 3.57/0.99  num_of_terms:                           8534
% 3.57/0.99  
% 3.57/0.99  ------ Preprocessing
% 3.57/0.99  
% 3.57/0.99  num_of_splits:                          0
% 3.57/0.99  num_of_split_atoms:                     0
% 3.57/0.99  num_of_reused_defs:                     0
% 3.57/0.99  num_eq_ax_congr_red:                    40
% 3.57/0.99  num_of_sem_filtered_clauses:            1
% 3.57/0.99  num_of_subtypes:                        0
% 3.57/0.99  monotx_restored_types:                  0
% 3.57/0.99  sat_num_of_epr_types:                   0
% 3.57/0.99  sat_num_of_non_cyclic_types:            0
% 3.57/0.99  sat_guarded_non_collapsed_types:        0
% 3.57/0.99  num_pure_diseq_elim:                    0
% 3.57/0.99  simp_replaced_by:                       0
% 3.57/0.99  res_preprocessed:                       162
% 3.57/0.99  prep_upred:                             0
% 3.57/0.99  prep_unflattend:                        35
% 3.57/0.99  smt_new_axioms:                         0
% 3.57/0.99  pred_elim_cands:                        5
% 3.57/0.99  pred_elim:                              2
% 3.57/0.99  pred_elim_cl:                           5
% 3.57/0.99  pred_elim_cycles:                       5
% 3.57/0.99  merged_defs:                            8
% 3.57/0.99  merged_defs_ncl:                        0
% 3.57/0.99  bin_hyper_res:                          9
% 3.57/0.99  prep_cycles:                            4
% 3.57/0.99  pred_elim_time:                         0.006
% 3.57/0.99  splitting_time:                         0.
% 3.57/0.99  sem_filter_time:                        0.
% 3.57/0.99  monotx_time:                            0.001
% 3.57/0.99  subtype_inf_time:                       0.
% 3.57/0.99  
% 3.57/0.99  ------ Problem properties
% 3.57/0.99  
% 3.57/0.99  clauses:                                31
% 3.57/0.99  conjectures:                            3
% 3.57/0.99  epr:                                    8
% 3.57/0.99  horn:                                   24
% 3.57/0.99  ground:                                 5
% 3.57/0.99  unary:                                  5
% 3.57/0.99  binary:                                 10
% 3.57/0.99  lits:                                   81
% 3.57/0.99  lits_eq:                                18
% 3.57/0.99  fd_pure:                                0
% 3.57/0.99  fd_pseudo:                              0
% 3.57/0.99  fd_cond:                                0
% 3.57/0.99  fd_pseudo_cond:                         5
% 3.57/0.99  ac_symbols:                             0
% 3.57/0.99  
% 3.57/0.99  ------ Propositional Solver
% 3.57/0.99  
% 3.57/0.99  prop_solver_calls:                      30
% 3.57/0.99  prop_fast_solver_calls:                 1248
% 3.57/0.99  smt_solver_calls:                       0
% 3.57/0.99  smt_fast_solver_calls:                  0
% 3.57/0.99  prop_num_of_clauses:                    3966
% 3.57/0.99  prop_preprocess_simplified:             9164
% 3.57/0.99  prop_fo_subsumed:                       42
% 3.57/0.99  prop_solver_time:                       0.
% 3.57/0.99  smt_solver_time:                        0.
% 3.57/0.99  smt_fast_solver_time:                   0.
% 3.57/0.99  prop_fast_solver_time:                  0.
% 3.57/0.99  prop_unsat_core_time:                   0.
% 3.57/0.99  
% 3.57/0.99  ------ QBF
% 3.57/0.99  
% 3.57/0.99  qbf_q_res:                              0
% 3.57/0.99  qbf_num_tautologies:                    0
% 3.57/0.99  qbf_prep_cycles:                        0
% 3.57/0.99  
% 3.57/0.99  ------ BMC1
% 3.57/0.99  
% 3.57/0.99  bmc1_current_bound:                     -1
% 3.57/0.99  bmc1_last_solved_bound:                 -1
% 3.57/0.99  bmc1_unsat_core_size:                   -1
% 3.57/0.99  bmc1_unsat_core_parents_size:           -1
% 3.57/0.99  bmc1_merge_next_fun:                    0
% 3.57/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.57/0.99  
% 3.57/0.99  ------ Instantiation
% 3.57/0.99  
% 3.57/0.99  inst_num_of_clauses:                    920
% 3.57/0.99  inst_num_in_passive:                    428
% 3.57/0.99  inst_num_in_active:                     395
% 3.57/0.99  inst_num_in_unprocessed:                97
% 3.57/0.99  inst_num_of_loops:                      550
% 3.57/0.99  inst_num_of_learning_restarts:          0
% 3.57/0.99  inst_num_moves_active_passive:          151
% 3.57/0.99  inst_lit_activity:                      0
% 3.57/0.99  inst_lit_activity_moves:                0
% 3.57/0.99  inst_num_tautologies:                   0
% 3.57/0.99  inst_num_prop_implied:                  0
% 3.57/0.99  inst_num_existing_simplified:           0
% 3.57/0.99  inst_num_eq_res_simplified:             0
% 3.57/0.99  inst_num_child_elim:                    0
% 3.57/0.99  inst_num_of_dismatching_blockings:      309
% 3.57/0.99  inst_num_of_non_proper_insts:           1084
% 3.57/0.99  inst_num_of_duplicates:                 0
% 3.57/0.99  inst_inst_num_from_inst_to_res:         0
% 3.57/0.99  inst_dismatching_checking_time:         0.
% 3.57/0.99  
% 3.57/0.99  ------ Resolution
% 3.57/0.99  
% 3.57/0.99  res_num_of_clauses:                     0
% 3.57/0.99  res_num_in_passive:                     0
% 3.57/0.99  res_num_in_active:                      0
% 3.57/0.99  res_num_of_loops:                       166
% 3.57/0.99  res_forward_subset_subsumed:            93
% 3.57/0.99  res_backward_subset_subsumed:           8
% 3.57/0.99  res_forward_subsumed:                   0
% 3.57/0.99  res_backward_subsumed:                  0
% 3.57/0.99  res_forward_subsumption_resolution:     0
% 3.57/0.99  res_backward_subsumption_resolution:    0
% 3.57/0.99  res_clause_to_clause_subsumption:       1130
% 3.57/0.99  res_orphan_elimination:                 0
% 3.57/0.99  res_tautology_del:                      142
% 3.57/0.99  res_num_eq_res_simplified:              0
% 3.57/0.99  res_num_sel_changes:                    0
% 3.57/0.99  res_moves_from_active_to_pass:          0
% 3.57/0.99  
% 3.57/0.99  ------ Superposition
% 3.57/0.99  
% 3.57/0.99  sup_time_total:                         0.
% 3.57/0.99  sup_time_generating:                    0.
% 3.57/0.99  sup_time_sim_full:                      0.
% 3.57/0.99  sup_time_sim_immed:                     0.
% 3.57/0.99  
% 3.57/0.99  sup_num_of_clauses:                     350
% 3.57/0.99  sup_num_in_active:                      95
% 3.57/0.99  sup_num_in_passive:                     255
% 3.57/0.99  sup_num_of_loops:                       108
% 3.57/0.99  sup_fw_superposition:                   243
% 3.57/0.99  sup_bw_superposition:                   142
% 3.57/0.99  sup_immediate_simplified:               40
% 3.57/0.99  sup_given_eliminated:                   4
% 3.57/0.99  comparisons_done:                       0
% 3.57/0.99  comparisons_avoided:                    4
% 3.57/0.99  
% 3.57/0.99  ------ Simplifications
% 3.57/0.99  
% 3.57/0.99  
% 3.57/0.99  sim_fw_subset_subsumed:                 24
% 3.57/0.99  sim_bw_subset_subsumed:                 2
% 3.57/0.99  sim_fw_subsumed:                        15
% 3.57/0.99  sim_bw_subsumed:                        1
% 3.57/0.99  sim_fw_subsumption_res:                 1
% 3.57/0.99  sim_bw_subsumption_res:                 0
% 3.57/0.99  sim_tautology_del:                      4
% 3.57/0.99  sim_eq_tautology_del:                   3
% 3.57/0.99  sim_eq_res_simp:                        0
% 3.57/0.99  sim_fw_demodulated:                     0
% 3.57/0.99  sim_bw_demodulated:                     13
% 3.57/0.99  sim_light_normalised:                   2
% 3.57/0.99  sim_joinable_taut:                      0
% 3.57/0.99  sim_joinable_simp:                      0
% 3.57/0.99  sim_ac_normalised:                      0
% 3.57/0.99  sim_smt_subsumption:                    0
% 3.57/0.99  
%------------------------------------------------------------------------------
