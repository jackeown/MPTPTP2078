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
% DateTime   : Thu Dec  3 12:00:51 EST 2020

% Result     : Theorem 55.69s
% Output     : CNFRefutation 55.69s
% Verified   : 
% Statistics : Number of formulae       :  181 (2990 expanded)
%              Number of clauses        :  114 ( 907 expanded)
%              Number of leaves         :   23 ( 784 expanded)
%              Depth                    :   28
%              Number of atoms          :  621 (15406 expanded)
%              Number of equality atoms :  342 (5491 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( ! [X4] :
                    ~ ( k1_funct_1(X2,X4) = X3
                      & r2_hidden(X4,X0) )
                & r2_hidden(X3,X1) )
         => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f43,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) = X3
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK11(X3)) = X3
        & r2_hidden(sK11(X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(X0,X1,X2) != X1
        & ! [X3] :
            ( ? [X4] :
                ( k1_funct_1(X2,X4) = X3
                & r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( k2_relset_1(sK8,sK9,sK10) != sK9
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK10,X4) = X3
              & r2_hidden(X4,sK8) )
          | ~ r2_hidden(X3,sK9) )
      & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
      & v1_funct_2(sK10,sK8,sK9)
      & v1_funct_1(sK10) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( k2_relset_1(sK8,sK9,sK10) != sK9
    & ! [X3] :
        ( ( k1_funct_1(sK10,sK11(X3)) = X3
          & r2_hidden(sK11(X3),sK8) )
        | ~ r2_hidden(X3,sK9) )
    & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
    & v1_funct_2(sK10,sK8,sK9)
    & v1_funct_1(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f22,f43,f42])).

fof(f72,plain,(
    v1_funct_2(sK10,sK8,sK9) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
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

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f73,plain,(
    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
              | ~ r2_hidden(X3,X1) )
          | k2_relset_1(X0,X1,X2) != X1 )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ? [X3] :
              ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
              | ~ r2_hidden(X3,X1) )
          | k2_relset_1(X0,X1,X2) != X1 )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ? [X5] :
              ( ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X2)
              & r2_hidden(X5,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(rectify,[],[f36])).

fof(f39,plain,(
    ! [X2,X1] :
      ( ? [X5] :
          ( ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X2)
          & r2_hidden(X5,X1) )
     => ( ! [X6] : ~ r2_hidden(k4_tarski(X6,sK7(X1,X2)),X2)
        & r2_hidden(sK7(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
     => r2_hidden(k4_tarski(sK6(X2,X3),X3),X2) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(sK6(X2,X3),X3),X2)
              | ~ r2_hidden(X3,X1) )
          | k2_relset_1(X0,X1,X2) != X1 )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(X6,sK7(X1,X2)),X2)
            & r2_hidden(sK7(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f37,f39,f38])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | r2_hidden(sK7(X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f76,plain,(
    k2_relset_1(sK8,sK9,sK10) != sK9 ),
    inference(cnf_transformation,[],[f44])).

fof(f75,plain,(
    ! [X3] :
      ( k1_funct_1(sK10,sK11(X3)) = X3
      | ~ r2_hidden(X3,sK9) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
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

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f34,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X5)) = X5
        & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) = X2
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
              ( k1_funct_1(X0,X3) != sK3(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK3(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK3(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK3(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK4(X0,X1)) = sK3(X0,X1)
                  & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK3(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK5(X0,X5)) = X5
                    & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f31,f34,f33,f32])).

fof(f55,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f79,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f80,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f79])).

fof(f71,plain,(
    v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f23])).

fof(f27,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK2(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK1(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK0(X0,X1)),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK0(X0,X1)),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK0(X0,X1)),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK2(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27,f26,f25])).

fof(f45,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f78,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK2(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f63,plain,(
    ! [X6,X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_hidden(k4_tarski(X6,sK7(X1,X2)),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f74,plain,(
    ! [X3] :
      ( r2_hidden(sK11(X3),sK8)
      | ~ r2_hidden(X3,sK9) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f85,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f69])).

fof(f2,axiom,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f87,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f66])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k2_relat_1(X0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k2_relat_1(X0) = k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k2_relat_1(X0) != k1_xboole_0 )
        & ( k2_relat_1(X0) = k1_xboole_0
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f51,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_xboole_0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK10,sK8,sK9) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_464,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
    | sK10 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_29])).

cnf(c_465,plain,
    ( ~ v1_funct_2(sK10,X0,X1)
    | k1_relset_1(X0,X1,sK10) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_464])).

cnf(c_847,plain,
    ( k1_relset_1(X0,X1,sK10) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
    | sK10 != sK10
    | sK9 != X1
    | sK8 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_465])).

cnf(c_848,plain,
    ( k1_relset_1(sK8,sK9,sK10) = sK8
    | k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
    | k1_xboole_0 = sK9 ),
    inference(unflattening,[status(thm)],[c_847])).

cnf(c_919,plain,
    ( k1_relset_1(sK8,sK9,sK10) = sK8
    | k1_xboole_0 = sK9 ),
    inference(equality_resolution_simp,[status(thm)],[c_848])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_557,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
    | sK10 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_29])).

cnf(c_558,plain,
    ( k1_relset_1(X0,X1,sK10) = k1_relat_1(sK10)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)) ),
    inference(unflattening,[status(thm)],[c_557])).

cnf(c_255132,plain,
    ( k1_relset_1(sK8,sK9,sK10) = k1_relat_1(sK10) ),
    inference(equality_resolution,[status(thm)],[c_558])).

cnf(c_255171,plain,
    ( k1_relat_1(sK10) = sK8
    | sK9 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_919,c_255132])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(sK7(X2,X0),X2)
    | k2_relset_1(X1,X2,X0) = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_500,plain,
    ( r2_hidden(sK7(X0,X1),X0)
    | k2_relset_1(X2,X0,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X2,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
    | sK10 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_29])).

cnf(c_501,plain,
    ( r2_hidden(sK7(X0,sK10),X0)
    | k2_relset_1(X1,X0,sK10) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)) ),
    inference(unflattening,[status(thm)],[c_500])).

cnf(c_255038,plain,
    ( k2_relset_1(X0,X1,sK10) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
    | r2_hidden(sK7(X1,sK10),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_501])).

cnf(c_255193,plain,
    ( k2_relset_1(sK8,sK9,sK10) = sK9
    | r2_hidden(sK7(sK9,sK10),sK9) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_255038])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_548,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
    | sK10 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_29])).

cnf(c_549,plain,
    ( k2_relset_1(X0,X1,sK10) = k2_relat_1(sK10)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)) ),
    inference(unflattening,[status(thm)],[c_548])).

cnf(c_255118,plain,
    ( k2_relset_1(sK8,sK9,sK10) = k2_relat_1(sK10) ),
    inference(equality_resolution,[status(thm)],[c_549])).

cnf(c_255194,plain,
    ( k2_relat_1(sK10) = sK9
    | r2_hidden(sK7(sK9,sK10),sK9) = iProver_top ),
    inference(demodulation,[status(thm)],[c_255193,c_255118])).

cnf(c_26,negated_conjecture,
    ( k2_relset_1(sK8,sK9,sK10) != sK9 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_49649,plain,
    ( r2_hidden(sK7(sK9,sK10),sK9)
    | k2_relset_1(sK8,sK9,sK10) = sK9
    | k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_501])).

cnf(c_49650,plain,
    ( k2_relset_1(sK8,sK9,sK10) = sK9
    | k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
    | r2_hidden(sK7(sK9,sK10),sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49649])).

cnf(c_1168,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_49765,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)) = k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_1168])).

cnf(c_255212,plain,
    ( r2_hidden(sK7(sK9,sK10),sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_255194,c_26,c_49650,c_49765])).

cnf(c_27,negated_conjecture,
    ( ~ r2_hidden(X0,sK9)
    | k1_funct_1(sK10,sK11(X0)) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_255039,plain,
    ( k1_funct_1(sK10,sK11(X0)) = X0
    | r2_hidden(X0,sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_255217,plain,
    ( k1_funct_1(sK10,sK11(sK7(sK9,sK10))) = sK7(sK9,sK10) ),
    inference(superposition,[status(thm)],[c_255212,c_255039])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_400,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK10 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_31])).

cnf(c_401,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK10))
    | r2_hidden(k1_funct_1(sK10,X0),k2_relat_1(sK10))
    | ~ v1_relat_1(sK10) ),
    inference(unflattening,[status(thm)],[c_400])).

cnf(c_49451,plain,
    ( r2_hidden(X0,k1_relat_1(sK10)) != iProver_top
    | r2_hidden(k1_funct_1(sK10,X0),k2_relat_1(sK10)) = iProver_top
    | v1_relat_1(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_401])).

cnf(c_402,plain,
    ( r2_hidden(X0,k1_relat_1(sK10)) != iProver_top
    | r2_hidden(k1_funct_1(sK10,X0),k2_relat_1(sK10)) = iProver_top
    | v1_relat_1(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_401])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_566,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_29])).

cnf(c_567,plain,
    ( v1_relat_1(sK10)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)) ),
    inference(unflattening,[status(thm)],[c_566])).

cnf(c_49448,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
    | v1_relat_1(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_567])).

cnf(c_49659,plain,
    ( v1_relat_1(sK10) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_49448])).

cnf(c_49685,plain,
    ( r2_hidden(k1_funct_1(sK10,X0),k2_relat_1(sK10)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK10)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_49451,c_402,c_49659])).

cnf(c_49686,plain,
    ( r2_hidden(X0,k1_relat_1(sK10)) != iProver_top
    | r2_hidden(k1_funct_1(sK10,X0),k2_relat_1(sK10)) = iProver_top ),
    inference(renaming,[status(thm)],[c_49685])).

cnf(c_49687,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK10))
    | r2_hidden(k1_funct_1(sK10,X0),k2_relat_1(sK10)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_49686])).

cnf(c_254944,plain,
    ( r2_hidden(k1_funct_1(sK10,X0),k2_relat_1(sK10))
    | ~ r2_hidden(X0,k1_relat_1(sK10)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_401,c_49687])).

cnf(c_254945,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK10))
    | r2_hidden(k1_funct_1(sK10,X0),k2_relat_1(sK10)) ),
    inference(renaming,[status(thm)],[c_254944])).

cnf(c_255035,plain,
    ( r2_hidden(X0,k1_relat_1(sK10)) != iProver_top
    | r2_hidden(k1_funct_1(sK10,X0),k2_relat_1(sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_254945])).

cnf(c_255219,plain,
    ( r2_hidden(sK7(sK9,sK10),k2_relat_1(sK10)) = iProver_top
    | r2_hidden(sK11(sK7(sK9,sK10)),k1_relat_1(sK10)) != iProver_top ),
    inference(superposition,[status(thm)],[c_255217,c_255035])).

cnf(c_49450,plain,
    ( k2_relset_1(X0,X1,sK10) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
    | r2_hidden(sK7(X1,sK10),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_501])).

cnf(c_49950,plain,
    ( k2_relset_1(sK8,sK9,sK10) = sK9
    | r2_hidden(sK7(sK9,sK10),sK9) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_49450])).

cnf(c_49644,plain,
    ( k2_relset_1(sK8,sK9,sK10) = k2_relat_1(sK10) ),
    inference(equality_resolution,[status(thm)],[c_549])).

cnf(c_49951,plain,
    ( k2_relat_1(sK10) = sK9
    | r2_hidden(sK7(sK9,sK10),sK9) = iProver_top ),
    inference(demodulation,[status(thm)],[c_49950,c_49644])).

cnf(c_50500,plain,
    ( r2_hidden(sK7(sK9,sK10),sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_49951,c_26,c_49650,c_49765])).

cnf(c_49454,plain,
    ( k1_funct_1(sK10,sK11(X0)) = X0
    | r2_hidden(X0,sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_50505,plain,
    ( k1_funct_1(sK10,sK11(sK7(sK9,sK10))) = sK7(sK9,sK10) ),
    inference(superposition,[status(thm)],[c_50500,c_49454])).

cnf(c_50524,plain,
    ( r2_hidden(sK7(sK9,sK10),k2_relat_1(sK10)) = iProver_top
    | r2_hidden(sK11(sK7(sK9,sK10)),k1_relat_1(sK10)) != iProver_top ),
    inference(superposition,[status(thm)],[c_50505,c_49686])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK2(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_255041,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(sK2(X1,X0),X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(k4_tarski(X3,sK7(X2,X0)),X0)
    | k2_relset_1(X1,X2,X0) = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_515,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK7(X1,X2)),X2)
    | k2_relset_1(X3,X1,X2) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X3,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
    | sK10 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_29])).

cnf(c_516,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK7(X1,sK10)),sK10)
    | k2_relset_1(X2,X1,sK10) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)) ),
    inference(unflattening,[status(thm)],[c_515])).

cnf(c_255037,plain,
    ( k2_relset_1(X0,X1,sK10) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
    | r2_hidden(k4_tarski(X2,sK7(X1,sK10)),sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_516])).

cnf(c_255182,plain,
    ( k2_relset_1(sK8,sK9,sK10) = sK9
    | r2_hidden(k4_tarski(X0,sK7(sK9,sK10)),sK10) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_255037])).

cnf(c_255183,plain,
    ( k2_relat_1(sK10) = sK9
    | r2_hidden(k4_tarski(X0,sK7(sK9,sK10)),sK10) != iProver_top ),
    inference(demodulation,[status(thm)],[c_255182,c_255118])).

cnf(c_49653,plain,
    ( k2_relat_1(sK10) != sK9 ),
    inference(demodulation,[status(thm)],[c_49644,c_26])).

cnf(c_49449,plain,
    ( k2_relset_1(X0,X1,sK10) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
    | r2_hidden(k4_tarski(X2,sK7(X1,sK10)),sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_516])).

cnf(c_49748,plain,
    ( k2_relset_1(sK8,sK9,sK10) = sK9
    | r2_hidden(k4_tarski(X0,sK7(sK9,sK10)),sK10) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_49449])).

cnf(c_49749,plain,
    ( k2_relat_1(sK10) = sK9
    | r2_hidden(k4_tarski(X0,sK7(sK9,sK10)),sK10) != iProver_top ),
    inference(demodulation,[status(thm)],[c_49748,c_49644])).

cnf(c_255199,plain,
    ( r2_hidden(k4_tarski(X0,sK7(sK9,sK10)),sK10) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_255183,c_49653,c_49749])).

cnf(c_255225,plain,
    ( r2_hidden(sK7(sK9,sK10),k2_relat_1(sK10)) != iProver_top ),
    inference(superposition,[status(thm)],[c_255041,c_255199])).

cnf(c_255263,plain,
    ( r2_hidden(sK11(sK7(sK9,sK10)),k1_relat_1(sK10)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_255219,c_50524,c_255225])).

cnf(c_255268,plain,
    ( sK9 = k1_xboole_0
    | r2_hidden(sK11(sK7(sK9,sK10)),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_255171,c_255263])).

cnf(c_28,negated_conjecture,
    ( ~ r2_hidden(X0,sK9)
    | r2_hidden(sK11(X0),sK8) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_53198,plain,
    ( ~ r2_hidden(sK7(sK9,sK10),sK9)
    | r2_hidden(sK11(sK7(sK9,sK10)),sK8) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_53202,plain,
    ( r2_hidden(sK7(sK9,sK10),sK9) != iProver_top
    | r2_hidden(sK11(sK7(sK9,sK10)),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53198])).

cnf(c_255272,plain,
    ( sK9 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_255268,c_26,c_49650,c_49765,c_53202])).

cnf(c_255285,plain,
    ( k1_relset_1(sK8,k1_xboole_0,sK10) = k1_relat_1(sK10) ),
    inference(demodulation,[status(thm)],[c_255272,c_255132])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_595,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
    | sK10 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_29])).

cnf(c_596,plain,
    ( ~ v1_funct_2(sK10,X0,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK10 ),
    inference(unflattening,[status(thm)],[c_595])).

cnf(c_858,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
    | sK10 != sK10
    | sK10 = k1_xboole_0
    | sK9 != k1_xboole_0
    | sK8 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_596])).

cnf(c_859,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK8,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
    | sK10 = k1_xboole_0
    | sK9 != k1_xboole_0
    | k1_xboole_0 = sK8 ),
    inference(unflattening,[status(thm)],[c_858])).

cnf(c_4,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1201,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1168])).

cnf(c_1170,plain,
    ( X0 != X1
    | k2_relat_1(X0) = k2_relat_1(X1) ),
    theory(equality)).

cnf(c_53598,plain,
    ( X0 != k1_xboole_0
    | k2_relat_1(X0) = k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1170])).

cnf(c_54220,plain,
    ( k2_relat_1(sK10) = k2_relat_1(k1_xboole_0)
    | sK10 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_53598])).

cnf(c_1169,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_53596,plain,
    ( X0 = X1
    | X1 != k1_xboole_0
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1169])).

cnf(c_54165,plain,
    ( X0 != k1_xboole_0
    | k2_relat_1(sK10) = X0
    | k2_relat_1(sK10) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_53596])).

cnf(c_89221,plain,
    ( k2_relat_1(sK10) = sK9
    | k2_relat_1(sK10) != k1_xboole_0
    | sK9 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_54165])).

cnf(c_87363,plain,
    ( X0 != X1
    | k2_relat_1(sK10) != X1
    | k2_relat_1(sK10) = X0 ),
    inference(instantiation,[status(thm)],[c_1169])).

cnf(c_165216,plain,
    ( X0 != k2_relat_1(k1_xboole_0)
    | k2_relat_1(sK10) = X0
    | k2_relat_1(sK10) != k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_87363])).

cnf(c_165217,plain,
    ( k2_relat_1(sK10) != k2_relat_1(k1_xboole_0)
    | k2_relat_1(sK10) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_165216])).

cnf(c_239770,plain,
    ( X0 = k2_relat_1(X1)
    | X0 != k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_53596])).

cnf(c_239771,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_239770])).

cnf(c_254955,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK8,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
    | sK9 != k1_xboole_0
    | k1_xboole_0 = sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_859,c_4,c_1201,c_49653,c_54220,c_89221,c_165217,c_239771])).

cnf(c_255290,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK8,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK8,k1_xboole_0))
    | sK8 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_255272,c_254955])).

cnf(c_255306,plain,
    ( sK8 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_255290])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_613,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_29])).

cnf(c_614,plain,
    ( ~ v1_funct_2(sK10,k1_xboole_0,X0)
    | k1_relset_1(k1_xboole_0,X0,sK10) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)) ),
    inference(unflattening,[status(thm)],[c_613])).

cnf(c_872,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK10) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
    | sK10 != sK10
    | sK9 != X0
    | sK8 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_614])).

cnf(c_873,plain,
    ( k1_relset_1(k1_xboole_0,sK9,sK10) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK9)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
    | sK8 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_872])).

cnf(c_255289,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK10) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(sK8,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | sK8 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_255272,c_873])).

cnf(c_255319,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK10) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_255289,c_255306])).

cnf(c_255320,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK10) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_255319])).

cnf(c_255328,plain,
    ( k1_relat_1(sK10) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_255285,c_255306,c_255320])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k2_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_49815,plain,
    ( ~ v1_relat_1(sK10)
    | k1_relat_1(sK10) != k1_xboole_0
    | k2_relat_1(sK10) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_49660,plain,
    ( v1_relat_1(sK10) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_49659])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_255328,c_255268,c_89221,c_53202,c_49815,c_49765,c_49660,c_49653,c_49650,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:45:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 55.69/7.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 55.69/7.50  
% 55.69/7.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 55.69/7.50  
% 55.69/7.50  ------  iProver source info
% 55.69/7.50  
% 55.69/7.50  git: date: 2020-06-30 10:37:57 +0100
% 55.69/7.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 55.69/7.50  git: non_committed_changes: false
% 55.69/7.50  git: last_make_outside_of_git: false
% 55.69/7.50  
% 55.69/7.50  ------ 
% 55.69/7.50  ------ Parsing...
% 55.69/7.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 55.69/7.50  
% 55.69/7.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 55.69/7.50  
% 55.69/7.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 55.69/7.50  
% 55.69/7.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 55.69/7.50  ------ Proving...
% 55.69/7.50  ------ Problem Properties 
% 55.69/7.50  
% 55.69/7.50  
% 55.69/7.50  clauses                                 26
% 55.69/7.50  conjectures                             3
% 55.69/7.50  EPR                                     0
% 55.69/7.50  Horn                                    20
% 55.69/7.50  unary                                   3
% 55.69/7.50  binary                                  8
% 55.69/7.50  lits                                    70
% 55.69/7.50  lits eq                                 36
% 55.69/7.50  fd_pure                                 0
% 55.69/7.50  fd_pseudo                               0
% 55.69/7.50  fd_cond                                 3
% 55.69/7.50  fd_pseudo_cond                          2
% 55.69/7.50  AC symbols                              0
% 55.69/7.50  
% 55.69/7.50  ------ Input Options Time Limit: Unbounded
% 55.69/7.50  
% 55.69/7.50  
% 55.69/7.50  
% 55.69/7.50  
% 55.69/7.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 55.69/7.50  Current options:
% 55.69/7.50  ------ 
% 55.69/7.50  
% 55.69/7.50  
% 55.69/7.50  
% 55.69/7.50  
% 55.69/7.50  ------ Proving...
% 55.69/7.50  
% 55.69/7.50  
% 55.69/7.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 55.69/7.50  
% 55.69/7.50  ------ Proving...
% 55.69/7.50  
% 55.69/7.50  
% 55.69/7.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 55.69/7.50  
% 55.69/7.50  ------ Proving...
% 55.69/7.50  
% 55.69/7.50  
% 55.69/7.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 55.69/7.50  
% 55.69/7.50  ------ Proving...
% 55.69/7.50  
% 55.69/7.50  
% 55.69/7.50  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 55.69/7.50  
% 55.69/7.50  ------ Proving...
% 55.69/7.50  
% 55.69/7.50  
% 55.69/7.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 55.69/7.50  
% 55.69/7.50  ------ Proving...
% 55.69/7.50  
% 55.69/7.50  
% 55.69/7.50  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 55.69/7.50  
% 55.69/7.50  ------ Proving...
% 55.69/7.50  
% 55.69/7.50  
% 55.69/7.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 55.69/7.50  
% 55.69/7.50  ------ Proving...
% 55.69/7.50  
% 55.69/7.50  
% 55.69/7.50  ------ Preprocessing... sf_s  rm: 11 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 55.69/7.50  
% 55.69/7.50  ------ Proving...
% 55.69/7.50  
% 55.69/7.50  
% 55.69/7.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 55.69/7.50  
% 55.69/7.50  ------ Proving...
% 55.69/7.50  
% 55.69/7.50  
% 55.69/7.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 55.69/7.50  
% 55.69/7.50  ------ Proving...
% 55.69/7.50  
% 55.69/7.50  
% 55.69/7.50  % SZS status Theorem for theBenchmark.p
% 55.69/7.50  
% 55.69/7.50  % SZS output start CNFRefutation for theBenchmark.p
% 55.69/7.50  
% 55.69/7.50  fof(f10,conjecture,(
% 55.69/7.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 55.69/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.69/7.50  
% 55.69/7.50  fof(f11,negated_conjecture,(
% 55.69/7.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 55.69/7.50    inference(negated_conjecture,[],[f10])).
% 55.69/7.50  
% 55.69/7.50  fof(f21,plain,(
% 55.69/7.50    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 55.69/7.50    inference(ennf_transformation,[],[f11])).
% 55.69/7.50  
% 55.69/7.50  fof(f22,plain,(
% 55.69/7.50    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 55.69/7.50    inference(flattening,[],[f21])).
% 55.69/7.50  
% 55.69/7.50  fof(f43,plain,(
% 55.69/7.50    ( ! [X2,X0] : (! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) => (k1_funct_1(X2,sK11(X3)) = X3 & r2_hidden(sK11(X3),X0)))) )),
% 55.69/7.50    introduced(choice_axiom,[])).
% 55.69/7.50  
% 55.69/7.50  fof(f42,plain,(
% 55.69/7.50    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k2_relset_1(sK8,sK9,sK10) != sK9 & ! [X3] : (? [X4] : (k1_funct_1(sK10,X4) = X3 & r2_hidden(X4,sK8)) | ~r2_hidden(X3,sK9)) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) & v1_funct_2(sK10,sK8,sK9) & v1_funct_1(sK10))),
% 55.69/7.50    introduced(choice_axiom,[])).
% 55.69/7.50  
% 55.69/7.50  fof(f44,plain,(
% 55.69/7.50    k2_relset_1(sK8,sK9,sK10) != sK9 & ! [X3] : ((k1_funct_1(sK10,sK11(X3)) = X3 & r2_hidden(sK11(X3),sK8)) | ~r2_hidden(X3,sK9)) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) & v1_funct_2(sK10,sK8,sK9) & v1_funct_1(sK10)),
% 55.69/7.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f22,f43,f42])).
% 55.69/7.50  
% 55.69/7.50  fof(f72,plain,(
% 55.69/7.50    v1_funct_2(sK10,sK8,sK9)),
% 55.69/7.50    inference(cnf_transformation,[],[f44])).
% 55.69/7.50  
% 55.69/7.50  fof(f9,axiom,(
% 55.69/7.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 55.69/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.69/7.50  
% 55.69/7.50  fof(f19,plain,(
% 55.69/7.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 55.69/7.50    inference(ennf_transformation,[],[f9])).
% 55.69/7.50  
% 55.69/7.50  fof(f20,plain,(
% 55.69/7.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 55.69/7.50    inference(flattening,[],[f19])).
% 55.69/7.50  
% 55.69/7.50  fof(f41,plain,(
% 55.69/7.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 55.69/7.50    inference(nnf_transformation,[],[f20])).
% 55.69/7.50  
% 55.69/7.50  fof(f65,plain,(
% 55.69/7.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 55.69/7.50    inference(cnf_transformation,[],[f41])).
% 55.69/7.50  
% 55.69/7.50  fof(f73,plain,(
% 55.69/7.50    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))),
% 55.69/7.50    inference(cnf_transformation,[],[f44])).
% 55.69/7.50  
% 55.69/7.50  fof(f6,axiom,(
% 55.69/7.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 55.69/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.69/7.50  
% 55.69/7.50  fof(f16,plain,(
% 55.69/7.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 55.69/7.50    inference(ennf_transformation,[],[f6])).
% 55.69/7.50  
% 55.69/7.50  fof(f60,plain,(
% 55.69/7.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 55.69/7.50    inference(cnf_transformation,[],[f16])).
% 55.69/7.50  
% 55.69/7.50  fof(f8,axiom,(
% 55.69/7.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 55.69/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.69/7.50  
% 55.69/7.50  fof(f18,plain,(
% 55.69/7.50    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 55.69/7.50    inference(ennf_transformation,[],[f8])).
% 55.69/7.50  
% 55.69/7.50  fof(f36,plain,(
% 55.69/7.50    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) | k2_relset_1(X0,X1,X2) != X1) & (k2_relset_1(X0,X1,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 55.69/7.50    inference(nnf_transformation,[],[f18])).
% 55.69/7.50  
% 55.69/7.50  fof(f37,plain,(
% 55.69/7.50    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) | k2_relset_1(X0,X1,X2) != X1) & (k2_relset_1(X0,X1,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X6,X5),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 55.69/7.50    inference(rectify,[],[f36])).
% 55.69/7.50  
% 55.69/7.50  fof(f39,plain,(
% 55.69/7.50    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X6,X5),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(X6,sK7(X1,X2)),X2) & r2_hidden(sK7(X1,X2),X1)))),
% 55.69/7.50    introduced(choice_axiom,[])).
% 55.69/7.50  
% 55.69/7.50  fof(f38,plain,(
% 55.69/7.50    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) => r2_hidden(k4_tarski(sK6(X2,X3),X3),X2))),
% 55.69/7.50    introduced(choice_axiom,[])).
% 55.69/7.50  
% 55.69/7.50  fof(f40,plain,(
% 55.69/7.50    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(sK6(X2,X3),X3),X2) | ~r2_hidden(X3,X1)) | k2_relset_1(X0,X1,X2) != X1) & (k2_relset_1(X0,X1,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(X6,sK7(X1,X2)),X2) & r2_hidden(sK7(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 55.69/7.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f37,f39,f38])).
% 55.69/7.50  
% 55.69/7.50  fof(f62,plain,(
% 55.69/7.50    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = X1 | r2_hidden(sK7(X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 55.69/7.50    inference(cnf_transformation,[],[f40])).
% 55.69/7.50  
% 55.69/7.50  fof(f7,axiom,(
% 55.69/7.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 55.69/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.69/7.50  
% 55.69/7.50  fof(f17,plain,(
% 55.69/7.50    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 55.69/7.50    inference(ennf_transformation,[],[f7])).
% 55.69/7.50  
% 55.69/7.50  fof(f61,plain,(
% 55.69/7.50    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 55.69/7.50    inference(cnf_transformation,[],[f17])).
% 55.69/7.50  
% 55.69/7.50  fof(f76,plain,(
% 55.69/7.50    k2_relset_1(sK8,sK9,sK10) != sK9),
% 55.69/7.50    inference(cnf_transformation,[],[f44])).
% 55.69/7.50  
% 55.69/7.50  fof(f75,plain,(
% 55.69/7.50    ( ! [X3] : (k1_funct_1(sK10,sK11(X3)) = X3 | ~r2_hidden(X3,sK9)) )),
% 55.69/7.50    inference(cnf_transformation,[],[f44])).
% 55.69/7.50  
% 55.69/7.50  fof(f4,axiom,(
% 55.69/7.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 55.69/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.69/7.50  
% 55.69/7.50  fof(f13,plain,(
% 55.69/7.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 55.69/7.50    inference(ennf_transformation,[],[f4])).
% 55.69/7.50  
% 55.69/7.50  fof(f14,plain,(
% 55.69/7.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 55.69/7.50    inference(flattening,[],[f13])).
% 55.69/7.50  
% 55.69/7.50  fof(f30,plain,(
% 55.69/7.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 55.69/7.50    inference(nnf_transformation,[],[f14])).
% 55.69/7.50  
% 55.69/7.50  fof(f31,plain,(
% 55.69/7.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 55.69/7.50    inference(rectify,[],[f30])).
% 55.69/7.50  
% 55.69/7.50  fof(f34,plain,(
% 55.69/7.50    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))))),
% 55.69/7.50    introduced(choice_axiom,[])).
% 55.69/7.50  
% 55.69/7.50  fof(f33,plain,(
% 55.69/7.50    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1)) = X2 & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))) )),
% 55.69/7.50    introduced(choice_axiom,[])).
% 55.69/7.50  
% 55.69/7.50  fof(f32,plain,(
% 55.69/7.50    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK3(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1))))),
% 55.69/7.50    introduced(choice_axiom,[])).
% 55.69/7.50  
% 55.69/7.50  fof(f35,plain,(
% 55.69/7.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & ((k1_funct_1(X0,sK4(X0,X1)) = sK3(X0,X1) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 55.69/7.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f31,f34,f33,f32])).
% 55.69/7.50  
% 55.69/7.50  fof(f55,plain,(
% 55.69/7.50    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 55.69/7.50    inference(cnf_transformation,[],[f35])).
% 55.69/7.50  
% 55.69/7.50  fof(f79,plain,(
% 55.69/7.50    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 55.69/7.50    inference(equality_resolution,[],[f55])).
% 55.69/7.50  
% 55.69/7.50  fof(f80,plain,(
% 55.69/7.50    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 55.69/7.50    inference(equality_resolution,[],[f79])).
% 55.69/7.50  
% 55.69/7.50  fof(f71,plain,(
% 55.69/7.50    v1_funct_1(sK10)),
% 55.69/7.50    inference(cnf_transformation,[],[f44])).
% 55.69/7.50  
% 55.69/7.50  fof(f5,axiom,(
% 55.69/7.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 55.69/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.69/7.50  
% 55.69/7.50  fof(f15,plain,(
% 55.69/7.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 55.69/7.50    inference(ennf_transformation,[],[f5])).
% 55.69/7.50  
% 55.69/7.50  fof(f59,plain,(
% 55.69/7.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 55.69/7.50    inference(cnf_transformation,[],[f15])).
% 55.69/7.50  
% 55.69/7.50  fof(f1,axiom,(
% 55.69/7.50    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 55.69/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.69/7.50  
% 55.69/7.50  fof(f23,plain,(
% 55.69/7.50    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 55.69/7.50    inference(nnf_transformation,[],[f1])).
% 55.69/7.50  
% 55.69/7.50  fof(f24,plain,(
% 55.69/7.50    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 55.69/7.50    inference(rectify,[],[f23])).
% 55.69/7.50  
% 55.69/7.50  fof(f27,plain,(
% 55.69/7.50    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK2(X0,X5),X5),X0))),
% 55.69/7.50    introduced(choice_axiom,[])).
% 55.69/7.50  
% 55.69/7.50  fof(f26,plain,(
% 55.69/7.50    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK1(X0,X1),X2),X0))) )),
% 55.69/7.50    introduced(choice_axiom,[])).
% 55.69/7.50  
% 55.69/7.50  fof(f25,plain,(
% 55.69/7.50    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK0(X0,X1)),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK0(X0,X1)),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 55.69/7.50    introduced(choice_axiom,[])).
% 55.69/7.50  
% 55.69/7.50  fof(f28,plain,(
% 55.69/7.50    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK0(X0,X1)),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK2(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 55.69/7.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27,f26,f25])).
% 55.69/7.50  
% 55.69/7.50  fof(f45,plain,(
% 55.69/7.50    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK2(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 55.69/7.50    inference(cnf_transformation,[],[f28])).
% 55.69/7.50  
% 55.69/7.50  fof(f78,plain,(
% 55.69/7.50    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK2(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 55.69/7.50    inference(equality_resolution,[],[f45])).
% 55.69/7.50  
% 55.69/7.50  fof(f63,plain,(
% 55.69/7.50    ( ! [X6,X2,X0,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_hidden(k4_tarski(X6,sK7(X1,X2)),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 55.69/7.50    inference(cnf_transformation,[],[f40])).
% 55.69/7.50  
% 55.69/7.50  fof(f74,plain,(
% 55.69/7.50    ( ! [X3] : (r2_hidden(sK11(X3),sK8) | ~r2_hidden(X3,sK9)) )),
% 55.69/7.50    inference(cnf_transformation,[],[f44])).
% 55.69/7.50  
% 55.69/7.50  fof(f69,plain,(
% 55.69/7.50    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 55.69/7.50    inference(cnf_transformation,[],[f41])).
% 55.69/7.50  
% 55.69/7.50  fof(f85,plain,(
% 55.69/7.50    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 55.69/7.50    inference(equality_resolution,[],[f69])).
% 55.69/7.50  
% 55.69/7.50  fof(f2,axiom,(
% 55.69/7.50    k2_relat_1(k1_xboole_0) = k1_xboole_0 & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 55.69/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.69/7.50  
% 55.69/7.50  fof(f50,plain,(
% 55.69/7.50    k2_relat_1(k1_xboole_0) = k1_xboole_0),
% 55.69/7.50    inference(cnf_transformation,[],[f2])).
% 55.69/7.50  
% 55.69/7.50  fof(f66,plain,(
% 55.69/7.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 55.69/7.50    inference(cnf_transformation,[],[f41])).
% 55.69/7.50  
% 55.69/7.50  fof(f87,plain,(
% 55.69/7.50    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 55.69/7.50    inference(equality_resolution,[],[f66])).
% 55.69/7.50  
% 55.69/7.50  fof(f3,axiom,(
% 55.69/7.50    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k2_relat_1(X0) = k1_xboole_0))),
% 55.69/7.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.69/7.50  
% 55.69/7.50  fof(f12,plain,(
% 55.69/7.50    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k2_relat_1(X0) = k1_xboole_0) | ~v1_relat_1(X0))),
% 55.69/7.50    inference(ennf_transformation,[],[f3])).
% 55.69/7.50  
% 55.69/7.50  fof(f29,plain,(
% 55.69/7.50    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k2_relat_1(X0) != k1_xboole_0) & (k2_relat_1(X0) = k1_xboole_0 | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 55.69/7.50    inference(nnf_transformation,[],[f12])).
% 55.69/7.50  
% 55.69/7.50  fof(f51,plain,(
% 55.69/7.50    ( ! [X0] : (k2_relat_1(X0) = k1_xboole_0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 55.69/7.50    inference(cnf_transformation,[],[f29])).
% 55.69/7.50  
% 55.69/7.50  cnf(c_30,negated_conjecture,
% 55.69/7.50      ( v1_funct_2(sK10,sK8,sK9) ),
% 55.69/7.50      inference(cnf_transformation,[],[f72]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_25,plain,
% 55.69/7.50      ( ~ v1_funct_2(X0,X1,X2)
% 55.69/7.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 55.69/7.50      | k1_relset_1(X1,X2,X0) = X1
% 55.69/7.50      | k1_xboole_0 = X2 ),
% 55.69/7.50      inference(cnf_transformation,[],[f65]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_29,negated_conjecture,
% 55.69/7.50      ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) ),
% 55.69/7.50      inference(cnf_transformation,[],[f73]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_464,plain,
% 55.69/7.50      ( ~ v1_funct_2(X0,X1,X2)
% 55.69/7.50      | k1_relset_1(X1,X2,X0) = X1
% 55.69/7.50      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
% 55.69/7.50      | sK10 != X0
% 55.69/7.50      | k1_xboole_0 = X2 ),
% 55.69/7.50      inference(resolution_lifted,[status(thm)],[c_25,c_29]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_465,plain,
% 55.69/7.50      ( ~ v1_funct_2(sK10,X0,X1)
% 55.69/7.50      | k1_relset_1(X0,X1,sK10) = X0
% 55.69/7.50      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
% 55.69/7.50      | k1_xboole_0 = X1 ),
% 55.69/7.50      inference(unflattening,[status(thm)],[c_464]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_847,plain,
% 55.69/7.50      ( k1_relset_1(X0,X1,sK10) = X0
% 55.69/7.50      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
% 55.69/7.50      | sK10 != sK10
% 55.69/7.50      | sK9 != X1
% 55.69/7.50      | sK8 != X0
% 55.69/7.50      | k1_xboole_0 = X1 ),
% 55.69/7.50      inference(resolution_lifted,[status(thm)],[c_30,c_465]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_848,plain,
% 55.69/7.50      ( k1_relset_1(sK8,sK9,sK10) = sK8
% 55.69/7.50      | k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
% 55.69/7.50      | k1_xboole_0 = sK9 ),
% 55.69/7.50      inference(unflattening,[status(thm)],[c_847]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_919,plain,
% 55.69/7.50      ( k1_relset_1(sK8,sK9,sK10) = sK8 | k1_xboole_0 = sK9 ),
% 55.69/7.50      inference(equality_resolution_simp,[status(thm)],[c_848]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_15,plain,
% 55.69/7.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 55.69/7.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 55.69/7.50      inference(cnf_transformation,[],[f60]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_557,plain,
% 55.69/7.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 55.69/7.50      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
% 55.69/7.50      | sK10 != X2 ),
% 55.69/7.50      inference(resolution_lifted,[status(thm)],[c_15,c_29]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_558,plain,
% 55.69/7.50      ( k1_relset_1(X0,X1,sK10) = k1_relat_1(sK10)
% 55.69/7.50      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)) ),
% 55.69/7.50      inference(unflattening,[status(thm)],[c_557]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_255132,plain,
% 55.69/7.50      ( k1_relset_1(sK8,sK9,sK10) = k1_relat_1(sK10) ),
% 55.69/7.50      inference(equality_resolution,[status(thm)],[c_558]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_255171,plain,
% 55.69/7.50      ( k1_relat_1(sK10) = sK8 | sK9 = k1_xboole_0 ),
% 55.69/7.50      inference(superposition,[status(thm)],[c_919,c_255132]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_19,plain,
% 55.69/7.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 55.69/7.50      | r2_hidden(sK7(X2,X0),X2)
% 55.69/7.50      | k2_relset_1(X1,X2,X0) = X2 ),
% 55.69/7.50      inference(cnf_transformation,[],[f62]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_500,plain,
% 55.69/7.50      ( r2_hidden(sK7(X0,X1),X0)
% 55.69/7.50      | k2_relset_1(X2,X0,X1) = X0
% 55.69/7.50      | k1_zfmisc_1(k2_zfmisc_1(X2,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
% 55.69/7.50      | sK10 != X1 ),
% 55.69/7.50      inference(resolution_lifted,[status(thm)],[c_19,c_29]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_501,plain,
% 55.69/7.50      ( r2_hidden(sK7(X0,sK10),X0)
% 55.69/7.50      | k2_relset_1(X1,X0,sK10) = X0
% 55.69/7.50      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)) ),
% 55.69/7.50      inference(unflattening,[status(thm)],[c_500]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_255038,plain,
% 55.69/7.50      ( k2_relset_1(X0,X1,sK10) = X1
% 55.69/7.50      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
% 55.69/7.50      | r2_hidden(sK7(X1,sK10),X1) = iProver_top ),
% 55.69/7.50      inference(predicate_to_equality,[status(thm)],[c_501]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_255193,plain,
% 55.69/7.50      ( k2_relset_1(sK8,sK9,sK10) = sK9
% 55.69/7.50      | r2_hidden(sK7(sK9,sK10),sK9) = iProver_top ),
% 55.69/7.50      inference(equality_resolution,[status(thm)],[c_255038]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_16,plain,
% 55.69/7.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 55.69/7.50      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 55.69/7.50      inference(cnf_transformation,[],[f61]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_548,plain,
% 55.69/7.50      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 55.69/7.50      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
% 55.69/7.50      | sK10 != X2 ),
% 55.69/7.50      inference(resolution_lifted,[status(thm)],[c_16,c_29]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_549,plain,
% 55.69/7.50      ( k2_relset_1(X0,X1,sK10) = k2_relat_1(sK10)
% 55.69/7.50      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)) ),
% 55.69/7.50      inference(unflattening,[status(thm)],[c_548]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_255118,plain,
% 55.69/7.50      ( k2_relset_1(sK8,sK9,sK10) = k2_relat_1(sK10) ),
% 55.69/7.50      inference(equality_resolution,[status(thm)],[c_549]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_255194,plain,
% 55.69/7.50      ( k2_relat_1(sK10) = sK9
% 55.69/7.50      | r2_hidden(sK7(sK9,sK10),sK9) = iProver_top ),
% 55.69/7.50      inference(demodulation,[status(thm)],[c_255193,c_255118]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_26,negated_conjecture,
% 55.69/7.50      ( k2_relset_1(sK8,sK9,sK10) != sK9 ),
% 55.69/7.50      inference(cnf_transformation,[],[f76]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_49649,plain,
% 55.69/7.50      ( r2_hidden(sK7(sK9,sK10),sK9)
% 55.69/7.50      | k2_relset_1(sK8,sK9,sK10) = sK9
% 55.69/7.50      | k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)) ),
% 55.69/7.50      inference(instantiation,[status(thm)],[c_501]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_49650,plain,
% 55.69/7.50      ( k2_relset_1(sK8,sK9,sK10) = sK9
% 55.69/7.50      | k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
% 55.69/7.50      | r2_hidden(sK7(sK9,sK10),sK9) = iProver_top ),
% 55.69/7.50      inference(predicate_to_equality,[status(thm)],[c_49649]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_1168,plain,( X0 = X0 ),theory(equality) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_49765,plain,
% 55.69/7.50      ( k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)) = k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)) ),
% 55.69/7.50      inference(instantiation,[status(thm)],[c_1168]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_255212,plain,
% 55.69/7.50      ( r2_hidden(sK7(sK9,sK10),sK9) = iProver_top ),
% 55.69/7.50      inference(global_propositional_subsumption,
% 55.69/7.50                [status(thm)],
% 55.69/7.50                [c_255194,c_26,c_49650,c_49765]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_27,negated_conjecture,
% 55.69/7.50      ( ~ r2_hidden(X0,sK9) | k1_funct_1(sK10,sK11(X0)) = X0 ),
% 55.69/7.50      inference(cnf_transformation,[],[f75]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_255039,plain,
% 55.69/7.50      ( k1_funct_1(sK10,sK11(X0)) = X0
% 55.69/7.50      | r2_hidden(X0,sK9) != iProver_top ),
% 55.69/7.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_255217,plain,
% 55.69/7.50      ( k1_funct_1(sK10,sK11(sK7(sK9,sK10))) = sK7(sK9,sK10) ),
% 55.69/7.50      inference(superposition,[status(thm)],[c_255212,c_255039]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_11,plain,
% 55.69/7.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 55.69/7.50      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 55.69/7.50      | ~ v1_funct_1(X1)
% 55.69/7.50      | ~ v1_relat_1(X1) ),
% 55.69/7.50      inference(cnf_transformation,[],[f80]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_31,negated_conjecture,
% 55.69/7.50      ( v1_funct_1(sK10) ),
% 55.69/7.50      inference(cnf_transformation,[],[f71]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_400,plain,
% 55.69/7.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 55.69/7.50      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 55.69/7.50      | ~ v1_relat_1(X1)
% 55.69/7.50      | sK10 != X1 ),
% 55.69/7.50      inference(resolution_lifted,[status(thm)],[c_11,c_31]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_401,plain,
% 55.69/7.50      ( ~ r2_hidden(X0,k1_relat_1(sK10))
% 55.69/7.50      | r2_hidden(k1_funct_1(sK10,X0),k2_relat_1(sK10))
% 55.69/7.50      | ~ v1_relat_1(sK10) ),
% 55.69/7.50      inference(unflattening,[status(thm)],[c_400]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_49451,plain,
% 55.69/7.50      ( r2_hidden(X0,k1_relat_1(sK10)) != iProver_top
% 55.69/7.50      | r2_hidden(k1_funct_1(sK10,X0),k2_relat_1(sK10)) = iProver_top
% 55.69/7.50      | v1_relat_1(sK10) != iProver_top ),
% 55.69/7.50      inference(predicate_to_equality,[status(thm)],[c_401]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_402,plain,
% 55.69/7.50      ( r2_hidden(X0,k1_relat_1(sK10)) != iProver_top
% 55.69/7.50      | r2_hidden(k1_funct_1(sK10,X0),k2_relat_1(sK10)) = iProver_top
% 55.69/7.50      | v1_relat_1(sK10) != iProver_top ),
% 55.69/7.50      inference(predicate_to_equality,[status(thm)],[c_401]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_14,plain,
% 55.69/7.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 55.69/7.50      | v1_relat_1(X0) ),
% 55.69/7.50      inference(cnf_transformation,[],[f59]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_566,plain,
% 55.69/7.50      ( v1_relat_1(X0)
% 55.69/7.50      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
% 55.69/7.50      | sK10 != X0 ),
% 55.69/7.50      inference(resolution_lifted,[status(thm)],[c_14,c_29]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_567,plain,
% 55.69/7.50      ( v1_relat_1(sK10)
% 55.69/7.50      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)) ),
% 55.69/7.50      inference(unflattening,[status(thm)],[c_566]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_49448,plain,
% 55.69/7.50      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
% 55.69/7.50      | v1_relat_1(sK10) = iProver_top ),
% 55.69/7.50      inference(predicate_to_equality,[status(thm)],[c_567]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_49659,plain,
% 55.69/7.50      ( v1_relat_1(sK10) = iProver_top ),
% 55.69/7.50      inference(equality_resolution,[status(thm)],[c_49448]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_49685,plain,
% 55.69/7.50      ( r2_hidden(k1_funct_1(sK10,X0),k2_relat_1(sK10)) = iProver_top
% 55.69/7.50      | r2_hidden(X0,k1_relat_1(sK10)) != iProver_top ),
% 55.69/7.50      inference(global_propositional_subsumption,
% 55.69/7.50                [status(thm)],
% 55.69/7.50                [c_49451,c_402,c_49659]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_49686,plain,
% 55.69/7.50      ( r2_hidden(X0,k1_relat_1(sK10)) != iProver_top
% 55.69/7.50      | r2_hidden(k1_funct_1(sK10,X0),k2_relat_1(sK10)) = iProver_top ),
% 55.69/7.50      inference(renaming,[status(thm)],[c_49685]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_49687,plain,
% 55.69/7.50      ( ~ r2_hidden(X0,k1_relat_1(sK10))
% 55.69/7.50      | r2_hidden(k1_funct_1(sK10,X0),k2_relat_1(sK10)) ),
% 55.69/7.50      inference(predicate_to_equality_rev,[status(thm)],[c_49686]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_254944,plain,
% 55.69/7.50      ( r2_hidden(k1_funct_1(sK10,X0),k2_relat_1(sK10))
% 55.69/7.50      | ~ r2_hidden(X0,k1_relat_1(sK10)) ),
% 55.69/7.50      inference(global_propositional_subsumption,
% 55.69/7.50                [status(thm)],
% 55.69/7.50                [c_401,c_49687]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_254945,plain,
% 55.69/7.50      ( ~ r2_hidden(X0,k1_relat_1(sK10))
% 55.69/7.50      | r2_hidden(k1_funct_1(sK10,X0),k2_relat_1(sK10)) ),
% 55.69/7.50      inference(renaming,[status(thm)],[c_254944]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_255035,plain,
% 55.69/7.50      ( r2_hidden(X0,k1_relat_1(sK10)) != iProver_top
% 55.69/7.50      | r2_hidden(k1_funct_1(sK10,X0),k2_relat_1(sK10)) = iProver_top ),
% 55.69/7.50      inference(predicate_to_equality,[status(thm)],[c_254945]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_255219,plain,
% 55.69/7.50      ( r2_hidden(sK7(sK9,sK10),k2_relat_1(sK10)) = iProver_top
% 55.69/7.50      | r2_hidden(sK11(sK7(sK9,sK10)),k1_relat_1(sK10)) != iProver_top ),
% 55.69/7.50      inference(superposition,[status(thm)],[c_255217,c_255035]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_49450,plain,
% 55.69/7.50      ( k2_relset_1(X0,X1,sK10) = X1
% 55.69/7.50      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
% 55.69/7.50      | r2_hidden(sK7(X1,sK10),X1) = iProver_top ),
% 55.69/7.50      inference(predicate_to_equality,[status(thm)],[c_501]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_49950,plain,
% 55.69/7.50      ( k2_relset_1(sK8,sK9,sK10) = sK9
% 55.69/7.50      | r2_hidden(sK7(sK9,sK10),sK9) = iProver_top ),
% 55.69/7.50      inference(equality_resolution,[status(thm)],[c_49450]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_49644,plain,
% 55.69/7.50      ( k2_relset_1(sK8,sK9,sK10) = k2_relat_1(sK10) ),
% 55.69/7.50      inference(equality_resolution,[status(thm)],[c_549]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_49951,plain,
% 55.69/7.50      ( k2_relat_1(sK10) = sK9
% 55.69/7.50      | r2_hidden(sK7(sK9,sK10),sK9) = iProver_top ),
% 55.69/7.50      inference(demodulation,[status(thm)],[c_49950,c_49644]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_50500,plain,
% 55.69/7.50      ( r2_hidden(sK7(sK9,sK10),sK9) = iProver_top ),
% 55.69/7.50      inference(global_propositional_subsumption,
% 55.69/7.50                [status(thm)],
% 55.69/7.50                [c_49951,c_26,c_49650,c_49765]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_49454,plain,
% 55.69/7.50      ( k1_funct_1(sK10,sK11(X0)) = X0
% 55.69/7.50      | r2_hidden(X0,sK9) != iProver_top ),
% 55.69/7.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_50505,plain,
% 55.69/7.50      ( k1_funct_1(sK10,sK11(sK7(sK9,sK10))) = sK7(sK9,sK10) ),
% 55.69/7.50      inference(superposition,[status(thm)],[c_50500,c_49454]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_50524,plain,
% 55.69/7.50      ( r2_hidden(sK7(sK9,sK10),k2_relat_1(sK10)) = iProver_top
% 55.69/7.50      | r2_hidden(sK11(sK7(sK9,sK10)),k1_relat_1(sK10)) != iProver_top ),
% 55.69/7.50      inference(superposition,[status(thm)],[c_50505,c_49686]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_3,plain,
% 55.69/7.50      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 55.69/7.50      | r2_hidden(k4_tarski(sK2(X1,X0),X0),X1) ),
% 55.69/7.50      inference(cnf_transformation,[],[f78]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_255041,plain,
% 55.69/7.50      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 55.69/7.50      | r2_hidden(k4_tarski(sK2(X1,X0),X0),X1) = iProver_top ),
% 55.69/7.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_18,plain,
% 55.69/7.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 55.69/7.50      | ~ r2_hidden(k4_tarski(X3,sK7(X2,X0)),X0)
% 55.69/7.50      | k2_relset_1(X1,X2,X0) = X2 ),
% 55.69/7.50      inference(cnf_transformation,[],[f63]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_515,plain,
% 55.69/7.50      ( ~ r2_hidden(k4_tarski(X0,sK7(X1,X2)),X2)
% 55.69/7.50      | k2_relset_1(X3,X1,X2) = X1
% 55.69/7.50      | k1_zfmisc_1(k2_zfmisc_1(X3,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
% 55.69/7.50      | sK10 != X2 ),
% 55.69/7.50      inference(resolution_lifted,[status(thm)],[c_18,c_29]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_516,plain,
% 55.69/7.50      ( ~ r2_hidden(k4_tarski(X0,sK7(X1,sK10)),sK10)
% 55.69/7.50      | k2_relset_1(X2,X1,sK10) = X1
% 55.69/7.50      | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)) ),
% 55.69/7.50      inference(unflattening,[status(thm)],[c_515]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_255037,plain,
% 55.69/7.50      ( k2_relset_1(X0,X1,sK10) = X1
% 55.69/7.50      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
% 55.69/7.50      | r2_hidden(k4_tarski(X2,sK7(X1,sK10)),sK10) != iProver_top ),
% 55.69/7.50      inference(predicate_to_equality,[status(thm)],[c_516]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_255182,plain,
% 55.69/7.50      ( k2_relset_1(sK8,sK9,sK10) = sK9
% 55.69/7.50      | r2_hidden(k4_tarski(X0,sK7(sK9,sK10)),sK10) != iProver_top ),
% 55.69/7.50      inference(equality_resolution,[status(thm)],[c_255037]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_255183,plain,
% 55.69/7.50      ( k2_relat_1(sK10) = sK9
% 55.69/7.50      | r2_hidden(k4_tarski(X0,sK7(sK9,sK10)),sK10) != iProver_top ),
% 55.69/7.50      inference(demodulation,[status(thm)],[c_255182,c_255118]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_49653,plain,
% 55.69/7.50      ( k2_relat_1(sK10) != sK9 ),
% 55.69/7.50      inference(demodulation,[status(thm)],[c_49644,c_26]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_49449,plain,
% 55.69/7.50      ( k2_relset_1(X0,X1,sK10) = X1
% 55.69/7.50      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
% 55.69/7.50      | r2_hidden(k4_tarski(X2,sK7(X1,sK10)),sK10) != iProver_top ),
% 55.69/7.50      inference(predicate_to_equality,[status(thm)],[c_516]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_49748,plain,
% 55.69/7.50      ( k2_relset_1(sK8,sK9,sK10) = sK9
% 55.69/7.50      | r2_hidden(k4_tarski(X0,sK7(sK9,sK10)),sK10) != iProver_top ),
% 55.69/7.50      inference(equality_resolution,[status(thm)],[c_49449]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_49749,plain,
% 55.69/7.50      ( k2_relat_1(sK10) = sK9
% 55.69/7.50      | r2_hidden(k4_tarski(X0,sK7(sK9,sK10)),sK10) != iProver_top ),
% 55.69/7.50      inference(demodulation,[status(thm)],[c_49748,c_49644]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_255199,plain,
% 55.69/7.50      ( r2_hidden(k4_tarski(X0,sK7(sK9,sK10)),sK10) != iProver_top ),
% 55.69/7.50      inference(global_propositional_subsumption,
% 55.69/7.50                [status(thm)],
% 55.69/7.50                [c_255183,c_49653,c_49749]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_255225,plain,
% 55.69/7.50      ( r2_hidden(sK7(sK9,sK10),k2_relat_1(sK10)) != iProver_top ),
% 55.69/7.50      inference(superposition,[status(thm)],[c_255041,c_255199]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_255263,plain,
% 55.69/7.50      ( r2_hidden(sK11(sK7(sK9,sK10)),k1_relat_1(sK10)) != iProver_top ),
% 55.69/7.50      inference(global_propositional_subsumption,
% 55.69/7.50                [status(thm)],
% 55.69/7.50                [c_255219,c_50524,c_255225]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_255268,plain,
% 55.69/7.50      ( sK9 = k1_xboole_0
% 55.69/7.50      | r2_hidden(sK11(sK7(sK9,sK10)),sK8) != iProver_top ),
% 55.69/7.50      inference(superposition,[status(thm)],[c_255171,c_255263]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_28,negated_conjecture,
% 55.69/7.50      ( ~ r2_hidden(X0,sK9) | r2_hidden(sK11(X0),sK8) ),
% 55.69/7.50      inference(cnf_transformation,[],[f74]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_53198,plain,
% 55.69/7.50      ( ~ r2_hidden(sK7(sK9,sK10),sK9)
% 55.69/7.50      | r2_hidden(sK11(sK7(sK9,sK10)),sK8) ),
% 55.69/7.50      inference(instantiation,[status(thm)],[c_28]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_53202,plain,
% 55.69/7.50      ( r2_hidden(sK7(sK9,sK10),sK9) != iProver_top
% 55.69/7.50      | r2_hidden(sK11(sK7(sK9,sK10)),sK8) = iProver_top ),
% 55.69/7.50      inference(predicate_to_equality,[status(thm)],[c_53198]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_255272,plain,
% 55.69/7.50      ( sK9 = k1_xboole_0 ),
% 55.69/7.50      inference(global_propositional_subsumption,
% 55.69/7.50                [status(thm)],
% 55.69/7.50                [c_255268,c_26,c_49650,c_49765,c_53202]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_255285,plain,
% 55.69/7.50      ( k1_relset_1(sK8,k1_xboole_0,sK10) = k1_relat_1(sK10) ),
% 55.69/7.50      inference(demodulation,[status(thm)],[c_255272,c_255132]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_21,plain,
% 55.69/7.50      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 55.69/7.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 55.69/7.50      | k1_xboole_0 = X1
% 55.69/7.50      | k1_xboole_0 = X0 ),
% 55.69/7.50      inference(cnf_transformation,[],[f85]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_595,plain,
% 55.69/7.50      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 55.69/7.50      | k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
% 55.69/7.50      | sK10 != X0
% 55.69/7.50      | k1_xboole_0 = X0
% 55.69/7.50      | k1_xboole_0 = X1 ),
% 55.69/7.50      inference(resolution_lifted,[status(thm)],[c_21,c_29]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_596,plain,
% 55.69/7.50      ( ~ v1_funct_2(sK10,X0,k1_xboole_0)
% 55.69/7.50      | k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
% 55.69/7.50      | k1_xboole_0 = X0
% 55.69/7.50      | k1_xboole_0 = sK10 ),
% 55.69/7.50      inference(unflattening,[status(thm)],[c_595]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_858,plain,
% 55.69/7.50      ( k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
% 55.69/7.50      | sK10 != sK10
% 55.69/7.50      | sK10 = k1_xboole_0
% 55.69/7.50      | sK9 != k1_xboole_0
% 55.69/7.50      | sK8 != X0
% 55.69/7.50      | k1_xboole_0 = X0 ),
% 55.69/7.50      inference(resolution_lifted,[status(thm)],[c_30,c_596]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_859,plain,
% 55.69/7.50      ( k1_zfmisc_1(k2_zfmisc_1(sK8,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
% 55.69/7.50      | sK10 = k1_xboole_0
% 55.69/7.50      | sK9 != k1_xboole_0
% 55.69/7.50      | k1_xboole_0 = sK8 ),
% 55.69/7.50      inference(unflattening,[status(thm)],[c_858]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_4,plain,
% 55.69/7.50      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 55.69/7.50      inference(cnf_transformation,[],[f50]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_1201,plain,
% 55.69/7.50      ( k1_xboole_0 = k1_xboole_0 ),
% 55.69/7.50      inference(instantiation,[status(thm)],[c_1168]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_1170,plain,
% 55.69/7.50      ( X0 != X1 | k2_relat_1(X0) = k2_relat_1(X1) ),
% 55.69/7.50      theory(equality) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_53598,plain,
% 55.69/7.50      ( X0 != k1_xboole_0 | k2_relat_1(X0) = k2_relat_1(k1_xboole_0) ),
% 55.69/7.50      inference(instantiation,[status(thm)],[c_1170]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_54220,plain,
% 55.69/7.50      ( k2_relat_1(sK10) = k2_relat_1(k1_xboole_0)
% 55.69/7.50      | sK10 != k1_xboole_0 ),
% 55.69/7.50      inference(instantiation,[status(thm)],[c_53598]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_1169,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_53596,plain,
% 55.69/7.50      ( X0 = X1 | X1 != k1_xboole_0 | X0 != k1_xboole_0 ),
% 55.69/7.50      inference(instantiation,[status(thm)],[c_1169]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_54165,plain,
% 55.69/7.50      ( X0 != k1_xboole_0
% 55.69/7.50      | k2_relat_1(sK10) = X0
% 55.69/7.50      | k2_relat_1(sK10) != k1_xboole_0 ),
% 55.69/7.50      inference(instantiation,[status(thm)],[c_53596]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_89221,plain,
% 55.69/7.50      ( k2_relat_1(sK10) = sK9
% 55.69/7.50      | k2_relat_1(sK10) != k1_xboole_0
% 55.69/7.50      | sK9 != k1_xboole_0 ),
% 55.69/7.50      inference(instantiation,[status(thm)],[c_54165]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_87363,plain,
% 55.69/7.50      ( X0 != X1 | k2_relat_1(sK10) != X1 | k2_relat_1(sK10) = X0 ),
% 55.69/7.50      inference(instantiation,[status(thm)],[c_1169]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_165216,plain,
% 55.69/7.50      ( X0 != k2_relat_1(k1_xboole_0)
% 55.69/7.50      | k2_relat_1(sK10) = X0
% 55.69/7.50      | k2_relat_1(sK10) != k2_relat_1(k1_xboole_0) ),
% 55.69/7.50      inference(instantiation,[status(thm)],[c_87363]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_165217,plain,
% 55.69/7.50      ( k2_relat_1(sK10) != k2_relat_1(k1_xboole_0)
% 55.69/7.50      | k2_relat_1(sK10) = k1_xboole_0
% 55.69/7.50      | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
% 55.69/7.50      inference(instantiation,[status(thm)],[c_165216]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_239770,plain,
% 55.69/7.50      ( X0 = k2_relat_1(X1)
% 55.69/7.50      | X0 != k1_xboole_0
% 55.69/7.50      | k2_relat_1(X1) != k1_xboole_0 ),
% 55.69/7.50      inference(instantiation,[status(thm)],[c_53596]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_239771,plain,
% 55.69/7.50      ( k2_relat_1(k1_xboole_0) != k1_xboole_0
% 55.69/7.50      | k1_xboole_0 = k2_relat_1(k1_xboole_0)
% 55.69/7.50      | k1_xboole_0 != k1_xboole_0 ),
% 55.69/7.50      inference(instantiation,[status(thm)],[c_239770]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_254955,plain,
% 55.69/7.50      ( k1_zfmisc_1(k2_zfmisc_1(sK8,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
% 55.69/7.50      | sK9 != k1_xboole_0
% 55.69/7.50      | k1_xboole_0 = sK8 ),
% 55.69/7.50      inference(global_propositional_subsumption,
% 55.69/7.50                [status(thm)],
% 55.69/7.50                [c_859,c_4,c_1201,c_49653,c_54220,c_89221,c_165217,
% 55.69/7.50                 c_239771]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_255290,plain,
% 55.69/7.50      ( k1_zfmisc_1(k2_zfmisc_1(sK8,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK8,k1_xboole_0))
% 55.69/7.50      | sK8 = k1_xboole_0
% 55.69/7.50      | k1_xboole_0 != k1_xboole_0 ),
% 55.69/7.50      inference(demodulation,[status(thm)],[c_255272,c_254955]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_255306,plain,
% 55.69/7.50      ( sK8 = k1_xboole_0 ),
% 55.69/7.50      inference(equality_resolution_simp,[status(thm)],[c_255290]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_24,plain,
% 55.69/7.50      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 55.69/7.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 55.69/7.50      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 55.69/7.50      inference(cnf_transformation,[],[f87]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_613,plain,
% 55.69/7.50      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 55.69/7.50      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 55.69/7.50      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
% 55.69/7.50      | sK10 != X0 ),
% 55.69/7.50      inference(resolution_lifted,[status(thm)],[c_24,c_29]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_614,plain,
% 55.69/7.50      ( ~ v1_funct_2(sK10,k1_xboole_0,X0)
% 55.69/7.50      | k1_relset_1(k1_xboole_0,X0,sK10) = k1_xboole_0
% 55.69/7.50      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)) ),
% 55.69/7.50      inference(unflattening,[status(thm)],[c_613]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_872,plain,
% 55.69/7.50      ( k1_relset_1(k1_xboole_0,X0,sK10) = k1_xboole_0
% 55.69/7.50      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
% 55.69/7.50      | sK10 != sK10
% 55.69/7.50      | sK9 != X0
% 55.69/7.50      | sK8 != k1_xboole_0 ),
% 55.69/7.50      inference(resolution_lifted,[status(thm)],[c_30,c_614]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_873,plain,
% 55.69/7.50      ( k1_relset_1(k1_xboole_0,sK9,sK10) = k1_xboole_0
% 55.69/7.50      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK9)) != k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))
% 55.69/7.50      | sK8 != k1_xboole_0 ),
% 55.69/7.50      inference(unflattening,[status(thm)],[c_872]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_255289,plain,
% 55.69/7.50      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK10) = k1_xboole_0
% 55.69/7.50      | k1_zfmisc_1(k2_zfmisc_1(sK8,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 55.69/7.50      | sK8 != k1_xboole_0 ),
% 55.69/7.50      inference(demodulation,[status(thm)],[c_255272,c_873]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_255319,plain,
% 55.69/7.50      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK10) = k1_xboole_0
% 55.69/7.50      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 55.69/7.50      | k1_xboole_0 != k1_xboole_0 ),
% 55.69/7.50      inference(light_normalisation,[status(thm)],[c_255289,c_255306]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_255320,plain,
% 55.69/7.50      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK10) = k1_xboole_0 ),
% 55.69/7.50      inference(equality_resolution_simp,[status(thm)],[c_255319]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_255328,plain,
% 55.69/7.50      ( k1_relat_1(sK10) = k1_xboole_0 ),
% 55.69/7.50      inference(light_normalisation,
% 55.69/7.50                [status(thm)],
% 55.69/7.50                [c_255285,c_255306,c_255320]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_7,plain,
% 55.69/7.50      ( ~ v1_relat_1(X0)
% 55.69/7.50      | k1_relat_1(X0) != k1_xboole_0
% 55.69/7.50      | k2_relat_1(X0) = k1_xboole_0 ),
% 55.69/7.50      inference(cnf_transformation,[],[f51]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_49815,plain,
% 55.69/7.50      ( ~ v1_relat_1(sK10)
% 55.69/7.50      | k1_relat_1(sK10) != k1_xboole_0
% 55.69/7.50      | k2_relat_1(sK10) = k1_xboole_0 ),
% 55.69/7.50      inference(instantiation,[status(thm)],[c_7]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(c_49660,plain,
% 55.69/7.50      ( v1_relat_1(sK10) ),
% 55.69/7.50      inference(predicate_to_equality_rev,[status(thm)],[c_49659]) ).
% 55.69/7.50  
% 55.69/7.50  cnf(contradiction,plain,
% 55.69/7.50      ( $false ),
% 55.69/7.50      inference(minisat,
% 55.69/7.50                [status(thm)],
% 55.69/7.50                [c_255328,c_255268,c_89221,c_53202,c_49815,c_49765,
% 55.69/7.50                 c_49660,c_49653,c_49650,c_26]) ).
% 55.69/7.50  
% 55.69/7.50  
% 55.69/7.50  % SZS output end CNFRefutation for theBenchmark.p
% 55.69/7.50  
% 55.69/7.50  ------                               Statistics
% 55.69/7.50  
% 55.69/7.50  ------ Selected
% 55.69/7.50  
% 55.69/7.50  total_time:                             6.875
% 55.69/7.50  
%------------------------------------------------------------------------------
