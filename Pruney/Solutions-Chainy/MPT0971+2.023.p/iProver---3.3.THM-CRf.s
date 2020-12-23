%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:04 EST 2020

% Result     : Theorem 3.63s
% Output     : CNFRefutation 3.63s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 349 expanded)
%              Number of clauses        :   75 ( 123 expanded)
%              Number of leaves         :   23 (  73 expanded)
%              Depth                    :   16
%              Number of atoms          :  447 (1330 expanded)
%              Number of equality atoms :  172 ( 322 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ~ ( k1_funct_1(X3,X4) = X2
                & r2_hidden(X4,X0) )
          & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ~ ( k1_funct_1(X3,X4) = X2
                  & r2_hidden(X4,X0) )
            & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f32,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X2
          | ~ r2_hidden(X4,X0) )
      & r2_hidden(X2,k2_relset_1(X0,X1,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f33,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X2
          | ~ r2_hidden(X4,X0) )
      & r2_hidden(X2,k2_relset_1(X0,X1,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f32])).

fof(f43,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( k1_funct_1(X3,X4) != X2
            | ~ r2_hidden(X4,X0) )
        & r2_hidden(X2,k2_relset_1(X0,X1,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( k1_funct_1(sK6,X4) != sK5
          | ~ r2_hidden(X4,sK3) )
      & r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6))
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK6,sK3,sK4)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ! [X4] :
        ( k1_funct_1(sK6,X4) != sK5
        | ~ r2_hidden(X4,sK3) )
    & r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6))
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK6,sK3,sK4)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f33,f43])).

fof(f75,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f44])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f40,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X5)) = X5
        & r2_hidden(sK2(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1)) = X2
        & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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
              ( k1_funct_1(X0,X3) != sK0(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK0(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK0(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK0(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1)
                  & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK0(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK2(X0,X5)) = X5
                    & r2_hidden(sK2(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f40,f39,f38])).

fof(f59,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK2(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f84,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK2(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f73,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f44])).

fof(f77,plain,(
    ! [X4] :
      ( k1_funct_1(sK6,X4) != sK5
      | ~ r2_hidden(X4,sK3) ) ),
    inference(cnf_transformation,[],[f44])).

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
    inference(ennf_transformation,[],[f16])).

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

fof(f42,plain,(
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

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f74,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f58,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK2(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f85,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK2(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f76,plain,(
    r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6)) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f78,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f79,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f46,f78])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_enumset1(X0,X0,X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f79])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f80,plain,(
    ! [X0,X1] : k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) != k1_xboole_0 ),
    inference(definition_unfolding,[],[f49,f79])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_232,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_233,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_232])).

cnf(c_295,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_233])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2672,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(sK3,sK4)) ),
    inference(resolution,[status(thm)],[c_5,c_27])).

cnf(c_5273,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
    | v1_relat_1(sK6) ),
    inference(resolution,[status(thm)],[c_295,c_2672])).

cnf(c_2477,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | r1_tarski(sK6,k2_zfmisc_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2607,plain,
    ( ~ r1_tarski(sK6,k2_zfmisc_1(sK3,sK4))
    | ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_295])).

cnf(c_9,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2700,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_5276,plain,
    ( v1_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5273,c_27,c_2477,c_2607,c_2700])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK2(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_468,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK2(X1,X0)) = X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_29])).

cnf(c_469,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,sK2(sK6,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_468])).

cnf(c_5493,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | k1_funct_1(sK6,sK2(sK6,X0)) = X0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_5276,c_469])).

cnf(c_1687,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_5882,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | X1 != X0
    | k1_funct_1(sK6,sK2(sK6,X0)) = X1 ),
    inference(resolution,[status(thm)],[c_5493,c_1687])).

cnf(c_25,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | k1_funct_1(sK6,X0) != sK5 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_15030,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | ~ r2_hidden(sK2(sK6,X0),sK3)
    | sK5 != X0 ),
    inference(resolution,[status(thm)],[c_5882,c_25])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_717,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X2
    | sK3 != X1
    | sK6 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_28])).

cnf(c_718,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_717])).

cnf(c_720,plain,
    ( k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_718,c_27])).

cnf(c_2267,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2271,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3587,plain,
    ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_2267,c_2271])).

cnf(c_3808,plain,
    ( k1_relat_1(sK6) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_720,c_3587])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK2(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_453,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK2(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_29])).

cnf(c_454,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_453])).

cnf(c_2261,plain,
    ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_454])).

cnf(c_3883,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(sK2(sK6,X0),sK3) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3808,c_2261])).

cnf(c_3921,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | r2_hidden(sK2(sK6,X0),sK3)
    | ~ v1_relat_1(sK6)
    | sK4 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3883])).

cnf(c_16,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_8,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_398,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_16,c_8])).

cnf(c_2264,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_398])).

cnf(c_3358,plain,
    ( r1_tarski(k2_relat_1(sK6),sK4) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2267,c_2264])).

cnf(c_32,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2478,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | r1_tarski(sK6,k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2477])).

cnf(c_2617,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(sK3,sK4)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2607])).

cnf(c_2701,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2700])).

cnf(c_3811,plain,
    ( r1_tarski(k2_relat_1(sK6),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3358,c_32,c_2478,c_2617,c_2701])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2270,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3511,plain,
    ( k2_relset_1(sK3,sK4,sK6) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_2267,c_2270])).

cnf(c_26,negated_conjecture,
    ( r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2268,plain,
    ( r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3697,plain,
    ( r2_hidden(sK5,k2_relat_1(sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3511,c_2268])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_292,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_2,c_233])).

cnf(c_2266,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_292])).

cnf(c_4102,plain,
    ( r2_hidden(sK5,X0) = iProver_top
    | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3697,c_2266])).

cnf(c_4631,plain,
    ( r2_hidden(sK5,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3811,c_4102])).

cnf(c_3,plain,
    ( m1_subset_1(k2_enumset1(X0,X0,X0,X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2275,plain,
    ( m1_subset_1(k2_enumset1(X0,X0,X0,X0),k1_zfmisc_1(X1)) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2273,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3600,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2275,c_2273])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2276,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4317,plain,
    ( k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = X1
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3600,c_2276])).

cnf(c_4635,plain,
    ( k2_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK4) = sK4 ),
    inference(superposition,[status(thm)],[c_4631,c_4317])).

cnf(c_1,plain,
    ( k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_7213,plain,
    ( sK4 != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4635,c_1])).

cnf(c_15087,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | sK5 != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15030,c_27,c_2477,c_2607,c_2700,c_3921,c_7213])).

cnf(c_1686,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_15105,plain,
    ( ~ r2_hidden(sK5,k2_relat_1(sK6)) ),
    inference(resolution,[status(thm)],[c_15087,c_1686])).

cnf(c_3698,plain,
    ( r2_hidden(sK5,k2_relat_1(sK6)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3697])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15105,c_3698])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:22:38 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.63/0.94  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.63/0.94  
% 3.63/0.94  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.63/0.94  
% 3.63/0.94  ------  iProver source info
% 3.63/0.94  
% 3.63/0.94  git: date: 2020-06-30 10:37:57 +0100
% 3.63/0.94  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.63/0.94  git: non_committed_changes: false
% 3.63/0.94  git: last_make_outside_of_git: false
% 3.63/0.94  
% 3.63/0.94  ------ 
% 3.63/0.94  ------ Parsing...
% 3.63/0.94  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.63/0.94  
% 3.63/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.63/0.94  
% 3.63/0.94  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.63/0.94  
% 3.63/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.63/0.94  ------ Proving...
% 3.63/0.94  ------ Problem Properties 
% 3.63/0.94  
% 3.63/0.94  
% 3.63/0.94  clauses                                 23
% 3.63/0.94  conjectures                             3
% 3.63/0.94  EPR                                     2
% 3.63/0.94  Horn                                    19
% 3.63/0.94  unary                                   4
% 3.63/0.94  binary                                  8
% 3.63/0.94  lits                                    58
% 3.63/0.94  lits eq                                 18
% 3.63/0.94  fd_pure                                 0
% 3.63/0.94  fd_pseudo                               0
% 3.63/0.94  fd_cond                                 3
% 3.63/0.94  fd_pseudo_cond                          0
% 3.63/0.94  AC symbols                              0
% 3.63/0.94  
% 3.63/0.94  ------ Input Options Time Limit: Unbounded
% 3.63/0.94  
% 3.63/0.94  
% 3.63/0.94  ------ 
% 3.63/0.94  Current options:
% 3.63/0.94  ------ 
% 3.63/0.94  
% 3.63/0.94  
% 3.63/0.94  
% 3.63/0.94  
% 3.63/0.94  ------ Proving...
% 3.63/0.94  
% 3.63/0.94  
% 3.63/0.94  % SZS status Theorem for theBenchmark.p
% 3.63/0.94  
% 3.63/0.94  % SZS output start CNFRefutation for theBenchmark.p
% 3.63/0.94  
% 3.63/0.94  fof(f9,axiom,(
% 3.63/0.94    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.63/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.94  
% 3.63/0.94  fof(f23,plain,(
% 3.63/0.94    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.63/0.94    inference(ennf_transformation,[],[f9])).
% 3.63/0.94  
% 3.63/0.94  fof(f54,plain,(
% 3.63/0.94    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.63/0.94    inference(cnf_transformation,[],[f23])).
% 3.63/0.94  
% 3.63/0.94  fof(f8,axiom,(
% 3.63/0.94    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.63/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.94  
% 3.63/0.94  fof(f34,plain,(
% 3.63/0.94    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.63/0.94    inference(nnf_transformation,[],[f8])).
% 3.63/0.94  
% 3.63/0.94  fof(f53,plain,(
% 3.63/0.94    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.63/0.94    inference(cnf_transformation,[],[f34])).
% 3.63/0.94  
% 3.63/0.94  fof(f52,plain,(
% 3.63/0.94    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.63/0.94    inference(cnf_transformation,[],[f34])).
% 3.63/0.94  
% 3.63/0.94  fof(f17,conjecture,(
% 3.63/0.94    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ~(! [X4] : ~(k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))))),
% 3.63/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.94  
% 3.63/0.94  fof(f18,negated_conjecture,(
% 3.63/0.94    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ~(! [X4] : ~(k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))))),
% 3.63/0.94    inference(negated_conjecture,[],[f17])).
% 3.63/0.94  
% 3.63/0.94  fof(f32,plain,(
% 3.63/0.94    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.63/0.94    inference(ennf_transformation,[],[f18])).
% 3.63/0.94  
% 3.63/0.94  fof(f33,plain,(
% 3.63/0.94    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.63/0.94    inference(flattening,[],[f32])).
% 3.63/0.94  
% 3.63/0.94  fof(f43,plain,(
% 3.63/0.94    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (k1_funct_1(sK6,X4) != sK5 | ~r2_hidden(X4,sK3)) & r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6))),
% 3.63/0.94    introduced(choice_axiom,[])).
% 3.63/0.94  
% 3.63/0.94  fof(f44,plain,(
% 3.63/0.94    ! [X4] : (k1_funct_1(sK6,X4) != sK5 | ~r2_hidden(X4,sK3)) & r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)),
% 3.63/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f33,f43])).
% 3.63/0.94  
% 3.63/0.94  fof(f75,plain,(
% 3.63/0.94    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.63/0.94    inference(cnf_transformation,[],[f44])).
% 3.63/0.94  
% 3.63/0.94  fof(f11,axiom,(
% 3.63/0.94    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.63/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.94  
% 3.63/0.94  fof(f57,plain,(
% 3.63/0.94    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.63/0.94    inference(cnf_transformation,[],[f11])).
% 3.63/0.94  
% 3.63/0.94  fof(f12,axiom,(
% 3.63/0.94    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.63/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.94  
% 3.63/0.94  fof(f25,plain,(
% 3.63/0.94    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.63/0.94    inference(ennf_transformation,[],[f12])).
% 3.63/0.94  
% 3.63/0.94  fof(f26,plain,(
% 3.63/0.94    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.63/0.94    inference(flattening,[],[f25])).
% 3.63/0.94  
% 3.63/0.94  fof(f36,plain,(
% 3.63/0.94    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.63/0.94    inference(nnf_transformation,[],[f26])).
% 3.63/0.94  
% 3.63/0.94  fof(f37,plain,(
% 3.63/0.94    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.63/0.94    inference(rectify,[],[f36])).
% 3.63/0.94  
% 3.63/0.94  fof(f40,plain,(
% 3.63/0.94    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X5)) = X5 & r2_hidden(sK2(X0,X5),k1_relat_1(X0))))),
% 3.63/0.94    introduced(choice_axiom,[])).
% 3.63/0.94  
% 3.63/0.94  fof(f39,plain,(
% 3.63/0.94    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1)) = X2 & r2_hidden(sK1(X0,X1),k1_relat_1(X0))))) )),
% 3.63/0.94    introduced(choice_axiom,[])).
% 3.63/0.94  
% 3.63/0.94  fof(f38,plain,(
% 3.63/0.94    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK0(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK0(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK0(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK0(X0,X1),X1))))),
% 3.63/0.94    introduced(choice_axiom,[])).
% 3.63/0.94  
% 3.63/0.94  fof(f41,plain,(
% 3.63/0.94    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK0(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK0(X0,X1),X1)) & ((k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))) | r2_hidden(sK0(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK2(X0,X5)) = X5 & r2_hidden(sK2(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.63/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f40,f39,f38])).
% 3.63/0.94  
% 3.63/0.94  fof(f59,plain,(
% 3.63/0.94    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK2(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.63/0.94    inference(cnf_transformation,[],[f41])).
% 3.63/0.94  
% 3.63/0.94  fof(f84,plain,(
% 3.63/0.94    ( ! [X0,X5] : (k1_funct_1(X0,sK2(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.63/0.94    inference(equality_resolution,[],[f59])).
% 3.63/0.94  
% 3.63/0.94  fof(f73,plain,(
% 3.63/0.94    v1_funct_1(sK6)),
% 3.63/0.94    inference(cnf_transformation,[],[f44])).
% 3.63/0.94  
% 3.63/0.94  fof(f77,plain,(
% 3.63/0.94    ( ! [X4] : (k1_funct_1(sK6,X4) != sK5 | ~r2_hidden(X4,sK3)) )),
% 3.63/0.94    inference(cnf_transformation,[],[f44])).
% 3.63/0.94  
% 3.63/0.94  fof(f16,axiom,(
% 3.63/0.94    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.63/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.94  
% 3.63/0.94  fof(f30,plain,(
% 3.63/0.94    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.63/0.94    inference(ennf_transformation,[],[f16])).
% 3.63/0.94  
% 3.63/0.94  fof(f31,plain,(
% 3.63/0.94    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.63/0.94    inference(flattening,[],[f30])).
% 3.63/0.94  
% 3.63/0.94  fof(f42,plain,(
% 3.63/0.94    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.63/0.94    inference(nnf_transformation,[],[f31])).
% 3.63/0.94  
% 3.63/0.94  fof(f67,plain,(
% 3.63/0.94    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.63/0.94    inference(cnf_transformation,[],[f42])).
% 3.63/0.94  
% 3.63/0.94  fof(f74,plain,(
% 3.63/0.94    v1_funct_2(sK6,sK3,sK4)),
% 3.63/0.94    inference(cnf_transformation,[],[f44])).
% 3.63/0.94  
% 3.63/0.94  fof(f14,axiom,(
% 3.63/0.94    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.63/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.94  
% 3.63/0.94  fof(f28,plain,(
% 3.63/0.94    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.63/0.94    inference(ennf_transformation,[],[f14])).
% 3.63/0.94  
% 3.63/0.94  fof(f65,plain,(
% 3.63/0.94    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.63/0.94    inference(cnf_transformation,[],[f28])).
% 3.63/0.94  
% 3.63/0.94  fof(f58,plain,(
% 3.63/0.94    ( ! [X0,X5,X1] : (r2_hidden(sK2(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.63/0.94    inference(cnf_transformation,[],[f41])).
% 3.63/0.94  
% 3.63/0.94  fof(f85,plain,(
% 3.63/0.94    ( ! [X0,X5] : (r2_hidden(sK2(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.63/0.94    inference(equality_resolution,[],[f58])).
% 3.63/0.94  
% 3.63/0.94  fof(f13,axiom,(
% 3.63/0.94    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.63/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.94  
% 3.63/0.94  fof(f19,plain,(
% 3.63/0.94    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.63/0.94    inference(pure_predicate_removal,[],[f13])).
% 3.63/0.94  
% 3.63/0.94  fof(f27,plain,(
% 3.63/0.94    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.63/0.94    inference(ennf_transformation,[],[f19])).
% 3.63/0.94  
% 3.63/0.94  fof(f64,plain,(
% 3.63/0.94    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.63/0.94    inference(cnf_transformation,[],[f27])).
% 3.63/0.94  
% 3.63/0.94  fof(f10,axiom,(
% 3.63/0.94    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.63/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.94  
% 3.63/0.94  fof(f24,plain,(
% 3.63/0.94    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.63/0.94    inference(ennf_transformation,[],[f10])).
% 3.63/0.94  
% 3.63/0.94  fof(f35,plain,(
% 3.63/0.94    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.63/0.94    inference(nnf_transformation,[],[f24])).
% 3.63/0.94  
% 3.63/0.94  fof(f55,plain,(
% 3.63/0.94    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.63/0.94    inference(cnf_transformation,[],[f35])).
% 3.63/0.94  
% 3.63/0.94  fof(f15,axiom,(
% 3.63/0.94    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.63/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.94  
% 3.63/0.94  fof(f29,plain,(
% 3.63/0.94    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.63/0.94    inference(ennf_transformation,[],[f15])).
% 3.63/0.94  
% 3.63/0.94  fof(f66,plain,(
% 3.63/0.94    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.63/0.94    inference(cnf_transformation,[],[f29])).
% 3.63/0.94  
% 3.63/0.94  fof(f76,plain,(
% 3.63/0.94    r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6))),
% 3.63/0.94    inference(cnf_transformation,[],[f44])).
% 3.63/0.94  
% 3.63/0.94  fof(f6,axiom,(
% 3.63/0.94    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.63/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.94  
% 3.63/0.94  fof(f21,plain,(
% 3.63/0.94    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.63/0.94    inference(ennf_transformation,[],[f6])).
% 3.63/0.94  
% 3.63/0.94  fof(f50,plain,(
% 3.63/0.94    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.63/0.94    inference(cnf_transformation,[],[f21])).
% 3.63/0.94  
% 3.63/0.94  fof(f7,axiom,(
% 3.63/0.94    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 3.63/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.94  
% 3.63/0.94  fof(f22,plain,(
% 3.63/0.94    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 3.63/0.94    inference(ennf_transformation,[],[f7])).
% 3.63/0.94  
% 3.63/0.94  fof(f51,plain,(
% 3.63/0.94    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 3.63/0.94    inference(cnf_transformation,[],[f22])).
% 3.63/0.94  
% 3.63/0.94  fof(f2,axiom,(
% 3.63/0.94    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.63/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.94  
% 3.63/0.94  fof(f46,plain,(
% 3.63/0.94    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.63/0.94    inference(cnf_transformation,[],[f2])).
% 3.63/0.94  
% 3.63/0.94  fof(f3,axiom,(
% 3.63/0.94    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.63/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.94  
% 3.63/0.94  fof(f47,plain,(
% 3.63/0.94    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.63/0.94    inference(cnf_transformation,[],[f3])).
% 3.63/0.94  
% 3.63/0.94  fof(f4,axiom,(
% 3.63/0.94    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.63/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.94  
% 3.63/0.94  fof(f48,plain,(
% 3.63/0.94    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.63/0.94    inference(cnf_transformation,[],[f4])).
% 3.63/0.94  
% 3.63/0.94  fof(f78,plain,(
% 3.63/0.94    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.63/0.94    inference(definition_unfolding,[],[f47,f48])).
% 3.63/0.94  
% 3.63/0.94  fof(f79,plain,(
% 3.63/0.94    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.63/0.94    inference(definition_unfolding,[],[f46,f78])).
% 3.63/0.94  
% 3.63/0.94  fof(f81,plain,(
% 3.63/0.94    ( ! [X0,X1] : (m1_subset_1(k2_enumset1(X0,X0,X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 3.63/0.94    inference(definition_unfolding,[],[f51,f79])).
% 3.63/0.94  
% 3.63/0.94  fof(f1,axiom,(
% 3.63/0.94    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.63/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.94  
% 3.63/0.94  fof(f20,plain,(
% 3.63/0.94    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.63/0.94    inference(ennf_transformation,[],[f1])).
% 3.63/0.94  
% 3.63/0.94  fof(f45,plain,(
% 3.63/0.94    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.63/0.94    inference(cnf_transformation,[],[f20])).
% 3.63/0.94  
% 3.63/0.94  fof(f5,axiom,(
% 3.63/0.94    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 3.63/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.94  
% 3.63/0.94  fof(f49,plain,(
% 3.63/0.94    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 3.63/0.94    inference(cnf_transformation,[],[f5])).
% 3.63/0.94  
% 3.63/0.94  fof(f80,plain,(
% 3.63/0.94    ( ! [X0,X1] : (k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) != k1_xboole_0) )),
% 3.63/0.94    inference(definition_unfolding,[],[f49,f79])).
% 3.63/0.94  
% 3.63/0.94  cnf(c_6,plain,
% 3.63/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.63/0.94      | ~ v1_relat_1(X1)
% 3.63/0.94      | v1_relat_1(X0) ),
% 3.63/0.94      inference(cnf_transformation,[],[f54]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_4,plain,
% 3.63/0.94      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.63/0.94      inference(cnf_transformation,[],[f53]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_232,plain,
% 3.63/0.94      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.63/0.94      inference(prop_impl,[status(thm)],[c_4]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_233,plain,
% 3.63/0.94      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.63/0.94      inference(renaming,[status(thm)],[c_232]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_295,plain,
% 3.63/0.94      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.63/0.94      inference(bin_hyper_res,[status(thm)],[c_6,c_233]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_5,plain,
% 3.63/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.63/0.94      inference(cnf_transformation,[],[f52]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_27,negated_conjecture,
% 3.63/0.94      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.63/0.94      inference(cnf_transformation,[],[f75]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_2672,plain,
% 3.63/0.94      ( r1_tarski(sK6,k2_zfmisc_1(sK3,sK4)) ),
% 3.63/0.94      inference(resolution,[status(thm)],[c_5,c_27]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_5273,plain,
% 3.63/0.94      ( ~ v1_relat_1(k2_zfmisc_1(sK3,sK4)) | v1_relat_1(sK6) ),
% 3.63/0.94      inference(resolution,[status(thm)],[c_295,c_2672]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_2477,plain,
% 3.63/0.94      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.63/0.94      | r1_tarski(sK6,k2_zfmisc_1(sK3,sK4)) ),
% 3.63/0.94      inference(instantiation,[status(thm)],[c_5]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_2607,plain,
% 3.63/0.94      ( ~ r1_tarski(sK6,k2_zfmisc_1(sK3,sK4))
% 3.63/0.94      | ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
% 3.63/0.94      | v1_relat_1(sK6) ),
% 3.63/0.94      inference(instantiation,[status(thm)],[c_295]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_9,plain,
% 3.63/0.94      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.63/0.94      inference(cnf_transformation,[],[f57]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_2700,plain,
% 3.63/0.94      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) ),
% 3.63/0.94      inference(instantiation,[status(thm)],[c_9]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_5276,plain,
% 3.63/0.94      ( v1_relat_1(sK6) ),
% 3.63/0.94      inference(global_propositional_subsumption,
% 3.63/0.94                [status(thm)],
% 3.63/0.94                [c_5273,c_27,c_2477,c_2607,c_2700]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_14,plain,
% 3.63/0.94      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.63/0.94      | ~ v1_funct_1(X1)
% 3.63/0.94      | ~ v1_relat_1(X1)
% 3.63/0.94      | k1_funct_1(X1,sK2(X1,X0)) = X0 ),
% 3.63/0.94      inference(cnf_transformation,[],[f84]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_29,negated_conjecture,
% 3.63/0.94      ( v1_funct_1(sK6) ),
% 3.63/0.94      inference(cnf_transformation,[],[f73]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_468,plain,
% 3.63/0.94      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.63/0.94      | ~ v1_relat_1(X1)
% 3.63/0.94      | k1_funct_1(X1,sK2(X1,X0)) = X0
% 3.63/0.94      | sK6 != X1 ),
% 3.63/0.94      inference(resolution_lifted,[status(thm)],[c_14,c_29]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_469,plain,
% 3.63/0.94      ( ~ r2_hidden(X0,k2_relat_1(sK6))
% 3.63/0.94      | ~ v1_relat_1(sK6)
% 3.63/0.94      | k1_funct_1(sK6,sK2(sK6,X0)) = X0 ),
% 3.63/0.94      inference(unflattening,[status(thm)],[c_468]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_5493,plain,
% 3.63/0.94      ( ~ r2_hidden(X0,k2_relat_1(sK6))
% 3.63/0.94      | k1_funct_1(sK6,sK2(sK6,X0)) = X0 ),
% 3.63/0.94      inference(backward_subsumption_resolution,
% 3.63/0.94                [status(thm)],
% 3.63/0.94                [c_5276,c_469]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_1687,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_5882,plain,
% 3.63/0.94      ( ~ r2_hidden(X0,k2_relat_1(sK6))
% 3.63/0.94      | X1 != X0
% 3.63/0.94      | k1_funct_1(sK6,sK2(sK6,X0)) = X1 ),
% 3.63/0.94      inference(resolution,[status(thm)],[c_5493,c_1687]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_25,negated_conjecture,
% 3.63/0.94      ( ~ r2_hidden(X0,sK3) | k1_funct_1(sK6,X0) != sK5 ),
% 3.63/0.94      inference(cnf_transformation,[],[f77]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_15030,plain,
% 3.63/0.94      ( ~ r2_hidden(X0,k2_relat_1(sK6))
% 3.63/0.94      | ~ r2_hidden(sK2(sK6,X0),sK3)
% 3.63/0.94      | sK5 != X0 ),
% 3.63/0.94      inference(resolution,[status(thm)],[c_5882,c_25]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_24,plain,
% 3.63/0.94      ( ~ v1_funct_2(X0,X1,X2)
% 3.63/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.63/0.94      | k1_relset_1(X1,X2,X0) = X1
% 3.63/0.94      | k1_xboole_0 = X2 ),
% 3.63/0.94      inference(cnf_transformation,[],[f67]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_28,negated_conjecture,
% 3.63/0.94      ( v1_funct_2(sK6,sK3,sK4) ),
% 3.63/0.94      inference(cnf_transformation,[],[f74]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_717,plain,
% 3.63/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.63/0.94      | k1_relset_1(X1,X2,X0) = X1
% 3.63/0.94      | sK4 != X2
% 3.63/0.94      | sK3 != X1
% 3.63/0.94      | sK6 != X0
% 3.63/0.94      | k1_xboole_0 = X2 ),
% 3.63/0.94      inference(resolution_lifted,[status(thm)],[c_24,c_28]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_718,plain,
% 3.63/0.94      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.63/0.94      | k1_relset_1(sK3,sK4,sK6) = sK3
% 3.63/0.94      | k1_xboole_0 = sK4 ),
% 3.63/0.94      inference(unflattening,[status(thm)],[c_717]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_720,plain,
% 3.63/0.94      ( k1_relset_1(sK3,sK4,sK6) = sK3 | k1_xboole_0 = sK4 ),
% 3.63/0.94      inference(global_propositional_subsumption,
% 3.63/0.94                [status(thm)],
% 3.63/0.94                [c_718,c_27]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_2267,plain,
% 3.63/0.94      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.63/0.94      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_17,plain,
% 3.63/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.63/0.94      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.63/0.94      inference(cnf_transformation,[],[f65]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_2271,plain,
% 3.63/0.94      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.63/0.94      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.63/0.94      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_3587,plain,
% 3.63/0.94      ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
% 3.63/0.94      inference(superposition,[status(thm)],[c_2267,c_2271]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_3808,plain,
% 3.63/0.94      ( k1_relat_1(sK6) = sK3 | sK4 = k1_xboole_0 ),
% 3.63/0.94      inference(superposition,[status(thm)],[c_720,c_3587]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_15,plain,
% 3.63/0.94      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.63/0.94      | r2_hidden(sK2(X1,X0),k1_relat_1(X1))
% 3.63/0.94      | ~ v1_funct_1(X1)
% 3.63/0.94      | ~ v1_relat_1(X1) ),
% 3.63/0.94      inference(cnf_transformation,[],[f85]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_453,plain,
% 3.63/0.94      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.63/0.94      | r2_hidden(sK2(X1,X0),k1_relat_1(X1))
% 3.63/0.94      | ~ v1_relat_1(X1)
% 3.63/0.94      | sK6 != X1 ),
% 3.63/0.94      inference(resolution_lifted,[status(thm)],[c_15,c_29]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_454,plain,
% 3.63/0.94      ( ~ r2_hidden(X0,k2_relat_1(sK6))
% 3.63/0.94      | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6))
% 3.63/0.94      | ~ v1_relat_1(sK6) ),
% 3.63/0.94      inference(unflattening,[status(thm)],[c_453]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_2261,plain,
% 3.63/0.94      ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 3.63/0.94      | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 3.63/0.94      | v1_relat_1(sK6) != iProver_top ),
% 3.63/0.94      inference(predicate_to_equality,[status(thm)],[c_454]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_3883,plain,
% 3.63/0.94      ( sK4 = k1_xboole_0
% 3.63/0.94      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 3.63/0.94      | r2_hidden(sK2(sK6,X0),sK3) = iProver_top
% 3.63/0.94      | v1_relat_1(sK6) != iProver_top ),
% 3.63/0.94      inference(superposition,[status(thm)],[c_3808,c_2261]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_3921,plain,
% 3.63/0.94      ( ~ r2_hidden(X0,k2_relat_1(sK6))
% 3.63/0.94      | r2_hidden(sK2(sK6,X0),sK3)
% 3.63/0.94      | ~ v1_relat_1(sK6)
% 3.63/0.94      | sK4 = k1_xboole_0 ),
% 3.63/0.94      inference(predicate_to_equality_rev,[status(thm)],[c_3883]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_16,plain,
% 3.63/0.94      ( v5_relat_1(X0,X1)
% 3.63/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.63/0.94      inference(cnf_transformation,[],[f64]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_8,plain,
% 3.63/0.94      ( ~ v5_relat_1(X0,X1)
% 3.63/0.94      | r1_tarski(k2_relat_1(X0),X1)
% 3.63/0.94      | ~ v1_relat_1(X0) ),
% 3.63/0.94      inference(cnf_transformation,[],[f55]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_398,plain,
% 3.63/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.63/0.94      | r1_tarski(k2_relat_1(X0),X2)
% 3.63/0.94      | ~ v1_relat_1(X0) ),
% 3.63/0.94      inference(resolution,[status(thm)],[c_16,c_8]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_2264,plain,
% 3.63/0.94      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.63/0.94      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 3.63/0.94      | v1_relat_1(X0) != iProver_top ),
% 3.63/0.94      inference(predicate_to_equality,[status(thm)],[c_398]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_3358,plain,
% 3.63/0.94      ( r1_tarski(k2_relat_1(sK6),sK4) = iProver_top
% 3.63/0.94      | v1_relat_1(sK6) != iProver_top ),
% 3.63/0.94      inference(superposition,[status(thm)],[c_2267,c_2264]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_32,plain,
% 3.63/0.94      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.63/0.94      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_2478,plain,
% 3.63/0.94      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.63/0.94      | r1_tarski(sK6,k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 3.63/0.94      inference(predicate_to_equality,[status(thm)],[c_2477]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_2617,plain,
% 3.63/0.94      ( r1_tarski(sK6,k2_zfmisc_1(sK3,sK4)) != iProver_top
% 3.63/0.94      | v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
% 3.63/0.94      | v1_relat_1(sK6) = iProver_top ),
% 3.63/0.94      inference(predicate_to_equality,[status(thm)],[c_2607]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_2701,plain,
% 3.63/0.94      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 3.63/0.94      inference(predicate_to_equality,[status(thm)],[c_2700]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_3811,plain,
% 3.63/0.94      ( r1_tarski(k2_relat_1(sK6),sK4) = iProver_top ),
% 3.63/0.94      inference(global_propositional_subsumption,
% 3.63/0.94                [status(thm)],
% 3.63/0.94                [c_3358,c_32,c_2478,c_2617,c_2701]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_18,plain,
% 3.63/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.63/0.94      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.63/0.94      inference(cnf_transformation,[],[f66]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_2270,plain,
% 3.63/0.94      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.63/0.94      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.63/0.94      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_3511,plain,
% 3.63/0.94      ( k2_relset_1(sK3,sK4,sK6) = k2_relat_1(sK6) ),
% 3.63/0.94      inference(superposition,[status(thm)],[c_2267,c_2270]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_26,negated_conjecture,
% 3.63/0.94      ( r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6)) ),
% 3.63/0.94      inference(cnf_transformation,[],[f76]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_2268,plain,
% 3.63/0.94      ( r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6)) = iProver_top ),
% 3.63/0.94      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_3697,plain,
% 3.63/0.94      ( r2_hidden(sK5,k2_relat_1(sK6)) = iProver_top ),
% 3.63/0.94      inference(demodulation,[status(thm)],[c_3511,c_2268]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_2,plain,
% 3.63/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.63/0.94      | ~ r2_hidden(X2,X0)
% 3.63/0.94      | r2_hidden(X2,X1) ),
% 3.63/0.94      inference(cnf_transformation,[],[f50]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_292,plain,
% 3.63/0.94      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.63/0.94      inference(bin_hyper_res,[status(thm)],[c_2,c_233]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_2266,plain,
% 3.63/0.94      ( r2_hidden(X0,X1) != iProver_top
% 3.63/0.94      | r2_hidden(X0,X2) = iProver_top
% 3.63/0.94      | r1_tarski(X1,X2) != iProver_top ),
% 3.63/0.94      inference(predicate_to_equality,[status(thm)],[c_292]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_4102,plain,
% 3.63/0.94      ( r2_hidden(sK5,X0) = iProver_top
% 3.63/0.94      | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
% 3.63/0.94      inference(superposition,[status(thm)],[c_3697,c_2266]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_4631,plain,
% 3.63/0.94      ( r2_hidden(sK5,sK4) = iProver_top ),
% 3.63/0.94      inference(superposition,[status(thm)],[c_3811,c_4102]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_3,plain,
% 3.63/0.94      ( m1_subset_1(k2_enumset1(X0,X0,X0,X0),k1_zfmisc_1(X1))
% 3.63/0.94      | ~ r2_hidden(X0,X1) ),
% 3.63/0.94      inference(cnf_transformation,[],[f81]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_2275,plain,
% 3.63/0.94      ( m1_subset_1(k2_enumset1(X0,X0,X0,X0),k1_zfmisc_1(X1)) = iProver_top
% 3.63/0.94      | r2_hidden(X0,X1) != iProver_top ),
% 3.63/0.94      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_2273,plain,
% 3.63/0.94      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.63/0.94      | r1_tarski(X0,X1) = iProver_top ),
% 3.63/0.94      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_3600,plain,
% 3.63/0.94      ( r2_hidden(X0,X1) != iProver_top
% 3.63/0.94      | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) = iProver_top ),
% 3.63/0.94      inference(superposition,[status(thm)],[c_2275,c_2273]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_0,plain,
% 3.63/0.94      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 3.63/0.94      inference(cnf_transformation,[],[f45]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_2276,plain,
% 3.63/0.94      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 3.63/0.94      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_4317,plain,
% 3.63/0.94      ( k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = X1
% 3.63/0.94      | r2_hidden(X0,X1) != iProver_top ),
% 3.63/0.94      inference(superposition,[status(thm)],[c_3600,c_2276]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_4635,plain,
% 3.63/0.94      ( k2_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK4) = sK4 ),
% 3.63/0.94      inference(superposition,[status(thm)],[c_4631,c_4317]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_1,plain,
% 3.63/0.94      ( k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) != k1_xboole_0 ),
% 3.63/0.94      inference(cnf_transformation,[],[f80]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_7213,plain,
% 3.63/0.94      ( sK4 != k1_xboole_0 ),
% 3.63/0.94      inference(superposition,[status(thm)],[c_4635,c_1]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_15087,plain,
% 3.63/0.94      ( ~ r2_hidden(X0,k2_relat_1(sK6)) | sK5 != X0 ),
% 3.63/0.94      inference(global_propositional_subsumption,
% 3.63/0.94                [status(thm)],
% 3.63/0.94                [c_15030,c_27,c_2477,c_2607,c_2700,c_3921,c_7213]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_1686,plain,( X0 = X0 ),theory(equality) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_15105,plain,
% 3.63/0.94      ( ~ r2_hidden(sK5,k2_relat_1(sK6)) ),
% 3.63/0.94      inference(resolution,[status(thm)],[c_15087,c_1686]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(c_3698,plain,
% 3.63/0.94      ( r2_hidden(sK5,k2_relat_1(sK6)) ),
% 3.63/0.94      inference(predicate_to_equality_rev,[status(thm)],[c_3697]) ).
% 3.63/0.94  
% 3.63/0.94  cnf(contradiction,plain,
% 3.63/0.94      ( $false ),
% 3.63/0.94      inference(minisat,[status(thm)],[c_15105,c_3698]) ).
% 3.63/0.94  
% 3.63/0.94  
% 3.63/0.94  % SZS output end CNFRefutation for theBenchmark.p
% 3.63/0.94  
% 3.63/0.94  ------                               Statistics
% 3.63/0.94  
% 3.63/0.94  ------ Selected
% 3.63/0.94  
% 3.63/0.94  total_time:                             0.473
% 3.63/0.94  
%------------------------------------------------------------------------------
