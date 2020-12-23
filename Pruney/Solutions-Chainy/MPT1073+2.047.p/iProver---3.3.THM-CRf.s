%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:09 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 354 expanded)
%              Number of clauses        :   64 ( 112 expanded)
%              Number of leaves         :   22 (  75 expanded)
%              Depth                    :   18
%              Number of atoms          :  482 (1509 expanded)
%              Number of equality atoms :  193 ( 430 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ( m1_subset_1(X4,X1)
             => k1_funct_1(X3,X4) != X0 )
          & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f32,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f31])).

fof(f47,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( k1_funct_1(X3,X4) != X0
            | ~ m1_subset_1(X4,X1) )
        & r2_hidden(X0,k2_relset_1(X1,X2,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( k1_funct_1(sK7,X4) != sK4
          | ~ m1_subset_1(X4,sK5) )
      & r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7))
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      & v1_funct_2(sK7,sK5,sK6)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ! [X4] :
        ( k1_funct_1(sK7,X4) != sK4
        | ~ m1_subset_1(X4,sK5) )
    & r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7))
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK7,sK5,sK6)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f32,f47])).

fof(f84,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f48])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(flattening,[],[f29])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f83,plain,(
    v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f48])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f12])).

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
    inference(flattening,[],[f24])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f44,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) = X2
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f41,f44,f43,f42])).

fof(f67,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f98,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f82,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f48])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f85,plain,(
    r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f48])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f33])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & ~ r2_hidden(sK0(X0,X1,X2),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( r2_hidden(sK0(X0,X1,X2),X1)
          | r2_hidden(sK0(X0,X1,X2),X0)
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & ~ r2_hidden(sK0(X0,X1,X2),X0) )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( r2_hidden(sK0(X0,X1,X2),X1)
            | r2_hidden(sK0(X0,X1,X2),X0)
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f93,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f87,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f88,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f56,f87])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f60,f88])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f91,plain,(
    ! [X0,X1] : k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) != k1_xboole_0 ),
    inference(definition_unfolding,[],[f61,f88])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f68,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f97,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f86,plain,(
    ! [X4] :
      ( k1_funct_1(sK7,X4) != sK4
      | ~ m1_subset_1(X4,sK5) ) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1157,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1160,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5390,plain,
    ( k1_relset_1(sK5,sK6,sK7) = sK5
    | sK6 = k1_xboole_0
    | v1_funct_2(sK7,sK5,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1157,c_1160])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1167,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3175,plain,
    ( k1_relset_1(sK5,sK6,sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_1157,c_1167])).

cnf(c_5391,plain,
    ( k1_relat_1(sK7) = sK5
    | sK6 = k1_xboole_0
    | v1_funct_2(sK7,sK5,sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5390,c_3175])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_36,plain,
    ( v1_funct_2(sK7,sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_5485,plain,
    ( sK6 = k1_xboole_0
    | k1_relat_1(sK7) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5391,c_36])).

cnf(c_5486,plain,
    ( k1_relat_1(sK7) = sK5
    | sK6 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5485])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1169,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5489,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | r2_hidden(sK3(sK7,X0),sK5) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_5486,c_1169])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_35,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1607,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK5,sK6))
    | v1_relat_1(sK7) ),
    inference(resolution,[status(thm)],[c_11,c_32])).

cnf(c_14,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1612,plain,
    ( v1_relat_1(sK7) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1607,c_14])).

cnf(c_1613,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1612])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1166,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2907,plain,
    ( k2_relset_1(sK5,sK6,sK7) = k2_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_1157,c_1166])).

cnf(c_31,negated_conjecture,
    ( r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1158,plain,
    ( r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3353,plain,
    ( r2_hidden(sK4,k2_relat_1(sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2907,c_1158])).

cnf(c_21,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1168,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1988,plain,
    ( v5_relat_1(sK7,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1157,c_1168])).

cnf(c_13,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1176,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1182,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4001,plain,
    ( k2_xboole_0(k2_relat_1(X0),X1) = X1
    | v5_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1176,c_1182])).

cnf(c_4761,plain,
    ( k2_xboole_0(k2_relat_1(sK7),sK6) = sK6
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1988,c_4001])).

cnf(c_4764,plain,
    ( k2_xboole_0(k2_relat_1(sK7),sK6) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4761,c_1613])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1184,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4771,plain,
    ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_4764,c_1184])).

cnf(c_5629,plain,
    ( r2_hidden(sK4,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_3353,c_4771])).

cnf(c_7,plain,
    ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1181,plain,
    ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2623,plain,
    ( k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = X1
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1181,c_1182])).

cnf(c_5633,plain,
    ( k2_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK6) = sK6 ),
    inference(superposition,[status(thm)],[c_5629,c_2623])).

cnf(c_9,plain,
    ( k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_5694,plain,
    ( sK6 != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5633,c_9])).

cnf(c_5712,plain,
    ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | r2_hidden(sK3(sK7,X0),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5489,c_35,c_1613,c_5694])).

cnf(c_10,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1179,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5721,plain,
    ( m1_subset_1(sK3(sK7,X0),sK5) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5712,c_1179])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK3(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1170,plain,
    ( k1_funct_1(X0,sK3(X0,X1)) = X1
    | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5270,plain,
    ( k1_funct_1(sK7,sK3(sK7,sK4)) = sK4
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3353,c_1170])).

cnf(c_2770,plain,
    ( ~ r2_hidden(sK4,k2_relat_1(sK7))
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | k1_funct_1(sK7,sK3(sK7,sK4)) = sK4 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2774,plain,
    ( k1_funct_1(sK7,sK3(sK7,sK4)) = sK4
    | r2_hidden(sK4,k2_relat_1(sK7)) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2770])).

cnf(c_5394,plain,
    ( k1_funct_1(sK7,sK3(sK7,sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5270,c_35,c_1613,c_2774,c_3353])).

cnf(c_30,negated_conjecture,
    ( ~ m1_subset_1(X0,sK5)
    | k1_funct_1(sK7,X0) != sK4 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1159,plain,
    ( k1_funct_1(sK7,X0) != sK4
    | m1_subset_1(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_5397,plain,
    ( m1_subset_1(sK3(sK7,sK4),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5394,c_1159])).

cnf(c_7345,plain,
    ( r2_hidden(sK4,k2_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5721,c_5397])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7345,c_3353])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:39:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.62/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/0.99  
% 3.62/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.62/0.99  
% 3.62/0.99  ------  iProver source info
% 3.62/0.99  
% 3.62/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.62/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.62/0.99  git: non_committed_changes: false
% 3.62/0.99  git: last_make_outside_of_git: false
% 3.62/0.99  
% 3.62/0.99  ------ 
% 3.62/0.99  ------ Parsing...
% 3.62/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.62/0.99  
% 3.62/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.62/0.99  
% 3.62/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.62/0.99  
% 3.62/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.62/0.99  ------ Proving...
% 3.62/0.99  ------ Problem Properties 
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  clauses                                 35
% 3.62/0.99  conjectures                             5
% 3.62/0.99  EPR                                     3
% 3.62/0.99  Horn                                    27
% 3.62/0.99  unary                                   6
% 3.62/0.99  binary                                  10
% 3.62/0.99  lits                                    97
% 3.62/0.99  lits eq                                 23
% 3.62/0.99  fd_pure                                 0
% 3.62/0.99  fd_pseudo                               0
% 3.62/0.99  fd_cond                                 3
% 3.62/0.99  fd_pseudo_cond                          6
% 3.62/0.99  AC symbols                              0
% 3.62/0.99  
% 3.62/0.99  ------ Input Options Time Limit: Unbounded
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  ------ 
% 3.62/0.99  Current options:
% 3.62/0.99  ------ 
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  ------ Proving...
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  % SZS status Theorem for theBenchmark.p
% 3.62/0.99  
% 3.62/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.62/0.99  
% 3.62/0.99  fof(f17,conjecture,(
% 3.62/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f18,negated_conjecture,(
% 3.62/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 3.62/0.99    inference(negated_conjecture,[],[f17])).
% 3.62/0.99  
% 3.62/0.99  fof(f31,plain,(
% 3.62/0.99    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)))),
% 3.62/0.99    inference(ennf_transformation,[],[f18])).
% 3.62/0.99  
% 3.62/0.99  fof(f32,plain,(
% 3.62/0.99    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))),
% 3.62/0.99    inference(flattening,[],[f31])).
% 3.62/0.99  
% 3.62/0.99  fof(f47,plain,(
% 3.62/0.99    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (k1_funct_1(sK7,X4) != sK4 | ~m1_subset_1(X4,sK5)) & r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7))),
% 3.62/0.99    introduced(choice_axiom,[])).
% 3.62/0.99  
% 3.62/0.99  fof(f48,plain,(
% 3.62/0.99    ! [X4] : (k1_funct_1(sK7,X4) != sK4 | ~m1_subset_1(X4,sK5)) & r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7)),
% 3.62/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f32,f47])).
% 3.62/0.99  
% 3.62/0.99  fof(f84,plain,(
% 3.62/0.99    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 3.62/0.99    inference(cnf_transformation,[],[f48])).
% 3.62/0.99  
% 3.62/0.99  fof(f16,axiom,(
% 3.62/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f29,plain,(
% 3.62/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.62/0.99    inference(ennf_transformation,[],[f16])).
% 3.62/0.99  
% 3.62/0.99  fof(f30,plain,(
% 3.62/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.62/0.99    inference(flattening,[],[f29])).
% 3.62/0.99  
% 3.62/0.99  fof(f46,plain,(
% 3.62/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.62/0.99    inference(nnf_transformation,[],[f30])).
% 3.62/0.99  
% 3.62/0.99  fof(f76,plain,(
% 3.62/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.62/0.99    inference(cnf_transformation,[],[f46])).
% 3.62/0.99  
% 3.62/0.99  fof(f14,axiom,(
% 3.62/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f27,plain,(
% 3.62/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.62/0.99    inference(ennf_transformation,[],[f14])).
% 3.62/0.99  
% 3.62/0.99  fof(f74,plain,(
% 3.62/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.62/0.99    inference(cnf_transformation,[],[f27])).
% 3.62/0.99  
% 3.62/0.99  fof(f83,plain,(
% 3.62/0.99    v1_funct_2(sK7,sK5,sK6)),
% 3.62/0.99    inference(cnf_transformation,[],[f48])).
% 3.62/0.99  
% 3.62/0.99  fof(f12,axiom,(
% 3.62/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f24,plain,(
% 3.62/0.99    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.62/0.99    inference(ennf_transformation,[],[f12])).
% 3.62/0.99  
% 3.62/0.99  fof(f25,plain,(
% 3.62/0.99    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.62/0.99    inference(flattening,[],[f24])).
% 3.62/0.99  
% 3.62/0.99  fof(f40,plain,(
% 3.62/0.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.62/0.99    inference(nnf_transformation,[],[f25])).
% 3.62/0.99  
% 3.62/0.99  fof(f41,plain,(
% 3.62/0.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.62/0.99    inference(rectify,[],[f40])).
% 3.62/0.99  
% 3.62/0.99  fof(f44,plain,(
% 3.62/0.99    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))))),
% 3.62/0.99    introduced(choice_axiom,[])).
% 3.62/0.99  
% 3.62/0.99  fof(f43,plain,(
% 3.62/0.99    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) = X2 & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))) )),
% 3.62/0.99    introduced(choice_axiom,[])).
% 3.62/0.99  
% 3.62/0.99  fof(f42,plain,(
% 3.62/0.99    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1))))),
% 3.62/0.99    introduced(choice_axiom,[])).
% 3.62/0.99  
% 3.62/0.99  fof(f45,plain,(
% 3.62/0.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & ((k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.62/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f41,f44,f43,f42])).
% 3.62/0.99  
% 3.62/0.99  fof(f67,plain,(
% 3.62/0.99    ( ! [X0,X5,X1] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f45])).
% 3.62/0.99  
% 3.62/0.99  fof(f98,plain,(
% 3.62/0.99    ( ! [X0,X5] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.62/0.99    inference(equality_resolution,[],[f67])).
% 3.62/0.99  
% 3.62/0.99  fof(f82,plain,(
% 3.62/0.99    v1_funct_1(sK7)),
% 3.62/0.99    inference(cnf_transformation,[],[f48])).
% 3.62/0.99  
% 3.62/0.99  fof(f9,axiom,(
% 3.62/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f22,plain,(
% 3.62/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.62/0.99    inference(ennf_transformation,[],[f9])).
% 3.62/0.99  
% 3.62/0.99  fof(f63,plain,(
% 3.62/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f22])).
% 3.62/0.99  
% 3.62/0.99  fof(f11,axiom,(
% 3.62/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f66,plain,(
% 3.62/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.62/0.99    inference(cnf_transformation,[],[f11])).
% 3.62/0.99  
% 3.62/0.99  fof(f15,axiom,(
% 3.62/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f28,plain,(
% 3.62/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.62/0.99    inference(ennf_transformation,[],[f15])).
% 3.62/0.99  
% 3.62/0.99  fof(f75,plain,(
% 3.62/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.62/0.99    inference(cnf_transformation,[],[f28])).
% 3.62/0.99  
% 3.62/0.99  fof(f85,plain,(
% 3.62/0.99    r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7))),
% 3.62/0.99    inference(cnf_transformation,[],[f48])).
% 3.62/0.99  
% 3.62/0.99  fof(f13,axiom,(
% 3.62/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f19,plain,(
% 3.62/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.62/0.99    inference(pure_predicate_removal,[],[f13])).
% 3.62/0.99  
% 3.62/0.99  fof(f26,plain,(
% 3.62/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.62/0.99    inference(ennf_transformation,[],[f19])).
% 3.62/0.99  
% 3.62/0.99  fof(f73,plain,(
% 3.62/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.62/0.99    inference(cnf_transformation,[],[f26])).
% 3.62/0.99  
% 3.62/0.99  fof(f10,axiom,(
% 3.62/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f23,plain,(
% 3.62/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.62/0.99    inference(ennf_transformation,[],[f10])).
% 3.62/0.99  
% 3.62/0.99  fof(f39,plain,(
% 3.62/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.62/0.99    inference(nnf_transformation,[],[f23])).
% 3.62/0.99  
% 3.62/0.99  fof(f64,plain,(
% 3.62/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f39])).
% 3.62/0.99  
% 3.62/0.99  fof(f2,axiom,(
% 3.62/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f20,plain,(
% 3.62/0.99    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.62/0.99    inference(ennf_transformation,[],[f2])).
% 3.62/0.99  
% 3.62/0.99  fof(f55,plain,(
% 3.62/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f20])).
% 3.62/0.99  
% 3.62/0.99  fof(f1,axiom,(
% 3.62/0.99    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f33,plain,(
% 3.62/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.62/0.99    inference(nnf_transformation,[],[f1])).
% 3.62/0.99  
% 3.62/0.99  fof(f34,plain,(
% 3.62/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.62/0.99    inference(flattening,[],[f33])).
% 3.62/0.99  
% 3.62/0.99  fof(f35,plain,(
% 3.62/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.62/0.99    inference(rectify,[],[f34])).
% 3.62/0.99  
% 3.62/0.99  fof(f36,plain,(
% 3.62/0.99    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.62/0.99    introduced(choice_axiom,[])).
% 3.62/0.99  
% 3.62/0.99  fof(f37,plain,(
% 3.62/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.62/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).
% 3.62/0.99  
% 3.62/0.99  fof(f50,plain,(
% 3.62/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 3.62/0.99    inference(cnf_transformation,[],[f37])).
% 3.62/0.99  
% 3.62/0.99  fof(f93,plain,(
% 3.62/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 3.62/0.99    inference(equality_resolution,[],[f50])).
% 3.62/0.99  
% 3.62/0.99  fof(f6,axiom,(
% 3.62/0.99    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f38,plain,(
% 3.62/0.99    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 3.62/0.99    inference(nnf_transformation,[],[f6])).
% 3.62/0.99  
% 3.62/0.99  fof(f60,plain,(
% 3.62/0.99    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f38])).
% 3.62/0.99  
% 3.62/0.99  fof(f3,axiom,(
% 3.62/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f56,plain,(
% 3.62/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f3])).
% 3.62/0.99  
% 3.62/0.99  fof(f4,axiom,(
% 3.62/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f57,plain,(
% 3.62/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f4])).
% 3.62/0.99  
% 3.62/0.99  fof(f5,axiom,(
% 3.62/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f58,plain,(
% 3.62/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f5])).
% 3.62/0.99  
% 3.62/0.99  fof(f87,plain,(
% 3.62/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.62/0.99    inference(definition_unfolding,[],[f57,f58])).
% 3.62/0.99  
% 3.62/0.99  fof(f88,plain,(
% 3.62/0.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.62/0.99    inference(definition_unfolding,[],[f56,f87])).
% 3.62/0.99  
% 3.62/0.99  fof(f89,plain,(
% 3.62/0.99    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.62/0.99    inference(definition_unfolding,[],[f60,f88])).
% 3.62/0.99  
% 3.62/0.99  fof(f7,axiom,(
% 3.62/0.99    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f61,plain,(
% 3.62/0.99    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 3.62/0.99    inference(cnf_transformation,[],[f7])).
% 3.62/0.99  
% 3.62/0.99  fof(f91,plain,(
% 3.62/0.99    ( ! [X0,X1] : (k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) != k1_xboole_0) )),
% 3.62/0.99    inference(definition_unfolding,[],[f61,f88])).
% 3.62/0.99  
% 3.62/0.99  fof(f8,axiom,(
% 3.62/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f21,plain,(
% 3.62/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.62/0.99    inference(ennf_transformation,[],[f8])).
% 3.62/0.99  
% 3.62/0.99  fof(f62,plain,(
% 3.62/0.99    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f21])).
% 3.62/0.99  
% 3.62/0.99  fof(f68,plain,(
% 3.62/0.99    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK3(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f45])).
% 3.62/0.99  
% 3.62/0.99  fof(f97,plain,(
% 3.62/0.99    ( ! [X0,X5] : (k1_funct_1(X0,sK3(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.62/0.99    inference(equality_resolution,[],[f68])).
% 3.62/0.99  
% 3.62/0.99  fof(f86,plain,(
% 3.62/0.99    ( ! [X4] : (k1_funct_1(sK7,X4) != sK4 | ~m1_subset_1(X4,sK5)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f48])).
% 3.62/0.99  
% 3.62/0.99  cnf(c_32,negated_conjecture,
% 3.62/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 3.62/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1157,plain,
% 3.62/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_29,plain,
% 3.62/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.62/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.62/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.62/0.99      | k1_xboole_0 = X2 ),
% 3.62/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1160,plain,
% 3.62/0.99      ( k1_relset_1(X0,X1,X2) = X0
% 3.62/0.99      | k1_xboole_0 = X1
% 3.62/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.62/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_5390,plain,
% 3.62/0.99      ( k1_relset_1(sK5,sK6,sK7) = sK5
% 3.62/0.99      | sK6 = k1_xboole_0
% 3.62/0.99      | v1_funct_2(sK7,sK5,sK6) != iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_1157,c_1160]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_22,plain,
% 3.62/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.62/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.62/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1167,plain,
% 3.62/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.62/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_3175,plain,
% 3.62/0.99      ( k1_relset_1(sK5,sK6,sK7) = k1_relat_1(sK7) ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_1157,c_1167]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_5391,plain,
% 3.62/0.99      ( k1_relat_1(sK7) = sK5
% 3.62/0.99      | sK6 = k1_xboole_0
% 3.62/0.99      | v1_funct_2(sK7,sK5,sK6) != iProver_top ),
% 3.62/0.99      inference(demodulation,[status(thm)],[c_5390,c_3175]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_33,negated_conjecture,
% 3.62/0.99      ( v1_funct_2(sK7,sK5,sK6) ),
% 3.62/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_36,plain,
% 3.62/0.99      ( v1_funct_2(sK7,sK5,sK6) = iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_5485,plain,
% 3.62/0.99      ( sK6 = k1_xboole_0 | k1_relat_1(sK7) = sK5 ),
% 3.62/0.99      inference(global_propositional_subsumption,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_5391,c_36]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_5486,plain,
% 3.62/0.99      ( k1_relat_1(sK7) = sK5 | sK6 = k1_xboole_0 ),
% 3.62/0.99      inference(renaming,[status(thm)],[c_5485]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_20,plain,
% 3.62/0.99      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.62/0.99      | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
% 3.62/0.99      | ~ v1_funct_1(X1)
% 3.62/0.99      | ~ v1_relat_1(X1) ),
% 3.62/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1169,plain,
% 3.62/0.99      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 3.62/0.99      | r2_hidden(sK3(X1,X0),k1_relat_1(X1)) = iProver_top
% 3.62/0.99      | v1_funct_1(X1) != iProver_top
% 3.62/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_5489,plain,
% 3.62/0.99      ( sK6 = k1_xboole_0
% 3.62/0.99      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 3.62/0.99      | r2_hidden(sK3(sK7,X0),sK5) = iProver_top
% 3.62/0.99      | v1_funct_1(sK7) != iProver_top
% 3.62/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_5486,c_1169]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_34,negated_conjecture,
% 3.62/0.99      ( v1_funct_1(sK7) ),
% 3.62/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_35,plain,
% 3.62/0.99      ( v1_funct_1(sK7) = iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_11,plain,
% 3.62/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.62/0.99      | ~ v1_relat_1(X1)
% 3.62/0.99      | v1_relat_1(X0) ),
% 3.62/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1607,plain,
% 3.62/0.99      ( ~ v1_relat_1(k2_zfmisc_1(sK5,sK6)) | v1_relat_1(sK7) ),
% 3.62/0.99      inference(resolution,[status(thm)],[c_11,c_32]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_14,plain,
% 3.62/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.62/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1612,plain,
% 3.62/0.99      ( v1_relat_1(sK7) ),
% 3.62/0.99      inference(forward_subsumption_resolution,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_1607,c_14]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1613,plain,
% 3.62/0.99      ( v1_relat_1(sK7) = iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_1612]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_23,plain,
% 3.62/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.62/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.62/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1166,plain,
% 3.62/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.62/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2907,plain,
% 3.62/0.99      ( k2_relset_1(sK5,sK6,sK7) = k2_relat_1(sK7) ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_1157,c_1166]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_31,negated_conjecture,
% 3.62/0.99      ( r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) ),
% 3.62/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1158,plain,
% 3.62/0.99      ( r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) = iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_3353,plain,
% 3.62/0.99      ( r2_hidden(sK4,k2_relat_1(sK7)) = iProver_top ),
% 3.62/0.99      inference(demodulation,[status(thm)],[c_2907,c_1158]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_21,plain,
% 3.62/0.99      ( v5_relat_1(X0,X1)
% 3.62/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.62/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1168,plain,
% 3.62/0.99      ( v5_relat_1(X0,X1) = iProver_top
% 3.62/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1988,plain,
% 3.62/0.99      ( v5_relat_1(sK7,sK6) = iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_1157,c_1168]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_13,plain,
% 3.62/0.99      ( ~ v5_relat_1(X0,X1)
% 3.62/0.99      | r1_tarski(k2_relat_1(X0),X1)
% 3.62/0.99      | ~ v1_relat_1(X0) ),
% 3.62/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1176,plain,
% 3.62/0.99      ( v5_relat_1(X0,X1) != iProver_top
% 3.62/0.99      | r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 3.62/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_6,plain,
% 3.62/0.99      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 3.62/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1182,plain,
% 3.62/0.99      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_4001,plain,
% 3.62/0.99      ( k2_xboole_0(k2_relat_1(X0),X1) = X1
% 3.62/0.99      | v5_relat_1(X0,X1) != iProver_top
% 3.62/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_1176,c_1182]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_4761,plain,
% 3.62/0.99      ( k2_xboole_0(k2_relat_1(sK7),sK6) = sK6
% 3.62/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_1988,c_4001]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_4764,plain,
% 3.62/0.99      ( k2_xboole_0(k2_relat_1(sK7),sK6) = sK6 ),
% 3.62/0.99      inference(global_propositional_subsumption,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_4761,c_1613]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_4,plain,
% 3.62/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
% 3.62/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1184,plain,
% 3.62/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.62/0.99      | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_4771,plain,
% 3.62/0.99      ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 3.62/0.99      | r2_hidden(X0,sK6) = iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_4764,c_1184]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_5629,plain,
% 3.62/0.99      ( r2_hidden(sK4,sK6) = iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_3353,c_4771]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_7,plain,
% 3.62/0.99      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~ r2_hidden(X0,X1) ),
% 3.62/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1181,plain,
% 3.62/0.99      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) = iProver_top
% 3.62/0.99      | r2_hidden(X0,X1) != iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2623,plain,
% 3.62/0.99      ( k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = X1
% 3.62/0.99      | r2_hidden(X0,X1) != iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_1181,c_1182]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_5633,plain,
% 3.62/0.99      ( k2_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK6) = sK6 ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_5629,c_2623]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_9,plain,
% 3.62/0.99      ( k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) != k1_xboole_0 ),
% 3.62/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_5694,plain,
% 3.62/0.99      ( sK6 != k1_xboole_0 ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_5633,c_9]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_5712,plain,
% 3.62/0.99      ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 3.62/0.99      | r2_hidden(sK3(sK7,X0),sK5) = iProver_top ),
% 3.62/0.99      inference(global_propositional_subsumption,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_5489,c_35,c_1613,c_5694]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_10,plain,
% 3.62/0.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.62/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1179,plain,
% 3.62/0.99      ( m1_subset_1(X0,X1) = iProver_top
% 3.62/0.99      | r2_hidden(X0,X1) != iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_5721,plain,
% 3.62/0.99      ( m1_subset_1(sK3(sK7,X0),sK5) = iProver_top
% 3.62/0.99      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_5712,c_1179]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_19,plain,
% 3.62/0.99      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.62/0.99      | ~ v1_funct_1(X1)
% 3.62/0.99      | ~ v1_relat_1(X1)
% 3.62/0.99      | k1_funct_1(X1,sK3(X1,X0)) = X0 ),
% 3.62/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1170,plain,
% 3.62/0.99      ( k1_funct_1(X0,sK3(X0,X1)) = X1
% 3.62/0.99      | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
% 3.62/0.99      | v1_funct_1(X0) != iProver_top
% 3.62/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_5270,plain,
% 3.62/0.99      ( k1_funct_1(sK7,sK3(sK7,sK4)) = sK4
% 3.62/0.99      | v1_funct_1(sK7) != iProver_top
% 3.62/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_3353,c_1170]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2770,plain,
% 3.62/0.99      ( ~ r2_hidden(sK4,k2_relat_1(sK7))
% 3.62/0.99      | ~ v1_funct_1(sK7)
% 3.62/0.99      | ~ v1_relat_1(sK7)
% 3.62/0.99      | k1_funct_1(sK7,sK3(sK7,sK4)) = sK4 ),
% 3.62/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2774,plain,
% 3.62/0.99      ( k1_funct_1(sK7,sK3(sK7,sK4)) = sK4
% 3.62/0.99      | r2_hidden(sK4,k2_relat_1(sK7)) != iProver_top
% 3.62/0.99      | v1_funct_1(sK7) != iProver_top
% 3.62/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_2770]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_5394,plain,
% 3.62/0.99      ( k1_funct_1(sK7,sK3(sK7,sK4)) = sK4 ),
% 3.62/0.99      inference(global_propositional_subsumption,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_5270,c_35,c_1613,c_2774,c_3353]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_30,negated_conjecture,
% 3.62/0.99      ( ~ m1_subset_1(X0,sK5) | k1_funct_1(sK7,X0) != sK4 ),
% 3.62/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1159,plain,
% 3.62/0.99      ( k1_funct_1(sK7,X0) != sK4 | m1_subset_1(X0,sK5) != iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_5397,plain,
% 3.62/0.99      ( m1_subset_1(sK3(sK7,sK4),sK5) != iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_5394,c_1159]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_7345,plain,
% 3.62/0.99      ( r2_hidden(sK4,k2_relat_1(sK7)) != iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_5721,c_5397]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(contradiction,plain,
% 3.62/0.99      ( $false ),
% 3.62/0.99      inference(minisat,[status(thm)],[c_7345,c_3353]) ).
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.62/0.99  
% 3.62/0.99  ------                               Statistics
% 3.62/0.99  
% 3.62/0.99  ------ Selected
% 3.62/0.99  
% 3.62/0.99  total_time:                             0.251
% 3.62/0.99  
%------------------------------------------------------------------------------
