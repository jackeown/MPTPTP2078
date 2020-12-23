%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:00 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 511 expanded)
%              Number of clauses        :   92 ( 194 expanded)
%              Number of leaves         :   25 ( 105 expanded)
%              Depth                    :   18
%              Number of atoms          :  546 (2146 expanded)
%              Number of equality atoms :  212 ( 608 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   2 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f37,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f38,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f37])).

fof(f52,plain,
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

fof(f53,plain,
    ( ! [X4] :
        ( k1_funct_1(sK7,X4) != sK4
        | ~ m1_subset_1(X4,sK5) )
    & r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7))
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK7,sK5,sK6)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f38,f52])).

fof(f88,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f53])).

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

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f87,plain,(
    v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f53])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

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

fof(f45,plain,(
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

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f49,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
        & r2_hidden(sK3(X0,X1,X6),X1)
        & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1,X2)) = X3
        & r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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

fof(f50,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f46,f49,f48,f47])).

fof(f64,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f95,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f86,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f53])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f89,plain,(
    r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f53])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).

fof(f54,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f55,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f66,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f93,plain,(
    ! [X6,X0,X1] :
      ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f90,plain,(
    ! [X4] :
      ( k1_funct_1(sK7,X4) != sK4
      | ~ m1_subset_1(X4,sK5) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1215,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1218,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1723,plain,
    ( k1_relset_1(sK5,sK6,sK7) = sK5
    | sK6 = k1_xboole_0
    | v1_funct_2(sK7,sK5,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1215,c_1218])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1724,plain,
    ( ~ v1_funct_2(sK7,sK5,sK6)
    | k1_relset_1(sK5,sK6,sK7) = sK5
    | sK6 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1723])).

cnf(c_2066,plain,
    ( sK6 = k1_xboole_0
    | k1_relset_1(sK5,sK6,sK7) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1723,c_35,c_1724])).

cnf(c_2067,plain,
    ( k1_relset_1(sK5,sK6,sK7) = sK5
    | sK6 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2066])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1227,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2548,plain,
    ( k1_relset_1(sK5,sK6,sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_1215,c_1227])).

cnf(c_2878,plain,
    ( k1_relat_1(sK7) = sK5
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2067,c_2548])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1232,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5325,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(sK7,X1,X0),sK5) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2878,c_1232])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_37,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_39,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1582,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1583,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1582])).

cnf(c_6244,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(sK7,X1,X0),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5325,c_37,c_39,c_1583])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1244,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1242,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4615,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1244,c_1242])).

cnf(c_12089,plain,
    ( sK6 = k1_xboole_0
    | m1_subset_1(sK3(sK7,X0,X1),X2) = iProver_top
    | r1_tarski(sK5,X2) != iProver_top
    | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6244,c_4615])).

cnf(c_33,negated_conjecture,
    ( r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_426,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_449,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_426])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1552,plain,
    ( ~ r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7))
    | ~ v1_xboole_0(k2_relset_1(sK5,sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1625,plain,
    ( m1_subset_1(k2_relset_1(sK5,sK6,sK7),k1_zfmisc_1(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_264,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_265,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_264])).

cnf(c_335,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_3,c_265])).

cnf(c_1762,plain,
    ( ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),X0)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_relset_1(sK5,sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_335])).

cnf(c_1767,plain,
    ( ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_xboole_0)
    | v1_xboole_0(k2_relset_1(sK5,sK6,sK7))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1762])).

cnf(c_2,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1734,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_18])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2005,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1734,c_0])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2016,plain,
    ( ~ m1_subset_1(k2_relset_1(sK5,sK6,sK7),k1_zfmisc_1(X0))
    | r1_tarski(k2_relset_1(sK5,sK6,sK7),X0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2018,plain,
    ( ~ m1_subset_1(k2_relset_1(sK5,sK6,sK7),k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2016])).

cnf(c_427,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3058,plain,
    ( X0 != X1
    | X0 = sK6
    | sK6 != X1 ),
    inference(instantiation,[status(thm)],[c_427])).

cnf(c_3059,plain,
    ( sK6 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3058])).

cnf(c_3258,plain,
    ( k2_relset_1(sK5,sK6,sK7) = k2_relset_1(sK5,sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_426])).

cnf(c_431,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1637,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_431])).

cnf(c_2112,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X3))
    | X2 != X0
    | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1637])).

cnf(c_3841,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k2_relset_1(sK5,sK6,sK7),k1_zfmisc_1(X2))
    | k2_relset_1(sK5,sK6,sK7) != X0
    | k1_zfmisc_1(X2) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_2112])).

cnf(c_4547,plain,
    ( ~ m1_subset_1(k2_relset_1(sK5,sK6,sK7),k1_zfmisc_1(X0))
    | m1_subset_1(k2_relset_1(sK5,sK6,sK7),k1_zfmisc_1(X1))
    | k2_relset_1(sK5,sK6,sK7) != k2_relset_1(sK5,sK6,sK7)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_3841])).

cnf(c_5409,plain,
    ( m1_subset_1(k2_relset_1(sK5,sK6,sK7),k1_zfmisc_1(X0))
    | ~ m1_subset_1(k2_relset_1(sK5,sK6,sK7),k1_zfmisc_1(sK6))
    | k2_relset_1(sK5,sK6,sK7) != k2_relset_1(sK5,sK6,sK7)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK6) ),
    inference(instantiation,[status(thm)],[c_4547])).

cnf(c_5411,plain,
    ( ~ m1_subset_1(k2_relset_1(sK5,sK6,sK7),k1_zfmisc_1(sK6))
    | m1_subset_1(k2_relset_1(sK5,sK6,sK7),k1_zfmisc_1(k1_xboole_0))
    | k2_relset_1(sK5,sK6,sK7) != k2_relset_1(sK5,sK6,sK7)
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(sK6) ),
    inference(instantiation,[status(thm)],[c_5409])).

cnf(c_430,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_9407,plain,
    ( X0 != sK6
    | k1_zfmisc_1(X0) = k1_zfmisc_1(sK6) ),
    inference(instantiation,[status(thm)],[c_430])).

cnf(c_9408,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(sK6)
    | k1_xboole_0 != sK6 ),
    inference(instantiation,[status(thm)],[c_9407])).

cnf(c_13324,plain,
    ( m1_subset_1(sK3(sK7,X0,X1),X2) = iProver_top
    | r1_tarski(sK5,X2) != iProver_top
    | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12089,c_34,c_33,c_449,c_1552,c_1625,c_1767,c_2005,c_2018,c_3059,c_3258,c_5411,c_9408])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1224,plain,
    ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4456,plain,
    ( k7_relset_1(sK5,sK6,sK7,sK5) = k2_relset_1(sK5,sK6,sK7) ),
    inference(superposition,[status(thm)],[c_1215,c_1224])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1226,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2762,plain,
    ( k7_relset_1(sK5,sK6,sK7,X0) = k9_relat_1(sK7,X0) ),
    inference(superposition,[status(thm)],[c_1215,c_1226])).

cnf(c_4458,plain,
    ( k2_relset_1(sK5,sK6,sK7) = k9_relat_1(sK7,sK5) ),
    inference(demodulation,[status(thm)],[c_4456,c_2762])).

cnf(c_1216,plain,
    ( r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4858,plain,
    ( r2_hidden(sK4,k9_relat_1(sK7,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4458,c_1216])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK3(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1234,plain,
    ( k1_funct_1(X0,sK3(X0,X1,X2)) = X2
    | r2_hidden(X2,k9_relat_1(X0,X1)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5528,plain,
    ( k1_funct_1(sK7,sK3(sK7,sK5,sK4)) = sK4
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_4858,c_1234])).

cnf(c_5922,plain,
    ( k1_funct_1(sK7,sK3(sK7,sK5,sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5528,c_37,c_39,c_1583])).

cnf(c_32,negated_conjecture,
    ( ~ m1_subset_1(X0,sK5)
    | k1_funct_1(sK7,X0) != sK4 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1217,plain,
    ( k1_funct_1(sK7,X0) != sK4
    | m1_subset_1(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_5926,plain,
    ( m1_subset_1(sK3(sK7,sK5,sK4),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5922,c_1217])).

cnf(c_13346,plain,
    ( r1_tarski(sK5,sK5) != iProver_top
    | r2_hidden(sK4,k9_relat_1(sK7,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13324,c_5926])).

cnf(c_20,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1229,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2446,plain,
    ( v4_relat_1(sK7,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1215,c_1229])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1240,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3530,plain,
    ( sK6 = k1_xboole_0
    | v4_relat_1(sK7,X0) != iProver_top
    | r1_tarski(sK5,X0) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2878,c_1240])).

cnf(c_3770,plain,
    ( r1_tarski(sK5,X0) = iProver_top
    | v4_relat_1(sK7,X0) != iProver_top
    | sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3530,c_39,c_1583])).

cnf(c_3771,plain,
    ( sK6 = k1_xboole_0
    | v4_relat_1(sK7,X0) != iProver_top
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_3770])).

cnf(c_3779,plain,
    ( sK6 = k1_xboole_0
    | r1_tarski(sK5,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2446,c_3771])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13346,c_9408,c_5411,c_4858,c_3779,c_3258,c_3059,c_2018,c_2005,c_1767,c_1625,c_1552,c_449,c_33,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:53:40 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.73/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/0.98  
% 3.73/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.73/0.98  
% 3.73/0.98  ------  iProver source info
% 3.73/0.98  
% 3.73/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.73/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.73/0.98  git: non_committed_changes: false
% 3.73/0.98  git: last_make_outside_of_git: false
% 3.73/0.98  
% 3.73/0.98  ------ 
% 3.73/0.98  ------ Parsing...
% 3.73/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.73/0.98  
% 3.73/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.73/0.98  
% 3.73/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.73/0.98  
% 3.73/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/0.98  ------ Proving...
% 3.73/0.98  ------ Problem Properties 
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  clauses                                 37
% 3.73/0.98  conjectures                             5
% 3.73/0.98  EPR                                     7
% 3.73/0.98  Horn                                    28
% 3.73/0.98  unary                                   5
% 3.73/0.98  binary                                  13
% 3.73/0.98  lits                                    106
% 3.73/0.98  lits eq                                 21
% 3.73/0.98  fd_pure                                 0
% 3.73/0.98  fd_pseudo                               0
% 3.73/0.98  fd_cond                                 3
% 3.73/0.98  fd_pseudo_cond                          4
% 3.73/0.98  AC symbols                              0
% 3.73/0.98  
% 3.73/0.98  ------ Input Options Time Limit: Unbounded
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  ------ 
% 3.73/0.98  Current options:
% 3.73/0.98  ------ 
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  ------ Proving...
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  % SZS status Theorem for theBenchmark.p
% 3.73/0.98  
% 3.73/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.73/0.98  
% 3.73/0.98  fof(f17,conjecture,(
% 3.73/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f18,negated_conjecture,(
% 3.73/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 3.73/0.98    inference(negated_conjecture,[],[f17])).
% 3.73/0.98  
% 3.73/0.98  fof(f37,plain,(
% 3.73/0.98    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)))),
% 3.73/0.98    inference(ennf_transformation,[],[f18])).
% 3.73/0.98  
% 3.73/0.98  fof(f38,plain,(
% 3.73/0.98    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))),
% 3.73/0.98    inference(flattening,[],[f37])).
% 3.73/0.98  
% 3.73/0.98  fof(f52,plain,(
% 3.73/0.98    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (k1_funct_1(sK7,X4) != sK4 | ~m1_subset_1(X4,sK5)) & r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7))),
% 3.73/0.98    introduced(choice_axiom,[])).
% 3.73/0.98  
% 3.73/0.98  fof(f53,plain,(
% 3.73/0.98    ! [X4] : (k1_funct_1(sK7,X4) != sK4 | ~m1_subset_1(X4,sK5)) & r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7)),
% 3.73/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f38,f52])).
% 3.73/0.98  
% 3.73/0.98  fof(f88,plain,(
% 3.73/0.98    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 3.73/0.98    inference(cnf_transformation,[],[f53])).
% 3.73/0.98  
% 3.73/0.98  fof(f16,axiom,(
% 3.73/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f35,plain,(
% 3.73/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.73/0.98    inference(ennf_transformation,[],[f16])).
% 3.73/0.98  
% 3.73/0.98  fof(f36,plain,(
% 3.73/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.73/0.98    inference(flattening,[],[f35])).
% 3.73/0.98  
% 3.73/0.98  fof(f51,plain,(
% 3.73/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.73/0.98    inference(nnf_transformation,[],[f36])).
% 3.73/0.98  
% 3.73/0.98  fof(f80,plain,(
% 3.73/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.73/0.98    inference(cnf_transformation,[],[f51])).
% 3.73/0.98  
% 3.73/0.98  fof(f87,plain,(
% 3.73/0.98    v1_funct_2(sK7,sK5,sK6)),
% 3.73/0.98    inference(cnf_transformation,[],[f53])).
% 3.73/0.98  
% 3.73/0.98  fof(f13,axiom,(
% 3.73/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f32,plain,(
% 3.73/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.73/0.98    inference(ennf_transformation,[],[f13])).
% 3.73/0.98  
% 3.73/0.98  fof(f76,plain,(
% 3.73/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.73/0.98    inference(cnf_transformation,[],[f32])).
% 3.73/0.98  
% 3.73/0.98  fof(f8,axiom,(
% 3.73/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f26,plain,(
% 3.73/0.98    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.73/0.98    inference(ennf_transformation,[],[f8])).
% 3.73/0.98  
% 3.73/0.98  fof(f27,plain,(
% 3.73/0.98    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.73/0.98    inference(flattening,[],[f26])).
% 3.73/0.98  
% 3.73/0.98  fof(f45,plain,(
% 3.73/0.98    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.73/0.98    inference(nnf_transformation,[],[f27])).
% 3.73/0.98  
% 3.73/0.98  fof(f46,plain,(
% 3.73/0.98    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.73/0.98    inference(rectify,[],[f45])).
% 3.73/0.98  
% 3.73/0.98  fof(f49,plain,(
% 3.73/0.98    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1,X6)) = X6 & r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))))),
% 3.73/0.98    introduced(choice_axiom,[])).
% 3.73/0.98  
% 3.73/0.98  fof(f48,plain,(
% 3.73/0.98    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1,X2)) = X3 & r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))))) )),
% 3.73/0.98    introduced(choice_axiom,[])).
% 3.73/0.98  
% 3.73/0.98  fof(f47,plain,(
% 3.73/0.98    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK1(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK1(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.73/0.98    introduced(choice_axiom,[])).
% 3.73/0.98  
% 3.73/0.98  fof(f50,plain,(
% 3.73/0.98    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK1(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((k1_funct_1(X0,sK2(X0,X1,X2)) = sK1(X0,X1,X2) & r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X1,X6)) = X6 & r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.73/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f46,f49,f48,f47])).
% 3.73/0.98  
% 3.73/0.98  fof(f64,plain,(
% 3.73/0.98    ( ! [X6,X2,X0,X1] : (r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f50])).
% 3.73/0.98  
% 3.73/0.98  fof(f95,plain,(
% 3.73/0.98    ( ! [X6,X0,X1] : (r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.73/0.98    inference(equality_resolution,[],[f64])).
% 3.73/0.98  
% 3.73/0.98  fof(f86,plain,(
% 3.73/0.98    v1_funct_1(sK7)),
% 3.73/0.98    inference(cnf_transformation,[],[f53])).
% 3.73/0.98  
% 3.73/0.98  fof(f10,axiom,(
% 3.73/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f29,plain,(
% 3.73/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.73/0.98    inference(ennf_transformation,[],[f10])).
% 3.73/0.98  
% 3.73/0.98  fof(f73,plain,(
% 3.73/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.73/0.98    inference(cnf_transformation,[],[f29])).
% 3.73/0.98  
% 3.73/0.98  fof(f5,axiom,(
% 3.73/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f43,plain,(
% 3.73/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.73/0.98    inference(nnf_transformation,[],[f5])).
% 3.73/0.98  
% 3.73/0.98  fof(f60,plain,(
% 3.73/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f43])).
% 3.73/0.98  
% 3.73/0.98  fof(f6,axiom,(
% 3.73/0.98    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f23,plain,(
% 3.73/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.73/0.98    inference(ennf_transformation,[],[f6])).
% 3.73/0.98  
% 3.73/0.98  fof(f24,plain,(
% 3.73/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.73/0.98    inference(flattening,[],[f23])).
% 3.73/0.98  
% 3.73/0.98  fof(f61,plain,(
% 3.73/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f24])).
% 3.73/0.98  
% 3.73/0.98  fof(f89,plain,(
% 3.73/0.98    r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7))),
% 3.73/0.98    inference(cnf_transformation,[],[f53])).
% 3.73/0.98  
% 3.73/0.98  fof(f1,axiom,(
% 3.73/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f39,plain,(
% 3.73/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.73/0.98    inference(nnf_transformation,[],[f1])).
% 3.73/0.98  
% 3.73/0.98  fof(f40,plain,(
% 3.73/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.73/0.98    inference(rectify,[],[f39])).
% 3.73/0.98  
% 3.73/0.98  fof(f41,plain,(
% 3.73/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.73/0.98    introduced(choice_axiom,[])).
% 3.73/0.98  
% 3.73/0.98  fof(f42,plain,(
% 3.73/0.98    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.73/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).
% 3.73/0.98  
% 3.73/0.98  fof(f54,plain,(
% 3.73/0.98    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f42])).
% 3.73/0.98  
% 3.73/0.98  fof(f12,axiom,(
% 3.73/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f31,plain,(
% 3.73/0.98    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.73/0.98    inference(ennf_transformation,[],[f12])).
% 3.73/0.98  
% 3.73/0.98  fof(f75,plain,(
% 3.73/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.73/0.98    inference(cnf_transformation,[],[f31])).
% 3.73/0.98  
% 3.73/0.98  fof(f3,axiom,(
% 3.73/0.98    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f20,plain,(
% 3.73/0.98    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.73/0.98    inference(ennf_transformation,[],[f3])).
% 3.73/0.98  
% 3.73/0.98  fof(f57,plain,(
% 3.73/0.98    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f20])).
% 3.73/0.98  
% 3.73/0.98  fof(f2,axiom,(
% 3.73/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f56,plain,(
% 3.73/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f2])).
% 3.73/0.98  
% 3.73/0.98  fof(f9,axiom,(
% 3.73/0.98    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f28,plain,(
% 3.73/0.98    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.73/0.98    inference(ennf_transformation,[],[f9])).
% 3.73/0.98  
% 3.73/0.98  fof(f72,plain,(
% 3.73/0.98    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f28])).
% 3.73/0.98  
% 3.73/0.98  fof(f55,plain,(
% 3.73/0.98    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f42])).
% 3.73/0.98  
% 3.73/0.98  fof(f59,plain,(
% 3.73/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.73/0.98    inference(cnf_transformation,[],[f43])).
% 3.73/0.98  
% 3.73/0.98  fof(f15,axiom,(
% 3.73/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f34,plain,(
% 3.73/0.98    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.73/0.98    inference(ennf_transformation,[],[f15])).
% 3.73/0.98  
% 3.73/0.98  fof(f78,plain,(
% 3.73/0.98    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.73/0.98    inference(cnf_transformation,[],[f34])).
% 3.73/0.98  
% 3.73/0.98  fof(f14,axiom,(
% 3.73/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f33,plain,(
% 3.73/0.98    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.73/0.98    inference(ennf_transformation,[],[f14])).
% 3.73/0.98  
% 3.73/0.98  fof(f77,plain,(
% 3.73/0.98    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.73/0.98    inference(cnf_transformation,[],[f33])).
% 3.73/0.98  
% 3.73/0.98  fof(f66,plain,(
% 3.73/0.98    ( ! [X6,X2,X0,X1] : (k1_funct_1(X0,sK3(X0,X1,X6)) = X6 | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f50])).
% 3.73/0.98  
% 3.73/0.98  fof(f93,plain,(
% 3.73/0.98    ( ! [X6,X0,X1] : (k1_funct_1(X0,sK3(X0,X1,X6)) = X6 | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.73/0.98    inference(equality_resolution,[],[f66])).
% 3.73/0.98  
% 3.73/0.98  fof(f90,plain,(
% 3.73/0.98    ( ! [X4] : (k1_funct_1(sK7,X4) != sK4 | ~m1_subset_1(X4,sK5)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f53])).
% 3.73/0.98  
% 3.73/0.98  fof(f11,axiom,(
% 3.73/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f19,plain,(
% 3.73/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.73/0.98    inference(pure_predicate_removal,[],[f11])).
% 3.73/0.98  
% 3.73/0.98  fof(f30,plain,(
% 3.73/0.98    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.73/0.98    inference(ennf_transformation,[],[f19])).
% 3.73/0.98  
% 3.73/0.98  fof(f74,plain,(
% 3.73/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.73/0.98    inference(cnf_transformation,[],[f30])).
% 3.73/0.98  
% 3.73/0.98  fof(f7,axiom,(
% 3.73/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f25,plain,(
% 3.73/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.73/0.98    inference(ennf_transformation,[],[f7])).
% 3.73/0.98  
% 3.73/0.98  fof(f44,plain,(
% 3.73/0.98    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.73/0.98    inference(nnf_transformation,[],[f25])).
% 3.73/0.98  
% 3.73/0.98  fof(f62,plain,(
% 3.73/0.98    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f44])).
% 3.73/0.98  
% 3.73/0.98  cnf(c_34,negated_conjecture,
% 3.73/0.98      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 3.73/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1215,plain,
% 3.73/0.98      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_31,plain,
% 3.73/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.73/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.73/0.98      | k1_xboole_0 = X2 ),
% 3.73/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1218,plain,
% 3.73/0.98      ( k1_relset_1(X0,X1,X2) = X0
% 3.73/0.98      | k1_xboole_0 = X1
% 3.73/0.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.73/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1723,plain,
% 3.73/0.98      ( k1_relset_1(sK5,sK6,sK7) = sK5
% 3.73/0.98      | sK6 = k1_xboole_0
% 3.73/0.98      | v1_funct_2(sK7,sK5,sK6) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_1215,c_1218]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_35,negated_conjecture,
% 3.73/0.98      ( v1_funct_2(sK7,sK5,sK6) ),
% 3.73/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1724,plain,
% 3.73/0.98      ( ~ v1_funct_2(sK7,sK5,sK6)
% 3.73/0.98      | k1_relset_1(sK5,sK6,sK7) = sK5
% 3.73/0.98      | sK6 = k1_xboole_0 ),
% 3.73/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_1723]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2066,plain,
% 3.73/0.98      ( sK6 = k1_xboole_0 | k1_relset_1(sK5,sK6,sK7) = sK5 ),
% 3.73/0.98      inference(global_propositional_subsumption,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_1723,c_35,c_1724]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2067,plain,
% 3.73/0.98      ( k1_relset_1(sK5,sK6,sK7) = sK5 | sK6 = k1_xboole_0 ),
% 3.73/0.98      inference(renaming,[status(thm)],[c_2066]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_22,plain,
% 3.73/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.73/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1227,plain,
% 3.73/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.73/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2548,plain,
% 3.73/0.98      ( k1_relset_1(sK5,sK6,sK7) = k1_relat_1(sK7) ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_1215,c_1227]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2878,plain,
% 3.73/0.98      ( k1_relat_1(sK7) = sK5 | sK6 = k1_xboole_0 ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_2067,c_2548]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_17,plain,
% 3.73/0.98      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.73/0.98      | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1))
% 3.73/0.98      | ~ v1_funct_1(X1)
% 3.73/0.98      | ~ v1_relat_1(X1) ),
% 3.73/0.98      inference(cnf_transformation,[],[f95]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1232,plain,
% 3.73/0.98      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.73/0.98      | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1)) = iProver_top
% 3.73/0.98      | v1_funct_1(X1) != iProver_top
% 3.73/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_5325,plain,
% 3.73/0.98      ( sK6 = k1_xboole_0
% 3.73/0.98      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.73/0.98      | r2_hidden(sK3(sK7,X1,X0),sK5) = iProver_top
% 3.73/0.98      | v1_funct_1(sK7) != iProver_top
% 3.73/0.98      | v1_relat_1(sK7) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_2878,c_1232]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_36,negated_conjecture,
% 3.73/0.98      ( v1_funct_1(sK7) ),
% 3.73/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_37,plain,
% 3.73/0.98      ( v1_funct_1(sK7) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_39,plain,
% 3.73/0.98      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_19,plain,
% 3.73/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/0.98      | v1_relat_1(X0) ),
% 3.73/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1582,plain,
% 3.73/0.98      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.73/0.98      | v1_relat_1(sK7) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_19]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1583,plain,
% 3.73/0.98      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.73/0.98      | v1_relat_1(sK7) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_1582]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_6244,plain,
% 3.73/0.98      ( sK6 = k1_xboole_0
% 3.73/0.98      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.73/0.98      | r2_hidden(sK3(sK7,X1,X0),sK5) = iProver_top ),
% 3.73/0.98      inference(global_propositional_subsumption,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_5325,c_37,c_39,c_1583]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_5,plain,
% 3.73/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.73/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1244,plain,
% 3.73/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.73/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_7,plain,
% 3.73/0.98      ( m1_subset_1(X0,X1)
% 3.73/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.73/0.98      | ~ r2_hidden(X0,X2) ),
% 3.73/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1242,plain,
% 3.73/0.98      ( m1_subset_1(X0,X1) = iProver_top
% 3.73/0.98      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 3.73/0.98      | r2_hidden(X0,X2) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_4615,plain,
% 3.73/0.98      ( m1_subset_1(X0,X1) = iProver_top
% 3.73/0.98      | r1_tarski(X2,X1) != iProver_top
% 3.73/0.98      | r2_hidden(X0,X2) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_1244,c_1242]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_12089,plain,
% 3.73/0.98      ( sK6 = k1_xboole_0
% 3.73/0.98      | m1_subset_1(sK3(sK7,X0,X1),X2) = iProver_top
% 3.73/0.98      | r1_tarski(sK5,X2) != iProver_top
% 3.73/0.98      | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_6244,c_4615]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_33,negated_conjecture,
% 3.73/0.98      ( r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) ),
% 3.73/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_426,plain,( X0 = X0 ),theory(equality) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_449,plain,
% 3.73/0.98      ( k1_xboole_0 = k1_xboole_0 ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_426]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1,plain,
% 3.73/0.98      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.73/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1552,plain,
% 3.73/0.98      ( ~ r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7))
% 3.73/0.98      | ~ v1_xboole_0(k2_relset_1(sK5,sK6,sK7)) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_21,plain,
% 3.73/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/0.98      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 3.73/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1625,plain,
% 3.73/0.98      ( m1_subset_1(k2_relset_1(sK5,sK6,sK7),k1_zfmisc_1(sK6))
% 3.73/0.98      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_21]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3,plain,
% 3.73/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.73/0.98      | ~ v1_xboole_0(X1)
% 3.73/0.98      | v1_xboole_0(X0) ),
% 3.73/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_264,plain,
% 3.73/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.73/0.98      inference(prop_impl,[status(thm)],[c_5]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_265,plain,
% 3.73/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.73/0.98      inference(renaming,[status(thm)],[c_264]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_335,plain,
% 3.73/0.98      ( ~ r1_tarski(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 3.73/0.98      inference(bin_hyper_res,[status(thm)],[c_3,c_265]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1762,plain,
% 3.73/0.98      ( ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),X0)
% 3.73/0.98      | ~ v1_xboole_0(X0)
% 3.73/0.98      | v1_xboole_0(k2_relset_1(sK5,sK6,sK7)) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_335]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1767,plain,
% 3.73/0.98      ( ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_xboole_0)
% 3.73/0.98      | v1_xboole_0(k2_relset_1(sK5,sK6,sK7))
% 3.73/0.98      | ~ v1_xboole_0(k1_xboole_0) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_1762]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2,plain,
% 3.73/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 3.73/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_18,plain,
% 3.73/0.98      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.73/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1734,plain,
% 3.73/0.98      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.73/0.98      inference(resolution,[status(thm)],[c_2,c_18]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_0,plain,
% 3.73/0.98      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.73/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2005,plain,
% 3.73/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 3.73/0.98      inference(resolution,[status(thm)],[c_1734,c_0]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_6,plain,
% 3.73/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.73/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2016,plain,
% 3.73/0.98      ( ~ m1_subset_1(k2_relset_1(sK5,sK6,sK7),k1_zfmisc_1(X0))
% 3.73/0.98      | r1_tarski(k2_relset_1(sK5,sK6,sK7),X0) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2018,plain,
% 3.73/0.98      ( ~ m1_subset_1(k2_relset_1(sK5,sK6,sK7),k1_zfmisc_1(k1_xboole_0))
% 3.73/0.98      | r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_xboole_0) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_2016]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_427,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3058,plain,
% 3.73/0.98      ( X0 != X1 | X0 = sK6 | sK6 != X1 ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_427]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3059,plain,
% 3.73/0.98      ( sK6 != k1_xboole_0
% 3.73/0.98      | k1_xboole_0 = sK6
% 3.73/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_3058]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3258,plain,
% 3.73/0.98      ( k2_relset_1(sK5,sK6,sK7) = k2_relset_1(sK5,sK6,sK7) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_426]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_431,plain,
% 3.73/0.98      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.73/0.98      theory(equality) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1637,plain,
% 3.73/0.98      ( m1_subset_1(X0,X1)
% 3.73/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 3.73/0.98      | X0 != X2
% 3.73/0.98      | X1 != k1_zfmisc_1(X3) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_431]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2112,plain,
% 3.73/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.73/0.98      | m1_subset_1(X2,k1_zfmisc_1(X3))
% 3.73/0.98      | X2 != X0
% 3.73/0.98      | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_1637]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3841,plain,
% 3.73/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.73/0.98      | m1_subset_1(k2_relset_1(sK5,sK6,sK7),k1_zfmisc_1(X2))
% 3.73/0.98      | k2_relset_1(sK5,sK6,sK7) != X0
% 3.73/0.98      | k1_zfmisc_1(X2) != k1_zfmisc_1(X1) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_2112]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_4547,plain,
% 3.73/0.98      ( ~ m1_subset_1(k2_relset_1(sK5,sK6,sK7),k1_zfmisc_1(X0))
% 3.73/0.98      | m1_subset_1(k2_relset_1(sK5,sK6,sK7),k1_zfmisc_1(X1))
% 3.73/0.98      | k2_relset_1(sK5,sK6,sK7) != k2_relset_1(sK5,sK6,sK7)
% 3.73/0.98      | k1_zfmisc_1(X1) != k1_zfmisc_1(X0) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_3841]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_5409,plain,
% 3.73/0.98      ( m1_subset_1(k2_relset_1(sK5,sK6,sK7),k1_zfmisc_1(X0))
% 3.73/0.98      | ~ m1_subset_1(k2_relset_1(sK5,sK6,sK7),k1_zfmisc_1(sK6))
% 3.73/0.98      | k2_relset_1(sK5,sK6,sK7) != k2_relset_1(sK5,sK6,sK7)
% 3.73/0.98      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK6) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_4547]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_5411,plain,
% 3.73/0.98      ( ~ m1_subset_1(k2_relset_1(sK5,sK6,sK7),k1_zfmisc_1(sK6))
% 3.73/0.98      | m1_subset_1(k2_relset_1(sK5,sK6,sK7),k1_zfmisc_1(k1_xboole_0))
% 3.73/0.98      | k2_relset_1(sK5,sK6,sK7) != k2_relset_1(sK5,sK6,sK7)
% 3.73/0.98      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(sK6) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_5409]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_430,plain,
% 3.73/0.98      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 3.73/0.98      theory(equality) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_9407,plain,
% 3.73/0.98      ( X0 != sK6 | k1_zfmisc_1(X0) = k1_zfmisc_1(sK6) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_430]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_9408,plain,
% 3.73/0.98      ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(sK6)
% 3.73/0.98      | k1_xboole_0 != sK6 ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_9407]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_13324,plain,
% 3.73/0.98      ( m1_subset_1(sK3(sK7,X0,X1),X2) = iProver_top
% 3.73/0.98      | r1_tarski(sK5,X2) != iProver_top
% 3.73/0.98      | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top ),
% 3.73/0.98      inference(global_propositional_subsumption,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_12089,c_34,c_33,c_449,c_1552,c_1625,c_1767,c_2005,
% 3.73/0.98                 c_2018,c_3059,c_3258,c_5411,c_9408]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_25,plain,
% 3.73/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/0.98      | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
% 3.73/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1224,plain,
% 3.73/0.98      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
% 3.73/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_4456,plain,
% 3.73/0.98      ( k7_relset_1(sK5,sK6,sK7,sK5) = k2_relset_1(sK5,sK6,sK7) ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_1215,c_1224]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_23,plain,
% 3.73/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/0.98      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.73/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1226,plain,
% 3.73/0.98      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.73/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2762,plain,
% 3.73/0.98      ( k7_relset_1(sK5,sK6,sK7,X0) = k9_relat_1(sK7,X0) ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_1215,c_1226]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_4458,plain,
% 3.73/0.98      ( k2_relset_1(sK5,sK6,sK7) = k9_relat_1(sK7,sK5) ),
% 3.73/0.98      inference(demodulation,[status(thm)],[c_4456,c_2762]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1216,plain,
% 3.73/0.98      ( r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_4858,plain,
% 3.73/0.98      ( r2_hidden(sK4,k9_relat_1(sK7,sK5)) = iProver_top ),
% 3.73/0.98      inference(demodulation,[status(thm)],[c_4458,c_1216]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_15,plain,
% 3.73/0.98      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.73/0.98      | ~ v1_funct_1(X1)
% 3.73/0.98      | ~ v1_relat_1(X1)
% 3.73/0.98      | k1_funct_1(X1,sK3(X1,X2,X0)) = X0 ),
% 3.73/0.98      inference(cnf_transformation,[],[f93]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1234,plain,
% 3.73/0.98      ( k1_funct_1(X0,sK3(X0,X1,X2)) = X2
% 3.73/0.98      | r2_hidden(X2,k9_relat_1(X0,X1)) != iProver_top
% 3.73/0.98      | v1_funct_1(X0) != iProver_top
% 3.73/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_5528,plain,
% 3.73/0.98      ( k1_funct_1(sK7,sK3(sK7,sK5,sK4)) = sK4
% 3.73/0.98      | v1_funct_1(sK7) != iProver_top
% 3.73/0.98      | v1_relat_1(sK7) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_4858,c_1234]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_5922,plain,
% 3.73/0.98      ( k1_funct_1(sK7,sK3(sK7,sK5,sK4)) = sK4 ),
% 3.73/0.98      inference(global_propositional_subsumption,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_5528,c_37,c_39,c_1583]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_32,negated_conjecture,
% 3.73/0.98      ( ~ m1_subset_1(X0,sK5) | k1_funct_1(sK7,X0) != sK4 ),
% 3.73/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1217,plain,
% 3.73/0.98      ( k1_funct_1(sK7,X0) != sK4 | m1_subset_1(X0,sK5) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_5926,plain,
% 3.73/0.98      ( m1_subset_1(sK3(sK7,sK5,sK4),sK5) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_5922,c_1217]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_13346,plain,
% 3.73/0.98      ( r1_tarski(sK5,sK5) != iProver_top
% 3.73/0.98      | r2_hidden(sK4,k9_relat_1(sK7,sK5)) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_13324,c_5926]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_20,plain,
% 3.73/0.98      ( v4_relat_1(X0,X1)
% 3.73/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.73/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1229,plain,
% 3.73/0.98      ( v4_relat_1(X0,X1) = iProver_top
% 3.73/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2446,plain,
% 3.73/0.98      ( v4_relat_1(sK7,sK5) = iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_1215,c_1229]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_9,plain,
% 3.73/0.98      ( ~ v4_relat_1(X0,X1)
% 3.73/0.98      | r1_tarski(k1_relat_1(X0),X1)
% 3.73/0.98      | ~ v1_relat_1(X0) ),
% 3.73/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1240,plain,
% 3.73/0.98      ( v4_relat_1(X0,X1) != iProver_top
% 3.73/0.98      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.73/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3530,plain,
% 3.73/0.98      ( sK6 = k1_xboole_0
% 3.73/0.98      | v4_relat_1(sK7,X0) != iProver_top
% 3.73/0.98      | r1_tarski(sK5,X0) = iProver_top
% 3.73/0.98      | v1_relat_1(sK7) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_2878,c_1240]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3770,plain,
% 3.73/0.98      ( r1_tarski(sK5,X0) = iProver_top
% 3.73/0.98      | v4_relat_1(sK7,X0) != iProver_top
% 3.73/0.98      | sK6 = k1_xboole_0 ),
% 3.73/0.98      inference(global_propositional_subsumption,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_3530,c_39,c_1583]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3771,plain,
% 3.73/0.98      ( sK6 = k1_xboole_0
% 3.73/0.98      | v4_relat_1(sK7,X0) != iProver_top
% 3.73/0.98      | r1_tarski(sK5,X0) = iProver_top ),
% 3.73/0.98      inference(renaming,[status(thm)],[c_3770]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3779,plain,
% 3.73/0.98      ( sK6 = k1_xboole_0 | r1_tarski(sK5,sK5) = iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_2446,c_3771]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(contradiction,plain,
% 3.73/0.98      ( $false ),
% 3.73/0.98      inference(minisat,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_13346,c_9408,c_5411,c_4858,c_3779,c_3258,c_3059,
% 3.73/0.98                 c_2018,c_2005,c_1767,c_1625,c_1552,c_449,c_33,c_34]) ).
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.73/0.98  
% 3.73/0.98  ------                               Statistics
% 3.73/0.98  
% 3.73/0.98  ------ Selected
% 3.73/0.98  
% 3.73/0.98  total_time:                             0.441
% 3.73/0.98  
%------------------------------------------------------------------------------
