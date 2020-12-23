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
% DateTime   : Thu Dec  3 12:00:50 EST 2020

% Result     : Theorem 35.49s
% Output     : CNFRefutation 35.49s
% Verified   : 
% Statistics : Number of formulae       :  205 (13329 expanded)
%              Number of clauses        :  137 (4491 expanded)
%              Number of leaves         :   21 (3173 expanded)
%              Depth                    :   31
%              Number of atoms          :  646 (60163 expanded)
%              Number of equality atoms :  361 (21034 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f42,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) = X3
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK7(X3)) = X3
        & r2_hidden(sK7(X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
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
   => ( k2_relset_1(sK4,sK5,sK6) != sK5
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK6,X4) = X3
              & r2_hidden(X4,sK4) )
          | ~ r2_hidden(X3,sK5) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK6,sK4,sK5)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( k2_relset_1(sK4,sK5,sK6) != sK5
    & ! [X3] :
        ( ( k1_funct_1(sK6,sK7(X3)) = X3
          & r2_hidden(sK7(X3),sK4) )
        | ~ r2_hidden(X3,sK5) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK6,sK4,sK5)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f26,f42,f41])).

fof(f73,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
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

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f72,plain,(
    v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
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

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f38,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) = X2
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f35,f38,f37,f36])).

fof(f54,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f82,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f78,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f74,plain,(
    ! [X3] :
      ( r2_hidden(sK7(X3),sK4)
      | ~ r2_hidden(X3,sK5) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f75,plain,(
    ! [X3] :
      ( k1_funct_1(sK6,sK7(X3)) = X3
      | ~ r2_hidden(X3,sK5) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f76,plain,(
    k2_relset_1(sK4,sK5,sK6) != sK5 ),
    inference(cnf_transformation,[],[f43])).

fof(f56,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f79,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f80,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f79])).

fof(f71,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f85,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f68])).

fof(f4,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f87,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f65])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1207,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1211,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5014,plain,
    ( k1_relset_1(sK4,sK5,sK6) = sK4
    | sK5 = k1_xboole_0
    | v1_funct_2(sK6,sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1207,c_1211])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1218,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2480,plain,
    ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1207,c_1218])).

cnf(c_5018,plain,
    ( k1_relat_1(sK6) = sK4
    | sK5 = k1_xboole_0
    | v1_funct_2(sK6,sK4,sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5014,c_2480])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_34,plain,
    ( v1_funct_2(sK6,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_54458,plain,
    ( sK5 = k1_xboole_0
    | k1_relat_1(sK6) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5018,c_34])).

cnf(c_54459,plain,
    ( k1_relat_1(sK6) = sK4
    | sK5 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_54458])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1221,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_54470,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(sK3(sK6,X0),sK4) = iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_54459,c_1221])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_8781,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_8784,plain,
    ( r1_tarski(sK4,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8781])).

cnf(c_29,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(sK7(X0),sK4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1208,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK7(X0),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1231,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3484,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK7(X0),X1) = iProver_top
    | r1_tarski(sK4,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1208,c_1231])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1232,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_28,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | k1_funct_1(sK6,sK7(X0)) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1209,plain,
    ( k1_funct_1(sK6,sK7(X0)) = X0
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1932,plain,
    ( k1_funct_1(sK6,sK7(sK0(sK5,X0))) = sK0(sK5,X0)
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1232,c_1209])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1217,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2466,plain,
    ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1207,c_1217])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1219,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3283,plain,
    ( m1_subset_1(k2_relat_1(sK6),k1_zfmisc_1(sK5)) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2466,c_1219])).

cnf(c_35,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3901,plain,
    ( m1_subset_1(k2_relat_1(sK6),k1_zfmisc_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3283,c_35])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1227,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3906,plain,
    ( r1_tarski(k2_relat_1(sK6),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3901,c_1227])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1230,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_9477,plain,
    ( k2_relat_1(sK6) = sK5
    | r1_tarski(sK5,k2_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3906,c_1230])).

cnf(c_27,negated_conjecture,
    ( k2_relset_1(sK4,sK5,sK6) != sK5 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1561,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_554,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1531,plain,
    ( k2_relset_1(sK4,sK5,sK6) != X0
    | k2_relset_1(sK4,sK5,sK6) = sK5
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_554])).

cnf(c_2427,plain,
    ( k2_relset_1(sK4,sK5,sK6) != k2_relat_1(sK6)
    | k2_relset_1(sK4,sK5,sK6) = sK5
    | sK5 != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1531])).

cnf(c_4636,plain,
    ( ~ r1_tarski(X0,k2_relat_1(sK6))
    | ~ r1_tarski(k2_relat_1(sK6),X0)
    | X0 = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_7223,plain,
    ( ~ r1_tarski(k2_relat_1(sK6),sK5)
    | ~ r1_tarski(sK5,k2_relat_1(sK6))
    | sK5 = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_4636])).

cnf(c_7225,plain,
    ( sK5 = k2_relat_1(sK6)
    | r1_tarski(k2_relat_1(sK6),sK5) != iProver_top
    | r1_tarski(sK5,k2_relat_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7223])).

cnf(c_9641,plain,
    ( r1_tarski(sK5,k2_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9477,c_30,c_27,c_1561,c_2427,c_3906,c_7225])).

cnf(c_9646,plain,
    ( k1_funct_1(sK6,sK7(sK0(sK5,k2_relat_1(sK6)))) = sK0(sK5,k2_relat_1(sK6)) ),
    inference(superposition,[status(thm)],[c_1932,c_9641])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1223,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_10078,plain,
    ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top
    | r2_hidden(sK7(sK0(sK5,k2_relat_1(sK6))),k1_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_9646,c_1223])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_33,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1509,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1510,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1509])).

cnf(c_52567,plain,
    ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top
    | r2_hidden(sK7(sK0(sK5,k2_relat_1(sK6))),k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10078,c_33,c_35,c_1510])).

cnf(c_52573,plain,
    ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top
    | r2_hidden(sK0(sK5,k2_relat_1(sK6)),sK5) != iProver_top
    | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3484,c_52567])).

cnf(c_2700,plain,
    ( r2_hidden(sK0(sK5,X0),sK5)
    | r1_tarski(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_7224,plain,
    ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),sK5)
    | r1_tarski(sK5,k2_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_2700])).

cnf(c_7227,plain,
    ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),sK5) = iProver_top
    | r1_tarski(sK5,k2_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7224])).

cnf(c_52922,plain,
    ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top
    | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_52573,c_30,c_27,c_1561,c_2427,c_3906,c_7225,c_7227])).

cnf(c_4511,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK3(X1,X0),X2) = iProver_top
    | r1_tarski(k1_relat_1(X1),X2) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1221,c_1231])).

cnf(c_39505,plain,
    ( k1_funct_1(sK6,sK7(sK3(X0,X1))) = sK3(X0,X1)
    | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
    | r1_tarski(k1_relat_1(X0),sK5) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4511,c_1209])).

cnf(c_52931,plain,
    ( k1_funct_1(sK6,sK7(sK3(sK6,sK0(sK5,k2_relat_1(sK6))))) = sK3(sK6,sK0(sK5,k2_relat_1(sK6)))
    | r1_tarski(k1_relat_1(sK6),sK5) != iProver_top
    | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_52922,c_39505])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1233,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_52928,plain,
    ( r1_tarski(sK5,k2_relat_1(sK6)) = iProver_top
    | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_52922,c_1233])).

cnf(c_53680,plain,
    ( r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_52931,c_30,c_27,c_1561,c_2427,c_3906,c_7225,c_52928])).

cnf(c_54471,plain,
    ( sK5 = k1_xboole_0
    | r1_tarski(sK4,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_54459,c_53680])).

cnf(c_54749,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_54470,c_8784,c_54471])).

cnf(c_54918,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_54749,c_1207])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1215,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_57301,plain,
    ( sK6 = k1_xboole_0
    | sK4 = k1_xboole_0
    | v1_funct_2(sK6,sK4,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_54918,c_1215])).

cnf(c_100,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_104,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_553,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1722,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_553])).

cnf(c_1629,plain,
    ( ~ r1_tarski(X0,sK6)
    | ~ r1_tarski(sK6,X0)
    | X0 = sK6 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1884,plain,
    ( ~ r1_tarski(sK6,sK6)
    | sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_1629])).

cnf(c_1885,plain,
    ( r1_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2004,plain,
    ( X0 != X1
    | X0 = sK5
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_554])).

cnf(c_2005,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2004])).

cnf(c_2420,plain,
    ( k2_relset_1(sK4,sK5,sK6) != k2_relset_1(sK4,sK5,sK6)
    | k2_relset_1(sK4,sK5,sK6) = sK5
    | sK5 != k2_relset_1(sK4,sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_1531])).

cnf(c_2421,plain,
    ( k2_relset_1(sK4,sK5,sK6) = k2_relset_1(sK4,sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_553])).

cnf(c_565,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_1591,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK6,sK4,sK5)
    | X0 != sK6
    | X2 != sK5
    | X1 != sK4 ),
    inference(instantiation,[status(thm)],[c_565])).

cnf(c_1721,plain,
    ( v1_funct_2(X0,sK4,X1)
    | ~ v1_funct_2(sK6,sK4,sK5)
    | X0 != sK6
    | X1 != sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1591])).

cnf(c_2447,plain,
    ( v1_funct_2(sK6,sK4,X0)
    | ~ v1_funct_2(sK6,sK4,sK5)
    | X0 != sK5
    | sK6 != sK6
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1721])).

cnf(c_2449,plain,
    ( X0 != sK5
    | sK6 != sK6
    | sK4 != sK4
    | v1_funct_2(sK6,sK4,X0) = iProver_top
    | v1_funct_2(sK6,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2447])).

cnf(c_2451,plain,
    ( sK6 != sK6
    | sK4 != sK4
    | k1_xboole_0 != sK5
    | v1_funct_2(sK6,sK4,sK5) != iProver_top
    | v1_funct_2(sK6,sK4,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2449])).

cnf(c_2422,plain,
    ( X0 != X1
    | k2_relset_1(sK4,sK5,sK6) != X1
    | k2_relset_1(sK4,sK5,sK6) = X0 ),
    inference(instantiation,[status(thm)],[c_554])).

cnf(c_2785,plain,
    ( X0 != k2_relat_1(sK6)
    | k2_relset_1(sK4,sK5,sK6) = X0
    | k2_relset_1(sK4,sK5,sK6) != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_2422])).

cnf(c_2786,plain,
    ( k2_relset_1(sK4,sK5,sK6) != k2_relat_1(sK6)
    | k2_relset_1(sK4,sK5,sK6) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_2785])).

cnf(c_1923,plain,
    ( X0 != X1
    | sK6 != X1
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_554])).

cnf(c_3468,plain,
    ( X0 != sK6
    | sK6 = X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1923])).

cnf(c_3469,plain,
    ( sK6 != sK6
    | sK6 = k1_xboole_0
    | k1_xboole_0 != sK6 ),
    inference(instantiation,[status(thm)],[c_3468])).

cnf(c_2012,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_554])).

cnf(c_3596,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2012])).

cnf(c_3597,plain,
    ( sK4 != sK4
    | sK4 = k1_xboole_0
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_3596])).

cnf(c_1666,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_554])).

cnf(c_6669,plain,
    ( k2_relset_1(sK4,sK5,sK6) != X0
    | sK5 != X0
    | sK5 = k2_relset_1(sK4,sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_1666])).

cnf(c_6670,plain,
    ( k2_relset_1(sK4,sK5,sK6) != k1_xboole_0
    | sK5 = k2_relset_1(sK4,sK5,sK6)
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6669])).

cnf(c_1651,plain,
    ( ~ v1_funct_2(sK6,X0,k1_xboole_0)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_6694,plain,
    ( ~ v1_funct_2(sK6,sK4,k1_xboole_0)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0)))
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1651])).

cnf(c_6697,plain,
    ( k1_xboole_0 = sK6
    | k1_xboole_0 = sK4
    | v1_funct_2(sK6,sK4,k1_xboole_0) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6694])).

cnf(c_4670,plain,
    ( X0 != X1
    | X0 = k2_relat_1(sK6)
    | k2_relat_1(sK6) != X1 ),
    inference(instantiation,[status(thm)],[c_554])).

cnf(c_8041,plain,
    ( X0 != k2_relat_1(X1)
    | X0 = k2_relat_1(sK6)
    | k2_relat_1(sK6) != k2_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_4670])).

cnf(c_8043,plain,
    ( k2_relat_1(sK6) != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(sK6)
    | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8041])).

cnf(c_558,plain,
    ( X0 != X1
    | k2_relat_1(X0) = k2_relat_1(X1) ),
    theory(equality)).

cnf(c_8042,plain,
    ( k2_relat_1(sK6) = k2_relat_1(X0)
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_558])).

cnf(c_8044,plain,
    ( k2_relat_1(sK6) = k2_relat_1(k1_xboole_0)
    | sK6 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8042])).

cnf(c_2502,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_554,c_553])).

cnf(c_8,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_12302,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2502,c_8])).

cnf(c_58412,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_57301,c_34,c_30,c_27,c_100,c_104,c_1561,c_1722,c_1884,c_1885,c_2005,c_2420,c_2421,c_2451,c_2786,c_3469,c_3597,c_6670,c_6697,c_8043,c_8044,c_8784,c_12302,c_54471,c_54918])).

cnf(c_58422,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(sK6)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_58412,c_53680])).

cnf(c_54910,plain,
    ( k1_relset_1(sK4,k1_xboole_0,sK6) = k1_relat_1(sK6) ),
    inference(demodulation,[status(thm)],[c_54749,c_2480])).

cnf(c_58417,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_relat_1(sK6) ),
    inference(demodulation,[status(thm)],[c_58412,c_54910])).

cnf(c_58419,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_58412,c_54918])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1212,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_59495,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0
    | v1_funct_2(sK6,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_58419,c_1212])).

cnf(c_1206,plain,
    ( v1_funct_2(sK6,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_54919,plain,
    ( v1_funct_2(sK6,sK4,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_54749,c_1206])).

cnf(c_58420,plain,
    ( v1_funct_2(sK6,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_58412,c_54919])).

cnf(c_60547,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_59495,c_58420])).

cnf(c_87098,plain,
    ( k1_relat_1(sK6) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_58417,c_60547])).

cnf(c_87348,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_58422,c_87098])).

cnf(c_1229,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_87350,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_87348,c_1229])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:30:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 35.49/4.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.49/4.99  
% 35.49/4.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.49/4.99  
% 35.49/4.99  ------  iProver source info
% 35.49/4.99  
% 35.49/4.99  git: date: 2020-06-30 10:37:57 +0100
% 35.49/4.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.49/4.99  git: non_committed_changes: false
% 35.49/4.99  git: last_make_outside_of_git: false
% 35.49/4.99  
% 35.49/4.99  ------ 
% 35.49/4.99  ------ Parsing...
% 35.49/4.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.49/4.99  
% 35.49/4.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 35.49/4.99  
% 35.49/4.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.49/4.99  
% 35.49/4.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.49/4.99  ------ Proving...
% 35.49/4.99  ------ Problem Properties 
% 35.49/4.99  
% 35.49/4.99  
% 35.49/4.99  clauses                                 32
% 35.49/4.99  conjectures                             6
% 35.49/4.99  EPR                                     5
% 35.49/4.99  Horn                                    24
% 35.49/4.99  unary                                   7
% 35.49/4.99  binary                                  10
% 35.49/4.99  lits                                    88
% 35.49/4.99  lits eq                                 23
% 35.49/4.99  fd_pure                                 0
% 35.49/5.00  fd_pseudo                               0
% 35.49/5.00  fd_cond                                 4
% 35.49/5.00  fd_pseudo_cond                          4
% 35.49/5.00  AC symbols                              0
% 35.49/5.00  
% 35.49/5.00  ------ Input Options Time Limit: Unbounded
% 35.49/5.00  
% 35.49/5.00  
% 35.49/5.00  ------ 
% 35.49/5.00  Current options:
% 35.49/5.00  ------ 
% 35.49/5.00  
% 35.49/5.00  
% 35.49/5.00  
% 35.49/5.00  
% 35.49/5.00  ------ Proving...
% 35.49/5.00  
% 35.49/5.00  
% 35.49/5.00  % SZS status Theorem for theBenchmark.p
% 35.49/5.00  
% 35.49/5.00   Resolution empty clause
% 35.49/5.00  
% 35.49/5.00  % SZS output start CNFRefutation for theBenchmark.p
% 35.49/5.00  
% 35.49/5.00  fof(f12,conjecture,(
% 35.49/5.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 35.49/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.49/5.00  
% 35.49/5.00  fof(f13,negated_conjecture,(
% 35.49/5.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 35.49/5.00    inference(negated_conjecture,[],[f12])).
% 35.49/5.00  
% 35.49/5.00  fof(f25,plain,(
% 35.49/5.00    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 35.49/5.00    inference(ennf_transformation,[],[f13])).
% 35.49/5.00  
% 35.49/5.00  fof(f26,plain,(
% 35.49/5.00    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 35.49/5.00    inference(flattening,[],[f25])).
% 35.49/5.00  
% 35.49/5.00  fof(f42,plain,(
% 35.49/5.00    ( ! [X2,X0] : (! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) => (k1_funct_1(X2,sK7(X3)) = X3 & r2_hidden(sK7(X3),X0)))) )),
% 35.49/5.00    introduced(choice_axiom,[])).
% 35.49/5.00  
% 35.49/5.00  fof(f41,plain,(
% 35.49/5.00    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k2_relset_1(sK4,sK5,sK6) != sK5 & ! [X3] : (? [X4] : (k1_funct_1(sK6,X4) = X3 & r2_hidden(X4,sK4)) | ~r2_hidden(X3,sK5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6))),
% 35.49/5.00    introduced(choice_axiom,[])).
% 35.49/5.00  
% 35.49/5.00  fof(f43,plain,(
% 35.49/5.00    k2_relset_1(sK4,sK5,sK6) != sK5 & ! [X3] : ((k1_funct_1(sK6,sK7(X3)) = X3 & r2_hidden(sK7(X3),sK4)) | ~r2_hidden(X3,sK5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6)),
% 35.49/5.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f26,f42,f41])).
% 35.49/5.00  
% 35.49/5.00  fof(f73,plain,(
% 35.49/5.00    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 35.49/5.00    inference(cnf_transformation,[],[f43])).
% 35.49/5.00  
% 35.49/5.00  fof(f10,axiom,(
% 35.49/5.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 35.49/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.49/5.00  
% 35.49/5.00  fof(f21,plain,(
% 35.49/5.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.49/5.00    inference(ennf_transformation,[],[f10])).
% 35.49/5.00  
% 35.49/5.00  fof(f22,plain,(
% 35.49/5.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.49/5.00    inference(flattening,[],[f21])).
% 35.49/5.00  
% 35.49/5.00  fof(f40,plain,(
% 35.49/5.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.49/5.00    inference(nnf_transformation,[],[f22])).
% 35.49/5.00  
% 35.49/5.00  fof(f64,plain,(
% 35.49/5.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.49/5.00    inference(cnf_transformation,[],[f40])).
% 35.49/5.00  
% 35.49/5.00  fof(f8,axiom,(
% 35.49/5.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 35.49/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.49/5.00  
% 35.49/5.00  fof(f19,plain,(
% 35.49/5.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.49/5.00    inference(ennf_transformation,[],[f8])).
% 35.49/5.00  
% 35.49/5.00  fof(f62,plain,(
% 35.49/5.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.49/5.00    inference(cnf_transformation,[],[f19])).
% 35.49/5.00  
% 35.49/5.00  fof(f72,plain,(
% 35.49/5.00    v1_funct_2(sK6,sK4,sK5)),
% 35.49/5.00    inference(cnf_transformation,[],[f43])).
% 35.49/5.00  
% 35.49/5.00  fof(f5,axiom,(
% 35.49/5.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 35.49/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.49/5.00  
% 35.49/5.00  fof(f15,plain,(
% 35.49/5.00    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 35.49/5.00    inference(ennf_transformation,[],[f5])).
% 35.49/5.00  
% 35.49/5.00  fof(f16,plain,(
% 35.49/5.00    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 35.49/5.00    inference(flattening,[],[f15])).
% 35.49/5.00  
% 35.49/5.00  fof(f34,plain,(
% 35.49/5.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 35.49/5.00    inference(nnf_transformation,[],[f16])).
% 35.49/5.00  
% 35.49/5.00  fof(f35,plain,(
% 35.49/5.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 35.49/5.00    inference(rectify,[],[f34])).
% 35.49/5.00  
% 35.49/5.00  fof(f38,plain,(
% 35.49/5.00    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))))),
% 35.49/5.00    introduced(choice_axiom,[])).
% 35.49/5.00  
% 35.49/5.00  fof(f37,plain,(
% 35.49/5.00    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) = X2 & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))) )),
% 35.49/5.00    introduced(choice_axiom,[])).
% 35.49/5.00  
% 35.49/5.00  fof(f36,plain,(
% 35.49/5.00    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1))))),
% 35.49/5.00    introduced(choice_axiom,[])).
% 35.49/5.00  
% 35.49/5.00  fof(f39,plain,(
% 35.49/5.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & ((k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 35.49/5.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f35,f38,f37,f36])).
% 35.49/5.00  
% 35.49/5.00  fof(f54,plain,(
% 35.49/5.00    ( ! [X0,X5,X1] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 35.49/5.00    inference(cnf_transformation,[],[f39])).
% 35.49/5.00  
% 35.49/5.00  fof(f82,plain,(
% 35.49/5.00    ( ! [X0,X5] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 35.49/5.00    inference(equality_resolution,[],[f54])).
% 35.49/5.00  
% 35.49/5.00  fof(f2,axiom,(
% 35.49/5.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 35.49/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.49/5.00  
% 35.49/5.00  fof(f31,plain,(
% 35.49/5.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 35.49/5.00    inference(nnf_transformation,[],[f2])).
% 35.49/5.00  
% 35.49/5.00  fof(f32,plain,(
% 35.49/5.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 35.49/5.00    inference(flattening,[],[f31])).
% 35.49/5.00  
% 35.49/5.00  fof(f47,plain,(
% 35.49/5.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 35.49/5.00    inference(cnf_transformation,[],[f32])).
% 35.49/5.00  
% 35.49/5.00  fof(f78,plain,(
% 35.49/5.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 35.49/5.00    inference(equality_resolution,[],[f47])).
% 35.49/5.00  
% 35.49/5.00  fof(f74,plain,(
% 35.49/5.00    ( ! [X3] : (r2_hidden(sK7(X3),sK4) | ~r2_hidden(X3,sK5)) )),
% 35.49/5.00    inference(cnf_transformation,[],[f43])).
% 35.49/5.00  
% 35.49/5.00  fof(f1,axiom,(
% 35.49/5.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 35.49/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.49/5.00  
% 35.49/5.00  fof(f14,plain,(
% 35.49/5.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 35.49/5.00    inference(ennf_transformation,[],[f1])).
% 35.49/5.00  
% 35.49/5.00  fof(f27,plain,(
% 35.49/5.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 35.49/5.00    inference(nnf_transformation,[],[f14])).
% 35.49/5.00  
% 35.49/5.00  fof(f28,plain,(
% 35.49/5.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 35.49/5.00    inference(rectify,[],[f27])).
% 35.49/5.00  
% 35.49/5.00  fof(f29,plain,(
% 35.49/5.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 35.49/5.00    introduced(choice_axiom,[])).
% 35.49/5.00  
% 35.49/5.00  fof(f30,plain,(
% 35.49/5.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 35.49/5.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 35.49/5.00  
% 35.49/5.00  fof(f44,plain,(
% 35.49/5.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 35.49/5.00    inference(cnf_transformation,[],[f30])).
% 35.49/5.00  
% 35.49/5.00  fof(f45,plain,(
% 35.49/5.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 35.49/5.00    inference(cnf_transformation,[],[f30])).
% 35.49/5.00  
% 35.49/5.00  fof(f75,plain,(
% 35.49/5.00    ( ! [X3] : (k1_funct_1(sK6,sK7(X3)) = X3 | ~r2_hidden(X3,sK5)) )),
% 35.49/5.00    inference(cnf_transformation,[],[f43])).
% 35.49/5.00  
% 35.49/5.00  fof(f9,axiom,(
% 35.49/5.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 35.49/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.49/5.00  
% 35.49/5.00  fof(f20,plain,(
% 35.49/5.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.49/5.00    inference(ennf_transformation,[],[f9])).
% 35.49/5.00  
% 35.49/5.00  fof(f63,plain,(
% 35.49/5.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.49/5.00    inference(cnf_transformation,[],[f20])).
% 35.49/5.00  
% 35.49/5.00  fof(f7,axiom,(
% 35.49/5.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 35.49/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.49/5.00  
% 35.49/5.00  fof(f18,plain,(
% 35.49/5.00    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.49/5.00    inference(ennf_transformation,[],[f7])).
% 35.49/5.00  
% 35.49/5.00  fof(f61,plain,(
% 35.49/5.00    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.49/5.00    inference(cnf_transformation,[],[f18])).
% 35.49/5.00  
% 35.49/5.00  fof(f3,axiom,(
% 35.49/5.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 35.49/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.49/5.00  
% 35.49/5.00  fof(f33,plain,(
% 35.49/5.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 35.49/5.00    inference(nnf_transformation,[],[f3])).
% 35.49/5.00  
% 35.49/5.00  fof(f50,plain,(
% 35.49/5.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 35.49/5.00    inference(cnf_transformation,[],[f33])).
% 35.49/5.00  
% 35.49/5.00  fof(f49,plain,(
% 35.49/5.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 35.49/5.00    inference(cnf_transformation,[],[f32])).
% 35.49/5.00  
% 35.49/5.00  fof(f76,plain,(
% 35.49/5.00    k2_relset_1(sK4,sK5,sK6) != sK5),
% 35.49/5.00    inference(cnf_transformation,[],[f43])).
% 35.49/5.00  
% 35.49/5.00  fof(f56,plain,(
% 35.49/5.00    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 35.49/5.00    inference(cnf_transformation,[],[f39])).
% 35.49/5.00  
% 35.49/5.00  fof(f79,plain,(
% 35.49/5.00    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 35.49/5.00    inference(equality_resolution,[],[f56])).
% 35.49/5.00  
% 35.49/5.00  fof(f80,plain,(
% 35.49/5.00    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 35.49/5.00    inference(equality_resolution,[],[f79])).
% 35.49/5.00  
% 35.49/5.00  fof(f71,plain,(
% 35.49/5.00    v1_funct_1(sK6)),
% 35.49/5.00    inference(cnf_transformation,[],[f43])).
% 35.49/5.00  
% 35.49/5.00  fof(f6,axiom,(
% 35.49/5.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 35.49/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.49/5.00  
% 35.49/5.00  fof(f17,plain,(
% 35.49/5.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.49/5.00    inference(ennf_transformation,[],[f6])).
% 35.49/5.00  
% 35.49/5.00  fof(f60,plain,(
% 35.49/5.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.49/5.00    inference(cnf_transformation,[],[f17])).
% 35.49/5.00  
% 35.49/5.00  fof(f46,plain,(
% 35.49/5.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 35.49/5.00    inference(cnf_transformation,[],[f30])).
% 35.49/5.00  
% 35.49/5.00  fof(f68,plain,(
% 35.49/5.00    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.49/5.00    inference(cnf_transformation,[],[f40])).
% 35.49/5.00  
% 35.49/5.00  fof(f85,plain,(
% 35.49/5.00    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 35.49/5.00    inference(equality_resolution,[],[f68])).
% 35.49/5.00  
% 35.49/5.00  fof(f4,axiom,(
% 35.49/5.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 35.49/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.49/5.00  
% 35.49/5.00  fof(f53,plain,(
% 35.49/5.00    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 35.49/5.00    inference(cnf_transformation,[],[f4])).
% 35.49/5.00  
% 35.49/5.00  fof(f65,plain,(
% 35.49/5.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.49/5.00    inference(cnf_transformation,[],[f40])).
% 35.49/5.00  
% 35.49/5.00  fof(f87,plain,(
% 35.49/5.00    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 35.49/5.00    inference(equality_resolution,[],[f65])).
% 35.49/5.00  
% 35.49/5.00  cnf(c_30,negated_conjecture,
% 35.49/5.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 35.49/5.00      inference(cnf_transformation,[],[f73]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_1207,plain,
% 35.49/5.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 35.49/5.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_25,plain,
% 35.49/5.00      ( ~ v1_funct_2(X0,X1,X2)
% 35.49/5.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.49/5.00      | k1_relset_1(X1,X2,X0) = X1
% 35.49/5.00      | k1_xboole_0 = X2 ),
% 35.49/5.00      inference(cnf_transformation,[],[f64]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_1211,plain,
% 35.49/5.00      ( k1_relset_1(X0,X1,X2) = X0
% 35.49/5.00      | k1_xboole_0 = X1
% 35.49/5.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 35.49/5.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 35.49/5.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_5014,plain,
% 35.49/5.00      ( k1_relset_1(sK4,sK5,sK6) = sK4
% 35.49/5.00      | sK5 = k1_xboole_0
% 35.49/5.00      | v1_funct_2(sK6,sK4,sK5) != iProver_top ),
% 35.49/5.00      inference(superposition,[status(thm)],[c_1207,c_1211]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_18,plain,
% 35.49/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.49/5.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 35.49/5.00      inference(cnf_transformation,[],[f62]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_1218,plain,
% 35.49/5.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 35.49/5.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 35.49/5.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_2480,plain,
% 35.49/5.00      ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
% 35.49/5.00      inference(superposition,[status(thm)],[c_1207,c_1218]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_5018,plain,
% 35.49/5.00      ( k1_relat_1(sK6) = sK4
% 35.49/5.00      | sK5 = k1_xboole_0
% 35.49/5.00      | v1_funct_2(sK6,sK4,sK5) != iProver_top ),
% 35.49/5.00      inference(demodulation,[status(thm)],[c_5014,c_2480]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_31,negated_conjecture,
% 35.49/5.00      ( v1_funct_2(sK6,sK4,sK5) ),
% 35.49/5.00      inference(cnf_transformation,[],[f72]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_34,plain,
% 35.49/5.00      ( v1_funct_2(sK6,sK4,sK5) = iProver_top ),
% 35.49/5.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_54458,plain,
% 35.49/5.00      ( sK5 = k1_xboole_0 | k1_relat_1(sK6) = sK4 ),
% 35.49/5.00      inference(global_propositional_subsumption,[status(thm)],[c_5018,c_34]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_54459,plain,
% 35.49/5.00      ( k1_relat_1(sK6) = sK4 | sK5 = k1_xboole_0 ),
% 35.49/5.00      inference(renaming,[status(thm)],[c_54458]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_15,plain,
% 35.49/5.00      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 35.49/5.00      | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
% 35.49/5.00      | ~ v1_relat_1(X1)
% 35.49/5.00      | ~ v1_funct_1(X1) ),
% 35.49/5.00      inference(cnf_transformation,[],[f82]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_1221,plain,
% 35.49/5.00      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 35.49/5.00      | r2_hidden(sK3(X1,X0),k1_relat_1(X1)) = iProver_top
% 35.49/5.00      | v1_relat_1(X1) != iProver_top
% 35.49/5.00      | v1_funct_1(X1) != iProver_top ),
% 35.49/5.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_54470,plain,
% 35.49/5.00      ( sK5 = k1_xboole_0
% 35.49/5.00      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 35.49/5.00      | r2_hidden(sK3(sK6,X0),sK4) = iProver_top
% 35.49/5.00      | v1_relat_1(sK6) != iProver_top
% 35.49/5.00      | v1_funct_1(sK6) != iProver_top ),
% 35.49/5.00      inference(superposition,[status(thm)],[c_54459,c_1221]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_5,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f78]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_8781,plain,
% 35.49/5.00      ( r1_tarski(sK4,sK4) ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_5]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_8784,plain,
% 35.49/5.00      ( r1_tarski(sK4,sK4) = iProver_top ),
% 35.49/5.00      inference(predicate_to_equality,[status(thm)],[c_8781]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_29,negated_conjecture,
% 35.49/5.00      ( ~ r2_hidden(X0,sK5) | r2_hidden(sK7(X0),sK4) ),
% 35.49/5.00      inference(cnf_transformation,[],[f74]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_1208,plain,
% 35.49/5.00      ( r2_hidden(X0,sK5) != iProver_top
% 35.49/5.00      | r2_hidden(sK7(X0),sK4) = iProver_top ),
% 35.49/5.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_2,plain,
% 35.49/5.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 35.49/5.00      inference(cnf_transformation,[],[f44]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_1231,plain,
% 35.49/5.00      ( r2_hidden(X0,X1) != iProver_top
% 35.49/5.00      | r2_hidden(X0,X2) = iProver_top
% 35.49/5.00      | r1_tarski(X1,X2) != iProver_top ),
% 35.49/5.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_3484,plain,
% 35.49/5.00      ( r2_hidden(X0,sK5) != iProver_top
% 35.49/5.00      | r2_hidden(sK7(X0),X1) = iProver_top
% 35.49/5.00      | r1_tarski(sK4,X1) != iProver_top ),
% 35.49/5.00      inference(superposition,[status(thm)],[c_1208,c_1231]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_1,plain,
% 35.49/5.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 35.49/5.00      inference(cnf_transformation,[],[f45]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_1232,plain,
% 35.49/5.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 35.49/5.00      | r1_tarski(X0,X1) = iProver_top ),
% 35.49/5.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_28,negated_conjecture,
% 35.49/5.00      ( ~ r2_hidden(X0,sK5) | k1_funct_1(sK6,sK7(X0)) = X0 ),
% 35.49/5.00      inference(cnf_transformation,[],[f75]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_1209,plain,
% 35.49/5.00      ( k1_funct_1(sK6,sK7(X0)) = X0 | r2_hidden(X0,sK5) != iProver_top ),
% 35.49/5.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_1932,plain,
% 35.49/5.00      ( k1_funct_1(sK6,sK7(sK0(sK5,X0))) = sK0(sK5,X0)
% 35.49/5.00      | r1_tarski(sK5,X0) = iProver_top ),
% 35.49/5.00      inference(superposition,[status(thm)],[c_1232,c_1209]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_19,plain,
% 35.49/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.49/5.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 35.49/5.00      inference(cnf_transformation,[],[f63]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_1217,plain,
% 35.49/5.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 35.49/5.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 35.49/5.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_2466,plain,
% 35.49/5.00      ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
% 35.49/5.00      inference(superposition,[status(thm)],[c_1207,c_1217]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_17,plain,
% 35.49/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.49/5.00      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 35.49/5.00      inference(cnf_transformation,[],[f61]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_1219,plain,
% 35.49/5.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 35.49/5.00      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 35.49/5.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_3283,plain,
% 35.49/5.00      ( m1_subset_1(k2_relat_1(sK6),k1_zfmisc_1(sK5)) = iProver_top
% 35.49/5.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
% 35.49/5.00      inference(superposition,[status(thm)],[c_2466,c_1219]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_35,plain,
% 35.49/5.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 35.49/5.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_3901,plain,
% 35.49/5.00      ( m1_subset_1(k2_relat_1(sK6),k1_zfmisc_1(sK5)) = iProver_top ),
% 35.49/5.00      inference(global_propositional_subsumption,[status(thm)],[c_3283,c_35]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_7,plain,
% 35.49/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 35.49/5.00      inference(cnf_transformation,[],[f50]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_1227,plain,
% 35.49/5.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 35.49/5.00      | r1_tarski(X0,X1) = iProver_top ),
% 35.49/5.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_3906,plain,
% 35.49/5.00      ( r1_tarski(k2_relat_1(sK6),sK5) = iProver_top ),
% 35.49/5.00      inference(superposition,[status(thm)],[c_3901,c_1227]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_3,plain,
% 35.49/5.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 35.49/5.00      inference(cnf_transformation,[],[f49]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_1230,plain,
% 35.49/5.00      ( X0 = X1
% 35.49/5.00      | r1_tarski(X1,X0) != iProver_top
% 35.49/5.00      | r1_tarski(X0,X1) != iProver_top ),
% 35.49/5.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_9477,plain,
% 35.49/5.00      ( k2_relat_1(sK6) = sK5 | r1_tarski(sK5,k2_relat_1(sK6)) != iProver_top ),
% 35.49/5.00      inference(superposition,[status(thm)],[c_3906,c_1230]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_27,negated_conjecture,
% 35.49/5.00      ( k2_relset_1(sK4,sK5,sK6) != sK5 ),
% 35.49/5.00      inference(cnf_transformation,[],[f76]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_1561,plain,
% 35.49/5.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 35.49/5.00      | k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_19]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_554,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_1531,plain,
% 35.49/5.00      ( k2_relset_1(sK4,sK5,sK6) != X0
% 35.49/5.00      | k2_relset_1(sK4,sK5,sK6) = sK5
% 35.49/5.00      | sK5 != X0 ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_554]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_2427,plain,
% 35.49/5.00      ( k2_relset_1(sK4,sK5,sK6) != k2_relat_1(sK6)
% 35.49/5.00      | k2_relset_1(sK4,sK5,sK6) = sK5
% 35.49/5.00      | sK5 != k2_relat_1(sK6) ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_1531]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_4636,plain,
% 35.49/5.00      ( ~ r1_tarski(X0,k2_relat_1(sK6))
% 35.49/5.00      | ~ r1_tarski(k2_relat_1(sK6),X0)
% 35.49/5.00      | X0 = k2_relat_1(sK6) ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_3]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_7223,plain,
% 35.49/5.00      ( ~ r1_tarski(k2_relat_1(sK6),sK5)
% 35.49/5.00      | ~ r1_tarski(sK5,k2_relat_1(sK6))
% 35.49/5.00      | sK5 = k2_relat_1(sK6) ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_4636]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_7225,plain,
% 35.49/5.00      ( sK5 = k2_relat_1(sK6)
% 35.49/5.00      | r1_tarski(k2_relat_1(sK6),sK5) != iProver_top
% 35.49/5.00      | r1_tarski(sK5,k2_relat_1(sK6)) != iProver_top ),
% 35.49/5.00      inference(predicate_to_equality,[status(thm)],[c_7223]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_9641,plain,
% 35.49/5.00      ( r1_tarski(sK5,k2_relat_1(sK6)) != iProver_top ),
% 35.49/5.00      inference(global_propositional_subsumption,
% 35.49/5.00                [status(thm)],
% 35.49/5.00                [c_9477,c_30,c_27,c_1561,c_2427,c_3906,c_7225]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_9646,plain,
% 35.49/5.00      ( k1_funct_1(sK6,sK7(sK0(sK5,k2_relat_1(sK6)))) = sK0(sK5,k2_relat_1(sK6)) ),
% 35.49/5.00      inference(superposition,[status(thm)],[c_1932,c_9641]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_13,plain,
% 35.49/5.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 35.49/5.00      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 35.49/5.00      | ~ v1_relat_1(X1)
% 35.49/5.00      | ~ v1_funct_1(X1) ),
% 35.49/5.00      inference(cnf_transformation,[],[f80]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_1223,plain,
% 35.49/5.00      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 35.49/5.00      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 35.49/5.00      | v1_relat_1(X1) != iProver_top
% 35.49/5.00      | v1_funct_1(X1) != iProver_top ),
% 35.49/5.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_10078,plain,
% 35.49/5.00      ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top
% 35.49/5.00      | r2_hidden(sK7(sK0(sK5,k2_relat_1(sK6))),k1_relat_1(sK6)) != iProver_top
% 35.49/5.00      | v1_relat_1(sK6) != iProver_top
% 35.49/5.00      | v1_funct_1(sK6) != iProver_top ),
% 35.49/5.00      inference(superposition,[status(thm)],[c_9646,c_1223]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_32,negated_conjecture,
% 35.49/5.00      ( v1_funct_1(sK6) ),
% 35.49/5.00      inference(cnf_transformation,[],[f71]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_33,plain,
% 35.49/5.00      ( v1_funct_1(sK6) = iProver_top ),
% 35.49/5.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_16,plain,
% 35.49/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 35.49/5.00      inference(cnf_transformation,[],[f60]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_1509,plain,
% 35.49/5.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 35.49/5.00      | v1_relat_1(sK6) ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_16]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_1510,plain,
% 35.49/5.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 35.49/5.00      | v1_relat_1(sK6) = iProver_top ),
% 35.49/5.00      inference(predicate_to_equality,[status(thm)],[c_1509]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_52567,plain,
% 35.49/5.00      ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top
% 35.49/5.00      | r2_hidden(sK7(sK0(sK5,k2_relat_1(sK6))),k1_relat_1(sK6)) != iProver_top ),
% 35.49/5.00      inference(global_propositional_subsumption,
% 35.49/5.00                [status(thm)],
% 35.49/5.00                [c_10078,c_33,c_35,c_1510]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_52573,plain,
% 35.49/5.00      ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top
% 35.49/5.00      | r2_hidden(sK0(sK5,k2_relat_1(sK6)),sK5) != iProver_top
% 35.49/5.00      | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
% 35.49/5.00      inference(superposition,[status(thm)],[c_3484,c_52567]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_2700,plain,
% 35.49/5.00      ( r2_hidden(sK0(sK5,X0),sK5) | r1_tarski(sK5,X0) ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_1]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_7224,plain,
% 35.49/5.00      ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),sK5)
% 35.49/5.00      | r1_tarski(sK5,k2_relat_1(sK6)) ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_2700]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_7227,plain,
% 35.49/5.00      ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),sK5) = iProver_top
% 35.49/5.00      | r1_tarski(sK5,k2_relat_1(sK6)) = iProver_top ),
% 35.49/5.00      inference(predicate_to_equality,[status(thm)],[c_7224]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_52922,plain,
% 35.49/5.00      ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top
% 35.49/5.00      | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
% 35.49/5.00      inference(global_propositional_subsumption,
% 35.49/5.00                [status(thm)],
% 35.49/5.00                [c_52573,c_30,c_27,c_1561,c_2427,c_3906,c_7225,c_7227]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_4511,plain,
% 35.49/5.00      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 35.49/5.00      | r2_hidden(sK3(X1,X0),X2) = iProver_top
% 35.49/5.00      | r1_tarski(k1_relat_1(X1),X2) != iProver_top
% 35.49/5.00      | v1_relat_1(X1) != iProver_top
% 35.49/5.00      | v1_funct_1(X1) != iProver_top ),
% 35.49/5.00      inference(superposition,[status(thm)],[c_1221,c_1231]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_39505,plain,
% 35.49/5.00      ( k1_funct_1(sK6,sK7(sK3(X0,X1))) = sK3(X0,X1)
% 35.49/5.00      | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
% 35.49/5.00      | r1_tarski(k1_relat_1(X0),sK5) != iProver_top
% 35.49/5.00      | v1_relat_1(X0) != iProver_top
% 35.49/5.00      | v1_funct_1(X0) != iProver_top ),
% 35.49/5.00      inference(superposition,[status(thm)],[c_4511,c_1209]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_52931,plain,
% 35.49/5.00      ( k1_funct_1(sK6,sK7(sK3(sK6,sK0(sK5,k2_relat_1(sK6))))) = sK3(sK6,sK0(sK5,k2_relat_1(sK6)))
% 35.49/5.00      | r1_tarski(k1_relat_1(sK6),sK5) != iProver_top
% 35.49/5.00      | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top
% 35.49/5.00      | v1_relat_1(sK6) != iProver_top
% 35.49/5.00      | v1_funct_1(sK6) != iProver_top ),
% 35.49/5.00      inference(superposition,[status(thm)],[c_52922,c_39505]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_0,plain,
% 35.49/5.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 35.49/5.00      inference(cnf_transformation,[],[f46]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_1233,plain,
% 35.49/5.00      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 35.49/5.00      | r1_tarski(X0,X1) = iProver_top ),
% 35.49/5.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_52928,plain,
% 35.49/5.00      ( r1_tarski(sK5,k2_relat_1(sK6)) = iProver_top
% 35.49/5.00      | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
% 35.49/5.00      inference(superposition,[status(thm)],[c_52922,c_1233]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_53680,plain,
% 35.49/5.00      ( r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
% 35.49/5.00      inference(global_propositional_subsumption,
% 35.49/5.00                [status(thm)],
% 35.49/5.00                [c_52931,c_30,c_27,c_1561,c_2427,c_3906,c_7225,c_52928]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_54471,plain,
% 35.49/5.00      ( sK5 = k1_xboole_0 | r1_tarski(sK4,sK4) != iProver_top ),
% 35.49/5.00      inference(superposition,[status(thm)],[c_54459,c_53680]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_54749,plain,
% 35.49/5.00      ( sK5 = k1_xboole_0 ),
% 35.49/5.00      inference(global_propositional_subsumption,
% 35.49/5.00                [status(thm)],
% 35.49/5.00                [c_54470,c_8784,c_54471]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_54918,plain,
% 35.49/5.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) = iProver_top ),
% 35.49/5.00      inference(demodulation,[status(thm)],[c_54749,c_1207]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_21,plain,
% 35.49/5.00      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 35.49/5.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 35.49/5.00      | k1_xboole_0 = X1
% 35.49/5.00      | k1_xboole_0 = X0 ),
% 35.49/5.00      inference(cnf_transformation,[],[f85]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_1215,plain,
% 35.49/5.00      ( k1_xboole_0 = X0
% 35.49/5.00      | k1_xboole_0 = X1
% 35.49/5.00      | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
% 35.49/5.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
% 35.49/5.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_57301,plain,
% 35.49/5.00      ( sK6 = k1_xboole_0
% 35.49/5.00      | sK4 = k1_xboole_0
% 35.49/5.00      | v1_funct_2(sK6,sK4,k1_xboole_0) != iProver_top ),
% 35.49/5.00      inference(superposition,[status(thm)],[c_54918,c_1215]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_100,plain,
% 35.49/5.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_5]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_104,plain,
% 35.49/5.00      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_3]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_553,plain,( X0 = X0 ),theory(equality) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_1722,plain,
% 35.49/5.00      ( sK4 = sK4 ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_553]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_1629,plain,
% 35.49/5.00      ( ~ r1_tarski(X0,sK6) | ~ r1_tarski(sK6,X0) | X0 = sK6 ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_3]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_1884,plain,
% 35.49/5.00      ( ~ r1_tarski(sK6,sK6) | sK6 = sK6 ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_1629]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_1885,plain,
% 35.49/5.00      ( r1_tarski(sK6,sK6) ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_5]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_2004,plain,
% 35.49/5.00      ( X0 != X1 | X0 = sK5 | sK5 != X1 ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_554]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_2005,plain,
% 35.49/5.00      ( sK5 != k1_xboole_0 | k1_xboole_0 = sK5 | k1_xboole_0 != k1_xboole_0 ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_2004]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_2420,plain,
% 35.49/5.00      ( k2_relset_1(sK4,sK5,sK6) != k2_relset_1(sK4,sK5,sK6)
% 35.49/5.00      | k2_relset_1(sK4,sK5,sK6) = sK5
% 35.49/5.00      | sK5 != k2_relset_1(sK4,sK5,sK6) ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_1531]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_2421,plain,
% 35.49/5.00      ( k2_relset_1(sK4,sK5,sK6) = k2_relset_1(sK4,sK5,sK6) ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_553]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_565,plain,
% 35.49/5.00      ( ~ v1_funct_2(X0,X1,X2)
% 35.49/5.00      | v1_funct_2(X3,X4,X5)
% 35.49/5.00      | X3 != X0
% 35.49/5.00      | X4 != X1
% 35.49/5.00      | X5 != X2 ),
% 35.49/5.00      theory(equality) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_1591,plain,
% 35.49/5.00      ( v1_funct_2(X0,X1,X2)
% 35.49/5.00      | ~ v1_funct_2(sK6,sK4,sK5)
% 35.49/5.00      | X0 != sK6
% 35.49/5.00      | X2 != sK5
% 35.49/5.00      | X1 != sK4 ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_565]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_1721,plain,
% 35.49/5.00      ( v1_funct_2(X0,sK4,X1)
% 35.49/5.00      | ~ v1_funct_2(sK6,sK4,sK5)
% 35.49/5.00      | X0 != sK6
% 35.49/5.00      | X1 != sK5
% 35.49/5.00      | sK4 != sK4 ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_1591]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_2447,plain,
% 35.49/5.00      ( v1_funct_2(sK6,sK4,X0)
% 35.49/5.00      | ~ v1_funct_2(sK6,sK4,sK5)
% 35.49/5.00      | X0 != sK5
% 35.49/5.00      | sK6 != sK6
% 35.49/5.00      | sK4 != sK4 ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_1721]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_2449,plain,
% 35.49/5.00      ( X0 != sK5
% 35.49/5.00      | sK6 != sK6
% 35.49/5.00      | sK4 != sK4
% 35.49/5.00      | v1_funct_2(sK6,sK4,X0) = iProver_top
% 35.49/5.00      | v1_funct_2(sK6,sK4,sK5) != iProver_top ),
% 35.49/5.00      inference(predicate_to_equality,[status(thm)],[c_2447]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_2451,plain,
% 35.49/5.00      ( sK6 != sK6
% 35.49/5.00      | sK4 != sK4
% 35.49/5.00      | k1_xboole_0 != sK5
% 35.49/5.00      | v1_funct_2(sK6,sK4,sK5) != iProver_top
% 35.49/5.00      | v1_funct_2(sK6,sK4,k1_xboole_0) = iProver_top ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_2449]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_2422,plain,
% 35.49/5.00      ( X0 != X1
% 35.49/5.00      | k2_relset_1(sK4,sK5,sK6) != X1
% 35.49/5.00      | k2_relset_1(sK4,sK5,sK6) = X0 ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_554]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_2785,plain,
% 35.49/5.00      ( X0 != k2_relat_1(sK6)
% 35.49/5.00      | k2_relset_1(sK4,sK5,sK6) = X0
% 35.49/5.00      | k2_relset_1(sK4,sK5,sK6) != k2_relat_1(sK6) ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_2422]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_2786,plain,
% 35.49/5.00      ( k2_relset_1(sK4,sK5,sK6) != k2_relat_1(sK6)
% 35.49/5.00      | k2_relset_1(sK4,sK5,sK6) = k1_xboole_0
% 35.49/5.00      | k1_xboole_0 != k2_relat_1(sK6) ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_2785]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_1923,plain,
% 35.49/5.00      ( X0 != X1 | sK6 != X1 | sK6 = X0 ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_554]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_3468,plain,
% 35.49/5.00      ( X0 != sK6 | sK6 = X0 | sK6 != sK6 ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_1923]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_3469,plain,
% 35.49/5.00      ( sK6 != sK6 | sK6 = k1_xboole_0 | k1_xboole_0 != sK6 ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_3468]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_2012,plain,
% 35.49/5.00      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_554]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_3596,plain,
% 35.49/5.00      ( X0 != sK4 | sK4 = X0 | sK4 != sK4 ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_2012]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_3597,plain,
% 35.49/5.00      ( sK4 != sK4 | sK4 = k1_xboole_0 | k1_xboole_0 != sK4 ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_3596]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_1666,plain,
% 35.49/5.00      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_554]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_6669,plain,
% 35.49/5.00      ( k2_relset_1(sK4,sK5,sK6) != X0
% 35.49/5.00      | sK5 != X0
% 35.49/5.00      | sK5 = k2_relset_1(sK4,sK5,sK6) ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_1666]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_6670,plain,
% 35.49/5.00      ( k2_relset_1(sK4,sK5,sK6) != k1_xboole_0
% 35.49/5.00      | sK5 = k2_relset_1(sK4,sK5,sK6)
% 35.49/5.00      | sK5 != k1_xboole_0 ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_6669]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_1651,plain,
% 35.49/5.00      ( ~ v1_funct_2(sK6,X0,k1_xboole_0)
% 35.49/5.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 35.49/5.00      | k1_xboole_0 = X0
% 35.49/5.00      | k1_xboole_0 = sK6 ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_21]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_6694,plain,
% 35.49/5.00      ( ~ v1_funct_2(sK6,sK4,k1_xboole_0)
% 35.49/5.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0)))
% 35.49/5.00      | k1_xboole_0 = sK6
% 35.49/5.00      | k1_xboole_0 = sK4 ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_1651]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_6697,plain,
% 35.49/5.00      ( k1_xboole_0 = sK6
% 35.49/5.00      | k1_xboole_0 = sK4
% 35.49/5.00      | v1_funct_2(sK6,sK4,k1_xboole_0) != iProver_top
% 35.49/5.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) != iProver_top ),
% 35.49/5.00      inference(predicate_to_equality,[status(thm)],[c_6694]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_4670,plain,
% 35.49/5.00      ( X0 != X1 | X0 = k2_relat_1(sK6) | k2_relat_1(sK6) != X1 ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_554]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_8041,plain,
% 35.49/5.00      ( X0 != k2_relat_1(X1)
% 35.49/5.00      | X0 = k2_relat_1(sK6)
% 35.49/5.00      | k2_relat_1(sK6) != k2_relat_1(X1) ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_4670]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_8043,plain,
% 35.49/5.00      ( k2_relat_1(sK6) != k2_relat_1(k1_xboole_0)
% 35.49/5.00      | k1_xboole_0 = k2_relat_1(sK6)
% 35.49/5.00      | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_8041]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_558,plain,
% 35.49/5.00      ( X0 != X1 | k2_relat_1(X0) = k2_relat_1(X1) ),
% 35.49/5.00      theory(equality) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_8042,plain,
% 35.49/5.00      ( k2_relat_1(sK6) = k2_relat_1(X0) | sK6 != X0 ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_558]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_8044,plain,
% 35.49/5.00      ( k2_relat_1(sK6) = k2_relat_1(k1_xboole_0) | sK6 != k1_xboole_0 ),
% 35.49/5.00      inference(instantiation,[status(thm)],[c_8042]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_2502,plain,
% 35.49/5.00      ( X0 != X1 | X1 = X0 ),
% 35.49/5.00      inference(resolution,[status(thm)],[c_554,c_553]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_8,plain,
% 35.49/5.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 35.49/5.00      inference(cnf_transformation,[],[f53]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_12302,plain,
% 35.49/5.00      ( k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
% 35.49/5.00      inference(resolution,[status(thm)],[c_2502,c_8]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_58412,plain,
% 35.49/5.00      ( sK4 = k1_xboole_0 ),
% 35.49/5.00      inference(global_propositional_subsumption,
% 35.49/5.00                [status(thm)],
% 35.49/5.00                [c_57301,c_34,c_30,c_27,c_100,c_104,c_1561,c_1722,c_1884,
% 35.49/5.00                 c_1885,c_2005,c_2420,c_2421,c_2451,c_2786,c_3469,c_3597,
% 35.49/5.00                 c_6670,c_6697,c_8043,c_8044,c_8784,c_12302,c_54471,c_54918]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_58422,plain,
% 35.49/5.00      ( r1_tarski(k1_xboole_0,k1_relat_1(sK6)) != iProver_top ),
% 35.49/5.00      inference(demodulation,[status(thm)],[c_58412,c_53680]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_54910,plain,
% 35.49/5.00      ( k1_relset_1(sK4,k1_xboole_0,sK6) = k1_relat_1(sK6) ),
% 35.49/5.00      inference(demodulation,[status(thm)],[c_54749,c_2480]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_58417,plain,
% 35.49/5.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_relat_1(sK6) ),
% 35.49/5.00      inference(demodulation,[status(thm)],[c_58412,c_54910]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_58419,plain,
% 35.49/5.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 35.49/5.00      inference(demodulation,[status(thm)],[c_58412,c_54918]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_24,plain,
% 35.49/5.00      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 35.49/5.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 35.49/5.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 35.49/5.00      inference(cnf_transformation,[],[f87]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_1212,plain,
% 35.49/5.00      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 35.49/5.00      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 35.49/5.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 35.49/5.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_59495,plain,
% 35.49/5.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0
% 35.49/5.00      | v1_funct_2(sK6,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 35.49/5.00      inference(superposition,[status(thm)],[c_58419,c_1212]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_1206,plain,
% 35.49/5.00      ( v1_funct_2(sK6,sK4,sK5) = iProver_top ),
% 35.49/5.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_54919,plain,
% 35.49/5.00      ( v1_funct_2(sK6,sK4,k1_xboole_0) = iProver_top ),
% 35.49/5.00      inference(demodulation,[status(thm)],[c_54749,c_1206]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_58420,plain,
% 35.49/5.00      ( v1_funct_2(sK6,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 35.49/5.00      inference(demodulation,[status(thm)],[c_58412,c_54919]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_60547,plain,
% 35.49/5.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0 ),
% 35.49/5.00      inference(global_propositional_subsumption,
% 35.49/5.00                [status(thm)],
% 35.49/5.00                [c_59495,c_58420]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_87098,plain,
% 35.49/5.00      ( k1_relat_1(sK6) = k1_xboole_0 ),
% 35.49/5.00      inference(light_normalisation,[status(thm)],[c_58417,c_60547]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_87348,plain,
% 35.49/5.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 35.49/5.00      inference(light_normalisation,[status(thm)],[c_58422,c_87098]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_1229,plain,
% 35.49/5.00      ( r1_tarski(X0,X0) = iProver_top ),
% 35.49/5.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 35.49/5.00  
% 35.49/5.00  cnf(c_87350,plain,
% 35.49/5.00      ( $false ),
% 35.49/5.00      inference(forward_subsumption_resolution,[status(thm)],[c_87348,c_1229]) ).
% 35.49/5.00  
% 35.49/5.00  
% 35.49/5.00  % SZS output end CNFRefutation for theBenchmark.p
% 35.49/5.00  
% 35.49/5.00  ------                               Statistics
% 35.49/5.00  
% 35.49/5.00  ------ Selected
% 35.49/5.00  
% 35.49/5.00  total_time:                             4.102
% 35.49/5.00  
%------------------------------------------------------------------------------
