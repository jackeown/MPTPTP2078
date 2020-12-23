%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:27 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :  144 (1392 expanded)
%              Number of clauses        :   77 ( 354 expanded)
%              Number of leaves         :   16 ( 338 expanded)
%              Depth                    :   25
%              Number of atoms          :  484 (5383 expanded)
%              Number of equality atoms :  263 (2554 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

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
    inference(ennf_transformation,[],[f6])).

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

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f29,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) = X2
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f26,f29,f28,f27])).

fof(f44,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f72,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f73,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( k1_tarski(k1_funct_1(sK6,sK4)) != k2_relset_1(k1_tarski(sK4),sK5,sK6)
      & k1_xboole_0 != sK5
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK4),sK5)))
      & v1_funct_2(sK6,k1_tarski(sK4),sK5)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( k1_tarski(k1_funct_1(sK6,sK4)) != k2_relset_1(k1_tarski(sK4),sK5,sK6)
    & k1_xboole_0 != sK5
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK4),sK5)))
    & v1_funct_2(sK6,k1_tarski(sK4),sK5)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f20,f32])).

fof(f56,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f58,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK4),sK5))) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f61,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f67,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5))) ),
    inference(definition_unfolding,[],[f58,f61])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK0(X0,X1) != X0
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( sK0(X0,X1) = X0
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK0(X0,X1) != X0
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( sK0(X0,X1) = X0
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK0(X0,X1) = X0
      | r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X0,X0,X0) = X1
      | sK0(X0,X1) = X0
      | r2_hidden(sK0(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f36,f61])).

fof(f42,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f75,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f57,plain,(
    v1_funct_2(sK6,k1_tarski(sK4),sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f68,plain,(
    v1_funct_2(sK6,k1_enumset1(sK4,sK4,sK4),sK5) ),
    inference(definition_unfolding,[],[f57,f61])).

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

fof(f17,plain,(
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

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f59,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f33])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f34,f61])).

fof(f71,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_enumset1(X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f65])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f60,plain,(
    k1_tarski(k1_funct_1(sK6,sK4)) != k2_relset_1(k1_tarski(sK4),sK5,sK6) ),
    inference(cnf_transformation,[],[f33])).

fof(f66,plain,(
    k1_enumset1(k1_funct_1(sK6,sK4),k1_funct_1(sK6,sK4),k1_funct_1(sK6,sK4)) != k2_relset_1(k1_enumset1(sK4,sK4,sK4),sK5,sK6) ),
    inference(definition_unfolding,[],[f60,f61,f61])).

fof(f43,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f74,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK0(X0,X1) != X0
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X0,X0,X0) = X1
      | sK0(X0,X1) != X0
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f37,f61])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f35,f61])).

fof(f69,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_enumset1(X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f64])).

fof(f70,plain,(
    ! [X3] : r2_hidden(X3,k1_enumset1(X3,X3,X3)) ),
    inference(equality_resolution,[],[f69])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_500,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_24])).

cnf(c_501,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_500])).

cnf(c_942,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_501])).

cnf(c_502,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_501])).

cnf(c_715,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1084,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) = k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) ),
    inference(instantiation,[status(thm)],[c_715])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_264,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) != k1_zfmisc_1(X0)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_22])).

cnf(c_265,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_264])).

cnf(c_1079,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_265])).

cnf(c_1183,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5))
    | v1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) ),
    inference(instantiation,[status(thm)],[c_1079])).

cnf(c_1184,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5))
    | v1_relat_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1183])).

cnf(c_5,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1313,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1314,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1313])).

cnf(c_1411,plain,
    ( r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_942,c_502,c_1084,c_1184,c_1314])).

cnf(c_1412,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1411])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | k1_enumset1(X0,X0,X0) = X1
    | sK0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_951,plain,
    ( k1_enumset1(X0,X0,X0) = X1
    | sK0(X0,X1) = X0
    | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_470,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_24])).

cnf(c_471,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | r2_hidden(sK3(sK6,X0),k1_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_470])).

cnf(c_944,plain,
    ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(sK3(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_471])).

cnf(c_472,plain,
    ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(sK3(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_471])).

cnf(c_1477,plain,
    ( r2_hidden(sK3(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_944,c_472,c_1084,c_1184,c_1314])).

cnf(c_1478,plain,
    ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(sK3(sK6,X0),k1_relat_1(sK6)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1477])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_324,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_325,plain,
    ( k1_relset_1(X0,X1,sK6) = k1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_324])).

cnf(c_1099,plain,
    ( k1_relset_1(k1_enumset1(sK4,sK4,sK4),sK5,sK6) = k1_relat_1(sK6) ),
    inference(equality_resolution,[status(thm)],[c_325])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK6,k1_enumset1(sK4,sK4,sK4),sK5) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_279,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK6 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_22])).

cnf(c_280,plain,
    ( ~ v1_funct_2(sK6,X0,X1)
    | k1_relset_1(X0,X1,sK6) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_279])).

cnf(c_572,plain,
    ( k1_relset_1(X0,X1,sK6) = X0
    | k1_enumset1(sK4,sK4,sK4) != X0
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK5 != X1
    | sK6 != sK6
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_280])).

cnf(c_573,plain,
    ( k1_relset_1(k1_enumset1(sK4,sK4,sK4),sK5,sK6) = k1_enumset1(sK4,sK4,sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5))
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_572])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_574,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5))
    | k1_relset_1(k1_enumset1(sK4,sK4,sK4),sK5,sK6) = k1_enumset1(sK4,sK4,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_573,c_21])).

cnf(c_575,plain,
    ( k1_relset_1(k1_enumset1(sK4,sK4,sK4),sK5,sK6) = k1_enumset1(sK4,sK4,sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) ),
    inference(renaming,[status(thm)],[c_574])).

cnf(c_636,plain,
    ( k1_relset_1(k1_enumset1(sK4,sK4,sK4),sK5,sK6) = k1_enumset1(sK4,sK4,sK4) ),
    inference(equality_resolution_simp,[status(thm)],[c_575])).

cnf(c_1350,plain,
    ( k1_enumset1(sK4,sK4,sK4) = k1_relat_1(sK6) ),
    inference(demodulation,[status(thm)],[c_1099,c_636])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_949,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3218,plain,
    ( sK4 = X0
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1350,c_949])).

cnf(c_3330,plain,
    ( sK3(sK6,X0) = sK4
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1478,c_3218])).

cnf(c_3984,plain,
    ( k1_enumset1(X0,X0,X0) = k2_relat_1(sK6)
    | sK3(sK6,sK0(X0,k2_relat_1(sK6))) = sK4
    | sK0(X0,k2_relat_1(sK6)) = X0 ),
    inference(superposition,[status(thm)],[c_951,c_3330])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_315,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_316,plain,
    ( k2_relset_1(X0,X1,sK6) = k2_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_315])).

cnf(c_1096,plain,
    ( k2_relset_1(k1_enumset1(sK4,sK4,sK4),sK5,sK6) = k2_relat_1(sK6) ),
    inference(equality_resolution,[status(thm)],[c_316])).

cnf(c_20,negated_conjecture,
    ( k1_enumset1(k1_funct_1(sK6,sK4),k1_funct_1(sK6,sK4),k1_funct_1(sK6,sK4)) != k2_relset_1(k1_enumset1(sK4,sK4,sK4),sK5,sK6) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1159,plain,
    ( k1_enumset1(k1_funct_1(sK6,sK4),k1_funct_1(sK6,sK4),k1_funct_1(sK6,sK4)) != k2_relat_1(sK6) ),
    inference(demodulation,[status(thm)],[c_1096,c_20])).

cnf(c_4223,plain,
    ( sK3(sK6,sK0(k1_funct_1(sK6,sK4),k2_relat_1(sK6))) = sK4
    | sK0(k1_funct_1(sK6,sK4),k2_relat_1(sK6)) = k1_funct_1(sK6,sK4) ),
    inference(superposition,[status(thm)],[c_3984,c_1159])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK3(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_485,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK3(X1,X0)) = X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_24])).

cnf(c_486,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,sK3(sK6,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_485])).

cnf(c_943,plain,
    ( k1_funct_1(sK6,sK3(sK6,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_486])).

cnf(c_487,plain,
    ( k1_funct_1(sK6,sK3(sK6,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_486])).

cnf(c_1400,plain,
    ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | k1_funct_1(sK6,sK3(sK6,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_943,c_487,c_1084,c_1184,c_1314])).

cnf(c_1401,plain,
    ( k1_funct_1(sK6,sK3(sK6,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1400])).

cnf(c_1408,plain,
    ( k1_enumset1(X0,X0,X0) = k2_relat_1(sK6)
    | k1_funct_1(sK6,sK3(sK6,sK0(X0,k2_relat_1(sK6)))) = sK0(X0,k2_relat_1(sK6))
    | sK0(X0,k2_relat_1(sK6)) = X0 ),
    inference(superposition,[status(thm)],[c_951,c_1401])).

cnf(c_3448,plain,
    ( k1_funct_1(sK6,sK3(sK6,sK0(k1_funct_1(sK6,sK4),k2_relat_1(sK6)))) = sK0(k1_funct_1(sK6,sK4),k2_relat_1(sK6))
    | sK0(k1_funct_1(sK6,sK4),k2_relat_1(sK6)) = k1_funct_1(sK6,sK4) ),
    inference(superposition,[status(thm)],[c_1408,c_1159])).

cnf(c_4208,plain,
    ( k1_enumset1(k1_funct_1(sK6,sK4),k1_funct_1(sK6,sK4),k1_funct_1(sK6,sK4)) = k2_relat_1(sK6)
    | sK0(k1_funct_1(sK6,sK4),k2_relat_1(sK6)) = k1_funct_1(sK6,sK4) ),
    inference(superposition,[status(thm)],[c_3984,c_3448])).

cnf(c_4725,plain,
    ( sK0(k1_funct_1(sK6,sK4),k2_relat_1(sK6)) = k1_funct_1(sK6,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4223,c_1159,c_4208])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | k1_enumset1(X0,X0,X0) = X1
    | sK0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_952,plain,
    ( k1_enumset1(X0,X0,X0) = X1
    | sK0(X0,X1) != X0
    | r2_hidden(sK0(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4729,plain,
    ( k1_enumset1(k1_funct_1(sK6,sK4),k1_funct_1(sK6,sK4),k1_funct_1(sK6,sK4)) = k2_relat_1(sK6)
    | r2_hidden(sK0(k1_funct_1(sK6,sK4),k2_relat_1(sK6)),k2_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4725,c_952])).

cnf(c_4735,plain,
    ( k1_enumset1(k1_funct_1(sK6,sK4),k1_funct_1(sK6,sK4),k1_funct_1(sK6,sK4)) = k2_relat_1(sK6)
    | r2_hidden(k1_funct_1(sK6,sK4),k2_relat_1(sK6)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4729,c_4725])).

cnf(c_5520,plain,
    ( r2_hidden(k1_funct_1(sK6,sK4),k2_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4735,c_1159])).

cnf(c_5526,plain,
    ( r2_hidden(sK4,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1412,c_5520])).

cnf(c_2,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_950,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3214,plain,
    ( r2_hidden(sK4,k1_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1350,c_950])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5526,c_3214])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:18:12 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.14/0.94  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/0.94  
% 3.14/0.94  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.14/0.94  
% 3.14/0.94  ------  iProver source info
% 3.14/0.94  
% 3.14/0.94  git: date: 2020-06-30 10:37:57 +0100
% 3.14/0.94  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.14/0.94  git: non_committed_changes: false
% 3.14/0.94  git: last_make_outside_of_git: false
% 3.14/0.94  
% 3.14/0.94  ------ 
% 3.14/0.94  
% 3.14/0.94  ------ Input Options
% 3.14/0.94  
% 3.14/0.94  --out_options                           all
% 3.14/0.94  --tptp_safe_out                         true
% 3.14/0.94  --problem_path                          ""
% 3.14/0.94  --include_path                          ""
% 3.14/0.94  --clausifier                            res/vclausify_rel
% 3.14/0.94  --clausifier_options                    --mode clausify
% 3.14/0.94  --stdin                                 false
% 3.14/0.94  --stats_out                             all
% 3.14/0.94  
% 3.14/0.94  ------ General Options
% 3.14/0.94  
% 3.14/0.94  --fof                                   false
% 3.14/0.94  --time_out_real                         305.
% 3.14/0.94  --time_out_virtual                      -1.
% 3.14/0.94  --symbol_type_check                     false
% 3.14/0.94  --clausify_out                          false
% 3.14/0.94  --sig_cnt_out                           false
% 3.14/0.94  --trig_cnt_out                          false
% 3.14/0.94  --trig_cnt_out_tolerance                1.
% 3.14/0.94  --trig_cnt_out_sk_spl                   false
% 3.14/0.94  --abstr_cl_out                          false
% 3.14/0.94  
% 3.14/0.94  ------ Global Options
% 3.14/0.94  
% 3.14/0.94  --schedule                              default
% 3.14/0.94  --add_important_lit                     false
% 3.14/0.94  --prop_solver_per_cl                    1000
% 3.14/0.94  --min_unsat_core                        false
% 3.14/0.94  --soft_assumptions                      false
% 3.14/0.94  --soft_lemma_size                       3
% 3.14/0.94  --prop_impl_unit_size                   0
% 3.14/0.94  --prop_impl_unit                        []
% 3.14/0.94  --share_sel_clauses                     true
% 3.14/0.94  --reset_solvers                         false
% 3.14/0.94  --bc_imp_inh                            [conj_cone]
% 3.14/0.94  --conj_cone_tolerance                   3.
% 3.14/0.94  --extra_neg_conj                        none
% 3.14/0.94  --large_theory_mode                     true
% 3.14/0.94  --prolific_symb_bound                   200
% 3.14/0.94  --lt_threshold                          2000
% 3.14/0.94  --clause_weak_htbl                      true
% 3.14/0.94  --gc_record_bc_elim                     false
% 3.14/0.94  
% 3.14/0.94  ------ Preprocessing Options
% 3.14/0.94  
% 3.14/0.94  --preprocessing_flag                    true
% 3.14/0.94  --time_out_prep_mult                    0.1
% 3.14/0.94  --splitting_mode                        input
% 3.14/0.94  --splitting_grd                         true
% 3.14/0.94  --splitting_cvd                         false
% 3.14/0.94  --splitting_cvd_svl                     false
% 3.14/0.94  --splitting_nvd                         32
% 3.14/0.94  --sub_typing                            true
% 3.14/0.94  --prep_gs_sim                           true
% 3.14/0.94  --prep_unflatten                        true
% 3.14/0.94  --prep_res_sim                          true
% 3.14/0.94  --prep_upred                            true
% 3.14/0.94  --prep_sem_filter                       exhaustive
% 3.14/0.94  --prep_sem_filter_out                   false
% 3.14/0.94  --pred_elim                             true
% 3.14/0.94  --res_sim_input                         true
% 3.14/0.94  --eq_ax_congr_red                       true
% 3.14/0.94  --pure_diseq_elim                       true
% 3.14/0.94  --brand_transform                       false
% 3.14/0.94  --non_eq_to_eq                          false
% 3.14/0.94  --prep_def_merge                        true
% 3.14/0.94  --prep_def_merge_prop_impl              false
% 3.14/0.94  --prep_def_merge_mbd                    true
% 3.14/0.94  --prep_def_merge_tr_red                 false
% 3.14/0.94  --prep_def_merge_tr_cl                  false
% 3.14/0.94  --smt_preprocessing                     true
% 3.14/0.94  --smt_ac_axioms                         fast
% 3.14/0.94  --preprocessed_out                      false
% 3.14/0.94  --preprocessed_stats                    false
% 3.14/0.94  
% 3.14/0.94  ------ Abstraction refinement Options
% 3.14/0.94  
% 3.14/0.94  --abstr_ref                             []
% 3.14/0.94  --abstr_ref_prep                        false
% 3.14/0.94  --abstr_ref_until_sat                   false
% 3.14/0.94  --abstr_ref_sig_restrict                funpre
% 3.14/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 3.14/0.94  --abstr_ref_under                       []
% 3.14/0.94  
% 3.14/0.94  ------ SAT Options
% 3.14/0.94  
% 3.14/0.94  --sat_mode                              false
% 3.14/0.94  --sat_fm_restart_options                ""
% 3.14/0.94  --sat_gr_def                            false
% 3.14/0.94  --sat_epr_types                         true
% 3.14/0.94  --sat_non_cyclic_types                  false
% 3.14/0.94  --sat_finite_models                     false
% 3.14/0.94  --sat_fm_lemmas                         false
% 3.14/0.94  --sat_fm_prep                           false
% 3.14/0.94  --sat_fm_uc_incr                        true
% 3.14/0.94  --sat_out_model                         small
% 3.14/0.94  --sat_out_clauses                       false
% 3.14/0.94  
% 3.14/0.94  ------ QBF Options
% 3.14/0.94  
% 3.14/0.94  --qbf_mode                              false
% 3.14/0.94  --qbf_elim_univ                         false
% 3.14/0.94  --qbf_dom_inst                          none
% 3.14/0.94  --qbf_dom_pre_inst                      false
% 3.14/0.94  --qbf_sk_in                             false
% 3.14/0.94  --qbf_pred_elim                         true
% 3.14/0.94  --qbf_split                             512
% 3.14/0.94  
% 3.14/0.94  ------ BMC1 Options
% 3.14/0.94  
% 3.14/0.94  --bmc1_incremental                      false
% 3.14/0.94  --bmc1_axioms                           reachable_all
% 3.14/0.94  --bmc1_min_bound                        0
% 3.14/0.94  --bmc1_max_bound                        -1
% 3.14/0.94  --bmc1_max_bound_default                -1
% 3.14/0.94  --bmc1_symbol_reachability              true
% 3.14/0.94  --bmc1_property_lemmas                  false
% 3.14/0.94  --bmc1_k_induction                      false
% 3.14/0.94  --bmc1_non_equiv_states                 false
% 3.14/0.94  --bmc1_deadlock                         false
% 3.14/0.94  --bmc1_ucm                              false
% 3.14/0.94  --bmc1_add_unsat_core                   none
% 3.14/0.94  --bmc1_unsat_core_children              false
% 3.14/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 3.14/0.94  --bmc1_out_stat                         full
% 3.14/0.94  --bmc1_ground_init                      false
% 3.14/0.94  --bmc1_pre_inst_next_state              false
% 3.14/0.94  --bmc1_pre_inst_state                   false
% 3.14/0.94  --bmc1_pre_inst_reach_state             false
% 3.14/0.94  --bmc1_out_unsat_core                   false
% 3.14/0.94  --bmc1_aig_witness_out                  false
% 3.14/0.94  --bmc1_verbose                          false
% 3.14/0.94  --bmc1_dump_clauses_tptp                false
% 3.14/0.94  --bmc1_dump_unsat_core_tptp             false
% 3.14/0.94  --bmc1_dump_file                        -
% 3.14/0.94  --bmc1_ucm_expand_uc_limit              128
% 3.14/0.94  --bmc1_ucm_n_expand_iterations          6
% 3.14/0.94  --bmc1_ucm_extend_mode                  1
% 3.14/0.94  --bmc1_ucm_init_mode                    2
% 3.14/0.94  --bmc1_ucm_cone_mode                    none
% 3.14/0.94  --bmc1_ucm_reduced_relation_type        0
% 3.14/0.94  --bmc1_ucm_relax_model                  4
% 3.14/0.94  --bmc1_ucm_full_tr_after_sat            true
% 3.14/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 3.14/0.94  --bmc1_ucm_layered_model                none
% 3.14/0.94  --bmc1_ucm_max_lemma_size               10
% 3.14/0.94  
% 3.14/0.94  ------ AIG Options
% 3.14/0.94  
% 3.14/0.94  --aig_mode                              false
% 3.14/0.94  
% 3.14/0.94  ------ Instantiation Options
% 3.14/0.94  
% 3.14/0.94  --instantiation_flag                    true
% 3.14/0.94  --inst_sos_flag                         false
% 3.14/0.94  --inst_sos_phase                        true
% 3.14/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.14/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.14/0.94  --inst_lit_sel_side                     num_symb
% 3.14/0.94  --inst_solver_per_active                1400
% 3.14/0.94  --inst_solver_calls_frac                1.
% 3.14/0.94  --inst_passive_queue_type               priority_queues
% 3.14/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.14/0.94  --inst_passive_queues_freq              [25;2]
% 3.14/0.94  --inst_dismatching                      true
% 3.14/0.94  --inst_eager_unprocessed_to_passive     true
% 3.14/0.94  --inst_prop_sim_given                   true
% 3.14/0.94  --inst_prop_sim_new                     false
% 3.14/0.94  --inst_subs_new                         false
% 3.14/0.94  --inst_eq_res_simp                      false
% 3.14/0.94  --inst_subs_given                       false
% 3.14/0.94  --inst_orphan_elimination               true
% 3.14/0.94  --inst_learning_loop_flag               true
% 3.14/0.94  --inst_learning_start                   3000
% 3.14/0.94  --inst_learning_factor                  2
% 3.14/0.94  --inst_start_prop_sim_after_learn       3
% 3.14/0.94  --inst_sel_renew                        solver
% 3.14/0.94  --inst_lit_activity_flag                true
% 3.14/0.94  --inst_restr_to_given                   false
% 3.14/0.94  --inst_activity_threshold               500
% 3.14/0.94  --inst_out_proof                        true
% 3.14/0.94  
% 3.14/0.94  ------ Resolution Options
% 3.14/0.94  
% 3.14/0.94  --resolution_flag                       true
% 3.14/0.94  --res_lit_sel                           adaptive
% 3.14/0.94  --res_lit_sel_side                      none
% 3.14/0.94  --res_ordering                          kbo
% 3.14/0.94  --res_to_prop_solver                    active
% 3.14/0.94  --res_prop_simpl_new                    false
% 3.14/0.94  --res_prop_simpl_given                  true
% 3.14/0.94  --res_passive_queue_type                priority_queues
% 3.14/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.14/0.94  --res_passive_queues_freq               [15;5]
% 3.14/0.94  --res_forward_subs                      full
% 3.14/0.94  --res_backward_subs                     full
% 3.14/0.94  --res_forward_subs_resolution           true
% 3.14/0.94  --res_backward_subs_resolution          true
% 3.14/0.94  --res_orphan_elimination                true
% 3.14/0.94  --res_time_limit                        2.
% 3.14/0.94  --res_out_proof                         true
% 3.14/0.94  
% 3.14/0.94  ------ Superposition Options
% 3.14/0.94  
% 3.14/0.94  --superposition_flag                    true
% 3.14/0.94  --sup_passive_queue_type                priority_queues
% 3.14/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.14/0.94  --sup_passive_queues_freq               [8;1;4]
% 3.14/0.94  --demod_completeness_check              fast
% 3.14/0.94  --demod_use_ground                      true
% 3.14/0.94  --sup_to_prop_solver                    passive
% 3.14/0.94  --sup_prop_simpl_new                    true
% 3.14/0.94  --sup_prop_simpl_given                  true
% 3.14/0.94  --sup_fun_splitting                     false
% 3.14/0.94  --sup_smt_interval                      50000
% 3.14/0.94  
% 3.14/0.94  ------ Superposition Simplification Setup
% 3.14/0.94  
% 3.14/0.94  --sup_indices_passive                   []
% 3.14/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 3.14/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.94  --sup_full_bw                           [BwDemod]
% 3.14/0.94  --sup_immed_triv                        [TrivRules]
% 3.14/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.14/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.94  --sup_immed_bw_main                     []
% 3.14/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 3.14/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/0.94  
% 3.14/0.94  ------ Combination Options
% 3.14/0.94  
% 3.14/0.94  --comb_res_mult                         3
% 3.14/0.94  --comb_sup_mult                         2
% 3.14/0.94  --comb_inst_mult                        10
% 3.14/0.94  
% 3.14/0.94  ------ Debug Options
% 3.14/0.94  
% 3.14/0.94  --dbg_backtrace                         false
% 3.14/0.94  --dbg_dump_prop_clauses                 false
% 3.14/0.94  --dbg_dump_prop_clauses_file            -
% 3.14/0.94  --dbg_out_stat                          false
% 3.14/0.94  ------ Parsing...
% 3.14/0.94  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.14/0.94  
% 3.14/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.14/0.94  
% 3.14/0.94  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.14/0.94  
% 3.14/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.14/0.94  ------ Proving...
% 3.14/0.94  ------ Problem Properties 
% 3.14/0.94  
% 3.14/0.94  
% 3.14/0.94  clauses                                 19
% 3.14/0.94  conjectures                             2
% 3.14/0.94  EPR                                     1
% 3.14/0.94  Horn                                    15
% 3.14/0.94  unary                                   5
% 3.14/0.94  binary                                  3
% 3.14/0.94  lits                                    49
% 3.14/0.94  lits eq                                 26
% 3.14/0.94  fd_pure                                 0
% 3.14/0.94  fd_pseudo                               0
% 3.14/0.94  fd_cond                                 3
% 3.14/0.94  fd_pseudo_cond                          2
% 3.14/0.94  AC symbols                              0
% 3.14/0.94  
% 3.14/0.94  ------ Schedule dynamic 5 is on 
% 3.14/0.94  
% 3.14/0.94  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.14/0.94  
% 3.14/0.94  
% 3.14/0.94  ------ 
% 3.14/0.94  Current options:
% 3.14/0.94  ------ 
% 3.14/0.94  
% 3.14/0.94  ------ Input Options
% 3.14/0.94  
% 3.14/0.94  --out_options                           all
% 3.14/0.94  --tptp_safe_out                         true
% 3.14/0.94  --problem_path                          ""
% 3.14/0.94  --include_path                          ""
% 3.14/0.94  --clausifier                            res/vclausify_rel
% 3.14/0.94  --clausifier_options                    --mode clausify
% 3.14/0.94  --stdin                                 false
% 3.14/0.94  --stats_out                             all
% 3.14/0.94  
% 3.14/0.94  ------ General Options
% 3.14/0.94  
% 3.14/0.94  --fof                                   false
% 3.14/0.94  --time_out_real                         305.
% 3.14/0.94  --time_out_virtual                      -1.
% 3.14/0.94  --symbol_type_check                     false
% 3.14/0.94  --clausify_out                          false
% 3.14/0.94  --sig_cnt_out                           false
% 3.14/0.94  --trig_cnt_out                          false
% 3.14/0.94  --trig_cnt_out_tolerance                1.
% 3.14/0.94  --trig_cnt_out_sk_spl                   false
% 3.14/0.94  --abstr_cl_out                          false
% 3.14/0.94  
% 3.14/0.94  ------ Global Options
% 3.14/0.94  
% 3.14/0.94  --schedule                              default
% 3.14/0.94  --add_important_lit                     false
% 3.14/0.94  --prop_solver_per_cl                    1000
% 3.14/0.94  --min_unsat_core                        false
% 3.14/0.94  --soft_assumptions                      false
% 3.14/0.94  --soft_lemma_size                       3
% 3.14/0.94  --prop_impl_unit_size                   0
% 3.14/0.94  --prop_impl_unit                        []
% 3.14/0.94  --share_sel_clauses                     true
% 3.14/0.94  --reset_solvers                         false
% 3.14/0.94  --bc_imp_inh                            [conj_cone]
% 3.14/0.94  --conj_cone_tolerance                   3.
% 3.14/0.94  --extra_neg_conj                        none
% 3.14/0.94  --large_theory_mode                     true
% 3.14/0.94  --prolific_symb_bound                   200
% 3.14/0.94  --lt_threshold                          2000
% 3.14/0.94  --clause_weak_htbl                      true
% 3.14/0.94  --gc_record_bc_elim                     false
% 3.14/0.94  
% 3.14/0.94  ------ Preprocessing Options
% 3.14/0.94  
% 3.14/0.94  --preprocessing_flag                    true
% 3.14/0.94  --time_out_prep_mult                    0.1
% 3.14/0.94  --splitting_mode                        input
% 3.14/0.94  --splitting_grd                         true
% 3.14/0.94  --splitting_cvd                         false
% 3.14/0.94  --splitting_cvd_svl                     false
% 3.14/0.94  --splitting_nvd                         32
% 3.14/0.94  --sub_typing                            true
% 3.14/0.94  --prep_gs_sim                           true
% 3.14/0.94  --prep_unflatten                        true
% 3.14/0.94  --prep_res_sim                          true
% 3.14/0.94  --prep_upred                            true
% 3.14/0.94  --prep_sem_filter                       exhaustive
% 3.14/0.94  --prep_sem_filter_out                   false
% 3.14/0.94  --pred_elim                             true
% 3.14/0.94  --res_sim_input                         true
% 3.14/0.94  --eq_ax_congr_red                       true
% 3.14/0.94  --pure_diseq_elim                       true
% 3.14/0.94  --brand_transform                       false
% 3.14/0.94  --non_eq_to_eq                          false
% 3.14/0.94  --prep_def_merge                        true
% 3.14/0.94  --prep_def_merge_prop_impl              false
% 3.14/0.94  --prep_def_merge_mbd                    true
% 3.14/0.94  --prep_def_merge_tr_red                 false
% 3.14/0.94  --prep_def_merge_tr_cl                  false
% 3.14/0.94  --smt_preprocessing                     true
% 3.14/0.94  --smt_ac_axioms                         fast
% 3.14/0.94  --preprocessed_out                      false
% 3.14/0.94  --preprocessed_stats                    false
% 3.14/0.94  
% 3.14/0.94  ------ Abstraction refinement Options
% 3.14/0.94  
% 3.14/0.94  --abstr_ref                             []
% 3.14/0.94  --abstr_ref_prep                        false
% 3.14/0.94  --abstr_ref_until_sat                   false
% 3.14/0.94  --abstr_ref_sig_restrict                funpre
% 3.14/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 3.14/0.94  --abstr_ref_under                       []
% 3.14/0.94  
% 3.14/0.94  ------ SAT Options
% 3.14/0.94  
% 3.14/0.94  --sat_mode                              false
% 3.14/0.94  --sat_fm_restart_options                ""
% 3.14/0.94  --sat_gr_def                            false
% 3.14/0.94  --sat_epr_types                         true
% 3.14/0.94  --sat_non_cyclic_types                  false
% 3.14/0.94  --sat_finite_models                     false
% 3.14/0.94  --sat_fm_lemmas                         false
% 3.14/0.94  --sat_fm_prep                           false
% 3.14/0.94  --sat_fm_uc_incr                        true
% 3.14/0.94  --sat_out_model                         small
% 3.14/0.94  --sat_out_clauses                       false
% 3.14/0.94  
% 3.14/0.94  ------ QBF Options
% 3.14/0.94  
% 3.14/0.94  --qbf_mode                              false
% 3.14/0.94  --qbf_elim_univ                         false
% 3.14/0.94  --qbf_dom_inst                          none
% 3.14/0.94  --qbf_dom_pre_inst                      false
% 3.14/0.94  --qbf_sk_in                             false
% 3.14/0.94  --qbf_pred_elim                         true
% 3.14/0.94  --qbf_split                             512
% 3.14/0.94  
% 3.14/0.94  ------ BMC1 Options
% 3.14/0.94  
% 3.14/0.94  --bmc1_incremental                      false
% 3.14/0.94  --bmc1_axioms                           reachable_all
% 3.14/0.94  --bmc1_min_bound                        0
% 3.14/0.94  --bmc1_max_bound                        -1
% 3.14/0.94  --bmc1_max_bound_default                -1
% 3.14/0.94  --bmc1_symbol_reachability              true
% 3.14/0.94  --bmc1_property_lemmas                  false
% 3.14/0.94  --bmc1_k_induction                      false
% 3.14/0.94  --bmc1_non_equiv_states                 false
% 3.14/0.94  --bmc1_deadlock                         false
% 3.14/0.94  --bmc1_ucm                              false
% 3.14/0.94  --bmc1_add_unsat_core                   none
% 3.14/0.94  --bmc1_unsat_core_children              false
% 3.14/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 3.14/0.94  --bmc1_out_stat                         full
% 3.14/0.94  --bmc1_ground_init                      false
% 3.14/0.94  --bmc1_pre_inst_next_state              false
% 3.14/0.94  --bmc1_pre_inst_state                   false
% 3.14/0.94  --bmc1_pre_inst_reach_state             false
% 3.14/0.94  --bmc1_out_unsat_core                   false
% 3.14/0.94  --bmc1_aig_witness_out                  false
% 3.14/0.94  --bmc1_verbose                          false
% 3.14/0.94  --bmc1_dump_clauses_tptp                false
% 3.14/0.94  --bmc1_dump_unsat_core_tptp             false
% 3.14/0.94  --bmc1_dump_file                        -
% 3.14/0.94  --bmc1_ucm_expand_uc_limit              128
% 3.14/0.94  --bmc1_ucm_n_expand_iterations          6
% 3.14/0.94  --bmc1_ucm_extend_mode                  1
% 3.14/0.94  --bmc1_ucm_init_mode                    2
% 3.14/0.94  --bmc1_ucm_cone_mode                    none
% 3.14/0.94  --bmc1_ucm_reduced_relation_type        0
% 3.14/0.94  --bmc1_ucm_relax_model                  4
% 3.14/0.94  --bmc1_ucm_full_tr_after_sat            true
% 3.14/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 3.14/0.94  --bmc1_ucm_layered_model                none
% 3.14/0.94  --bmc1_ucm_max_lemma_size               10
% 3.14/0.94  
% 3.14/0.94  ------ AIG Options
% 3.14/0.94  
% 3.14/0.94  --aig_mode                              false
% 3.14/0.94  
% 3.14/0.94  ------ Instantiation Options
% 3.14/0.94  
% 3.14/0.94  --instantiation_flag                    true
% 3.14/0.94  --inst_sos_flag                         false
% 3.14/0.94  --inst_sos_phase                        true
% 3.14/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.14/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.14/0.94  --inst_lit_sel_side                     none
% 3.14/0.94  --inst_solver_per_active                1400
% 3.14/0.94  --inst_solver_calls_frac                1.
% 3.14/0.94  --inst_passive_queue_type               priority_queues
% 3.14/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.14/0.94  --inst_passive_queues_freq              [25;2]
% 3.14/0.94  --inst_dismatching                      true
% 3.14/0.94  --inst_eager_unprocessed_to_passive     true
% 3.14/0.94  --inst_prop_sim_given                   true
% 3.14/0.94  --inst_prop_sim_new                     false
% 3.14/0.94  --inst_subs_new                         false
% 3.14/0.94  --inst_eq_res_simp                      false
% 3.14/0.94  --inst_subs_given                       false
% 3.14/0.94  --inst_orphan_elimination               true
% 3.14/0.94  --inst_learning_loop_flag               true
% 3.14/0.94  --inst_learning_start                   3000
% 3.14/0.94  --inst_learning_factor                  2
% 3.14/0.94  --inst_start_prop_sim_after_learn       3
% 3.14/0.94  --inst_sel_renew                        solver
% 3.14/0.94  --inst_lit_activity_flag                true
% 3.14/0.94  --inst_restr_to_given                   false
% 3.14/0.94  --inst_activity_threshold               500
% 3.14/0.94  --inst_out_proof                        true
% 3.14/0.94  
% 3.14/0.94  ------ Resolution Options
% 3.14/0.94  
% 3.14/0.94  --resolution_flag                       false
% 3.14/0.94  --res_lit_sel                           adaptive
% 3.14/0.94  --res_lit_sel_side                      none
% 3.14/0.94  --res_ordering                          kbo
% 3.14/0.94  --res_to_prop_solver                    active
% 3.14/0.94  --res_prop_simpl_new                    false
% 3.14/0.94  --res_prop_simpl_given                  true
% 3.14/0.94  --res_passive_queue_type                priority_queues
% 3.14/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.14/0.94  --res_passive_queues_freq               [15;5]
% 3.14/0.94  --res_forward_subs                      full
% 3.14/0.94  --res_backward_subs                     full
% 3.14/0.94  --res_forward_subs_resolution           true
% 3.14/0.94  --res_backward_subs_resolution          true
% 3.14/0.94  --res_orphan_elimination                true
% 3.14/0.94  --res_time_limit                        2.
% 3.14/0.94  --res_out_proof                         true
% 3.14/0.94  
% 3.14/0.94  ------ Superposition Options
% 3.14/0.94  
% 3.14/0.94  --superposition_flag                    true
% 3.14/0.94  --sup_passive_queue_type                priority_queues
% 3.14/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.14/0.94  --sup_passive_queues_freq               [8;1;4]
% 3.14/0.94  --demod_completeness_check              fast
% 3.14/0.94  --demod_use_ground                      true
% 3.14/0.94  --sup_to_prop_solver                    passive
% 3.14/0.94  --sup_prop_simpl_new                    true
% 3.14/0.94  --sup_prop_simpl_given                  true
% 3.14/0.94  --sup_fun_splitting                     false
% 3.14/0.94  --sup_smt_interval                      50000
% 3.14/0.94  
% 3.14/0.94  ------ Superposition Simplification Setup
% 3.14/0.94  
% 3.14/0.94  --sup_indices_passive                   []
% 3.14/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 3.14/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.94  --sup_full_bw                           [BwDemod]
% 3.14/0.94  --sup_immed_triv                        [TrivRules]
% 3.14/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.14/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.94  --sup_immed_bw_main                     []
% 3.14/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 3.14/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/0.94  
% 3.14/0.94  ------ Combination Options
% 3.14/0.94  
% 3.14/0.94  --comb_res_mult                         3
% 3.14/0.94  --comb_sup_mult                         2
% 3.14/0.94  --comb_inst_mult                        10
% 3.14/0.94  
% 3.14/0.94  ------ Debug Options
% 3.14/0.94  
% 3.14/0.94  --dbg_backtrace                         false
% 3.14/0.94  --dbg_dump_prop_clauses                 false
% 3.14/0.94  --dbg_dump_prop_clauses_file            -
% 3.14/0.94  --dbg_out_stat                          false
% 3.14/0.94  
% 3.14/0.94  
% 3.14/0.94  
% 3.14/0.94  
% 3.14/0.94  ------ Proving...
% 3.14/0.94  
% 3.14/0.94  
% 3.14/0.94  % SZS status Theorem for theBenchmark.p
% 3.14/0.94  
% 3.14/0.94  % SZS output start CNFRefutation for theBenchmark.p
% 3.14/0.94  
% 3.14/0.94  fof(f6,axiom,(
% 3.14/0.94    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.14/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/0.94  
% 3.14/0.94  fof(f13,plain,(
% 3.14/0.94    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.14/0.94    inference(ennf_transformation,[],[f6])).
% 3.14/0.94  
% 3.14/0.94  fof(f14,plain,(
% 3.14/0.94    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.14/0.94    inference(flattening,[],[f13])).
% 3.14/0.94  
% 3.14/0.94  fof(f25,plain,(
% 3.14/0.94    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.14/0.94    inference(nnf_transformation,[],[f14])).
% 3.14/0.94  
% 3.14/0.94  fof(f26,plain,(
% 3.14/0.94    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.14/0.94    inference(rectify,[],[f25])).
% 3.14/0.94  
% 3.14/0.94  fof(f29,plain,(
% 3.14/0.94    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))))),
% 3.14/0.94    introduced(choice_axiom,[])).
% 3.14/0.94  
% 3.14/0.94  fof(f28,plain,(
% 3.14/0.94    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) = X2 & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))) )),
% 3.14/0.94    introduced(choice_axiom,[])).
% 3.14/0.94  
% 3.14/0.94  fof(f27,plain,(
% 3.14/0.94    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1))))),
% 3.14/0.94    introduced(choice_axiom,[])).
% 3.14/0.94  
% 3.14/0.94  fof(f30,plain,(
% 3.14/0.94    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & ((k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.14/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f26,f29,f28,f27])).
% 3.14/0.94  
% 3.14/0.94  fof(f44,plain,(
% 3.14/0.94    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.14/0.94    inference(cnf_transformation,[],[f30])).
% 3.14/0.94  
% 3.14/0.94  fof(f72,plain,(
% 3.14/0.94    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.14/0.94    inference(equality_resolution,[],[f44])).
% 3.14/0.94  
% 3.14/0.94  fof(f73,plain,(
% 3.14/0.94    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.14/0.94    inference(equality_resolution,[],[f72])).
% 3.14/0.94  
% 3.14/0.94  fof(f10,conjecture,(
% 3.14/0.94    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 3.14/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/0.95  
% 3.14/0.95  fof(f11,negated_conjecture,(
% 3.14/0.95    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 3.14/0.95    inference(negated_conjecture,[],[f10])).
% 3.14/0.95  
% 3.14/0.95  fof(f19,plain,(
% 3.14/0.95    ? [X0,X1,X2] : ((k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 3.14/0.95    inference(ennf_transformation,[],[f11])).
% 3.14/0.95  
% 3.14/0.95  fof(f20,plain,(
% 3.14/0.95    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 3.14/0.95    inference(flattening,[],[f19])).
% 3.14/0.95  
% 3.14/0.95  fof(f32,plain,(
% 3.14/0.95    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_tarski(k1_funct_1(sK6,sK4)) != k2_relset_1(k1_tarski(sK4),sK5,sK6) & k1_xboole_0 != sK5 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK4),sK5))) & v1_funct_2(sK6,k1_tarski(sK4),sK5) & v1_funct_1(sK6))),
% 3.14/0.95    introduced(choice_axiom,[])).
% 3.14/0.95  
% 3.14/0.95  fof(f33,plain,(
% 3.14/0.95    k1_tarski(k1_funct_1(sK6,sK4)) != k2_relset_1(k1_tarski(sK4),sK5,sK6) & k1_xboole_0 != sK5 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK4),sK5))) & v1_funct_2(sK6,k1_tarski(sK4),sK5) & v1_funct_1(sK6)),
% 3.14/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f20,f32])).
% 3.14/0.95  
% 3.14/0.95  fof(f56,plain,(
% 3.14/0.95    v1_funct_1(sK6)),
% 3.14/0.95    inference(cnf_transformation,[],[f33])).
% 3.14/0.95  
% 3.14/0.95  fof(f4,axiom,(
% 3.14/0.95    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.14/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/0.95  
% 3.14/0.95  fof(f12,plain,(
% 3.14/0.95    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.14/0.95    inference(ennf_transformation,[],[f4])).
% 3.14/0.95  
% 3.14/0.95  fof(f40,plain,(
% 3.14/0.95    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.14/0.95    inference(cnf_transformation,[],[f12])).
% 3.14/0.95  
% 3.14/0.95  fof(f58,plain,(
% 3.14/0.95    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK4),sK5)))),
% 3.14/0.95    inference(cnf_transformation,[],[f33])).
% 3.14/0.95  
% 3.14/0.95  fof(f2,axiom,(
% 3.14/0.95    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.14/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/0.95  
% 3.14/0.95  fof(f38,plain,(
% 3.14/0.95    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.14/0.95    inference(cnf_transformation,[],[f2])).
% 3.14/0.95  
% 3.14/0.95  fof(f3,axiom,(
% 3.14/0.95    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.14/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/0.95  
% 3.14/0.95  fof(f39,plain,(
% 3.14/0.95    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.14/0.95    inference(cnf_transformation,[],[f3])).
% 3.14/0.95  
% 3.14/0.95  fof(f61,plain,(
% 3.14/0.95    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 3.14/0.95    inference(definition_unfolding,[],[f38,f39])).
% 3.14/0.95  
% 3.14/0.95  fof(f67,plain,(
% 3.14/0.95    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)))),
% 3.14/0.95    inference(definition_unfolding,[],[f58,f61])).
% 3.14/0.95  
% 3.14/0.95  fof(f5,axiom,(
% 3.14/0.95    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.14/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/0.95  
% 3.14/0.95  fof(f41,plain,(
% 3.14/0.95    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.14/0.95    inference(cnf_transformation,[],[f5])).
% 3.14/0.95  
% 3.14/0.95  fof(f1,axiom,(
% 3.14/0.95    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.14/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/0.95  
% 3.14/0.95  fof(f21,plain,(
% 3.14/0.95    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.14/0.95    inference(nnf_transformation,[],[f1])).
% 3.14/0.95  
% 3.14/0.95  fof(f22,plain,(
% 3.14/0.95    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.14/0.95    inference(rectify,[],[f21])).
% 3.14/0.95  
% 3.14/0.95  fof(f23,plain,(
% 3.14/0.95    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 3.14/0.95    introduced(choice_axiom,[])).
% 3.14/0.95  
% 3.14/0.95  fof(f24,plain,(
% 3.14/0.95    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.14/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 3.14/0.95  
% 3.14/0.95  fof(f36,plain,(
% 3.14/0.95    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)) )),
% 3.14/0.95    inference(cnf_transformation,[],[f24])).
% 3.14/0.95  
% 3.14/0.95  fof(f63,plain,(
% 3.14/0.95    ( ! [X0,X1] : (k1_enumset1(X0,X0,X0) = X1 | sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)) )),
% 3.14/0.95    inference(definition_unfolding,[],[f36,f61])).
% 3.14/0.95  
% 3.14/0.95  fof(f42,plain,(
% 3.14/0.95    ( ! [X0,X5,X1] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.14/0.95    inference(cnf_transformation,[],[f30])).
% 3.14/0.95  
% 3.14/0.95  fof(f75,plain,(
% 3.14/0.95    ( ! [X0,X5] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.14/0.95    inference(equality_resolution,[],[f42])).
% 3.14/0.95  
% 3.14/0.95  fof(f7,axiom,(
% 3.14/0.95    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.14/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/0.95  
% 3.14/0.95  fof(f15,plain,(
% 3.14/0.95    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/0.95    inference(ennf_transformation,[],[f7])).
% 3.14/0.95  
% 3.14/0.95  fof(f48,plain,(
% 3.14/0.95    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.14/0.95    inference(cnf_transformation,[],[f15])).
% 3.14/0.95  
% 3.14/0.95  fof(f57,plain,(
% 3.14/0.95    v1_funct_2(sK6,k1_tarski(sK4),sK5)),
% 3.14/0.95    inference(cnf_transformation,[],[f33])).
% 3.14/0.95  
% 3.14/0.95  fof(f68,plain,(
% 3.14/0.95    v1_funct_2(sK6,k1_enumset1(sK4,sK4,sK4),sK5)),
% 3.14/0.95    inference(definition_unfolding,[],[f57,f61])).
% 3.14/0.95  
% 3.14/0.95  fof(f9,axiom,(
% 3.14/0.95    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.14/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/0.95  
% 3.14/0.95  fof(f17,plain,(
% 3.14/0.95    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/0.95    inference(ennf_transformation,[],[f9])).
% 3.14/0.95  
% 3.14/0.95  fof(f18,plain,(
% 3.14/0.95    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/0.95    inference(flattening,[],[f17])).
% 3.14/0.95  
% 3.14/0.95  fof(f31,plain,(
% 3.14/0.95    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/0.95    inference(nnf_transformation,[],[f18])).
% 3.14/0.95  
% 3.14/0.95  fof(f50,plain,(
% 3.14/0.95    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.14/0.95    inference(cnf_transformation,[],[f31])).
% 3.14/0.95  
% 3.14/0.95  fof(f59,plain,(
% 3.14/0.95    k1_xboole_0 != sK5),
% 3.14/0.95    inference(cnf_transformation,[],[f33])).
% 3.14/0.95  
% 3.14/0.95  fof(f34,plain,(
% 3.14/0.95    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.14/0.95    inference(cnf_transformation,[],[f24])).
% 3.14/0.95  
% 3.14/0.95  fof(f65,plain,(
% 3.14/0.95    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 3.14/0.95    inference(definition_unfolding,[],[f34,f61])).
% 3.14/0.95  
% 3.14/0.95  fof(f71,plain,(
% 3.14/0.95    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_enumset1(X0,X0,X0))) )),
% 3.14/0.95    inference(equality_resolution,[],[f65])).
% 3.14/0.95  
% 3.14/0.95  fof(f8,axiom,(
% 3.14/0.95    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.14/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/0.95  
% 3.14/0.95  fof(f16,plain,(
% 3.14/0.95    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/0.95    inference(ennf_transformation,[],[f8])).
% 3.14/0.95  
% 3.14/0.95  fof(f49,plain,(
% 3.14/0.95    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.14/0.95    inference(cnf_transformation,[],[f16])).
% 3.14/0.95  
% 3.14/0.95  fof(f60,plain,(
% 3.14/0.95    k1_tarski(k1_funct_1(sK6,sK4)) != k2_relset_1(k1_tarski(sK4),sK5,sK6)),
% 3.14/0.95    inference(cnf_transformation,[],[f33])).
% 3.14/0.95  
% 3.14/0.95  fof(f66,plain,(
% 3.14/0.95    k1_enumset1(k1_funct_1(sK6,sK4),k1_funct_1(sK6,sK4),k1_funct_1(sK6,sK4)) != k2_relset_1(k1_enumset1(sK4,sK4,sK4),sK5,sK6)),
% 3.14/0.95    inference(definition_unfolding,[],[f60,f61,f61])).
% 3.14/0.95  
% 3.14/0.95  fof(f43,plain,(
% 3.14/0.95    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK3(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.14/0.95    inference(cnf_transformation,[],[f30])).
% 3.14/0.95  
% 3.14/0.95  fof(f74,plain,(
% 3.14/0.95    ( ! [X0,X5] : (k1_funct_1(X0,sK3(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.14/0.95    inference(equality_resolution,[],[f43])).
% 3.14/0.95  
% 3.14/0.95  fof(f37,plain,(
% 3.14/0.95    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.14/0.95    inference(cnf_transformation,[],[f24])).
% 3.14/0.95  
% 3.14/0.95  fof(f62,plain,(
% 3.14/0.95    ( ! [X0,X1] : (k1_enumset1(X0,X0,X0) = X1 | sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.14/0.95    inference(definition_unfolding,[],[f37,f61])).
% 3.14/0.95  
% 3.14/0.95  fof(f35,plain,(
% 3.14/0.95    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.14/0.95    inference(cnf_transformation,[],[f24])).
% 3.14/0.95  
% 3.14/0.95  fof(f64,plain,(
% 3.14/0.95    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_enumset1(X0,X0,X0) != X1) )),
% 3.14/0.95    inference(definition_unfolding,[],[f35,f61])).
% 3.14/0.95  
% 3.14/0.95  fof(f69,plain,(
% 3.14/0.95    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_enumset1(X3,X3,X3) != X1) )),
% 3.14/0.95    inference(equality_resolution,[],[f64])).
% 3.14/0.95  
% 3.14/0.95  fof(f70,plain,(
% 3.14/0.95    ( ! [X3] : (r2_hidden(X3,k1_enumset1(X3,X3,X3))) )),
% 3.14/0.95    inference(equality_resolution,[],[f69])).
% 3.14/0.95  
% 3.14/0.95  cnf(c_9,plain,
% 3.14/0.95      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.14/0.95      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.14/0.95      | ~ v1_funct_1(X1)
% 3.14/0.95      | ~ v1_relat_1(X1) ),
% 3.14/0.95      inference(cnf_transformation,[],[f73]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_24,negated_conjecture,
% 3.14/0.95      ( v1_funct_1(sK6) ),
% 3.14/0.95      inference(cnf_transformation,[],[f56]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_500,plain,
% 3.14/0.95      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.14/0.95      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.14/0.95      | ~ v1_relat_1(X1)
% 3.14/0.95      | sK6 != X1 ),
% 3.14/0.95      inference(resolution_lifted,[status(thm)],[c_9,c_24]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_501,plain,
% 3.14/0.95      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 3.14/0.95      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6))
% 3.14/0.95      | ~ v1_relat_1(sK6) ),
% 3.14/0.95      inference(unflattening,[status(thm)],[c_500]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_942,plain,
% 3.14/0.95      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 3.14/0.95      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
% 3.14/0.95      | v1_relat_1(sK6) != iProver_top ),
% 3.14/0.95      inference(predicate_to_equality,[status(thm)],[c_501]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_502,plain,
% 3.14/0.95      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 3.14/0.95      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
% 3.14/0.95      | v1_relat_1(sK6) != iProver_top ),
% 3.14/0.95      inference(predicate_to_equality,[status(thm)],[c_501]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_715,plain,( X0 = X0 ),theory(equality) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_1084,plain,
% 3.14/0.95      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) = k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) ),
% 3.14/0.95      inference(instantiation,[status(thm)],[c_715]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_4,plain,
% 3.14/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.14/0.95      | ~ v1_relat_1(X1)
% 3.14/0.95      | v1_relat_1(X0) ),
% 3.14/0.95      inference(cnf_transformation,[],[f40]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_22,negated_conjecture,
% 3.14/0.95      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5))) ),
% 3.14/0.95      inference(cnf_transformation,[],[f67]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_264,plain,
% 3.14/0.95      ( ~ v1_relat_1(X0)
% 3.14/0.95      | v1_relat_1(X1)
% 3.14/0.95      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) != k1_zfmisc_1(X0)
% 3.14/0.95      | sK6 != X1 ),
% 3.14/0.95      inference(resolution_lifted,[status(thm)],[c_4,c_22]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_265,plain,
% 3.14/0.95      ( ~ v1_relat_1(X0)
% 3.14/0.95      | v1_relat_1(sK6)
% 3.14/0.95      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) != k1_zfmisc_1(X0) ),
% 3.14/0.95      inference(unflattening,[status(thm)],[c_264]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_1079,plain,
% 3.14/0.95      ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 3.14/0.95      | v1_relat_1(sK6)
% 3.14/0.95      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.14/0.95      inference(instantiation,[status(thm)],[c_265]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_1183,plain,
% 3.14/0.95      ( ~ v1_relat_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5))
% 3.14/0.95      | v1_relat_1(sK6)
% 3.14/0.95      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) ),
% 3.14/0.95      inference(instantiation,[status(thm)],[c_1079]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_1184,plain,
% 3.14/0.95      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5))
% 3.14/0.95      | v1_relat_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) != iProver_top
% 3.14/0.95      | v1_relat_1(sK6) = iProver_top ),
% 3.14/0.95      inference(predicate_to_equality,[status(thm)],[c_1183]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_5,plain,
% 3.14/0.95      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.14/0.95      inference(cnf_transformation,[],[f41]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_1313,plain,
% 3.14/0.95      ( v1_relat_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) ),
% 3.14/0.95      inference(instantiation,[status(thm)],[c_5]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_1314,plain,
% 3.14/0.95      ( v1_relat_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) = iProver_top ),
% 3.14/0.95      inference(predicate_to_equality,[status(thm)],[c_1313]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_1411,plain,
% 3.14/0.95      ( r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
% 3.14/0.95      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 3.14/0.95      inference(global_propositional_subsumption,
% 3.14/0.95                [status(thm)],
% 3.14/0.95                [c_942,c_502,c_1084,c_1184,c_1314]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_1412,plain,
% 3.14/0.95      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 3.14/0.95      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top ),
% 3.14/0.95      inference(renaming,[status(thm)],[c_1411]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_1,plain,
% 3.14/0.95      ( r2_hidden(sK0(X0,X1),X1)
% 3.14/0.95      | k1_enumset1(X0,X0,X0) = X1
% 3.14/0.95      | sK0(X0,X1) = X0 ),
% 3.14/0.95      inference(cnf_transformation,[],[f63]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_951,plain,
% 3.14/0.95      ( k1_enumset1(X0,X0,X0) = X1
% 3.14/0.95      | sK0(X0,X1) = X0
% 3.14/0.95      | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
% 3.14/0.95      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_11,plain,
% 3.14/0.95      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.14/0.95      | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
% 3.14/0.95      | ~ v1_funct_1(X1)
% 3.14/0.95      | ~ v1_relat_1(X1) ),
% 3.14/0.95      inference(cnf_transformation,[],[f75]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_470,plain,
% 3.14/0.95      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.14/0.95      | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
% 3.14/0.95      | ~ v1_relat_1(X1)
% 3.14/0.95      | sK6 != X1 ),
% 3.14/0.95      inference(resolution_lifted,[status(thm)],[c_11,c_24]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_471,plain,
% 3.14/0.95      ( ~ r2_hidden(X0,k2_relat_1(sK6))
% 3.14/0.95      | r2_hidden(sK3(sK6,X0),k1_relat_1(sK6))
% 3.14/0.95      | ~ v1_relat_1(sK6) ),
% 3.14/0.95      inference(unflattening,[status(thm)],[c_470]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_944,plain,
% 3.14/0.95      ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 3.14/0.95      | r2_hidden(sK3(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 3.14/0.95      | v1_relat_1(sK6) != iProver_top ),
% 3.14/0.95      inference(predicate_to_equality,[status(thm)],[c_471]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_472,plain,
% 3.14/0.95      ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 3.14/0.95      | r2_hidden(sK3(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 3.14/0.95      | v1_relat_1(sK6) != iProver_top ),
% 3.14/0.95      inference(predicate_to_equality,[status(thm)],[c_471]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_1477,plain,
% 3.14/0.95      ( r2_hidden(sK3(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 3.14/0.95      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
% 3.14/0.95      inference(global_propositional_subsumption,
% 3.14/0.95                [status(thm)],
% 3.14/0.95                [c_944,c_472,c_1084,c_1184,c_1314]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_1478,plain,
% 3.14/0.95      ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 3.14/0.95      | r2_hidden(sK3(sK6,X0),k1_relat_1(sK6)) = iProver_top ),
% 3.14/0.95      inference(renaming,[status(thm)],[c_1477]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_12,plain,
% 3.14/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/0.95      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.14/0.95      inference(cnf_transformation,[],[f48]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_324,plain,
% 3.14/0.95      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.14/0.95      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.14/0.95      | sK6 != X2 ),
% 3.14/0.95      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_325,plain,
% 3.14/0.95      ( k1_relset_1(X0,X1,sK6) = k1_relat_1(sK6)
% 3.14/0.95      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.14/0.95      inference(unflattening,[status(thm)],[c_324]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_1099,plain,
% 3.14/0.95      ( k1_relset_1(k1_enumset1(sK4,sK4,sK4),sK5,sK6) = k1_relat_1(sK6) ),
% 3.14/0.95      inference(equality_resolution,[status(thm)],[c_325]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_23,negated_conjecture,
% 3.14/0.95      ( v1_funct_2(sK6,k1_enumset1(sK4,sK4,sK4),sK5) ),
% 3.14/0.95      inference(cnf_transformation,[],[f68]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_19,plain,
% 3.14/0.95      ( ~ v1_funct_2(X0,X1,X2)
% 3.14/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/0.95      | k1_relset_1(X1,X2,X0) = X1
% 3.14/0.95      | k1_xboole_0 = X2 ),
% 3.14/0.95      inference(cnf_transformation,[],[f50]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_279,plain,
% 3.14/0.95      ( ~ v1_funct_2(X0,X1,X2)
% 3.14/0.95      | k1_relset_1(X1,X2,X0) = X1
% 3.14/0.95      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 3.14/0.95      | sK6 != X0
% 3.14/0.95      | k1_xboole_0 = X2 ),
% 3.14/0.95      inference(resolution_lifted,[status(thm)],[c_19,c_22]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_280,plain,
% 3.14/0.95      ( ~ v1_funct_2(sK6,X0,X1)
% 3.14/0.95      | k1_relset_1(X0,X1,sK6) = X0
% 3.14/0.95      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.14/0.95      | k1_xboole_0 = X1 ),
% 3.14/0.95      inference(unflattening,[status(thm)],[c_279]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_572,plain,
% 3.14/0.95      ( k1_relset_1(X0,X1,sK6) = X0
% 3.14/0.95      | k1_enumset1(sK4,sK4,sK4) != X0
% 3.14/0.95      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.14/0.95      | sK5 != X1
% 3.14/0.95      | sK6 != sK6
% 3.14/0.95      | k1_xboole_0 = X1 ),
% 3.14/0.95      inference(resolution_lifted,[status(thm)],[c_23,c_280]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_573,plain,
% 3.14/0.95      ( k1_relset_1(k1_enumset1(sK4,sK4,sK4),sK5,sK6) = k1_enumset1(sK4,sK4,sK4)
% 3.14/0.95      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5))
% 3.14/0.95      | k1_xboole_0 = sK5 ),
% 3.14/0.95      inference(unflattening,[status(thm)],[c_572]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_21,negated_conjecture,
% 3.14/0.95      ( k1_xboole_0 != sK5 ),
% 3.14/0.95      inference(cnf_transformation,[],[f59]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_574,plain,
% 3.14/0.95      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5))
% 3.14/0.95      | k1_relset_1(k1_enumset1(sK4,sK4,sK4),sK5,sK6) = k1_enumset1(sK4,sK4,sK4) ),
% 3.14/0.95      inference(global_propositional_subsumption,
% 3.14/0.95                [status(thm)],
% 3.14/0.95                [c_573,c_21]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_575,plain,
% 3.14/0.95      ( k1_relset_1(k1_enumset1(sK4,sK4,sK4),sK5,sK6) = k1_enumset1(sK4,sK4,sK4)
% 3.14/0.95      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) ),
% 3.14/0.95      inference(renaming,[status(thm)],[c_574]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_636,plain,
% 3.14/0.95      ( k1_relset_1(k1_enumset1(sK4,sK4,sK4),sK5,sK6) = k1_enumset1(sK4,sK4,sK4) ),
% 3.14/0.95      inference(equality_resolution_simp,[status(thm)],[c_575]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_1350,plain,
% 3.14/0.95      ( k1_enumset1(sK4,sK4,sK4) = k1_relat_1(sK6) ),
% 3.14/0.95      inference(demodulation,[status(thm)],[c_1099,c_636]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_3,plain,
% 3.14/0.95      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1)) | X0 = X1 ),
% 3.14/0.95      inference(cnf_transformation,[],[f71]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_949,plain,
% 3.14/0.95      ( X0 = X1 | r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top ),
% 3.14/0.95      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_3218,plain,
% 3.14/0.95      ( sK4 = X0 | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 3.14/0.95      inference(superposition,[status(thm)],[c_1350,c_949]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_3330,plain,
% 3.14/0.95      ( sK3(sK6,X0) = sK4
% 3.14/0.95      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
% 3.14/0.95      inference(superposition,[status(thm)],[c_1478,c_3218]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_3984,plain,
% 3.14/0.95      ( k1_enumset1(X0,X0,X0) = k2_relat_1(sK6)
% 3.14/0.95      | sK3(sK6,sK0(X0,k2_relat_1(sK6))) = sK4
% 3.14/0.95      | sK0(X0,k2_relat_1(sK6)) = X0 ),
% 3.14/0.95      inference(superposition,[status(thm)],[c_951,c_3330]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_13,plain,
% 3.14/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/0.95      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.14/0.95      inference(cnf_transformation,[],[f49]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_315,plain,
% 3.14/0.95      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.14/0.95      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.14/0.95      | sK6 != X2 ),
% 3.14/0.95      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_316,plain,
% 3.14/0.95      ( k2_relset_1(X0,X1,sK6) = k2_relat_1(sK6)
% 3.14/0.95      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.14/0.95      inference(unflattening,[status(thm)],[c_315]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_1096,plain,
% 3.14/0.95      ( k2_relset_1(k1_enumset1(sK4,sK4,sK4),sK5,sK6) = k2_relat_1(sK6) ),
% 3.14/0.95      inference(equality_resolution,[status(thm)],[c_316]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_20,negated_conjecture,
% 3.14/0.95      ( k1_enumset1(k1_funct_1(sK6,sK4),k1_funct_1(sK6,sK4),k1_funct_1(sK6,sK4)) != k2_relset_1(k1_enumset1(sK4,sK4,sK4),sK5,sK6) ),
% 3.14/0.95      inference(cnf_transformation,[],[f66]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_1159,plain,
% 3.14/0.95      ( k1_enumset1(k1_funct_1(sK6,sK4),k1_funct_1(sK6,sK4),k1_funct_1(sK6,sK4)) != k2_relat_1(sK6) ),
% 3.14/0.95      inference(demodulation,[status(thm)],[c_1096,c_20]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_4223,plain,
% 3.14/0.95      ( sK3(sK6,sK0(k1_funct_1(sK6,sK4),k2_relat_1(sK6))) = sK4
% 3.14/0.95      | sK0(k1_funct_1(sK6,sK4),k2_relat_1(sK6)) = k1_funct_1(sK6,sK4) ),
% 3.14/0.95      inference(superposition,[status(thm)],[c_3984,c_1159]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_10,plain,
% 3.14/0.95      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.14/0.95      | ~ v1_funct_1(X1)
% 3.14/0.95      | ~ v1_relat_1(X1)
% 3.14/0.95      | k1_funct_1(X1,sK3(X1,X0)) = X0 ),
% 3.14/0.95      inference(cnf_transformation,[],[f74]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_485,plain,
% 3.14/0.95      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.14/0.95      | ~ v1_relat_1(X1)
% 3.14/0.95      | k1_funct_1(X1,sK3(X1,X0)) = X0
% 3.14/0.95      | sK6 != X1 ),
% 3.14/0.95      inference(resolution_lifted,[status(thm)],[c_10,c_24]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_486,plain,
% 3.14/0.95      ( ~ r2_hidden(X0,k2_relat_1(sK6))
% 3.14/0.95      | ~ v1_relat_1(sK6)
% 3.14/0.95      | k1_funct_1(sK6,sK3(sK6,X0)) = X0 ),
% 3.14/0.95      inference(unflattening,[status(thm)],[c_485]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_943,plain,
% 3.14/0.95      ( k1_funct_1(sK6,sK3(sK6,X0)) = X0
% 3.14/0.95      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 3.14/0.95      | v1_relat_1(sK6) != iProver_top ),
% 3.14/0.95      inference(predicate_to_equality,[status(thm)],[c_486]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_487,plain,
% 3.14/0.95      ( k1_funct_1(sK6,sK3(sK6,X0)) = X0
% 3.14/0.95      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 3.14/0.95      | v1_relat_1(sK6) != iProver_top ),
% 3.14/0.95      inference(predicate_to_equality,[status(thm)],[c_486]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_1400,plain,
% 3.14/0.95      ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 3.14/0.95      | k1_funct_1(sK6,sK3(sK6,X0)) = X0 ),
% 3.14/0.95      inference(global_propositional_subsumption,
% 3.14/0.95                [status(thm)],
% 3.14/0.95                [c_943,c_487,c_1084,c_1184,c_1314]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_1401,plain,
% 3.14/0.95      ( k1_funct_1(sK6,sK3(sK6,X0)) = X0
% 3.14/0.95      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
% 3.14/0.95      inference(renaming,[status(thm)],[c_1400]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_1408,plain,
% 3.14/0.95      ( k1_enumset1(X0,X0,X0) = k2_relat_1(sK6)
% 3.14/0.95      | k1_funct_1(sK6,sK3(sK6,sK0(X0,k2_relat_1(sK6)))) = sK0(X0,k2_relat_1(sK6))
% 3.14/0.95      | sK0(X0,k2_relat_1(sK6)) = X0 ),
% 3.14/0.95      inference(superposition,[status(thm)],[c_951,c_1401]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_3448,plain,
% 3.14/0.95      ( k1_funct_1(sK6,sK3(sK6,sK0(k1_funct_1(sK6,sK4),k2_relat_1(sK6)))) = sK0(k1_funct_1(sK6,sK4),k2_relat_1(sK6))
% 3.14/0.95      | sK0(k1_funct_1(sK6,sK4),k2_relat_1(sK6)) = k1_funct_1(sK6,sK4) ),
% 3.14/0.95      inference(superposition,[status(thm)],[c_1408,c_1159]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_4208,plain,
% 3.14/0.95      ( k1_enumset1(k1_funct_1(sK6,sK4),k1_funct_1(sK6,sK4),k1_funct_1(sK6,sK4)) = k2_relat_1(sK6)
% 3.14/0.95      | sK0(k1_funct_1(sK6,sK4),k2_relat_1(sK6)) = k1_funct_1(sK6,sK4) ),
% 3.14/0.95      inference(superposition,[status(thm)],[c_3984,c_3448]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_4725,plain,
% 3.14/0.95      ( sK0(k1_funct_1(sK6,sK4),k2_relat_1(sK6)) = k1_funct_1(sK6,sK4) ),
% 3.14/0.95      inference(global_propositional_subsumption,
% 3.14/0.95                [status(thm)],
% 3.14/0.95                [c_4223,c_1159,c_4208]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_0,plain,
% 3.14/0.95      ( ~ r2_hidden(sK0(X0,X1),X1)
% 3.14/0.95      | k1_enumset1(X0,X0,X0) = X1
% 3.14/0.95      | sK0(X0,X1) != X0 ),
% 3.14/0.95      inference(cnf_transformation,[],[f62]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_952,plain,
% 3.14/0.95      ( k1_enumset1(X0,X0,X0) = X1
% 3.14/0.95      | sK0(X0,X1) != X0
% 3.14/0.95      | r2_hidden(sK0(X0,X1),X1) != iProver_top ),
% 3.14/0.95      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_4729,plain,
% 3.14/0.95      ( k1_enumset1(k1_funct_1(sK6,sK4),k1_funct_1(sK6,sK4),k1_funct_1(sK6,sK4)) = k2_relat_1(sK6)
% 3.14/0.95      | r2_hidden(sK0(k1_funct_1(sK6,sK4),k2_relat_1(sK6)),k2_relat_1(sK6)) != iProver_top ),
% 3.14/0.95      inference(superposition,[status(thm)],[c_4725,c_952]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_4735,plain,
% 3.14/0.95      ( k1_enumset1(k1_funct_1(sK6,sK4),k1_funct_1(sK6,sK4),k1_funct_1(sK6,sK4)) = k2_relat_1(sK6)
% 3.14/0.95      | r2_hidden(k1_funct_1(sK6,sK4),k2_relat_1(sK6)) != iProver_top ),
% 3.14/0.95      inference(light_normalisation,[status(thm)],[c_4729,c_4725]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_5520,plain,
% 3.14/0.95      ( r2_hidden(k1_funct_1(sK6,sK4),k2_relat_1(sK6)) != iProver_top ),
% 3.14/0.95      inference(global_propositional_subsumption,
% 3.14/0.95                [status(thm)],
% 3.14/0.95                [c_4735,c_1159]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_5526,plain,
% 3.14/0.95      ( r2_hidden(sK4,k1_relat_1(sK6)) != iProver_top ),
% 3.14/0.95      inference(superposition,[status(thm)],[c_1412,c_5520]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_2,plain,
% 3.14/0.95      ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) ),
% 3.14/0.95      inference(cnf_transformation,[],[f70]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_950,plain,
% 3.14/0.95      ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) = iProver_top ),
% 3.14/0.95      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(c_3214,plain,
% 3.14/0.95      ( r2_hidden(sK4,k1_relat_1(sK6)) = iProver_top ),
% 3.14/0.95      inference(superposition,[status(thm)],[c_1350,c_950]) ).
% 3.14/0.95  
% 3.14/0.95  cnf(contradiction,plain,
% 3.14/0.95      ( $false ),
% 3.14/0.95      inference(minisat,[status(thm)],[c_5526,c_3214]) ).
% 3.14/0.95  
% 3.14/0.95  
% 3.14/0.95  % SZS output end CNFRefutation for theBenchmark.p
% 3.14/0.95  
% 3.14/0.95  ------                               Statistics
% 3.14/0.95  
% 3.14/0.95  ------ General
% 3.14/0.95  
% 3.14/0.95  abstr_ref_over_cycles:                  0
% 3.14/0.95  abstr_ref_under_cycles:                 0
% 3.14/0.95  gc_basic_clause_elim:                   0
% 3.14/0.95  forced_gc_time:                         0
% 3.14/0.95  parsing_time:                           0.013
% 3.14/0.95  unif_index_cands_time:                  0.
% 3.14/0.95  unif_index_add_time:                    0.
% 3.14/0.95  orderings_time:                         0.
% 3.14/0.95  out_proof_time:                         0.011
% 3.14/0.95  total_time:                             0.192
% 3.14/0.95  num_of_symbols:                         52
% 3.14/0.95  num_of_terms:                           5417
% 3.14/0.95  
% 3.14/0.95  ------ Preprocessing
% 3.14/0.95  
% 3.14/0.95  num_of_splits:                          0
% 3.14/0.95  num_of_split_atoms:                     0
% 3.14/0.95  num_of_reused_defs:                     0
% 3.14/0.95  num_eq_ax_congr_red:                    22
% 3.14/0.95  num_of_sem_filtered_clauses:            1
% 3.14/0.95  num_of_subtypes:                        0
% 3.14/0.95  monotx_restored_types:                  0
% 3.14/0.95  sat_num_of_epr_types:                   0
% 3.14/0.95  sat_num_of_non_cyclic_types:            0
% 3.14/0.95  sat_guarded_non_collapsed_types:        0
% 3.14/0.95  num_pure_diseq_elim:                    0
% 3.14/0.95  simp_replaced_by:                       0
% 3.14/0.95  res_preprocessed:                       113
% 3.14/0.95  prep_upred:                             0
% 3.14/0.95  prep_unflattend:                        31
% 3.14/0.95  smt_new_axioms:                         0
% 3.14/0.95  pred_elim_cands:                        2
% 3.14/0.95  pred_elim:                              3
% 3.14/0.95  pred_elim_cl:                           6
% 3.14/0.95  pred_elim_cycles:                       5
% 3.14/0.95  merged_defs:                            0
% 3.14/0.95  merged_defs_ncl:                        0
% 3.14/0.95  bin_hyper_res:                          0
% 3.14/0.95  prep_cycles:                            4
% 3.14/0.95  pred_elim_time:                         0.008
% 3.14/0.95  splitting_time:                         0.
% 3.14/0.95  sem_filter_time:                        0.
% 3.14/0.95  monotx_time:                            0.
% 3.14/0.95  subtype_inf_time:                       0.
% 3.14/0.95  
% 3.14/0.95  ------ Problem properties
% 3.14/0.95  
% 3.14/0.95  clauses:                                19
% 3.14/0.95  conjectures:                            2
% 3.14/0.95  epr:                                    1
% 3.14/0.95  horn:                                   15
% 3.14/0.95  ground:                                 5
% 3.14/0.95  unary:                                  5
% 3.14/0.95  binary:                                 3
% 3.14/0.95  lits:                                   49
% 3.14/0.95  lits_eq:                                26
% 3.14/0.95  fd_pure:                                0
% 3.14/0.95  fd_pseudo:                              0
% 3.14/0.95  fd_cond:                                3
% 3.14/0.95  fd_pseudo_cond:                         2
% 3.14/0.95  ac_symbols:                             0
% 3.14/0.95  
% 3.14/0.95  ------ Propositional Solver
% 3.14/0.95  
% 3.14/0.95  prop_solver_calls:                      27
% 3.14/0.95  prop_fast_solver_calls:                 829
% 3.14/0.95  smt_solver_calls:                       0
% 3.14/0.95  smt_fast_solver_calls:                  0
% 3.14/0.95  prop_num_of_clauses:                    1931
% 3.14/0.95  prop_preprocess_simplified:             5040
% 3.14/0.95  prop_fo_subsumed:                       14
% 3.14/0.95  prop_solver_time:                       0.
% 3.14/0.95  smt_solver_time:                        0.
% 3.14/0.95  smt_fast_solver_time:                   0.
% 3.14/0.95  prop_fast_solver_time:                  0.
% 3.14/0.95  prop_unsat_core_time:                   0.
% 3.14/0.95  
% 3.14/0.95  ------ QBF
% 3.14/0.95  
% 3.14/0.95  qbf_q_res:                              0
% 3.14/0.95  qbf_num_tautologies:                    0
% 3.14/0.95  qbf_prep_cycles:                        0
% 3.14/0.95  
% 3.14/0.95  ------ BMC1
% 3.14/0.95  
% 3.14/0.95  bmc1_current_bound:                     -1
% 3.14/0.95  bmc1_last_solved_bound:                 -1
% 3.14/0.95  bmc1_unsat_core_size:                   -1
% 3.14/0.95  bmc1_unsat_core_parents_size:           -1
% 3.14/0.95  bmc1_merge_next_fun:                    0
% 3.14/0.95  bmc1_unsat_core_clauses_time:           0.
% 3.14/0.95  
% 3.14/0.95  ------ Instantiation
% 3.14/0.95  
% 3.14/0.95  inst_num_of_clauses:                    560
% 3.14/0.95  inst_num_in_passive:                    53
% 3.14/0.95  inst_num_in_active:                     257
% 3.14/0.95  inst_num_in_unprocessed:                250
% 3.14/0.95  inst_num_of_loops:                      290
% 3.14/0.95  inst_num_of_learning_restarts:          0
% 3.14/0.95  inst_num_moves_active_passive:          31
% 3.14/0.95  inst_lit_activity:                      0
% 3.14/0.95  inst_lit_activity_moves:                0
% 3.14/0.95  inst_num_tautologies:                   0
% 3.14/0.95  inst_num_prop_implied:                  0
% 3.14/0.95  inst_num_existing_simplified:           0
% 3.14/0.95  inst_num_eq_res_simplified:             0
% 3.14/0.95  inst_num_child_elim:                    0
% 3.14/0.95  inst_num_of_dismatching_blockings:      192
% 3.14/0.95  inst_num_of_non_proper_insts:           531
% 3.14/0.95  inst_num_of_duplicates:                 0
% 3.14/0.95  inst_inst_num_from_inst_to_res:         0
% 3.14/0.95  inst_dismatching_checking_time:         0.
% 3.14/0.95  
% 3.14/0.95  ------ Resolution
% 3.14/0.95  
% 3.14/0.95  res_num_of_clauses:                     0
% 3.14/0.95  res_num_in_passive:                     0
% 3.14/0.95  res_num_in_active:                      0
% 3.14/0.95  res_num_of_loops:                       117
% 3.14/0.95  res_forward_subset_subsumed:            62
% 3.14/0.95  res_backward_subset_subsumed:           0
% 3.14/0.95  res_forward_subsumed:                   0
% 3.14/0.95  res_backward_subsumed:                  0
% 3.14/0.95  res_forward_subsumption_resolution:     0
% 3.14/0.95  res_backward_subsumption_resolution:    0
% 3.14/0.95  res_clause_to_clause_subsumption:       786
% 3.14/0.95  res_orphan_elimination:                 0
% 3.14/0.95  res_tautology_del:                      41
% 3.14/0.95  res_num_eq_res_simplified:              1
% 3.14/0.95  res_num_sel_changes:                    0
% 3.14/0.95  res_moves_from_active_to_pass:          0
% 3.14/0.95  
% 3.14/0.95  ------ Superposition
% 3.14/0.95  
% 3.14/0.95  sup_time_total:                         0.
% 3.14/0.95  sup_time_generating:                    0.
% 3.14/0.95  sup_time_sim_full:                      0.
% 3.14/0.95  sup_time_sim_immed:                     0.
% 3.14/0.95  
% 3.14/0.95  sup_num_of_clauses:                     178
% 3.14/0.95  sup_num_in_active:                      45
% 3.14/0.95  sup_num_in_passive:                     133
% 3.14/0.95  sup_num_of_loops:                       56
% 3.14/0.95  sup_fw_superposition:                   98
% 3.14/0.95  sup_bw_superposition:                   122
% 3.14/0.95  sup_immediate_simplified:               27
% 3.14/0.95  sup_given_eliminated:                   0
% 3.14/0.95  comparisons_done:                       0
% 3.14/0.95  comparisons_avoided:                    33
% 3.14/0.95  
% 3.14/0.95  ------ Simplifications
% 3.14/0.95  
% 3.14/0.95  
% 3.14/0.95  sim_fw_subset_subsumed:                 9
% 3.14/0.95  sim_bw_subset_subsumed:                 1
% 3.14/0.95  sim_fw_subsumed:                        8
% 3.14/0.95  sim_bw_subsumed:                        0
% 3.14/0.95  sim_fw_subsumption_res:                 1
% 3.14/0.95  sim_bw_subsumption_res:                 0
% 3.14/0.95  sim_tautology_del:                      3
% 3.14/0.95  sim_eq_tautology_del:                   12
% 3.14/0.95  sim_eq_res_simp:                        0
% 3.14/0.95  sim_fw_demodulated:                     0
% 3.14/0.95  sim_bw_demodulated:                     12
% 3.14/0.95  sim_light_normalised:                   10
% 3.14/0.95  sim_joinable_taut:                      0
% 3.14/0.95  sim_joinable_simp:                      0
% 3.14/0.95  sim_ac_normalised:                      0
% 3.14/0.95  sim_smt_subsumption:                    0
% 3.14/0.95  
%------------------------------------------------------------------------------
