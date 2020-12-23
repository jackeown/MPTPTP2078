%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:14 EST 2020

% Result     : Theorem 7.77s
% Output     : CNFRefutation 7.77s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 252 expanded)
%              Number of clauses        :   57 (  62 expanded)
%              Number of leaves         :   23 (  60 expanded)
%              Depth                    :   14
%              Number of atoms          :  479 ( 894 expanded)
%              Number of equality atoms :  205 ( 363 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
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

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f43,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X5)) = X5
        & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1)) = X2
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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

fof(f44,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f40,f43,f42,f41])).

fof(f65,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f100,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f101,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f100])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f27])).

fof(f46,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( k1_funct_1(sK8,sK7) != sK6
      & r2_hidden(sK7,sK5)
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))
      & v1_funct_2(sK8,sK5,k1_tarski(sK6))
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( k1_funct_1(sK8,sK7) != sK6
    & r2_hidden(sK7,sK5)
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))
    & v1_funct_2(sK8,sK5,k1_tarski(sK6))
    & v1_funct_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f28,f46])).

fof(f80,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f47])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

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

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f81,plain,(
    v1_funct_2(sK8,sK5,k1_tarski(sK6)) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f85,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f59,f60])).

fof(f86,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f58,f85])).

fof(f94,plain,(
    v1_funct_2(sK8,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) ),
    inference(definition_unfolding,[],[f81,f86])).

fof(f82,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6)))) ),
    inference(cnf_transformation,[],[f47])).

fof(f93,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6)))) ),
    inference(definition_unfolding,[],[f82,f86])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f33])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK1(X0,X1,X2) != X1
            & sK1(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( sK1(X0,X1,X2) = X1
          | sK1(X0,X1,X2) = X0
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK1(X0,X1,X2) != X1
              & sK1(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( sK1(X0,X1,X2) = X1
            | sK1(X0,X1,X2) = X0
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f90,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f54,f85])).

fof(f95,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f90])).

fof(f96,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_enumset1(X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f95])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f92,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f52,f85])).

fof(f99,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f92])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f84,plain,(
    k1_funct_1(sK8,sK7) != sK6 ),
    inference(cnf_transformation,[],[f47])).

fof(f83,plain,(
    r2_hidden(sK7,sK5) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2271,plain,
    ( ~ r2_hidden(k1_funct_1(sK8,sK7),X0)
    | r2_hidden(k1_funct_1(sK8,sK7),X1)
    | ~ r1_tarski(X0,X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_7132,plain,
    ( r2_hidden(k1_funct_1(sK8,sK7),X0)
    | ~ r2_hidden(k1_funct_1(sK8,sK7),k2_relat_1(sK8))
    | ~ r1_tarski(k2_relat_1(sK8),X0) ),
    inference(instantiation,[status(thm)],[c_2271])).

cnf(c_14525,plain,
    ( r2_hidden(k1_funct_1(sK8,sK7),k2_enumset1(sK6,sK6,sK6,X0))
    | ~ r2_hidden(k1_funct_1(sK8,sK7),k2_relat_1(sK8))
    | ~ r1_tarski(k2_relat_1(sK8),k2_enumset1(sK6,sK6,sK6,X0)) ),
    inference(instantiation,[status(thm)],[c_7132])).

cnf(c_21955,plain,
    ( r2_hidden(k1_funct_1(sK8,sK7),k2_enumset1(sK6,sK6,sK6,sK6))
    | ~ r2_hidden(k1_funct_1(sK8,sK7),k2_relat_1(sK8))
    | ~ r1_tarski(k2_relat_1(sK8),k2_enumset1(sK6,sK6,sK6,sK6)) ),
    inference(instantiation,[status(thm)],[c_14525])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_505,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_33])).

cnf(c_506,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK8))
    | r2_hidden(k1_funct_1(sK8,X0),k2_relat_1(sK8))
    | ~ v1_relat_1(sK8) ),
    inference(unflattening,[status(thm)],[c_505])).

cnf(c_21318,plain,
    ( r2_hidden(k1_funct_1(sK8,sK7),k2_relat_1(sK8))
    | ~ r2_hidden(sK7,k1_relat_1(sK8))
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_506])).

cnf(c_1403,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3558,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK7,sK5)
    | X1 != sK5
    | X0 != sK7 ),
    inference(instantiation,[status(thm)],[c_1403])).

cnf(c_5863,plain,
    ( r2_hidden(sK7,X0)
    | ~ r2_hidden(sK7,sK5)
    | X0 != sK5
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_3558])).

cnf(c_10138,plain,
    ( r2_hidden(sK7,k1_relat_1(sK8))
    | ~ r2_hidden(sK7,sK5)
    | k1_relat_1(sK8) != sK5
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_5863])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2053,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK8,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_889,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_enumset1(sK6,sK6,sK6,sK6) != X2
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X1
    | sK8 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_32])).

cnf(c_890,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6))))
    | k1_relset_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK8) = sK5
    | k1_xboole_0 = k2_enumset1(sK6,sK6,sK6,sK6) ),
    inference(unflattening,[status(thm)],[c_889])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6)))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_892,plain,
    ( k1_relset_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK8) = sK5
    | k1_xboole_0 = k2_enumset1(sK6,sK6,sK6,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_890,c_31])).

cnf(c_2038,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2041,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4057,plain,
    ( k1_relset_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK8) = k1_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_2038,c_2041])).

cnf(c_4257,plain,
    ( k2_enumset1(sK6,sK6,sK6,sK6) = k1_xboole_0
    | k1_relat_1(sK8) = sK5 ),
    inference(superposition,[status(thm)],[c_892,c_4057])).

cnf(c_7,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2049,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2044,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2636,plain,
    ( r1_tarski(k2_enumset1(X0,X0,X0,X1),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2049,c_2044])).

cnf(c_4946,plain,
    ( k1_relat_1(sK8) = sK5
    | r1_tarski(k1_xboole_0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4257,c_2636])).

cnf(c_5141,plain,
    ( k1_relat_1(sK8) = sK5 ),
    inference(superposition,[status(thm)],[c_2053,c_4946])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2040,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3131,plain,
    ( k2_relset_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK8) = k2_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_2038,c_2040])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2042,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4176,plain,
    ( m1_subset_1(k2_relat_1(sK8),k1_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6))) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3131,c_2042])).

cnf(c_36,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_4538,plain,
    ( m1_subset_1(k2_relat_1(sK8),k1_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4176,c_36])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2045,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4543,plain,
    ( r1_tarski(k2_relat_1(sK8),k2_enumset1(sK6,sK6,sK6,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4538,c_2045])).

cnf(c_4545,plain,
    ( r1_tarski(k2_relat_1(sK8),k2_enumset1(sK6,sK6,sK6,sK6)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4543])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2094,plain,
    ( ~ r2_hidden(k1_funct_1(sK8,sK7),k2_enumset1(sK6,sK6,sK6,X0))
    | k1_funct_1(sK8,sK7) = X0
    | k1_funct_1(sK8,sK7) = sK6 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3752,plain,
    ( ~ r2_hidden(k1_funct_1(sK8,sK7),k2_enumset1(sK6,sK6,sK6,sK6))
    | k1_funct_1(sK8,sK7) = sK6 ),
    inference(instantiation,[status(thm)],[c_2094])).

cnf(c_1400,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3181,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_1400])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2118,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2233,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6))))
    | v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_2118])).

cnf(c_29,negated_conjecture,
    ( k1_funct_1(sK8,sK7) != sK6 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_30,negated_conjecture,
    ( r2_hidden(sK7,sK5) ),
    inference(cnf_transformation,[],[f83])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21955,c_21318,c_10138,c_5141,c_4545,c_3752,c_3181,c_2233,c_29,c_30,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:11:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 7.77/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.77/1.48  
% 7.77/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.77/1.48  
% 7.77/1.48  ------  iProver source info
% 7.77/1.48  
% 7.77/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.77/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.77/1.48  git: non_committed_changes: false
% 7.77/1.48  git: last_make_outside_of_git: false
% 7.77/1.48  
% 7.77/1.48  ------ 
% 7.77/1.48  
% 7.77/1.48  ------ Input Options
% 7.77/1.48  
% 7.77/1.48  --out_options                           all
% 7.77/1.48  --tptp_safe_out                         true
% 7.77/1.48  --problem_path                          ""
% 7.77/1.48  --include_path                          ""
% 7.77/1.48  --clausifier                            res/vclausify_rel
% 7.77/1.48  --clausifier_options                    ""
% 7.77/1.48  --stdin                                 false
% 7.77/1.48  --stats_out                             all
% 7.77/1.48  
% 7.77/1.48  ------ General Options
% 7.77/1.48  
% 7.77/1.48  --fof                                   false
% 7.77/1.48  --time_out_real                         305.
% 7.77/1.48  --time_out_virtual                      -1.
% 7.77/1.48  --symbol_type_check                     false
% 7.77/1.48  --clausify_out                          false
% 7.77/1.48  --sig_cnt_out                           false
% 7.77/1.48  --trig_cnt_out                          false
% 7.77/1.48  --trig_cnt_out_tolerance                1.
% 7.77/1.48  --trig_cnt_out_sk_spl                   false
% 7.77/1.48  --abstr_cl_out                          false
% 7.77/1.48  
% 7.77/1.48  ------ Global Options
% 7.77/1.48  
% 7.77/1.48  --schedule                              default
% 7.77/1.48  --add_important_lit                     false
% 7.77/1.48  --prop_solver_per_cl                    1000
% 7.77/1.48  --min_unsat_core                        false
% 7.77/1.48  --soft_assumptions                      false
% 7.77/1.48  --soft_lemma_size                       3
% 7.77/1.48  --prop_impl_unit_size                   0
% 7.77/1.48  --prop_impl_unit                        []
% 7.77/1.48  --share_sel_clauses                     true
% 7.77/1.48  --reset_solvers                         false
% 7.77/1.48  --bc_imp_inh                            [conj_cone]
% 7.77/1.48  --conj_cone_tolerance                   3.
% 7.77/1.48  --extra_neg_conj                        none
% 7.77/1.48  --large_theory_mode                     true
% 7.77/1.48  --prolific_symb_bound                   200
% 7.77/1.48  --lt_threshold                          2000
% 7.77/1.48  --clause_weak_htbl                      true
% 7.77/1.48  --gc_record_bc_elim                     false
% 7.77/1.48  
% 7.77/1.48  ------ Preprocessing Options
% 7.77/1.48  
% 7.77/1.48  --preprocessing_flag                    true
% 7.77/1.48  --time_out_prep_mult                    0.1
% 7.77/1.48  --splitting_mode                        input
% 7.77/1.48  --splitting_grd                         true
% 7.77/1.48  --splitting_cvd                         false
% 7.77/1.48  --splitting_cvd_svl                     false
% 7.77/1.48  --splitting_nvd                         32
% 7.77/1.48  --sub_typing                            true
% 7.77/1.48  --prep_gs_sim                           true
% 7.77/1.48  --prep_unflatten                        true
% 7.77/1.48  --prep_res_sim                          true
% 7.77/1.48  --prep_upred                            true
% 7.77/1.48  --prep_sem_filter                       exhaustive
% 7.77/1.48  --prep_sem_filter_out                   false
% 7.77/1.48  --pred_elim                             true
% 7.77/1.48  --res_sim_input                         true
% 7.77/1.48  --eq_ax_congr_red                       true
% 7.77/1.48  --pure_diseq_elim                       true
% 7.77/1.48  --brand_transform                       false
% 7.77/1.48  --non_eq_to_eq                          false
% 7.77/1.48  --prep_def_merge                        true
% 7.77/1.48  --prep_def_merge_prop_impl              false
% 7.77/1.48  --prep_def_merge_mbd                    true
% 7.77/1.48  --prep_def_merge_tr_red                 false
% 7.77/1.48  --prep_def_merge_tr_cl                  false
% 7.77/1.48  --smt_preprocessing                     true
% 7.77/1.48  --smt_ac_axioms                         fast
% 7.77/1.48  --preprocessed_out                      false
% 7.77/1.48  --preprocessed_stats                    false
% 7.77/1.48  
% 7.77/1.48  ------ Abstraction refinement Options
% 7.77/1.48  
% 7.77/1.48  --abstr_ref                             []
% 7.77/1.48  --abstr_ref_prep                        false
% 7.77/1.48  --abstr_ref_until_sat                   false
% 7.77/1.48  --abstr_ref_sig_restrict                funpre
% 7.77/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.77/1.48  --abstr_ref_under                       []
% 7.77/1.48  
% 7.77/1.48  ------ SAT Options
% 7.77/1.48  
% 7.77/1.48  --sat_mode                              false
% 7.77/1.48  --sat_fm_restart_options                ""
% 7.77/1.48  --sat_gr_def                            false
% 7.77/1.48  --sat_epr_types                         true
% 7.77/1.48  --sat_non_cyclic_types                  false
% 7.77/1.48  --sat_finite_models                     false
% 7.77/1.48  --sat_fm_lemmas                         false
% 7.77/1.48  --sat_fm_prep                           false
% 7.77/1.48  --sat_fm_uc_incr                        true
% 7.77/1.48  --sat_out_model                         small
% 7.77/1.48  --sat_out_clauses                       false
% 7.77/1.48  
% 7.77/1.48  ------ QBF Options
% 7.77/1.48  
% 7.77/1.48  --qbf_mode                              false
% 7.77/1.48  --qbf_elim_univ                         false
% 7.77/1.48  --qbf_dom_inst                          none
% 7.77/1.48  --qbf_dom_pre_inst                      false
% 7.77/1.48  --qbf_sk_in                             false
% 7.77/1.48  --qbf_pred_elim                         true
% 7.77/1.48  --qbf_split                             512
% 7.77/1.48  
% 7.77/1.48  ------ BMC1 Options
% 7.77/1.48  
% 7.77/1.48  --bmc1_incremental                      false
% 7.77/1.48  --bmc1_axioms                           reachable_all
% 7.77/1.48  --bmc1_min_bound                        0
% 7.77/1.48  --bmc1_max_bound                        -1
% 7.77/1.48  --bmc1_max_bound_default                -1
% 7.77/1.48  --bmc1_symbol_reachability              true
% 7.77/1.48  --bmc1_property_lemmas                  false
% 7.77/1.48  --bmc1_k_induction                      false
% 7.77/1.48  --bmc1_non_equiv_states                 false
% 7.77/1.48  --bmc1_deadlock                         false
% 7.77/1.48  --bmc1_ucm                              false
% 7.77/1.48  --bmc1_add_unsat_core                   none
% 7.77/1.48  --bmc1_unsat_core_children              false
% 7.77/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.77/1.48  --bmc1_out_stat                         full
% 7.77/1.48  --bmc1_ground_init                      false
% 7.77/1.48  --bmc1_pre_inst_next_state              false
% 7.77/1.48  --bmc1_pre_inst_state                   false
% 7.77/1.48  --bmc1_pre_inst_reach_state             false
% 7.77/1.48  --bmc1_out_unsat_core                   false
% 7.77/1.48  --bmc1_aig_witness_out                  false
% 7.77/1.48  --bmc1_verbose                          false
% 7.77/1.48  --bmc1_dump_clauses_tptp                false
% 7.77/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.77/1.48  --bmc1_dump_file                        -
% 7.77/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.77/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.77/1.48  --bmc1_ucm_extend_mode                  1
% 7.77/1.48  --bmc1_ucm_init_mode                    2
% 7.77/1.48  --bmc1_ucm_cone_mode                    none
% 7.77/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.77/1.48  --bmc1_ucm_relax_model                  4
% 7.77/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.77/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.77/1.48  --bmc1_ucm_layered_model                none
% 7.77/1.48  --bmc1_ucm_max_lemma_size               10
% 7.77/1.48  
% 7.77/1.48  ------ AIG Options
% 7.77/1.48  
% 7.77/1.48  --aig_mode                              false
% 7.77/1.48  
% 7.77/1.48  ------ Instantiation Options
% 7.77/1.48  
% 7.77/1.48  --instantiation_flag                    true
% 7.77/1.48  --inst_sos_flag                         true
% 7.77/1.48  --inst_sos_phase                        true
% 7.77/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.77/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.77/1.48  --inst_lit_sel_side                     num_symb
% 7.77/1.48  --inst_solver_per_active                1400
% 7.77/1.48  --inst_solver_calls_frac                1.
% 7.77/1.48  --inst_passive_queue_type               priority_queues
% 7.77/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.77/1.48  --inst_passive_queues_freq              [25;2]
% 7.77/1.48  --inst_dismatching                      true
% 7.77/1.48  --inst_eager_unprocessed_to_passive     true
% 7.77/1.48  --inst_prop_sim_given                   true
% 7.77/1.48  --inst_prop_sim_new                     false
% 7.77/1.48  --inst_subs_new                         false
% 7.77/1.48  --inst_eq_res_simp                      false
% 7.77/1.48  --inst_subs_given                       false
% 7.77/1.48  --inst_orphan_elimination               true
% 7.77/1.48  --inst_learning_loop_flag               true
% 7.77/1.48  --inst_learning_start                   3000
% 7.77/1.48  --inst_learning_factor                  2
% 7.77/1.48  --inst_start_prop_sim_after_learn       3
% 7.77/1.48  --inst_sel_renew                        solver
% 7.77/1.48  --inst_lit_activity_flag                true
% 7.77/1.48  --inst_restr_to_given                   false
% 7.77/1.48  --inst_activity_threshold               500
% 7.77/1.48  --inst_out_proof                        true
% 7.77/1.48  
% 7.77/1.48  ------ Resolution Options
% 7.77/1.48  
% 7.77/1.48  --resolution_flag                       true
% 7.77/1.48  --res_lit_sel                           adaptive
% 7.77/1.48  --res_lit_sel_side                      none
% 7.77/1.48  --res_ordering                          kbo
% 7.77/1.48  --res_to_prop_solver                    active
% 7.77/1.48  --res_prop_simpl_new                    false
% 7.77/1.48  --res_prop_simpl_given                  true
% 7.77/1.48  --res_passive_queue_type                priority_queues
% 7.77/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.77/1.48  --res_passive_queues_freq               [15;5]
% 7.77/1.48  --res_forward_subs                      full
% 7.77/1.48  --res_backward_subs                     full
% 7.77/1.48  --res_forward_subs_resolution           true
% 7.77/1.48  --res_backward_subs_resolution          true
% 7.77/1.48  --res_orphan_elimination                true
% 7.77/1.48  --res_time_limit                        2.
% 7.77/1.48  --res_out_proof                         true
% 7.77/1.48  
% 7.77/1.48  ------ Superposition Options
% 7.77/1.48  
% 7.77/1.48  --superposition_flag                    true
% 7.77/1.48  --sup_passive_queue_type                priority_queues
% 7.77/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.77/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.77/1.48  --demod_completeness_check              fast
% 7.77/1.48  --demod_use_ground                      true
% 7.77/1.48  --sup_to_prop_solver                    passive
% 7.77/1.48  --sup_prop_simpl_new                    true
% 7.77/1.48  --sup_prop_simpl_given                  true
% 7.77/1.48  --sup_fun_splitting                     true
% 7.77/1.48  --sup_smt_interval                      50000
% 7.77/1.48  
% 7.77/1.48  ------ Superposition Simplification Setup
% 7.77/1.48  
% 7.77/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.77/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.77/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.77/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.77/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.77/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.77/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.77/1.48  --sup_immed_triv                        [TrivRules]
% 7.77/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.77/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.77/1.48  --sup_immed_bw_main                     []
% 7.77/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.77/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.77/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.77/1.48  --sup_input_bw                          []
% 7.77/1.48  
% 7.77/1.48  ------ Combination Options
% 7.77/1.48  
% 7.77/1.48  --comb_res_mult                         3
% 7.77/1.48  --comb_sup_mult                         2
% 7.77/1.48  --comb_inst_mult                        10
% 7.77/1.48  
% 7.77/1.48  ------ Debug Options
% 7.77/1.48  
% 7.77/1.48  --dbg_backtrace                         false
% 7.77/1.48  --dbg_dump_prop_clauses                 false
% 7.77/1.48  --dbg_dump_prop_clauses_file            -
% 7.77/1.48  --dbg_out_stat                          false
% 7.77/1.48  ------ Parsing...
% 7.77/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.77/1.48  
% 7.77/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.77/1.48  
% 7.77/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.77/1.48  
% 7.77/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.77/1.48  ------ Proving...
% 7.77/1.48  ------ Problem Properties 
% 7.77/1.48  
% 7.77/1.48  
% 7.77/1.48  clauses                                 29
% 7.77/1.48  conjectures                             3
% 7.77/1.48  EPR                                     4
% 7.77/1.48  Horn                                    22
% 7.77/1.48  unary                                   6
% 7.77/1.48  binary                                  10
% 7.77/1.48  lits                                    71
% 7.77/1.48  lits eq                                 25
% 7.77/1.48  fd_pure                                 0
% 7.77/1.48  fd_pseudo                               0
% 7.77/1.48  fd_cond                                 3
% 7.77/1.48  fd_pseudo_cond                          3
% 7.77/1.48  AC symbols                              0
% 7.77/1.48  
% 7.77/1.48  ------ Schedule dynamic 5 is on 
% 7.77/1.48  
% 7.77/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.77/1.48  
% 7.77/1.48  
% 7.77/1.48  ------ 
% 7.77/1.48  Current options:
% 7.77/1.48  ------ 
% 7.77/1.48  
% 7.77/1.48  ------ Input Options
% 7.77/1.48  
% 7.77/1.48  --out_options                           all
% 7.77/1.48  --tptp_safe_out                         true
% 7.77/1.48  --problem_path                          ""
% 7.77/1.48  --include_path                          ""
% 7.77/1.48  --clausifier                            res/vclausify_rel
% 7.77/1.48  --clausifier_options                    ""
% 7.77/1.48  --stdin                                 false
% 7.77/1.48  --stats_out                             all
% 7.77/1.48  
% 7.77/1.48  ------ General Options
% 7.77/1.48  
% 7.77/1.48  --fof                                   false
% 7.77/1.48  --time_out_real                         305.
% 7.77/1.48  --time_out_virtual                      -1.
% 7.77/1.48  --symbol_type_check                     false
% 7.77/1.48  --clausify_out                          false
% 7.77/1.48  --sig_cnt_out                           false
% 7.77/1.48  --trig_cnt_out                          false
% 7.77/1.48  --trig_cnt_out_tolerance                1.
% 7.77/1.48  --trig_cnt_out_sk_spl                   false
% 7.77/1.48  --abstr_cl_out                          false
% 7.77/1.48  
% 7.77/1.48  ------ Global Options
% 7.77/1.48  
% 7.77/1.48  --schedule                              default
% 7.77/1.48  --add_important_lit                     false
% 7.77/1.48  --prop_solver_per_cl                    1000
% 7.77/1.48  --min_unsat_core                        false
% 7.77/1.48  --soft_assumptions                      false
% 7.77/1.48  --soft_lemma_size                       3
% 7.77/1.48  --prop_impl_unit_size                   0
% 7.77/1.48  --prop_impl_unit                        []
% 7.77/1.48  --share_sel_clauses                     true
% 7.77/1.48  --reset_solvers                         false
% 7.77/1.48  --bc_imp_inh                            [conj_cone]
% 7.77/1.48  --conj_cone_tolerance                   3.
% 7.77/1.48  --extra_neg_conj                        none
% 7.77/1.48  --large_theory_mode                     true
% 7.77/1.48  --prolific_symb_bound                   200
% 7.77/1.48  --lt_threshold                          2000
% 7.77/1.48  --clause_weak_htbl                      true
% 7.77/1.48  --gc_record_bc_elim                     false
% 7.77/1.48  
% 7.77/1.48  ------ Preprocessing Options
% 7.77/1.48  
% 7.77/1.48  --preprocessing_flag                    true
% 7.77/1.48  --time_out_prep_mult                    0.1
% 7.77/1.48  --splitting_mode                        input
% 7.77/1.48  --splitting_grd                         true
% 7.77/1.48  --splitting_cvd                         false
% 7.77/1.48  --splitting_cvd_svl                     false
% 7.77/1.48  --splitting_nvd                         32
% 7.77/1.48  --sub_typing                            true
% 7.77/1.48  --prep_gs_sim                           true
% 7.77/1.48  --prep_unflatten                        true
% 7.77/1.48  --prep_res_sim                          true
% 7.77/1.48  --prep_upred                            true
% 7.77/1.48  --prep_sem_filter                       exhaustive
% 7.77/1.48  --prep_sem_filter_out                   false
% 7.77/1.48  --pred_elim                             true
% 7.77/1.48  --res_sim_input                         true
% 7.77/1.48  --eq_ax_congr_red                       true
% 7.77/1.48  --pure_diseq_elim                       true
% 7.77/1.48  --brand_transform                       false
% 7.77/1.48  --non_eq_to_eq                          false
% 7.77/1.48  --prep_def_merge                        true
% 7.77/1.48  --prep_def_merge_prop_impl              false
% 7.77/1.48  --prep_def_merge_mbd                    true
% 7.77/1.48  --prep_def_merge_tr_red                 false
% 7.77/1.48  --prep_def_merge_tr_cl                  false
% 7.77/1.48  --smt_preprocessing                     true
% 7.77/1.48  --smt_ac_axioms                         fast
% 7.77/1.48  --preprocessed_out                      false
% 7.77/1.48  --preprocessed_stats                    false
% 7.77/1.48  
% 7.77/1.48  ------ Abstraction refinement Options
% 7.77/1.48  
% 7.77/1.48  --abstr_ref                             []
% 7.77/1.48  --abstr_ref_prep                        false
% 7.77/1.48  --abstr_ref_until_sat                   false
% 7.77/1.48  --abstr_ref_sig_restrict                funpre
% 7.77/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.77/1.48  --abstr_ref_under                       []
% 7.77/1.48  
% 7.77/1.48  ------ SAT Options
% 7.77/1.48  
% 7.77/1.48  --sat_mode                              false
% 7.77/1.48  --sat_fm_restart_options                ""
% 7.77/1.48  --sat_gr_def                            false
% 7.77/1.48  --sat_epr_types                         true
% 7.77/1.48  --sat_non_cyclic_types                  false
% 7.77/1.48  --sat_finite_models                     false
% 7.77/1.48  --sat_fm_lemmas                         false
% 7.77/1.48  --sat_fm_prep                           false
% 7.77/1.48  --sat_fm_uc_incr                        true
% 7.77/1.48  --sat_out_model                         small
% 7.77/1.48  --sat_out_clauses                       false
% 7.77/1.48  
% 7.77/1.48  ------ QBF Options
% 7.77/1.48  
% 7.77/1.48  --qbf_mode                              false
% 7.77/1.48  --qbf_elim_univ                         false
% 7.77/1.48  --qbf_dom_inst                          none
% 7.77/1.48  --qbf_dom_pre_inst                      false
% 7.77/1.48  --qbf_sk_in                             false
% 7.77/1.48  --qbf_pred_elim                         true
% 7.77/1.48  --qbf_split                             512
% 7.77/1.48  
% 7.77/1.48  ------ BMC1 Options
% 7.77/1.48  
% 7.77/1.48  --bmc1_incremental                      false
% 7.77/1.48  --bmc1_axioms                           reachable_all
% 7.77/1.48  --bmc1_min_bound                        0
% 7.77/1.48  --bmc1_max_bound                        -1
% 7.77/1.48  --bmc1_max_bound_default                -1
% 7.77/1.48  --bmc1_symbol_reachability              true
% 7.77/1.48  --bmc1_property_lemmas                  false
% 7.77/1.48  --bmc1_k_induction                      false
% 7.77/1.48  --bmc1_non_equiv_states                 false
% 7.77/1.48  --bmc1_deadlock                         false
% 7.77/1.48  --bmc1_ucm                              false
% 7.77/1.48  --bmc1_add_unsat_core                   none
% 7.77/1.48  --bmc1_unsat_core_children              false
% 7.77/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.77/1.48  --bmc1_out_stat                         full
% 7.77/1.48  --bmc1_ground_init                      false
% 7.77/1.48  --bmc1_pre_inst_next_state              false
% 7.77/1.48  --bmc1_pre_inst_state                   false
% 7.77/1.48  --bmc1_pre_inst_reach_state             false
% 7.77/1.48  --bmc1_out_unsat_core                   false
% 7.77/1.48  --bmc1_aig_witness_out                  false
% 7.77/1.48  --bmc1_verbose                          false
% 7.77/1.48  --bmc1_dump_clauses_tptp                false
% 7.77/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.77/1.48  --bmc1_dump_file                        -
% 7.77/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.77/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.77/1.48  --bmc1_ucm_extend_mode                  1
% 7.77/1.48  --bmc1_ucm_init_mode                    2
% 7.77/1.48  --bmc1_ucm_cone_mode                    none
% 7.77/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.77/1.48  --bmc1_ucm_relax_model                  4
% 7.77/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.77/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.77/1.48  --bmc1_ucm_layered_model                none
% 7.77/1.48  --bmc1_ucm_max_lemma_size               10
% 7.77/1.48  
% 7.77/1.48  ------ AIG Options
% 7.77/1.48  
% 7.77/1.48  --aig_mode                              false
% 7.77/1.48  
% 7.77/1.48  ------ Instantiation Options
% 7.77/1.48  
% 7.77/1.48  --instantiation_flag                    true
% 7.77/1.48  --inst_sos_flag                         true
% 7.77/1.48  --inst_sos_phase                        true
% 7.77/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.77/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.77/1.48  --inst_lit_sel_side                     none
% 7.77/1.48  --inst_solver_per_active                1400
% 7.77/1.48  --inst_solver_calls_frac                1.
% 7.77/1.48  --inst_passive_queue_type               priority_queues
% 7.77/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.77/1.48  --inst_passive_queues_freq              [25;2]
% 7.77/1.48  --inst_dismatching                      true
% 7.77/1.48  --inst_eager_unprocessed_to_passive     true
% 7.77/1.48  --inst_prop_sim_given                   true
% 7.77/1.48  --inst_prop_sim_new                     false
% 7.77/1.48  --inst_subs_new                         false
% 7.77/1.48  --inst_eq_res_simp                      false
% 7.77/1.48  --inst_subs_given                       false
% 7.77/1.48  --inst_orphan_elimination               true
% 7.77/1.48  --inst_learning_loop_flag               true
% 7.77/1.48  --inst_learning_start                   3000
% 7.77/1.48  --inst_learning_factor                  2
% 7.77/1.48  --inst_start_prop_sim_after_learn       3
% 7.77/1.48  --inst_sel_renew                        solver
% 7.77/1.48  --inst_lit_activity_flag                true
% 7.77/1.48  --inst_restr_to_given                   false
% 7.77/1.48  --inst_activity_threshold               500
% 7.77/1.48  --inst_out_proof                        true
% 7.77/1.48  
% 7.77/1.48  ------ Resolution Options
% 7.77/1.48  
% 7.77/1.48  --resolution_flag                       false
% 7.77/1.48  --res_lit_sel                           adaptive
% 7.77/1.48  --res_lit_sel_side                      none
% 7.77/1.48  --res_ordering                          kbo
% 7.77/1.48  --res_to_prop_solver                    active
% 7.77/1.48  --res_prop_simpl_new                    false
% 7.77/1.48  --res_prop_simpl_given                  true
% 7.77/1.48  --res_passive_queue_type                priority_queues
% 7.77/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.77/1.48  --res_passive_queues_freq               [15;5]
% 7.77/1.48  --res_forward_subs                      full
% 7.77/1.48  --res_backward_subs                     full
% 7.77/1.48  --res_forward_subs_resolution           true
% 7.77/1.48  --res_backward_subs_resolution          true
% 7.77/1.48  --res_orphan_elimination                true
% 7.77/1.48  --res_time_limit                        2.
% 7.77/1.48  --res_out_proof                         true
% 7.77/1.48  
% 7.77/1.48  ------ Superposition Options
% 7.77/1.48  
% 7.77/1.48  --superposition_flag                    true
% 7.77/1.48  --sup_passive_queue_type                priority_queues
% 7.77/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.77/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.77/1.48  --demod_completeness_check              fast
% 7.77/1.48  --demod_use_ground                      true
% 7.77/1.48  --sup_to_prop_solver                    passive
% 7.77/1.48  --sup_prop_simpl_new                    true
% 7.77/1.48  --sup_prop_simpl_given                  true
% 7.77/1.48  --sup_fun_splitting                     true
% 7.77/1.48  --sup_smt_interval                      50000
% 7.77/1.48  
% 7.77/1.48  ------ Superposition Simplification Setup
% 7.77/1.48  
% 7.77/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.77/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.77/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.77/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.77/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.77/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.77/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.77/1.48  --sup_immed_triv                        [TrivRules]
% 7.77/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.77/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.77/1.48  --sup_immed_bw_main                     []
% 7.77/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.77/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.77/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.77/1.48  --sup_input_bw                          []
% 7.77/1.48  
% 7.77/1.48  ------ Combination Options
% 7.77/1.48  
% 7.77/1.48  --comb_res_mult                         3
% 7.77/1.48  --comb_sup_mult                         2
% 7.77/1.48  --comb_inst_mult                        10
% 7.77/1.48  
% 7.77/1.48  ------ Debug Options
% 7.77/1.48  
% 7.77/1.48  --dbg_backtrace                         false
% 7.77/1.48  --dbg_dump_prop_clauses                 false
% 7.77/1.48  --dbg_dump_prop_clauses_file            -
% 7.77/1.48  --dbg_out_stat                          false
% 7.77/1.48  
% 7.77/1.48  
% 7.77/1.48  
% 7.77/1.48  
% 7.77/1.48  ------ Proving...
% 7.77/1.48  
% 7.77/1.48  
% 7.77/1.48  % SZS status Theorem for theBenchmark.p
% 7.77/1.48  
% 7.77/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.77/1.48  
% 7.77/1.48  fof(f1,axiom,(
% 7.77/1.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f17,plain,(
% 7.77/1.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.77/1.48    inference(ennf_transformation,[],[f1])).
% 7.77/1.48  
% 7.77/1.48  fof(f29,plain,(
% 7.77/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.77/1.48    inference(nnf_transformation,[],[f17])).
% 7.77/1.48  
% 7.77/1.48  fof(f30,plain,(
% 7.77/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.77/1.48    inference(rectify,[],[f29])).
% 7.77/1.48  
% 7.77/1.48  fof(f31,plain,(
% 7.77/1.48    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.77/1.48    introduced(choice_axiom,[])).
% 7.77/1.48  
% 7.77/1.48  fof(f32,plain,(
% 7.77/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.77/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 7.77/1.48  
% 7.77/1.48  fof(f48,plain,(
% 7.77/1.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f32])).
% 7.77/1.48  
% 7.77/1.48  fof(f8,axiom,(
% 7.77/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f18,plain,(
% 7.77/1.48    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.77/1.48    inference(ennf_transformation,[],[f8])).
% 7.77/1.48  
% 7.77/1.48  fof(f19,plain,(
% 7.77/1.48    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.77/1.48    inference(flattening,[],[f18])).
% 7.77/1.48  
% 7.77/1.48  fof(f39,plain,(
% 7.77/1.48    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.77/1.48    inference(nnf_transformation,[],[f19])).
% 7.77/1.48  
% 7.77/1.48  fof(f40,plain,(
% 7.77/1.48    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.77/1.48    inference(rectify,[],[f39])).
% 7.77/1.48  
% 7.77/1.48  fof(f43,plain,(
% 7.77/1.48    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))))),
% 7.77/1.48    introduced(choice_axiom,[])).
% 7.77/1.48  
% 7.77/1.48  fof(f42,plain,(
% 7.77/1.48    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1)) = X2 & r2_hidden(sK3(X0,X1),k1_relat_1(X0))))) )),
% 7.77/1.48    introduced(choice_axiom,[])).
% 7.77/1.48  
% 7.77/1.48  fof(f41,plain,(
% 7.77/1.48    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK2(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1))))),
% 7.77/1.48    introduced(choice_axiom,[])).
% 7.77/1.48  
% 7.77/1.48  fof(f44,plain,(
% 7.77/1.48    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & ((k1_funct_1(X0,sK3(X0,X1)) = sK2(X0,X1) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.77/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f40,f43,f42,f41])).
% 7.77/1.48  
% 7.77/1.48  fof(f65,plain,(
% 7.77/1.48    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f44])).
% 7.77/1.48  
% 7.77/1.48  fof(f100,plain,(
% 7.77/1.48    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.77/1.48    inference(equality_resolution,[],[f65])).
% 7.77/1.48  
% 7.77/1.48  fof(f101,plain,(
% 7.77/1.48    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.77/1.48    inference(equality_resolution,[],[f100])).
% 7.77/1.48  
% 7.77/1.48  fof(f15,conjecture,(
% 7.77/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f16,negated_conjecture,(
% 7.77/1.48    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 7.77/1.48    inference(negated_conjecture,[],[f15])).
% 7.77/1.48  
% 7.77/1.48  fof(f27,plain,(
% 7.77/1.48    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 7.77/1.48    inference(ennf_transformation,[],[f16])).
% 7.77/1.48  
% 7.77/1.48  fof(f28,plain,(
% 7.77/1.48    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 7.77/1.48    inference(flattening,[],[f27])).
% 7.77/1.48  
% 7.77/1.48  fof(f46,plain,(
% 7.77/1.48    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (k1_funct_1(sK8,sK7) != sK6 & r2_hidden(sK7,sK5) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6)))) & v1_funct_2(sK8,sK5,k1_tarski(sK6)) & v1_funct_1(sK8))),
% 7.77/1.48    introduced(choice_axiom,[])).
% 7.77/1.48  
% 7.77/1.48  fof(f47,plain,(
% 7.77/1.48    k1_funct_1(sK8,sK7) != sK6 & r2_hidden(sK7,sK5) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6)))) & v1_funct_2(sK8,sK5,k1_tarski(sK6)) & v1_funct_1(sK8)),
% 7.77/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f28,f46])).
% 7.77/1.48  
% 7.77/1.48  fof(f80,plain,(
% 7.77/1.48    v1_funct_1(sK8)),
% 7.77/1.48    inference(cnf_transformation,[],[f47])).
% 7.77/1.48  
% 7.77/1.48  fof(f2,axiom,(
% 7.77/1.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f51,plain,(
% 7.77/1.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f2])).
% 7.77/1.48  
% 7.77/1.48  fof(f14,axiom,(
% 7.77/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f25,plain,(
% 7.77/1.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.77/1.48    inference(ennf_transformation,[],[f14])).
% 7.77/1.48  
% 7.77/1.48  fof(f26,plain,(
% 7.77/1.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.77/1.48    inference(flattening,[],[f25])).
% 7.77/1.48  
% 7.77/1.48  fof(f45,plain,(
% 7.77/1.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.77/1.48    inference(nnf_transformation,[],[f26])).
% 7.77/1.48  
% 7.77/1.48  fof(f74,plain,(
% 7.77/1.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.77/1.48    inference(cnf_transformation,[],[f45])).
% 7.77/1.48  
% 7.77/1.48  fof(f81,plain,(
% 7.77/1.48    v1_funct_2(sK8,sK5,k1_tarski(sK6))),
% 7.77/1.48    inference(cnf_transformation,[],[f47])).
% 7.77/1.48  
% 7.77/1.48  fof(f4,axiom,(
% 7.77/1.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f58,plain,(
% 7.77/1.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f4])).
% 7.77/1.48  
% 7.77/1.48  fof(f5,axiom,(
% 7.77/1.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f59,plain,(
% 7.77/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f5])).
% 7.77/1.48  
% 7.77/1.48  fof(f6,axiom,(
% 7.77/1.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f60,plain,(
% 7.77/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f6])).
% 7.77/1.48  
% 7.77/1.48  fof(f85,plain,(
% 7.77/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.77/1.48    inference(definition_unfolding,[],[f59,f60])).
% 7.77/1.48  
% 7.77/1.48  fof(f86,plain,(
% 7.77/1.48    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 7.77/1.48    inference(definition_unfolding,[],[f58,f85])).
% 7.77/1.48  
% 7.77/1.48  fof(f94,plain,(
% 7.77/1.48    v1_funct_2(sK8,sK5,k2_enumset1(sK6,sK6,sK6,sK6))),
% 7.77/1.48    inference(definition_unfolding,[],[f81,f86])).
% 7.77/1.48  
% 7.77/1.48  fof(f82,plain,(
% 7.77/1.48    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))),
% 7.77/1.48    inference(cnf_transformation,[],[f47])).
% 7.77/1.48  
% 7.77/1.48  fof(f93,plain,(
% 7.77/1.48    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6))))),
% 7.77/1.48    inference(definition_unfolding,[],[f82,f86])).
% 7.77/1.48  
% 7.77/1.48  fof(f12,axiom,(
% 7.77/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f23,plain,(
% 7.77/1.48    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.77/1.48    inference(ennf_transformation,[],[f12])).
% 7.77/1.48  
% 7.77/1.48  fof(f72,plain,(
% 7.77/1.48    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.77/1.48    inference(cnf_transformation,[],[f23])).
% 7.77/1.48  
% 7.77/1.48  fof(f3,axiom,(
% 7.77/1.48    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f33,plain,(
% 7.77/1.48    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.77/1.48    inference(nnf_transformation,[],[f3])).
% 7.77/1.48  
% 7.77/1.48  fof(f34,plain,(
% 7.77/1.48    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.77/1.48    inference(flattening,[],[f33])).
% 7.77/1.48  
% 7.77/1.48  fof(f35,plain,(
% 7.77/1.48    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.77/1.48    inference(rectify,[],[f34])).
% 7.77/1.48  
% 7.77/1.48  fof(f36,plain,(
% 7.77/1.48    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 7.77/1.48    introduced(choice_axiom,[])).
% 7.77/1.48  
% 7.77/1.48  fof(f37,plain,(
% 7.77/1.48    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.77/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).
% 7.77/1.48  
% 7.77/1.48  fof(f54,plain,(
% 7.77/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 7.77/1.48    inference(cnf_transformation,[],[f37])).
% 7.77/1.48  
% 7.77/1.48  fof(f90,plain,(
% 7.77/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 7.77/1.48    inference(definition_unfolding,[],[f54,f85])).
% 7.77/1.48  
% 7.77/1.48  fof(f95,plain,(
% 7.77/1.48    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X4) != X2) )),
% 7.77/1.48    inference(equality_resolution,[],[f90])).
% 7.77/1.48  
% 7.77/1.48  fof(f96,plain,(
% 7.77/1.48    ( ! [X4,X0] : (r2_hidden(X4,k2_enumset1(X0,X0,X0,X4))) )),
% 7.77/1.48    inference(equality_resolution,[],[f95])).
% 7.77/1.48  
% 7.77/1.48  fof(f9,axiom,(
% 7.77/1.48    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f20,plain,(
% 7.77/1.48    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 7.77/1.48    inference(ennf_transformation,[],[f9])).
% 7.77/1.48  
% 7.77/1.48  fof(f69,plain,(
% 7.77/1.48    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f20])).
% 7.77/1.48  
% 7.77/1.48  fof(f13,axiom,(
% 7.77/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f24,plain,(
% 7.77/1.48    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.77/1.48    inference(ennf_transformation,[],[f13])).
% 7.77/1.48  
% 7.77/1.48  fof(f73,plain,(
% 7.77/1.48    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.77/1.48    inference(cnf_transformation,[],[f24])).
% 7.77/1.48  
% 7.77/1.48  fof(f11,axiom,(
% 7.77/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f22,plain,(
% 7.77/1.48    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.77/1.48    inference(ennf_transformation,[],[f11])).
% 7.77/1.48  
% 7.77/1.48  fof(f71,plain,(
% 7.77/1.48    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.77/1.48    inference(cnf_transformation,[],[f22])).
% 7.77/1.48  
% 7.77/1.48  fof(f7,axiom,(
% 7.77/1.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f38,plain,(
% 7.77/1.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.77/1.48    inference(nnf_transformation,[],[f7])).
% 7.77/1.48  
% 7.77/1.48  fof(f61,plain,(
% 7.77/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.77/1.48    inference(cnf_transformation,[],[f38])).
% 7.77/1.48  
% 7.77/1.48  fof(f52,plain,(
% 7.77/1.48    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 7.77/1.48    inference(cnf_transformation,[],[f37])).
% 7.77/1.48  
% 7.77/1.48  fof(f92,plain,(
% 7.77/1.48    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 7.77/1.48    inference(definition_unfolding,[],[f52,f85])).
% 7.77/1.48  
% 7.77/1.48  fof(f99,plain,(
% 7.77/1.48    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))) )),
% 7.77/1.48    inference(equality_resolution,[],[f92])).
% 7.77/1.48  
% 7.77/1.48  fof(f10,axiom,(
% 7.77/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f21,plain,(
% 7.77/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.77/1.48    inference(ennf_transformation,[],[f10])).
% 7.77/1.48  
% 7.77/1.48  fof(f70,plain,(
% 7.77/1.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.77/1.48    inference(cnf_transformation,[],[f21])).
% 7.77/1.48  
% 7.77/1.48  fof(f84,plain,(
% 7.77/1.48    k1_funct_1(sK8,sK7) != sK6),
% 7.77/1.48    inference(cnf_transformation,[],[f47])).
% 7.77/1.48  
% 7.77/1.48  fof(f83,plain,(
% 7.77/1.48    r2_hidden(sK7,sK5)),
% 7.77/1.48    inference(cnf_transformation,[],[f47])).
% 7.77/1.48  
% 7.77/1.48  cnf(c_2,plain,
% 7.77/1.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.77/1.48      inference(cnf_transformation,[],[f48]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_2271,plain,
% 7.77/1.48      ( ~ r2_hidden(k1_funct_1(sK8,sK7),X0)
% 7.77/1.48      | r2_hidden(k1_funct_1(sK8,sK7),X1)
% 7.77/1.48      | ~ r1_tarski(X0,X1) ),
% 7.77/1.48      inference(instantiation,[status(thm)],[c_2]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_7132,plain,
% 7.77/1.48      ( r2_hidden(k1_funct_1(sK8,sK7),X0)
% 7.77/1.48      | ~ r2_hidden(k1_funct_1(sK8,sK7),k2_relat_1(sK8))
% 7.77/1.48      | ~ r1_tarski(k2_relat_1(sK8),X0) ),
% 7.77/1.48      inference(instantiation,[status(thm)],[c_2271]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_14525,plain,
% 7.77/1.48      ( r2_hidden(k1_funct_1(sK8,sK7),k2_enumset1(sK6,sK6,sK6,X0))
% 7.77/1.48      | ~ r2_hidden(k1_funct_1(sK8,sK7),k2_relat_1(sK8))
% 7.77/1.48      | ~ r1_tarski(k2_relat_1(sK8),k2_enumset1(sK6,sK6,sK6,X0)) ),
% 7.77/1.48      inference(instantiation,[status(thm)],[c_7132]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_21955,plain,
% 7.77/1.48      ( r2_hidden(k1_funct_1(sK8,sK7),k2_enumset1(sK6,sK6,sK6,sK6))
% 7.77/1.48      | ~ r2_hidden(k1_funct_1(sK8,sK7),k2_relat_1(sK8))
% 7.77/1.48      | ~ r1_tarski(k2_relat_1(sK8),k2_enumset1(sK6,sK6,sK6,sK6)) ),
% 7.77/1.48      inference(instantiation,[status(thm)],[c_14525]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_15,plain,
% 7.77/1.48      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.77/1.48      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 7.77/1.48      | ~ v1_relat_1(X1)
% 7.77/1.48      | ~ v1_funct_1(X1) ),
% 7.77/1.48      inference(cnf_transformation,[],[f101]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_33,negated_conjecture,
% 7.77/1.48      ( v1_funct_1(sK8) ),
% 7.77/1.48      inference(cnf_transformation,[],[f80]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_505,plain,
% 7.77/1.48      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.77/1.48      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 7.77/1.48      | ~ v1_relat_1(X1)
% 7.77/1.48      | sK8 != X1 ),
% 7.77/1.48      inference(resolution_lifted,[status(thm)],[c_15,c_33]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_506,plain,
% 7.77/1.48      ( ~ r2_hidden(X0,k1_relat_1(sK8))
% 7.77/1.48      | r2_hidden(k1_funct_1(sK8,X0),k2_relat_1(sK8))
% 7.77/1.48      | ~ v1_relat_1(sK8) ),
% 7.77/1.48      inference(unflattening,[status(thm)],[c_505]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_21318,plain,
% 7.77/1.48      ( r2_hidden(k1_funct_1(sK8,sK7),k2_relat_1(sK8))
% 7.77/1.48      | ~ r2_hidden(sK7,k1_relat_1(sK8))
% 7.77/1.48      | ~ v1_relat_1(sK8) ),
% 7.77/1.48      inference(instantiation,[status(thm)],[c_506]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1403,plain,
% 7.77/1.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.77/1.48      theory(equality) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_3558,plain,
% 7.77/1.48      ( r2_hidden(X0,X1) | ~ r2_hidden(sK7,sK5) | X1 != sK5 | X0 != sK7 ),
% 7.77/1.48      inference(instantiation,[status(thm)],[c_1403]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_5863,plain,
% 7.77/1.48      ( r2_hidden(sK7,X0)
% 7.77/1.48      | ~ r2_hidden(sK7,sK5)
% 7.77/1.48      | X0 != sK5
% 7.77/1.48      | sK7 != sK7 ),
% 7.77/1.48      inference(instantiation,[status(thm)],[c_3558]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_10138,plain,
% 7.77/1.48      ( r2_hidden(sK7,k1_relat_1(sK8))
% 7.77/1.48      | ~ r2_hidden(sK7,sK5)
% 7.77/1.48      | k1_relat_1(sK8) != sK5
% 7.77/1.48      | sK7 != sK7 ),
% 7.77/1.48      inference(instantiation,[status(thm)],[c_5863]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_3,plain,
% 7.77/1.48      ( r1_tarski(k1_xboole_0,X0) ),
% 7.77/1.48      inference(cnf_transformation,[],[f51]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_2053,plain,
% 7.77/1.48      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.77/1.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_28,plain,
% 7.77/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.77/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.77/1.48      | k1_relset_1(X1,X2,X0) = X1
% 7.77/1.48      | k1_xboole_0 = X2 ),
% 7.77/1.48      inference(cnf_transformation,[],[f74]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_32,negated_conjecture,
% 7.77/1.48      ( v1_funct_2(sK8,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) ),
% 7.77/1.48      inference(cnf_transformation,[],[f94]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_889,plain,
% 7.77/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.77/1.48      | k2_enumset1(sK6,sK6,sK6,sK6) != X2
% 7.77/1.48      | k1_relset_1(X1,X2,X0) = X1
% 7.77/1.48      | sK5 != X1
% 7.77/1.48      | sK8 != X0
% 7.77/1.48      | k1_xboole_0 = X2 ),
% 7.77/1.48      inference(resolution_lifted,[status(thm)],[c_28,c_32]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_890,plain,
% 7.77/1.48      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6))))
% 7.77/1.48      | k1_relset_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK8) = sK5
% 7.77/1.48      | k1_xboole_0 = k2_enumset1(sK6,sK6,sK6,sK6) ),
% 7.77/1.48      inference(unflattening,[status(thm)],[c_889]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_31,negated_conjecture,
% 7.77/1.48      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6)))) ),
% 7.77/1.48      inference(cnf_transformation,[],[f93]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_892,plain,
% 7.77/1.48      ( k1_relset_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK8) = sK5
% 7.77/1.48      | k1_xboole_0 = k2_enumset1(sK6,sK6,sK6,sK6) ),
% 7.77/1.48      inference(global_propositional_subsumption,
% 7.77/1.48                [status(thm)],
% 7.77/1.48                [c_890,c_31]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_2038,plain,
% 7.77/1.48      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6)))) = iProver_top ),
% 7.77/1.48      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_21,plain,
% 7.77/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.77/1.48      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.77/1.48      inference(cnf_transformation,[],[f72]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_2041,plain,
% 7.77/1.48      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.77/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.77/1.48      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_4057,plain,
% 7.77/1.48      ( k1_relset_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK8) = k1_relat_1(sK8) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_2038,c_2041]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_4257,plain,
% 7.77/1.48      ( k2_enumset1(sK6,sK6,sK6,sK6) = k1_xboole_0
% 7.77/1.48      | k1_relat_1(sK8) = sK5 ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_892,c_4057]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_7,plain,
% 7.77/1.48      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
% 7.77/1.48      inference(cnf_transformation,[],[f96]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_2049,plain,
% 7.77/1.48      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) = iProver_top ),
% 7.77/1.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_18,plain,
% 7.77/1.48      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 7.77/1.48      inference(cnf_transformation,[],[f69]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_2044,plain,
% 7.77/1.48      ( r2_hidden(X0,X1) != iProver_top
% 7.77/1.48      | r1_tarski(X1,X0) != iProver_top ),
% 7.77/1.48      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_2636,plain,
% 7.77/1.48      ( r1_tarski(k2_enumset1(X0,X0,X0,X1),X1) != iProver_top ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_2049,c_2044]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_4946,plain,
% 7.77/1.48      ( k1_relat_1(sK8) = sK5
% 7.77/1.48      | r1_tarski(k1_xboole_0,sK6) != iProver_top ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_4257,c_2636]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_5141,plain,
% 7.77/1.48      ( k1_relat_1(sK8) = sK5 ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_2053,c_4946]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_22,plain,
% 7.77/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.77/1.48      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.77/1.48      inference(cnf_transformation,[],[f73]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_2040,plain,
% 7.77/1.48      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.77/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.77/1.48      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_3131,plain,
% 7.77/1.48      ( k2_relset_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK8) = k2_relat_1(sK8) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_2038,c_2040]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_20,plain,
% 7.77/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.77/1.48      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 7.77/1.48      inference(cnf_transformation,[],[f71]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_2042,plain,
% 7.77/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.77/1.48      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 7.77/1.48      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_4176,plain,
% 7.77/1.48      ( m1_subset_1(k2_relat_1(sK8),k1_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6))) = iProver_top
% 7.77/1.48      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6)))) != iProver_top ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_3131,c_2042]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_36,plain,
% 7.77/1.48      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6)))) = iProver_top ),
% 7.77/1.48      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_4538,plain,
% 7.77/1.48      ( m1_subset_1(k2_relat_1(sK8),k1_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6))) = iProver_top ),
% 7.77/1.48      inference(global_propositional_subsumption,
% 7.77/1.48                [status(thm)],
% 7.77/1.48                [c_4176,c_36]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_11,plain,
% 7.77/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.77/1.48      inference(cnf_transformation,[],[f61]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_2045,plain,
% 7.77/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.77/1.48      | r1_tarski(X0,X1) = iProver_top ),
% 7.77/1.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_4543,plain,
% 7.77/1.48      ( r1_tarski(k2_relat_1(sK8),k2_enumset1(sK6,sK6,sK6,sK6)) = iProver_top ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_4538,c_2045]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_4545,plain,
% 7.77/1.48      ( r1_tarski(k2_relat_1(sK8),k2_enumset1(sK6,sK6,sK6,sK6)) ),
% 7.77/1.48      inference(predicate_to_equality_rev,[status(thm)],[c_4543]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_9,plain,
% 7.77/1.48      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 7.77/1.48      inference(cnf_transformation,[],[f99]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_2094,plain,
% 7.77/1.48      ( ~ r2_hidden(k1_funct_1(sK8,sK7),k2_enumset1(sK6,sK6,sK6,X0))
% 7.77/1.48      | k1_funct_1(sK8,sK7) = X0
% 7.77/1.48      | k1_funct_1(sK8,sK7) = sK6 ),
% 7.77/1.48      inference(instantiation,[status(thm)],[c_9]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_3752,plain,
% 7.77/1.48      ( ~ r2_hidden(k1_funct_1(sK8,sK7),k2_enumset1(sK6,sK6,sK6,sK6))
% 7.77/1.48      | k1_funct_1(sK8,sK7) = sK6 ),
% 7.77/1.48      inference(instantiation,[status(thm)],[c_2094]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1400,plain,( X0 = X0 ),theory(equality) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_3181,plain,
% 7.77/1.48      ( sK7 = sK7 ),
% 7.77/1.48      inference(instantiation,[status(thm)],[c_1400]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_19,plain,
% 7.77/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.77/1.48      | v1_relat_1(X0) ),
% 7.77/1.48      inference(cnf_transformation,[],[f70]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_2118,plain,
% 7.77/1.48      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.77/1.48      | v1_relat_1(sK8) ),
% 7.77/1.48      inference(instantiation,[status(thm)],[c_19]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_2233,plain,
% 7.77/1.48      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6))))
% 7.77/1.48      | v1_relat_1(sK8) ),
% 7.77/1.48      inference(instantiation,[status(thm)],[c_2118]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_29,negated_conjecture,
% 7.77/1.48      ( k1_funct_1(sK8,sK7) != sK6 ),
% 7.77/1.48      inference(cnf_transformation,[],[f84]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_30,negated_conjecture,
% 7.77/1.48      ( r2_hidden(sK7,sK5) ),
% 7.77/1.48      inference(cnf_transformation,[],[f83]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(contradiction,plain,
% 7.77/1.48      ( $false ),
% 7.77/1.48      inference(minisat,
% 7.77/1.48                [status(thm)],
% 7.77/1.48                [c_21955,c_21318,c_10138,c_5141,c_4545,c_3752,c_3181,
% 7.77/1.48                 c_2233,c_29,c_30,c_31]) ).
% 7.77/1.48  
% 7.77/1.48  
% 7.77/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.77/1.48  
% 7.77/1.48  ------                               Statistics
% 7.77/1.48  
% 7.77/1.48  ------ General
% 7.77/1.48  
% 7.77/1.48  abstr_ref_over_cycles:                  0
% 7.77/1.48  abstr_ref_under_cycles:                 0
% 7.77/1.48  gc_basic_clause_elim:                   0
% 7.77/1.48  forced_gc_time:                         0
% 7.77/1.48  parsing_time:                           0.009
% 7.77/1.48  unif_index_cands_time:                  0.
% 7.77/1.48  unif_index_add_time:                    0.
% 7.77/1.48  orderings_time:                         0.
% 7.77/1.48  out_proof_time:                         0.009
% 7.77/1.48  total_time:                             0.624
% 7.77/1.48  num_of_symbols:                         55
% 7.77/1.48  num_of_terms:                           19049
% 7.77/1.48  
% 7.77/1.48  ------ Preprocessing
% 7.77/1.48  
% 7.77/1.48  num_of_splits:                          0
% 7.77/1.48  num_of_split_atoms:                     0
% 7.77/1.48  num_of_reused_defs:                     0
% 7.77/1.48  num_eq_ax_congr_red:                    44
% 7.77/1.48  num_of_sem_filtered_clauses:            1
% 7.77/1.48  num_of_subtypes:                        0
% 7.77/1.48  monotx_restored_types:                  0
% 7.77/1.48  sat_num_of_epr_types:                   0
% 7.77/1.48  sat_num_of_non_cyclic_types:            0
% 7.77/1.48  sat_guarded_non_collapsed_types:        0
% 7.77/1.48  num_pure_diseq_elim:                    0
% 7.77/1.48  simp_replaced_by:                       0
% 7.77/1.48  res_preprocessed:                       154
% 7.77/1.48  prep_upred:                             0
% 7.77/1.48  prep_unflattend:                        81
% 7.77/1.48  smt_new_axioms:                         0
% 7.77/1.48  pred_elim_cands:                        4
% 7.77/1.48  pred_elim:                              2
% 7.77/1.48  pred_elim_cl:                           5
% 7.77/1.48  pred_elim_cycles:                       7
% 7.77/1.48  merged_defs:                            8
% 7.77/1.48  merged_defs_ncl:                        0
% 7.77/1.48  bin_hyper_res:                          8
% 7.77/1.48  prep_cycles:                            4
% 7.77/1.48  pred_elim_time:                         0.012
% 7.77/1.48  splitting_time:                         0.
% 7.77/1.48  sem_filter_time:                        0.
% 7.77/1.48  monotx_time:                            0.
% 7.77/1.48  subtype_inf_time:                       0.
% 7.77/1.48  
% 7.77/1.48  ------ Problem properties
% 7.77/1.48  
% 7.77/1.48  clauses:                                29
% 7.77/1.48  conjectures:                            3
% 7.77/1.48  epr:                                    4
% 7.77/1.48  horn:                                   22
% 7.77/1.48  ground:                                 6
% 7.77/1.48  unary:                                  6
% 7.77/1.48  binary:                                 10
% 7.77/1.48  lits:                                   71
% 7.77/1.48  lits_eq:                                25
% 7.77/1.48  fd_pure:                                0
% 7.77/1.48  fd_pseudo:                              0
% 7.77/1.48  fd_cond:                                3
% 7.77/1.48  fd_pseudo_cond:                         3
% 7.77/1.48  ac_symbols:                             0
% 7.77/1.48  
% 7.77/1.48  ------ Propositional Solver
% 7.77/1.48  
% 7.77/1.48  prop_solver_calls:                      30
% 7.77/1.48  prop_fast_solver_calls:                 1575
% 7.77/1.48  smt_solver_calls:                       0
% 7.77/1.48  smt_fast_solver_calls:                  0
% 7.77/1.48  prop_num_of_clauses:                    9030
% 7.77/1.48  prop_preprocess_simplified:             19144
% 7.77/1.48  prop_fo_subsumed:                       13
% 7.77/1.48  prop_solver_time:                       0.
% 7.77/1.48  smt_solver_time:                        0.
% 7.77/1.48  smt_fast_solver_time:                   0.
% 7.77/1.48  prop_fast_solver_time:                  0.
% 7.77/1.48  prop_unsat_core_time:                   0.
% 7.77/1.48  
% 7.77/1.48  ------ QBF
% 7.77/1.48  
% 7.77/1.48  qbf_q_res:                              0
% 7.77/1.48  qbf_num_tautologies:                    0
% 7.77/1.48  qbf_prep_cycles:                        0
% 7.77/1.48  
% 7.77/1.48  ------ BMC1
% 7.77/1.48  
% 7.77/1.48  bmc1_current_bound:                     -1
% 7.77/1.48  bmc1_last_solved_bound:                 -1
% 7.77/1.48  bmc1_unsat_core_size:                   -1
% 7.77/1.48  bmc1_unsat_core_parents_size:           -1
% 7.77/1.48  bmc1_merge_next_fun:                    0
% 7.77/1.48  bmc1_unsat_core_clauses_time:           0.
% 7.77/1.48  
% 7.77/1.48  ------ Instantiation
% 7.77/1.48  
% 7.77/1.48  inst_num_of_clauses:                    2127
% 7.77/1.48  inst_num_in_passive:                    1307
% 7.77/1.48  inst_num_in_active:                     696
% 7.77/1.48  inst_num_in_unprocessed:                123
% 7.77/1.48  inst_num_of_loops:                      1129
% 7.77/1.48  inst_num_of_learning_restarts:          0
% 7.77/1.48  inst_num_moves_active_passive:          431
% 7.77/1.48  inst_lit_activity:                      0
% 7.77/1.48  inst_lit_activity_moves:                0
% 7.77/1.48  inst_num_tautologies:                   0
% 7.77/1.48  inst_num_prop_implied:                  0
% 7.77/1.48  inst_num_existing_simplified:           0
% 7.77/1.48  inst_num_eq_res_simplified:             0
% 7.77/1.48  inst_num_child_elim:                    0
% 7.77/1.48  inst_num_of_dismatching_blockings:      2047
% 7.77/1.48  inst_num_of_non_proper_insts:           3043
% 7.77/1.48  inst_num_of_duplicates:                 0
% 7.77/1.48  inst_inst_num_from_inst_to_res:         0
% 7.77/1.48  inst_dismatching_checking_time:         0.
% 7.77/1.48  
% 7.77/1.48  ------ Resolution
% 7.77/1.48  
% 7.77/1.48  res_num_of_clauses:                     0
% 7.77/1.48  res_num_in_passive:                     0
% 7.77/1.48  res_num_in_active:                      0
% 7.77/1.48  res_num_of_loops:                       158
% 7.77/1.48  res_forward_subset_subsumed:            213
% 7.77/1.48  res_backward_subset_subsumed:           0
% 7.77/1.48  res_forward_subsumed:                   0
% 7.77/1.48  res_backward_subsumed:                  1
% 7.77/1.48  res_forward_subsumption_resolution:     0
% 7.77/1.48  res_backward_subsumption_resolution:    1
% 7.77/1.48  res_clause_to_clause_subsumption:       2707
% 7.77/1.48  res_orphan_elimination:                 0
% 7.77/1.48  res_tautology_del:                      175
% 7.77/1.48  res_num_eq_res_simplified:              0
% 7.77/1.48  res_num_sel_changes:                    0
% 7.77/1.48  res_moves_from_active_to_pass:          0
% 7.77/1.48  
% 7.77/1.48  ------ Superposition
% 7.77/1.48  
% 7.77/1.48  sup_time_total:                         0.
% 7.77/1.48  sup_time_generating:                    0.
% 7.77/1.48  sup_time_sim_full:                      0.
% 7.77/1.48  sup_time_sim_immed:                     0.
% 7.77/1.48  
% 7.77/1.48  sup_num_of_clauses:                     905
% 7.77/1.48  sup_num_in_active:                      202
% 7.77/1.48  sup_num_in_passive:                     703
% 7.77/1.48  sup_num_of_loops:                       224
% 7.77/1.48  sup_fw_superposition:                   797
% 7.77/1.48  sup_bw_superposition:                   518
% 7.77/1.48  sup_immediate_simplified:               223
% 7.77/1.48  sup_given_eliminated:                   0
% 7.77/1.48  comparisons_done:                       0
% 7.77/1.48  comparisons_avoided:                    121
% 7.77/1.48  
% 7.77/1.48  ------ Simplifications
% 7.77/1.48  
% 7.77/1.48  
% 7.77/1.48  sim_fw_subset_subsumed:                 95
% 7.77/1.48  sim_bw_subset_subsumed:                 34
% 7.77/1.48  sim_fw_subsumed:                        39
% 7.77/1.48  sim_bw_subsumed:                        22
% 7.77/1.48  sim_fw_subsumption_res:                 0
% 7.77/1.48  sim_bw_subsumption_res:                 0
% 7.77/1.48  sim_tautology_del:                      14
% 7.77/1.48  sim_eq_tautology_del:                   136
% 7.77/1.48  sim_eq_res_simp:                        0
% 7.77/1.48  sim_fw_demodulated:                     4
% 7.77/1.48  sim_bw_demodulated:                     14
% 7.77/1.48  sim_light_normalised:                   69
% 7.77/1.48  sim_joinable_taut:                      0
% 7.77/1.48  sim_joinable_simp:                      0
% 7.77/1.48  sim_ac_normalised:                      0
% 7.77/1.48  sim_smt_subsumption:                    0
% 7.77/1.48  
%------------------------------------------------------------------------------
