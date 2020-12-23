%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:03 EST 2020

% Result     : Theorem 4.11s
% Output     : CNFRefutation 4.11s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 287 expanded)
%              Number of clauses        :   66 (  75 expanded)
%              Number of leaves         :   22 (  62 expanded)
%              Depth                    :   18
%              Number of atoms          :  547 (1193 expanded)
%              Number of equality atoms :  256 ( 539 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f36,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f37,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f36])).

fof(f52,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( k1_funct_1(sK7,sK6) != sK5
      & r2_hidden(sK6,sK4)
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_tarski(sK5))))
      & v1_funct_2(sK7,sK4,k1_tarski(sK5))
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( k1_funct_1(sK7,sK6) != sK5
    & r2_hidden(sK6,sK4)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_tarski(sK5))))
    & v1_funct_2(sK7,sK4,k1_tarski(sK5))
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f37,f52])).

fof(f92,plain,(
    r2_hidden(sK6,sK4) ),
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

fof(f34,plain,(
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
    inference(flattening,[],[f34])).

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
    inference(nnf_transformation,[],[f35])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f90,plain,(
    v1_funct_2(sK7,sK4,k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f53])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f94,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f65,f66])).

fof(f95,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f64,f94])).

fof(f105,plain,(
    v1_funct_2(sK7,sK4,k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(definition_unfolding,[],[f90,f95])).

fof(f91,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_tarski(sK5)))) ),
    inference(cnf_transformation,[],[f53])).

fof(f104,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5)))) ),
    inference(definition_unfolding,[],[f91,f95])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f38])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK0(X0,X1,X2,X3) != X2
            & sK0(X0,X1,X2,X3) != X1
            & sK0(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
        & ( sK0(X0,X1,X2,X3) = X2
          | sK0(X0,X1,X2,X3) = X1
          | sK0(X0,X1,X2,X3) = X0
          | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK0(X0,X1,X2,X3) != X2
              & sK0(X0,X1,X2,X3) != X1
              & sK0(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
          & ( sK0(X0,X1,X2,X3) = X2
            | sK0(X0,X1,X2,X3) = X1
            | sK0(X0,X1,X2,X3) = X0
            | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).

fof(f58,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f101,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f58,f66])).

fof(f108,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f101])).

fof(f109,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k2_enumset1(X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f108])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f49,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) = X2
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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

fof(f50,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f46,f49,f48,f47])).

fof(f75,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f113,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f114,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f113])).

fof(f89,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f53])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
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
    inference(nnf_transformation,[],[f8])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f59,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f100,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f59,f66])).

fof(f106,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f100])).

fof(f107,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f106])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f56,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f103,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f56,f66])).

fof(f112,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f103])).

fof(f93,plain,(
    k1_funct_1(sK7,sK6) != sK5 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_33,negated_conjecture,
    ( r2_hidden(sK6,sK4) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1715,plain,
    ( r2_hidden(sK6,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK7,sK4,k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_888,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_enumset1(sK5,sK5,sK5,sK5) != X2
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X1
    | sK7 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_35])).

cnf(c_889,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5))))
    | k1_relset_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK7) = sK4
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(unflattening,[status(thm)],[c_888])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5)))) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_891,plain,
    ( k1_relset_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK7) = sK4
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_889,c_34])).

cnf(c_1714,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1716,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3287,plain,
    ( k1_relset_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_1714,c_1716])).

cnf(c_3818,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) = k1_xboole_0
    | k1_relat_1(sK7) = sK4 ),
    inference(superposition,[status(thm)],[c_891,c_3287])).

cnf(c_7,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1722,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4046,plain,
    ( k1_relat_1(sK7) = sK4
    | r2_hidden(sK5,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3818,c_1722])).

cnf(c_1,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_22,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_530,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_22])).

cnf(c_531,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_530])).

cnf(c_1712,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_531])).

cnf(c_7163,plain,
    ( k1_relat_1(sK7) = sK4 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4046,c_1712])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_619,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_36])).

cnf(c_620,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK7))
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7))
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_619])).

cnf(c_1706,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_620])).

cnf(c_39,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_621,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_620])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1941,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5))))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1942,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5)))) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1941])).

cnf(c_2010,plain,
    ( r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1706,c_39,c_621,c_1942])).

cnf(c_2011,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2010])).

cnf(c_7178,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7163,c_2011])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_282,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_283,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_282])).

cnf(c_24,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_15,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_497,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_24,c_15])).

cnf(c_501,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_497,c_23])).

cnf(c_502,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_501])).

cnf(c_560,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | X4 != X1
    | k2_relat_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_283,c_502])).

cnf(c_561,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X2)) ),
    inference(unflattening,[status(thm)],[c_560])).

cnf(c_1709,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_561])).

cnf(c_3111,plain,
    ( m1_subset_1(k2_relat_1(sK7),k1_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1714,c_1709])).

cnf(c_13,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1718,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3717,plain,
    ( m1_subset_1(X0,k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3111,c_1718])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1719,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4416,plain,
    ( r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | v1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3717,c_1719])).

cnf(c_6,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1723,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1728,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2252,plain,
    ( v1_xboole_0(k2_enumset1(X0,X0,X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1723,c_1728])).

cnf(c_9711,plain,
    ( r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4416,c_2252])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1720,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | r2_hidden(X0,k2_enumset1(X1,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_9717,plain,
    ( sK5 = X0
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9711,c_1720])).

cnf(c_9885,plain,
    ( k1_funct_1(sK7,X0) = sK5
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7178,c_9717])).

cnf(c_20303,plain,
    ( k1_funct_1(sK7,sK6) = sK5 ),
    inference(superposition,[status(thm)],[c_1715,c_9885])).

cnf(c_32,negated_conjecture,
    ( k1_funct_1(sK7,sK6) != sK5 ),
    inference(cnf_transformation,[],[f93])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_20303,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:33:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.11/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.11/0.98  
% 4.11/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.11/0.98  
% 4.11/0.98  ------  iProver source info
% 4.11/0.98  
% 4.11/0.98  git: date: 2020-06-30 10:37:57 +0100
% 4.11/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.11/0.98  git: non_committed_changes: false
% 4.11/0.98  git: last_make_outside_of_git: false
% 4.11/0.98  
% 4.11/0.98  ------ 
% 4.11/0.98  
% 4.11/0.98  ------ Input Options
% 4.11/0.98  
% 4.11/0.98  --out_options                           all
% 4.11/0.98  --tptp_safe_out                         true
% 4.11/0.98  --problem_path                          ""
% 4.11/0.98  --include_path                          ""
% 4.11/0.98  --clausifier                            res/vclausify_rel
% 4.11/0.98  --clausifier_options                    --mode clausify
% 4.11/0.98  --stdin                                 false
% 4.11/0.98  --stats_out                             all
% 4.11/0.98  
% 4.11/0.98  ------ General Options
% 4.11/0.98  
% 4.11/0.98  --fof                                   false
% 4.11/0.98  --time_out_real                         305.
% 4.11/0.98  --time_out_virtual                      -1.
% 4.11/0.98  --symbol_type_check                     false
% 4.11/0.98  --clausify_out                          false
% 4.11/0.98  --sig_cnt_out                           false
% 4.11/0.98  --trig_cnt_out                          false
% 4.11/0.98  --trig_cnt_out_tolerance                1.
% 4.11/0.98  --trig_cnt_out_sk_spl                   false
% 4.11/0.98  --abstr_cl_out                          false
% 4.11/0.98  
% 4.11/0.98  ------ Global Options
% 4.11/0.98  
% 4.11/0.98  --schedule                              default
% 4.11/0.98  --add_important_lit                     false
% 4.11/0.98  --prop_solver_per_cl                    1000
% 4.11/0.98  --min_unsat_core                        false
% 4.11/0.98  --soft_assumptions                      false
% 4.11/0.98  --soft_lemma_size                       3
% 4.11/0.98  --prop_impl_unit_size                   0
% 4.11/0.98  --prop_impl_unit                        []
% 4.11/0.98  --share_sel_clauses                     true
% 4.11/0.98  --reset_solvers                         false
% 4.11/0.98  --bc_imp_inh                            [conj_cone]
% 4.11/0.98  --conj_cone_tolerance                   3.
% 4.11/0.98  --extra_neg_conj                        none
% 4.11/0.98  --large_theory_mode                     true
% 4.11/0.98  --prolific_symb_bound                   200
% 4.11/0.98  --lt_threshold                          2000
% 4.11/0.98  --clause_weak_htbl                      true
% 4.11/0.98  --gc_record_bc_elim                     false
% 4.11/0.98  
% 4.11/0.98  ------ Preprocessing Options
% 4.11/0.98  
% 4.11/0.98  --preprocessing_flag                    true
% 4.11/0.98  --time_out_prep_mult                    0.1
% 4.11/0.98  --splitting_mode                        input
% 4.11/0.98  --splitting_grd                         true
% 4.11/0.98  --splitting_cvd                         false
% 4.11/0.98  --splitting_cvd_svl                     false
% 4.11/0.98  --splitting_nvd                         32
% 4.11/0.98  --sub_typing                            true
% 4.11/0.98  --prep_gs_sim                           true
% 4.11/0.98  --prep_unflatten                        true
% 4.11/0.98  --prep_res_sim                          true
% 4.11/0.98  --prep_upred                            true
% 4.11/0.98  --prep_sem_filter                       exhaustive
% 4.11/0.98  --prep_sem_filter_out                   false
% 4.11/0.98  --pred_elim                             true
% 4.11/0.98  --res_sim_input                         true
% 4.11/0.98  --eq_ax_congr_red                       true
% 4.11/0.98  --pure_diseq_elim                       true
% 4.11/0.98  --brand_transform                       false
% 4.11/0.98  --non_eq_to_eq                          false
% 4.11/0.98  --prep_def_merge                        true
% 4.11/0.98  --prep_def_merge_prop_impl              false
% 4.11/0.99  --prep_def_merge_mbd                    true
% 4.11/0.99  --prep_def_merge_tr_red                 false
% 4.11/0.99  --prep_def_merge_tr_cl                  false
% 4.11/0.99  --smt_preprocessing                     true
% 4.11/0.99  --smt_ac_axioms                         fast
% 4.11/0.99  --preprocessed_out                      false
% 4.11/0.99  --preprocessed_stats                    false
% 4.11/0.99  
% 4.11/0.99  ------ Abstraction refinement Options
% 4.11/0.99  
% 4.11/0.99  --abstr_ref                             []
% 4.11/0.99  --abstr_ref_prep                        false
% 4.11/0.99  --abstr_ref_until_sat                   false
% 4.11/0.99  --abstr_ref_sig_restrict                funpre
% 4.11/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.11/0.99  --abstr_ref_under                       []
% 4.11/0.99  
% 4.11/0.99  ------ SAT Options
% 4.11/0.99  
% 4.11/0.99  --sat_mode                              false
% 4.11/0.99  --sat_fm_restart_options                ""
% 4.11/0.99  --sat_gr_def                            false
% 4.11/0.99  --sat_epr_types                         true
% 4.11/0.99  --sat_non_cyclic_types                  false
% 4.11/0.99  --sat_finite_models                     false
% 4.11/0.99  --sat_fm_lemmas                         false
% 4.11/0.99  --sat_fm_prep                           false
% 4.11/0.99  --sat_fm_uc_incr                        true
% 4.11/0.99  --sat_out_model                         small
% 4.11/0.99  --sat_out_clauses                       false
% 4.11/0.99  
% 4.11/0.99  ------ QBF Options
% 4.11/0.99  
% 4.11/0.99  --qbf_mode                              false
% 4.11/0.99  --qbf_elim_univ                         false
% 4.11/0.99  --qbf_dom_inst                          none
% 4.11/0.99  --qbf_dom_pre_inst                      false
% 4.11/0.99  --qbf_sk_in                             false
% 4.11/0.99  --qbf_pred_elim                         true
% 4.11/0.99  --qbf_split                             512
% 4.11/0.99  
% 4.11/0.99  ------ BMC1 Options
% 4.11/0.99  
% 4.11/0.99  --bmc1_incremental                      false
% 4.11/0.99  --bmc1_axioms                           reachable_all
% 4.11/0.99  --bmc1_min_bound                        0
% 4.11/0.99  --bmc1_max_bound                        -1
% 4.11/0.99  --bmc1_max_bound_default                -1
% 4.11/0.99  --bmc1_symbol_reachability              true
% 4.11/0.99  --bmc1_property_lemmas                  false
% 4.11/0.99  --bmc1_k_induction                      false
% 4.11/0.99  --bmc1_non_equiv_states                 false
% 4.11/0.99  --bmc1_deadlock                         false
% 4.11/0.99  --bmc1_ucm                              false
% 4.11/0.99  --bmc1_add_unsat_core                   none
% 4.11/0.99  --bmc1_unsat_core_children              false
% 4.11/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.11/0.99  --bmc1_out_stat                         full
% 4.11/0.99  --bmc1_ground_init                      false
% 4.11/0.99  --bmc1_pre_inst_next_state              false
% 4.11/0.99  --bmc1_pre_inst_state                   false
% 4.11/0.99  --bmc1_pre_inst_reach_state             false
% 4.11/0.99  --bmc1_out_unsat_core                   false
% 4.11/0.99  --bmc1_aig_witness_out                  false
% 4.11/0.99  --bmc1_verbose                          false
% 4.11/0.99  --bmc1_dump_clauses_tptp                false
% 4.11/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.11/0.99  --bmc1_dump_file                        -
% 4.11/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.11/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.11/0.99  --bmc1_ucm_extend_mode                  1
% 4.11/0.99  --bmc1_ucm_init_mode                    2
% 4.11/0.99  --bmc1_ucm_cone_mode                    none
% 4.11/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.11/0.99  --bmc1_ucm_relax_model                  4
% 4.11/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.11/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.11/0.99  --bmc1_ucm_layered_model                none
% 4.11/0.99  --bmc1_ucm_max_lemma_size               10
% 4.11/0.99  
% 4.11/0.99  ------ AIG Options
% 4.11/0.99  
% 4.11/0.99  --aig_mode                              false
% 4.11/0.99  
% 4.11/0.99  ------ Instantiation Options
% 4.11/0.99  
% 4.11/0.99  --instantiation_flag                    true
% 4.11/0.99  --inst_sos_flag                         false
% 4.11/0.99  --inst_sos_phase                        true
% 4.11/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.11/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.11/0.99  --inst_lit_sel_side                     num_symb
% 4.11/0.99  --inst_solver_per_active                1400
% 4.11/0.99  --inst_solver_calls_frac                1.
% 4.11/0.99  --inst_passive_queue_type               priority_queues
% 4.11/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.11/0.99  --inst_passive_queues_freq              [25;2]
% 4.11/0.99  --inst_dismatching                      true
% 4.11/0.99  --inst_eager_unprocessed_to_passive     true
% 4.11/0.99  --inst_prop_sim_given                   true
% 4.11/0.99  --inst_prop_sim_new                     false
% 4.11/0.99  --inst_subs_new                         false
% 4.11/0.99  --inst_eq_res_simp                      false
% 4.11/0.99  --inst_subs_given                       false
% 4.11/0.99  --inst_orphan_elimination               true
% 4.11/0.99  --inst_learning_loop_flag               true
% 4.11/0.99  --inst_learning_start                   3000
% 4.11/0.99  --inst_learning_factor                  2
% 4.11/0.99  --inst_start_prop_sim_after_learn       3
% 4.11/0.99  --inst_sel_renew                        solver
% 4.11/0.99  --inst_lit_activity_flag                true
% 4.11/0.99  --inst_restr_to_given                   false
% 4.11/0.99  --inst_activity_threshold               500
% 4.11/0.99  --inst_out_proof                        true
% 4.11/0.99  
% 4.11/0.99  ------ Resolution Options
% 4.11/0.99  
% 4.11/0.99  --resolution_flag                       true
% 4.11/0.99  --res_lit_sel                           adaptive
% 4.11/0.99  --res_lit_sel_side                      none
% 4.11/0.99  --res_ordering                          kbo
% 4.11/0.99  --res_to_prop_solver                    active
% 4.11/0.99  --res_prop_simpl_new                    false
% 4.11/0.99  --res_prop_simpl_given                  true
% 4.11/0.99  --res_passive_queue_type                priority_queues
% 4.11/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.11/0.99  --res_passive_queues_freq               [15;5]
% 4.11/0.99  --res_forward_subs                      full
% 4.11/0.99  --res_backward_subs                     full
% 4.11/0.99  --res_forward_subs_resolution           true
% 4.11/0.99  --res_backward_subs_resolution          true
% 4.11/0.99  --res_orphan_elimination                true
% 4.11/0.99  --res_time_limit                        2.
% 4.11/0.99  --res_out_proof                         true
% 4.11/0.99  
% 4.11/0.99  ------ Superposition Options
% 4.11/0.99  
% 4.11/0.99  --superposition_flag                    true
% 4.11/0.99  --sup_passive_queue_type                priority_queues
% 4.11/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.11/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.11/0.99  --demod_completeness_check              fast
% 4.11/0.99  --demod_use_ground                      true
% 4.11/0.99  --sup_to_prop_solver                    passive
% 4.11/0.99  --sup_prop_simpl_new                    true
% 4.11/0.99  --sup_prop_simpl_given                  true
% 4.11/0.99  --sup_fun_splitting                     false
% 4.11/0.99  --sup_smt_interval                      50000
% 4.11/0.99  
% 4.11/0.99  ------ Superposition Simplification Setup
% 4.11/0.99  
% 4.11/0.99  --sup_indices_passive                   []
% 4.11/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.11/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.11/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.11/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.11/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.11/0.99  --sup_full_bw                           [BwDemod]
% 4.11/0.99  --sup_immed_triv                        [TrivRules]
% 4.11/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.11/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.11/0.99  --sup_immed_bw_main                     []
% 4.11/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.11/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.11/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.11/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.11/0.99  
% 4.11/0.99  ------ Combination Options
% 4.11/0.99  
% 4.11/0.99  --comb_res_mult                         3
% 4.11/0.99  --comb_sup_mult                         2
% 4.11/0.99  --comb_inst_mult                        10
% 4.11/0.99  
% 4.11/0.99  ------ Debug Options
% 4.11/0.99  
% 4.11/0.99  --dbg_backtrace                         false
% 4.11/0.99  --dbg_dump_prop_clauses                 false
% 4.11/0.99  --dbg_dump_prop_clauses_file            -
% 4.11/0.99  --dbg_out_stat                          false
% 4.11/0.99  ------ Parsing...
% 4.11/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.11/0.99  
% 4.11/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 4.11/0.99  
% 4.11/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.11/0.99  
% 4.11/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.11/0.99  ------ Proving...
% 4.11/0.99  ------ Problem Properties 
% 4.11/0.99  
% 4.11/0.99  
% 4.11/0.99  clauses                                 30
% 4.11/0.99  conjectures                             3
% 4.11/0.99  EPR                                     4
% 4.11/0.99  Horn                                    23
% 4.11/0.99  unary                                   8
% 4.11/0.99  binary                                  7
% 4.11/0.99  lits                                    75
% 4.11/0.99  lits eq                                 28
% 4.11/0.99  fd_pure                                 0
% 4.11/0.99  fd_pseudo                               0
% 4.11/0.99  fd_cond                                 3
% 4.11/0.99  fd_pseudo_cond                          4
% 4.11/0.99  AC symbols                              0
% 4.11/0.99  
% 4.11/0.99  ------ Schedule dynamic 5 is on 
% 4.11/0.99  
% 4.11/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.11/0.99  
% 4.11/0.99  
% 4.11/0.99  ------ 
% 4.11/0.99  Current options:
% 4.11/0.99  ------ 
% 4.11/0.99  
% 4.11/0.99  ------ Input Options
% 4.11/0.99  
% 4.11/0.99  --out_options                           all
% 4.11/0.99  --tptp_safe_out                         true
% 4.11/0.99  --problem_path                          ""
% 4.11/0.99  --include_path                          ""
% 4.11/0.99  --clausifier                            res/vclausify_rel
% 4.11/0.99  --clausifier_options                    --mode clausify
% 4.11/0.99  --stdin                                 false
% 4.11/0.99  --stats_out                             all
% 4.11/0.99  
% 4.11/0.99  ------ General Options
% 4.11/0.99  
% 4.11/0.99  --fof                                   false
% 4.11/0.99  --time_out_real                         305.
% 4.11/0.99  --time_out_virtual                      -1.
% 4.11/0.99  --symbol_type_check                     false
% 4.11/0.99  --clausify_out                          false
% 4.11/0.99  --sig_cnt_out                           false
% 4.11/0.99  --trig_cnt_out                          false
% 4.11/0.99  --trig_cnt_out_tolerance                1.
% 4.11/0.99  --trig_cnt_out_sk_spl                   false
% 4.11/0.99  --abstr_cl_out                          false
% 4.11/0.99  
% 4.11/0.99  ------ Global Options
% 4.11/0.99  
% 4.11/0.99  --schedule                              default
% 4.11/0.99  --add_important_lit                     false
% 4.11/0.99  --prop_solver_per_cl                    1000
% 4.11/0.99  --min_unsat_core                        false
% 4.11/0.99  --soft_assumptions                      false
% 4.11/0.99  --soft_lemma_size                       3
% 4.11/0.99  --prop_impl_unit_size                   0
% 4.11/0.99  --prop_impl_unit                        []
% 4.11/0.99  --share_sel_clauses                     true
% 4.11/0.99  --reset_solvers                         false
% 4.11/0.99  --bc_imp_inh                            [conj_cone]
% 4.11/0.99  --conj_cone_tolerance                   3.
% 4.11/0.99  --extra_neg_conj                        none
% 4.11/0.99  --large_theory_mode                     true
% 4.11/0.99  --prolific_symb_bound                   200
% 4.11/0.99  --lt_threshold                          2000
% 4.11/0.99  --clause_weak_htbl                      true
% 4.11/0.99  --gc_record_bc_elim                     false
% 4.11/0.99  
% 4.11/0.99  ------ Preprocessing Options
% 4.11/0.99  
% 4.11/0.99  --preprocessing_flag                    true
% 4.11/0.99  --time_out_prep_mult                    0.1
% 4.11/0.99  --splitting_mode                        input
% 4.11/0.99  --splitting_grd                         true
% 4.11/0.99  --splitting_cvd                         false
% 4.11/0.99  --splitting_cvd_svl                     false
% 4.11/0.99  --splitting_nvd                         32
% 4.11/0.99  --sub_typing                            true
% 4.11/0.99  --prep_gs_sim                           true
% 4.11/0.99  --prep_unflatten                        true
% 4.11/0.99  --prep_res_sim                          true
% 4.11/0.99  --prep_upred                            true
% 4.11/0.99  --prep_sem_filter                       exhaustive
% 4.11/0.99  --prep_sem_filter_out                   false
% 4.11/0.99  --pred_elim                             true
% 4.11/0.99  --res_sim_input                         true
% 4.11/0.99  --eq_ax_congr_red                       true
% 4.11/0.99  --pure_diseq_elim                       true
% 4.11/0.99  --brand_transform                       false
% 4.11/0.99  --non_eq_to_eq                          false
% 4.11/0.99  --prep_def_merge                        true
% 4.11/0.99  --prep_def_merge_prop_impl              false
% 4.11/0.99  --prep_def_merge_mbd                    true
% 4.11/0.99  --prep_def_merge_tr_red                 false
% 4.11/0.99  --prep_def_merge_tr_cl                  false
% 4.11/0.99  --smt_preprocessing                     true
% 4.11/0.99  --smt_ac_axioms                         fast
% 4.11/0.99  --preprocessed_out                      false
% 4.11/0.99  --preprocessed_stats                    false
% 4.11/0.99  
% 4.11/0.99  ------ Abstraction refinement Options
% 4.11/0.99  
% 4.11/0.99  --abstr_ref                             []
% 4.11/0.99  --abstr_ref_prep                        false
% 4.11/0.99  --abstr_ref_until_sat                   false
% 4.11/0.99  --abstr_ref_sig_restrict                funpre
% 4.11/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.11/0.99  --abstr_ref_under                       []
% 4.11/0.99  
% 4.11/0.99  ------ SAT Options
% 4.11/0.99  
% 4.11/0.99  --sat_mode                              false
% 4.11/0.99  --sat_fm_restart_options                ""
% 4.11/0.99  --sat_gr_def                            false
% 4.11/0.99  --sat_epr_types                         true
% 4.11/0.99  --sat_non_cyclic_types                  false
% 4.11/0.99  --sat_finite_models                     false
% 4.11/0.99  --sat_fm_lemmas                         false
% 4.11/0.99  --sat_fm_prep                           false
% 4.11/0.99  --sat_fm_uc_incr                        true
% 4.11/0.99  --sat_out_model                         small
% 4.11/0.99  --sat_out_clauses                       false
% 4.11/0.99  
% 4.11/0.99  ------ QBF Options
% 4.11/0.99  
% 4.11/0.99  --qbf_mode                              false
% 4.11/0.99  --qbf_elim_univ                         false
% 4.11/0.99  --qbf_dom_inst                          none
% 4.11/0.99  --qbf_dom_pre_inst                      false
% 4.11/0.99  --qbf_sk_in                             false
% 4.11/0.99  --qbf_pred_elim                         true
% 4.11/0.99  --qbf_split                             512
% 4.11/0.99  
% 4.11/0.99  ------ BMC1 Options
% 4.11/0.99  
% 4.11/0.99  --bmc1_incremental                      false
% 4.11/0.99  --bmc1_axioms                           reachable_all
% 4.11/0.99  --bmc1_min_bound                        0
% 4.11/0.99  --bmc1_max_bound                        -1
% 4.11/0.99  --bmc1_max_bound_default                -1
% 4.11/0.99  --bmc1_symbol_reachability              true
% 4.11/0.99  --bmc1_property_lemmas                  false
% 4.11/0.99  --bmc1_k_induction                      false
% 4.11/0.99  --bmc1_non_equiv_states                 false
% 4.11/0.99  --bmc1_deadlock                         false
% 4.11/0.99  --bmc1_ucm                              false
% 4.11/0.99  --bmc1_add_unsat_core                   none
% 4.11/0.99  --bmc1_unsat_core_children              false
% 4.11/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.11/0.99  --bmc1_out_stat                         full
% 4.11/0.99  --bmc1_ground_init                      false
% 4.11/0.99  --bmc1_pre_inst_next_state              false
% 4.11/0.99  --bmc1_pre_inst_state                   false
% 4.11/0.99  --bmc1_pre_inst_reach_state             false
% 4.11/0.99  --bmc1_out_unsat_core                   false
% 4.11/0.99  --bmc1_aig_witness_out                  false
% 4.11/0.99  --bmc1_verbose                          false
% 4.11/0.99  --bmc1_dump_clauses_tptp                false
% 4.11/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.11/0.99  --bmc1_dump_file                        -
% 4.11/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.11/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.11/0.99  --bmc1_ucm_extend_mode                  1
% 4.11/0.99  --bmc1_ucm_init_mode                    2
% 4.11/0.99  --bmc1_ucm_cone_mode                    none
% 4.11/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.11/0.99  --bmc1_ucm_relax_model                  4
% 4.11/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.11/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.11/0.99  --bmc1_ucm_layered_model                none
% 4.11/0.99  --bmc1_ucm_max_lemma_size               10
% 4.11/0.99  
% 4.11/0.99  ------ AIG Options
% 4.11/0.99  
% 4.11/0.99  --aig_mode                              false
% 4.11/0.99  
% 4.11/0.99  ------ Instantiation Options
% 4.11/0.99  
% 4.11/0.99  --instantiation_flag                    true
% 4.11/0.99  --inst_sos_flag                         false
% 4.11/0.99  --inst_sos_phase                        true
% 4.11/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.11/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.11/0.99  --inst_lit_sel_side                     none
% 4.11/0.99  --inst_solver_per_active                1400
% 4.11/0.99  --inst_solver_calls_frac                1.
% 4.11/0.99  --inst_passive_queue_type               priority_queues
% 4.11/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.11/0.99  --inst_passive_queues_freq              [25;2]
% 4.11/0.99  --inst_dismatching                      true
% 4.11/0.99  --inst_eager_unprocessed_to_passive     true
% 4.11/0.99  --inst_prop_sim_given                   true
% 4.11/0.99  --inst_prop_sim_new                     false
% 4.11/0.99  --inst_subs_new                         false
% 4.11/0.99  --inst_eq_res_simp                      false
% 4.11/0.99  --inst_subs_given                       false
% 4.11/0.99  --inst_orphan_elimination               true
% 4.11/0.99  --inst_learning_loop_flag               true
% 4.11/0.99  --inst_learning_start                   3000
% 4.11/0.99  --inst_learning_factor                  2
% 4.11/0.99  --inst_start_prop_sim_after_learn       3
% 4.11/0.99  --inst_sel_renew                        solver
% 4.11/0.99  --inst_lit_activity_flag                true
% 4.11/0.99  --inst_restr_to_given                   false
% 4.11/0.99  --inst_activity_threshold               500
% 4.11/0.99  --inst_out_proof                        true
% 4.11/0.99  
% 4.11/0.99  ------ Resolution Options
% 4.11/0.99  
% 4.11/0.99  --resolution_flag                       false
% 4.11/0.99  --res_lit_sel                           adaptive
% 4.11/0.99  --res_lit_sel_side                      none
% 4.11/0.99  --res_ordering                          kbo
% 4.11/0.99  --res_to_prop_solver                    active
% 4.11/0.99  --res_prop_simpl_new                    false
% 4.11/0.99  --res_prop_simpl_given                  true
% 4.11/0.99  --res_passive_queue_type                priority_queues
% 4.11/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.11/0.99  --res_passive_queues_freq               [15;5]
% 4.11/0.99  --res_forward_subs                      full
% 4.11/0.99  --res_backward_subs                     full
% 4.11/0.99  --res_forward_subs_resolution           true
% 4.11/0.99  --res_backward_subs_resolution          true
% 4.11/0.99  --res_orphan_elimination                true
% 4.11/0.99  --res_time_limit                        2.
% 4.11/0.99  --res_out_proof                         true
% 4.11/0.99  
% 4.11/0.99  ------ Superposition Options
% 4.11/0.99  
% 4.11/0.99  --superposition_flag                    true
% 4.11/0.99  --sup_passive_queue_type                priority_queues
% 4.11/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.11/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.11/0.99  --demod_completeness_check              fast
% 4.11/0.99  --demod_use_ground                      true
% 4.11/0.99  --sup_to_prop_solver                    passive
% 4.11/0.99  --sup_prop_simpl_new                    true
% 4.11/0.99  --sup_prop_simpl_given                  true
% 4.11/0.99  --sup_fun_splitting                     false
% 4.11/0.99  --sup_smt_interval                      50000
% 4.11/0.99  
% 4.11/0.99  ------ Superposition Simplification Setup
% 4.11/0.99  
% 4.11/0.99  --sup_indices_passive                   []
% 4.11/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.11/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.11/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.11/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.11/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.11/0.99  --sup_full_bw                           [BwDemod]
% 4.11/0.99  --sup_immed_triv                        [TrivRules]
% 4.11/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.11/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.11/0.99  --sup_immed_bw_main                     []
% 4.11/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.11/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.11/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.11/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.11/0.99  
% 4.11/0.99  ------ Combination Options
% 4.11/0.99  
% 4.11/0.99  --comb_res_mult                         3
% 4.11/0.99  --comb_sup_mult                         2
% 4.11/0.99  --comb_inst_mult                        10
% 4.11/0.99  
% 4.11/0.99  ------ Debug Options
% 4.11/0.99  
% 4.11/0.99  --dbg_backtrace                         false
% 4.11/0.99  --dbg_dump_prop_clauses                 false
% 4.11/0.99  --dbg_dump_prop_clauses_file            -
% 4.11/0.99  --dbg_out_stat                          false
% 4.11/0.99  
% 4.11/0.99  
% 4.11/0.99  
% 4.11/0.99  
% 4.11/0.99  ------ Proving...
% 4.11/0.99  
% 4.11/0.99  
% 4.11/0.99  % SZS status Theorem for theBenchmark.p
% 4.11/0.99  
% 4.11/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 4.11/0.99  
% 4.11/0.99  fof(f17,conjecture,(
% 4.11/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 4.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/0.99  
% 4.11/0.99  fof(f18,negated_conjecture,(
% 4.11/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 4.11/0.99    inference(negated_conjecture,[],[f17])).
% 4.11/0.99  
% 4.11/0.99  fof(f36,plain,(
% 4.11/0.99    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 4.11/0.99    inference(ennf_transformation,[],[f18])).
% 4.11/0.99  
% 4.11/0.99  fof(f37,plain,(
% 4.11/0.99    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 4.11/0.99    inference(flattening,[],[f36])).
% 4.11/0.99  
% 4.11/0.99  fof(f52,plain,(
% 4.11/0.99    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (k1_funct_1(sK7,sK6) != sK5 & r2_hidden(sK6,sK4) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_tarski(sK5)))) & v1_funct_2(sK7,sK4,k1_tarski(sK5)) & v1_funct_1(sK7))),
% 4.11/0.99    introduced(choice_axiom,[])).
% 4.11/0.99  
% 4.11/0.99  fof(f53,plain,(
% 4.11/0.99    k1_funct_1(sK7,sK6) != sK5 & r2_hidden(sK6,sK4) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_tarski(sK5)))) & v1_funct_2(sK7,sK4,k1_tarski(sK5)) & v1_funct_1(sK7)),
% 4.11/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f37,f52])).
% 4.11/0.99  
% 4.11/0.99  fof(f92,plain,(
% 4.11/0.99    r2_hidden(sK6,sK4)),
% 4.11/0.99    inference(cnf_transformation,[],[f53])).
% 4.11/0.99  
% 4.11/0.99  fof(f16,axiom,(
% 4.11/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 4.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/0.99  
% 4.11/0.99  fof(f34,plain,(
% 4.11/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.11/0.99    inference(ennf_transformation,[],[f16])).
% 4.11/0.99  
% 4.11/0.99  fof(f35,plain,(
% 4.11/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.11/0.99    inference(flattening,[],[f34])).
% 4.11/0.99  
% 4.11/0.99  fof(f51,plain,(
% 4.11/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.11/0.99    inference(nnf_transformation,[],[f35])).
% 4.11/0.99  
% 4.11/0.99  fof(f83,plain,(
% 4.11/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.11/0.99    inference(cnf_transformation,[],[f51])).
% 4.11/0.99  
% 4.11/0.99  fof(f90,plain,(
% 4.11/0.99    v1_funct_2(sK7,sK4,k1_tarski(sK5))),
% 4.11/0.99    inference(cnf_transformation,[],[f53])).
% 4.11/0.99  
% 4.11/0.99  fof(f4,axiom,(
% 4.11/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 4.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/0.99  
% 4.11/0.99  fof(f64,plain,(
% 4.11/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 4.11/0.99    inference(cnf_transformation,[],[f4])).
% 4.11/0.99  
% 4.11/0.99  fof(f5,axiom,(
% 4.11/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 4.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/0.99  
% 4.11/0.99  fof(f65,plain,(
% 4.11/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 4.11/0.99    inference(cnf_transformation,[],[f5])).
% 4.11/0.99  
% 4.11/0.99  fof(f6,axiom,(
% 4.11/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 4.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/0.99  
% 4.11/0.99  fof(f66,plain,(
% 4.11/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 4.11/0.99    inference(cnf_transformation,[],[f6])).
% 4.11/0.99  
% 4.11/0.99  fof(f94,plain,(
% 4.11/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 4.11/0.99    inference(definition_unfolding,[],[f65,f66])).
% 4.11/0.99  
% 4.11/0.99  fof(f95,plain,(
% 4.11/0.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 4.11/0.99    inference(definition_unfolding,[],[f64,f94])).
% 4.11/0.99  
% 4.11/0.99  fof(f105,plain,(
% 4.11/0.99    v1_funct_2(sK7,sK4,k2_enumset1(sK5,sK5,sK5,sK5))),
% 4.11/0.99    inference(definition_unfolding,[],[f90,f95])).
% 4.11/0.99  
% 4.11/0.99  fof(f91,plain,(
% 4.11/0.99    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_tarski(sK5))))),
% 4.11/0.99    inference(cnf_transformation,[],[f53])).
% 4.11/0.99  
% 4.11/0.99  fof(f104,plain,(
% 4.11/0.99    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5))))),
% 4.11/0.99    inference(definition_unfolding,[],[f91,f95])).
% 4.11/0.99  
% 4.11/0.99  fof(f15,axiom,(
% 4.11/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 4.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/0.99  
% 4.11/0.99  fof(f33,plain,(
% 4.11/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.11/0.99    inference(ennf_transformation,[],[f15])).
% 4.11/0.99  
% 4.11/0.99  fof(f82,plain,(
% 4.11/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.11/0.99    inference(cnf_transformation,[],[f33])).
% 4.11/0.99  
% 4.11/0.99  fof(f3,axiom,(
% 4.11/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 4.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/0.99  
% 4.11/0.99  fof(f22,plain,(
% 4.11/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 4.11/0.99    inference(ennf_transformation,[],[f3])).
% 4.11/0.99  
% 4.11/0.99  fof(f38,plain,(
% 4.11/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 4.11/0.99    inference(nnf_transformation,[],[f22])).
% 4.11/0.99  
% 4.11/0.99  fof(f39,plain,(
% 4.11/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 4.11/0.99    inference(flattening,[],[f38])).
% 4.11/0.99  
% 4.11/0.99  fof(f40,plain,(
% 4.11/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 4.11/0.99    inference(rectify,[],[f39])).
% 4.11/0.99  
% 4.11/0.99  fof(f41,plain,(
% 4.11/0.99    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 4.11/0.99    introduced(choice_axiom,[])).
% 4.11/0.99  
% 4.11/0.99  fof(f42,plain,(
% 4.11/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 4.11/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).
% 4.11/0.99  
% 4.11/0.99  fof(f58,plain,(
% 4.11/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 4.11/0.99    inference(cnf_transformation,[],[f42])).
% 4.11/0.99  
% 4.11/0.99  fof(f101,plain,(
% 4.11/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 4.11/0.99    inference(definition_unfolding,[],[f58,f66])).
% 4.11/0.99  
% 4.11/0.99  fof(f108,plain,(
% 4.11/0.99    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X5,X2) != X3) )),
% 4.11/0.99    inference(equality_resolution,[],[f101])).
% 4.11/0.99  
% 4.11/0.99  fof(f109,plain,(
% 4.11/0.99    ( ! [X2,X0,X5] : (r2_hidden(X5,k2_enumset1(X0,X0,X5,X2))) )),
% 4.11/0.99    inference(equality_resolution,[],[f108])).
% 4.11/0.99  
% 4.11/0.99  fof(f2,axiom,(
% 4.11/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 4.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/0.99  
% 4.11/0.99  fof(f55,plain,(
% 4.11/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 4.11/0.99    inference(cnf_transformation,[],[f2])).
% 4.11/0.99  
% 4.11/0.99  fof(f12,axiom,(
% 4.11/0.99    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 4.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/0.99  
% 4.11/0.99  fof(f30,plain,(
% 4.11/0.99    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 4.11/0.99    inference(ennf_transformation,[],[f12])).
% 4.11/0.99  
% 4.11/0.99  fof(f79,plain,(
% 4.11/0.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 4.11/0.99    inference(cnf_transformation,[],[f30])).
% 4.11/0.99  
% 4.11/0.99  fof(f11,axiom,(
% 4.11/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 4.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/0.99  
% 4.11/0.99  fof(f28,plain,(
% 4.11/0.99    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.11/0.99    inference(ennf_transformation,[],[f11])).
% 4.11/0.99  
% 4.11/0.99  fof(f29,plain,(
% 4.11/0.99    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.11/0.99    inference(flattening,[],[f28])).
% 4.11/0.99  
% 4.11/0.99  fof(f45,plain,(
% 4.11/0.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.11/0.99    inference(nnf_transformation,[],[f29])).
% 4.11/0.99  
% 4.11/0.99  fof(f46,plain,(
% 4.11/0.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.11/0.99    inference(rectify,[],[f45])).
% 4.11/0.99  
% 4.11/0.99  fof(f49,plain,(
% 4.11/0.99    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))))),
% 4.11/0.99    introduced(choice_axiom,[])).
% 4.11/0.99  
% 4.11/0.99  fof(f48,plain,(
% 4.11/0.99    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) = X2 & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))) )),
% 4.11/0.99    introduced(choice_axiom,[])).
% 4.11/0.99  
% 4.11/0.99  fof(f47,plain,(
% 4.11/0.99    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1))))),
% 4.11/0.99    introduced(choice_axiom,[])).
% 4.11/0.99  
% 4.11/0.99  fof(f50,plain,(
% 4.11/0.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & ((k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.11/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f46,f49,f48,f47])).
% 4.11/0.99  
% 4.11/0.99  fof(f75,plain,(
% 4.11/0.99    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.11/0.99    inference(cnf_transformation,[],[f50])).
% 4.11/0.99  
% 4.11/0.99  fof(f113,plain,(
% 4.11/0.99    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.11/0.99    inference(equality_resolution,[],[f75])).
% 4.11/0.99  
% 4.11/0.99  fof(f114,plain,(
% 4.11/0.99    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.11/0.99    inference(equality_resolution,[],[f113])).
% 4.11/0.99  
% 4.11/0.99  fof(f89,plain,(
% 4.11/0.99    v1_funct_1(sK7)),
% 4.11/0.99    inference(cnf_transformation,[],[f53])).
% 4.11/0.99  
% 4.11/0.99  fof(f13,axiom,(
% 4.11/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 4.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/0.99  
% 4.11/0.99  fof(f31,plain,(
% 4.11/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.11/0.99    inference(ennf_transformation,[],[f13])).
% 4.11/0.99  
% 4.11/0.99  fof(f80,plain,(
% 4.11/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.11/0.99    inference(cnf_transformation,[],[f31])).
% 4.11/0.99  
% 4.11/0.99  fof(f8,axiom,(
% 4.11/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 4.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/0.99  
% 4.11/0.99  fof(f43,plain,(
% 4.11/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 4.11/0.99    inference(nnf_transformation,[],[f8])).
% 4.11/0.99  
% 4.11/0.99  fof(f69,plain,(
% 4.11/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 4.11/0.99    inference(cnf_transformation,[],[f43])).
% 4.11/0.99  
% 4.11/0.99  fof(f14,axiom,(
% 4.11/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 4.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/0.99  
% 4.11/0.99  fof(f20,plain,(
% 4.11/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 4.11/0.99    inference(pure_predicate_removal,[],[f14])).
% 4.11/0.99  
% 4.11/0.99  fof(f32,plain,(
% 4.11/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.11/0.99    inference(ennf_transformation,[],[f20])).
% 4.11/0.99  
% 4.11/0.99  fof(f81,plain,(
% 4.11/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.11/0.99    inference(cnf_transformation,[],[f32])).
% 4.11/0.99  
% 4.11/0.99  fof(f10,axiom,(
% 4.11/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 4.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/0.99  
% 4.11/0.99  fof(f27,plain,(
% 4.11/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 4.11/0.99    inference(ennf_transformation,[],[f10])).
% 4.11/0.99  
% 4.11/0.99  fof(f44,plain,(
% 4.11/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 4.11/0.99    inference(nnf_transformation,[],[f27])).
% 4.11/0.99  
% 4.11/0.99  fof(f71,plain,(
% 4.11/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 4.11/0.99    inference(cnf_transformation,[],[f44])).
% 4.11/0.99  
% 4.11/0.99  fof(f9,axiom,(
% 4.11/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 4.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/0.99  
% 4.11/0.99  fof(f25,plain,(
% 4.11/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 4.11/0.99    inference(ennf_transformation,[],[f9])).
% 4.11/0.99  
% 4.11/0.99  fof(f26,plain,(
% 4.11/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 4.11/0.99    inference(flattening,[],[f25])).
% 4.11/0.99  
% 4.11/0.99  fof(f70,plain,(
% 4.11/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 4.11/0.99    inference(cnf_transformation,[],[f26])).
% 4.11/0.99  
% 4.11/0.99  fof(f7,axiom,(
% 4.11/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 4.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/0.99  
% 4.11/0.99  fof(f23,plain,(
% 4.11/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 4.11/0.99    inference(ennf_transformation,[],[f7])).
% 4.11/0.99  
% 4.11/0.99  fof(f24,plain,(
% 4.11/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 4.11/0.99    inference(flattening,[],[f23])).
% 4.11/0.99  
% 4.11/0.99  fof(f67,plain,(
% 4.11/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 4.11/0.99    inference(cnf_transformation,[],[f24])).
% 4.11/0.99  
% 4.11/0.99  fof(f59,plain,(
% 4.11/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 4.11/0.99    inference(cnf_transformation,[],[f42])).
% 4.11/0.99  
% 4.11/0.99  fof(f100,plain,(
% 4.11/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 4.11/0.99    inference(definition_unfolding,[],[f59,f66])).
% 4.11/0.99  
% 4.11/0.99  fof(f106,plain,(
% 4.11/0.99    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 4.11/0.99    inference(equality_resolution,[],[f100])).
% 4.11/0.99  
% 4.11/0.99  fof(f107,plain,(
% 4.11/0.99    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 4.11/0.99    inference(equality_resolution,[],[f106])).
% 4.11/0.99  
% 4.11/0.99  fof(f1,axiom,(
% 4.11/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 4.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/0.99  
% 4.11/0.99  fof(f19,plain,(
% 4.11/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 4.11/0.99    inference(unused_predicate_definition_removal,[],[f1])).
% 4.11/0.99  
% 4.11/0.99  fof(f21,plain,(
% 4.11/0.99    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 4.11/0.99    inference(ennf_transformation,[],[f19])).
% 4.11/0.99  
% 4.11/0.99  fof(f54,plain,(
% 4.11/0.99    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 4.11/0.99    inference(cnf_transformation,[],[f21])).
% 4.11/0.99  
% 4.11/0.99  fof(f56,plain,(
% 4.11/0.99    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 4.11/0.99    inference(cnf_transformation,[],[f42])).
% 4.11/0.99  
% 4.11/0.99  fof(f103,plain,(
% 4.11/0.99    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 4.11/0.99    inference(definition_unfolding,[],[f56,f66])).
% 4.11/0.99  
% 4.11/0.99  fof(f112,plain,(
% 4.11/0.99    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))) )),
% 4.11/0.99    inference(equality_resolution,[],[f103])).
% 4.11/0.99  
% 4.11/0.99  fof(f93,plain,(
% 4.11/0.99    k1_funct_1(sK7,sK6) != sK5),
% 4.11/0.99    inference(cnf_transformation,[],[f53])).
% 4.11/0.99  
% 4.11/0.99  cnf(c_33,negated_conjecture,
% 4.11/0.99      ( r2_hidden(sK6,sK4) ),
% 4.11/0.99      inference(cnf_transformation,[],[f92]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_1715,plain,
% 4.11/0.99      ( r2_hidden(sK6,sK4) = iProver_top ),
% 4.11/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_31,plain,
% 4.11/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 4.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.11/0.99      | k1_relset_1(X1,X2,X0) = X1
% 4.11/0.99      | k1_xboole_0 = X2 ),
% 4.11/0.99      inference(cnf_transformation,[],[f83]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_35,negated_conjecture,
% 4.11/0.99      ( v1_funct_2(sK7,sK4,k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 4.11/0.99      inference(cnf_transformation,[],[f105]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_888,plain,
% 4.11/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.11/0.99      | k2_enumset1(sK5,sK5,sK5,sK5) != X2
% 4.11/0.99      | k1_relset_1(X1,X2,X0) = X1
% 4.11/0.99      | sK4 != X1
% 4.11/0.99      | sK7 != X0
% 4.11/0.99      | k1_xboole_0 = X2 ),
% 4.11/0.99      inference(resolution_lifted,[status(thm)],[c_31,c_35]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_889,plain,
% 4.11/0.99      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5))))
% 4.11/0.99      | k1_relset_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK7) = sK4
% 4.11/0.99      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 4.11/0.99      inference(unflattening,[status(thm)],[c_888]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_34,negated_conjecture,
% 4.11/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5)))) ),
% 4.11/0.99      inference(cnf_transformation,[],[f104]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_891,plain,
% 4.11/0.99      ( k1_relset_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK7) = sK4
% 4.11/0.99      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 4.11/0.99      inference(global_propositional_subsumption,
% 4.11/0.99                [status(thm)],
% 4.11/0.99                [c_889,c_34]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_1714,plain,
% 4.11/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5)))) = iProver_top ),
% 4.11/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_25,plain,
% 4.11/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.11/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 4.11/0.99      inference(cnf_transformation,[],[f82]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_1716,plain,
% 4.11/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 4.11/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.11/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_3287,plain,
% 4.11/0.99      ( k1_relset_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK7) = k1_relat_1(sK7) ),
% 4.11/0.99      inference(superposition,[status(thm)],[c_1714,c_1716]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_3818,plain,
% 4.11/0.99      ( k2_enumset1(sK5,sK5,sK5,sK5) = k1_xboole_0
% 4.11/0.99      | k1_relat_1(sK7) = sK4 ),
% 4.11/0.99      inference(superposition,[status(thm)],[c_891,c_3287]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_7,plain,
% 4.11/0.99      ( r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) ),
% 4.11/0.99      inference(cnf_transformation,[],[f109]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_1722,plain,
% 4.11/0.99      ( r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) = iProver_top ),
% 4.11/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_4046,plain,
% 4.11/0.99      ( k1_relat_1(sK7) = sK4
% 4.11/0.99      | r2_hidden(sK5,k1_xboole_0) = iProver_top ),
% 4.11/0.99      inference(superposition,[status(thm)],[c_3818,c_1722]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_1,plain,
% 4.11/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 4.11/0.99      inference(cnf_transformation,[],[f55]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_22,plain,
% 4.11/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 4.11/0.99      inference(cnf_transformation,[],[f79]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_530,plain,
% 4.11/0.99      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 4.11/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_22]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_531,plain,
% 4.11/0.99      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 4.11/0.99      inference(unflattening,[status(thm)],[c_530]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_1712,plain,
% 4.11/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 4.11/0.99      inference(predicate_to_equality,[status(thm)],[c_531]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_7163,plain,
% 4.11/0.99      ( k1_relat_1(sK7) = sK4 ),
% 4.11/0.99      inference(forward_subsumption_resolution,
% 4.11/0.99                [status(thm)],
% 4.11/0.99                [c_4046,c_1712]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_19,plain,
% 4.11/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 4.11/0.99      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 4.11/0.99      | ~ v1_funct_1(X1)
% 4.11/0.99      | ~ v1_relat_1(X1) ),
% 4.11/0.99      inference(cnf_transformation,[],[f114]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_36,negated_conjecture,
% 4.11/0.99      ( v1_funct_1(sK7) ),
% 4.11/0.99      inference(cnf_transformation,[],[f89]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_619,plain,
% 4.11/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 4.11/0.99      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 4.11/0.99      | ~ v1_relat_1(X1)
% 4.11/0.99      | sK7 != X1 ),
% 4.11/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_36]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_620,plain,
% 4.11/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK7))
% 4.11/0.99      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7))
% 4.11/0.99      | ~ v1_relat_1(sK7) ),
% 4.11/0.99      inference(unflattening,[status(thm)],[c_619]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_1706,plain,
% 4.11/0.99      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 4.11/0.99      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
% 4.11/0.99      | v1_relat_1(sK7) != iProver_top ),
% 4.11/0.99      inference(predicate_to_equality,[status(thm)],[c_620]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_39,plain,
% 4.11/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5)))) = iProver_top ),
% 4.11/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_621,plain,
% 4.11/0.99      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 4.11/0.99      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
% 4.11/0.99      | v1_relat_1(sK7) != iProver_top ),
% 4.11/0.99      inference(predicate_to_equality,[status(thm)],[c_620]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_23,plain,
% 4.11/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.11/0.99      | v1_relat_1(X0) ),
% 4.11/0.99      inference(cnf_transformation,[],[f80]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_1941,plain,
% 4.11/0.99      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5))))
% 4.11/0.99      | v1_relat_1(sK7) ),
% 4.11/0.99      inference(instantiation,[status(thm)],[c_23]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_1942,plain,
% 4.11/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5)))) != iProver_top
% 4.11/0.99      | v1_relat_1(sK7) = iProver_top ),
% 4.11/0.99      inference(predicate_to_equality,[status(thm)],[c_1941]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_2010,plain,
% 4.11/0.99      ( r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
% 4.11/0.99      | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
% 4.11/0.99      inference(global_propositional_subsumption,
% 4.11/0.99                [status(thm)],
% 4.11/0.99                [c_1706,c_39,c_621,c_1942]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_2011,plain,
% 4.11/0.99      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 4.11/0.99      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top ),
% 4.11/0.99      inference(renaming,[status(thm)],[c_2010]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_7178,plain,
% 4.11/0.99      ( r2_hidden(X0,sK4) != iProver_top
% 4.11/0.99      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top ),
% 4.11/0.99      inference(demodulation,[status(thm)],[c_7163,c_2011]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_11,plain,
% 4.11/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 4.11/0.99      inference(cnf_transformation,[],[f69]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_282,plain,
% 4.11/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 4.11/0.99      inference(prop_impl,[status(thm)],[c_11]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_283,plain,
% 4.11/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 4.11/0.99      inference(renaming,[status(thm)],[c_282]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_24,plain,
% 4.11/0.99      ( v5_relat_1(X0,X1)
% 4.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 4.11/0.99      inference(cnf_transformation,[],[f81]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_15,plain,
% 4.11/0.99      ( ~ v5_relat_1(X0,X1)
% 4.11/0.99      | r1_tarski(k2_relat_1(X0),X1)
% 4.11/0.99      | ~ v1_relat_1(X0) ),
% 4.11/0.99      inference(cnf_transformation,[],[f71]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_497,plain,
% 4.11/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.11/0.99      | r1_tarski(k2_relat_1(X0),X2)
% 4.11/0.99      | ~ v1_relat_1(X0) ),
% 4.11/0.99      inference(resolution,[status(thm)],[c_24,c_15]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_501,plain,
% 4.11/0.99      ( r1_tarski(k2_relat_1(X0),X2)
% 4.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 4.11/0.99      inference(global_propositional_subsumption,
% 4.11/0.99                [status(thm)],
% 4.11/0.99                [c_497,c_23]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_502,plain,
% 4.11/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.11/0.99      | r1_tarski(k2_relat_1(X0),X2) ),
% 4.11/0.99      inference(renaming,[status(thm)],[c_501]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_560,plain,
% 4.11/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.11/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 4.11/0.99      | X4 != X1
% 4.11/0.99      | k2_relat_1(X2) != X0 ),
% 4.11/0.99      inference(resolution_lifted,[status(thm)],[c_283,c_502]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_561,plain,
% 4.11/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.11/0.99      | m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X2)) ),
% 4.11/0.99      inference(unflattening,[status(thm)],[c_560]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_1709,plain,
% 4.11/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 4.11/0.99      | m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X2)) = iProver_top ),
% 4.11/0.99      inference(predicate_to_equality,[status(thm)],[c_561]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_3111,plain,
% 4.11/0.99      ( m1_subset_1(k2_relat_1(sK7),k1_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5))) = iProver_top ),
% 4.11/0.99      inference(superposition,[status(thm)],[c_1714,c_1709]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_13,plain,
% 4.11/0.99      ( m1_subset_1(X0,X1)
% 4.11/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 4.11/0.99      | ~ r2_hidden(X0,X2) ),
% 4.11/0.99      inference(cnf_transformation,[],[f70]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_1718,plain,
% 4.11/0.99      ( m1_subset_1(X0,X1) = iProver_top
% 4.11/0.99      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 4.11/0.99      | r2_hidden(X0,X2) != iProver_top ),
% 4.11/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_3717,plain,
% 4.11/0.99      ( m1_subset_1(X0,k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top
% 4.11/0.99      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 4.11/0.99      inference(superposition,[status(thm)],[c_3111,c_1718]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_10,plain,
% 4.11/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 4.11/0.99      inference(cnf_transformation,[],[f67]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_1719,plain,
% 4.11/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 4.11/0.99      | r2_hidden(X0,X1) = iProver_top
% 4.11/0.99      | v1_xboole_0(X1) = iProver_top ),
% 4.11/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_4416,plain,
% 4.11/0.99      ( r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top
% 4.11/0.99      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 4.11/0.99      | v1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
% 4.11/0.99      inference(superposition,[status(thm)],[c_3717,c_1719]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_6,plain,
% 4.11/0.99      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
% 4.11/0.99      inference(cnf_transformation,[],[f107]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_1723,plain,
% 4.11/0.99      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
% 4.11/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_0,plain,
% 4.11/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 4.11/0.99      inference(cnf_transformation,[],[f54]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_1728,plain,
% 4.11/0.99      ( r2_hidden(X0,X1) != iProver_top
% 4.11/0.99      | v1_xboole_0(X1) != iProver_top ),
% 4.11/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_2252,plain,
% 4.11/0.99      ( v1_xboole_0(k2_enumset1(X0,X0,X1,X2)) != iProver_top ),
% 4.11/0.99      inference(superposition,[status(thm)],[c_1723,c_1728]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_9711,plain,
% 4.11/0.99      ( r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top
% 4.11/0.99      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 4.11/0.99      inference(forward_subsumption_resolution,
% 4.11/0.99                [status(thm)],
% 4.11/0.99                [c_4416,c_2252]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_9,plain,
% 4.11/0.99      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
% 4.11/0.99      | X0 = X1
% 4.11/0.99      | X0 = X2
% 4.11/0.99      | X0 = X3 ),
% 4.11/0.99      inference(cnf_transformation,[],[f112]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_1720,plain,
% 4.11/0.99      ( X0 = X1
% 4.11/0.99      | X0 = X2
% 4.11/0.99      | X0 = X3
% 4.11/0.99      | r2_hidden(X0,k2_enumset1(X1,X1,X2,X3)) != iProver_top ),
% 4.11/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_9717,plain,
% 4.11/0.99      ( sK5 = X0 | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 4.11/0.99      inference(superposition,[status(thm)],[c_9711,c_1720]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_9885,plain,
% 4.11/0.99      ( k1_funct_1(sK7,X0) = sK5 | r2_hidden(X0,sK4) != iProver_top ),
% 4.11/0.99      inference(superposition,[status(thm)],[c_7178,c_9717]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_20303,plain,
% 4.11/0.99      ( k1_funct_1(sK7,sK6) = sK5 ),
% 4.11/0.99      inference(superposition,[status(thm)],[c_1715,c_9885]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_32,negated_conjecture,
% 4.11/0.99      ( k1_funct_1(sK7,sK6) != sK5 ),
% 4.11/0.99      inference(cnf_transformation,[],[f93]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(contradiction,plain,
% 4.11/0.99      ( $false ),
% 4.11/0.99      inference(minisat,[status(thm)],[c_20303,c_32]) ).
% 4.11/0.99  
% 4.11/0.99  
% 4.11/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 4.11/0.99  
% 4.11/0.99  ------                               Statistics
% 4.11/0.99  
% 4.11/0.99  ------ General
% 4.11/0.99  
% 4.11/0.99  abstr_ref_over_cycles:                  0
% 4.11/0.99  abstr_ref_under_cycles:                 0
% 4.11/0.99  gc_basic_clause_elim:                   0
% 4.11/0.99  forced_gc_time:                         0
% 4.11/0.99  parsing_time:                           0.009
% 4.11/0.99  unif_index_cands_time:                  0.
% 4.11/0.99  unif_index_add_time:                    0.
% 4.11/0.99  orderings_time:                         0.
% 4.11/0.99  out_proof_time:                         0.011
% 4.11/0.99  total_time:                             0.498
% 4.11/0.99  num_of_symbols:                         55
% 4.11/0.99  num_of_terms:                           22160
% 4.11/0.99  
% 4.11/0.99  ------ Preprocessing
% 4.11/0.99  
% 4.11/0.99  num_of_splits:                          0
% 4.11/0.99  num_of_split_atoms:                     0
% 4.11/0.99  num_of_reused_defs:                     0
% 4.11/0.99  num_eq_ax_congr_red:                    35
% 4.11/0.99  num_of_sem_filtered_clauses:            1
% 4.11/0.99  num_of_subtypes:                        0
% 4.11/0.99  monotx_restored_types:                  0
% 4.11/0.99  sat_num_of_epr_types:                   0
% 4.11/0.99  sat_num_of_non_cyclic_types:            0
% 4.11/0.99  sat_guarded_non_collapsed_types:        0
% 4.11/0.99  num_pure_diseq_elim:                    0
% 4.11/0.99  simp_replaced_by:                       0
% 4.11/0.99  res_preprocessed:                       158
% 4.11/0.99  prep_upred:                             0
% 4.11/0.99  prep_unflattend:                        53
% 4.11/0.99  smt_new_axioms:                         0
% 4.11/0.99  pred_elim_cands:                        4
% 4.11/0.99  pred_elim:                              4
% 4.11/0.99  pred_elim_cl:                           7
% 4.11/0.99  pred_elim_cycles:                       9
% 4.11/0.99  merged_defs:                            2
% 4.11/0.99  merged_defs_ncl:                        0
% 4.11/0.99  bin_hyper_res:                          2
% 4.11/0.99  prep_cycles:                            4
% 4.11/0.99  pred_elim_time:                         0.01
% 4.11/0.99  splitting_time:                         0.
% 4.11/0.99  sem_filter_time:                        0.
% 4.11/0.99  monotx_time:                            0.
% 4.11/0.99  subtype_inf_time:                       0.
% 4.11/0.99  
% 4.11/0.99  ------ Problem properties
% 4.11/0.99  
% 4.11/0.99  clauses:                                30
% 4.11/0.99  conjectures:                            3
% 4.11/0.99  epr:                                    4
% 4.11/0.99  horn:                                   23
% 4.11/0.99  ground:                                 6
% 4.11/0.99  unary:                                  8
% 4.11/0.99  binary:                                 7
% 4.11/0.99  lits:                                   75
% 4.11/0.99  lits_eq:                                28
% 4.11/0.99  fd_pure:                                0
% 4.11/0.99  fd_pseudo:                              0
% 4.11/0.99  fd_cond:                                3
% 4.11/0.99  fd_pseudo_cond:                         4
% 4.11/0.99  ac_symbols:                             0
% 4.11/0.99  
% 4.11/0.99  ------ Propositional Solver
% 4.11/0.99  
% 4.11/0.99  prop_solver_calls:                      29
% 4.11/0.99  prop_fast_solver_calls:                 1388
% 4.11/0.99  smt_solver_calls:                       0
% 4.11/0.99  smt_fast_solver_calls:                  0
% 4.11/0.99  prop_num_of_clauses:                    7289
% 4.11/0.99  prop_preprocess_simplified:             17841
% 4.11/0.99  prop_fo_subsumed:                       11
% 4.11/0.99  prop_solver_time:                       0.
% 4.11/0.99  smt_solver_time:                        0.
% 4.11/0.99  smt_fast_solver_time:                   0.
% 4.11/0.99  prop_fast_solver_time:                  0.
% 4.11/0.99  prop_unsat_core_time:                   0.
% 4.11/0.99  
% 4.11/0.99  ------ QBF
% 4.11/0.99  
% 4.11/0.99  qbf_q_res:                              0
% 4.11/0.99  qbf_num_tautologies:                    0
% 4.11/0.99  qbf_prep_cycles:                        0
% 4.11/0.99  
% 4.11/0.99  ------ BMC1
% 4.11/0.99  
% 4.11/0.99  bmc1_current_bound:                     -1
% 4.11/0.99  bmc1_last_solved_bound:                 -1
% 4.11/0.99  bmc1_unsat_core_size:                   -1
% 4.11/0.99  bmc1_unsat_core_parents_size:           -1
% 4.11/0.99  bmc1_merge_next_fun:                    0
% 4.11/0.99  bmc1_unsat_core_clauses_time:           0.
% 4.11/0.99  
% 4.11/0.99  ------ Instantiation
% 4.11/0.99  
% 4.11/0.99  inst_num_of_clauses:                    2166
% 4.11/0.99  inst_num_in_passive:                    911
% 4.11/0.99  inst_num_in_active:                     646
% 4.11/0.99  inst_num_in_unprocessed:                609
% 4.11/0.99  inst_num_of_loops:                      740
% 4.11/0.99  inst_num_of_learning_restarts:          0
% 4.11/0.99  inst_num_moves_active_passive:          93
% 4.11/0.99  inst_lit_activity:                      0
% 4.11/0.99  inst_lit_activity_moves:                0
% 4.11/0.99  inst_num_tautologies:                   0
% 4.11/0.99  inst_num_prop_implied:                  0
% 4.11/0.99  inst_num_existing_simplified:           0
% 4.11/0.99  inst_num_eq_res_simplified:             0
% 4.11/0.99  inst_num_child_elim:                    0
% 4.11/0.99  inst_num_of_dismatching_blockings:      2653
% 4.11/0.99  inst_num_of_non_proper_insts:           1994
% 4.11/0.99  inst_num_of_duplicates:                 0
% 4.11/0.99  inst_inst_num_from_inst_to_res:         0
% 4.11/0.99  inst_dismatching_checking_time:         0.
% 4.11/0.99  
% 4.11/0.99  ------ Resolution
% 4.11/0.99  
% 4.11/0.99  res_num_of_clauses:                     0
% 4.11/0.99  res_num_in_passive:                     0
% 4.11/0.99  res_num_in_active:                      0
% 4.11/0.99  res_num_of_loops:                       162
% 4.11/0.99  res_forward_subset_subsumed:            451
% 4.11/0.99  res_backward_subset_subsumed:           0
% 4.11/0.99  res_forward_subsumed:                   0
% 4.11/0.99  res_backward_subsumed:                  0
% 4.11/0.99  res_forward_subsumption_resolution:     0
% 4.11/0.99  res_backward_subsumption_resolution:    1
% 4.11/0.99  res_clause_to_clause_subsumption:       1035
% 4.11/0.99  res_orphan_elimination:                 0
% 4.11/0.99  res_tautology_del:                      31
% 4.11/0.99  res_num_eq_res_simplified:              0
% 4.11/0.99  res_num_sel_changes:                    0
% 4.11/0.99  res_moves_from_active_to_pass:          0
% 4.11/0.99  
% 4.11/0.99  ------ Superposition
% 4.11/0.99  
% 4.11/0.99  sup_time_total:                         0.
% 4.11/0.99  sup_time_generating:                    0.
% 4.11/0.99  sup_time_sim_full:                      0.
% 4.11/0.99  sup_time_sim_immed:                     0.
% 4.11/0.99  
% 4.11/0.99  sup_num_of_clauses:                     282
% 4.11/0.99  sup_num_in_active:                      128
% 4.11/0.99  sup_num_in_passive:                     154
% 4.11/0.99  sup_num_of_loops:                       147
% 4.11/0.99  sup_fw_superposition:                   176
% 4.11/0.99  sup_bw_superposition:                   397
% 4.11/0.99  sup_immediate_simplified:               89
% 4.11/0.99  sup_given_eliminated:                   0
% 4.11/0.99  comparisons_done:                       0
% 4.11/0.99  comparisons_avoided:                    154
% 4.11/0.99  
% 4.11/0.99  ------ Simplifications
% 4.11/0.99  
% 4.11/0.99  
% 4.11/0.99  sim_fw_subset_subsumed:                 34
% 4.11/0.99  sim_bw_subset_subsumed:                 20
% 4.11/0.99  sim_fw_subsumed:                        51
% 4.11/0.99  sim_bw_subsumed:                        0
% 4.11/0.99  sim_fw_subsumption_res:                 5
% 4.11/0.99  sim_bw_subsumption_res:                 0
% 4.11/0.99  sim_tautology_del:                      8
% 4.11/0.99  sim_eq_tautology_del:                   121
% 4.11/0.99  sim_eq_res_simp:                        0
% 4.11/0.99  sim_fw_demodulated:                     0
% 4.11/0.99  sim_bw_demodulated:                     15
% 4.11/0.99  sim_light_normalised:                   24
% 4.11/0.99  sim_joinable_taut:                      0
% 4.11/0.99  sim_joinable_simp:                      0
% 4.11/0.99  sim_ac_normalised:                      0
% 4.11/0.99  sim_smt_subsumption:                    0
% 4.11/0.99  
%------------------------------------------------------------------------------
