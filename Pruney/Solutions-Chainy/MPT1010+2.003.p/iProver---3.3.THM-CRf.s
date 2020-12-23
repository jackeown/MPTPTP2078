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
% DateTime   : Thu Dec  3 12:06:02 EST 2020

% Result     : Theorem 7.35s
% Output     : CNFRefutation 7.35s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 357 expanded)
%              Number of clauses        :   60 (  87 expanded)
%              Number of leaves         :   22 (  82 expanded)
%              Depth                    :   21
%              Number of atoms          :  561 (1296 expanded)
%              Number of equality atoms :  277 ( 541 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f29])).

fof(f52,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( k1_funct_1(sK9,sK8) != sK7
      & r2_hidden(sK8,sK6)
      & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7))))
      & v1_funct_2(sK9,sK6,k1_tarski(sK7))
      & v1_funct_1(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( k1_funct_1(sK9,sK8) != sK7
    & r2_hidden(sK8,sK6)
    & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7))))
    & v1_funct_2(sK9,sK6,k1_tarski(sK7))
    & v1_funct_1(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f30,f52])).

fof(f94,plain,(
    r2_hidden(sK8,sK6) ),
    inference(cnf_transformation,[],[f53])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f93,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7)))) ),
    inference(cnf_transformation,[],[f53])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f96,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f97,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f70,f96])).

fof(f110,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) ),
    inference(definition_unfolding,[],[f93,f97])).

fof(f9,axiom,(
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

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f21])).

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
    inference(nnf_transformation,[],[f22])).

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
     => ( k1_funct_1(X0,sK5(X0,X5)) = X5
        & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) = X2
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
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
              ( k1_funct_1(X0,X3) != sK3(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK3(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f46,f49,f48,f47])).

fof(f77,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f122,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f123,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f122])).

fof(f91,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f53])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f109,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f66,f97])).

fof(f121,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f109])).

fof(f92,plain,(
    v1_funct_2(sK9,sK6,k1_tarski(sK7)) ),
    inference(cnf_transformation,[],[f53])).

fof(f111,plain,(
    v1_funct_2(sK9,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) ),
    inference(definition_unfolding,[],[f92,f97])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

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
    inference(nnf_transformation,[],[f28])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
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
     => ( ( ( sK1(X0,X1,X2,X3) != X2
            & sK1(X0,X1,X2,X3) != X1
            & sK1(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
        & ( sK1(X0,X1,X2,X3) = X2
          | sK1(X0,X1,X2,X3) = X1
          | sK1(X0,X1,X2,X3) = X0
          | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK1(X0,X1,X2,X3) != X2
              & sK1(X0,X1,X2,X3) != X1
              & sK1(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
          & ( sK1(X0,X1,X2,X3) = X2
            | sK1(X0,X1,X2,X3) = X1
            | sK1(X0,X1,X2,X3) = X0
            | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).

fof(f59,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f104,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f59,f72])).

fof(f116,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f104])).

fof(f117,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k2_enumset1(X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f116])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f95,plain,(
    k1_funct_1(sK9,sK8) != sK7 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_35,negated_conjecture,
    ( r2_hidden(sK8,sK6) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1962,plain,
    ( r2_hidden(sK8,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_17,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_414,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_415,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_414])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_419,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_415,c_25])).

cnf(c_420,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_419])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_547,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))) != k1_zfmisc_1(k2_zfmisc_1(X2,X1))
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_420,c_36])).

cnf(c_548,plain,
    ( r1_tarski(k2_relat_1(sK9),X0)
    | k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0)) ),
    inference(unflattening,[status(thm)],[c_547])).

cnf(c_1961,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | r1_tarski(k2_relat_1(sK9),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_548])).

cnf(c_2569,plain,
    ( r1_tarski(k2_relat_1(sK9),k2_enumset1(sK7,sK7,sK7,sK7)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1961])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_885,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_38])).

cnf(c_886,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK9))
    | r2_hidden(k1_funct_1(sK9,X0),k2_relat_1(sK9))
    | ~ v1_relat_1(sK9) ),
    inference(unflattening,[status(thm)],[c_885])).

cnf(c_1955,plain,
    ( r2_hidden(X0,k1_relat_1(sK9)) != iProver_top
    | r2_hidden(k1_funct_1(sK9,X0),k2_relat_1(sK9)) = iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_886])).

cnf(c_887,plain,
    ( r2_hidden(X0,k1_relat_1(sK9)) != iProver_top
    | r2_hidden(k1_funct_1(sK9,X0),k2_relat_1(sK9)) = iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_886])).

cnf(c_604,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_36])).

cnf(c_605,plain,
    ( v1_relat_1(sK9)
    | k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_604])).

cnf(c_1960,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_605])).

cnf(c_2309,plain,
    ( v1_relat_1(sK9) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1960])).

cnf(c_2689,plain,
    ( r2_hidden(k1_funct_1(sK9,X0),k2_relat_1(sK9)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK9)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1955,c_887,c_2309])).

cnf(c_2690,plain,
    ( r2_hidden(X0,k1_relat_1(sK9)) != iProver_top
    | r2_hidden(k1_funct_1(sK9,X0),k2_relat_1(sK9)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2689])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1977,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3428,plain,
    ( r2_hidden(X0,k1_relat_1(sK9)) != iProver_top
    | r2_hidden(k1_funct_1(sK9,X0),X1) = iProver_top
    | r1_tarski(k2_relat_1(sK9),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2690,c_1977])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f121])).

cnf(c_1964,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4758,plain,
    ( k1_funct_1(sK9,X0) = X1
    | r2_hidden(X0,k1_relat_1(sK9)) != iProver_top
    | r1_tarski(k2_relat_1(sK9),k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3428,c_1964])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK9,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_33,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_559,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK9 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_36])).

cnf(c_560,plain,
    ( ~ v1_funct_2(sK9,X0,X1)
    | k1_relset_1(X0,X1,sK9) = X0
    | k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_559])).

cnf(c_1071,plain,
    ( k2_enumset1(sK7,sK7,sK7,sK7) != X0
    | k1_relset_1(X1,X0,sK9) = X1
    | k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0))
    | sK6 != X1
    | sK9 != sK9
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_560])).

cnf(c_1072,plain,
    ( k1_relset_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = sK6
    | k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))) != k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))
    | k1_xboole_0 = k2_enumset1(sK7,sK7,sK7,sK7) ),
    inference(unflattening,[status(thm)],[c_1071])).

cnf(c_1151,plain,
    ( k1_relset_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = sK6
    | k1_xboole_0 = k2_enumset1(sK7,sK7,sK7,sK7) ),
    inference(equality_resolution_simp,[status(thm)],[c_1072])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_595,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK9 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_36])).

cnf(c_596,plain,
    ( k1_relset_1(X0,X1,sK9) = k1_relat_1(sK9)
    | k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_595])).

cnf(c_2208,plain,
    ( k1_relset_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_relat_1(sK9) ),
    inference(equality_resolution,[status(thm)],[c_596])).

cnf(c_2354,plain,
    ( k2_enumset1(sK7,sK7,sK7,sK7) = k1_xboole_0
    | k1_relat_1(sK9) = sK6 ),
    inference(demodulation,[status(thm)],[c_1151,c_2208])).

cnf(c_2358,plain,
    ( k1_relset_1(sK6,k1_xboole_0,sK9) = k1_relat_1(sK9)
    | k1_relat_1(sK9) = sK6 ),
    inference(superposition,[status(thm)],[c_2354,c_2208])).

cnf(c_10,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_1969,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2514,plain,
    ( k1_relat_1(sK9) = sK6
    | r2_hidden(sK7,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2354,c_1969])).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1963,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_6288,plain,
    ( k1_relat_1(sK9) = sK6
    | r1_tarski(k1_xboole_0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2514,c_1963])).

cnf(c_6300,plain,
    ( ~ r1_tarski(k1_xboole_0,sK7)
    | k1_relat_1(sK9) = sK6 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6288])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_6310,plain,
    ( r1_tarski(k1_xboole_0,sK7) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_7863,plain,
    ( k1_relat_1(sK9) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2358,c_6300,c_6310])).

cnf(c_22262,plain,
    ( k1_funct_1(sK9,X0) = X1
    | r2_hidden(X0,sK6) != iProver_top
    | r1_tarski(k2_relat_1(sK9),k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4758,c_7863])).

cnf(c_22270,plain,
    ( k1_funct_1(sK9,X0) = sK7
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2569,c_22262])).

cnf(c_23382,plain,
    ( k1_funct_1(sK9,sK8) = sK7 ),
    inference(superposition,[status(thm)],[c_1962,c_22270])).

cnf(c_34,negated_conjecture,
    ( k1_funct_1(sK9,sK8) != sK7 ),
    inference(cnf_transformation,[],[f95])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23382,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:07:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.35/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.35/1.49  
% 7.35/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.35/1.49  
% 7.35/1.49  ------  iProver source info
% 7.35/1.49  
% 7.35/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.35/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.35/1.49  git: non_committed_changes: false
% 7.35/1.49  git: last_make_outside_of_git: false
% 7.35/1.49  
% 7.35/1.49  ------ 
% 7.35/1.49  
% 7.35/1.49  ------ Input Options
% 7.35/1.49  
% 7.35/1.49  --out_options                           all
% 7.35/1.49  --tptp_safe_out                         true
% 7.35/1.49  --problem_path                          ""
% 7.35/1.49  --include_path                          ""
% 7.35/1.49  --clausifier                            res/vclausify_rel
% 7.35/1.49  --clausifier_options                    --mode clausify
% 7.35/1.49  --stdin                                 false
% 7.35/1.49  --stats_out                             all
% 7.35/1.49  
% 7.35/1.49  ------ General Options
% 7.35/1.49  
% 7.35/1.49  --fof                                   false
% 7.35/1.49  --time_out_real                         305.
% 7.35/1.49  --time_out_virtual                      -1.
% 7.35/1.49  --symbol_type_check                     false
% 7.35/1.49  --clausify_out                          false
% 7.35/1.49  --sig_cnt_out                           false
% 7.35/1.49  --trig_cnt_out                          false
% 7.35/1.49  --trig_cnt_out_tolerance                1.
% 7.35/1.49  --trig_cnt_out_sk_spl                   false
% 7.35/1.49  --abstr_cl_out                          false
% 7.35/1.49  
% 7.35/1.49  ------ Global Options
% 7.35/1.49  
% 7.35/1.49  --schedule                              default
% 7.35/1.49  --add_important_lit                     false
% 7.35/1.49  --prop_solver_per_cl                    1000
% 7.35/1.49  --min_unsat_core                        false
% 7.35/1.49  --soft_assumptions                      false
% 7.35/1.49  --soft_lemma_size                       3
% 7.35/1.49  --prop_impl_unit_size                   0
% 7.35/1.49  --prop_impl_unit                        []
% 7.35/1.49  --share_sel_clauses                     true
% 7.35/1.49  --reset_solvers                         false
% 7.35/1.49  --bc_imp_inh                            [conj_cone]
% 7.35/1.49  --conj_cone_tolerance                   3.
% 7.35/1.49  --extra_neg_conj                        none
% 7.35/1.49  --large_theory_mode                     true
% 7.35/1.49  --prolific_symb_bound                   200
% 7.35/1.49  --lt_threshold                          2000
% 7.35/1.49  --clause_weak_htbl                      true
% 7.35/1.49  --gc_record_bc_elim                     false
% 7.35/1.49  
% 7.35/1.49  ------ Preprocessing Options
% 7.35/1.49  
% 7.35/1.49  --preprocessing_flag                    true
% 7.35/1.49  --time_out_prep_mult                    0.1
% 7.35/1.49  --splitting_mode                        input
% 7.35/1.49  --splitting_grd                         true
% 7.35/1.49  --splitting_cvd                         false
% 7.35/1.49  --splitting_cvd_svl                     false
% 7.35/1.49  --splitting_nvd                         32
% 7.35/1.49  --sub_typing                            true
% 7.35/1.49  --prep_gs_sim                           true
% 7.35/1.49  --prep_unflatten                        true
% 7.35/1.49  --prep_res_sim                          true
% 7.35/1.49  --prep_upred                            true
% 7.35/1.49  --prep_sem_filter                       exhaustive
% 7.35/1.49  --prep_sem_filter_out                   false
% 7.35/1.49  --pred_elim                             true
% 7.35/1.49  --res_sim_input                         true
% 7.35/1.49  --eq_ax_congr_red                       true
% 7.35/1.49  --pure_diseq_elim                       true
% 7.35/1.49  --brand_transform                       false
% 7.35/1.49  --non_eq_to_eq                          false
% 7.35/1.49  --prep_def_merge                        true
% 7.35/1.49  --prep_def_merge_prop_impl              false
% 7.35/1.49  --prep_def_merge_mbd                    true
% 7.35/1.49  --prep_def_merge_tr_red                 false
% 7.35/1.49  --prep_def_merge_tr_cl                  false
% 7.35/1.49  --smt_preprocessing                     true
% 7.35/1.49  --smt_ac_axioms                         fast
% 7.35/1.49  --preprocessed_out                      false
% 7.35/1.49  --preprocessed_stats                    false
% 7.35/1.49  
% 7.35/1.49  ------ Abstraction refinement Options
% 7.35/1.49  
% 7.35/1.49  --abstr_ref                             []
% 7.35/1.49  --abstr_ref_prep                        false
% 7.35/1.49  --abstr_ref_until_sat                   false
% 7.35/1.49  --abstr_ref_sig_restrict                funpre
% 7.35/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.35/1.49  --abstr_ref_under                       []
% 7.35/1.49  
% 7.35/1.49  ------ SAT Options
% 7.35/1.49  
% 7.35/1.49  --sat_mode                              false
% 7.35/1.49  --sat_fm_restart_options                ""
% 7.35/1.49  --sat_gr_def                            false
% 7.35/1.49  --sat_epr_types                         true
% 7.35/1.49  --sat_non_cyclic_types                  false
% 7.35/1.49  --sat_finite_models                     false
% 7.35/1.49  --sat_fm_lemmas                         false
% 7.35/1.49  --sat_fm_prep                           false
% 7.35/1.49  --sat_fm_uc_incr                        true
% 7.35/1.49  --sat_out_model                         small
% 7.35/1.49  --sat_out_clauses                       false
% 7.35/1.49  
% 7.35/1.49  ------ QBF Options
% 7.35/1.49  
% 7.35/1.49  --qbf_mode                              false
% 7.35/1.49  --qbf_elim_univ                         false
% 7.35/1.49  --qbf_dom_inst                          none
% 7.35/1.49  --qbf_dom_pre_inst                      false
% 7.35/1.49  --qbf_sk_in                             false
% 7.35/1.49  --qbf_pred_elim                         true
% 7.35/1.49  --qbf_split                             512
% 7.35/1.49  
% 7.35/1.49  ------ BMC1 Options
% 7.35/1.49  
% 7.35/1.49  --bmc1_incremental                      false
% 7.35/1.49  --bmc1_axioms                           reachable_all
% 7.35/1.49  --bmc1_min_bound                        0
% 7.35/1.49  --bmc1_max_bound                        -1
% 7.35/1.49  --bmc1_max_bound_default                -1
% 7.35/1.49  --bmc1_symbol_reachability              true
% 7.35/1.49  --bmc1_property_lemmas                  false
% 7.35/1.49  --bmc1_k_induction                      false
% 7.35/1.49  --bmc1_non_equiv_states                 false
% 7.35/1.49  --bmc1_deadlock                         false
% 7.35/1.49  --bmc1_ucm                              false
% 7.35/1.49  --bmc1_add_unsat_core                   none
% 7.35/1.49  --bmc1_unsat_core_children              false
% 7.35/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.35/1.49  --bmc1_out_stat                         full
% 7.35/1.49  --bmc1_ground_init                      false
% 7.35/1.49  --bmc1_pre_inst_next_state              false
% 7.35/1.49  --bmc1_pre_inst_state                   false
% 7.35/1.49  --bmc1_pre_inst_reach_state             false
% 7.35/1.49  --bmc1_out_unsat_core                   false
% 7.35/1.49  --bmc1_aig_witness_out                  false
% 7.35/1.49  --bmc1_verbose                          false
% 7.35/1.49  --bmc1_dump_clauses_tptp                false
% 7.35/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.35/1.49  --bmc1_dump_file                        -
% 7.35/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.35/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.35/1.49  --bmc1_ucm_extend_mode                  1
% 7.35/1.49  --bmc1_ucm_init_mode                    2
% 7.35/1.49  --bmc1_ucm_cone_mode                    none
% 7.35/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.35/1.49  --bmc1_ucm_relax_model                  4
% 7.35/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.35/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.35/1.49  --bmc1_ucm_layered_model                none
% 7.35/1.49  --bmc1_ucm_max_lemma_size               10
% 7.35/1.49  
% 7.35/1.49  ------ AIG Options
% 7.35/1.49  
% 7.35/1.49  --aig_mode                              false
% 7.35/1.49  
% 7.35/1.49  ------ Instantiation Options
% 7.35/1.49  
% 7.35/1.49  --instantiation_flag                    true
% 7.35/1.49  --inst_sos_flag                         false
% 7.35/1.49  --inst_sos_phase                        true
% 7.35/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.35/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.35/1.49  --inst_lit_sel_side                     num_symb
% 7.35/1.49  --inst_solver_per_active                1400
% 7.35/1.49  --inst_solver_calls_frac                1.
% 7.35/1.49  --inst_passive_queue_type               priority_queues
% 7.35/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.35/1.49  --inst_passive_queues_freq              [25;2]
% 7.35/1.49  --inst_dismatching                      true
% 7.35/1.49  --inst_eager_unprocessed_to_passive     true
% 7.35/1.49  --inst_prop_sim_given                   true
% 7.35/1.49  --inst_prop_sim_new                     false
% 7.35/1.49  --inst_subs_new                         false
% 7.35/1.49  --inst_eq_res_simp                      false
% 7.35/1.49  --inst_subs_given                       false
% 7.35/1.49  --inst_orphan_elimination               true
% 7.35/1.49  --inst_learning_loop_flag               true
% 7.35/1.49  --inst_learning_start                   3000
% 7.35/1.49  --inst_learning_factor                  2
% 7.35/1.49  --inst_start_prop_sim_after_learn       3
% 7.35/1.49  --inst_sel_renew                        solver
% 7.35/1.49  --inst_lit_activity_flag                true
% 7.35/1.49  --inst_restr_to_given                   false
% 7.35/1.49  --inst_activity_threshold               500
% 7.35/1.49  --inst_out_proof                        true
% 7.35/1.49  
% 7.35/1.49  ------ Resolution Options
% 7.35/1.49  
% 7.35/1.49  --resolution_flag                       true
% 7.35/1.49  --res_lit_sel                           adaptive
% 7.35/1.49  --res_lit_sel_side                      none
% 7.35/1.49  --res_ordering                          kbo
% 7.35/1.49  --res_to_prop_solver                    active
% 7.35/1.49  --res_prop_simpl_new                    false
% 7.35/1.49  --res_prop_simpl_given                  true
% 7.35/1.49  --res_passive_queue_type                priority_queues
% 7.35/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.35/1.49  --res_passive_queues_freq               [15;5]
% 7.35/1.49  --res_forward_subs                      full
% 7.35/1.49  --res_backward_subs                     full
% 7.35/1.49  --res_forward_subs_resolution           true
% 7.35/1.49  --res_backward_subs_resolution          true
% 7.35/1.49  --res_orphan_elimination                true
% 7.35/1.49  --res_time_limit                        2.
% 7.35/1.49  --res_out_proof                         true
% 7.35/1.49  
% 7.35/1.49  ------ Superposition Options
% 7.35/1.49  
% 7.35/1.49  --superposition_flag                    true
% 7.35/1.49  --sup_passive_queue_type                priority_queues
% 7.35/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.35/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.35/1.49  --demod_completeness_check              fast
% 7.35/1.49  --demod_use_ground                      true
% 7.35/1.49  --sup_to_prop_solver                    passive
% 7.35/1.49  --sup_prop_simpl_new                    true
% 7.35/1.49  --sup_prop_simpl_given                  true
% 7.35/1.49  --sup_fun_splitting                     false
% 7.35/1.49  --sup_smt_interval                      50000
% 7.35/1.49  
% 7.35/1.49  ------ Superposition Simplification Setup
% 7.35/1.49  
% 7.35/1.49  --sup_indices_passive                   []
% 7.35/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.35/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.35/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.35/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.35/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.35/1.49  --sup_full_bw                           [BwDemod]
% 7.35/1.49  --sup_immed_triv                        [TrivRules]
% 7.35/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.35/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.35/1.49  --sup_immed_bw_main                     []
% 7.35/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.35/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.35/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.35/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.35/1.49  
% 7.35/1.49  ------ Combination Options
% 7.35/1.49  
% 7.35/1.49  --comb_res_mult                         3
% 7.35/1.49  --comb_sup_mult                         2
% 7.35/1.49  --comb_inst_mult                        10
% 7.35/1.49  
% 7.35/1.49  ------ Debug Options
% 7.35/1.49  
% 7.35/1.49  --dbg_backtrace                         false
% 7.35/1.49  --dbg_dump_prop_clauses                 false
% 7.35/1.49  --dbg_dump_prop_clauses_file            -
% 7.35/1.49  --dbg_out_stat                          false
% 7.35/1.49  ------ Parsing...
% 7.35/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.35/1.49  
% 7.35/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 7.35/1.49  
% 7.35/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.35/1.49  
% 7.35/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.35/1.49  ------ Proving...
% 7.35/1.49  ------ Problem Properties 
% 7.35/1.49  
% 7.35/1.49  
% 7.35/1.49  clauses                                 31
% 7.35/1.49  conjectures                             2
% 7.35/1.49  EPR                                     4
% 7.35/1.49  Horn                                    23
% 7.35/1.49  unary                                   7
% 7.35/1.49  binary                                  8
% 7.35/1.49  lits                                    79
% 7.35/1.49  lits eq                                 38
% 7.35/1.49  fd_pure                                 0
% 7.35/1.49  fd_pseudo                               0
% 7.35/1.49  fd_cond                                 3
% 7.35/1.49  fd_pseudo_cond                          6
% 7.35/1.49  AC symbols                              0
% 7.35/1.49  
% 7.35/1.49  ------ Schedule dynamic 5 is on 
% 7.35/1.49  
% 7.35/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.35/1.49  
% 7.35/1.49  
% 7.35/1.49  ------ 
% 7.35/1.49  Current options:
% 7.35/1.49  ------ 
% 7.35/1.49  
% 7.35/1.49  ------ Input Options
% 7.35/1.49  
% 7.35/1.49  --out_options                           all
% 7.35/1.49  --tptp_safe_out                         true
% 7.35/1.49  --problem_path                          ""
% 7.35/1.49  --include_path                          ""
% 7.35/1.49  --clausifier                            res/vclausify_rel
% 7.35/1.49  --clausifier_options                    --mode clausify
% 7.35/1.49  --stdin                                 false
% 7.35/1.49  --stats_out                             all
% 7.35/1.49  
% 7.35/1.49  ------ General Options
% 7.35/1.49  
% 7.35/1.49  --fof                                   false
% 7.35/1.49  --time_out_real                         305.
% 7.35/1.49  --time_out_virtual                      -1.
% 7.35/1.49  --symbol_type_check                     false
% 7.35/1.49  --clausify_out                          false
% 7.35/1.49  --sig_cnt_out                           false
% 7.35/1.49  --trig_cnt_out                          false
% 7.35/1.49  --trig_cnt_out_tolerance                1.
% 7.35/1.49  --trig_cnt_out_sk_spl                   false
% 7.35/1.49  --abstr_cl_out                          false
% 7.35/1.49  
% 7.35/1.49  ------ Global Options
% 7.35/1.49  
% 7.35/1.49  --schedule                              default
% 7.35/1.49  --add_important_lit                     false
% 7.35/1.49  --prop_solver_per_cl                    1000
% 7.35/1.49  --min_unsat_core                        false
% 7.35/1.49  --soft_assumptions                      false
% 7.35/1.49  --soft_lemma_size                       3
% 7.35/1.49  --prop_impl_unit_size                   0
% 7.35/1.49  --prop_impl_unit                        []
% 7.35/1.49  --share_sel_clauses                     true
% 7.35/1.49  --reset_solvers                         false
% 7.35/1.49  --bc_imp_inh                            [conj_cone]
% 7.35/1.49  --conj_cone_tolerance                   3.
% 7.35/1.49  --extra_neg_conj                        none
% 7.35/1.49  --large_theory_mode                     true
% 7.35/1.49  --prolific_symb_bound                   200
% 7.35/1.49  --lt_threshold                          2000
% 7.35/1.49  --clause_weak_htbl                      true
% 7.35/1.49  --gc_record_bc_elim                     false
% 7.35/1.49  
% 7.35/1.49  ------ Preprocessing Options
% 7.35/1.49  
% 7.35/1.49  --preprocessing_flag                    true
% 7.35/1.49  --time_out_prep_mult                    0.1
% 7.35/1.49  --splitting_mode                        input
% 7.35/1.49  --splitting_grd                         true
% 7.35/1.49  --splitting_cvd                         false
% 7.35/1.49  --splitting_cvd_svl                     false
% 7.35/1.49  --splitting_nvd                         32
% 7.35/1.49  --sub_typing                            true
% 7.35/1.49  --prep_gs_sim                           true
% 7.35/1.49  --prep_unflatten                        true
% 7.35/1.49  --prep_res_sim                          true
% 7.35/1.49  --prep_upred                            true
% 7.35/1.49  --prep_sem_filter                       exhaustive
% 7.35/1.49  --prep_sem_filter_out                   false
% 7.35/1.49  --pred_elim                             true
% 7.35/1.49  --res_sim_input                         true
% 7.35/1.49  --eq_ax_congr_red                       true
% 7.35/1.49  --pure_diseq_elim                       true
% 7.35/1.49  --brand_transform                       false
% 7.35/1.49  --non_eq_to_eq                          false
% 7.35/1.49  --prep_def_merge                        true
% 7.35/1.49  --prep_def_merge_prop_impl              false
% 7.35/1.49  --prep_def_merge_mbd                    true
% 7.35/1.49  --prep_def_merge_tr_red                 false
% 7.35/1.49  --prep_def_merge_tr_cl                  false
% 7.35/1.49  --smt_preprocessing                     true
% 7.35/1.49  --smt_ac_axioms                         fast
% 7.35/1.49  --preprocessed_out                      false
% 7.35/1.49  --preprocessed_stats                    false
% 7.35/1.49  
% 7.35/1.49  ------ Abstraction refinement Options
% 7.35/1.49  
% 7.35/1.49  --abstr_ref                             []
% 7.35/1.49  --abstr_ref_prep                        false
% 7.35/1.49  --abstr_ref_until_sat                   false
% 7.35/1.49  --abstr_ref_sig_restrict                funpre
% 7.35/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.35/1.49  --abstr_ref_under                       []
% 7.35/1.49  
% 7.35/1.49  ------ SAT Options
% 7.35/1.49  
% 7.35/1.49  --sat_mode                              false
% 7.35/1.49  --sat_fm_restart_options                ""
% 7.35/1.49  --sat_gr_def                            false
% 7.35/1.49  --sat_epr_types                         true
% 7.35/1.49  --sat_non_cyclic_types                  false
% 7.35/1.49  --sat_finite_models                     false
% 7.35/1.49  --sat_fm_lemmas                         false
% 7.35/1.49  --sat_fm_prep                           false
% 7.35/1.49  --sat_fm_uc_incr                        true
% 7.35/1.49  --sat_out_model                         small
% 7.35/1.49  --sat_out_clauses                       false
% 7.35/1.49  
% 7.35/1.49  ------ QBF Options
% 7.35/1.49  
% 7.35/1.49  --qbf_mode                              false
% 7.35/1.49  --qbf_elim_univ                         false
% 7.35/1.49  --qbf_dom_inst                          none
% 7.35/1.49  --qbf_dom_pre_inst                      false
% 7.35/1.49  --qbf_sk_in                             false
% 7.35/1.49  --qbf_pred_elim                         true
% 7.35/1.49  --qbf_split                             512
% 7.35/1.49  
% 7.35/1.49  ------ BMC1 Options
% 7.35/1.49  
% 7.35/1.49  --bmc1_incremental                      false
% 7.35/1.49  --bmc1_axioms                           reachable_all
% 7.35/1.49  --bmc1_min_bound                        0
% 7.35/1.49  --bmc1_max_bound                        -1
% 7.35/1.49  --bmc1_max_bound_default                -1
% 7.35/1.49  --bmc1_symbol_reachability              true
% 7.35/1.49  --bmc1_property_lemmas                  false
% 7.35/1.49  --bmc1_k_induction                      false
% 7.35/1.49  --bmc1_non_equiv_states                 false
% 7.35/1.49  --bmc1_deadlock                         false
% 7.35/1.49  --bmc1_ucm                              false
% 7.35/1.49  --bmc1_add_unsat_core                   none
% 7.35/1.49  --bmc1_unsat_core_children              false
% 7.35/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.35/1.49  --bmc1_out_stat                         full
% 7.35/1.49  --bmc1_ground_init                      false
% 7.35/1.49  --bmc1_pre_inst_next_state              false
% 7.35/1.49  --bmc1_pre_inst_state                   false
% 7.35/1.49  --bmc1_pre_inst_reach_state             false
% 7.35/1.49  --bmc1_out_unsat_core                   false
% 7.35/1.49  --bmc1_aig_witness_out                  false
% 7.35/1.49  --bmc1_verbose                          false
% 7.35/1.49  --bmc1_dump_clauses_tptp                false
% 7.35/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.35/1.49  --bmc1_dump_file                        -
% 7.35/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.35/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.35/1.49  --bmc1_ucm_extend_mode                  1
% 7.35/1.49  --bmc1_ucm_init_mode                    2
% 7.35/1.49  --bmc1_ucm_cone_mode                    none
% 7.35/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.35/1.49  --bmc1_ucm_relax_model                  4
% 7.35/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.35/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.35/1.49  --bmc1_ucm_layered_model                none
% 7.35/1.49  --bmc1_ucm_max_lemma_size               10
% 7.35/1.49  
% 7.35/1.49  ------ AIG Options
% 7.35/1.49  
% 7.35/1.49  --aig_mode                              false
% 7.35/1.49  
% 7.35/1.49  ------ Instantiation Options
% 7.35/1.49  
% 7.35/1.49  --instantiation_flag                    true
% 7.35/1.49  --inst_sos_flag                         false
% 7.35/1.49  --inst_sos_phase                        true
% 7.35/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.35/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.35/1.49  --inst_lit_sel_side                     none
% 7.35/1.49  --inst_solver_per_active                1400
% 7.35/1.49  --inst_solver_calls_frac                1.
% 7.35/1.49  --inst_passive_queue_type               priority_queues
% 7.35/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.35/1.49  --inst_passive_queues_freq              [25;2]
% 7.35/1.49  --inst_dismatching                      true
% 7.35/1.49  --inst_eager_unprocessed_to_passive     true
% 7.35/1.49  --inst_prop_sim_given                   true
% 7.35/1.49  --inst_prop_sim_new                     false
% 7.35/1.49  --inst_subs_new                         false
% 7.35/1.49  --inst_eq_res_simp                      false
% 7.35/1.49  --inst_subs_given                       false
% 7.35/1.49  --inst_orphan_elimination               true
% 7.35/1.49  --inst_learning_loop_flag               true
% 7.35/1.49  --inst_learning_start                   3000
% 7.35/1.49  --inst_learning_factor                  2
% 7.35/1.49  --inst_start_prop_sim_after_learn       3
% 7.35/1.49  --inst_sel_renew                        solver
% 7.35/1.49  --inst_lit_activity_flag                true
% 7.35/1.49  --inst_restr_to_given                   false
% 7.35/1.49  --inst_activity_threshold               500
% 7.35/1.49  --inst_out_proof                        true
% 7.35/1.49  
% 7.35/1.49  ------ Resolution Options
% 7.35/1.49  
% 7.35/1.49  --resolution_flag                       false
% 7.35/1.49  --res_lit_sel                           adaptive
% 7.35/1.49  --res_lit_sel_side                      none
% 7.35/1.49  --res_ordering                          kbo
% 7.35/1.49  --res_to_prop_solver                    active
% 7.35/1.49  --res_prop_simpl_new                    false
% 7.35/1.49  --res_prop_simpl_given                  true
% 7.35/1.49  --res_passive_queue_type                priority_queues
% 7.35/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.35/1.49  --res_passive_queues_freq               [15;5]
% 7.35/1.49  --res_forward_subs                      full
% 7.35/1.49  --res_backward_subs                     full
% 7.35/1.49  --res_forward_subs_resolution           true
% 7.35/1.49  --res_backward_subs_resolution          true
% 7.35/1.49  --res_orphan_elimination                true
% 7.35/1.49  --res_time_limit                        2.
% 7.35/1.49  --res_out_proof                         true
% 7.35/1.49  
% 7.35/1.49  ------ Superposition Options
% 7.35/1.49  
% 7.35/1.49  --superposition_flag                    true
% 7.35/1.49  --sup_passive_queue_type                priority_queues
% 7.35/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.35/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.35/1.49  --demod_completeness_check              fast
% 7.35/1.49  --demod_use_ground                      true
% 7.35/1.49  --sup_to_prop_solver                    passive
% 7.35/1.49  --sup_prop_simpl_new                    true
% 7.35/1.49  --sup_prop_simpl_given                  true
% 7.35/1.49  --sup_fun_splitting                     false
% 7.35/1.49  --sup_smt_interval                      50000
% 7.35/1.49  
% 7.35/1.49  ------ Superposition Simplification Setup
% 7.35/1.49  
% 7.35/1.49  --sup_indices_passive                   []
% 7.35/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.35/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.35/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.35/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.35/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.35/1.49  --sup_full_bw                           [BwDemod]
% 7.35/1.49  --sup_immed_triv                        [TrivRules]
% 7.35/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.35/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.35/1.49  --sup_immed_bw_main                     []
% 7.35/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.35/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.35/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.35/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.35/1.49  
% 7.35/1.49  ------ Combination Options
% 7.35/1.49  
% 7.35/1.49  --comb_res_mult                         3
% 7.35/1.49  --comb_sup_mult                         2
% 7.35/1.49  --comb_inst_mult                        10
% 7.35/1.49  
% 7.35/1.49  ------ Debug Options
% 7.35/1.49  
% 7.35/1.49  --dbg_backtrace                         false
% 7.35/1.49  --dbg_dump_prop_clauses                 false
% 7.35/1.49  --dbg_dump_prop_clauses_file            -
% 7.35/1.49  --dbg_out_stat                          false
% 7.35/1.49  
% 7.35/1.49  
% 7.35/1.49  
% 7.35/1.49  
% 7.35/1.49  ------ Proving...
% 7.35/1.49  
% 7.35/1.49  
% 7.35/1.49  % SZS status Theorem for theBenchmark.p
% 7.35/1.49  
% 7.35/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.35/1.49  
% 7.35/1.49  fof(f15,conjecture,(
% 7.35/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 7.35/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.35/1.49  
% 7.35/1.49  fof(f16,negated_conjecture,(
% 7.35/1.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 7.35/1.49    inference(negated_conjecture,[],[f15])).
% 7.35/1.49  
% 7.35/1.49  fof(f29,plain,(
% 7.35/1.49    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 7.35/1.49    inference(ennf_transformation,[],[f16])).
% 7.35/1.49  
% 7.35/1.49  fof(f30,plain,(
% 7.35/1.49    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 7.35/1.49    inference(flattening,[],[f29])).
% 7.35/1.49  
% 7.35/1.49  fof(f52,plain,(
% 7.35/1.49    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (k1_funct_1(sK9,sK8) != sK7 & r2_hidden(sK8,sK6) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7)))) & v1_funct_2(sK9,sK6,k1_tarski(sK7)) & v1_funct_1(sK9))),
% 7.35/1.49    introduced(choice_axiom,[])).
% 7.35/1.49  
% 7.35/1.49  fof(f53,plain,(
% 7.35/1.49    k1_funct_1(sK9,sK8) != sK7 & r2_hidden(sK8,sK6) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7)))) & v1_funct_2(sK9,sK6,k1_tarski(sK7)) & v1_funct_1(sK9)),
% 7.35/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f30,f52])).
% 7.35/1.49  
% 7.35/1.49  fof(f94,plain,(
% 7.35/1.49    r2_hidden(sK8,sK6)),
% 7.35/1.49    inference(cnf_transformation,[],[f53])).
% 7.35/1.49  
% 7.35/1.49  fof(f8,axiom,(
% 7.35/1.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 7.35/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.35/1.49  
% 7.35/1.49  fof(f20,plain,(
% 7.35/1.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.35/1.49    inference(ennf_transformation,[],[f8])).
% 7.35/1.49  
% 7.35/1.49  fof(f44,plain,(
% 7.35/1.49    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.35/1.49    inference(nnf_transformation,[],[f20])).
% 7.35/1.49  
% 7.35/1.49  fof(f73,plain,(
% 7.35/1.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.35/1.49    inference(cnf_transformation,[],[f44])).
% 7.35/1.49  
% 7.35/1.49  fof(f12,axiom,(
% 7.35/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.35/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.35/1.49  
% 7.35/1.49  fof(f17,plain,(
% 7.35/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 7.35/1.49    inference(pure_predicate_removal,[],[f12])).
% 7.35/1.49  
% 7.35/1.49  fof(f25,plain,(
% 7.35/1.49    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.35/1.49    inference(ennf_transformation,[],[f17])).
% 7.35/1.49  
% 7.35/1.49  fof(f83,plain,(
% 7.35/1.49    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.35/1.49    inference(cnf_transformation,[],[f25])).
% 7.35/1.49  
% 7.35/1.49  fof(f11,axiom,(
% 7.35/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.35/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.35/1.49  
% 7.35/1.49  fof(f24,plain,(
% 7.35/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.35/1.49    inference(ennf_transformation,[],[f11])).
% 7.35/1.49  
% 7.35/1.49  fof(f82,plain,(
% 7.35/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.35/1.49    inference(cnf_transformation,[],[f24])).
% 7.35/1.49  
% 7.35/1.49  fof(f93,plain,(
% 7.35/1.49    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7))))),
% 7.35/1.49    inference(cnf_transformation,[],[f53])).
% 7.35/1.49  
% 7.35/1.49  fof(f5,axiom,(
% 7.35/1.49    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 7.35/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.35/1.49  
% 7.35/1.49  fof(f70,plain,(
% 7.35/1.49    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 7.35/1.49    inference(cnf_transformation,[],[f5])).
% 7.35/1.49  
% 7.35/1.49  fof(f6,axiom,(
% 7.35/1.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.35/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.35/1.49  
% 7.35/1.49  fof(f71,plain,(
% 7.35/1.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.35/1.49    inference(cnf_transformation,[],[f6])).
% 7.35/1.49  
% 7.35/1.49  fof(f7,axiom,(
% 7.35/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.35/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.35/1.49  
% 7.35/1.49  fof(f72,plain,(
% 7.35/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.35/1.49    inference(cnf_transformation,[],[f7])).
% 7.35/1.49  
% 7.35/1.49  fof(f96,plain,(
% 7.35/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.35/1.49    inference(definition_unfolding,[],[f71,f72])).
% 7.35/1.49  
% 7.35/1.49  fof(f97,plain,(
% 7.35/1.49    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 7.35/1.49    inference(definition_unfolding,[],[f70,f96])).
% 7.35/1.49  
% 7.35/1.49  fof(f110,plain,(
% 7.35/1.49    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))))),
% 7.35/1.49    inference(definition_unfolding,[],[f93,f97])).
% 7.35/1.49  
% 7.35/1.49  fof(f9,axiom,(
% 7.35/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 7.35/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.35/1.49  
% 7.35/1.49  fof(f21,plain,(
% 7.35/1.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.35/1.49    inference(ennf_transformation,[],[f9])).
% 7.35/1.49  
% 7.35/1.49  fof(f22,plain,(
% 7.35/1.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.35/1.49    inference(flattening,[],[f21])).
% 7.35/1.49  
% 7.35/1.49  fof(f45,plain,(
% 7.35/1.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.35/1.49    inference(nnf_transformation,[],[f22])).
% 7.35/1.49  
% 7.35/1.49  fof(f46,plain,(
% 7.35/1.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.35/1.49    inference(rectify,[],[f45])).
% 7.35/1.49  
% 7.35/1.49  fof(f49,plain,(
% 7.35/1.49    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))))),
% 7.35/1.49    introduced(choice_axiom,[])).
% 7.35/1.49  
% 7.35/1.49  fof(f48,plain,(
% 7.35/1.49    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1)) = X2 & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))) )),
% 7.35/1.49    introduced(choice_axiom,[])).
% 7.35/1.49  
% 7.35/1.49  fof(f47,plain,(
% 7.35/1.49    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK3(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1))))),
% 7.35/1.49    introduced(choice_axiom,[])).
% 7.35/1.49  
% 7.35/1.49  fof(f50,plain,(
% 7.35/1.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & ((k1_funct_1(X0,sK4(X0,X1)) = sK3(X0,X1) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.35/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f46,f49,f48,f47])).
% 7.35/1.49  
% 7.35/1.49  fof(f77,plain,(
% 7.35/1.49    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.35/1.49    inference(cnf_transformation,[],[f50])).
% 7.35/1.49  
% 7.35/1.49  fof(f122,plain,(
% 7.35/1.49    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.35/1.49    inference(equality_resolution,[],[f77])).
% 7.35/1.49  
% 7.35/1.49  fof(f123,plain,(
% 7.35/1.49    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.35/1.49    inference(equality_resolution,[],[f122])).
% 7.35/1.49  
% 7.35/1.49  fof(f91,plain,(
% 7.35/1.49    v1_funct_1(sK9)),
% 7.35/1.49    inference(cnf_transformation,[],[f53])).
% 7.35/1.49  
% 7.35/1.49  fof(f1,axiom,(
% 7.35/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.35/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.35/1.49  
% 7.35/1.49  fof(f18,plain,(
% 7.35/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.35/1.49    inference(ennf_transformation,[],[f1])).
% 7.35/1.49  
% 7.35/1.49  fof(f31,plain,(
% 7.35/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.35/1.49    inference(nnf_transformation,[],[f18])).
% 7.35/1.49  
% 7.35/1.49  fof(f32,plain,(
% 7.35/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.35/1.49    inference(rectify,[],[f31])).
% 7.35/1.49  
% 7.35/1.49  fof(f33,plain,(
% 7.35/1.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.35/1.49    introduced(choice_axiom,[])).
% 7.35/1.49  
% 7.35/1.49  fof(f34,plain,(
% 7.35/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.35/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 7.35/1.49  
% 7.35/1.49  fof(f54,plain,(
% 7.35/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.35/1.49    inference(cnf_transformation,[],[f34])).
% 7.35/1.50  
% 7.35/1.50  fof(f4,axiom,(
% 7.35/1.50    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 7.35/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.35/1.50  
% 7.35/1.50  fof(f40,plain,(
% 7.35/1.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 7.35/1.50    inference(nnf_transformation,[],[f4])).
% 7.35/1.50  
% 7.35/1.50  fof(f41,plain,(
% 7.35/1.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.35/1.50    inference(rectify,[],[f40])).
% 7.35/1.50  
% 7.35/1.50  fof(f42,plain,(
% 7.35/1.50    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 7.35/1.50    introduced(choice_axiom,[])).
% 7.35/1.50  
% 7.35/1.50  fof(f43,plain,(
% 7.35/1.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.35/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).
% 7.35/1.50  
% 7.35/1.50  fof(f66,plain,(
% 7.35/1.50    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 7.35/1.50    inference(cnf_transformation,[],[f43])).
% 7.35/1.50  
% 7.35/1.50  fof(f109,plain,(
% 7.35/1.50    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 7.35/1.50    inference(definition_unfolding,[],[f66,f97])).
% 7.35/1.50  
% 7.35/1.50  fof(f121,plain,(
% 7.35/1.50    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 7.35/1.50    inference(equality_resolution,[],[f109])).
% 7.35/1.50  
% 7.35/1.50  fof(f92,plain,(
% 7.35/1.50    v1_funct_2(sK9,sK6,k1_tarski(sK7))),
% 7.35/1.50    inference(cnf_transformation,[],[f53])).
% 7.35/1.50  
% 7.35/1.50  fof(f111,plain,(
% 7.35/1.50    v1_funct_2(sK9,sK6,k2_enumset1(sK7,sK7,sK7,sK7))),
% 7.35/1.50    inference(definition_unfolding,[],[f92,f97])).
% 7.35/1.50  
% 7.35/1.50  fof(f14,axiom,(
% 7.35/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.35/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.35/1.50  
% 7.35/1.50  fof(f27,plain,(
% 7.35/1.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.35/1.50    inference(ennf_transformation,[],[f14])).
% 7.35/1.50  
% 7.35/1.50  fof(f28,plain,(
% 7.35/1.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.35/1.50    inference(flattening,[],[f27])).
% 7.35/1.50  
% 7.35/1.50  fof(f51,plain,(
% 7.35/1.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.35/1.50    inference(nnf_transformation,[],[f28])).
% 7.35/1.50  
% 7.35/1.50  fof(f85,plain,(
% 7.35/1.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.35/1.50    inference(cnf_transformation,[],[f51])).
% 7.35/1.50  
% 7.35/1.50  fof(f13,axiom,(
% 7.35/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.35/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.35/1.50  
% 7.35/1.50  fof(f26,plain,(
% 7.35/1.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.35/1.50    inference(ennf_transformation,[],[f13])).
% 7.35/1.50  
% 7.35/1.50  fof(f84,plain,(
% 7.35/1.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.35/1.50    inference(cnf_transformation,[],[f26])).
% 7.35/1.50  
% 7.35/1.50  fof(f3,axiom,(
% 7.35/1.50    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 7.35/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.35/1.50  
% 7.35/1.50  fof(f19,plain,(
% 7.35/1.50    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 7.35/1.50    inference(ennf_transformation,[],[f3])).
% 7.35/1.50  
% 7.35/1.50  fof(f35,plain,(
% 7.35/1.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.35/1.50    inference(nnf_transformation,[],[f19])).
% 7.35/1.50  
% 7.35/1.50  fof(f36,plain,(
% 7.35/1.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.35/1.50    inference(flattening,[],[f35])).
% 7.35/1.50  
% 7.35/1.50  fof(f37,plain,(
% 7.35/1.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.35/1.50    inference(rectify,[],[f36])).
% 7.35/1.50  
% 7.35/1.50  fof(f38,plain,(
% 7.35/1.50    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 7.35/1.50    introduced(choice_axiom,[])).
% 7.35/1.50  
% 7.35/1.50  fof(f39,plain,(
% 7.35/1.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.35/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).
% 7.35/1.50  
% 7.35/1.50  fof(f59,plain,(
% 7.35/1.50    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 7.35/1.50    inference(cnf_transformation,[],[f39])).
% 7.35/1.50  
% 7.35/1.50  fof(f104,plain,(
% 7.35/1.50    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 7.35/1.50    inference(definition_unfolding,[],[f59,f72])).
% 7.35/1.50  
% 7.35/1.50  fof(f116,plain,(
% 7.35/1.50    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X5,X5,X1,X2) != X3) )),
% 7.35/1.50    inference(equality_resolution,[],[f104])).
% 7.35/1.50  
% 7.35/1.50  fof(f117,plain,(
% 7.35/1.50    ( ! [X2,X5,X1] : (r2_hidden(X5,k2_enumset1(X5,X5,X1,X2))) )),
% 7.35/1.50    inference(equality_resolution,[],[f116])).
% 7.35/1.50  
% 7.35/1.50  fof(f10,axiom,(
% 7.35/1.50    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 7.35/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.35/1.50  
% 7.35/1.50  fof(f23,plain,(
% 7.35/1.50    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 7.35/1.50    inference(ennf_transformation,[],[f10])).
% 7.35/1.50  
% 7.35/1.50  fof(f81,plain,(
% 7.35/1.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 7.35/1.50    inference(cnf_transformation,[],[f23])).
% 7.35/1.50  
% 7.35/1.50  fof(f2,axiom,(
% 7.35/1.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.35/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.35/1.50  
% 7.35/1.50  fof(f57,plain,(
% 7.35/1.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.35/1.50    inference(cnf_transformation,[],[f2])).
% 7.35/1.50  
% 7.35/1.50  fof(f95,plain,(
% 7.35/1.50    k1_funct_1(sK9,sK8) != sK7),
% 7.35/1.50    inference(cnf_transformation,[],[f53])).
% 7.35/1.50  
% 7.35/1.50  cnf(c_35,negated_conjecture,
% 7.35/1.50      ( r2_hidden(sK8,sK6) ),
% 7.35/1.50      inference(cnf_transformation,[],[f94]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_1962,plain,
% 7.35/1.50      ( r2_hidden(sK8,sK6) = iProver_top ),
% 7.35/1.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_17,plain,
% 7.35/1.50      ( ~ v5_relat_1(X0,X1)
% 7.35/1.50      | r1_tarski(k2_relat_1(X0),X1)
% 7.35/1.50      | ~ v1_relat_1(X0) ),
% 7.35/1.50      inference(cnf_transformation,[],[f73]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_26,plain,
% 7.35/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.35/1.50      | v5_relat_1(X0,X2) ),
% 7.35/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_414,plain,
% 7.35/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.35/1.50      | r1_tarski(k2_relat_1(X3),X4)
% 7.35/1.50      | ~ v1_relat_1(X3)
% 7.35/1.50      | X0 != X3
% 7.35/1.50      | X2 != X4 ),
% 7.35/1.50      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_415,plain,
% 7.35/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.35/1.50      | r1_tarski(k2_relat_1(X0),X2)
% 7.35/1.50      | ~ v1_relat_1(X0) ),
% 7.35/1.50      inference(unflattening,[status(thm)],[c_414]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_25,plain,
% 7.35/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.35/1.50      | v1_relat_1(X0) ),
% 7.35/1.50      inference(cnf_transformation,[],[f82]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_419,plain,
% 7.35/1.50      ( r1_tarski(k2_relat_1(X0),X2)
% 7.35/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.35/1.50      inference(global_propositional_subsumption,
% 7.35/1.50                [status(thm)],
% 7.35/1.50                [c_415,c_25]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_420,plain,
% 7.35/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.35/1.50      | r1_tarski(k2_relat_1(X0),X2) ),
% 7.35/1.50      inference(renaming,[status(thm)],[c_419]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_36,negated_conjecture,
% 7.35/1.50      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) ),
% 7.35/1.50      inference(cnf_transformation,[],[f110]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_547,plain,
% 7.35/1.50      ( r1_tarski(k2_relat_1(X0),X1)
% 7.35/1.50      | k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))) != k1_zfmisc_1(k2_zfmisc_1(X2,X1))
% 7.35/1.50      | sK9 != X0 ),
% 7.35/1.50      inference(resolution_lifted,[status(thm)],[c_420,c_36]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_548,plain,
% 7.35/1.50      ( r1_tarski(k2_relat_1(sK9),X0)
% 7.35/1.50      | k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0)) ),
% 7.35/1.50      inference(unflattening,[status(thm)],[c_547]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_1961,plain,
% 7.35/1.50      ( k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 7.35/1.50      | r1_tarski(k2_relat_1(sK9),X1) = iProver_top ),
% 7.35/1.50      inference(predicate_to_equality,[status(thm)],[c_548]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_2569,plain,
% 7.35/1.50      ( r1_tarski(k2_relat_1(sK9),k2_enumset1(sK7,sK7,sK7,sK7)) = iProver_top ),
% 7.35/1.50      inference(equality_resolution,[status(thm)],[c_1961]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_21,plain,
% 7.35/1.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.35/1.50      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 7.35/1.50      | ~ v1_funct_1(X1)
% 7.35/1.50      | ~ v1_relat_1(X1) ),
% 7.35/1.50      inference(cnf_transformation,[],[f123]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_38,negated_conjecture,
% 7.35/1.50      ( v1_funct_1(sK9) ),
% 7.35/1.50      inference(cnf_transformation,[],[f91]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_885,plain,
% 7.35/1.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.35/1.50      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 7.35/1.50      | ~ v1_relat_1(X1)
% 7.35/1.50      | sK9 != X1 ),
% 7.35/1.50      inference(resolution_lifted,[status(thm)],[c_21,c_38]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_886,plain,
% 7.35/1.50      ( ~ r2_hidden(X0,k1_relat_1(sK9))
% 7.35/1.50      | r2_hidden(k1_funct_1(sK9,X0),k2_relat_1(sK9))
% 7.35/1.50      | ~ v1_relat_1(sK9) ),
% 7.35/1.50      inference(unflattening,[status(thm)],[c_885]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_1955,plain,
% 7.35/1.50      ( r2_hidden(X0,k1_relat_1(sK9)) != iProver_top
% 7.35/1.50      | r2_hidden(k1_funct_1(sK9,X0),k2_relat_1(sK9)) = iProver_top
% 7.35/1.50      | v1_relat_1(sK9) != iProver_top ),
% 7.35/1.50      inference(predicate_to_equality,[status(thm)],[c_886]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_887,plain,
% 7.35/1.50      ( r2_hidden(X0,k1_relat_1(sK9)) != iProver_top
% 7.35/1.50      | r2_hidden(k1_funct_1(sK9,X0),k2_relat_1(sK9)) = iProver_top
% 7.35/1.50      | v1_relat_1(sK9) != iProver_top ),
% 7.35/1.50      inference(predicate_to_equality,[status(thm)],[c_886]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_604,plain,
% 7.35/1.50      ( v1_relat_1(X0)
% 7.35/1.50      | k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 7.35/1.50      | sK9 != X0 ),
% 7.35/1.50      inference(resolution_lifted,[status(thm)],[c_25,c_36]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_605,plain,
% 7.35/1.50      ( v1_relat_1(sK9)
% 7.35/1.50      | k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 7.35/1.50      inference(unflattening,[status(thm)],[c_604]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_1960,plain,
% 7.35/1.50      ( k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 7.35/1.50      | v1_relat_1(sK9) = iProver_top ),
% 7.35/1.50      inference(predicate_to_equality,[status(thm)],[c_605]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_2309,plain,
% 7.35/1.50      ( v1_relat_1(sK9) = iProver_top ),
% 7.35/1.50      inference(equality_resolution,[status(thm)],[c_1960]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_2689,plain,
% 7.35/1.50      ( r2_hidden(k1_funct_1(sK9,X0),k2_relat_1(sK9)) = iProver_top
% 7.35/1.50      | r2_hidden(X0,k1_relat_1(sK9)) != iProver_top ),
% 7.35/1.50      inference(global_propositional_subsumption,
% 7.35/1.50                [status(thm)],
% 7.35/1.50                [c_1955,c_887,c_2309]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_2690,plain,
% 7.35/1.50      ( r2_hidden(X0,k1_relat_1(sK9)) != iProver_top
% 7.35/1.50      | r2_hidden(k1_funct_1(sK9,X0),k2_relat_1(sK9)) = iProver_top ),
% 7.35/1.50      inference(renaming,[status(thm)],[c_2689]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_2,plain,
% 7.35/1.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.35/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_1977,plain,
% 7.35/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.35/1.50      | r2_hidden(X0,X2) = iProver_top
% 7.35/1.50      | r1_tarski(X1,X2) != iProver_top ),
% 7.35/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_3428,plain,
% 7.35/1.50      ( r2_hidden(X0,k1_relat_1(sK9)) != iProver_top
% 7.35/1.50      | r2_hidden(k1_funct_1(sK9,X0),X1) = iProver_top
% 7.35/1.50      | r1_tarski(k2_relat_1(sK9),X1) != iProver_top ),
% 7.35/1.50      inference(superposition,[status(thm)],[c_2690,c_1977]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_15,plain,
% 7.35/1.50      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 7.35/1.50      inference(cnf_transformation,[],[f121]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_1964,plain,
% 7.35/1.50      ( X0 = X1 | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
% 7.35/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_4758,plain,
% 7.35/1.50      ( k1_funct_1(sK9,X0) = X1
% 7.35/1.50      | r2_hidden(X0,k1_relat_1(sK9)) != iProver_top
% 7.35/1.50      | r1_tarski(k2_relat_1(sK9),k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
% 7.35/1.50      inference(superposition,[status(thm)],[c_3428,c_1964]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_37,negated_conjecture,
% 7.35/1.50      ( v1_funct_2(sK9,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) ),
% 7.35/1.50      inference(cnf_transformation,[],[f111]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_33,plain,
% 7.35/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.35/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.35/1.50      | k1_relset_1(X1,X2,X0) = X1
% 7.35/1.50      | k1_xboole_0 = X2 ),
% 7.35/1.50      inference(cnf_transformation,[],[f85]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_559,plain,
% 7.35/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.35/1.50      | k1_relset_1(X1,X2,X0) = X1
% 7.35/1.50      | k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 7.35/1.50      | sK9 != X0
% 7.35/1.50      | k1_xboole_0 = X2 ),
% 7.35/1.50      inference(resolution_lifted,[status(thm)],[c_33,c_36]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_560,plain,
% 7.35/1.50      ( ~ v1_funct_2(sK9,X0,X1)
% 7.35/1.50      | k1_relset_1(X0,X1,sK9) = X0
% 7.35/1.50      | k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 7.35/1.50      | k1_xboole_0 = X1 ),
% 7.35/1.50      inference(unflattening,[status(thm)],[c_559]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_1071,plain,
% 7.35/1.50      ( k2_enumset1(sK7,sK7,sK7,sK7) != X0
% 7.35/1.50      | k1_relset_1(X1,X0,sK9) = X1
% 7.35/1.50      | k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0))
% 7.35/1.50      | sK6 != X1
% 7.35/1.50      | sK9 != sK9
% 7.35/1.50      | k1_xboole_0 = X0 ),
% 7.35/1.50      inference(resolution_lifted,[status(thm)],[c_37,c_560]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_1072,plain,
% 7.35/1.50      ( k1_relset_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = sK6
% 7.35/1.50      | k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))) != k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))
% 7.35/1.50      | k1_xboole_0 = k2_enumset1(sK7,sK7,sK7,sK7) ),
% 7.35/1.50      inference(unflattening,[status(thm)],[c_1071]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_1151,plain,
% 7.35/1.50      ( k1_relset_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = sK6
% 7.35/1.50      | k1_xboole_0 = k2_enumset1(sK7,sK7,sK7,sK7) ),
% 7.35/1.50      inference(equality_resolution_simp,[status(thm)],[c_1072]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_27,plain,
% 7.35/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.35/1.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.35/1.50      inference(cnf_transformation,[],[f84]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_595,plain,
% 7.35/1.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.35/1.50      | k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 7.35/1.50      | sK9 != X2 ),
% 7.35/1.50      inference(resolution_lifted,[status(thm)],[c_27,c_36]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_596,plain,
% 7.35/1.50      ( k1_relset_1(X0,X1,sK9) = k1_relat_1(sK9)
% 7.35/1.50      | k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 7.35/1.50      inference(unflattening,[status(thm)],[c_595]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_2208,plain,
% 7.35/1.50      ( k1_relset_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9) = k1_relat_1(sK9) ),
% 7.35/1.50      inference(equality_resolution,[status(thm)],[c_596]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_2354,plain,
% 7.35/1.50      ( k2_enumset1(sK7,sK7,sK7,sK7) = k1_xboole_0
% 7.35/1.50      | k1_relat_1(sK9) = sK6 ),
% 7.35/1.50      inference(demodulation,[status(thm)],[c_1151,c_2208]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_2358,plain,
% 7.35/1.50      ( k1_relset_1(sK6,k1_xboole_0,sK9) = k1_relat_1(sK9)
% 7.35/1.50      | k1_relat_1(sK9) = sK6 ),
% 7.35/1.50      inference(superposition,[status(thm)],[c_2354,c_2208]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_10,plain,
% 7.35/1.50      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
% 7.35/1.50      inference(cnf_transformation,[],[f117]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_1969,plain,
% 7.35/1.50      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
% 7.35/1.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_2514,plain,
% 7.35/1.50      ( k1_relat_1(sK9) = sK6
% 7.35/1.50      | r2_hidden(sK7,k1_xboole_0) = iProver_top ),
% 7.35/1.50      inference(superposition,[status(thm)],[c_2354,c_1969]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_24,plain,
% 7.35/1.50      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 7.35/1.50      inference(cnf_transformation,[],[f81]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_1963,plain,
% 7.35/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.35/1.50      | r1_tarski(X1,X0) != iProver_top ),
% 7.35/1.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_6288,plain,
% 7.35/1.50      ( k1_relat_1(sK9) = sK6
% 7.35/1.50      | r1_tarski(k1_xboole_0,sK7) != iProver_top ),
% 7.35/1.50      inference(superposition,[status(thm)],[c_2514,c_1963]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_6300,plain,
% 7.35/1.50      ( ~ r1_tarski(k1_xboole_0,sK7) | k1_relat_1(sK9) = sK6 ),
% 7.35/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_6288]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_3,plain,
% 7.35/1.50      ( r1_tarski(k1_xboole_0,X0) ),
% 7.35/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_6310,plain,
% 7.35/1.50      ( r1_tarski(k1_xboole_0,sK7) ),
% 7.35/1.50      inference(instantiation,[status(thm)],[c_3]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_7863,plain,
% 7.35/1.50      ( k1_relat_1(sK9) = sK6 ),
% 7.35/1.50      inference(global_propositional_subsumption,
% 7.35/1.50                [status(thm)],
% 7.35/1.50                [c_2358,c_6300,c_6310]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_22262,plain,
% 7.35/1.50      ( k1_funct_1(sK9,X0) = X1
% 7.35/1.50      | r2_hidden(X0,sK6) != iProver_top
% 7.35/1.50      | r1_tarski(k2_relat_1(sK9),k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
% 7.35/1.50      inference(light_normalisation,[status(thm)],[c_4758,c_7863]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_22270,plain,
% 7.35/1.50      ( k1_funct_1(sK9,X0) = sK7 | r2_hidden(X0,sK6) != iProver_top ),
% 7.35/1.50      inference(superposition,[status(thm)],[c_2569,c_22262]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_23382,plain,
% 7.35/1.50      ( k1_funct_1(sK9,sK8) = sK7 ),
% 7.35/1.50      inference(superposition,[status(thm)],[c_1962,c_22270]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_34,negated_conjecture,
% 7.35/1.50      ( k1_funct_1(sK9,sK8) != sK7 ),
% 7.35/1.50      inference(cnf_transformation,[],[f95]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(contradiction,plain,
% 7.35/1.50      ( $false ),
% 7.35/1.50      inference(minisat,[status(thm)],[c_23382,c_34]) ).
% 7.35/1.50  
% 7.35/1.50  
% 7.35/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.35/1.50  
% 7.35/1.50  ------                               Statistics
% 7.35/1.50  
% 7.35/1.50  ------ General
% 7.35/1.50  
% 7.35/1.50  abstr_ref_over_cycles:                  0
% 7.35/1.50  abstr_ref_under_cycles:                 0
% 7.35/1.50  gc_basic_clause_elim:                   0
% 7.35/1.50  forced_gc_time:                         0
% 7.35/1.50  parsing_time:                           0.009
% 7.35/1.50  unif_index_cands_time:                  0.
% 7.35/1.50  unif_index_add_time:                    0.
% 7.35/1.50  orderings_time:                         0.
% 7.35/1.50  out_proof_time:                         0.01
% 7.35/1.50  total_time:                             0.604
% 7.35/1.50  num_of_symbols:                         56
% 7.35/1.50  num_of_terms:                           22712
% 7.35/1.50  
% 7.35/1.50  ------ Preprocessing
% 7.35/1.50  
% 7.35/1.50  num_of_splits:                          0
% 7.35/1.50  num_of_split_atoms:                     0
% 7.35/1.50  num_of_reused_defs:                     0
% 7.35/1.50  num_eq_ax_congr_red:                    46
% 7.35/1.50  num_of_sem_filtered_clauses:            1
% 7.35/1.50  num_of_subtypes:                        0
% 7.35/1.50  monotx_restored_types:                  0
% 7.35/1.50  sat_num_of_epr_types:                   0
% 7.35/1.50  sat_num_of_non_cyclic_types:            0
% 7.35/1.50  sat_guarded_non_collapsed_types:        0
% 7.35/1.50  num_pure_diseq_elim:                    0
% 7.35/1.50  simp_replaced_by:                       0
% 7.35/1.50  res_preprocessed:                       163
% 7.35/1.50  prep_upred:                             0
% 7.35/1.50  prep_unflattend:                        81
% 7.35/1.50  smt_new_axioms:                         0
% 7.35/1.50  pred_elim_cands:                        3
% 7.35/1.50  pred_elim:                              4
% 7.35/1.50  pred_elim_cl:                           8
% 7.35/1.50  pred_elim_cycles:                       10
% 7.35/1.50  merged_defs:                            0
% 7.35/1.50  merged_defs_ncl:                        0
% 7.35/1.50  bin_hyper_res:                          0
% 7.35/1.50  prep_cycles:                            4
% 7.35/1.50  pred_elim_time:                         0.016
% 7.35/1.50  splitting_time:                         0.
% 7.35/1.50  sem_filter_time:                        0.
% 7.35/1.50  monotx_time:                            0.
% 7.35/1.50  subtype_inf_time:                       0.
% 7.35/1.50  
% 7.35/1.50  ------ Problem properties
% 7.35/1.50  
% 7.35/1.50  clauses:                                31
% 7.35/1.50  conjectures:                            2
% 7.35/1.50  epr:                                    4
% 7.35/1.50  horn:                                   23
% 7.35/1.50  ground:                                 5
% 7.35/1.50  unary:                                  7
% 7.35/1.50  binary:                                 8
% 7.35/1.50  lits:                                   79
% 7.35/1.50  lits_eq:                                38
% 7.35/1.50  fd_pure:                                0
% 7.35/1.50  fd_pseudo:                              0
% 7.35/1.50  fd_cond:                                3
% 7.35/1.50  fd_pseudo_cond:                         6
% 7.35/1.50  ac_symbols:                             0
% 7.35/1.50  
% 7.35/1.50  ------ Propositional Solver
% 7.35/1.50  
% 7.35/1.50  prop_solver_calls:                      28
% 7.35/1.50  prop_fast_solver_calls:                 1579
% 7.35/1.50  smt_solver_calls:                       0
% 7.35/1.50  smt_fast_solver_calls:                  0
% 7.35/1.50  prop_num_of_clauses:                    8014
% 7.35/1.50  prop_preprocess_simplified:             17700
% 7.35/1.50  prop_fo_subsumed:                       22
% 7.35/1.50  prop_solver_time:                       0.
% 7.35/1.50  smt_solver_time:                        0.
% 7.35/1.50  smt_fast_solver_time:                   0.
% 7.35/1.50  prop_fast_solver_time:                  0.
% 7.35/1.50  prop_unsat_core_time:                   0.
% 7.35/1.50  
% 7.35/1.50  ------ QBF
% 7.35/1.50  
% 7.35/1.50  qbf_q_res:                              0
% 7.35/1.50  qbf_num_tautologies:                    0
% 7.35/1.50  qbf_prep_cycles:                        0
% 7.35/1.50  
% 7.35/1.50  ------ BMC1
% 7.35/1.50  
% 7.35/1.50  bmc1_current_bound:                     -1
% 7.35/1.50  bmc1_last_solved_bound:                 -1
% 7.35/1.50  bmc1_unsat_core_size:                   -1
% 7.35/1.50  bmc1_unsat_core_parents_size:           -1
% 7.35/1.50  bmc1_merge_next_fun:                    0
% 7.35/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.35/1.50  
% 7.35/1.50  ------ Instantiation
% 7.35/1.50  
% 7.35/1.50  inst_num_of_clauses:                    2144
% 7.35/1.50  inst_num_in_passive:                    903
% 7.35/1.50  inst_num_in_active:                     721
% 7.35/1.50  inst_num_in_unprocessed:                520
% 7.35/1.50  inst_num_of_loops:                      810
% 7.35/1.50  inst_num_of_learning_restarts:          0
% 7.35/1.50  inst_num_moves_active_passive:          87
% 7.35/1.50  inst_lit_activity:                      0
% 7.35/1.50  inst_lit_activity_moves:                0
% 7.35/1.50  inst_num_tautologies:                   0
% 7.35/1.50  inst_num_prop_implied:                  0
% 7.35/1.50  inst_num_existing_simplified:           0
% 7.35/1.50  inst_num_eq_res_simplified:             0
% 7.35/1.50  inst_num_child_elim:                    0
% 7.35/1.50  inst_num_of_dismatching_blockings:      2773
% 7.35/1.50  inst_num_of_non_proper_insts:           2497
% 7.35/1.50  inst_num_of_duplicates:                 0
% 7.35/1.50  inst_inst_num_from_inst_to_res:         0
% 7.35/1.50  inst_dismatching_checking_time:         0.
% 7.35/1.50  
% 7.35/1.50  ------ Resolution
% 7.35/1.50  
% 7.35/1.50  res_num_of_clauses:                     0
% 7.35/1.50  res_num_in_passive:                     0
% 7.35/1.50  res_num_in_active:                      0
% 7.35/1.50  res_num_of_loops:                       167
% 7.35/1.50  res_forward_subset_subsumed:            365
% 7.35/1.50  res_backward_subset_subsumed:           0
% 7.35/1.50  res_forward_subsumed:                   0
% 7.35/1.50  res_backward_subsumed:                  1
% 7.35/1.50  res_forward_subsumption_resolution:     0
% 7.35/1.50  res_backward_subsumption_resolution:    0
% 7.35/1.50  res_clause_to_clause_subsumption:       2220
% 7.35/1.50  res_orphan_elimination:                 0
% 7.35/1.50  res_tautology_del:                      60
% 7.35/1.50  res_num_eq_res_simplified:              1
% 7.35/1.50  res_num_sel_changes:                    0
% 7.35/1.50  res_moves_from_active_to_pass:          0
% 7.35/1.50  
% 7.35/1.50  ------ Superposition
% 7.35/1.50  
% 7.35/1.50  sup_time_total:                         0.
% 7.35/1.50  sup_time_generating:                    0.
% 7.35/1.50  sup_time_sim_full:                      0.
% 7.35/1.50  sup_time_sim_immed:                     0.
% 7.35/1.50  
% 7.35/1.50  sup_num_of_clauses:                     543
% 7.35/1.50  sup_num_in_active:                      139
% 7.35/1.50  sup_num_in_passive:                     404
% 7.35/1.50  sup_num_of_loops:                       161
% 7.35/1.50  sup_fw_superposition:                   374
% 7.35/1.50  sup_bw_superposition:                   448
% 7.35/1.50  sup_immediate_simplified:               70
% 7.35/1.50  sup_given_eliminated:                   0
% 7.35/1.50  comparisons_done:                       0
% 7.35/1.50  comparisons_avoided:                    162
% 7.35/1.50  
% 7.35/1.50  ------ Simplifications
% 7.35/1.50  
% 7.35/1.50  
% 7.35/1.50  sim_fw_subset_subsumed:                 40
% 7.35/1.50  sim_bw_subset_subsumed:                 27
% 7.35/1.50  sim_fw_subsumed:                        11
% 7.35/1.50  sim_bw_subsumed:                        3
% 7.35/1.50  sim_fw_subsumption_res:                 2
% 7.35/1.50  sim_bw_subsumption_res:                 0
% 7.35/1.50  sim_tautology_del:                      1
% 7.35/1.50  sim_eq_tautology_del:                   124
% 7.35/1.50  sim_eq_res_simp:                        0
% 7.35/1.50  sim_fw_demodulated:                     2
% 7.35/1.50  sim_bw_demodulated:                     22
% 7.35/1.50  sim_light_normalised:                   29
% 7.35/1.50  sim_joinable_taut:                      0
% 7.35/1.50  sim_joinable_simp:                      0
% 7.35/1.50  sim_ac_normalised:                      0
% 7.35/1.50  sim_smt_subsumption:                    0
% 7.35/1.50  
%------------------------------------------------------------------------------
