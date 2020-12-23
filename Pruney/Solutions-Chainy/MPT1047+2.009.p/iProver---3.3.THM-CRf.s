%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:52 EST 2020

% Result     : Theorem 7.56s
% Output     : CNFRefutation 7.56s
% Verified   : 
% Statistics : Number of formulae       :  208 (2379 expanded)
%              Number of clauses        :  112 ( 331 expanded)
%              Number of leaves         :   28 ( 734 expanded)
%              Depth                    :   20
%              Number of atoms          :  827 (8258 expanded)
%              Number of equality atoms :  255 (2549 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => k1_tarski(X3) = k5_partfun1(X0,k1_tarski(X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
              & v1_funct_2(X3,X0,k1_tarski(X1))
              & v1_funct_1(X3) )
           => k1_tarski(X3) = k5_partfun1(X0,k1_tarski(X1),X2) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
     => ( k1_tarski(sK9) != k5_partfun1(X0,k1_tarski(X1),X2)
        & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(sK9,X0,k1_tarski(X1))
        & v1_funct_1(sK9) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(sK6,k1_tarski(sK7),sK8)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7))))
          & v1_funct_2(X3,sK6,k1_tarski(sK7))
          & v1_funct_1(X3) )
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7))))
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( k1_tarski(sK9) != k5_partfun1(sK6,k1_tarski(sK7),sK8)
    & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7))))
    & v1_funct_2(sK9,sK6,k1_tarski(sK7))
    & v1_funct_1(sK9)
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7))))
    & v1_funct_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f33,f53,f52])).

fof(f99,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7)))) ),
    inference(cnf_transformation,[],[f54])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f104,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f105,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f56,f104])).

fof(f125,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) ),
    inference(definition_unfolding,[],[f99,f105])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f35,plain,(
    ! [X1,X0,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> sP0(X2,X0,X1,X3) )
      | ~ sP1(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f34,plain,(
    ! [X2,X0,X1,X3] :
      ( sP0(X2,X0,X1,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5] :
              ( r1_partfun1(X2,X5)
              & v1_partfun1(X5,X0)
              & X4 = X5
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X5) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f23,f35,f34])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f98,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f54])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X2,X0,X1,X3] :
      ( ( sP0(X2,X0,X1,X3)
        | ? [X4] :
            ( ( ! [X5] :
                  ( ~ r1_partfun1(X2,X5)
                  | ~ v1_partfun1(X5,X0)
                  | X4 != X5
                  | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  | ~ v1_funct_1(X5) )
              | ~ r2_hidden(X4,X3) )
            & ( ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) )
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ! [X5] :
                  ( ~ r1_partfun1(X2,X5)
                  | ~ v1_partfun1(X5,X0)
                  | X4 != X5
                  | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  | ~ v1_funct_1(X5) ) )
            & ( ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) )
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP0(X2,X0,X1,X3) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ! [X5] :
                  ( ~ r1_partfun1(X0,X5)
                  | ~ v1_partfun1(X5,X1)
                  | X4 != X5
                  | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  | ~ v1_funct_1(X5) )
              | ~ r2_hidden(X4,X3) )
            & ( ? [X6] :
                  ( r1_partfun1(X0,X6)
                  & v1_partfun1(X6,X1)
                  & X4 = X6
                  & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_1(X6) )
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X3)
              | ! [X8] :
                  ( ~ r1_partfun1(X0,X8)
                  | ~ v1_partfun1(X8,X1)
                  | X7 != X8
                  | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  | ~ v1_funct_1(X8) ) )
            & ( ? [X9] :
                  ( r1_partfun1(X0,X9)
                  & v1_partfun1(X9,X1)
                  & X7 = X9
                  & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_1(X9) )
              | ~ r2_hidden(X7,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f46])).

fof(f50,plain,(
    ! [X7,X2,X1,X0] :
      ( ? [X9] :
          ( r1_partfun1(X0,X9)
          & v1_partfun1(X9,X1)
          & X7 = X9
          & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X9) )
     => ( r1_partfun1(X0,sK5(X0,X1,X2,X7))
        & v1_partfun1(sK5(X0,X1,X2,X7),X1)
        & sK5(X0,X1,X2,X7) = X7
        & m1_subset_1(sK5(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(sK5(X0,X1,X2,X7)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r1_partfun1(X0,X6)
          & v1_partfun1(X6,X1)
          & X4 = X6
          & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X6) )
     => ( r1_partfun1(X0,sK4(X0,X1,X2,X3))
        & v1_partfun1(sK4(X0,X1,X2,X3),X1)
        & sK4(X0,X1,X2,X3) = X4
        & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(sK4(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r1_partfun1(X0,X5)
                | ~ v1_partfun1(X5,X1)
                | X4 != X5
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                | ~ v1_funct_1(X5) )
            | ~ r2_hidden(X4,X3) )
          & ( ? [X6] :
                ( r1_partfun1(X0,X6)
                & v1_partfun1(X6,X1)
                & X4 = X6
                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_1(X6) )
            | r2_hidden(X4,X3) ) )
     => ( ( ! [X5] :
              ( ~ r1_partfun1(X0,X5)
              | ~ v1_partfun1(X5,X1)
              | sK3(X0,X1,X2,X3) != X5
              | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              | ~ v1_funct_1(X5) )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( ? [X6] :
              ( r1_partfun1(X0,X6)
              & v1_partfun1(X6,X1)
              & sK3(X0,X1,X2,X3) = X6
              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_1(X6) )
          | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ! [X5] :
                ( ~ r1_partfun1(X0,X5)
                | ~ v1_partfun1(X5,X1)
                | sK3(X0,X1,X2,X3) != X5
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                | ~ v1_funct_1(X5) )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( ( r1_partfun1(X0,sK4(X0,X1,X2,X3))
              & v1_partfun1(sK4(X0,X1,X2,X3),X1)
              & sK3(X0,X1,X2,X3) = sK4(X0,X1,X2,X3)
              & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_1(sK4(X0,X1,X2,X3)) )
            | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X3)
              | ! [X8] :
                  ( ~ r1_partfun1(X0,X8)
                  | ~ v1_partfun1(X8,X1)
                  | X7 != X8
                  | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  | ~ v1_funct_1(X8) ) )
            & ( ( r1_partfun1(X0,sK5(X0,X1,X2,X7))
                & v1_partfun1(sK5(X0,X1,X2,X7),X1)
                & sK5(X0,X1,X2,X7) = X7
                & m1_subset_1(sK5(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_1(sK5(X0,X1,X2,X7)) )
              | ~ r2_hidden(X7,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f47,f50,f49,f48])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | sK3(X0,X1,X2,X3) = sK4(X0,X1,X2,X3)
      | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f44,plain,(
    ! [X1,X0,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ~ sP0(X2,X0,X1,X3) )
          & ( sP0(X2,X0,X1,X3)
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ sP1(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X1,X0,X2) = X3
            | ~ sP0(X2,X1,X0,X3) )
          & ( sP0(X2,X1,X0,X3)
            | k5_partfun1(X1,X0,X2) != X3 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f44])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_partfun1(X1,X0,X2) = X3
      | ~ sP0(X2,X1,X0,X3)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f37])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f59,f105])).

fof(f103,plain,(
    k1_tarski(sK9) != k5_partfun1(sK6,k1_tarski(sK7),sK8) ),
    inference(cnf_transformation,[],[f54])).

fof(f122,plain,(
    k2_enumset1(sK9,sK9,sK9,sK9) != k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) ),
    inference(definition_unfolding,[],[f103,f105,f105])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_1(X3) )
         => r1_partfun1(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f120,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f93,f105,f105])).

fof(f102,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7)))) ),
    inference(cnf_transformation,[],[f54])).

fof(f123,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) ),
    inference(definition_unfolding,[],[f102,f105])).

fof(f100,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f54])).

fof(f60,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f106,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f60,f105])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(X3)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X1)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X2,X0,k1_tarski(X1))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => r2_relset_1(X0,k1_tarski(X1),X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,k1_tarski(X1),X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_2(X3,X0,k1_tarski(X1))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X2,X0,k1_tarski(X1))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,k1_tarski(X1),X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_2(X3,X0,k1_tarski(X1))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X2,X0,k1_tarski(X1))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,k1_tarski(X1),X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X3,X0,k1_tarski(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X2,X0,k1_tarski(X1))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f121,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,k2_enumset1(X1,X1,X1,X1),X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))))
      | ~ v1_funct_2(X3,X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))))
      | ~ v1_funct_2(X2,X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f97,f105,f105,f105,f105,f105])).

fof(f101,plain,(
    v1_funct_2(sK9,sK6,k1_tarski(sK7)) ),
    inference(cnf_transformation,[],[f54])).

fof(f124,plain,(
    v1_funct_2(sK9,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) ),
    inference(definition_unfolding,[],[f101,f105])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f20])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k5_partfun1(X1,X0,X2) != X3
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0,k5_partfun1(X1,X0,X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f76])).

fof(f83,plain,(
    ! [X2,X0,X8,X7,X3,X1] :
      ( r2_hidden(X7,X3)
      | ~ r1_partfun1(X0,X8)
      | ~ v1_partfun1(X8,X1)
      | X7 != X8
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X8)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f137,plain,(
    ! [X2,X0,X8,X3,X1] :
      ( r2_hidden(X8,X3)
      | ~ r1_partfun1(X0,X8)
      | ~ v1_partfun1(X8,X1)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X8)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(equality_resolution,[],[f83])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ~ ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3 ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(flattening,[],[f39])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
      | k1_tarski(X0) != X3 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f114,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))
      | k2_enumset1(X0,X0,X0,X0) != X3 ) ),
    inference(definition_unfolding,[],[f63,f58,f105])).

fof(f132,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f114])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f41])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f71,f104])).

cnf(c_44,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_1114,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_32,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1125,plain,
    ( sP1(X0,X1,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_3538,plain,
    ( sP1(k2_enumset1(sK7,sK7,sK7,sK7),sK6,sK8) = iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1114,c_1125])).

cnf(c_45,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_46,plain,
    ( v1_funct_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_47,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_1555,plain,
    ( sP1(X0,X1,sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(sK8) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_1859,plain,
    ( sP1(k2_enumset1(sK7,sK7,sK7,sK7),sK6,sK8)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))))
    | ~ v1_funct_1(sK8) ),
    inference(instantiation,[status(thm)],[c_1555])).

cnf(c_1860,plain,
    ( sP1(k2_enumset1(sK7,sK7,sK7,sK7),sK6,sK8) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1859])).

cnf(c_3650,plain,
    ( sP1(k2_enumset1(sK7,sK7,sK7,sK7),sK6,sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3538,c_46,c_47,c_1860])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1156,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_23,plain,
    ( sP0(X0,X1,X2,X3)
    | r2_hidden(sK3(X0,X1,X2,X3),X3)
    | sK4(X0,X1,X2,X3) = sK3(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1134,plain,
    ( sK4(X0,X1,X2,X3) = sK3(X0,X1,X2,X3)
    | sP0(X0,X1,X2,X3) = iProver_top
    | r2_hidden(sK3(X0,X1,X2,X3),X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1142,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_7469,plain,
    ( sK4(X0,X1,X2,X3) = sK3(X0,X1,X2,X3)
    | sP0(X0,X1,X2,X3) = iProver_top
    | r1_tarski(X3,sK3(X0,X1,X2,X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1134,c_1142])).

cnf(c_19865,plain,
    ( sK4(X0,X1,X2,k1_xboole_0) = sK3(X0,X1,X2,k1_xboole_0)
    | sP0(X0,X1,X2,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1156,c_7469])).

cnf(c_18,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ sP1(X2,X1,X0)
    | k5_partfun1(X1,X2,X0) = X3 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1139,plain,
    ( k5_partfun1(X0,X1,X2) = X3
    | sP0(X2,X0,X1,X3) != iProver_top
    | sP1(X1,X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_21539,plain,
    ( sK4(X0,X1,X2,k1_xboole_0) = sK3(X0,X1,X2,k1_xboole_0)
    | k5_partfun1(X1,X2,X0) = k1_xboole_0
    | sP1(X2,X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_19865,c_1139])).

cnf(c_24039,plain,
    ( sK4(sK8,sK6,k2_enumset1(sK7,sK7,sK7,sK7),k1_xboole_0) = sK3(sK8,sK6,k2_enumset1(sK7,sK7,sK7,sK7),k1_xboole_0)
    | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3650,c_21539])).

cnf(c_36,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_40,negated_conjecture,
    ( k2_enumset1(sK9,sK9,sK9,sK9) != k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_3404,plain,
    ( r2_hidden(sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),sK9),k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8))
    | k1_xboole_0 = k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) ),
    inference(resolution,[status(thm)],[c_2,c_40])).

cnf(c_8873,plain,
    ( m1_subset_1(sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),sK9),k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))))
    | ~ v1_funct_1(sK8)
    | k1_xboole_0 = k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) ),
    inference(resolution,[status(thm)],[c_36,c_3404])).

cnf(c_17984,plain,
    ( m1_subset_1(sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),sK9),k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))))
    | k1_xboole_0 = k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8873,c_45,c_44])).

cnf(c_35,plain,
    ( r1_partfun1(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_41,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_10695,plain,
    ( r1_partfun1(sK9,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK9) ),
    inference(resolution,[status(thm)],[c_35,c_41])).

cnf(c_43,negated_conjecture,
    ( v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_11460,plain,
    ( ~ v1_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))))
    | r1_partfun1(sK9,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10695,c_43])).

cnf(c_11461,plain,
    ( r1_partfun1(sK9,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))))
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_11460])).

cnf(c_18520,plain,
    ( r1_partfun1(sK9,sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),sK9))
    | ~ v1_funct_1(sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),sK9))
    | k1_xboole_0 = k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) ),
    inference(resolution,[status(thm)],[c_17984,c_11461])).

cnf(c_1,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | sK2(X1,X0) != X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_6167,plain,
    ( sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),sK9) != sK9
    | k1_xboole_0 = k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) ),
    inference(resolution,[status(thm)],[c_1,c_40])).

cnf(c_38,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_7572,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))))
    | v1_funct_1(sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),sK9))
    | ~ v1_funct_1(sK8)
    | k1_xboole_0 = k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) ),
    inference(resolution,[status(thm)],[c_38,c_3404])).

cnf(c_7644,plain,
    ( v1_funct_1(sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),sK9))
    | k1_xboole_0 = k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7572,c_45,c_44])).

cnf(c_37,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X0,k5_partfun1(X1,X2,X3))
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_7610,plain,
    ( v1_funct_2(sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),sK9),sK6,k2_enumset1(sK7,sK7,sK7,sK7))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))))
    | ~ v1_funct_1(sK8)
    | k1_xboole_0 = k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) ),
    inference(resolution,[status(thm)],[c_37,c_3404])).

cnf(c_7689,plain,
    ( v1_funct_2(sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),sK9),sK6,k2_enumset1(sK7,sK7,sK7,sK7))
    | k1_xboole_0 = k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7610,c_45,c_44])).

cnf(c_39,plain,
    ( r2_relset_1(X0,k2_enumset1(X1,X1,X1,X1),X2,X3)
    | ~ v1_funct_2(X3,X0,k2_enumset1(X1,X1,X1,X1))
    | ~ v1_funct_2(X2,X0,k2_enumset1(X1,X1,X1,X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_13169,plain,
    ( r2_relset_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9,X0)
    | ~ v1_funct_2(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7))
    | ~ v1_funct_2(sK9,sK6,k2_enumset1(sK7,sK7,sK7,sK7))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK9) ),
    inference(resolution,[status(thm)],[c_39,c_41])).

cnf(c_42,negated_conjecture,
    ( v1_funct_2(sK9,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_14977,plain,
    ( ~ v1_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))))
    | r2_relset_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9,X0)
    | ~ v1_funct_2(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13169,c_43,c_42])).

cnf(c_14978,plain,
    ( r2_relset_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9,X0)
    | ~ v1_funct_2(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))))
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_14977])).

cnf(c_18522,plain,
    ( r2_relset_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9,sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),sK9))
    | ~ v1_funct_2(sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),sK9),sK6,k2_enumset1(sK7,sK7,sK7,sK7))
    | ~ v1_funct_1(sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),sK9))
    | k1_xboole_0 = k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) ),
    inference(resolution,[status(thm)],[c_17984,c_14978])).

cnf(c_17,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_9048,plain,
    ( ~ r2_relset_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))))
    | X0 = sK9 ),
    inference(resolution,[status(thm)],[c_17,c_41])).

cnf(c_18518,plain,
    ( ~ r2_relset_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9,sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),sK9))
    | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),sK9) = sK9
    | k1_xboole_0 = k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) ),
    inference(resolution,[status(thm)],[c_17984,c_9048])).

cnf(c_18529,plain,
    ( k1_xboole_0 = k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18520,c_6167,c_7644,c_7689,c_18522,c_18518])).

cnf(c_394,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_393,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2672,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_394,c_393])).

cnf(c_18535,plain,
    ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18529,c_2672])).

cnf(c_24703,plain,
    ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_24039,c_18535])).

cnf(c_19,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
    | ~ sP1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_1138,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0)) = iProver_top
    | sP1(X2,X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_24814,plain,
    ( sP0(sK8,sK6,k2_enumset1(sK7,sK7,sK7,sK7),k1_xboole_0) = iProver_top
    | sP1(k2_enumset1(sK7,sK7,sK7,sK7),sK6,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_24703,c_1138])).

cnf(c_403,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | sP0(X0,X1,X2,X4)
    | X4 != X3 ),
    theory(equality)).

cnf(c_3250,plain,
    ( sP0(X0,X1,X2,X3)
    | ~ sP1(X2,X1,X0)
    | X3 != k5_partfun1(X1,X2,X0) ),
    inference(resolution,[status(thm)],[c_403,c_19])).

cnf(c_18582,plain,
    ( sP0(sK8,sK6,k2_enumset1(sK7,sK7,sK7,sK7),k1_xboole_0)
    | ~ sP1(k2_enumset1(sK7,sK7,sK7,sK7),sK6,sK8) ),
    inference(resolution,[status(thm)],[c_18529,c_3250])).

cnf(c_18583,plain,
    ( sP0(sK8,sK6,k2_enumset1(sK7,sK7,sK7,sK7),k1_xboole_0) = iProver_top
    | sP1(k2_enumset1(sK7,sK7,sK7,sK7),sK6,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18582])).

cnf(c_26157,plain,
    ( sP0(sK8,sK6,k2_enumset1(sK7,sK7,sK7,sK7),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24814,c_46,c_47,c_1860,c_18583])).

cnf(c_1117,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_26,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ v1_partfun1(X4,X1)
    | ~ r1_partfun1(X0,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(X4,X3)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_1131,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | v1_partfun1(X4,X1) != iProver_top
    | r1_partfun1(X0,X4) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r2_hidden(X4,X3) = iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_8014,plain,
    ( sP0(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7),X1) != iProver_top
    | v1_partfun1(sK9,sK6) != iProver_top
    | r1_partfun1(X0,sK9) != iProver_top
    | r2_hidden(sK9,X1) = iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_1131])).

cnf(c_48,plain,
    ( v1_funct_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_9428,plain,
    ( r2_hidden(sK9,X1) = iProver_top
    | r1_partfun1(X0,sK9) != iProver_top
    | v1_partfun1(sK9,sK6) != iProver_top
    | sP0(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7),X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8014,c_48])).

cnf(c_9429,plain,
    ( sP0(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7),X1) != iProver_top
    | v1_partfun1(sK9,sK6) != iProver_top
    | r1_partfun1(X0,sK9) != iProver_top
    | r2_hidden(sK9,X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_9428])).

cnf(c_26169,plain,
    ( v1_partfun1(sK9,sK6) != iProver_top
    | r1_partfun1(sK8,sK9) != iProver_top
    | r2_hidden(sK9,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_26157,c_9429])).

cnf(c_50,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_1750,plain,
    ( r1_partfun1(X0,sK9)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_enumset1(X2,X2,X2,X2))))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X1,k2_enumset1(X2,X2,X2,X2))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK9) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_1962,plain,
    ( r1_partfun1(sK8,sK9)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))))
    | ~ v1_funct_1(sK8)
    | ~ v1_funct_1(sK9) ),
    inference(instantiation,[status(thm)],[c_1750])).

cnf(c_2006,plain,
    ( r1_partfun1(sK8,sK9)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))))
    | ~ v1_funct_1(sK8)
    | ~ v1_funct_1(sK9) ),
    inference(instantiation,[status(thm)],[c_1962])).

cnf(c_2007,plain,
    ( r1_partfun1(sK8,sK9) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) != iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2006])).

cnf(c_20356,plain,
    ( sP0(sK8,sK6,k2_enumset1(sK7,sK7,sK7,sK7),k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18582,c_45,c_44,c_1859])).

cnf(c_397,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3593,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_397,c_393])).

cnf(c_34,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_8839,plain,
    ( ~ v1_funct_2(sK9,sK6,k2_enumset1(sK7,sK7,sK7,sK7))
    | v1_partfun1(sK9,sK6)
    | ~ v1_funct_1(sK9)
    | k1_xboole_0 = k2_enumset1(sK7,sK7,sK7,sK7) ),
    inference(resolution,[status(thm)],[c_34,c_41])).

cnf(c_9092,plain,
    ( v1_partfun1(sK9,sK6)
    | k1_xboole_0 = k2_enumset1(sK7,sK7,sK7,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8839,c_43,c_42])).

cnf(c_14103,plain,
    ( v1_partfun1(sK9,sK6)
    | ~ r2_hidden(k2_enumset1(sK7,sK7,sK7,sK7),X0)
    | r2_hidden(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_3593,c_9092])).

cnf(c_9,plain,
    ( r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_136,plain,
    ( r1_tarski(k2_enumset1(sK7,sK7,sK7,sK7),k2_enumset1(sK7,sK7,sK7,sK7)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_149,plain,
    ( r1_tarski(k1_xboole_0,sK7) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_13,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k2_enumset1(X2,X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_1560,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0))
    | ~ r1_tarski(k2_enumset1(X1,X1,X1,X0),k2_enumset1(X1,X1,X1,X0)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1562,plain,
    ( r2_hidden(sK7,k2_enumset1(sK7,sK7,sK7,sK7))
    | ~ r1_tarski(k2_enumset1(sK7,sK7,sK7,sK7),k2_enumset1(sK7,sK7,sK7,sK7)) ),
    inference(instantiation,[status(thm)],[c_1560])).

cnf(c_2082,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X0))
    | ~ r1_tarski(k2_enumset1(X1,X1,X1,X0),X0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2084,plain,
    ( ~ r2_hidden(sK7,k2_enumset1(sK7,sK7,sK7,sK7))
    | ~ r1_tarski(k2_enumset1(sK7,sK7,sK7,sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_2082])).

cnf(c_395,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3575,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_395,c_393])).

cnf(c_9298,plain,
    ( v1_partfun1(sK9,sK6)
    | k2_enumset1(sK7,sK7,sK7,sK7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9092,c_2672])).

cnf(c_14048,plain,
    ( v1_partfun1(sK9,sK6)
    | r1_tarski(k2_enumset1(sK7,sK7,sK7,sK7),X0)
    | ~ r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_3575,c_9298])).

cnf(c_14050,plain,
    ( v1_partfun1(sK9,sK6)
    | r1_tarski(k2_enumset1(sK7,sK7,sK7,sK7),sK7)
    | ~ r1_tarski(k1_xboole_0,sK7) ),
    inference(instantiation,[status(thm)],[c_14048])).

cnf(c_16635,plain,
    ( v1_partfun1(sK9,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14103,c_136,c_149,c_1562,c_2084,c_14050])).

cnf(c_10675,plain,
    ( ~ sP0(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7),X1)
    | ~ v1_partfun1(sK9,sK6)
    | ~ r1_partfun1(X0,sK9)
    | r2_hidden(sK9,X1)
    | ~ v1_funct_1(sK9) ),
    inference(resolution,[status(thm)],[c_26,c_41])).

cnf(c_9430,plain,
    ( ~ sP0(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7),X1)
    | ~ v1_partfun1(sK9,sK6)
    | ~ r1_partfun1(X0,sK9)
    | r2_hidden(sK9,X1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9429])).

cnf(c_12483,plain,
    ( r2_hidden(sK9,X1)
    | ~ r1_partfun1(X0,sK9)
    | ~ v1_partfun1(sK9,sK6)
    | ~ sP0(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10675,c_9430])).

cnf(c_12484,plain,
    ( ~ sP0(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7),X1)
    | ~ v1_partfun1(sK9,sK6)
    | ~ r1_partfun1(X0,sK9)
    | r2_hidden(sK9,X1) ),
    inference(renaming,[status(thm)],[c_12483])).

cnf(c_16964,plain,
    ( ~ sP0(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7),X1)
    | ~ r1_partfun1(X0,sK9)
    | r2_hidden(sK9,X1) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_16635,c_12484])).

cnf(c_20393,plain,
    ( ~ r1_partfun1(sK8,sK9)
    | r2_hidden(sK9,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20356,c_16964])).

cnf(c_20394,plain,
    ( r1_partfun1(sK8,sK9) != iProver_top
    | r2_hidden(sK9,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20393])).

cnf(c_26511,plain,
    ( r2_hidden(sK9,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_26169,c_46,c_47,c_48,c_50,c_2007,c_20394])).

cnf(c_26517,plain,
    ( r1_tarski(k1_xboole_0,sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_26511,c_1142])).

cnf(c_27793,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_26517,c_1156])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:22:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.56/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.56/1.50  
% 7.56/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.56/1.50  
% 7.56/1.50  ------  iProver source info
% 7.56/1.50  
% 7.56/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.56/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.56/1.50  git: non_committed_changes: false
% 7.56/1.50  git: last_make_outside_of_git: false
% 7.56/1.50  
% 7.56/1.50  ------ 
% 7.56/1.50  ------ Parsing...
% 7.56/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.56/1.50  
% 7.56/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.56/1.50  
% 7.56/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.56/1.50  
% 7.56/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.56/1.50  ------ Proving...
% 7.56/1.50  ------ Problem Properties 
% 7.56/1.50  
% 7.56/1.50  
% 7.56/1.50  clauses                                 46
% 7.56/1.50  conjectures                             6
% 7.56/1.50  EPR                                     4
% 7.56/1.50  Horn                                    37
% 7.56/1.50  unary                                   15
% 7.56/1.50  binary                                  5
% 7.56/1.50  lits                                    128
% 7.56/1.50  lits eq                                 19
% 7.56/1.50  fd_pure                                 0
% 7.56/1.50  fd_pseudo                               0
% 7.56/1.50  fd_cond                                 1
% 7.56/1.50  fd_pseudo_cond                          5
% 7.56/1.50  AC symbols                              0
% 7.56/1.50  
% 7.56/1.50  ------ Input Options Time Limit: Unbounded
% 7.56/1.50  
% 7.56/1.50  
% 7.56/1.50  ------ 
% 7.56/1.50  Current options:
% 7.56/1.50  ------ 
% 7.56/1.50  
% 7.56/1.50  
% 7.56/1.50  
% 7.56/1.50  
% 7.56/1.50  ------ Proving...
% 7.56/1.50  
% 7.56/1.50  
% 7.56/1.50  % SZS status Theorem for theBenchmark.p
% 7.56/1.50  
% 7.56/1.50   Resolution empty clause
% 7.56/1.50  
% 7.56/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.56/1.50  
% 7.56/1.50  fof(f15,conjecture,(
% 7.56/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => k1_tarski(X3) = k5_partfun1(X0,k1_tarski(X1),X2)))),
% 7.56/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.50  
% 7.56/1.50  fof(f16,negated_conjecture,(
% 7.56/1.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => k1_tarski(X3) = k5_partfun1(X0,k1_tarski(X1),X2)))),
% 7.56/1.50    inference(negated_conjecture,[],[f15])).
% 7.56/1.50  
% 7.56/1.50  fof(f32,plain,(
% 7.56/1.50    ? [X0,X1,X2] : (? [X3] : (k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)))),
% 7.56/1.50    inference(ennf_transformation,[],[f16])).
% 7.56/1.50  
% 7.56/1.50  fof(f33,plain,(
% 7.56/1.50    ? [X0,X1,X2] : (? [X3] : (k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2))),
% 7.56/1.50    inference(flattening,[],[f32])).
% 7.56/1.50  
% 7.56/1.50  fof(f53,plain,(
% 7.56/1.50    ( ! [X2,X0,X1] : (? [X3] : (k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (k1_tarski(sK9) != k5_partfun1(X0,k1_tarski(X1),X2) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(sK9,X0,k1_tarski(X1)) & v1_funct_1(sK9))) )),
% 7.56/1.50    introduced(choice_axiom,[])).
% 7.56/1.50  
% 7.56/1.50  fof(f52,plain,(
% 7.56/1.50    ? [X0,X1,X2] : (? [X3] : (k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => (? [X3] : (k1_tarski(X3) != k5_partfun1(sK6,k1_tarski(sK7),sK8) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7)))) & v1_funct_2(X3,sK6,k1_tarski(sK7)) & v1_funct_1(X3)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7)))) & v1_funct_1(sK8))),
% 7.56/1.50    introduced(choice_axiom,[])).
% 7.56/1.50  
% 7.56/1.50  fof(f54,plain,(
% 7.56/1.50    (k1_tarski(sK9) != k5_partfun1(sK6,k1_tarski(sK7),sK8) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7)))) & v1_funct_2(sK9,sK6,k1_tarski(sK7)) & v1_funct_1(sK9)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7)))) & v1_funct_1(sK8)),
% 7.56/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f33,f53,f52])).
% 7.56/1.50  
% 7.56/1.50  fof(f99,plain,(
% 7.56/1.50    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7))))),
% 7.56/1.50    inference(cnf_transformation,[],[f54])).
% 7.56/1.50  
% 7.56/1.50  fof(f2,axiom,(
% 7.56/1.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.56/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.50  
% 7.56/1.50  fof(f56,plain,(
% 7.56/1.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.56/1.50    inference(cnf_transformation,[],[f2])).
% 7.56/1.50  
% 7.56/1.50  fof(f3,axiom,(
% 7.56/1.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.56/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.50  
% 7.56/1.50  fof(f57,plain,(
% 7.56/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.56/1.50    inference(cnf_transformation,[],[f3])).
% 7.56/1.50  
% 7.56/1.50  fof(f4,axiom,(
% 7.56/1.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.56/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.50  
% 7.56/1.50  fof(f58,plain,(
% 7.56/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.56/1.50    inference(cnf_transformation,[],[f4])).
% 7.56/1.50  
% 7.56/1.50  fof(f104,plain,(
% 7.56/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.56/1.50    inference(definition_unfolding,[],[f57,f58])).
% 7.56/1.50  
% 7.56/1.50  fof(f105,plain,(
% 7.56/1.50    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 7.56/1.50    inference(definition_unfolding,[],[f56,f104])).
% 7.56/1.50  
% 7.56/1.50  fof(f125,plain,(
% 7.56/1.50    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))))),
% 7.56/1.50    inference(definition_unfolding,[],[f99,f105])).
% 7.56/1.50  
% 7.56/1.50  fof(f10,axiom,(
% 7.56/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))))),
% 7.56/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.50  
% 7.56/1.50  fof(f22,plain,(
% 7.56/1.50    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.56/1.50    inference(ennf_transformation,[],[f10])).
% 7.56/1.50  
% 7.56/1.50  fof(f23,plain,(
% 7.56/1.50    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.56/1.50    inference(flattening,[],[f22])).
% 7.56/1.50  
% 7.56/1.50  fof(f35,plain,(
% 7.56/1.50    ! [X1,X0,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> sP0(X2,X0,X1,X3)) | ~sP1(X1,X0,X2))),
% 7.56/1.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 7.56/1.50  
% 7.56/1.50  fof(f34,plain,(
% 7.56/1.50    ! [X2,X0,X1,X3] : (sP0(X2,X0,X1,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5))))),
% 7.56/1.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 7.56/1.50  
% 7.56/1.50  fof(f36,plain,(
% 7.56/1.50    ! [X0,X1,X2] : (sP1(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.56/1.50    inference(definition_folding,[],[f23,f35,f34])).
% 7.56/1.50  
% 7.56/1.50  fof(f90,plain,(
% 7.56/1.50    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.56/1.50    inference(cnf_transformation,[],[f36])).
% 7.56/1.50  
% 7.56/1.50  fof(f98,plain,(
% 7.56/1.50    v1_funct_1(sK8)),
% 7.56/1.50    inference(cnf_transformation,[],[f54])).
% 7.56/1.50  
% 7.56/1.50  fof(f1,axiom,(
% 7.56/1.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.56/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.50  
% 7.56/1.50  fof(f55,plain,(
% 7.56/1.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.56/1.50    inference(cnf_transformation,[],[f1])).
% 7.56/1.50  
% 7.56/1.50  fof(f46,plain,(
% 7.56/1.50    ! [X2,X0,X1,X3] : ((sP0(X2,X0,X1,X3) | ? [X4] : ((! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5))) & (? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)) | ~r2_hidden(X4,X3))) | ~sP0(X2,X0,X1,X3)))),
% 7.56/1.50    inference(nnf_transformation,[],[f34])).
% 7.56/1.50  
% 7.56/1.50  fof(f47,plain,(
% 7.56/1.50    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & X4 = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) | r2_hidden(X4,X3)))) & (! [X7] : ((r2_hidden(X7,X3) | ! [X8] : (~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8))) & (? [X9] : (r1_partfun1(X0,X9) & v1_partfun1(X9,X1) & X7 = X9 & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X9)) | ~r2_hidden(X7,X3))) | ~sP0(X0,X1,X2,X3)))),
% 7.56/1.50    inference(rectify,[],[f46])).
% 7.56/1.50  
% 7.56/1.50  fof(f50,plain,(
% 7.56/1.50    ! [X7,X2,X1,X0] : (? [X9] : (r1_partfun1(X0,X9) & v1_partfun1(X9,X1) & X7 = X9 & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X9)) => (r1_partfun1(X0,sK5(X0,X1,X2,X7)) & v1_partfun1(sK5(X0,X1,X2,X7),X1) & sK5(X0,X1,X2,X7) = X7 & m1_subset_1(sK5(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK5(X0,X1,X2,X7))))),
% 7.56/1.50    introduced(choice_axiom,[])).
% 7.56/1.50  
% 7.56/1.50  fof(f49,plain,(
% 7.56/1.50    ( ! [X4] : (! [X3,X2,X1,X0] : (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & X4 = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) => (r1_partfun1(X0,sK4(X0,X1,X2,X3)) & v1_partfun1(sK4(X0,X1,X2,X3),X1) & sK4(X0,X1,X2,X3) = X4 & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK4(X0,X1,X2,X3))))) )),
% 7.56/1.50    introduced(choice_axiom,[])).
% 7.56/1.50  
% 7.56/1.50  fof(f48,plain,(
% 7.56/1.50    ! [X3,X2,X1,X0] : (? [X4] : ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & X4 = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) | r2_hidden(X4,X3))) => ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | sK3(X0,X1,X2,X3) != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & sK3(X0,X1,X2,X3) = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 7.56/1.50    introduced(choice_axiom,[])).
% 7.56/1.50  
% 7.56/1.50  fof(f51,plain,(
% 7.56/1.50    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | sK3(X0,X1,X2,X3) != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & ((r1_partfun1(X0,sK4(X0,X1,X2,X3)) & v1_partfun1(sK4(X0,X1,X2,X3),X1) & sK3(X0,X1,X2,X3) = sK4(X0,X1,X2,X3) & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK4(X0,X1,X2,X3))) | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X7] : ((r2_hidden(X7,X3) | ! [X8] : (~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8))) & ((r1_partfun1(X0,sK5(X0,X1,X2,X7)) & v1_partfun1(sK5(X0,X1,X2,X7),X1) & sK5(X0,X1,X2,X7) = X7 & m1_subset_1(sK5(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK5(X0,X1,X2,X7))) | ~r2_hidden(X7,X3))) | ~sP0(X0,X1,X2,X3)))),
% 7.56/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f47,f50,f49,f48])).
% 7.56/1.50  
% 7.56/1.50  fof(f86,plain,(
% 7.56/1.50    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | sK3(X0,X1,X2,X3) = sK4(X0,X1,X2,X3) | r2_hidden(sK3(X0,X1,X2,X3),X3)) )),
% 7.56/1.50    inference(cnf_transformation,[],[f51])).
% 7.56/1.50  
% 7.56/1.50  fof(f8,axiom,(
% 7.56/1.50    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 7.56/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.50  
% 7.56/1.50  fof(f19,plain,(
% 7.56/1.50    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 7.56/1.50    inference(ennf_transformation,[],[f8])).
% 7.56/1.50  
% 7.56/1.50  fof(f73,plain,(
% 7.56/1.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 7.56/1.50    inference(cnf_transformation,[],[f19])).
% 7.56/1.50  
% 7.56/1.50  fof(f44,plain,(
% 7.56/1.50    ! [X1,X0,X2] : (! [X3] : ((k5_partfun1(X0,X1,X2) = X3 | ~sP0(X2,X0,X1,X3)) & (sP0(X2,X0,X1,X3) | k5_partfun1(X0,X1,X2) != X3)) | ~sP1(X1,X0,X2))),
% 7.56/1.50    inference(nnf_transformation,[],[f35])).
% 7.56/1.50  
% 7.56/1.50  fof(f45,plain,(
% 7.56/1.50    ! [X0,X1,X2] : (! [X3] : ((k5_partfun1(X1,X0,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k5_partfun1(X1,X0,X2) != X3)) | ~sP1(X0,X1,X2))),
% 7.56/1.50    inference(rectify,[],[f44])).
% 7.56/1.50  
% 7.56/1.50  fof(f77,plain,(
% 7.56/1.50    ( ! [X2,X0,X3,X1] : (k5_partfun1(X1,X0,X2) = X3 | ~sP0(X2,X1,X0,X3) | ~sP1(X0,X1,X2)) )),
% 7.56/1.50    inference(cnf_transformation,[],[f45])).
% 7.56/1.50  
% 7.56/1.50  fof(f13,axiom,(
% 7.56/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))))),
% 7.56/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.50  
% 7.56/1.50  fof(f28,plain,(
% 7.56/1.50    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.56/1.50    inference(ennf_transformation,[],[f13])).
% 7.56/1.50  
% 7.56/1.50  fof(f29,plain,(
% 7.56/1.50    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.56/1.50    inference(flattening,[],[f28])).
% 7.56/1.50  
% 7.56/1.50  fof(f96,plain,(
% 7.56/1.50    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.56/1.50    inference(cnf_transformation,[],[f29])).
% 7.56/1.50  
% 7.56/1.50  fof(f5,axiom,(
% 7.56/1.50    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 7.56/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.50  
% 7.56/1.50  fof(f17,plain,(
% 7.56/1.50    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 7.56/1.50    inference(ennf_transformation,[],[f5])).
% 7.56/1.50  
% 7.56/1.50  fof(f37,plain,(
% 7.56/1.50    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)))),
% 7.56/1.50    introduced(choice_axiom,[])).
% 7.56/1.50  
% 7.56/1.50  fof(f38,plain,(
% 7.56/1.50    ! [X0,X1] : ((sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 7.56/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f37])).
% 7.56/1.50  
% 7.56/1.50  fof(f59,plain,(
% 7.56/1.50    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 7.56/1.50    inference(cnf_transformation,[],[f38])).
% 7.56/1.50  
% 7.56/1.50  fof(f107,plain,(
% 7.56/1.50    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 7.56/1.50    inference(definition_unfolding,[],[f59,f105])).
% 7.56/1.50  
% 7.56/1.50  fof(f103,plain,(
% 7.56/1.50    k1_tarski(sK9) != k5_partfun1(sK6,k1_tarski(sK7),sK8)),
% 7.56/1.50    inference(cnf_transformation,[],[f54])).
% 7.56/1.50  
% 7.56/1.50  fof(f122,plain,(
% 7.56/1.50    k2_enumset1(sK9,sK9,sK9,sK9) != k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8)),
% 7.56/1.50    inference(definition_unfolding,[],[f103,f105,f105])).
% 7.56/1.50  
% 7.56/1.50  fof(f12,axiom,(
% 7.56/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X3)) => r1_partfun1(X2,X3)))),
% 7.56/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.50  
% 7.56/1.50  fof(f26,plain,(
% 7.56/1.50    ! [X0,X1,X2] : (! [X3] : (r1_partfun1(X2,X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2)))),
% 7.56/1.50    inference(ennf_transformation,[],[f12])).
% 7.56/1.50  
% 7.56/1.50  fof(f27,plain,(
% 7.56/1.50    ! [X0,X1,X2] : (! [X3] : (r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2))),
% 7.56/1.50    inference(flattening,[],[f26])).
% 7.56/1.50  
% 7.56/1.50  fof(f93,plain,(
% 7.56/1.50    ( ! [X2,X0,X3,X1] : (r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2)) )),
% 7.56/1.50    inference(cnf_transformation,[],[f27])).
% 7.56/1.50  
% 7.56/1.50  fof(f120,plain,(
% 7.56/1.50    ( ! [X2,X0,X3,X1] : (r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1)))) | ~v1_funct_1(X2)) )),
% 7.56/1.50    inference(definition_unfolding,[],[f93,f105,f105])).
% 7.56/1.50  
% 7.56/1.50  fof(f102,plain,(
% 7.56/1.50    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7))))),
% 7.56/1.50    inference(cnf_transformation,[],[f54])).
% 7.56/1.50  
% 7.56/1.50  fof(f123,plain,(
% 7.56/1.50    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))))),
% 7.56/1.50    inference(definition_unfolding,[],[f102,f105])).
% 7.56/1.50  
% 7.56/1.50  fof(f100,plain,(
% 7.56/1.50    v1_funct_1(sK9)),
% 7.56/1.50    inference(cnf_transformation,[],[f54])).
% 7.56/1.50  
% 7.56/1.50  fof(f60,plain,(
% 7.56/1.50    ( ! [X0,X1] : (sK2(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 7.56/1.50    inference(cnf_transformation,[],[f38])).
% 7.56/1.50  
% 7.56/1.50  fof(f106,plain,(
% 7.56/1.50    ( ! [X0,X1] : (sK2(X0,X1) != X1 | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 7.56/1.50    inference(definition_unfolding,[],[f60,f105])).
% 7.56/1.50  
% 7.56/1.50  fof(f94,plain,(
% 7.56/1.50    ( ! [X2,X0,X3,X1] : (v1_funct_1(X3) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.56/1.50    inference(cnf_transformation,[],[f29])).
% 7.56/1.50  
% 7.56/1.50  fof(f95,plain,(
% 7.56/1.50    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X1) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.56/1.50    inference(cnf_transformation,[],[f29])).
% 7.56/1.50  
% 7.56/1.50  fof(f14,axiom,(
% 7.56/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X2,X0,k1_tarski(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => r2_relset_1(X0,k1_tarski(X1),X2,X3)))),
% 7.56/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.50  
% 7.56/1.50  fof(f30,plain,(
% 7.56/1.50    ! [X0,X1,X2] : (! [X3] : (r2_relset_1(X0,k1_tarski(X1),X2,X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_2(X3,X0,k1_tarski(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_2(X2,X0,k1_tarski(X1)) | ~v1_funct_1(X2)))),
% 7.56/1.50    inference(ennf_transformation,[],[f14])).
% 7.56/1.50  
% 7.56/1.50  fof(f31,plain,(
% 7.56/1.50    ! [X0,X1,X2] : (! [X3] : (r2_relset_1(X0,k1_tarski(X1),X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_2(X3,X0,k1_tarski(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_2(X2,X0,k1_tarski(X1)) | ~v1_funct_1(X2))),
% 7.56/1.50    inference(flattening,[],[f30])).
% 7.56/1.50  
% 7.56/1.50  fof(f97,plain,(
% 7.56/1.50    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,k1_tarski(X1),X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_2(X3,X0,k1_tarski(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_2(X2,X0,k1_tarski(X1)) | ~v1_funct_1(X2)) )),
% 7.56/1.50    inference(cnf_transformation,[],[f31])).
% 7.56/1.50  
% 7.56/1.50  fof(f121,plain,(
% 7.56/1.50    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,k2_enumset1(X1,X1,X1,X1),X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1)))) | ~v1_funct_2(X3,X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1)))) | ~v1_funct_2(X2,X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_funct_1(X2)) )),
% 7.56/1.50    inference(definition_unfolding,[],[f97,f105,f105,f105,f105,f105])).
% 7.56/1.50  
% 7.56/1.50  fof(f101,plain,(
% 7.56/1.50    v1_funct_2(sK9,sK6,k1_tarski(sK7))),
% 7.56/1.50    inference(cnf_transformation,[],[f54])).
% 7.56/1.50  
% 7.56/1.50  fof(f124,plain,(
% 7.56/1.50    v1_funct_2(sK9,sK6,k2_enumset1(sK7,sK7,sK7,sK7))),
% 7.56/1.50    inference(definition_unfolding,[],[f101,f105])).
% 7.56/1.50  
% 7.56/1.50  fof(f9,axiom,(
% 7.56/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 7.56/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.50  
% 7.56/1.50  fof(f20,plain,(
% 7.56/1.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.56/1.50    inference(ennf_transformation,[],[f9])).
% 7.56/1.50  
% 7.56/1.50  fof(f21,plain,(
% 7.56/1.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.56/1.50    inference(flattening,[],[f20])).
% 7.56/1.50  
% 7.56/1.50  fof(f43,plain,(
% 7.56/1.50    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.56/1.50    inference(nnf_transformation,[],[f21])).
% 7.56/1.50  
% 7.56/1.50  fof(f74,plain,(
% 7.56/1.50    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.56/1.50    inference(cnf_transformation,[],[f43])).
% 7.56/1.50  
% 7.56/1.50  fof(f76,plain,(
% 7.56/1.50    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k5_partfun1(X1,X0,X2) != X3 | ~sP1(X0,X1,X2)) )),
% 7.56/1.50    inference(cnf_transformation,[],[f45])).
% 7.56/1.50  
% 7.56/1.50  fof(f135,plain,(
% 7.56/1.50    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k5_partfun1(X1,X0,X2)) | ~sP1(X0,X1,X2)) )),
% 7.56/1.50    inference(equality_resolution,[],[f76])).
% 7.56/1.50  
% 7.56/1.50  fof(f83,plain,(
% 7.56/1.50    ( ! [X2,X0,X8,X7,X3,X1] : (r2_hidden(X7,X3) | ~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8) | ~sP0(X0,X1,X2,X3)) )),
% 7.56/1.50    inference(cnf_transformation,[],[f51])).
% 7.56/1.50  
% 7.56/1.50  fof(f137,plain,(
% 7.56/1.50    ( ! [X2,X0,X8,X3,X1] : (r2_hidden(X8,X3) | ~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8) | ~sP0(X0,X1,X2,X3)) )),
% 7.56/1.50    inference(equality_resolution,[],[f83])).
% 7.56/1.50  
% 7.56/1.50  fof(f11,axiom,(
% 7.56/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 7.56/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.50  
% 7.56/1.50  fof(f24,plain,(
% 7.56/1.50    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.56/1.50    inference(ennf_transformation,[],[f11])).
% 7.56/1.50  
% 7.56/1.50  fof(f25,plain,(
% 7.56/1.50    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.56/1.50    inference(flattening,[],[f24])).
% 7.56/1.50  
% 7.56/1.50  fof(f91,plain,(
% 7.56/1.50    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.56/1.50    inference(cnf_transformation,[],[f25])).
% 7.56/1.50  
% 7.56/1.50  fof(f6,axiom,(
% 7.56/1.50    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 7.56/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.50  
% 7.56/1.50  fof(f18,plain,(
% 7.56/1.50    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 7.56/1.50    inference(ennf_transformation,[],[f6])).
% 7.56/1.50  
% 7.56/1.50  fof(f39,plain,(
% 7.56/1.50    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & ((k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3) | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 7.56/1.50    inference(nnf_transformation,[],[f18])).
% 7.56/1.50  
% 7.56/1.50  fof(f40,plain,(
% 7.56/1.50    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 7.56/1.50    inference(flattening,[],[f39])).
% 7.56/1.50  
% 7.56/1.50  fof(f63,plain,(
% 7.56/1.50    ( ! [X2,X0,X3,X1] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) | k1_tarski(X0) != X3) )),
% 7.56/1.50    inference(cnf_transformation,[],[f40])).
% 7.56/1.50  
% 7.56/1.50  fof(f114,plain,(
% 7.56/1.50    ( ! [X2,X0,X3,X1] : (r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) | k2_enumset1(X0,X0,X0,X0) != X3) )),
% 7.56/1.50    inference(definition_unfolding,[],[f63,f58,f105])).
% 7.56/1.50  
% 7.56/1.50  fof(f132,plain,(
% 7.56/1.50    ( ! [X2,X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X1,X2))) )),
% 7.56/1.50    inference(equality_resolution,[],[f114])).
% 7.56/1.50  
% 7.56/1.50  fof(f7,axiom,(
% 7.56/1.50    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 7.56/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.50  
% 7.56/1.50  fof(f41,plain,(
% 7.56/1.50    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 7.56/1.50    inference(nnf_transformation,[],[f7])).
% 7.56/1.50  
% 7.56/1.50  fof(f42,plain,(
% 7.56/1.50    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 7.56/1.50    inference(flattening,[],[f41])).
% 7.56/1.50  
% 7.56/1.50  fof(f71,plain,(
% 7.56/1.50    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 7.56/1.50    inference(cnf_transformation,[],[f42])).
% 7.56/1.50  
% 7.56/1.50  fof(f118,plain,(
% 7.56/1.50    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)) )),
% 7.56/1.50    inference(definition_unfolding,[],[f71,f104])).
% 7.56/1.50  
% 7.56/1.50  cnf(c_44,negated_conjecture,
% 7.56/1.50      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) ),
% 7.56/1.50      inference(cnf_transformation,[],[f125]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_1114,plain,
% 7.56/1.50      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) = iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_32,plain,
% 7.56/1.50      ( sP1(X0,X1,X2)
% 7.56/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.56/1.50      | ~ v1_funct_1(X2) ),
% 7.56/1.50      inference(cnf_transformation,[],[f90]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_1125,plain,
% 7.56/1.50      ( sP1(X0,X1,X2) = iProver_top
% 7.56/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 7.56/1.50      | v1_funct_1(X2) != iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_3538,plain,
% 7.56/1.50      ( sP1(k2_enumset1(sK7,sK7,sK7,sK7),sK6,sK8) = iProver_top
% 7.56/1.50      | v1_funct_1(sK8) != iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_1114,c_1125]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_45,negated_conjecture,
% 7.56/1.50      ( v1_funct_1(sK8) ),
% 7.56/1.50      inference(cnf_transformation,[],[f98]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_46,plain,
% 7.56/1.50      ( v1_funct_1(sK8) = iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_47,plain,
% 7.56/1.50      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) = iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_1555,plain,
% 7.56/1.50      ( sP1(X0,X1,sK8)
% 7.56/1.50      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.56/1.50      | ~ v1_funct_1(sK8) ),
% 7.56/1.50      inference(instantiation,[status(thm)],[c_32]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_1859,plain,
% 7.56/1.50      ( sP1(k2_enumset1(sK7,sK7,sK7,sK7),sK6,sK8)
% 7.56/1.50      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))))
% 7.56/1.50      | ~ v1_funct_1(sK8) ),
% 7.56/1.50      inference(instantiation,[status(thm)],[c_1555]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_1860,plain,
% 7.56/1.50      ( sP1(k2_enumset1(sK7,sK7,sK7,sK7),sK6,sK8) = iProver_top
% 7.56/1.50      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) != iProver_top
% 7.56/1.50      | v1_funct_1(sK8) != iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_1859]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_3650,plain,
% 7.56/1.50      ( sP1(k2_enumset1(sK7,sK7,sK7,sK7),sK6,sK8) = iProver_top ),
% 7.56/1.50      inference(global_propositional_subsumption,
% 7.56/1.50                [status(thm)],
% 7.56/1.50                [c_3538,c_46,c_47,c_1860]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_0,plain,
% 7.56/1.50      ( r1_tarski(k1_xboole_0,X0) ),
% 7.56/1.50      inference(cnf_transformation,[],[f55]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_1156,plain,
% 7.56/1.50      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_23,plain,
% 7.56/1.50      ( sP0(X0,X1,X2,X3)
% 7.56/1.50      | r2_hidden(sK3(X0,X1,X2,X3),X3)
% 7.56/1.50      | sK4(X0,X1,X2,X3) = sK3(X0,X1,X2,X3) ),
% 7.56/1.50      inference(cnf_transformation,[],[f86]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_1134,plain,
% 7.56/1.50      ( sK4(X0,X1,X2,X3) = sK3(X0,X1,X2,X3)
% 7.56/1.50      | sP0(X0,X1,X2,X3) = iProver_top
% 7.56/1.50      | r2_hidden(sK3(X0,X1,X2,X3),X3) = iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_15,plain,
% 7.56/1.50      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 7.56/1.50      inference(cnf_transformation,[],[f73]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_1142,plain,
% 7.56/1.50      ( r2_hidden(X0,X1) != iProver_top | r1_tarski(X1,X0) != iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_7469,plain,
% 7.56/1.50      ( sK4(X0,X1,X2,X3) = sK3(X0,X1,X2,X3)
% 7.56/1.50      | sP0(X0,X1,X2,X3) = iProver_top
% 7.56/1.50      | r1_tarski(X3,sK3(X0,X1,X2,X3)) != iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_1134,c_1142]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_19865,plain,
% 7.56/1.50      ( sK4(X0,X1,X2,k1_xboole_0) = sK3(X0,X1,X2,k1_xboole_0)
% 7.56/1.50      | sP0(X0,X1,X2,k1_xboole_0) = iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_1156,c_7469]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_18,plain,
% 7.56/1.50      ( ~ sP0(X0,X1,X2,X3) | ~ sP1(X2,X1,X0) | k5_partfun1(X1,X2,X0) = X3 ),
% 7.56/1.50      inference(cnf_transformation,[],[f77]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_1139,plain,
% 7.56/1.50      ( k5_partfun1(X0,X1,X2) = X3
% 7.56/1.50      | sP0(X2,X0,X1,X3) != iProver_top
% 7.56/1.50      | sP1(X1,X0,X2) != iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_21539,plain,
% 7.56/1.50      ( sK4(X0,X1,X2,k1_xboole_0) = sK3(X0,X1,X2,k1_xboole_0)
% 7.56/1.50      | k5_partfun1(X1,X2,X0) = k1_xboole_0
% 7.56/1.50      | sP1(X2,X1,X0) != iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_19865,c_1139]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_24039,plain,
% 7.56/1.50      ( sK4(sK8,sK6,k2_enumset1(sK7,sK7,sK7,sK7),k1_xboole_0) = sK3(sK8,sK6,k2_enumset1(sK7,sK7,sK7,sK7),k1_xboole_0)
% 7.56/1.50      | k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k1_xboole_0 ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_3650,c_21539]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_36,plain,
% 7.56/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.56/1.50      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.56/1.50      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 7.56/1.50      | ~ v1_funct_1(X0) ),
% 7.56/1.50      inference(cnf_transformation,[],[f96]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_2,plain,
% 7.56/1.50      ( r2_hidden(sK2(X0,X1),X0)
% 7.56/1.50      | k2_enumset1(X1,X1,X1,X1) = X0
% 7.56/1.50      | k1_xboole_0 = X0 ),
% 7.56/1.50      inference(cnf_transformation,[],[f107]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_40,negated_conjecture,
% 7.56/1.50      ( k2_enumset1(sK9,sK9,sK9,sK9) != k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) ),
% 7.56/1.50      inference(cnf_transformation,[],[f122]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_3404,plain,
% 7.56/1.50      ( r2_hidden(sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),sK9),k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8))
% 7.56/1.50      | k1_xboole_0 = k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) ),
% 7.56/1.50      inference(resolution,[status(thm)],[c_2,c_40]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_8873,plain,
% 7.56/1.50      ( m1_subset_1(sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),sK9),k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))))
% 7.56/1.50      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))))
% 7.56/1.50      | ~ v1_funct_1(sK8)
% 7.56/1.50      | k1_xboole_0 = k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) ),
% 7.56/1.50      inference(resolution,[status(thm)],[c_36,c_3404]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_17984,plain,
% 7.56/1.50      ( m1_subset_1(sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),sK9),k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))))
% 7.56/1.50      | k1_xboole_0 = k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) ),
% 7.56/1.50      inference(global_propositional_subsumption,
% 7.56/1.50                [status(thm)],
% 7.56/1.50                [c_8873,c_45,c_44]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_35,plain,
% 7.56/1.50      ( r1_partfun1(X0,X1)
% 7.56/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))))
% 7.56/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))))
% 7.56/1.50      | ~ v1_funct_1(X0)
% 7.56/1.50      | ~ v1_funct_1(X1) ),
% 7.56/1.50      inference(cnf_transformation,[],[f120]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_41,negated_conjecture,
% 7.56/1.50      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) ),
% 7.56/1.50      inference(cnf_transformation,[],[f123]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_10695,plain,
% 7.56/1.50      ( r1_partfun1(sK9,X0)
% 7.56/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))))
% 7.56/1.50      | ~ v1_funct_1(X0)
% 7.56/1.50      | ~ v1_funct_1(sK9) ),
% 7.56/1.50      inference(resolution,[status(thm)],[c_35,c_41]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_43,negated_conjecture,
% 7.56/1.50      ( v1_funct_1(sK9) ),
% 7.56/1.50      inference(cnf_transformation,[],[f100]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_11460,plain,
% 7.56/1.50      ( ~ v1_funct_1(X0)
% 7.56/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))))
% 7.56/1.50      | r1_partfun1(sK9,X0) ),
% 7.56/1.50      inference(global_propositional_subsumption,[status(thm)],[c_10695,c_43]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_11461,plain,
% 7.56/1.50      ( r1_partfun1(sK9,X0)
% 7.56/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))))
% 7.56/1.50      | ~ v1_funct_1(X0) ),
% 7.56/1.50      inference(renaming,[status(thm)],[c_11460]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_18520,plain,
% 7.56/1.50      ( r1_partfun1(sK9,sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),sK9))
% 7.56/1.50      | ~ v1_funct_1(sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),sK9))
% 7.56/1.50      | k1_xboole_0 = k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) ),
% 7.56/1.50      inference(resolution,[status(thm)],[c_17984,c_11461]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_1,plain,
% 7.56/1.50      ( k2_enumset1(X0,X0,X0,X0) = X1 | sK2(X1,X0) != X0 | k1_xboole_0 = X1 ),
% 7.56/1.50      inference(cnf_transformation,[],[f106]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_6167,plain,
% 7.56/1.50      ( sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),sK9) != sK9
% 7.56/1.50      | k1_xboole_0 = k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) ),
% 7.56/1.50      inference(resolution,[status(thm)],[c_1,c_40]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_38,plain,
% 7.56/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.56/1.50      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 7.56/1.50      | ~ v1_funct_1(X0)
% 7.56/1.50      | v1_funct_1(X3) ),
% 7.56/1.50      inference(cnf_transformation,[],[f94]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_7572,plain,
% 7.56/1.50      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))))
% 7.56/1.50      | v1_funct_1(sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),sK9))
% 7.56/1.50      | ~ v1_funct_1(sK8)
% 7.56/1.50      | k1_xboole_0 = k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) ),
% 7.56/1.50      inference(resolution,[status(thm)],[c_38,c_3404]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_7644,plain,
% 7.56/1.50      ( v1_funct_1(sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),sK9))
% 7.56/1.50      | k1_xboole_0 = k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) ),
% 7.56/1.50      inference(global_propositional_subsumption,
% 7.56/1.50                [status(thm)],
% 7.56/1.50                [c_7572,c_45,c_44]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_37,plain,
% 7.56/1.50      ( v1_funct_2(X0,X1,X2)
% 7.56/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.56/1.50      | ~ r2_hidden(X0,k5_partfun1(X1,X2,X3))
% 7.56/1.50      | ~ v1_funct_1(X3) ),
% 7.56/1.50      inference(cnf_transformation,[],[f95]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_7610,plain,
% 7.56/1.50      ( v1_funct_2(sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),sK9),sK6,k2_enumset1(sK7,sK7,sK7,sK7))
% 7.56/1.50      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))))
% 7.56/1.50      | ~ v1_funct_1(sK8)
% 7.56/1.50      | k1_xboole_0 = k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) ),
% 7.56/1.50      inference(resolution,[status(thm)],[c_37,c_3404]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_7689,plain,
% 7.56/1.50      ( v1_funct_2(sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),sK9),sK6,k2_enumset1(sK7,sK7,sK7,sK7))
% 7.56/1.50      | k1_xboole_0 = k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) ),
% 7.56/1.50      inference(global_propositional_subsumption,
% 7.56/1.50                [status(thm)],
% 7.56/1.50                [c_7610,c_45,c_44]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_39,plain,
% 7.56/1.50      ( r2_relset_1(X0,k2_enumset1(X1,X1,X1,X1),X2,X3)
% 7.56/1.50      | ~ v1_funct_2(X3,X0,k2_enumset1(X1,X1,X1,X1))
% 7.56/1.50      | ~ v1_funct_2(X2,X0,k2_enumset1(X1,X1,X1,X1))
% 7.56/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))))
% 7.56/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))))
% 7.56/1.50      | ~ v1_funct_1(X2)
% 7.56/1.50      | ~ v1_funct_1(X3) ),
% 7.56/1.50      inference(cnf_transformation,[],[f121]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_13169,plain,
% 7.56/1.50      ( r2_relset_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9,X0)
% 7.56/1.50      | ~ v1_funct_2(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7))
% 7.56/1.50      | ~ v1_funct_2(sK9,sK6,k2_enumset1(sK7,sK7,sK7,sK7))
% 7.56/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))))
% 7.56/1.50      | ~ v1_funct_1(X0)
% 7.56/1.50      | ~ v1_funct_1(sK9) ),
% 7.56/1.50      inference(resolution,[status(thm)],[c_39,c_41]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_42,negated_conjecture,
% 7.56/1.50      ( v1_funct_2(sK9,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) ),
% 7.56/1.50      inference(cnf_transformation,[],[f124]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_14977,plain,
% 7.56/1.50      ( ~ v1_funct_1(X0)
% 7.56/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))))
% 7.56/1.50      | r2_relset_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9,X0)
% 7.56/1.50      | ~ v1_funct_2(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7)) ),
% 7.56/1.50      inference(global_propositional_subsumption,
% 7.56/1.50                [status(thm)],
% 7.56/1.50                [c_13169,c_43,c_42]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_14978,plain,
% 7.56/1.50      ( r2_relset_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9,X0)
% 7.56/1.50      | ~ v1_funct_2(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7))
% 7.56/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))))
% 7.56/1.50      | ~ v1_funct_1(X0) ),
% 7.56/1.50      inference(renaming,[status(thm)],[c_14977]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_18522,plain,
% 7.56/1.50      ( r2_relset_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9,sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),sK9))
% 7.56/1.50      | ~ v1_funct_2(sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),sK9),sK6,k2_enumset1(sK7,sK7,sK7,sK7))
% 7.56/1.50      | ~ v1_funct_1(sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),sK9))
% 7.56/1.50      | k1_xboole_0 = k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) ),
% 7.56/1.50      inference(resolution,[status(thm)],[c_17984,c_14978]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_17,plain,
% 7.56/1.50      ( ~ r2_relset_1(X0,X1,X2,X3)
% 7.56/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.56/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.56/1.50      | X3 = X2 ),
% 7.56/1.50      inference(cnf_transformation,[],[f74]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_9048,plain,
% 7.56/1.50      ( ~ r2_relset_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9,X0)
% 7.56/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))))
% 7.56/1.50      | X0 = sK9 ),
% 7.56/1.50      inference(resolution,[status(thm)],[c_17,c_41]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_18518,plain,
% 7.56/1.50      ( ~ r2_relset_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK9,sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),sK9))
% 7.56/1.50      | sK2(k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8),sK9) = sK9
% 7.56/1.50      | k1_xboole_0 = k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) ),
% 7.56/1.50      inference(resolution,[status(thm)],[c_17984,c_9048]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_18529,plain,
% 7.56/1.50      ( k1_xboole_0 = k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) ),
% 7.56/1.50      inference(global_propositional_subsumption,
% 7.56/1.50                [status(thm)],
% 7.56/1.50                [c_18520,c_6167,c_7644,c_7689,c_18522,c_18518]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_394,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_393,plain,( X0 = X0 ),theory(equality) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_2672,plain,
% 7.56/1.50      ( X0 != X1 | X1 = X0 ),
% 7.56/1.50      inference(resolution,[status(thm)],[c_394,c_393]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_18535,plain,
% 7.56/1.50      ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k1_xboole_0 ),
% 7.56/1.50      inference(resolution,[status(thm)],[c_18529,c_2672]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_24703,plain,
% 7.56/1.50      ( k5_partfun1(sK6,k2_enumset1(sK7,sK7,sK7,sK7),sK8) = k1_xboole_0 ),
% 7.56/1.50      inference(global_propositional_subsumption,
% 7.56/1.50                [status(thm)],
% 7.56/1.50                [c_24039,c_18535]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_19,plain,
% 7.56/1.50      ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0)) | ~ sP1(X2,X1,X0) ),
% 7.56/1.50      inference(cnf_transformation,[],[f135]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_1138,plain,
% 7.56/1.50      ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0)) = iProver_top
% 7.56/1.50      | sP1(X2,X1,X0) != iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_24814,plain,
% 7.56/1.50      ( sP0(sK8,sK6,k2_enumset1(sK7,sK7,sK7,sK7),k1_xboole_0) = iProver_top
% 7.56/1.50      | sP1(k2_enumset1(sK7,sK7,sK7,sK7),sK6,sK8) != iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_24703,c_1138]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_403,plain,
% 7.56/1.50      ( ~ sP0(X0,X1,X2,X3) | sP0(X0,X1,X2,X4) | X4 != X3 ),
% 7.56/1.50      theory(equality) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_3250,plain,
% 7.56/1.50      ( sP0(X0,X1,X2,X3) | ~ sP1(X2,X1,X0) | X3 != k5_partfun1(X1,X2,X0) ),
% 7.56/1.50      inference(resolution,[status(thm)],[c_403,c_19]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_18582,plain,
% 7.56/1.50      ( sP0(sK8,sK6,k2_enumset1(sK7,sK7,sK7,sK7),k1_xboole_0)
% 7.56/1.50      | ~ sP1(k2_enumset1(sK7,sK7,sK7,sK7),sK6,sK8) ),
% 7.56/1.50      inference(resolution,[status(thm)],[c_18529,c_3250]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_18583,plain,
% 7.56/1.50      ( sP0(sK8,sK6,k2_enumset1(sK7,sK7,sK7,sK7),k1_xboole_0) = iProver_top
% 7.56/1.50      | sP1(k2_enumset1(sK7,sK7,sK7,sK7),sK6,sK8) != iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_18582]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_26157,plain,
% 7.56/1.50      ( sP0(sK8,sK6,k2_enumset1(sK7,sK7,sK7,sK7),k1_xboole_0) = iProver_top ),
% 7.56/1.50      inference(global_propositional_subsumption,
% 7.56/1.50                [status(thm)],
% 7.56/1.50                [c_24814,c_46,c_47,c_1860,c_18583]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_1117,plain,
% 7.56/1.50      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) = iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_26,plain,
% 7.56/1.50      ( ~ sP0(X0,X1,X2,X3)
% 7.56/1.50      | ~ v1_partfun1(X4,X1)
% 7.56/1.50      | ~ r1_partfun1(X0,X4)
% 7.56/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.56/1.50      | r2_hidden(X4,X3)
% 7.56/1.50      | ~ v1_funct_1(X4) ),
% 7.56/1.50      inference(cnf_transformation,[],[f137]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_1131,plain,
% 7.56/1.50      ( sP0(X0,X1,X2,X3) != iProver_top
% 7.56/1.50      | v1_partfun1(X4,X1) != iProver_top
% 7.56/1.50      | r1_partfun1(X0,X4) != iProver_top
% 7.56/1.50      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.56/1.50      | r2_hidden(X4,X3) = iProver_top
% 7.56/1.50      | v1_funct_1(X4) != iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_8014,plain,
% 7.56/1.50      ( sP0(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7),X1) != iProver_top
% 7.56/1.50      | v1_partfun1(sK9,sK6) != iProver_top
% 7.56/1.50      | r1_partfun1(X0,sK9) != iProver_top
% 7.56/1.50      | r2_hidden(sK9,X1) = iProver_top
% 7.56/1.50      | v1_funct_1(sK9) != iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_1117,c_1131]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_48,plain,
% 7.56/1.50      ( v1_funct_1(sK9) = iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_9428,plain,
% 7.56/1.50      ( r2_hidden(sK9,X1) = iProver_top
% 7.56/1.50      | r1_partfun1(X0,sK9) != iProver_top
% 7.56/1.50      | v1_partfun1(sK9,sK6) != iProver_top
% 7.56/1.50      | sP0(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7),X1) != iProver_top ),
% 7.56/1.50      inference(global_propositional_subsumption,[status(thm)],[c_8014,c_48]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_9429,plain,
% 7.56/1.50      ( sP0(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7),X1) != iProver_top
% 7.56/1.50      | v1_partfun1(sK9,sK6) != iProver_top
% 7.56/1.50      | r1_partfun1(X0,sK9) != iProver_top
% 7.56/1.50      | r2_hidden(sK9,X1) = iProver_top ),
% 7.56/1.50      inference(renaming,[status(thm)],[c_9428]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_26169,plain,
% 7.56/1.50      ( v1_partfun1(sK9,sK6) != iProver_top
% 7.56/1.50      | r1_partfun1(sK8,sK9) != iProver_top
% 7.56/1.50      | r2_hidden(sK9,k1_xboole_0) = iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_26157,c_9429]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_50,plain,
% 7.56/1.50      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) = iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_1750,plain,
% 7.56/1.50      ( r1_partfun1(X0,sK9)
% 7.56/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_enumset1(X2,X2,X2,X2))))
% 7.56/1.50      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X1,k2_enumset1(X2,X2,X2,X2))))
% 7.56/1.50      | ~ v1_funct_1(X0)
% 7.56/1.50      | ~ v1_funct_1(sK9) ),
% 7.56/1.50      inference(instantiation,[status(thm)],[c_35]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_1962,plain,
% 7.56/1.50      ( r1_partfun1(sK8,sK9)
% 7.56/1.50      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))))
% 7.56/1.50      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(X1,X1,X1,X1))))
% 7.56/1.50      | ~ v1_funct_1(sK8)
% 7.56/1.50      | ~ v1_funct_1(sK9) ),
% 7.56/1.50      inference(instantiation,[status(thm)],[c_1750]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_2006,plain,
% 7.56/1.50      ( r1_partfun1(sK8,sK9)
% 7.56/1.50      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))))
% 7.56/1.50      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7))))
% 7.56/1.50      | ~ v1_funct_1(sK8)
% 7.56/1.50      | ~ v1_funct_1(sK9) ),
% 7.56/1.50      inference(instantiation,[status(thm)],[c_1962]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_2007,plain,
% 7.56/1.50      ( r1_partfun1(sK8,sK9) = iProver_top
% 7.56/1.50      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) != iProver_top
% 7.56/1.50      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_enumset1(sK7,sK7,sK7,sK7)))) != iProver_top
% 7.56/1.50      | v1_funct_1(sK8) != iProver_top
% 7.56/1.50      | v1_funct_1(sK9) != iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_2006]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_20356,plain,
% 7.56/1.50      ( sP0(sK8,sK6,k2_enumset1(sK7,sK7,sK7,sK7),k1_xboole_0) ),
% 7.56/1.50      inference(global_propositional_subsumption,
% 7.56/1.50                [status(thm)],
% 7.56/1.50                [c_18582,c_45,c_44,c_1859]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_397,plain,
% 7.56/1.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.56/1.50      theory(equality) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_3593,plain,
% 7.56/1.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 7.56/1.50      inference(resolution,[status(thm)],[c_397,c_393]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_34,plain,
% 7.56/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.56/1.50      | v1_partfun1(X0,X1)
% 7.56/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.56/1.50      | ~ v1_funct_1(X0)
% 7.56/1.50      | k1_xboole_0 = X2 ),
% 7.56/1.50      inference(cnf_transformation,[],[f91]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_8839,plain,
% 7.56/1.50      ( ~ v1_funct_2(sK9,sK6,k2_enumset1(sK7,sK7,sK7,sK7))
% 7.56/1.50      | v1_partfun1(sK9,sK6)
% 7.56/1.50      | ~ v1_funct_1(sK9)
% 7.56/1.50      | k1_xboole_0 = k2_enumset1(sK7,sK7,sK7,sK7) ),
% 7.56/1.50      inference(resolution,[status(thm)],[c_34,c_41]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_9092,plain,
% 7.56/1.50      ( v1_partfun1(sK9,sK6) | k1_xboole_0 = k2_enumset1(sK7,sK7,sK7,sK7) ),
% 7.56/1.50      inference(global_propositional_subsumption,
% 7.56/1.50                [status(thm)],
% 7.56/1.50                [c_8839,c_43,c_42]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_14103,plain,
% 7.56/1.50      ( v1_partfun1(sK9,sK6)
% 7.56/1.50      | ~ r2_hidden(k2_enumset1(sK7,sK7,sK7,sK7),X0)
% 7.56/1.50      | r2_hidden(k1_xboole_0,X0) ),
% 7.56/1.50      inference(resolution,[status(thm)],[c_3593,c_9092]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_9,plain,
% 7.56/1.50      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X1,X2)) ),
% 7.56/1.50      inference(cnf_transformation,[],[f132]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_136,plain,
% 7.56/1.50      ( r1_tarski(k2_enumset1(sK7,sK7,sK7,sK7),k2_enumset1(sK7,sK7,sK7,sK7)) ),
% 7.56/1.50      inference(instantiation,[status(thm)],[c_9]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_149,plain,
% 7.56/1.50      ( r1_tarski(k1_xboole_0,sK7) ),
% 7.56/1.50      inference(instantiation,[status(thm)],[c_0]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_13,plain,
% 7.56/1.50      ( r2_hidden(X0,X1) | ~ r1_tarski(k2_enumset1(X2,X2,X2,X0),X1) ),
% 7.56/1.50      inference(cnf_transformation,[],[f118]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_1560,plain,
% 7.56/1.50      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0))
% 7.56/1.50      | ~ r1_tarski(k2_enumset1(X1,X1,X1,X0),k2_enumset1(X1,X1,X1,X0)) ),
% 7.56/1.50      inference(instantiation,[status(thm)],[c_13]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_1562,plain,
% 7.56/1.50      ( r2_hidden(sK7,k2_enumset1(sK7,sK7,sK7,sK7))
% 7.56/1.50      | ~ r1_tarski(k2_enumset1(sK7,sK7,sK7,sK7),k2_enumset1(sK7,sK7,sK7,sK7)) ),
% 7.56/1.50      inference(instantiation,[status(thm)],[c_1560]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_2082,plain,
% 7.56/1.50      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X0))
% 7.56/1.50      | ~ r1_tarski(k2_enumset1(X1,X1,X1,X0),X0) ),
% 7.56/1.50      inference(instantiation,[status(thm)],[c_15]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_2084,plain,
% 7.56/1.50      ( ~ r2_hidden(sK7,k2_enumset1(sK7,sK7,sK7,sK7))
% 7.56/1.50      | ~ r1_tarski(k2_enumset1(sK7,sK7,sK7,sK7),sK7) ),
% 7.56/1.50      inference(instantiation,[status(thm)],[c_2082]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_395,plain,
% 7.56/1.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.56/1.50      theory(equality) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_3575,plain,
% 7.56/1.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 7.56/1.50      inference(resolution,[status(thm)],[c_395,c_393]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_9298,plain,
% 7.56/1.50      ( v1_partfun1(sK9,sK6) | k2_enumset1(sK7,sK7,sK7,sK7) = k1_xboole_0 ),
% 7.56/1.50      inference(resolution,[status(thm)],[c_9092,c_2672]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_14048,plain,
% 7.56/1.50      ( v1_partfun1(sK9,sK6)
% 7.56/1.50      | r1_tarski(k2_enumset1(sK7,sK7,sK7,sK7),X0)
% 7.56/1.50      | ~ r1_tarski(k1_xboole_0,X0) ),
% 7.56/1.50      inference(resolution,[status(thm)],[c_3575,c_9298]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_14050,plain,
% 7.56/1.50      ( v1_partfun1(sK9,sK6)
% 7.56/1.50      | r1_tarski(k2_enumset1(sK7,sK7,sK7,sK7),sK7)
% 7.56/1.50      | ~ r1_tarski(k1_xboole_0,sK7) ),
% 7.56/1.50      inference(instantiation,[status(thm)],[c_14048]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_16635,plain,
% 7.56/1.50      ( v1_partfun1(sK9,sK6) ),
% 7.56/1.50      inference(global_propositional_subsumption,
% 7.56/1.50                [status(thm)],
% 7.56/1.50                [c_14103,c_136,c_149,c_1562,c_2084,c_14050]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_10675,plain,
% 7.56/1.50      ( ~ sP0(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7),X1)
% 7.56/1.50      | ~ v1_partfun1(sK9,sK6)
% 7.56/1.50      | ~ r1_partfun1(X0,sK9)
% 7.56/1.50      | r2_hidden(sK9,X1)
% 7.56/1.50      | ~ v1_funct_1(sK9) ),
% 7.56/1.50      inference(resolution,[status(thm)],[c_26,c_41]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_9430,plain,
% 7.56/1.50      ( ~ sP0(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7),X1)
% 7.56/1.50      | ~ v1_partfun1(sK9,sK6)
% 7.56/1.50      | ~ r1_partfun1(X0,sK9)
% 7.56/1.50      | r2_hidden(sK9,X1) ),
% 7.56/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_9429]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_12483,plain,
% 7.56/1.50      ( r2_hidden(sK9,X1)
% 7.56/1.50      | ~ r1_partfun1(X0,sK9)
% 7.56/1.50      | ~ v1_partfun1(sK9,sK6)
% 7.56/1.50      | ~ sP0(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7),X1) ),
% 7.56/1.50      inference(global_propositional_subsumption,
% 7.56/1.50                [status(thm)],
% 7.56/1.50                [c_10675,c_9430]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_12484,plain,
% 7.56/1.50      ( ~ sP0(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7),X1)
% 7.56/1.50      | ~ v1_partfun1(sK9,sK6)
% 7.56/1.50      | ~ r1_partfun1(X0,sK9)
% 7.56/1.50      | r2_hidden(sK9,X1) ),
% 7.56/1.50      inference(renaming,[status(thm)],[c_12483]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_16964,plain,
% 7.56/1.50      ( ~ sP0(X0,sK6,k2_enumset1(sK7,sK7,sK7,sK7),X1)
% 7.56/1.50      | ~ r1_partfun1(X0,sK9)
% 7.56/1.50      | r2_hidden(sK9,X1) ),
% 7.56/1.50      inference(backward_subsumption_resolution,
% 7.56/1.50                [status(thm)],
% 7.56/1.50                [c_16635,c_12484]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_20393,plain,
% 7.56/1.50      ( ~ r1_partfun1(sK8,sK9) | r2_hidden(sK9,k1_xboole_0) ),
% 7.56/1.50      inference(resolution,[status(thm)],[c_20356,c_16964]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_20394,plain,
% 7.56/1.50      ( r1_partfun1(sK8,sK9) != iProver_top
% 7.56/1.50      | r2_hidden(sK9,k1_xboole_0) = iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_20393]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_26511,plain,
% 7.56/1.50      ( r2_hidden(sK9,k1_xboole_0) = iProver_top ),
% 7.56/1.50      inference(global_propositional_subsumption,
% 7.56/1.50                [status(thm)],
% 7.56/1.50                [c_26169,c_46,c_47,c_48,c_50,c_2007,c_20394]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_26517,plain,
% 7.56/1.50      ( r1_tarski(k1_xboole_0,sK9) != iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_26511,c_1142]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_27793,plain,
% 7.56/1.50      ( $false ),
% 7.56/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_26517,c_1156]) ).
% 7.56/1.50  
% 7.56/1.50  
% 7.56/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.56/1.50  
% 7.56/1.50  ------                               Statistics
% 7.56/1.50  
% 7.56/1.50  ------ Selected
% 7.56/1.50  
% 7.56/1.50  total_time:                             0.84
% 7.56/1.50  
%------------------------------------------------------------------------------
