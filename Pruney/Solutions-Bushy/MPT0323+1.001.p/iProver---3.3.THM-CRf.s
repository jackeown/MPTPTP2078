%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0323+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:00 EST 2020

% Result     : Theorem 35.53s
% Output     : CNFRefutation 35.53s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 212 expanded)
%              Number of clauses        :   43 (  45 expanded)
%              Number of leaves         :   13 (  63 expanded)
%              Depth                    :   14
%              Number of atoms          :  428 (1449 expanded)
%              Number of equality atoms :   27 (  27 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & ~ r2_tarski(X2,X1)
            & r1_tarski(X2,X1) )
      & ! [X2] :
          ~ ( ! [X3] :
                ~ ( ! [X4] :
                      ( r1_tarski(X4,X2)
                     => r2_hidden(X4,X3) )
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X1) )
      & ! [X2,X3] :
          ( ( r1_tarski(X3,X2)
            & r2_hidden(X2,X1) )
         => r2_hidden(X3,X1) )
      & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & ~ r2_tarski(X2,X1)
            & r1_tarski(X2,X1) )
      & ! [X3] :
          ~ ( ! [X4] :
                ~ ( ! [X5] :
                      ( r1_tarski(X5,X3)
                     => r2_hidden(X5,X4) )
                  & r2_hidden(X4,X1) )
            & r2_hidden(X3,X1) )
      & ! [X6,X7] :
          ( ( r1_tarski(X7,X6)
            & r2_hidden(X6,X1) )
         => r2_hidden(X7,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(rectify,[],[f3])).

fof(f9,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | r2_tarski(X2,X1)
          | ~ r1_tarski(X2,X1) )
      & ! [X3] :
          ( ? [X4] :
              ( ! [X5] :
                  ( r2_hidden(X5,X4)
                  | ~ r1_tarski(X5,X3) )
              & r2_hidden(X4,X1) )
          | ~ r2_hidden(X3,X1) )
      & ! [X6,X7] :
          ( r2_hidden(X7,X1)
          | ~ r1_tarski(X7,X6)
          | ~ r2_hidden(X6,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f10,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | r2_tarski(X2,X1)
          | ~ r1_tarski(X2,X1) )
      & ! [X3] :
          ( ? [X4] :
              ( ! [X5] :
                  ( r2_hidden(X5,X4)
                  | ~ r1_tarski(X5,X3) )
              & r2_hidden(X4,X1) )
          | ~ r2_hidden(X3,X1) )
      & ! [X6,X7] :
          ( r2_hidden(X7,X1)
          | ~ r1_tarski(X7,X6)
          | ~ r2_hidden(X6,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f24,plain,(
    ! [X1,X3,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( r2_hidden(X5,X4)
              | ~ r1_tarski(X5,X3) )
          & r2_hidden(X4,X1) )
     => ( ! [X5] :
            ( r2_hidden(X5,sK4(X0,X3))
            | ~ r1_tarski(X5,X3) )
        & r2_hidden(sK4(X0,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | r2_tarski(X2,X1)
              | ~ r1_tarski(X2,X1) )
          & ! [X3] :
              ( ? [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X4)
                      | ~ r1_tarski(X5,X3) )
                  & r2_hidden(X4,X1) )
              | ~ r2_hidden(X3,X1) )
          & ! [X6,X7] :
              ( r2_hidden(X7,X1)
              | ~ r1_tarski(X7,X6)
              | ~ r2_hidden(X6,X1) )
          & r2_hidden(X0,X1) )
     => ( ! [X2] :
            ( r2_hidden(X2,sK3(X0))
            | r2_tarski(X2,sK3(X0))
            | ~ r1_tarski(X2,sK3(X0)) )
        & ! [X3] :
            ( ? [X4] :
                ( ! [X5] :
                    ( r2_hidden(X5,X4)
                    | ~ r1_tarski(X5,X3) )
                & r2_hidden(X4,sK3(X0)) )
            | ~ r2_hidden(X3,sK3(X0)) )
        & ! [X7,X6] :
            ( r2_hidden(X7,sK3(X0))
            | ~ r1_tarski(X7,X6)
            | ~ r2_hidden(X6,sK3(X0)) )
        & r2_hidden(X0,sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X2] :
          ( r2_hidden(X2,sK3(X0))
          | r2_tarski(X2,sK3(X0))
          | ~ r1_tarski(X2,sK3(X0)) )
      & ! [X3] :
          ( ( ! [X5] :
                ( r2_hidden(X5,sK4(X0,X3))
                | ~ r1_tarski(X5,X3) )
            & r2_hidden(sK4(X0,X3),sK3(X0)) )
          | ~ r2_hidden(X3,sK3(X0)) )
      & ! [X6,X7] :
          ( r2_hidden(X7,sK3(X0))
          | ~ r1_tarski(X7,X6)
          | ~ r2_hidden(X6,sK3(X0)) )
      & r2_hidden(X0,sK3(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f10,f24,f23])).

fof(f44,plain,(
    ! [X0,X5,X3] :
      ( r2_hidden(X5,sK4(X0,X3))
      | ~ r1_tarski(X5,X3)
      | ~ r2_hidden(X3,sK3(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f15])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK1(X0,X1),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( r1_tarski(sK1(X0,X1),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK1(X0,X1),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r1_tarski(sK1(X0,X1),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f17])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f56,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f42,plain,(
    ! [X6,X0,X7] :
      ( r2_hidden(X7,sK3(X0))
      | ~ r1_tarski(X7,X6)
      | ~ r2_hidden(X6,sK3(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f43,plain,(
    ! [X0,X3] :
      ( r2_hidden(sK4(X0,X3),sK3(X0))
      | ~ r2_hidden(X3,sK3(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f45,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,sK3(X0))
      | r2_tarski(X2,sK3(X0))
      | ~ r1_tarski(X2,sK3(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,conjecture,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & ~ r2_tarski(X2,X1)
            & r1_tarski(X2,X1) )
      & ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(k1_zfmisc_1(X2),X1) )
      & ! [X2,X3] :
          ( ( r1_tarski(X3,X2)
            & r2_hidden(X2,X1) )
         => r2_hidden(X3,X1) )
      & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
      ? [X1] :
        ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X1)
              & ~ r2_tarski(X2,X1)
              & r1_tarski(X2,X1) )
        & ! [X2] :
            ( r2_hidden(X2,X1)
           => r2_hidden(k1_zfmisc_1(X2),X1) )
        & ! [X2,X3] :
            ( ( r1_tarski(X3,X2)
              & r2_hidden(X2,X1) )
           => r2_hidden(X3,X1) )
        & r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f7,plain,(
    ~ ! [X0] :
      ? [X1] :
        ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X1)
              & ~ r2_tarski(X2,X1)
              & r1_tarski(X2,X1) )
        & ! [X3] :
            ( r2_hidden(X3,X1)
           => r2_hidden(k1_zfmisc_1(X3),X1) )
        & ! [X4,X5] :
            ( ( r1_tarski(X5,X4)
              & r2_hidden(X4,X1) )
           => r2_hidden(X5,X1) )
        & r2_hidden(X0,X1) ) ),
    inference(rectify,[],[f5])).

fof(f11,plain,(
    ? [X0] :
    ! [X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & ~ r2_tarski(X2,X1)
          & r1_tarski(X2,X1) )
      | ? [X3] :
          ( ~ r2_hidden(k1_zfmisc_1(X3),X1)
          & r2_hidden(X3,X1) )
      | ? [X4,X5] :
          ( ~ r2_hidden(X5,X1)
          & r1_tarski(X5,X4)
          & r2_hidden(X4,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f12,plain,(
    ? [X0] :
    ! [X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & ~ r2_tarski(X2,X1)
          & r1_tarski(X2,X1) )
      | ? [X3] :
          ( ~ r2_hidden(k1_zfmisc_1(X3),X1)
          & r2_hidden(X3,X1) )
      | ? [X4,X5] :
          ( ~ r2_hidden(X5,X1)
          & r1_tarski(X5,X4)
          & r2_hidden(X4,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f13,plain,(
    ! [X1] :
      ( ? [X4,X5] :
          ( ~ r2_hidden(X5,X1)
          & r1_tarski(X5,X4)
          & r2_hidden(X4,X1) )
      | ~ sP0(X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f14,plain,(
    ? [X0] :
    ! [X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & ~ r2_tarski(X2,X1)
          & r1_tarski(X2,X1) )
      | ? [X3] :
          ( ~ r2_hidden(k1_zfmisc_1(X3),X1)
          & r2_hidden(X3,X1) )
      | sP0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_folding,[],[f12,f13])).

fof(f32,plain,(
    ! [X1] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_zfmisc_1(X3),X1)
          & r2_hidden(X3,X1) )
     => ( ~ r2_hidden(k1_zfmisc_1(sK9(X1)),X1)
        & r2_hidden(sK9(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & ~ r2_tarski(X2,X1)
          & r1_tarski(X2,X1) )
     => ( ~ r2_hidden(sK8(X1),X1)
        & ~ r2_tarski(sK8(X1),X1)
        & r1_tarski(sK8(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0] :
      ! [X1] :
        ( ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & ~ r2_tarski(X2,X1)
            & r1_tarski(X2,X1) )
        | ? [X3] :
            ( ~ r2_hidden(k1_zfmisc_1(X3),X1)
            & r2_hidden(X3,X1) )
        | sP0(X1)
        | ~ r2_hidden(X0,X1) )
   => ! [X1] :
        ( ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & ~ r2_tarski(X2,X1)
            & r1_tarski(X2,X1) )
        | ? [X3] :
            ( ~ r2_hidden(k1_zfmisc_1(X3),X1)
            & r2_hidden(X3,X1) )
        | sP0(X1)
        | ~ r2_hidden(sK7,X1) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X1] :
      ( ( ~ r2_hidden(sK8(X1),X1)
        & ~ r2_tarski(sK8(X1),X1)
        & r1_tarski(sK8(X1),X1) )
      | ( ~ r2_hidden(k1_zfmisc_1(sK9(X1)),X1)
        & r2_hidden(sK9(X1),X1) )
      | sP0(X1)
      | ~ r2_hidden(sK7,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f14,f32,f31,f30])).

fof(f52,plain,(
    ! [X1] :
      ( ~ r2_tarski(sK8(X1),X1)
      | ~ r2_hidden(k1_zfmisc_1(sK9(X1)),X1)
      | sP0(X1)
      | ~ r2_hidden(sK7,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    ! [X1] :
      ( r1_tarski(sK8(X1),X1)
      | ~ r2_hidden(k1_zfmisc_1(sK9(X1)),X1)
      | sP0(X1)
      | ~ r2_hidden(sK7,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK8(X1),X1)
      | ~ r2_hidden(k1_zfmisc_1(sK9(X1)),X1)
      | sP0(X1)
      | ~ r2_hidden(sK7,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f26,plain,(
    ! [X1] :
      ( ? [X4,X5] :
          ( ~ r2_hidden(X5,X1)
          & r1_tarski(X5,X4)
          & r2_hidden(X4,X1) )
      | ~ sP0(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(X2,X0)
          & r1_tarski(X2,X1)
          & r2_hidden(X1,X0) )
      | ~ sP0(X0) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(X2,X0)
          & r1_tarski(X2,X1)
          & r2_hidden(X1,X0) )
     => ( ~ r2_hidden(sK6(X0),X0)
        & r1_tarski(sK6(X0),sK5(X0))
        & r2_hidden(sK5(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ( ~ r2_hidden(sK6(X0),X0)
        & r1_tarski(sK6(X0),sK5(X0))
        & r2_hidden(sK5(X0),X0) )
      | ~ sP0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f27,f28])).

fof(f47,plain,(
    ! [X0] :
      ( r1_tarski(sK6(X0),sK5(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f46,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f48,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK6(X0),X0)
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f51,plain,(
    ! [X1] :
      ( ~ r2_tarski(sK8(X1),X1)
      | r2_hidden(sK9(X1),X1)
      | sP0(X1)
      | ~ r2_hidden(sK7,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    ! [X1] :
      ( r1_tarski(sK8(X1),X1)
      | r2_hidden(sK9(X1),X1)
      | sP0(X1)
      | ~ r2_hidden(sK7,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f53,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK8(X1),X1)
      | r2_hidden(sK9(X1),X1)
      | sP0(X1)
      | ~ r2_hidden(sK7,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f41,plain,(
    ! [X0] : r2_hidden(X0,sK3(X0)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_8,plain,
    ( r2_hidden(X0,sK4(X1,X2))
    | ~ r2_hidden(X2,sK3(X1))
    | ~ r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_4,plain,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_4373,plain,
    ( ~ r2_hidden(X0,sK3(X1))
    | r1_tarski(X2,sK4(X1,X0))
    | ~ r1_tarski(sK2(X2,sK4(X1,X0)),X0) ),
    inference(resolution,[status(thm)],[c_8,c_4])).

cnf(c_5,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_3509,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(X0),X1),X0)
    | r1_tarski(k1_zfmisc_1(X0),X1) ),
    inference(resolution,[status(thm)],[c_5,c_3])).

cnf(c_7282,plain,
    ( ~ r2_hidden(X0,sK3(X1))
    | r1_tarski(k1_zfmisc_1(X0),sK4(X1,X0)) ),
    inference(resolution,[status(thm)],[c_4373,c_3509])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,sK3(X1))
    | r2_hidden(X2,sK3(X1))
    | ~ r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,sK3(X1))
    | r2_hidden(sK4(X1,X0),sK3(X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_4182,plain,
    ( ~ r2_hidden(X0,sK3(X1))
    | r2_hidden(X2,sK3(X1))
    | ~ r1_tarski(X2,sK4(X1,X0)) ),
    inference(resolution,[status(thm)],[c_10,c_9])).

cnf(c_14158,plain,
    ( ~ r2_hidden(X0,sK3(X1))
    | r2_hidden(k1_zfmisc_1(X0),sK3(X1)) ),
    inference(resolution,[status(thm)],[c_7282,c_4182])).

cnf(c_7,plain,
    ( r2_tarski(X0,sK3(X1))
    | r2_hidden(X0,sK3(X1))
    | ~ r1_tarski(X0,sK3(X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_17,negated_conjecture,
    ( ~ r2_tarski(sK8(X0),X0)
    | ~ r2_hidden(k1_zfmisc_1(sK9(X0)),X0)
    | ~ r2_hidden(sK7,X0)
    | sP0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_304,plain,
    ( r2_hidden(X0,sK3(X1))
    | ~ r2_hidden(k1_zfmisc_1(sK9(X2)),X2)
    | ~ r2_hidden(sK7,X2)
    | ~ r1_tarski(X0,sK3(X1))
    | sP0(X2)
    | sK8(X2) != X0
    | sK3(X1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_17])).

cnf(c_305,plain,
    ( r2_hidden(sK8(sK3(X0)),sK3(X0))
    | ~ r2_hidden(k1_zfmisc_1(sK9(sK3(X0))),sK3(X0))
    | ~ r2_hidden(sK7,sK3(X0))
    | ~ r1_tarski(sK8(sK3(X0)),sK3(X0))
    | sP0(sK3(X0)) ),
    inference(unflattening,[status(thm)],[c_304])).

cnf(c_19,negated_conjecture,
    ( ~ r2_hidden(k1_zfmisc_1(sK9(X0)),X0)
    | ~ r2_hidden(sK7,X0)
    | r1_tarski(sK8(X0),X0)
    | sP0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_15,negated_conjecture,
    ( ~ r2_hidden(sK8(X0),X0)
    | ~ r2_hidden(k1_zfmisc_1(sK9(X0)),X0)
    | ~ r2_hidden(sK7,X0)
    | sP0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_319,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK9(sK3(X0))),sK3(X0))
    | ~ r2_hidden(sK7,sK3(X0))
    | sP0(sK3(X0)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_305,c_19,c_15])).

cnf(c_80104,plain,
    ( ~ r2_hidden(sK9(sK3(X0)),sK3(X0))
    | ~ r2_hidden(sK7,sK3(X0))
    | sP0(sK3(X0)) ),
    inference(resolution,[status(thm)],[c_14158,c_319])).

cnf(c_80106,plain,
    ( ~ r2_hidden(sK9(sK3(sK7)),sK3(sK7))
    | ~ r2_hidden(sK7,sK3(sK7))
    | sP0(sK3(sK7)) ),
    inference(instantiation,[status(thm)],[c_80104])).

cnf(c_13,plain,
    ( r1_tarski(sK6(X0),sK5(X0))
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2959,plain,
    ( r1_tarski(sK6(X0),sK5(X0)) = iProver_top
    | sP0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_14,plain,
    ( r2_hidden(sK5(X0),X0)
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2958,plain,
    ( r2_hidden(sK5(X0),X0) = iProver_top
    | sP0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2962,plain,
    ( r2_hidden(X0,sK3(X1)) != iProver_top
    | r2_hidden(X2,sK3(X1)) = iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3805,plain,
    ( r2_hidden(X0,sK3(X1)) = iProver_top
    | r1_tarski(X0,sK5(sK3(X1))) != iProver_top
    | sP0(sK3(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2958,c_2962])).

cnf(c_5653,plain,
    ( r2_hidden(sK6(sK3(X0)),sK3(X0)) = iProver_top
    | sP0(sK3(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2959,c_3805])).

cnf(c_12,plain,
    ( ~ r2_hidden(sK6(X0),X0)
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_3791,plain,
    ( ~ r2_hidden(sK6(sK3(X0)),sK3(X0))
    | ~ sP0(sK3(X0)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_3792,plain,
    ( r2_hidden(sK6(sK3(X0)),sK3(X0)) != iProver_top
    | sP0(sK3(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3791])).

cnf(c_5772,plain,
    ( sP0(sK3(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5653,c_3792])).

cnf(c_5774,plain,
    ( ~ sP0(sK3(X0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5772])).

cnf(c_5776,plain,
    ( ~ sP0(sK3(sK7)) ),
    inference(instantiation,[status(thm)],[c_5774])).

cnf(c_18,negated_conjecture,
    ( ~ r2_tarski(sK8(X0),X0)
    | r2_hidden(sK9(X0),X0)
    | ~ r2_hidden(sK7,X0)
    | sP0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_282,plain,
    ( r2_hidden(X0,sK3(X1))
    | r2_hidden(sK9(X2),X2)
    | ~ r2_hidden(sK7,X2)
    | ~ r1_tarski(X0,sK3(X1))
    | sP0(X2)
    | sK8(X2) != X0
    | sK3(X1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_18])).

cnf(c_283,plain,
    ( r2_hidden(sK9(sK3(X0)),sK3(X0))
    | r2_hidden(sK8(sK3(X0)),sK3(X0))
    | ~ r2_hidden(sK7,sK3(X0))
    | ~ r1_tarski(sK8(sK3(X0)),sK3(X0))
    | sP0(sK3(X0)) ),
    inference(unflattening,[status(thm)],[c_282])).

cnf(c_20,negated_conjecture,
    ( r2_hidden(sK9(X0),X0)
    | ~ r2_hidden(sK7,X0)
    | r1_tarski(sK8(X0),X0)
    | sP0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK9(X0),X0)
    | ~ r2_hidden(sK8(X0),X0)
    | ~ r2_hidden(sK7,X0)
    | sP0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_297,plain,
    ( r2_hidden(sK9(sK3(X0)),sK3(X0))
    | ~ r2_hidden(sK7,sK3(X0))
    | sP0(sK3(X0)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_283,c_20,c_16])).

cnf(c_302,plain,
    ( r2_hidden(sK9(sK3(sK7)),sK3(sK7))
    | ~ r2_hidden(sK7,sK3(sK7))
    | sP0(sK3(sK7)) ),
    inference(instantiation,[status(thm)],[c_297])).

cnf(c_11,plain,
    ( r2_hidden(X0,sK3(X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_49,plain,
    ( r2_hidden(sK7,sK3(sK7)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_80106,c_5776,c_302,c_49])).


%------------------------------------------------------------------------------
