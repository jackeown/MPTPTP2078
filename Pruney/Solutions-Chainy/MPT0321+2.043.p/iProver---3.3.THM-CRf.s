%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:45 EST 2020

% Result     : Theorem 3.67s
% Output     : CNFRefutation 3.67s
% Verified   : 
% Statistics : Number of formulae       :  164 (1928 expanded)
%              Number of clauses        :  106 ( 707 expanded)
%              Number of leaves         :   17 ( 393 expanded)
%              Depth                    :   23
%              Number of atoms          :  502 (6980 expanded)
%              Number of equality atoms :  316 (3541 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f20])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f18])).

fof(f35,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | X0 != X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) )
   => ( ( sK8 != sK10
        | sK7 != sK9 )
      & k1_xboole_0 != sK8
      & k1_xboole_0 != sK7
      & k2_zfmisc_1(sK7,sK8) = k2_zfmisc_1(sK9,sK10) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ( sK8 != sK10
      | sK7 != sK9 )
    & k1_xboole_0 != sK8
    & k1_xboole_0 != sK7
    & k2_zfmisc_1(sK7,sK8) = k2_zfmisc_1(sK9,sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f19,f35])).

fof(f61,plain,(
    k2_zfmisc_1(sK7,sK8) = k2_zfmisc_1(sK9,sK10) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f31])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f64,plain,
    ( sK8 != sK10
    | sK7 != sK9 ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(sK1(X0,X1),X0)
        & r2_hidden(sK1(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r2_hidden(sK1(X0,X1),X0)
        & r2_hidden(sK1(X0,X1),X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f23])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f63,plain,(
    k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f33])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f71,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k4_tarski(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k4_tarski(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f25])).

fof(f29,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
        & r2_hidden(sK6(X0,X1,X8),X1)
        & r2_hidden(sK5(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = X3
        & r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(sK3(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k4_tarski(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k4_tarski(X4,X5) != sK2(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK2(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK2(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = sK2(X0,X1,X2)
              & r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
                & r2_hidden(sK6(X0,X1,X8),X1)
                & r2_hidden(sK5(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f26,f29,f28,f27])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK1(X0,X1),X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f62,plain,(
    k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f36])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f70,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f60])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_512,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_27,negated_conjecture,
    ( k2_zfmisc_1(sK7,sK8) = k2_zfmisc_1(sK9,sK10) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_496,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_986,plain,
    ( r2_hidden(X0,sK9) != iProver_top
    | r2_hidden(X1,sK10) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK7,sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_496])).

cnf(c_19,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_495,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4470,plain,
    ( r2_hidden(X0,sK9) != iProver_top
    | r2_hidden(X1,sK10) != iProver_top
    | r2_hidden(X1,sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_986,c_495])).

cnf(c_8861,plain,
    ( r2_hidden(X0,sK10) != iProver_top
    | r2_hidden(X0,sK8) = iProver_top
    | r1_tarski(sK9,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_512,c_4470])).

cnf(c_9060,plain,
    ( r2_hidden(sK0(sK10,X0),sK8) = iProver_top
    | r1_tarski(sK9,X1) = iProver_top
    | r1_tarski(sK10,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_512,c_8861])).

cnf(c_2,plain,
    ( r2_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_511,plain,
    ( X0 = X1
    | r2_xboole_0(X1,X0) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_10331,plain,
    ( sK9 = X0
    | r2_xboole_0(sK9,X0) = iProver_top
    | r2_hidden(sK0(sK10,X1),sK8) = iProver_top
    | r1_tarski(sK10,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_9060,c_511])).

cnf(c_684,plain,
    ( r2_xboole_0(sK10,sK8)
    | ~ r1_tarski(sK10,sK8)
    | sK8 = sK10 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_685,plain,
    ( sK8 = sK10
    | r2_xboole_0(sK10,sK8) = iProver_top
    | r1_tarski(sK10,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_684])).

cnf(c_24,negated_conjecture,
    ( sK7 != sK9
    | sK8 != sK10 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_7931,plain,
    ( r2_xboole_0(sK9,sK7)
    | ~ r1_tarski(sK9,sK7)
    | sK8 != sK10 ),
    inference(resolution,[status(thm)],[c_2,c_24])).

cnf(c_7932,plain,
    ( sK8 != sK10
    | r2_xboole_0(sK9,sK7) = iProver_top
    | r1_tarski(sK9,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7931])).

cnf(c_8,plain,
    ( ~ r2_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_505,plain,
    ( r2_xboole_0(X0,X1) != iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_20,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_494,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_780,plain,
    ( r2_hidden(X0,sK9) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK7,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_494])).

cnf(c_1591,plain,
    ( r2_hidden(X0,sK9) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_496,c_780])).

cnf(c_5513,plain,
    ( r2_hidden(X0,sK9) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r1_tarski(sK8,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_512,c_1591])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_23,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_28,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_22,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_29,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_193,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_707,plain,
    ( sK8 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_193])).

cnf(c_708,plain,
    ( sK8 != k1_xboole_0
    | k1_xboole_0 = sK8
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_707])).

cnf(c_13,plain,
    ( r2_hidden(sK3(X0,X1,X2),X0)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k2_zfmisc_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_501,plain,
    ( k2_zfmisc_1(X0,X1) = X2
    | r2_hidden(sK3(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_9,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_510,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2516,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_510])).

cnf(c_2545,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = X1
    | r2_hidden(sK3(k1_xboole_0,X0,X1),X2) = iProver_top
    | r2_hidden(sK2(k1_xboole_0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_501,c_2516])).

cnf(c_2561,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK3(k1_xboole_0,X1,X0),X2) = iProver_top
    | r2_hidden(sK2(k1_xboole_0,X1,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2545,c_22])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k5_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_508,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4015,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_508])).

cnf(c_4406,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4015,c_2516])).

cnf(c_4420,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(k1_xboole_0,X1,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2561,c_4406])).

cnf(c_6888,plain,
    ( sK8 = k1_xboole_0
    | r2_hidden(X0,sK9) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_4420,c_1591])).

cnf(c_7770,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X0,sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5513,c_25,c_28,c_29,c_708,c_6888])).

cnf(c_7771,plain,
    ( r2_hidden(X0,sK9) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_7770])).

cnf(c_7779,plain,
    ( r2_xboole_0(X0,sK7) != iProver_top
    | r2_hidden(sK1(X0,sK7),sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_505,c_7771])).

cnf(c_7,plain,
    ( ~ r2_xboole_0(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_506,plain,
    ( r2_xboole_0(X0,X1) != iProver_top
    | r2_hidden(sK1(X0,X1),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_8420,plain,
    ( r2_xboole_0(sK9,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_7779,c_506])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_513,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_10332,plain,
    ( r1_tarski(sK9,X0) = iProver_top
    | r1_tarski(sK10,sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_9060,c_513])).

cnf(c_10361,plain,
    ( sK9 = X0
    | r2_xboole_0(sK9,X0) = iProver_top
    | r1_tarski(sK10,sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_10332,c_511])).

cnf(c_4471,plain,
    ( r2_hidden(X0,sK9) != iProver_top
    | r2_hidden(X0,sK7) = iProver_top
    | r2_hidden(X1,sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_986,c_494])).

cnf(c_9619,plain,
    ( r2_hidden(X0,sK10) != iProver_top
    | r2_hidden(sK0(sK9,X1),sK7) = iProver_top
    | r1_tarski(sK9,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_512,c_4471])).

cnf(c_11819,plain,
    ( r2_hidden(sK0(sK9,X0),sK7) = iProver_top
    | r1_tarski(sK9,X0) = iProver_top
    | r1_tarski(sK10,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_512,c_9619])).

cnf(c_705,plain,
    ( sK10 != X0
    | sK8 != X0
    | sK8 = sK10 ),
    inference(instantiation,[status(thm)],[c_193])).

cnf(c_818,plain,
    ( sK10 != sK8
    | sK8 = sK10
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_705])).

cnf(c_192,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_819,plain,
    ( sK8 = sK8 ),
    inference(instantiation,[status(thm)],[c_192])).

cnf(c_1321,plain,
    ( sK8 != sK10
    | k1_xboole_0 != sK10
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_707])).

cnf(c_2456,plain,
    ( sK10 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK10 ),
    inference(instantiation,[status(thm)],[c_193])).

cnf(c_2457,plain,
    ( sK10 != k1_xboole_0
    | k1_xboole_0 = sK10
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2456])).

cnf(c_779,plain,
    ( r2_hidden(X0,sK10) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK7,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_495])).

cnf(c_1584,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK10) = iProver_top
    | r2_hidden(X1,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_496,c_779])).

cnf(c_4612,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(sK0(sK8,X1),sK10) = iProver_top
    | r1_tarski(sK8,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_512,c_1584])).

cnf(c_11006,plain,
    ( r2_hidden(sK0(sK8,X0),sK10) = iProver_top
    | r1_tarski(sK7,X1) = iProver_top
    | r1_tarski(sK8,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_512,c_4612])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_709,plain,
    ( sK7 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_193])).

cnf(c_710,plain,
    ( sK7 != k1_xboole_0
    | k1_xboole_0 = sK7
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_709])).

cnf(c_12,plain,
    ( r2_hidden(sK4(X0,X1,X2),X1)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k2_zfmisc_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_502,plain,
    ( k2_zfmisc_1(X0,X1) = X2
    | r2_hidden(sK4(X0,X1,X2),X1) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2834,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = X1
    | r2_hidden(sK4(X0,k1_xboole_0,X1),X2) = iProver_top
    | r2_hidden(sK2(X0,k1_xboole_0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_502,c_2516])).

cnf(c_21,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2838,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK4(X1,k1_xboole_0,X0),X2) = iProver_top
    | r2_hidden(sK2(X1,k1_xboole_0,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2834,c_21])).

cnf(c_4422,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X1,k1_xboole_0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2838,c_4406])).

cnf(c_11025,plain,
    ( sK7 = k1_xboole_0
    | r2_hidden(sK0(sK8,X0),sK10) = iProver_top
    | r1_tarski(sK8,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4422,c_4612])).

cnf(c_11154,plain,
    ( r2_hidden(sK0(sK8,X0),sK10) = iProver_top
    | r1_tarski(sK8,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11006,c_26,c_28,c_29,c_710,c_11025])).

cnf(c_11162,plain,
    ( r1_tarski(sK8,sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_11154,c_513])).

cnf(c_11404,plain,
    ( sK10 = sK8
    | r2_xboole_0(sK8,sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_11162,c_511])).

cnf(c_9061,plain,
    ( r2_xboole_0(X0,sK10) != iProver_top
    | r2_hidden(sK1(X0,sK10),sK8) = iProver_top
    | r1_tarski(sK9,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_505,c_8861])).

cnf(c_11531,plain,
    ( r2_xboole_0(sK8,sK10) != iProver_top
    | r1_tarski(sK9,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9061,c_506])).

cnf(c_11566,plain,
    ( sK10 = sK8
    | r1_tarski(sK9,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_11404,c_11531])).

cnf(c_11838,plain,
    ( sK10 = k1_xboole_0
    | r2_hidden(sK0(sK9,X0),sK7) = iProver_top
    | r1_tarski(sK9,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4422,c_9619])).

cnf(c_12467,plain,
    ( r1_tarski(sK9,X0) = iProver_top
    | r2_hidden(sK0(sK9,X0),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11819,c_25,c_28,c_29,c_818,c_819,c_1321,c_2457,c_11566,c_11838])).

cnf(c_12468,plain,
    ( r2_hidden(sK0(sK9,X0),sK7) = iProver_top
    | r1_tarski(sK9,X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_12467])).

cnf(c_12475,plain,
    ( r1_tarski(sK9,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_12468,c_513])).

cnf(c_4613,plain,
    ( r2_xboole_0(X0,sK8) != iProver_top
    | r2_hidden(X1,sK7) != iProver_top
    | r2_hidden(sK1(X0,sK8),sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_505,c_1584])).

cnf(c_14960,plain,
    ( r2_xboole_0(X0,sK8) != iProver_top
    | r2_hidden(sK1(X0,sK8),sK10) = iProver_top
    | r1_tarski(sK7,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_512,c_4613])).

cnf(c_14986,plain,
    ( sK7 = k1_xboole_0
    | r2_xboole_0(X0,sK8) != iProver_top
    | r2_hidden(sK1(X0,sK8),sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_4422,c_4613])).

cnf(c_15404,plain,
    ( r2_hidden(sK1(X0,sK8),sK10) = iProver_top
    | r2_xboole_0(X0,sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14960,c_26,c_28,c_29,c_710,c_14986])).

cnf(c_15405,plain,
    ( r2_xboole_0(X0,sK8) != iProver_top
    | r2_hidden(sK1(X0,sK8),sK10) = iProver_top ),
    inference(renaming,[status(thm)],[c_15404])).

cnf(c_15414,plain,
    ( r2_xboole_0(sK10,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_15405,c_506])).

cnf(c_17387,plain,
    ( sK9 = X0
    | r2_xboole_0(sK9,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10331,c_685,c_7932,c_8420,c_10361,c_12475,c_15414])).

cnf(c_12490,plain,
    ( sK9 = sK7
    | r2_xboole_0(sK9,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_12475,c_511])).

cnf(c_12753,plain,
    ( sK9 = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12490,c_8420])).

cnf(c_17393,plain,
    ( sK9 = X0
    | r2_xboole_0(sK7,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17387,c_12753])).

cnf(c_17394,plain,
    ( sK7 = X0
    | r2_xboole_0(sK7,X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_17393,c_12753])).

cnf(c_4412,plain,
    ( r2_xboole_0(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_505,c_4406])).

cnf(c_17404,plain,
    ( sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_17394,c_4412])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17404,c_710,c_29,c_28,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:12:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.67/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.67/1.00  
% 3.67/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.67/1.00  
% 3.67/1.00  ------  iProver source info
% 3.67/1.00  
% 3.67/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.67/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.67/1.00  git: non_committed_changes: false
% 3.67/1.00  git: last_make_outside_of_git: false
% 3.67/1.00  
% 3.67/1.00  ------ 
% 3.67/1.00  
% 3.67/1.00  ------ Input Options
% 3.67/1.00  
% 3.67/1.00  --out_options                           all
% 3.67/1.00  --tptp_safe_out                         true
% 3.67/1.00  --problem_path                          ""
% 3.67/1.00  --include_path                          ""
% 3.67/1.00  --clausifier                            res/vclausify_rel
% 3.67/1.00  --clausifier_options                    --mode clausify
% 3.67/1.00  --stdin                                 false
% 3.67/1.00  --stats_out                             sel
% 3.67/1.00  
% 3.67/1.00  ------ General Options
% 3.67/1.00  
% 3.67/1.00  --fof                                   false
% 3.67/1.00  --time_out_real                         604.99
% 3.67/1.00  --time_out_virtual                      -1.
% 3.67/1.00  --symbol_type_check                     false
% 3.67/1.00  --clausify_out                          false
% 3.67/1.00  --sig_cnt_out                           false
% 3.67/1.00  --trig_cnt_out                          false
% 3.67/1.00  --trig_cnt_out_tolerance                1.
% 3.67/1.00  --trig_cnt_out_sk_spl                   false
% 3.67/1.00  --abstr_cl_out                          false
% 3.67/1.00  
% 3.67/1.00  ------ Global Options
% 3.67/1.00  
% 3.67/1.00  --schedule                              none
% 3.67/1.00  --add_important_lit                     false
% 3.67/1.00  --prop_solver_per_cl                    1000
% 3.67/1.00  --min_unsat_core                        false
% 3.67/1.00  --soft_assumptions                      false
% 3.67/1.00  --soft_lemma_size                       3
% 3.67/1.00  --prop_impl_unit_size                   0
% 3.67/1.00  --prop_impl_unit                        []
% 3.67/1.00  --share_sel_clauses                     true
% 3.67/1.00  --reset_solvers                         false
% 3.67/1.00  --bc_imp_inh                            [conj_cone]
% 3.67/1.00  --conj_cone_tolerance                   3.
% 3.67/1.00  --extra_neg_conj                        none
% 3.67/1.00  --large_theory_mode                     true
% 3.67/1.00  --prolific_symb_bound                   200
% 3.67/1.00  --lt_threshold                          2000
% 3.67/1.00  --clause_weak_htbl                      true
% 3.67/1.00  --gc_record_bc_elim                     false
% 3.67/1.00  
% 3.67/1.00  ------ Preprocessing Options
% 3.67/1.00  
% 3.67/1.00  --preprocessing_flag                    true
% 3.67/1.00  --time_out_prep_mult                    0.1
% 3.67/1.00  --splitting_mode                        input
% 3.67/1.00  --splitting_grd                         true
% 3.67/1.00  --splitting_cvd                         false
% 3.67/1.00  --splitting_cvd_svl                     false
% 3.67/1.00  --splitting_nvd                         32
% 3.67/1.00  --sub_typing                            true
% 3.67/1.00  --prep_gs_sim                           false
% 3.67/1.00  --prep_unflatten                        true
% 3.67/1.00  --prep_res_sim                          true
% 3.67/1.00  --prep_upred                            true
% 3.67/1.00  --prep_sem_filter                       exhaustive
% 3.67/1.00  --prep_sem_filter_out                   false
% 3.67/1.00  --pred_elim                             false
% 3.67/1.00  --res_sim_input                         true
% 3.67/1.00  --eq_ax_congr_red                       true
% 3.67/1.00  --pure_diseq_elim                       true
% 3.67/1.00  --brand_transform                       false
% 3.67/1.00  --non_eq_to_eq                          false
% 3.67/1.00  --prep_def_merge                        true
% 3.67/1.00  --prep_def_merge_prop_impl              false
% 3.67/1.00  --prep_def_merge_mbd                    true
% 3.67/1.00  --prep_def_merge_tr_red                 false
% 3.67/1.00  --prep_def_merge_tr_cl                  false
% 3.67/1.00  --smt_preprocessing                     true
% 3.67/1.00  --smt_ac_axioms                         fast
% 3.67/1.00  --preprocessed_out                      false
% 3.67/1.00  --preprocessed_stats                    false
% 3.67/1.00  
% 3.67/1.00  ------ Abstraction refinement Options
% 3.67/1.00  
% 3.67/1.00  --abstr_ref                             []
% 3.67/1.00  --abstr_ref_prep                        false
% 3.67/1.00  --abstr_ref_until_sat                   false
% 3.67/1.00  --abstr_ref_sig_restrict                funpre
% 3.67/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.67/1.00  --abstr_ref_under                       []
% 3.67/1.00  
% 3.67/1.00  ------ SAT Options
% 3.67/1.00  
% 3.67/1.00  --sat_mode                              false
% 3.67/1.00  --sat_fm_restart_options                ""
% 3.67/1.00  --sat_gr_def                            false
% 3.67/1.00  --sat_epr_types                         true
% 3.67/1.00  --sat_non_cyclic_types                  false
% 3.67/1.00  --sat_finite_models                     false
% 3.67/1.00  --sat_fm_lemmas                         false
% 3.67/1.00  --sat_fm_prep                           false
% 3.67/1.00  --sat_fm_uc_incr                        true
% 3.67/1.00  --sat_out_model                         small
% 3.67/1.00  --sat_out_clauses                       false
% 3.67/1.00  
% 3.67/1.00  ------ QBF Options
% 3.67/1.00  
% 3.67/1.00  --qbf_mode                              false
% 3.67/1.00  --qbf_elim_univ                         false
% 3.67/1.00  --qbf_dom_inst                          none
% 3.67/1.00  --qbf_dom_pre_inst                      false
% 3.67/1.00  --qbf_sk_in                             false
% 3.67/1.00  --qbf_pred_elim                         true
% 3.67/1.00  --qbf_split                             512
% 3.67/1.00  
% 3.67/1.00  ------ BMC1 Options
% 3.67/1.00  
% 3.67/1.00  --bmc1_incremental                      false
% 3.67/1.00  --bmc1_axioms                           reachable_all
% 3.67/1.00  --bmc1_min_bound                        0
% 3.67/1.00  --bmc1_max_bound                        -1
% 3.67/1.00  --bmc1_max_bound_default                -1
% 3.67/1.00  --bmc1_symbol_reachability              true
% 3.67/1.00  --bmc1_property_lemmas                  false
% 3.67/1.00  --bmc1_k_induction                      false
% 3.67/1.00  --bmc1_non_equiv_states                 false
% 3.67/1.00  --bmc1_deadlock                         false
% 3.67/1.00  --bmc1_ucm                              false
% 3.67/1.00  --bmc1_add_unsat_core                   none
% 3.67/1.00  --bmc1_unsat_core_children              false
% 3.67/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.67/1.00  --bmc1_out_stat                         full
% 3.67/1.00  --bmc1_ground_init                      false
% 3.67/1.00  --bmc1_pre_inst_next_state              false
% 3.67/1.00  --bmc1_pre_inst_state                   false
% 3.67/1.00  --bmc1_pre_inst_reach_state             false
% 3.67/1.00  --bmc1_out_unsat_core                   false
% 3.67/1.00  --bmc1_aig_witness_out                  false
% 3.67/1.00  --bmc1_verbose                          false
% 3.67/1.00  --bmc1_dump_clauses_tptp                false
% 3.67/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.67/1.00  --bmc1_dump_file                        -
% 3.67/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.67/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.67/1.00  --bmc1_ucm_extend_mode                  1
% 3.67/1.00  --bmc1_ucm_init_mode                    2
% 3.67/1.00  --bmc1_ucm_cone_mode                    none
% 3.67/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.67/1.00  --bmc1_ucm_relax_model                  4
% 3.67/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.67/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.67/1.00  --bmc1_ucm_layered_model                none
% 3.67/1.00  --bmc1_ucm_max_lemma_size               10
% 3.67/1.00  
% 3.67/1.00  ------ AIG Options
% 3.67/1.00  
% 3.67/1.00  --aig_mode                              false
% 3.67/1.00  
% 3.67/1.00  ------ Instantiation Options
% 3.67/1.00  
% 3.67/1.00  --instantiation_flag                    true
% 3.67/1.00  --inst_sos_flag                         false
% 3.67/1.00  --inst_sos_phase                        true
% 3.67/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.67/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.67/1.00  --inst_lit_sel_side                     num_symb
% 3.67/1.00  --inst_solver_per_active                1400
% 3.67/1.00  --inst_solver_calls_frac                1.
% 3.67/1.00  --inst_passive_queue_type               priority_queues
% 3.67/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.67/1.00  --inst_passive_queues_freq              [25;2]
% 3.67/1.00  --inst_dismatching                      true
% 3.67/1.00  --inst_eager_unprocessed_to_passive     true
% 3.67/1.00  --inst_prop_sim_given                   true
% 3.67/1.00  --inst_prop_sim_new                     false
% 3.67/1.00  --inst_subs_new                         false
% 3.67/1.00  --inst_eq_res_simp                      false
% 3.67/1.00  --inst_subs_given                       false
% 3.67/1.00  --inst_orphan_elimination               true
% 3.67/1.00  --inst_learning_loop_flag               true
% 3.67/1.00  --inst_learning_start                   3000
% 3.67/1.00  --inst_learning_factor                  2
% 3.67/1.00  --inst_start_prop_sim_after_learn       3
% 3.67/1.00  --inst_sel_renew                        solver
% 3.67/1.00  --inst_lit_activity_flag                true
% 3.67/1.00  --inst_restr_to_given                   false
% 3.67/1.00  --inst_activity_threshold               500
% 3.67/1.00  --inst_out_proof                        true
% 3.67/1.00  
% 3.67/1.00  ------ Resolution Options
% 3.67/1.00  
% 3.67/1.00  --resolution_flag                       true
% 3.67/1.00  --res_lit_sel                           adaptive
% 3.67/1.00  --res_lit_sel_side                      none
% 3.67/1.00  --res_ordering                          kbo
% 3.67/1.00  --res_to_prop_solver                    active
% 3.67/1.00  --res_prop_simpl_new                    false
% 3.67/1.00  --res_prop_simpl_given                  true
% 3.67/1.00  --res_passive_queue_type                priority_queues
% 3.67/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.67/1.00  --res_passive_queues_freq               [15;5]
% 3.67/1.00  --res_forward_subs                      full
% 3.67/1.00  --res_backward_subs                     full
% 3.67/1.00  --res_forward_subs_resolution           true
% 3.67/1.00  --res_backward_subs_resolution          true
% 3.67/1.00  --res_orphan_elimination                true
% 3.67/1.00  --res_time_limit                        2.
% 3.67/1.00  --res_out_proof                         true
% 3.67/1.00  
% 3.67/1.00  ------ Superposition Options
% 3.67/1.00  
% 3.67/1.00  --superposition_flag                    true
% 3.67/1.00  --sup_passive_queue_type                priority_queues
% 3.67/1.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.67/1.00  --sup_passive_queues_freq               [1;4]
% 3.67/1.00  --demod_completeness_check              fast
% 3.67/1.00  --demod_use_ground                      true
% 3.67/1.00  --sup_to_prop_solver                    passive
% 3.67/1.00  --sup_prop_simpl_new                    true
% 3.67/1.00  --sup_prop_simpl_given                  true
% 3.67/1.00  --sup_fun_splitting                     false
% 3.67/1.00  --sup_smt_interval                      50000
% 3.67/1.00  
% 3.67/1.00  ------ Superposition Simplification Setup
% 3.67/1.00  
% 3.67/1.00  --sup_indices_passive                   []
% 3.67/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.67/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.67/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.67/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.67/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.67/1.00  --sup_full_bw                           [BwDemod]
% 3.67/1.00  --sup_immed_triv                        [TrivRules]
% 3.67/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.67/1.00  --sup_immed_bw_main                     []
% 3.67/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.67/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.67/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.67/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.67/1.00  
% 3.67/1.00  ------ Combination Options
% 3.67/1.00  
% 3.67/1.00  --comb_res_mult                         3
% 3.67/1.00  --comb_sup_mult                         2
% 3.67/1.00  --comb_inst_mult                        10
% 3.67/1.00  
% 3.67/1.00  ------ Debug Options
% 3.67/1.00  
% 3.67/1.00  --dbg_backtrace                         false
% 3.67/1.00  --dbg_dump_prop_clauses                 false
% 3.67/1.00  --dbg_dump_prop_clauses_file            -
% 3.67/1.00  --dbg_out_stat                          false
% 3.67/1.00  ------ Parsing...
% 3.67/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.67/1.00  
% 3.67/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.67/1.00  
% 3.67/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.67/1.00  
% 3.67/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.67/1.00  ------ Proving...
% 3.67/1.00  ------ Problem Properties 
% 3.67/1.00  
% 3.67/1.00  
% 3.67/1.00  clauses                                 28
% 3.67/1.00  conjectures                             4
% 3.67/1.00  EPR                                     4
% 3.67/1.00  Horn                                    19
% 3.67/1.00  unary                                   6
% 3.67/1.00  binary                                  10
% 3.67/1.00  lits                                    64
% 3.67/1.00  lits eq                                 19
% 3.67/1.00  fd_pure                                 0
% 3.67/1.00  fd_pseudo                               0
% 3.67/1.00  fd_cond                                 1
% 3.67/1.00  fd_pseudo_cond                          5
% 3.67/1.00  AC symbols                              0
% 3.67/1.00  
% 3.67/1.00  ------ Input Options Time Limit: Unbounded
% 3.67/1.00  
% 3.67/1.00  
% 3.67/1.00  ------ 
% 3.67/1.00  Current options:
% 3.67/1.00  ------ 
% 3.67/1.00  
% 3.67/1.00  ------ Input Options
% 3.67/1.00  
% 3.67/1.00  --out_options                           all
% 3.67/1.00  --tptp_safe_out                         true
% 3.67/1.00  --problem_path                          ""
% 3.67/1.00  --include_path                          ""
% 3.67/1.00  --clausifier                            res/vclausify_rel
% 3.67/1.00  --clausifier_options                    --mode clausify
% 3.67/1.00  --stdin                                 false
% 3.67/1.00  --stats_out                             sel
% 3.67/1.00  
% 3.67/1.00  ------ General Options
% 3.67/1.00  
% 3.67/1.00  --fof                                   false
% 3.67/1.00  --time_out_real                         604.99
% 3.67/1.00  --time_out_virtual                      -1.
% 3.67/1.00  --symbol_type_check                     false
% 3.67/1.00  --clausify_out                          false
% 3.67/1.00  --sig_cnt_out                           false
% 3.67/1.00  --trig_cnt_out                          false
% 3.67/1.00  --trig_cnt_out_tolerance                1.
% 3.67/1.00  --trig_cnt_out_sk_spl                   false
% 3.67/1.00  --abstr_cl_out                          false
% 3.67/1.00  
% 3.67/1.00  ------ Global Options
% 3.67/1.00  
% 3.67/1.00  --schedule                              none
% 3.67/1.00  --add_important_lit                     false
% 3.67/1.00  --prop_solver_per_cl                    1000
% 3.67/1.00  --min_unsat_core                        false
% 3.67/1.00  --soft_assumptions                      false
% 3.67/1.00  --soft_lemma_size                       3
% 3.67/1.00  --prop_impl_unit_size                   0
% 3.67/1.00  --prop_impl_unit                        []
% 3.67/1.00  --share_sel_clauses                     true
% 3.67/1.00  --reset_solvers                         false
% 3.67/1.00  --bc_imp_inh                            [conj_cone]
% 3.67/1.00  --conj_cone_tolerance                   3.
% 3.67/1.00  --extra_neg_conj                        none
% 3.67/1.00  --large_theory_mode                     true
% 3.67/1.00  --prolific_symb_bound                   200
% 3.67/1.00  --lt_threshold                          2000
% 3.67/1.00  --clause_weak_htbl                      true
% 3.67/1.00  --gc_record_bc_elim                     false
% 3.67/1.00  
% 3.67/1.00  ------ Preprocessing Options
% 3.67/1.00  
% 3.67/1.00  --preprocessing_flag                    true
% 3.67/1.00  --time_out_prep_mult                    0.1
% 3.67/1.00  --splitting_mode                        input
% 3.67/1.00  --splitting_grd                         true
% 3.67/1.00  --splitting_cvd                         false
% 3.67/1.00  --splitting_cvd_svl                     false
% 3.67/1.00  --splitting_nvd                         32
% 3.67/1.00  --sub_typing                            true
% 3.67/1.00  --prep_gs_sim                           false
% 3.67/1.00  --prep_unflatten                        true
% 3.67/1.00  --prep_res_sim                          true
% 3.67/1.00  --prep_upred                            true
% 3.67/1.00  --prep_sem_filter                       exhaustive
% 3.67/1.00  --prep_sem_filter_out                   false
% 3.67/1.00  --pred_elim                             false
% 3.67/1.00  --res_sim_input                         true
% 3.67/1.00  --eq_ax_congr_red                       true
% 3.67/1.00  --pure_diseq_elim                       true
% 3.67/1.00  --brand_transform                       false
% 3.67/1.00  --non_eq_to_eq                          false
% 3.67/1.00  --prep_def_merge                        true
% 3.67/1.00  --prep_def_merge_prop_impl              false
% 3.67/1.00  --prep_def_merge_mbd                    true
% 3.67/1.00  --prep_def_merge_tr_red                 false
% 3.67/1.00  --prep_def_merge_tr_cl                  false
% 3.67/1.00  --smt_preprocessing                     true
% 3.67/1.00  --smt_ac_axioms                         fast
% 3.67/1.00  --preprocessed_out                      false
% 3.67/1.00  --preprocessed_stats                    false
% 3.67/1.00  
% 3.67/1.00  ------ Abstraction refinement Options
% 3.67/1.00  
% 3.67/1.00  --abstr_ref                             []
% 3.67/1.00  --abstr_ref_prep                        false
% 3.67/1.00  --abstr_ref_until_sat                   false
% 3.67/1.00  --abstr_ref_sig_restrict                funpre
% 3.67/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.67/1.00  --abstr_ref_under                       []
% 3.67/1.00  
% 3.67/1.00  ------ SAT Options
% 3.67/1.00  
% 3.67/1.00  --sat_mode                              false
% 3.67/1.00  --sat_fm_restart_options                ""
% 3.67/1.00  --sat_gr_def                            false
% 3.67/1.00  --sat_epr_types                         true
% 3.67/1.00  --sat_non_cyclic_types                  false
% 3.67/1.00  --sat_finite_models                     false
% 3.67/1.00  --sat_fm_lemmas                         false
% 3.67/1.00  --sat_fm_prep                           false
% 3.67/1.00  --sat_fm_uc_incr                        true
% 3.67/1.00  --sat_out_model                         small
% 3.67/1.00  --sat_out_clauses                       false
% 3.67/1.00  
% 3.67/1.00  ------ QBF Options
% 3.67/1.00  
% 3.67/1.00  --qbf_mode                              false
% 3.67/1.00  --qbf_elim_univ                         false
% 3.67/1.00  --qbf_dom_inst                          none
% 3.67/1.00  --qbf_dom_pre_inst                      false
% 3.67/1.00  --qbf_sk_in                             false
% 3.67/1.00  --qbf_pred_elim                         true
% 3.67/1.00  --qbf_split                             512
% 3.67/1.00  
% 3.67/1.00  ------ BMC1 Options
% 3.67/1.00  
% 3.67/1.00  --bmc1_incremental                      false
% 3.67/1.00  --bmc1_axioms                           reachable_all
% 3.67/1.00  --bmc1_min_bound                        0
% 3.67/1.00  --bmc1_max_bound                        -1
% 3.67/1.00  --bmc1_max_bound_default                -1
% 3.67/1.00  --bmc1_symbol_reachability              true
% 3.67/1.00  --bmc1_property_lemmas                  false
% 3.67/1.00  --bmc1_k_induction                      false
% 3.67/1.00  --bmc1_non_equiv_states                 false
% 3.67/1.00  --bmc1_deadlock                         false
% 3.67/1.00  --bmc1_ucm                              false
% 3.67/1.00  --bmc1_add_unsat_core                   none
% 3.67/1.00  --bmc1_unsat_core_children              false
% 3.67/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.67/1.00  --bmc1_out_stat                         full
% 3.67/1.00  --bmc1_ground_init                      false
% 3.67/1.00  --bmc1_pre_inst_next_state              false
% 3.67/1.00  --bmc1_pre_inst_state                   false
% 3.67/1.00  --bmc1_pre_inst_reach_state             false
% 3.67/1.00  --bmc1_out_unsat_core                   false
% 3.67/1.00  --bmc1_aig_witness_out                  false
% 3.67/1.00  --bmc1_verbose                          false
% 3.67/1.00  --bmc1_dump_clauses_tptp                false
% 3.67/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.67/1.00  --bmc1_dump_file                        -
% 3.67/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.67/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.67/1.00  --bmc1_ucm_extend_mode                  1
% 3.67/1.00  --bmc1_ucm_init_mode                    2
% 3.67/1.00  --bmc1_ucm_cone_mode                    none
% 3.67/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.67/1.00  --bmc1_ucm_relax_model                  4
% 3.67/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.67/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.67/1.00  --bmc1_ucm_layered_model                none
% 3.67/1.00  --bmc1_ucm_max_lemma_size               10
% 3.67/1.00  
% 3.67/1.00  ------ AIG Options
% 3.67/1.00  
% 3.67/1.00  --aig_mode                              false
% 3.67/1.00  
% 3.67/1.00  ------ Instantiation Options
% 3.67/1.00  
% 3.67/1.00  --instantiation_flag                    true
% 3.67/1.00  --inst_sos_flag                         false
% 3.67/1.00  --inst_sos_phase                        true
% 3.67/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.67/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.67/1.00  --inst_lit_sel_side                     num_symb
% 3.67/1.00  --inst_solver_per_active                1400
% 3.67/1.00  --inst_solver_calls_frac                1.
% 3.67/1.00  --inst_passive_queue_type               priority_queues
% 3.67/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.67/1.00  --inst_passive_queues_freq              [25;2]
% 3.67/1.00  --inst_dismatching                      true
% 3.67/1.00  --inst_eager_unprocessed_to_passive     true
% 3.67/1.00  --inst_prop_sim_given                   true
% 3.67/1.00  --inst_prop_sim_new                     false
% 3.67/1.00  --inst_subs_new                         false
% 3.67/1.00  --inst_eq_res_simp                      false
% 3.67/1.00  --inst_subs_given                       false
% 3.67/1.00  --inst_orphan_elimination               true
% 3.67/1.00  --inst_learning_loop_flag               true
% 3.67/1.00  --inst_learning_start                   3000
% 3.67/1.00  --inst_learning_factor                  2
% 3.67/1.00  --inst_start_prop_sim_after_learn       3
% 3.67/1.00  --inst_sel_renew                        solver
% 3.67/1.00  --inst_lit_activity_flag                true
% 3.67/1.00  --inst_restr_to_given                   false
% 3.67/1.00  --inst_activity_threshold               500
% 3.67/1.00  --inst_out_proof                        true
% 3.67/1.00  
% 3.67/1.00  ------ Resolution Options
% 3.67/1.00  
% 3.67/1.00  --resolution_flag                       true
% 3.67/1.00  --res_lit_sel                           adaptive
% 3.67/1.00  --res_lit_sel_side                      none
% 3.67/1.00  --res_ordering                          kbo
% 3.67/1.00  --res_to_prop_solver                    active
% 3.67/1.00  --res_prop_simpl_new                    false
% 3.67/1.00  --res_prop_simpl_given                  true
% 3.67/1.00  --res_passive_queue_type                priority_queues
% 3.67/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.67/1.00  --res_passive_queues_freq               [15;5]
% 3.67/1.00  --res_forward_subs                      full
% 3.67/1.00  --res_backward_subs                     full
% 3.67/1.00  --res_forward_subs_resolution           true
% 3.67/1.00  --res_backward_subs_resolution          true
% 3.67/1.00  --res_orphan_elimination                true
% 3.67/1.00  --res_time_limit                        2.
% 3.67/1.00  --res_out_proof                         true
% 3.67/1.00  
% 3.67/1.00  ------ Superposition Options
% 3.67/1.00  
% 3.67/1.00  --superposition_flag                    true
% 3.67/1.00  --sup_passive_queue_type                priority_queues
% 3.67/1.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.67/1.00  --sup_passive_queues_freq               [1;4]
% 3.67/1.00  --demod_completeness_check              fast
% 3.67/1.00  --demod_use_ground                      true
% 3.67/1.00  --sup_to_prop_solver                    passive
% 3.67/1.00  --sup_prop_simpl_new                    true
% 3.67/1.00  --sup_prop_simpl_given                  true
% 3.67/1.00  --sup_fun_splitting                     false
% 3.67/1.00  --sup_smt_interval                      50000
% 3.67/1.00  
% 3.67/1.00  ------ Superposition Simplification Setup
% 3.67/1.00  
% 3.67/1.00  --sup_indices_passive                   []
% 3.67/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.67/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.67/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.67/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.67/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.67/1.00  --sup_full_bw                           [BwDemod]
% 3.67/1.00  --sup_immed_triv                        [TrivRules]
% 3.67/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.67/1.00  --sup_immed_bw_main                     []
% 3.67/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.67/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.67/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.67/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.67/1.00  
% 3.67/1.00  ------ Combination Options
% 3.67/1.00  
% 3.67/1.00  --comb_res_mult                         3
% 3.67/1.00  --comb_sup_mult                         2
% 3.67/1.00  --comb_inst_mult                        10
% 3.67/1.00  
% 3.67/1.00  ------ Debug Options
% 3.67/1.00  
% 3.67/1.00  --dbg_backtrace                         false
% 3.67/1.00  --dbg_dump_prop_clauses                 false
% 3.67/1.00  --dbg_dump_prop_clauses_file            -
% 3.67/1.00  --dbg_out_stat                          false
% 3.67/1.00  
% 3.67/1.00  
% 3.67/1.00  
% 3.67/1.00  
% 3.67/1.00  ------ Proving...
% 3.67/1.00  
% 3.67/1.00  
% 3.67/1.00  % SZS status Theorem for theBenchmark.p
% 3.67/1.00  
% 3.67/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.67/1.00  
% 3.67/1.00  fof(f1,axiom,(
% 3.67/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f12,plain,(
% 3.67/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 3.67/1.00    inference(unused_predicate_definition_removal,[],[f1])).
% 3.67/1.00  
% 3.67/1.00  fof(f13,plain,(
% 3.67/1.00    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 3.67/1.00    inference(ennf_transformation,[],[f12])).
% 3.67/1.00  
% 3.67/1.00  fof(f20,plain,(
% 3.67/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.67/1.00    introduced(choice_axiom,[])).
% 3.67/1.00  
% 3.67/1.00  fof(f21,plain,(
% 3.67/1.00    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.67/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f20])).
% 3.67/1.00  
% 3.67/1.00  fof(f37,plain,(
% 3.67/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f21])).
% 3.67/1.00  
% 3.67/1.00  fof(f9,conjecture,(
% 3.67/1.00    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f10,negated_conjecture,(
% 3.67/1.00    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.67/1.00    inference(negated_conjecture,[],[f9])).
% 3.67/1.00  
% 3.67/1.00  fof(f18,plain,(
% 3.67/1.00    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 3.67/1.00    inference(ennf_transformation,[],[f10])).
% 3.67/1.00  
% 3.67/1.00  fof(f19,plain,(
% 3.67/1.00    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 3.67/1.00    inference(flattening,[],[f18])).
% 3.67/1.00  
% 3.67/1.00  fof(f35,plain,(
% 3.67/1.00    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)) => ((sK8 != sK10 | sK7 != sK9) & k1_xboole_0 != sK8 & k1_xboole_0 != sK7 & k2_zfmisc_1(sK7,sK8) = k2_zfmisc_1(sK9,sK10))),
% 3.67/1.00    introduced(choice_axiom,[])).
% 3.67/1.00  
% 3.67/1.00  fof(f36,plain,(
% 3.67/1.00    (sK8 != sK10 | sK7 != sK9) & k1_xboole_0 != sK8 & k1_xboole_0 != sK7 & k2_zfmisc_1(sK7,sK8) = k2_zfmisc_1(sK9,sK10)),
% 3.67/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f19,f35])).
% 3.67/1.00  
% 3.67/1.00  fof(f61,plain,(
% 3.67/1.00    k2_zfmisc_1(sK7,sK8) = k2_zfmisc_1(sK9,sK10)),
% 3.67/1.00    inference(cnf_transformation,[],[f36])).
% 3.67/1.00  
% 3.67/1.00  fof(f7,axiom,(
% 3.67/1.00    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 3.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f31,plain,(
% 3.67/1.00    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.67/1.00    inference(nnf_transformation,[],[f7])).
% 3.67/1.00  
% 3.67/1.00  fof(f32,plain,(
% 3.67/1.00    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.67/1.00    inference(flattening,[],[f31])).
% 3.67/1.00  
% 3.67/1.00  fof(f57,plain,(
% 3.67/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f32])).
% 3.67/1.00  
% 3.67/1.00  fof(f56,plain,(
% 3.67/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 3.67/1.00    inference(cnf_transformation,[],[f32])).
% 3.67/1.00  
% 3.67/1.00  fof(f2,axiom,(
% 3.67/1.00    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 3.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f11,plain,(
% 3.67/1.00    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 3.67/1.00    inference(unused_predicate_definition_removal,[],[f2])).
% 3.67/1.00  
% 3.67/1.00  fof(f14,plain,(
% 3.67/1.00    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 3.67/1.00    inference(ennf_transformation,[],[f11])).
% 3.67/1.00  
% 3.67/1.00  fof(f15,plain,(
% 3.67/1.00    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 3.67/1.00    inference(flattening,[],[f14])).
% 3.67/1.00  
% 3.67/1.00  fof(f39,plain,(
% 3.67/1.00    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f15])).
% 3.67/1.00  
% 3.67/1.00  fof(f64,plain,(
% 3.67/1.00    sK8 != sK10 | sK7 != sK9),
% 3.67/1.00    inference(cnf_transformation,[],[f36])).
% 3.67/1.00  
% 3.67/1.00  fof(f4,axiom,(
% 3.67/1.00    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 3.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f17,plain,(
% 3.67/1.00    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 3.67/1.00    inference(ennf_transformation,[],[f4])).
% 3.67/1.00  
% 3.67/1.00  fof(f23,plain,(
% 3.67/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) => (~r2_hidden(sK1(X0,X1),X0) & r2_hidden(sK1(X0,X1),X1)))),
% 3.67/1.00    introduced(choice_axiom,[])).
% 3.67/1.00  
% 3.67/1.00  fof(f24,plain,(
% 3.67/1.00    ! [X0,X1] : ((~r2_hidden(sK1(X0,X1),X0) & r2_hidden(sK1(X0,X1),X1)) | ~r2_xboole_0(X0,X1))),
% 3.67/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f23])).
% 3.67/1.00  
% 3.67/1.00  fof(f44,plain,(
% 3.67/1.00    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | ~r2_xboole_0(X0,X1)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f24])).
% 3.67/1.00  
% 3.67/1.00  fof(f55,plain,(
% 3.67/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 3.67/1.00    inference(cnf_transformation,[],[f32])).
% 3.67/1.00  
% 3.67/1.00  fof(f63,plain,(
% 3.67/1.00    k1_xboole_0 != sK8),
% 3.67/1.00    inference(cnf_transformation,[],[f36])).
% 3.67/1.00  
% 3.67/1.00  fof(f8,axiom,(
% 3.67/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f33,plain,(
% 3.67/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.67/1.00    inference(nnf_transformation,[],[f8])).
% 3.67/1.00  
% 3.67/1.00  fof(f34,plain,(
% 3.67/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.67/1.00    inference(flattening,[],[f33])).
% 3.67/1.00  
% 3.67/1.00  fof(f58,plain,(
% 3.67/1.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f34])).
% 3.67/1.00  
% 3.67/1.00  fof(f59,plain,(
% 3.67/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.67/1.00    inference(cnf_transformation,[],[f34])).
% 3.67/1.00  
% 3.67/1.00  fof(f71,plain,(
% 3.67/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.67/1.00    inference(equality_resolution,[],[f59])).
% 3.67/1.00  
% 3.67/1.00  fof(f6,axiom,(
% 3.67/1.00    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 3.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f25,plain,(
% 3.67/1.00    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.67/1.00    inference(nnf_transformation,[],[f6])).
% 3.67/1.00  
% 3.67/1.00  fof(f26,plain,(
% 3.67/1.00    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.67/1.00    inference(rectify,[],[f25])).
% 3.67/1.00  
% 3.67/1.00  fof(f29,plain,(
% 3.67/1.00    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)))),
% 3.67/1.00    introduced(choice_axiom,[])).
% 3.67/1.00  
% 3.67/1.00  fof(f28,plain,(
% 3.67/1.00    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = X3 & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)))) )),
% 3.67/1.00    introduced(choice_axiom,[])).
% 3.67/1.00  
% 3.67/1.00  fof(f27,plain,(
% 3.67/1.00    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK2(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 3.67/1.00    introduced(choice_axiom,[])).
% 3.67/1.00  
% 3.67/1.00  fof(f30,plain,(
% 3.67/1.00    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = sK2(X0,X1,X2) & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.67/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f26,f29,f28,f27])).
% 3.67/1.00  
% 3.67/1.00  fof(f51,plain,(
% 3.67/1.00    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f30])).
% 3.67/1.00  
% 3.67/1.00  fof(f5,axiom,(
% 3.67/1.00    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f46,plain,(
% 3.67/1.00    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.67/1.00    inference(cnf_transformation,[],[f5])).
% 3.67/1.00  
% 3.67/1.00  fof(f3,axiom,(
% 3.67/1.00    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 3.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f16,plain,(
% 3.67/1.00    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 3.67/1.00    inference(ennf_transformation,[],[f3])).
% 3.67/1.00  
% 3.67/1.00  fof(f22,plain,(
% 3.67/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 3.67/1.00    inference(nnf_transformation,[],[f16])).
% 3.67/1.00  
% 3.67/1.00  fof(f43,plain,(
% 3.67/1.00    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f22])).
% 3.67/1.00  
% 3.67/1.00  fof(f41,plain,(
% 3.67/1.00    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 3.67/1.00    inference(cnf_transformation,[],[f22])).
% 3.67/1.00  
% 3.67/1.00  fof(f45,plain,(
% 3.67/1.00    ( ! [X0,X1] : (~r2_hidden(sK1(X0,X1),X0) | ~r2_xboole_0(X0,X1)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f24])).
% 3.67/1.00  
% 3.67/1.00  fof(f38,plain,(
% 3.67/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f21])).
% 3.67/1.00  
% 3.67/1.00  fof(f62,plain,(
% 3.67/1.00    k1_xboole_0 != sK7),
% 3.67/1.00    inference(cnf_transformation,[],[f36])).
% 3.67/1.00  
% 3.67/1.00  fof(f52,plain,(
% 3.67/1.00    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f30])).
% 3.67/1.00  
% 3.67/1.00  fof(f60,plain,(
% 3.67/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.67/1.00    inference(cnf_transformation,[],[f34])).
% 3.67/1.00  
% 3.67/1.00  fof(f70,plain,(
% 3.67/1.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.67/1.00    inference(equality_resolution,[],[f60])).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1,plain,
% 3.67/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.67/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_512,plain,
% 3.67/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.67/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_27,negated_conjecture,
% 3.67/1.00      ( k2_zfmisc_1(sK7,sK8) = k2_zfmisc_1(sK9,sK10) ),
% 3.67/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_18,plain,
% 3.67/1.00      ( ~ r2_hidden(X0,X1)
% 3.67/1.00      | ~ r2_hidden(X2,X3)
% 3.67/1.00      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 3.67/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_496,plain,
% 3.67/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.67/1.00      | r2_hidden(X2,X3) != iProver_top
% 3.67/1.00      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_986,plain,
% 3.67/1.00      ( r2_hidden(X0,sK9) != iProver_top
% 3.67/1.00      | r2_hidden(X1,sK10) != iProver_top
% 3.67/1.00      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK7,sK8)) = iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_27,c_496]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_19,plain,
% 3.67/1.00      ( r2_hidden(X0,X1)
% 3.67/1.00      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 3.67/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_495,plain,
% 3.67/1.00      ( r2_hidden(X0,X1) = iProver_top
% 3.67/1.00      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_4470,plain,
% 3.67/1.00      ( r2_hidden(X0,sK9) != iProver_top
% 3.67/1.00      | r2_hidden(X1,sK10) != iProver_top
% 3.67/1.00      | r2_hidden(X1,sK8) = iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_986,c_495]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_8861,plain,
% 3.67/1.00      ( r2_hidden(X0,sK10) != iProver_top
% 3.67/1.00      | r2_hidden(X0,sK8) = iProver_top
% 3.67/1.00      | r1_tarski(sK9,X1) = iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_512,c_4470]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_9060,plain,
% 3.67/1.00      ( r2_hidden(sK0(sK10,X0),sK8) = iProver_top
% 3.67/1.00      | r1_tarski(sK9,X1) = iProver_top
% 3.67/1.00      | r1_tarski(sK10,X0) = iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_512,c_8861]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2,plain,
% 3.67/1.00      ( r2_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | X1 = X0 ),
% 3.67/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_511,plain,
% 3.67/1.00      ( X0 = X1
% 3.67/1.00      | r2_xboole_0(X1,X0) = iProver_top
% 3.67/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_10331,plain,
% 3.67/1.00      ( sK9 = X0
% 3.67/1.00      | r2_xboole_0(sK9,X0) = iProver_top
% 3.67/1.00      | r2_hidden(sK0(sK10,X1),sK8) = iProver_top
% 3.67/1.00      | r1_tarski(sK10,X1) = iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_9060,c_511]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_684,plain,
% 3.67/1.00      ( r2_xboole_0(sK10,sK8) | ~ r1_tarski(sK10,sK8) | sK8 = sK10 ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_685,plain,
% 3.67/1.00      ( sK8 = sK10
% 3.67/1.00      | r2_xboole_0(sK10,sK8) = iProver_top
% 3.67/1.00      | r1_tarski(sK10,sK8) != iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_684]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_24,negated_conjecture,
% 3.67/1.00      ( sK7 != sK9 | sK8 != sK10 ),
% 3.67/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_7931,plain,
% 3.67/1.00      ( r2_xboole_0(sK9,sK7) | ~ r1_tarski(sK9,sK7) | sK8 != sK10 ),
% 3.67/1.00      inference(resolution,[status(thm)],[c_2,c_24]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_7932,plain,
% 3.67/1.00      ( sK8 != sK10
% 3.67/1.00      | r2_xboole_0(sK9,sK7) = iProver_top
% 3.67/1.00      | r1_tarski(sK9,sK7) != iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_7931]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_8,plain,
% 3.67/1.00      ( ~ r2_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 3.67/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_505,plain,
% 3.67/1.00      ( r2_xboole_0(X0,X1) != iProver_top
% 3.67/1.00      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_20,plain,
% 3.67/1.00      ( r2_hidden(X0,X1)
% 3.67/1.00      | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 3.67/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_494,plain,
% 3.67/1.00      ( r2_hidden(X0,X1) = iProver_top
% 3.67/1.00      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_780,plain,
% 3.67/1.00      ( r2_hidden(X0,sK9) = iProver_top
% 3.67/1.00      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK7,sK8)) != iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_27,c_494]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1591,plain,
% 3.67/1.00      ( r2_hidden(X0,sK9) = iProver_top
% 3.67/1.00      | r2_hidden(X0,sK7) != iProver_top
% 3.67/1.00      | r2_hidden(X1,sK8) != iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_496,c_780]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_5513,plain,
% 3.67/1.00      ( r2_hidden(X0,sK9) = iProver_top
% 3.67/1.00      | r2_hidden(X0,sK7) != iProver_top
% 3.67/1.00      | r1_tarski(sK8,X1) = iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_512,c_1591]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_25,negated_conjecture,
% 3.67/1.00      ( k1_xboole_0 != sK8 ),
% 3.67/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_23,plain,
% 3.67/1.00      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.67/1.00      | k1_xboole_0 = X1
% 3.67/1.00      | k1_xboole_0 = X0 ),
% 3.67/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_28,plain,
% 3.67/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.67/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_23]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_22,plain,
% 3.67/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.67/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_29,plain,
% 3.67/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_22]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_193,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_707,plain,
% 3.67/1.00      ( sK8 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK8 ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_193]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_708,plain,
% 3.67/1.00      ( sK8 != k1_xboole_0
% 3.67/1.00      | k1_xboole_0 = sK8
% 3.67/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_707]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_13,plain,
% 3.67/1.00      ( r2_hidden(sK3(X0,X1,X2),X0)
% 3.67/1.00      | r2_hidden(sK2(X0,X1,X2),X2)
% 3.67/1.00      | k2_zfmisc_1(X0,X1) = X2 ),
% 3.67/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_501,plain,
% 3.67/1.00      ( k2_zfmisc_1(X0,X1) = X2
% 3.67/1.00      | r2_hidden(sK3(X0,X1,X2),X0) = iProver_top
% 3.67/1.00      | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_9,plain,
% 3.67/1.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.67/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_3,plain,
% 3.67/1.00      ( ~ r2_hidden(X0,X1)
% 3.67/1.00      | r2_hidden(X0,X2)
% 3.67/1.00      | r2_hidden(X0,k5_xboole_0(X2,X1)) ),
% 3.67/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_510,plain,
% 3.67/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.67/1.00      | r2_hidden(X0,X2) = iProver_top
% 3.67/1.00      | r2_hidden(X0,k5_xboole_0(X2,X1)) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2516,plain,
% 3.67/1.00      ( r2_hidden(X0,X1) = iProver_top
% 3.67/1.00      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_9,c_510]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2545,plain,
% 3.67/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = X1
% 3.67/1.00      | r2_hidden(sK3(k1_xboole_0,X0,X1),X2) = iProver_top
% 3.67/1.00      | r2_hidden(sK2(k1_xboole_0,X0,X1),X1) = iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_501,c_2516]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2561,plain,
% 3.67/1.00      ( k1_xboole_0 = X0
% 3.67/1.00      | r2_hidden(sK3(k1_xboole_0,X1,X0),X2) = iProver_top
% 3.67/1.00      | r2_hidden(sK2(k1_xboole_0,X1,X0),X0) = iProver_top ),
% 3.67/1.00      inference(demodulation,[status(thm)],[c_2545,c_22]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_5,plain,
% 3.67/1.00      ( ~ r2_hidden(X0,X1)
% 3.67/1.00      | ~ r2_hidden(X0,X2)
% 3.67/1.00      | ~ r2_hidden(X0,k5_xboole_0(X2,X1)) ),
% 3.67/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_508,plain,
% 3.67/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.67/1.00      | r2_hidden(X0,X2) != iProver_top
% 3.67/1.00      | r2_hidden(X0,k5_xboole_0(X2,X1)) != iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_4015,plain,
% 3.67/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.67/1.00      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_9,c_508]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_4406,plain,
% 3.67/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.67/1.00      inference(global_propositional_subsumption,
% 3.67/1.00                [status(thm)],
% 3.67/1.00                [c_4015,c_2516]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_4420,plain,
% 3.67/1.00      ( k1_xboole_0 = X0
% 3.67/1.00      | r2_hidden(sK2(k1_xboole_0,X1,X0),X0) = iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_2561,c_4406]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_6888,plain,
% 3.67/1.00      ( sK8 = k1_xboole_0
% 3.67/1.00      | r2_hidden(X0,sK9) = iProver_top
% 3.67/1.00      | r2_hidden(X0,sK7) != iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_4420,c_1591]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_7770,plain,
% 3.67/1.00      ( r2_hidden(X0,sK7) != iProver_top
% 3.67/1.00      | r2_hidden(X0,sK9) = iProver_top ),
% 3.67/1.00      inference(global_propositional_subsumption,
% 3.67/1.00                [status(thm)],
% 3.67/1.00                [c_5513,c_25,c_28,c_29,c_708,c_6888]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_7771,plain,
% 3.67/1.00      ( r2_hidden(X0,sK9) = iProver_top
% 3.67/1.00      | r2_hidden(X0,sK7) != iProver_top ),
% 3.67/1.00      inference(renaming,[status(thm)],[c_7770]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_7779,plain,
% 3.67/1.00      ( r2_xboole_0(X0,sK7) != iProver_top
% 3.67/1.00      | r2_hidden(sK1(X0,sK7),sK9) = iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_505,c_7771]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_7,plain,
% 3.67/1.00      ( ~ r2_xboole_0(X0,X1) | ~ r2_hidden(sK1(X0,X1),X0) ),
% 3.67/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_506,plain,
% 3.67/1.00      ( r2_xboole_0(X0,X1) != iProver_top
% 3.67/1.00      | r2_hidden(sK1(X0,X1),X0) != iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_8420,plain,
% 3.67/1.00      ( r2_xboole_0(sK9,sK7) != iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_7779,c_506]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_0,plain,
% 3.67/1.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.67/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_513,plain,
% 3.67/1.00      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.67/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_10332,plain,
% 3.67/1.00      ( r1_tarski(sK9,X0) = iProver_top
% 3.67/1.00      | r1_tarski(sK10,sK8) = iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_9060,c_513]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_10361,plain,
% 3.67/1.00      ( sK9 = X0
% 3.67/1.00      | r2_xboole_0(sK9,X0) = iProver_top
% 3.67/1.00      | r1_tarski(sK10,sK8) = iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_10332,c_511]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_4471,plain,
% 3.67/1.00      ( r2_hidden(X0,sK9) != iProver_top
% 3.67/1.00      | r2_hidden(X0,sK7) = iProver_top
% 3.67/1.00      | r2_hidden(X1,sK10) != iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_986,c_494]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_9619,plain,
% 3.67/1.00      ( r2_hidden(X0,sK10) != iProver_top
% 3.67/1.00      | r2_hidden(sK0(sK9,X1),sK7) = iProver_top
% 3.67/1.00      | r1_tarski(sK9,X1) = iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_512,c_4471]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_11819,plain,
% 3.67/1.00      ( r2_hidden(sK0(sK9,X0),sK7) = iProver_top
% 3.67/1.00      | r1_tarski(sK9,X0) = iProver_top
% 3.67/1.00      | r1_tarski(sK10,X1) = iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_512,c_9619]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_705,plain,
% 3.67/1.00      ( sK10 != X0 | sK8 != X0 | sK8 = sK10 ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_193]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_818,plain,
% 3.67/1.00      ( sK10 != sK8 | sK8 = sK10 | sK8 != sK8 ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_705]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_192,plain,( X0 = X0 ),theory(equality) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_819,plain,
% 3.67/1.00      ( sK8 = sK8 ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_192]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1321,plain,
% 3.67/1.00      ( sK8 != sK10 | k1_xboole_0 != sK10 | k1_xboole_0 = sK8 ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_707]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2456,plain,
% 3.67/1.00      ( sK10 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK10 ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_193]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2457,plain,
% 3.67/1.00      ( sK10 != k1_xboole_0
% 3.67/1.00      | k1_xboole_0 = sK10
% 3.67/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_2456]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_779,plain,
% 3.67/1.00      ( r2_hidden(X0,sK10) = iProver_top
% 3.67/1.00      | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK7,sK8)) != iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_27,c_495]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1584,plain,
% 3.67/1.00      ( r2_hidden(X0,sK7) != iProver_top
% 3.67/1.00      | r2_hidden(X1,sK10) = iProver_top
% 3.67/1.00      | r2_hidden(X1,sK8) != iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_496,c_779]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_4612,plain,
% 3.67/1.00      ( r2_hidden(X0,sK7) != iProver_top
% 3.67/1.00      | r2_hidden(sK0(sK8,X1),sK10) = iProver_top
% 3.67/1.00      | r1_tarski(sK8,X1) = iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_512,c_1584]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_11006,plain,
% 3.67/1.00      ( r2_hidden(sK0(sK8,X0),sK10) = iProver_top
% 3.67/1.00      | r1_tarski(sK7,X1) = iProver_top
% 3.67/1.00      | r1_tarski(sK8,X0) = iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_512,c_4612]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_26,negated_conjecture,
% 3.67/1.00      ( k1_xboole_0 != sK7 ),
% 3.67/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_709,plain,
% 3.67/1.00      ( sK7 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK7 ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_193]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_710,plain,
% 3.67/1.00      ( sK7 != k1_xboole_0
% 3.67/1.00      | k1_xboole_0 = sK7
% 3.67/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_709]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_12,plain,
% 3.67/1.00      ( r2_hidden(sK4(X0,X1,X2),X1)
% 3.67/1.00      | r2_hidden(sK2(X0,X1,X2),X2)
% 3.67/1.00      | k2_zfmisc_1(X0,X1) = X2 ),
% 3.67/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_502,plain,
% 3.67/1.00      ( k2_zfmisc_1(X0,X1) = X2
% 3.67/1.00      | r2_hidden(sK4(X0,X1,X2),X1) = iProver_top
% 3.67/1.00      | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top ),
% 3.67/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2834,plain,
% 3.67/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = X1
% 3.67/1.00      | r2_hidden(sK4(X0,k1_xboole_0,X1),X2) = iProver_top
% 3.67/1.00      | r2_hidden(sK2(X0,k1_xboole_0,X1),X1) = iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_502,c_2516]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_21,plain,
% 3.67/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.67/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2838,plain,
% 3.67/1.00      ( k1_xboole_0 = X0
% 3.67/1.00      | r2_hidden(sK4(X1,k1_xboole_0,X0),X2) = iProver_top
% 3.67/1.00      | r2_hidden(sK2(X1,k1_xboole_0,X0),X0) = iProver_top ),
% 3.67/1.00      inference(demodulation,[status(thm)],[c_2834,c_21]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_4422,plain,
% 3.67/1.00      ( k1_xboole_0 = X0
% 3.67/1.00      | r2_hidden(sK2(X1,k1_xboole_0,X0),X0) = iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_2838,c_4406]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_11025,plain,
% 3.67/1.00      ( sK7 = k1_xboole_0
% 3.67/1.00      | r2_hidden(sK0(sK8,X0),sK10) = iProver_top
% 3.67/1.00      | r1_tarski(sK8,X0) = iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_4422,c_4612]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_11154,plain,
% 3.67/1.00      ( r2_hidden(sK0(sK8,X0),sK10) = iProver_top
% 3.67/1.00      | r1_tarski(sK8,X0) = iProver_top ),
% 3.67/1.00      inference(global_propositional_subsumption,
% 3.67/1.00                [status(thm)],
% 3.67/1.00                [c_11006,c_26,c_28,c_29,c_710,c_11025]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_11162,plain,
% 3.67/1.00      ( r1_tarski(sK8,sK10) = iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_11154,c_513]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_11404,plain,
% 3.67/1.00      ( sK10 = sK8 | r2_xboole_0(sK8,sK10) = iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_11162,c_511]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_9061,plain,
% 3.67/1.00      ( r2_xboole_0(X0,sK10) != iProver_top
% 3.67/1.00      | r2_hidden(sK1(X0,sK10),sK8) = iProver_top
% 3.67/1.00      | r1_tarski(sK9,X1) = iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_505,c_8861]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_11531,plain,
% 3.67/1.00      ( r2_xboole_0(sK8,sK10) != iProver_top
% 3.67/1.00      | r1_tarski(sK9,X0) = iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_9061,c_506]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_11566,plain,
% 3.67/1.00      ( sK10 = sK8 | r1_tarski(sK9,X0) = iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_11404,c_11531]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_11838,plain,
% 3.67/1.00      ( sK10 = k1_xboole_0
% 3.67/1.00      | r2_hidden(sK0(sK9,X0),sK7) = iProver_top
% 3.67/1.00      | r1_tarski(sK9,X0) = iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_4422,c_9619]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_12467,plain,
% 3.67/1.00      ( r1_tarski(sK9,X0) = iProver_top
% 3.67/1.00      | r2_hidden(sK0(sK9,X0),sK7) = iProver_top ),
% 3.67/1.00      inference(global_propositional_subsumption,
% 3.67/1.00                [status(thm)],
% 3.67/1.00                [c_11819,c_25,c_28,c_29,c_818,c_819,c_1321,c_2457,
% 3.67/1.00                 c_11566,c_11838]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_12468,plain,
% 3.67/1.00      ( r2_hidden(sK0(sK9,X0),sK7) = iProver_top
% 3.67/1.00      | r1_tarski(sK9,X0) = iProver_top ),
% 3.67/1.00      inference(renaming,[status(thm)],[c_12467]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_12475,plain,
% 3.67/1.00      ( r1_tarski(sK9,sK7) = iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_12468,c_513]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_4613,plain,
% 3.67/1.00      ( r2_xboole_0(X0,sK8) != iProver_top
% 3.67/1.00      | r2_hidden(X1,sK7) != iProver_top
% 3.67/1.00      | r2_hidden(sK1(X0,sK8),sK10) = iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_505,c_1584]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_14960,plain,
% 3.67/1.00      ( r2_xboole_0(X0,sK8) != iProver_top
% 3.67/1.00      | r2_hidden(sK1(X0,sK8),sK10) = iProver_top
% 3.67/1.00      | r1_tarski(sK7,X1) = iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_512,c_4613]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_14986,plain,
% 3.67/1.00      ( sK7 = k1_xboole_0
% 3.67/1.00      | r2_xboole_0(X0,sK8) != iProver_top
% 3.67/1.00      | r2_hidden(sK1(X0,sK8),sK10) = iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_4422,c_4613]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_15404,plain,
% 3.67/1.00      ( r2_hidden(sK1(X0,sK8),sK10) = iProver_top
% 3.67/1.00      | r2_xboole_0(X0,sK8) != iProver_top ),
% 3.67/1.00      inference(global_propositional_subsumption,
% 3.67/1.00                [status(thm)],
% 3.67/1.00                [c_14960,c_26,c_28,c_29,c_710,c_14986]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_15405,plain,
% 3.67/1.00      ( r2_xboole_0(X0,sK8) != iProver_top
% 3.67/1.00      | r2_hidden(sK1(X0,sK8),sK10) = iProver_top ),
% 3.67/1.00      inference(renaming,[status(thm)],[c_15404]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_15414,plain,
% 3.67/1.00      ( r2_xboole_0(sK10,sK8) != iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_15405,c_506]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_17387,plain,
% 3.67/1.00      ( sK9 = X0 | r2_xboole_0(sK9,X0) = iProver_top ),
% 3.67/1.00      inference(global_propositional_subsumption,
% 3.67/1.00                [status(thm)],
% 3.67/1.00                [c_10331,c_685,c_7932,c_8420,c_10361,c_12475,c_15414]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_12490,plain,
% 3.67/1.00      ( sK9 = sK7 | r2_xboole_0(sK9,sK7) = iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_12475,c_511]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_12753,plain,
% 3.67/1.00      ( sK9 = sK7 ),
% 3.67/1.00      inference(global_propositional_subsumption,
% 3.67/1.00                [status(thm)],
% 3.67/1.00                [c_12490,c_8420]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_17393,plain,
% 3.67/1.00      ( sK9 = X0 | r2_xboole_0(sK7,X0) = iProver_top ),
% 3.67/1.00      inference(light_normalisation,[status(thm)],[c_17387,c_12753]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_17394,plain,
% 3.67/1.00      ( sK7 = X0 | r2_xboole_0(sK7,X0) = iProver_top ),
% 3.67/1.00      inference(demodulation,[status(thm)],[c_17393,c_12753]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_4412,plain,
% 3.67/1.00      ( r2_xboole_0(X0,k1_xboole_0) != iProver_top ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_505,c_4406]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_17404,plain,
% 3.67/1.00      ( sK7 = k1_xboole_0 ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_17394,c_4412]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(contradiction,plain,
% 3.67/1.00      ( $false ),
% 3.67/1.00      inference(minisat,[status(thm)],[c_17404,c_710,c_29,c_28,c_26]) ).
% 3.67/1.00  
% 3.67/1.00  
% 3.67/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.67/1.00  
% 3.67/1.00  ------                               Statistics
% 3.67/1.00  
% 3.67/1.00  ------ Selected
% 3.67/1.00  
% 3.67/1.00  total_time:                             0.491
% 3.67/1.00  
%------------------------------------------------------------------------------
