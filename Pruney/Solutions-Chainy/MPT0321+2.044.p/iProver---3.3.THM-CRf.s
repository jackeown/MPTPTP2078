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
% DateTime   : Thu Dec  3 11:37:45 EST 2020

% Result     : Theorem 7.23s
% Output     : CNFRefutation 7.23s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 875 expanded)
%              Number of clauses        :   79 ( 299 expanded)
%              Number of leaves         :   15 ( 175 expanded)
%              Depth                    :   20
%              Number of atoms          :  415 (3504 expanded)
%              Number of equality atoms :  231 (1624 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK2(X0,X1),X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f22])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f25])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f63,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f41])).

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

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f32])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f33])).

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

fof(f36,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | X0 != X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) )
   => ( ( sK5 != sK7
        | sK4 != sK6 )
      & k1_xboole_0 != sK5
      & k1_xboole_0 != sK4
      & k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK6,sK7) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ( sK5 != sK7
      | sK4 != sK6 )
    & k1_xboole_0 != sK5
    & k1_xboole_0 != sK4
    & k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f19,f36])).

fof(f58,plain,(
    k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK6,sK7) ),
    inference(cnf_transformation,[],[f37])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f59,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f34])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f66,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f3,axiom,(
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
    inference(unused_predicate_definition_removal,[],[f3])).

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

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(sK3(X0,X1),X0)
        & r2_hidden(sK3(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r2_hidden(sK3(X0,X1),X0)
        & r2_hidden(sK3(X0,X1),X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f30])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f60,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f37])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f61,plain,
    ( sK5 != sK7
    | sK4 != sK6 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_10,plain,
    ( r2_hidden(sK2(X0,X1),X1)
    | r2_hidden(sK2(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_528,plain,
    ( X0 = X1
    | r2_hidden(sK2(X1,X0),X0) = iProver_top
    | r2_hidden(sK2(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_13,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_532,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1250,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_532])).

cnf(c_1537,plain,
    ( X0 = X1
    | r2_hidden(sK2(X0,X1),X1) = iProver_top
    | r2_hidden(sK2(X0,X1),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_528,c_1250])).

cnf(c_3168,plain,
    ( X0 = X1
    | r2_hidden(sK2(X1,X0),k1_xboole_0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1537,c_1250])).

cnf(c_3170,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_528,c_3168])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_537,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_525,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_23,negated_conjecture,
    ( k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK6,sK7) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_15,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_524,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1359,plain,
    ( r2_hidden(X0,sK7) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_524])).

cnf(c_2160,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X1,sK7) = iProver_top
    | r2_hidden(X1,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_525,c_1359])).

cnf(c_2730,plain,
    ( r2_hidden(X0,sK7) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | r1_tarski(sK4,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_537,c_2160])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_19,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_24,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_18,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_25,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_261,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_693,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_261])).

cnf(c_694,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_693])).

cnf(c_1342,plain,
    ( r2_hidden(sK0(X0,X1),k1_xboole_0) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_537,c_1250])).

cnf(c_1849,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_537,c_1342])).

cnf(c_8,plain,
    ( r2_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_530,plain,
    ( X0 = X1
    | r2_xboole_0(X1,X0) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1853,plain,
    ( k1_xboole_0 = X0
    | r2_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1849,c_530])).

cnf(c_12,plain,
    ( ~ r2_xboole_0(X0,X1)
    | r2_hidden(sK3(X0,X1),X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_526,plain,
    ( r2_xboole_0(X0,X1) != iProver_top
    | r2_hidden(sK3(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2733,plain,
    ( r2_xboole_0(X0,sK4) != iProver_top
    | r2_hidden(X1,sK7) = iProver_top
    | r2_hidden(X1,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_526,c_2160])).

cnf(c_3408,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(X0,sK7) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1853,c_2733])).

cnf(c_3821,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X0,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2730,c_22,c_24,c_25,c_694,c_3408])).

cnf(c_3822,plain,
    ( r2_hidden(X0,sK7) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_3821])).

cnf(c_4415,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK2(sK5,k1_xboole_0),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_3170,c_3822])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_691,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_261])).

cnf(c_692,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_691])).

cnf(c_12806,plain,
    ( r2_hidden(sK2(sK5,k1_xboole_0),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4415,c_21,c_24,c_25,c_692])).

cnf(c_2155,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X1,sK7) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_525])).

cnf(c_16,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_523,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2591,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X1,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2155,c_523])).

cnf(c_2944,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(sK0(sK6,X1),sK4) = iProver_top
    | r1_tarski(sK6,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_537,c_2591])).

cnf(c_12823,plain,
    ( r2_hidden(sK0(sK6,X0),sK4) = iProver_top
    | r1_tarski(sK6,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_12806,c_2944])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_538,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_15419,plain,
    ( r1_tarski(sK6,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_12823,c_538])).

cnf(c_3832,plain,
    ( r2_xboole_0(X0,sK5) != iProver_top
    | r2_hidden(sK3(X0,sK5),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_526,c_3822])).

cnf(c_11,plain,
    ( ~ r2_xboole_0(X0,X1)
    | ~ r2_hidden(sK3(X0,X1),X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_527,plain,
    ( r2_xboole_0(X0,X1) != iProver_top
    | r2_hidden(sK3(X0,X1),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_9434,plain,
    ( r2_xboole_0(sK7,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3832,c_527])).

cnf(c_872,plain,
    ( r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_523])).

cnf(c_2159,plain,
    ( r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X1,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_525,c_872])).

cnf(c_4417,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK2(sK4,k1_xboole_0),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_3170,c_2159])).

cnf(c_5008,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK2(sK4,k1_xboole_0),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4417,c_22,c_24,c_25,c_694])).

cnf(c_5016,plain,
    ( r2_hidden(sK2(sK4,k1_xboole_0),sK6) = iProver_top
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_537,c_5008])).

cnf(c_5023,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK2(sK4,k1_xboole_0),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_3170,c_5008])).

cnf(c_7342,plain,
    ( r2_hidden(sK2(sK4,k1_xboole_0),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5016,c_21,c_24,c_25,c_692,c_5023])).

cnf(c_2590,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X1,sK7) != iProver_top
    | r2_hidden(X1,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2155,c_524])).

cnf(c_7350,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_7342,c_2590])).

cnf(c_7771,plain,
    ( r2_hidden(sK0(sK7,X0),sK5) = iProver_top
    | r1_tarski(sK7,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_537,c_7350])).

cnf(c_8658,plain,
    ( r1_tarski(sK7,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_7771,c_538])).

cnf(c_2628,plain,
    ( r2_xboole_0(X0,sK4) != iProver_top
    | r2_hidden(X1,sK5) != iProver_top
    | r2_hidden(sK3(X0,sK4),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_526,c_2159])).

cnf(c_3086,plain,
    ( r2_xboole_0(X0,sK4) != iProver_top
    | r2_hidden(sK3(X0,sK4),sK6) = iProver_top
    | r1_tarski(sK5,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_537,c_2628])).

cnf(c_4418,plain,
    ( sK5 = k1_xboole_0
    | r2_xboole_0(X0,sK4) != iProver_top
    | r2_hidden(sK3(X0,sK4),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_3170,c_2628])).

cnf(c_8619,plain,
    ( r2_hidden(sK3(X0,sK4),sK6) = iProver_top
    | r2_xboole_0(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3086,c_21,c_24,c_25,c_692,c_4418])).

cnf(c_8620,plain,
    ( r2_xboole_0(X0,sK4) != iProver_top
    | r2_hidden(sK3(X0,sK4),sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_8619])).

cnf(c_8629,plain,
    ( r2_xboole_0(sK6,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8620,c_527])).

cnf(c_738,plain,
    ( r2_xboole_0(sK7,sK5)
    | ~ r1_tarski(sK7,sK5)
    | sK5 = sK7 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_739,plain,
    ( sK5 = sK7
    | r2_xboole_0(sK7,sK5) = iProver_top
    | r1_tarski(sK7,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_738])).

cnf(c_678,plain,
    ( r2_xboole_0(sK6,sK4)
    | ~ r1_tarski(sK6,sK4)
    | sK4 = sK6 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_679,plain,
    ( sK4 = sK6
    | r2_xboole_0(sK6,sK4) = iProver_top
    | r1_tarski(sK6,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_678])).

cnf(c_20,negated_conjecture,
    ( sK4 != sK6
    | sK5 != sK7 ),
    inference(cnf_transformation,[],[f61])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15419,c_9434,c_8658,c_8629,c_739,c_679,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:43:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.23/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.23/1.51  
% 7.23/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.23/1.51  
% 7.23/1.51  ------  iProver source info
% 7.23/1.51  
% 7.23/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.23/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.23/1.51  git: non_committed_changes: false
% 7.23/1.51  git: last_make_outside_of_git: false
% 7.23/1.51  
% 7.23/1.51  ------ 
% 7.23/1.51  
% 7.23/1.51  ------ Input Options
% 7.23/1.51  
% 7.23/1.51  --out_options                           all
% 7.23/1.51  --tptp_safe_out                         true
% 7.23/1.51  --problem_path                          ""
% 7.23/1.51  --include_path                          ""
% 7.23/1.51  --clausifier                            res/vclausify_rel
% 7.23/1.51  --clausifier_options                    --mode clausify
% 7.23/1.51  --stdin                                 false
% 7.23/1.51  --stats_out                             all
% 7.23/1.51  
% 7.23/1.51  ------ General Options
% 7.23/1.51  
% 7.23/1.51  --fof                                   false
% 7.23/1.51  --time_out_real                         305.
% 7.23/1.51  --time_out_virtual                      -1.
% 7.23/1.51  --symbol_type_check                     false
% 7.23/1.51  --clausify_out                          false
% 7.23/1.51  --sig_cnt_out                           false
% 7.23/1.51  --trig_cnt_out                          false
% 7.23/1.51  --trig_cnt_out_tolerance                1.
% 7.23/1.51  --trig_cnt_out_sk_spl                   false
% 7.23/1.51  --abstr_cl_out                          false
% 7.23/1.51  
% 7.23/1.51  ------ Global Options
% 7.23/1.51  
% 7.23/1.51  --schedule                              default
% 7.23/1.51  --add_important_lit                     false
% 7.23/1.51  --prop_solver_per_cl                    1000
% 7.23/1.51  --min_unsat_core                        false
% 7.23/1.51  --soft_assumptions                      false
% 7.23/1.51  --soft_lemma_size                       3
% 7.23/1.51  --prop_impl_unit_size                   0
% 7.23/1.51  --prop_impl_unit                        []
% 7.23/1.51  --share_sel_clauses                     true
% 7.23/1.51  --reset_solvers                         false
% 7.23/1.51  --bc_imp_inh                            [conj_cone]
% 7.23/1.51  --conj_cone_tolerance                   3.
% 7.23/1.51  --extra_neg_conj                        none
% 7.23/1.51  --large_theory_mode                     true
% 7.23/1.51  --prolific_symb_bound                   200
% 7.23/1.51  --lt_threshold                          2000
% 7.23/1.51  --clause_weak_htbl                      true
% 7.23/1.51  --gc_record_bc_elim                     false
% 7.23/1.51  
% 7.23/1.51  ------ Preprocessing Options
% 7.23/1.51  
% 7.23/1.51  --preprocessing_flag                    true
% 7.23/1.51  --time_out_prep_mult                    0.1
% 7.23/1.51  --splitting_mode                        input
% 7.23/1.51  --splitting_grd                         true
% 7.23/1.51  --splitting_cvd                         false
% 7.23/1.51  --splitting_cvd_svl                     false
% 7.23/1.51  --splitting_nvd                         32
% 7.23/1.51  --sub_typing                            true
% 7.23/1.51  --prep_gs_sim                           true
% 7.23/1.51  --prep_unflatten                        true
% 7.23/1.51  --prep_res_sim                          true
% 7.23/1.51  --prep_upred                            true
% 7.23/1.51  --prep_sem_filter                       exhaustive
% 7.23/1.51  --prep_sem_filter_out                   false
% 7.23/1.51  --pred_elim                             true
% 7.23/1.51  --res_sim_input                         true
% 7.23/1.51  --eq_ax_congr_red                       true
% 7.23/1.51  --pure_diseq_elim                       true
% 7.23/1.51  --brand_transform                       false
% 7.23/1.51  --non_eq_to_eq                          false
% 7.23/1.51  --prep_def_merge                        true
% 7.23/1.51  --prep_def_merge_prop_impl              false
% 7.23/1.51  --prep_def_merge_mbd                    true
% 7.23/1.51  --prep_def_merge_tr_red                 false
% 7.23/1.51  --prep_def_merge_tr_cl                  false
% 7.23/1.51  --smt_preprocessing                     true
% 7.23/1.51  --smt_ac_axioms                         fast
% 7.23/1.51  --preprocessed_out                      false
% 7.23/1.51  --preprocessed_stats                    false
% 7.23/1.51  
% 7.23/1.51  ------ Abstraction refinement Options
% 7.23/1.51  
% 7.23/1.51  --abstr_ref                             []
% 7.23/1.51  --abstr_ref_prep                        false
% 7.23/1.51  --abstr_ref_until_sat                   false
% 7.23/1.51  --abstr_ref_sig_restrict                funpre
% 7.23/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.23/1.51  --abstr_ref_under                       []
% 7.23/1.51  
% 7.23/1.51  ------ SAT Options
% 7.23/1.51  
% 7.23/1.51  --sat_mode                              false
% 7.23/1.51  --sat_fm_restart_options                ""
% 7.23/1.51  --sat_gr_def                            false
% 7.23/1.51  --sat_epr_types                         true
% 7.23/1.51  --sat_non_cyclic_types                  false
% 7.23/1.51  --sat_finite_models                     false
% 7.23/1.51  --sat_fm_lemmas                         false
% 7.23/1.51  --sat_fm_prep                           false
% 7.23/1.51  --sat_fm_uc_incr                        true
% 7.23/1.51  --sat_out_model                         small
% 7.23/1.51  --sat_out_clauses                       false
% 7.23/1.51  
% 7.23/1.51  ------ QBF Options
% 7.23/1.51  
% 7.23/1.51  --qbf_mode                              false
% 7.23/1.51  --qbf_elim_univ                         false
% 7.23/1.51  --qbf_dom_inst                          none
% 7.23/1.51  --qbf_dom_pre_inst                      false
% 7.23/1.51  --qbf_sk_in                             false
% 7.23/1.51  --qbf_pred_elim                         true
% 7.23/1.51  --qbf_split                             512
% 7.23/1.51  
% 7.23/1.51  ------ BMC1 Options
% 7.23/1.51  
% 7.23/1.51  --bmc1_incremental                      false
% 7.23/1.51  --bmc1_axioms                           reachable_all
% 7.23/1.51  --bmc1_min_bound                        0
% 7.23/1.51  --bmc1_max_bound                        -1
% 7.23/1.51  --bmc1_max_bound_default                -1
% 7.23/1.51  --bmc1_symbol_reachability              true
% 7.23/1.51  --bmc1_property_lemmas                  false
% 7.23/1.51  --bmc1_k_induction                      false
% 7.23/1.51  --bmc1_non_equiv_states                 false
% 7.23/1.51  --bmc1_deadlock                         false
% 7.23/1.51  --bmc1_ucm                              false
% 7.23/1.51  --bmc1_add_unsat_core                   none
% 7.23/1.51  --bmc1_unsat_core_children              false
% 7.23/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.23/1.51  --bmc1_out_stat                         full
% 7.23/1.51  --bmc1_ground_init                      false
% 7.23/1.51  --bmc1_pre_inst_next_state              false
% 7.23/1.51  --bmc1_pre_inst_state                   false
% 7.23/1.51  --bmc1_pre_inst_reach_state             false
% 7.23/1.51  --bmc1_out_unsat_core                   false
% 7.23/1.51  --bmc1_aig_witness_out                  false
% 7.23/1.51  --bmc1_verbose                          false
% 7.23/1.51  --bmc1_dump_clauses_tptp                false
% 7.23/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.23/1.51  --bmc1_dump_file                        -
% 7.23/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.23/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.23/1.51  --bmc1_ucm_extend_mode                  1
% 7.23/1.51  --bmc1_ucm_init_mode                    2
% 7.23/1.51  --bmc1_ucm_cone_mode                    none
% 7.23/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.23/1.51  --bmc1_ucm_relax_model                  4
% 7.23/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.23/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.23/1.51  --bmc1_ucm_layered_model                none
% 7.23/1.51  --bmc1_ucm_max_lemma_size               10
% 7.23/1.51  
% 7.23/1.51  ------ AIG Options
% 7.23/1.51  
% 7.23/1.51  --aig_mode                              false
% 7.23/1.51  
% 7.23/1.51  ------ Instantiation Options
% 7.23/1.51  
% 7.23/1.51  --instantiation_flag                    true
% 7.23/1.51  --inst_sos_flag                         false
% 7.23/1.51  --inst_sos_phase                        true
% 7.23/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.23/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.23/1.51  --inst_lit_sel_side                     num_symb
% 7.23/1.51  --inst_solver_per_active                1400
% 7.23/1.51  --inst_solver_calls_frac                1.
% 7.23/1.51  --inst_passive_queue_type               priority_queues
% 7.23/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.23/1.51  --inst_passive_queues_freq              [25;2]
% 7.23/1.51  --inst_dismatching                      true
% 7.23/1.51  --inst_eager_unprocessed_to_passive     true
% 7.23/1.51  --inst_prop_sim_given                   true
% 7.23/1.51  --inst_prop_sim_new                     false
% 7.23/1.51  --inst_subs_new                         false
% 7.23/1.51  --inst_eq_res_simp                      false
% 7.23/1.51  --inst_subs_given                       false
% 7.23/1.51  --inst_orphan_elimination               true
% 7.23/1.51  --inst_learning_loop_flag               true
% 7.23/1.51  --inst_learning_start                   3000
% 7.23/1.51  --inst_learning_factor                  2
% 7.23/1.51  --inst_start_prop_sim_after_learn       3
% 7.23/1.51  --inst_sel_renew                        solver
% 7.23/1.51  --inst_lit_activity_flag                true
% 7.23/1.51  --inst_restr_to_given                   false
% 7.23/1.51  --inst_activity_threshold               500
% 7.23/1.51  --inst_out_proof                        true
% 7.23/1.51  
% 7.23/1.51  ------ Resolution Options
% 7.23/1.51  
% 7.23/1.51  --resolution_flag                       true
% 7.23/1.51  --res_lit_sel                           adaptive
% 7.23/1.51  --res_lit_sel_side                      none
% 7.23/1.51  --res_ordering                          kbo
% 7.23/1.51  --res_to_prop_solver                    active
% 7.23/1.51  --res_prop_simpl_new                    false
% 7.23/1.51  --res_prop_simpl_given                  true
% 7.23/1.51  --res_passive_queue_type                priority_queues
% 7.23/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.23/1.51  --res_passive_queues_freq               [15;5]
% 7.23/1.51  --res_forward_subs                      full
% 7.23/1.51  --res_backward_subs                     full
% 7.23/1.51  --res_forward_subs_resolution           true
% 7.23/1.51  --res_backward_subs_resolution          true
% 7.23/1.51  --res_orphan_elimination                true
% 7.23/1.51  --res_time_limit                        2.
% 7.23/1.51  --res_out_proof                         true
% 7.23/1.51  
% 7.23/1.51  ------ Superposition Options
% 7.23/1.51  
% 7.23/1.51  --superposition_flag                    true
% 7.23/1.51  --sup_passive_queue_type                priority_queues
% 7.23/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.23/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.23/1.51  --demod_completeness_check              fast
% 7.23/1.51  --demod_use_ground                      true
% 7.23/1.51  --sup_to_prop_solver                    passive
% 7.23/1.51  --sup_prop_simpl_new                    true
% 7.23/1.51  --sup_prop_simpl_given                  true
% 7.23/1.51  --sup_fun_splitting                     false
% 7.23/1.51  --sup_smt_interval                      50000
% 7.23/1.51  
% 7.23/1.51  ------ Superposition Simplification Setup
% 7.23/1.51  
% 7.23/1.51  --sup_indices_passive                   []
% 7.23/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.23/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.23/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.23/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.23/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.23/1.51  --sup_full_bw                           [BwDemod]
% 7.23/1.51  --sup_immed_triv                        [TrivRules]
% 7.23/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.23/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.23/1.51  --sup_immed_bw_main                     []
% 7.23/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.23/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.23/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.23/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.23/1.51  
% 7.23/1.51  ------ Combination Options
% 7.23/1.51  
% 7.23/1.51  --comb_res_mult                         3
% 7.23/1.51  --comb_sup_mult                         2
% 7.23/1.51  --comb_inst_mult                        10
% 7.23/1.51  
% 7.23/1.51  ------ Debug Options
% 7.23/1.51  
% 7.23/1.51  --dbg_backtrace                         false
% 7.23/1.51  --dbg_dump_prop_clauses                 false
% 7.23/1.51  --dbg_dump_prop_clauses_file            -
% 7.23/1.51  --dbg_out_stat                          false
% 7.23/1.51  ------ Parsing...
% 7.23/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.23/1.51  
% 7.23/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.23/1.51  
% 7.23/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.23/1.51  
% 7.23/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.23/1.51  ------ Proving...
% 7.23/1.51  ------ Problem Properties 
% 7.23/1.51  
% 7.23/1.51  
% 7.23/1.51  clauses                                 24
% 7.23/1.51  conjectures                             4
% 7.23/1.51  EPR                                     4
% 7.23/1.51  Horn                                    16
% 7.23/1.51  unary                                   6
% 7.23/1.51  binary                                  9
% 7.23/1.51  lits                                    52
% 7.23/1.51  lits eq                                 17
% 7.23/1.51  fd_pure                                 0
% 7.23/1.51  fd_pseudo                               0
% 7.23/1.51  fd_cond                                 1
% 7.23/1.51  fd_pseudo_cond                          6
% 7.23/1.51  AC symbols                              0
% 7.23/1.51  
% 7.23/1.51  ------ Schedule dynamic 5 is on 
% 7.23/1.51  
% 7.23/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.23/1.51  
% 7.23/1.51  
% 7.23/1.51  ------ 
% 7.23/1.51  Current options:
% 7.23/1.51  ------ 
% 7.23/1.51  
% 7.23/1.51  ------ Input Options
% 7.23/1.51  
% 7.23/1.51  --out_options                           all
% 7.23/1.51  --tptp_safe_out                         true
% 7.23/1.51  --problem_path                          ""
% 7.23/1.51  --include_path                          ""
% 7.23/1.51  --clausifier                            res/vclausify_rel
% 7.23/1.51  --clausifier_options                    --mode clausify
% 7.23/1.51  --stdin                                 false
% 7.23/1.51  --stats_out                             all
% 7.23/1.51  
% 7.23/1.51  ------ General Options
% 7.23/1.51  
% 7.23/1.51  --fof                                   false
% 7.23/1.51  --time_out_real                         305.
% 7.23/1.51  --time_out_virtual                      -1.
% 7.23/1.51  --symbol_type_check                     false
% 7.23/1.51  --clausify_out                          false
% 7.23/1.51  --sig_cnt_out                           false
% 7.23/1.51  --trig_cnt_out                          false
% 7.23/1.51  --trig_cnt_out_tolerance                1.
% 7.23/1.51  --trig_cnt_out_sk_spl                   false
% 7.23/1.51  --abstr_cl_out                          false
% 7.23/1.51  
% 7.23/1.51  ------ Global Options
% 7.23/1.51  
% 7.23/1.51  --schedule                              default
% 7.23/1.51  --add_important_lit                     false
% 7.23/1.51  --prop_solver_per_cl                    1000
% 7.23/1.51  --min_unsat_core                        false
% 7.23/1.51  --soft_assumptions                      false
% 7.23/1.51  --soft_lemma_size                       3
% 7.23/1.51  --prop_impl_unit_size                   0
% 7.23/1.51  --prop_impl_unit                        []
% 7.23/1.51  --share_sel_clauses                     true
% 7.23/1.51  --reset_solvers                         false
% 7.23/1.51  --bc_imp_inh                            [conj_cone]
% 7.23/1.51  --conj_cone_tolerance                   3.
% 7.23/1.51  --extra_neg_conj                        none
% 7.23/1.51  --large_theory_mode                     true
% 7.23/1.51  --prolific_symb_bound                   200
% 7.23/1.51  --lt_threshold                          2000
% 7.23/1.51  --clause_weak_htbl                      true
% 7.23/1.51  --gc_record_bc_elim                     false
% 7.23/1.51  
% 7.23/1.51  ------ Preprocessing Options
% 7.23/1.51  
% 7.23/1.51  --preprocessing_flag                    true
% 7.23/1.51  --time_out_prep_mult                    0.1
% 7.23/1.51  --splitting_mode                        input
% 7.23/1.51  --splitting_grd                         true
% 7.23/1.51  --splitting_cvd                         false
% 7.23/1.51  --splitting_cvd_svl                     false
% 7.23/1.51  --splitting_nvd                         32
% 7.23/1.51  --sub_typing                            true
% 7.23/1.51  --prep_gs_sim                           true
% 7.23/1.51  --prep_unflatten                        true
% 7.23/1.51  --prep_res_sim                          true
% 7.23/1.51  --prep_upred                            true
% 7.23/1.51  --prep_sem_filter                       exhaustive
% 7.23/1.51  --prep_sem_filter_out                   false
% 7.23/1.51  --pred_elim                             true
% 7.23/1.51  --res_sim_input                         true
% 7.23/1.51  --eq_ax_congr_red                       true
% 7.23/1.51  --pure_diseq_elim                       true
% 7.23/1.51  --brand_transform                       false
% 7.23/1.51  --non_eq_to_eq                          false
% 7.23/1.51  --prep_def_merge                        true
% 7.23/1.51  --prep_def_merge_prop_impl              false
% 7.23/1.51  --prep_def_merge_mbd                    true
% 7.23/1.51  --prep_def_merge_tr_red                 false
% 7.23/1.51  --prep_def_merge_tr_cl                  false
% 7.23/1.51  --smt_preprocessing                     true
% 7.23/1.51  --smt_ac_axioms                         fast
% 7.23/1.51  --preprocessed_out                      false
% 7.23/1.51  --preprocessed_stats                    false
% 7.23/1.51  
% 7.23/1.51  ------ Abstraction refinement Options
% 7.23/1.51  
% 7.23/1.51  --abstr_ref                             []
% 7.23/1.51  --abstr_ref_prep                        false
% 7.23/1.51  --abstr_ref_until_sat                   false
% 7.23/1.51  --abstr_ref_sig_restrict                funpre
% 7.23/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.23/1.51  --abstr_ref_under                       []
% 7.23/1.51  
% 7.23/1.51  ------ SAT Options
% 7.23/1.51  
% 7.23/1.51  --sat_mode                              false
% 7.23/1.51  --sat_fm_restart_options                ""
% 7.23/1.51  --sat_gr_def                            false
% 7.23/1.51  --sat_epr_types                         true
% 7.23/1.51  --sat_non_cyclic_types                  false
% 7.23/1.51  --sat_finite_models                     false
% 7.23/1.51  --sat_fm_lemmas                         false
% 7.23/1.51  --sat_fm_prep                           false
% 7.23/1.51  --sat_fm_uc_incr                        true
% 7.23/1.51  --sat_out_model                         small
% 7.23/1.51  --sat_out_clauses                       false
% 7.23/1.51  
% 7.23/1.51  ------ QBF Options
% 7.23/1.51  
% 7.23/1.51  --qbf_mode                              false
% 7.23/1.51  --qbf_elim_univ                         false
% 7.23/1.51  --qbf_dom_inst                          none
% 7.23/1.51  --qbf_dom_pre_inst                      false
% 7.23/1.51  --qbf_sk_in                             false
% 7.23/1.51  --qbf_pred_elim                         true
% 7.23/1.51  --qbf_split                             512
% 7.23/1.51  
% 7.23/1.51  ------ BMC1 Options
% 7.23/1.51  
% 7.23/1.51  --bmc1_incremental                      false
% 7.23/1.51  --bmc1_axioms                           reachable_all
% 7.23/1.51  --bmc1_min_bound                        0
% 7.23/1.51  --bmc1_max_bound                        -1
% 7.23/1.51  --bmc1_max_bound_default                -1
% 7.23/1.51  --bmc1_symbol_reachability              true
% 7.23/1.51  --bmc1_property_lemmas                  false
% 7.23/1.51  --bmc1_k_induction                      false
% 7.23/1.51  --bmc1_non_equiv_states                 false
% 7.23/1.51  --bmc1_deadlock                         false
% 7.23/1.51  --bmc1_ucm                              false
% 7.23/1.51  --bmc1_add_unsat_core                   none
% 7.23/1.51  --bmc1_unsat_core_children              false
% 7.23/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.23/1.51  --bmc1_out_stat                         full
% 7.23/1.51  --bmc1_ground_init                      false
% 7.23/1.51  --bmc1_pre_inst_next_state              false
% 7.23/1.51  --bmc1_pre_inst_state                   false
% 7.23/1.51  --bmc1_pre_inst_reach_state             false
% 7.23/1.51  --bmc1_out_unsat_core                   false
% 7.23/1.51  --bmc1_aig_witness_out                  false
% 7.23/1.51  --bmc1_verbose                          false
% 7.23/1.51  --bmc1_dump_clauses_tptp                false
% 7.23/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.23/1.51  --bmc1_dump_file                        -
% 7.23/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.23/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.23/1.51  --bmc1_ucm_extend_mode                  1
% 7.23/1.51  --bmc1_ucm_init_mode                    2
% 7.23/1.51  --bmc1_ucm_cone_mode                    none
% 7.23/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.23/1.51  --bmc1_ucm_relax_model                  4
% 7.23/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.23/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.23/1.51  --bmc1_ucm_layered_model                none
% 7.23/1.51  --bmc1_ucm_max_lemma_size               10
% 7.23/1.51  
% 7.23/1.51  ------ AIG Options
% 7.23/1.51  
% 7.23/1.51  --aig_mode                              false
% 7.23/1.51  
% 7.23/1.51  ------ Instantiation Options
% 7.23/1.51  
% 7.23/1.51  --instantiation_flag                    true
% 7.23/1.51  --inst_sos_flag                         false
% 7.23/1.51  --inst_sos_phase                        true
% 7.23/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.23/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.23/1.51  --inst_lit_sel_side                     none
% 7.23/1.51  --inst_solver_per_active                1400
% 7.23/1.51  --inst_solver_calls_frac                1.
% 7.23/1.51  --inst_passive_queue_type               priority_queues
% 7.23/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.23/1.51  --inst_passive_queues_freq              [25;2]
% 7.23/1.51  --inst_dismatching                      true
% 7.23/1.51  --inst_eager_unprocessed_to_passive     true
% 7.23/1.51  --inst_prop_sim_given                   true
% 7.23/1.51  --inst_prop_sim_new                     false
% 7.23/1.51  --inst_subs_new                         false
% 7.23/1.51  --inst_eq_res_simp                      false
% 7.23/1.51  --inst_subs_given                       false
% 7.23/1.51  --inst_orphan_elimination               true
% 7.23/1.51  --inst_learning_loop_flag               true
% 7.23/1.51  --inst_learning_start                   3000
% 7.23/1.51  --inst_learning_factor                  2
% 7.23/1.51  --inst_start_prop_sim_after_learn       3
% 7.23/1.51  --inst_sel_renew                        solver
% 7.23/1.51  --inst_lit_activity_flag                true
% 7.23/1.51  --inst_restr_to_given                   false
% 7.23/1.51  --inst_activity_threshold               500
% 7.23/1.51  --inst_out_proof                        true
% 7.23/1.51  
% 7.23/1.51  ------ Resolution Options
% 7.23/1.51  
% 7.23/1.51  --resolution_flag                       false
% 7.23/1.51  --res_lit_sel                           adaptive
% 7.23/1.51  --res_lit_sel_side                      none
% 7.23/1.51  --res_ordering                          kbo
% 7.23/1.51  --res_to_prop_solver                    active
% 7.23/1.51  --res_prop_simpl_new                    false
% 7.23/1.51  --res_prop_simpl_given                  true
% 7.23/1.51  --res_passive_queue_type                priority_queues
% 7.23/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.23/1.51  --res_passive_queues_freq               [15;5]
% 7.23/1.51  --res_forward_subs                      full
% 7.23/1.51  --res_backward_subs                     full
% 7.23/1.51  --res_forward_subs_resolution           true
% 7.23/1.51  --res_backward_subs_resolution          true
% 7.23/1.51  --res_orphan_elimination                true
% 7.23/1.51  --res_time_limit                        2.
% 7.23/1.51  --res_out_proof                         true
% 7.23/1.51  
% 7.23/1.51  ------ Superposition Options
% 7.23/1.51  
% 7.23/1.51  --superposition_flag                    true
% 7.23/1.51  --sup_passive_queue_type                priority_queues
% 7.23/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.23/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.23/1.51  --demod_completeness_check              fast
% 7.23/1.51  --demod_use_ground                      true
% 7.23/1.51  --sup_to_prop_solver                    passive
% 7.23/1.51  --sup_prop_simpl_new                    true
% 7.23/1.51  --sup_prop_simpl_given                  true
% 7.23/1.51  --sup_fun_splitting                     false
% 7.23/1.51  --sup_smt_interval                      50000
% 7.23/1.51  
% 7.23/1.51  ------ Superposition Simplification Setup
% 7.23/1.51  
% 7.23/1.51  --sup_indices_passive                   []
% 7.23/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.23/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.23/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.23/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.23/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.23/1.51  --sup_full_bw                           [BwDemod]
% 7.23/1.51  --sup_immed_triv                        [TrivRules]
% 7.23/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.23/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.23/1.51  --sup_immed_bw_main                     []
% 7.23/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.23/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.23/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.23/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.23/1.51  
% 7.23/1.51  ------ Combination Options
% 7.23/1.51  
% 7.23/1.51  --comb_res_mult                         3
% 7.23/1.51  --comb_sup_mult                         2
% 7.23/1.51  --comb_inst_mult                        10
% 7.23/1.51  
% 7.23/1.51  ------ Debug Options
% 7.23/1.51  
% 7.23/1.51  --dbg_backtrace                         false
% 7.23/1.51  --dbg_dump_prop_clauses                 false
% 7.23/1.51  --dbg_dump_prop_clauses_file            -
% 7.23/1.51  --dbg_out_stat                          false
% 7.23/1.51  
% 7.23/1.51  
% 7.23/1.51  
% 7.23/1.51  
% 7.23/1.51  ------ Proving...
% 7.23/1.51  
% 7.23/1.51  
% 7.23/1.51  % SZS status Theorem for theBenchmark.p
% 7.23/1.51  
% 7.23/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.23/1.51  
% 7.23/1.51  fof(f4,axiom,(
% 7.23/1.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 7.23/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.51  
% 7.23/1.51  fof(f16,plain,(
% 7.23/1.51    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 7.23/1.51    inference(ennf_transformation,[],[f4])).
% 7.23/1.51  
% 7.23/1.51  fof(f27,plain,(
% 7.23/1.51    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 7.23/1.51    inference(nnf_transformation,[],[f16])).
% 7.23/1.51  
% 7.23/1.51  fof(f28,plain,(
% 7.23/1.51    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(sK2(X0,X1),X0)) & (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0))))),
% 7.23/1.51    introduced(choice_axiom,[])).
% 7.23/1.51  
% 7.23/1.51  fof(f29,plain,(
% 7.23/1.51    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(sK2(X0,X1),X0)) & (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0))))),
% 7.23/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).
% 7.23/1.51  
% 7.23/1.51  fof(f47,plain,(
% 7.23/1.51    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 7.23/1.51    inference(cnf_transformation,[],[f29])).
% 7.23/1.51  
% 7.23/1.51  fof(f6,axiom,(
% 7.23/1.51    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.23/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.51  
% 7.23/1.51  fof(f51,plain,(
% 7.23/1.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.23/1.51    inference(cnf_transformation,[],[f6])).
% 7.23/1.51  
% 7.23/1.51  fof(f2,axiom,(
% 7.23/1.51    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.23/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.51  
% 7.23/1.51  fof(f22,plain,(
% 7.23/1.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.23/1.51    inference(nnf_transformation,[],[f2])).
% 7.23/1.51  
% 7.23/1.51  fof(f23,plain,(
% 7.23/1.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.23/1.51    inference(flattening,[],[f22])).
% 7.23/1.51  
% 7.23/1.51  fof(f24,plain,(
% 7.23/1.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.23/1.51    inference(rectify,[],[f23])).
% 7.23/1.51  
% 7.23/1.51  fof(f25,plain,(
% 7.23/1.51    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 7.23/1.51    introduced(choice_axiom,[])).
% 7.23/1.51  
% 7.23/1.51  fof(f26,plain,(
% 7.23/1.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.23/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f25])).
% 7.23/1.51  
% 7.23/1.51  fof(f41,plain,(
% 7.23/1.51    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.23/1.51    inference(cnf_transformation,[],[f26])).
% 7.23/1.51  
% 7.23/1.51  fof(f63,plain,(
% 7.23/1.51    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 7.23/1.51    inference(equality_resolution,[],[f41])).
% 7.23/1.51  
% 7.23/1.51  fof(f1,axiom,(
% 7.23/1.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.23/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.51  
% 7.23/1.51  fof(f12,plain,(
% 7.23/1.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 7.23/1.51    inference(unused_predicate_definition_removal,[],[f1])).
% 7.23/1.51  
% 7.23/1.51  fof(f13,plain,(
% 7.23/1.51    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 7.23/1.51    inference(ennf_transformation,[],[f12])).
% 7.23/1.51  
% 7.23/1.51  fof(f20,plain,(
% 7.23/1.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.23/1.51    introduced(choice_axiom,[])).
% 7.23/1.51  
% 7.23/1.51  fof(f21,plain,(
% 7.23/1.51    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.23/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f20])).
% 7.23/1.51  
% 7.23/1.51  fof(f38,plain,(
% 7.23/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.23/1.51    inference(cnf_transformation,[],[f21])).
% 7.23/1.51  
% 7.23/1.51  fof(f7,axiom,(
% 7.23/1.51    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 7.23/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.51  
% 7.23/1.51  fof(f32,plain,(
% 7.23/1.51    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 7.23/1.51    inference(nnf_transformation,[],[f7])).
% 7.23/1.51  
% 7.23/1.51  fof(f33,plain,(
% 7.23/1.51    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 7.23/1.51    inference(flattening,[],[f32])).
% 7.23/1.51  
% 7.23/1.51  fof(f54,plain,(
% 7.23/1.51    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 7.23/1.51    inference(cnf_transformation,[],[f33])).
% 7.23/1.51  
% 7.23/1.51  fof(f9,conjecture,(
% 7.23/1.51    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.23/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.51  
% 7.23/1.51  fof(f10,negated_conjecture,(
% 7.23/1.51    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.23/1.51    inference(negated_conjecture,[],[f9])).
% 7.23/1.51  
% 7.23/1.51  fof(f18,plain,(
% 7.23/1.51    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 7.23/1.51    inference(ennf_transformation,[],[f10])).
% 7.23/1.51  
% 7.23/1.51  fof(f19,plain,(
% 7.23/1.51    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 7.23/1.51    inference(flattening,[],[f18])).
% 7.23/1.51  
% 7.23/1.51  fof(f36,plain,(
% 7.23/1.51    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)) => ((sK5 != sK7 | sK4 != sK6) & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK6,sK7))),
% 7.23/1.51    introduced(choice_axiom,[])).
% 7.23/1.51  
% 7.23/1.51  fof(f37,plain,(
% 7.23/1.51    (sK5 != sK7 | sK4 != sK6) & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK6,sK7)),
% 7.23/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f19,f36])).
% 7.23/1.51  
% 7.23/1.51  fof(f58,plain,(
% 7.23/1.51    k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK6,sK7)),
% 7.23/1.51    inference(cnf_transformation,[],[f37])).
% 7.23/1.51  
% 7.23/1.51  fof(f53,plain,(
% 7.23/1.51    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 7.23/1.51    inference(cnf_transformation,[],[f33])).
% 7.23/1.51  
% 7.23/1.51  fof(f59,plain,(
% 7.23/1.51    k1_xboole_0 != sK4),
% 7.23/1.51    inference(cnf_transformation,[],[f37])).
% 7.23/1.51  
% 7.23/1.51  fof(f8,axiom,(
% 7.23/1.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.23/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.51  
% 7.23/1.51  fof(f34,plain,(
% 7.23/1.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.23/1.51    inference(nnf_transformation,[],[f8])).
% 7.23/1.51  
% 7.23/1.51  fof(f35,plain,(
% 7.23/1.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.23/1.51    inference(flattening,[],[f34])).
% 7.23/1.51  
% 7.23/1.51  fof(f55,plain,(
% 7.23/1.51    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 7.23/1.51    inference(cnf_transformation,[],[f35])).
% 7.23/1.51  
% 7.23/1.51  fof(f56,plain,(
% 7.23/1.51    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.23/1.51    inference(cnf_transformation,[],[f35])).
% 7.23/1.51  
% 7.23/1.51  fof(f66,plain,(
% 7.23/1.51    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.23/1.51    inference(equality_resolution,[],[f56])).
% 7.23/1.51  
% 7.23/1.51  fof(f3,axiom,(
% 7.23/1.51    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 7.23/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.51  
% 7.23/1.51  fof(f11,plain,(
% 7.23/1.51    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 7.23/1.51    inference(unused_predicate_definition_removal,[],[f3])).
% 7.23/1.51  
% 7.23/1.51  fof(f14,plain,(
% 7.23/1.51    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 7.23/1.51    inference(ennf_transformation,[],[f11])).
% 7.23/1.51  
% 7.23/1.51  fof(f15,plain,(
% 7.23/1.51    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 7.23/1.51    inference(flattening,[],[f14])).
% 7.23/1.51  
% 7.23/1.51  fof(f46,plain,(
% 7.23/1.51    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 7.23/1.51    inference(cnf_transformation,[],[f15])).
% 7.23/1.51  
% 7.23/1.51  fof(f5,axiom,(
% 7.23/1.51    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 7.23/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.51  
% 7.23/1.51  fof(f17,plain,(
% 7.23/1.51    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 7.23/1.51    inference(ennf_transformation,[],[f5])).
% 7.23/1.51  
% 7.23/1.51  fof(f30,plain,(
% 7.23/1.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) => (~r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK3(X0,X1),X1)))),
% 7.23/1.51    introduced(choice_axiom,[])).
% 7.23/1.51  
% 7.23/1.51  fof(f31,plain,(
% 7.23/1.51    ! [X0,X1] : ((~r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK3(X0,X1),X1)) | ~r2_xboole_0(X0,X1))),
% 7.23/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f30])).
% 7.23/1.51  
% 7.23/1.51  fof(f49,plain,(
% 7.23/1.51    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | ~r2_xboole_0(X0,X1)) )),
% 7.23/1.51    inference(cnf_transformation,[],[f31])).
% 7.23/1.51  
% 7.23/1.51  fof(f60,plain,(
% 7.23/1.51    k1_xboole_0 != sK5),
% 7.23/1.51    inference(cnf_transformation,[],[f37])).
% 7.23/1.51  
% 7.23/1.51  fof(f52,plain,(
% 7.23/1.51    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 7.23/1.51    inference(cnf_transformation,[],[f33])).
% 7.23/1.51  
% 7.23/1.51  fof(f39,plain,(
% 7.23/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.23/1.51    inference(cnf_transformation,[],[f21])).
% 7.23/1.51  
% 7.23/1.51  fof(f50,plain,(
% 7.23/1.51    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X0) | ~r2_xboole_0(X0,X1)) )),
% 7.23/1.51    inference(cnf_transformation,[],[f31])).
% 7.23/1.51  
% 7.23/1.51  fof(f61,plain,(
% 7.23/1.51    sK5 != sK7 | sK4 != sK6),
% 7.23/1.51    inference(cnf_transformation,[],[f37])).
% 7.23/1.51  
% 7.23/1.51  cnf(c_10,plain,
% 7.23/1.51      ( r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0) | X1 = X0 ),
% 7.23/1.51      inference(cnf_transformation,[],[f47]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_528,plain,
% 7.23/1.51      ( X0 = X1
% 7.23/1.51      | r2_hidden(sK2(X1,X0),X0) = iProver_top
% 7.23/1.51      | r2_hidden(sK2(X1,X0),X1) = iProver_top ),
% 7.23/1.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_13,plain,
% 7.23/1.51      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.23/1.51      inference(cnf_transformation,[],[f51]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_6,plain,
% 7.23/1.51      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 7.23/1.51      inference(cnf_transformation,[],[f63]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_532,plain,
% 7.23/1.51      ( r2_hidden(X0,X1) != iProver_top
% 7.23/1.51      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 7.23/1.51      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_1250,plain,
% 7.23/1.51      ( r2_hidden(X0,X1) != iProver_top
% 7.23/1.51      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.23/1.51      inference(superposition,[status(thm)],[c_13,c_532]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_1537,plain,
% 7.23/1.51      ( X0 = X1
% 7.23/1.51      | r2_hidden(sK2(X0,X1),X1) = iProver_top
% 7.23/1.51      | r2_hidden(sK2(X0,X1),k1_xboole_0) != iProver_top ),
% 7.23/1.51      inference(superposition,[status(thm)],[c_528,c_1250]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_3168,plain,
% 7.23/1.51      ( X0 = X1 | r2_hidden(sK2(X1,X0),k1_xboole_0) != iProver_top ),
% 7.23/1.51      inference(forward_subsumption_resolution,
% 7.23/1.51                [status(thm)],
% 7.23/1.51                [c_1537,c_1250]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_3170,plain,
% 7.23/1.51      ( k1_xboole_0 = X0
% 7.23/1.51      | r2_hidden(sK2(X0,k1_xboole_0),X0) = iProver_top ),
% 7.23/1.51      inference(superposition,[status(thm)],[c_528,c_3168]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_1,plain,
% 7.23/1.51      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.23/1.51      inference(cnf_transformation,[],[f38]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_537,plain,
% 7.23/1.51      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 7.23/1.51      | r1_tarski(X0,X1) = iProver_top ),
% 7.23/1.51      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_14,plain,
% 7.23/1.51      ( ~ r2_hidden(X0,X1)
% 7.23/1.51      | ~ r2_hidden(X2,X3)
% 7.23/1.51      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 7.23/1.51      inference(cnf_transformation,[],[f54]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_525,plain,
% 7.23/1.51      ( r2_hidden(X0,X1) != iProver_top
% 7.23/1.51      | r2_hidden(X2,X3) != iProver_top
% 7.23/1.51      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 7.23/1.51      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_23,negated_conjecture,
% 7.23/1.51      ( k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK6,sK7) ),
% 7.23/1.51      inference(cnf_transformation,[],[f58]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_15,plain,
% 7.23/1.51      ( r2_hidden(X0,X1)
% 7.23/1.51      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 7.23/1.51      inference(cnf_transformation,[],[f53]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_524,plain,
% 7.23/1.51      ( r2_hidden(X0,X1) = iProver_top
% 7.23/1.51      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 7.23/1.51      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_1359,plain,
% 7.23/1.51      ( r2_hidden(X0,sK7) = iProver_top
% 7.23/1.51      | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK4,sK5)) != iProver_top ),
% 7.23/1.51      inference(superposition,[status(thm)],[c_23,c_524]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_2160,plain,
% 7.23/1.51      ( r2_hidden(X0,sK4) != iProver_top
% 7.23/1.51      | r2_hidden(X1,sK7) = iProver_top
% 7.23/1.51      | r2_hidden(X1,sK5) != iProver_top ),
% 7.23/1.51      inference(superposition,[status(thm)],[c_525,c_1359]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_2730,plain,
% 7.23/1.51      ( r2_hidden(X0,sK7) = iProver_top
% 7.23/1.51      | r2_hidden(X0,sK5) != iProver_top
% 7.23/1.51      | r1_tarski(sK4,X1) = iProver_top ),
% 7.23/1.51      inference(superposition,[status(thm)],[c_537,c_2160]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_22,negated_conjecture,
% 7.23/1.51      ( k1_xboole_0 != sK4 ),
% 7.23/1.51      inference(cnf_transformation,[],[f59]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_19,plain,
% 7.23/1.51      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 7.23/1.51      | k1_xboole_0 = X1
% 7.23/1.51      | k1_xboole_0 = X0 ),
% 7.23/1.51      inference(cnf_transformation,[],[f55]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_24,plain,
% 7.23/1.51      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.23/1.51      | k1_xboole_0 = k1_xboole_0 ),
% 7.23/1.51      inference(instantiation,[status(thm)],[c_19]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_18,plain,
% 7.23/1.51      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.23/1.51      inference(cnf_transformation,[],[f66]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_25,plain,
% 7.23/1.51      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.23/1.51      inference(instantiation,[status(thm)],[c_18]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_261,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_693,plain,
% 7.23/1.51      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 7.23/1.51      inference(instantiation,[status(thm)],[c_261]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_694,plain,
% 7.23/1.51      ( sK4 != k1_xboole_0
% 7.23/1.51      | k1_xboole_0 = sK4
% 7.23/1.51      | k1_xboole_0 != k1_xboole_0 ),
% 7.23/1.51      inference(instantiation,[status(thm)],[c_693]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_1342,plain,
% 7.23/1.51      ( r2_hidden(sK0(X0,X1),k1_xboole_0) != iProver_top
% 7.23/1.51      | r1_tarski(X0,X1) = iProver_top ),
% 7.23/1.51      inference(superposition,[status(thm)],[c_537,c_1250]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_1849,plain,
% 7.23/1.51      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.23/1.51      inference(superposition,[status(thm)],[c_537,c_1342]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_8,plain,
% 7.23/1.51      ( r2_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | X1 = X0 ),
% 7.23/1.51      inference(cnf_transformation,[],[f46]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_530,plain,
% 7.23/1.51      ( X0 = X1
% 7.23/1.51      | r2_xboole_0(X1,X0) = iProver_top
% 7.23/1.51      | r1_tarski(X1,X0) != iProver_top ),
% 7.23/1.51      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_1853,plain,
% 7.23/1.51      ( k1_xboole_0 = X0 | r2_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 7.23/1.52      inference(superposition,[status(thm)],[c_1849,c_530]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_12,plain,
% 7.23/1.52      ( ~ r2_xboole_0(X0,X1) | r2_hidden(sK3(X0,X1),X1) ),
% 7.23/1.52      inference(cnf_transformation,[],[f49]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_526,plain,
% 7.23/1.52      ( r2_xboole_0(X0,X1) != iProver_top
% 7.23/1.52      | r2_hidden(sK3(X0,X1),X1) = iProver_top ),
% 7.23/1.52      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_2733,plain,
% 7.23/1.52      ( r2_xboole_0(X0,sK4) != iProver_top
% 7.23/1.52      | r2_hidden(X1,sK7) = iProver_top
% 7.23/1.52      | r2_hidden(X1,sK5) != iProver_top ),
% 7.23/1.52      inference(superposition,[status(thm)],[c_526,c_2160]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_3408,plain,
% 7.23/1.52      ( sK4 = k1_xboole_0
% 7.23/1.52      | r2_hidden(X0,sK7) = iProver_top
% 7.23/1.52      | r2_hidden(X0,sK5) != iProver_top ),
% 7.23/1.52      inference(superposition,[status(thm)],[c_1853,c_2733]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_3821,plain,
% 7.23/1.52      ( r2_hidden(X0,sK5) != iProver_top
% 7.23/1.52      | r2_hidden(X0,sK7) = iProver_top ),
% 7.23/1.52      inference(global_propositional_subsumption,
% 7.23/1.52                [status(thm)],
% 7.23/1.52                [c_2730,c_22,c_24,c_25,c_694,c_3408]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_3822,plain,
% 7.23/1.52      ( r2_hidden(X0,sK7) = iProver_top
% 7.23/1.52      | r2_hidden(X0,sK5) != iProver_top ),
% 7.23/1.52      inference(renaming,[status(thm)],[c_3821]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_4415,plain,
% 7.23/1.52      ( sK5 = k1_xboole_0
% 7.23/1.52      | r2_hidden(sK2(sK5,k1_xboole_0),sK7) = iProver_top ),
% 7.23/1.52      inference(superposition,[status(thm)],[c_3170,c_3822]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_21,negated_conjecture,
% 7.23/1.52      ( k1_xboole_0 != sK5 ),
% 7.23/1.52      inference(cnf_transformation,[],[f60]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_691,plain,
% 7.23/1.52      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 7.23/1.52      inference(instantiation,[status(thm)],[c_261]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_692,plain,
% 7.23/1.52      ( sK5 != k1_xboole_0
% 7.23/1.52      | k1_xboole_0 = sK5
% 7.23/1.52      | k1_xboole_0 != k1_xboole_0 ),
% 7.23/1.52      inference(instantiation,[status(thm)],[c_691]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_12806,plain,
% 7.23/1.52      ( r2_hidden(sK2(sK5,k1_xboole_0),sK7) = iProver_top ),
% 7.23/1.52      inference(global_propositional_subsumption,
% 7.23/1.52                [status(thm)],
% 7.23/1.52                [c_4415,c_21,c_24,c_25,c_692]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_2155,plain,
% 7.23/1.52      ( r2_hidden(X0,sK6) != iProver_top
% 7.23/1.52      | r2_hidden(X1,sK7) != iProver_top
% 7.23/1.52      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 7.23/1.52      inference(superposition,[status(thm)],[c_23,c_525]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_16,plain,
% 7.23/1.52      ( r2_hidden(X0,X1)
% 7.23/1.52      | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 7.23/1.52      inference(cnf_transformation,[],[f52]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_523,plain,
% 7.23/1.52      ( r2_hidden(X0,X1) = iProver_top
% 7.23/1.52      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
% 7.23/1.52      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_2591,plain,
% 7.23/1.52      ( r2_hidden(X0,sK6) != iProver_top
% 7.23/1.52      | r2_hidden(X0,sK4) = iProver_top
% 7.23/1.52      | r2_hidden(X1,sK7) != iProver_top ),
% 7.23/1.52      inference(superposition,[status(thm)],[c_2155,c_523]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_2944,plain,
% 7.23/1.52      ( r2_hidden(X0,sK7) != iProver_top
% 7.23/1.52      | r2_hidden(sK0(sK6,X1),sK4) = iProver_top
% 7.23/1.52      | r1_tarski(sK6,X1) = iProver_top ),
% 7.23/1.52      inference(superposition,[status(thm)],[c_537,c_2591]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_12823,plain,
% 7.23/1.52      ( r2_hidden(sK0(sK6,X0),sK4) = iProver_top
% 7.23/1.52      | r1_tarski(sK6,X0) = iProver_top ),
% 7.23/1.52      inference(superposition,[status(thm)],[c_12806,c_2944]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_0,plain,
% 7.23/1.52      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.23/1.52      inference(cnf_transformation,[],[f39]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_538,plain,
% 7.23/1.52      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 7.23/1.52      | r1_tarski(X0,X1) = iProver_top ),
% 7.23/1.52      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_15419,plain,
% 7.23/1.52      ( r1_tarski(sK6,sK4) = iProver_top ),
% 7.23/1.52      inference(superposition,[status(thm)],[c_12823,c_538]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_3832,plain,
% 7.23/1.52      ( r2_xboole_0(X0,sK5) != iProver_top
% 7.23/1.52      | r2_hidden(sK3(X0,sK5),sK7) = iProver_top ),
% 7.23/1.52      inference(superposition,[status(thm)],[c_526,c_3822]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_11,plain,
% 7.23/1.52      ( ~ r2_xboole_0(X0,X1) | ~ r2_hidden(sK3(X0,X1),X0) ),
% 7.23/1.52      inference(cnf_transformation,[],[f50]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_527,plain,
% 7.23/1.52      ( r2_xboole_0(X0,X1) != iProver_top
% 7.23/1.52      | r2_hidden(sK3(X0,X1),X0) != iProver_top ),
% 7.23/1.52      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_9434,plain,
% 7.23/1.52      ( r2_xboole_0(sK7,sK5) != iProver_top ),
% 7.23/1.52      inference(superposition,[status(thm)],[c_3832,c_527]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_872,plain,
% 7.23/1.52      ( r2_hidden(X0,sK6) = iProver_top
% 7.23/1.52      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK4,sK5)) != iProver_top ),
% 7.23/1.52      inference(superposition,[status(thm)],[c_23,c_523]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_2159,plain,
% 7.23/1.52      ( r2_hidden(X0,sK6) = iProver_top
% 7.23/1.52      | r2_hidden(X0,sK4) != iProver_top
% 7.23/1.52      | r2_hidden(X1,sK5) != iProver_top ),
% 7.23/1.52      inference(superposition,[status(thm)],[c_525,c_872]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_4417,plain,
% 7.23/1.52      ( sK4 = k1_xboole_0
% 7.23/1.52      | r2_hidden(X0,sK5) != iProver_top
% 7.23/1.52      | r2_hidden(sK2(sK4,k1_xboole_0),sK6) = iProver_top ),
% 7.23/1.52      inference(superposition,[status(thm)],[c_3170,c_2159]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_5008,plain,
% 7.23/1.52      ( r2_hidden(X0,sK5) != iProver_top
% 7.23/1.52      | r2_hidden(sK2(sK4,k1_xboole_0),sK6) = iProver_top ),
% 7.23/1.52      inference(global_propositional_subsumption,
% 7.23/1.52                [status(thm)],
% 7.23/1.52                [c_4417,c_22,c_24,c_25,c_694]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_5016,plain,
% 7.23/1.52      ( r2_hidden(sK2(sK4,k1_xboole_0),sK6) = iProver_top
% 7.23/1.52      | r1_tarski(sK5,X0) = iProver_top ),
% 7.23/1.52      inference(superposition,[status(thm)],[c_537,c_5008]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_5023,plain,
% 7.23/1.52      ( sK5 = k1_xboole_0
% 7.23/1.52      | r2_hidden(sK2(sK4,k1_xboole_0),sK6) = iProver_top ),
% 7.23/1.52      inference(superposition,[status(thm)],[c_3170,c_5008]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_7342,plain,
% 7.23/1.52      ( r2_hidden(sK2(sK4,k1_xboole_0),sK6) = iProver_top ),
% 7.23/1.52      inference(global_propositional_subsumption,
% 7.23/1.52                [status(thm)],
% 7.23/1.52                [c_5016,c_21,c_24,c_25,c_692,c_5023]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_2590,plain,
% 7.23/1.52      ( r2_hidden(X0,sK6) != iProver_top
% 7.23/1.52      | r2_hidden(X1,sK7) != iProver_top
% 7.23/1.52      | r2_hidden(X1,sK5) = iProver_top ),
% 7.23/1.52      inference(superposition,[status(thm)],[c_2155,c_524]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_7350,plain,
% 7.23/1.52      ( r2_hidden(X0,sK7) != iProver_top
% 7.23/1.52      | r2_hidden(X0,sK5) = iProver_top ),
% 7.23/1.52      inference(superposition,[status(thm)],[c_7342,c_2590]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_7771,plain,
% 7.23/1.52      ( r2_hidden(sK0(sK7,X0),sK5) = iProver_top
% 7.23/1.52      | r1_tarski(sK7,X0) = iProver_top ),
% 7.23/1.52      inference(superposition,[status(thm)],[c_537,c_7350]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_8658,plain,
% 7.23/1.52      ( r1_tarski(sK7,sK5) = iProver_top ),
% 7.23/1.52      inference(superposition,[status(thm)],[c_7771,c_538]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_2628,plain,
% 7.23/1.52      ( r2_xboole_0(X0,sK4) != iProver_top
% 7.23/1.52      | r2_hidden(X1,sK5) != iProver_top
% 7.23/1.52      | r2_hidden(sK3(X0,sK4),sK6) = iProver_top ),
% 7.23/1.52      inference(superposition,[status(thm)],[c_526,c_2159]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_3086,plain,
% 7.23/1.52      ( r2_xboole_0(X0,sK4) != iProver_top
% 7.23/1.52      | r2_hidden(sK3(X0,sK4),sK6) = iProver_top
% 7.23/1.52      | r1_tarski(sK5,X1) = iProver_top ),
% 7.23/1.52      inference(superposition,[status(thm)],[c_537,c_2628]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_4418,plain,
% 7.23/1.52      ( sK5 = k1_xboole_0
% 7.23/1.52      | r2_xboole_0(X0,sK4) != iProver_top
% 7.23/1.52      | r2_hidden(sK3(X0,sK4),sK6) = iProver_top ),
% 7.23/1.52      inference(superposition,[status(thm)],[c_3170,c_2628]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_8619,plain,
% 7.23/1.52      ( r2_hidden(sK3(X0,sK4),sK6) = iProver_top
% 7.23/1.52      | r2_xboole_0(X0,sK4) != iProver_top ),
% 7.23/1.52      inference(global_propositional_subsumption,
% 7.23/1.52                [status(thm)],
% 7.23/1.52                [c_3086,c_21,c_24,c_25,c_692,c_4418]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_8620,plain,
% 7.23/1.52      ( r2_xboole_0(X0,sK4) != iProver_top
% 7.23/1.52      | r2_hidden(sK3(X0,sK4),sK6) = iProver_top ),
% 7.23/1.52      inference(renaming,[status(thm)],[c_8619]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_8629,plain,
% 7.23/1.52      ( r2_xboole_0(sK6,sK4) != iProver_top ),
% 7.23/1.52      inference(superposition,[status(thm)],[c_8620,c_527]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_738,plain,
% 7.23/1.52      ( r2_xboole_0(sK7,sK5) | ~ r1_tarski(sK7,sK5) | sK5 = sK7 ),
% 7.23/1.52      inference(instantiation,[status(thm)],[c_8]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_739,plain,
% 7.23/1.52      ( sK5 = sK7
% 7.23/1.52      | r2_xboole_0(sK7,sK5) = iProver_top
% 7.23/1.52      | r1_tarski(sK7,sK5) != iProver_top ),
% 7.23/1.52      inference(predicate_to_equality,[status(thm)],[c_738]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_678,plain,
% 7.23/1.52      ( r2_xboole_0(sK6,sK4) | ~ r1_tarski(sK6,sK4) | sK4 = sK6 ),
% 7.23/1.52      inference(instantiation,[status(thm)],[c_8]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_679,plain,
% 7.23/1.52      ( sK4 = sK6
% 7.23/1.52      | r2_xboole_0(sK6,sK4) = iProver_top
% 7.23/1.52      | r1_tarski(sK6,sK4) != iProver_top ),
% 7.23/1.52      inference(predicate_to_equality,[status(thm)],[c_678]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(c_20,negated_conjecture,
% 7.23/1.52      ( sK4 != sK6 | sK5 != sK7 ),
% 7.23/1.52      inference(cnf_transformation,[],[f61]) ).
% 7.23/1.52  
% 7.23/1.52  cnf(contradiction,plain,
% 7.23/1.52      ( $false ),
% 7.23/1.52      inference(minisat,
% 7.23/1.52                [status(thm)],
% 7.23/1.52                [c_15419,c_9434,c_8658,c_8629,c_739,c_679,c_20]) ).
% 7.23/1.52  
% 7.23/1.52  
% 7.23/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 7.23/1.52  
% 7.23/1.52  ------                               Statistics
% 7.23/1.52  
% 7.23/1.52  ------ General
% 7.23/1.52  
% 7.23/1.52  abstr_ref_over_cycles:                  0
% 7.23/1.52  abstr_ref_under_cycles:                 0
% 7.23/1.52  gc_basic_clause_elim:                   0
% 7.23/1.52  forced_gc_time:                         0
% 7.23/1.52  parsing_time:                           0.012
% 7.23/1.52  unif_index_cands_time:                  0.
% 7.23/1.52  unif_index_add_time:                    0.
% 7.23/1.52  orderings_time:                         0.
% 7.23/1.52  out_proof_time:                         0.014
% 7.23/1.52  total_time:                             0.543
% 7.23/1.52  num_of_symbols:                         46
% 7.23/1.52  num_of_terms:                           11278
% 7.23/1.52  
% 7.23/1.52  ------ Preprocessing
% 7.23/1.52  
% 7.23/1.52  num_of_splits:                          0
% 7.23/1.52  num_of_split_atoms:                     0
% 7.23/1.52  num_of_reused_defs:                     0
% 7.23/1.52  num_eq_ax_congr_red:                    32
% 7.23/1.52  num_of_sem_filtered_clauses:            1
% 7.23/1.52  num_of_subtypes:                        0
% 7.23/1.52  monotx_restored_types:                  0
% 7.23/1.52  sat_num_of_epr_types:                   0
% 7.23/1.52  sat_num_of_non_cyclic_types:            0
% 7.23/1.52  sat_guarded_non_collapsed_types:        0
% 7.23/1.52  num_pure_diseq_elim:                    0
% 7.23/1.52  simp_replaced_by:                       0
% 7.23/1.52  res_preprocessed:                       83
% 7.23/1.52  prep_upred:                             0
% 7.23/1.52  prep_unflattend:                        0
% 7.23/1.52  smt_new_axioms:                         0
% 7.23/1.52  pred_elim_cands:                        3
% 7.23/1.52  pred_elim:                              0
% 7.23/1.52  pred_elim_cl:                           0
% 7.23/1.52  pred_elim_cycles:                       2
% 7.23/1.52  merged_defs:                            0
% 7.23/1.52  merged_defs_ncl:                        0
% 7.23/1.52  bin_hyper_res:                          0
% 7.23/1.52  prep_cycles:                            3
% 7.23/1.52  pred_elim_time:                         0.001
% 7.23/1.52  splitting_time:                         0.
% 7.23/1.52  sem_filter_time:                        0.
% 7.23/1.52  monotx_time:                            0.001
% 7.23/1.52  subtype_inf_time:                       0.
% 7.23/1.52  
% 7.23/1.52  ------ Problem properties
% 7.23/1.52  
% 7.23/1.52  clauses:                                24
% 7.23/1.52  conjectures:                            4
% 7.23/1.52  epr:                                    4
% 7.23/1.52  horn:                                   16
% 7.23/1.52  ground:                                 4
% 7.23/1.52  unary:                                  6
% 7.23/1.52  binary:                                 9
% 7.23/1.52  lits:                                   52
% 7.23/1.52  lits_eq:                                17
% 7.23/1.52  fd_pure:                                0
% 7.23/1.52  fd_pseudo:                              0
% 7.23/1.52  fd_cond:                                1
% 7.23/1.52  fd_pseudo_cond:                         6
% 7.23/1.52  ac_symbols:                             0
% 7.23/1.52  
% 7.23/1.52  ------ Propositional Solver
% 7.23/1.52  
% 7.23/1.52  prop_solver_calls:                      26
% 7.23/1.52  prop_fast_solver_calls:                 888
% 7.23/1.52  smt_solver_calls:                       0
% 7.23/1.52  smt_fast_solver_calls:                  0
% 7.23/1.52  prop_num_of_clauses:                    5924
% 7.23/1.52  prop_preprocess_simplified:             10915
% 7.23/1.52  prop_fo_subsumed:                       39
% 7.23/1.52  prop_solver_time:                       0.
% 7.23/1.52  smt_solver_time:                        0.
% 7.23/1.52  smt_fast_solver_time:                   0.
% 7.23/1.52  prop_fast_solver_time:                  0.
% 7.23/1.52  prop_unsat_core_time:                   0.
% 7.23/1.52  
% 7.23/1.52  ------ QBF
% 7.23/1.52  
% 7.23/1.52  qbf_q_res:                              0
% 7.23/1.52  qbf_num_tautologies:                    0
% 7.23/1.52  qbf_prep_cycles:                        0
% 7.23/1.52  
% 7.23/1.52  ------ BMC1
% 7.23/1.52  
% 7.23/1.52  bmc1_current_bound:                     -1
% 7.23/1.52  bmc1_last_solved_bound:                 -1
% 7.23/1.52  bmc1_unsat_core_size:                   -1
% 7.23/1.52  bmc1_unsat_core_parents_size:           -1
% 7.23/1.52  bmc1_merge_next_fun:                    0
% 7.23/1.52  bmc1_unsat_core_clauses_time:           0.
% 7.23/1.52  
% 7.23/1.52  ------ Instantiation
% 7.23/1.52  
% 7.23/1.52  inst_num_of_clauses:                    1478
% 7.23/1.52  inst_num_in_passive:                    567
% 7.23/1.52  inst_num_in_active:                     482
% 7.23/1.52  inst_num_in_unprocessed:                429
% 7.23/1.52  inst_num_of_loops:                      760
% 7.23/1.52  inst_num_of_learning_restarts:          0
% 7.23/1.52  inst_num_moves_active_passive:          276
% 7.23/1.52  inst_lit_activity:                      0
% 7.23/1.52  inst_lit_activity_moves:                0
% 7.23/1.52  inst_num_tautologies:                   0
% 7.23/1.52  inst_num_prop_implied:                  0
% 7.23/1.52  inst_num_existing_simplified:           0
% 7.23/1.52  inst_num_eq_res_simplified:             0
% 7.23/1.52  inst_num_child_elim:                    0
% 7.23/1.52  inst_num_of_dismatching_blockings:      177
% 7.23/1.52  inst_num_of_non_proper_insts:           717
% 7.23/1.52  inst_num_of_duplicates:                 0
% 7.23/1.52  inst_inst_num_from_inst_to_res:         0
% 7.23/1.52  inst_dismatching_checking_time:         0.
% 7.23/1.52  
% 7.23/1.52  ------ Resolution
% 7.23/1.52  
% 7.23/1.52  res_num_of_clauses:                     0
% 7.23/1.52  res_num_in_passive:                     0
% 7.23/1.52  res_num_in_active:                      0
% 7.23/1.52  res_num_of_loops:                       86
% 7.23/1.52  res_forward_subset_subsumed:            30
% 7.23/1.52  res_backward_subset_subsumed:           0
% 7.23/1.52  res_forward_subsumed:                   0
% 7.23/1.52  res_backward_subsumed:                  0
% 7.23/1.52  res_forward_subsumption_resolution:     0
% 7.23/1.52  res_backward_subsumption_resolution:    0
% 7.23/1.52  res_clause_to_clause_subsumption:       3535
% 7.23/1.52  res_orphan_elimination:                 0
% 7.23/1.52  res_tautology_del:                      56
% 7.23/1.52  res_num_eq_res_simplified:              0
% 7.23/1.52  res_num_sel_changes:                    0
% 7.23/1.52  res_moves_from_active_to_pass:          0
% 7.23/1.52  
% 7.23/1.52  ------ Superposition
% 7.23/1.52  
% 7.23/1.52  sup_time_total:                         0.
% 7.23/1.52  sup_time_generating:                    0.
% 7.23/1.52  sup_time_sim_full:                      0.
% 7.23/1.52  sup_time_sim_immed:                     0.
% 7.23/1.52  
% 7.23/1.52  sup_num_of_clauses:                     608
% 7.23/1.52  sup_num_in_active:                      142
% 7.23/1.52  sup_num_in_passive:                     466
% 7.23/1.52  sup_num_of_loops:                       150
% 7.23/1.52  sup_fw_superposition:                   565
% 7.23/1.52  sup_bw_superposition:                   636
% 7.23/1.52  sup_immediate_simplified:               236
% 7.23/1.52  sup_given_eliminated:                   6
% 7.23/1.52  comparisons_done:                       0
% 7.23/1.52  comparisons_avoided:                    0
% 7.23/1.52  
% 7.23/1.52  ------ Simplifications
% 7.23/1.52  
% 7.23/1.52  
% 7.23/1.52  sim_fw_subset_subsumed:                 112
% 7.23/1.52  sim_bw_subset_subsumed:                 61
% 7.23/1.52  sim_fw_subsumed:                        111
% 7.23/1.52  sim_bw_subsumed:                        34
% 7.23/1.52  sim_fw_subsumption_res:                 7
% 7.23/1.52  sim_bw_subsumption_res:                 0
% 7.23/1.52  sim_tautology_del:                      14
% 7.23/1.52  sim_eq_tautology_del:                   10
% 7.23/1.52  sim_eq_res_simp:                        1
% 7.23/1.52  sim_fw_demodulated:                     9
% 7.23/1.52  sim_bw_demodulated:                     8
% 7.23/1.52  sim_light_normalised:                   4
% 7.23/1.52  sim_joinable_taut:                      0
% 7.23/1.52  sim_joinable_simp:                      0
% 7.23/1.52  sim_ac_normalised:                      0
% 7.23/1.52  sim_smt_subsumption:                    0
% 7.23/1.52  
%------------------------------------------------------------------------------
