%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:10 EST 2020

% Result     : Theorem 55.39s
% Output     : CNFRefutation 55.39s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 626 expanded)
%              Number of clauses        :   83 ( 227 expanded)
%              Number of leaves         :   12 ( 132 expanded)
%              Depth                    :   27
%              Number of atoms          :  419 (3231 expanded)
%              Number of equality atoms :  196 ( 661 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   3 average)
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

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f12])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f14])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ r1_tarski(X1,X2)
          & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
            | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X1,X2)
      & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 )
   => ( ~ r1_tarski(sK4,sK5)
      & ( r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK3,sK5))
        | r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK5,sK3)) )
      & k1_xboole_0 != sK3 ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ~ r1_tarski(sK4,sK5)
    & ( r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK3,sK5))
      | r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK5,sK3)) )
    & k1_xboole_0 != sK3 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f11,f25])).

fof(f44,plain,
    ( r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK3,sK5))
    | r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK5,sK3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f23])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f43,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f16])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f19])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f21])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f45,plain,(
    ~ r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f26])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_566,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK3,sK5))
    | r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK5,sK3)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_550,plain,
    ( r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK3,sK5)) = iProver_top
    | r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK5,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_554,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_565,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2148,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),X4) = iProver_top
    | r1_tarski(k2_zfmisc_1(X3,X1),X4) != iProver_top ),
    inference(superposition,[status(thm)],[c_554,c_565])).

cnf(c_6685,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X1,sK4) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK3,sK5)) = iProver_top
    | r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK5,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_550,c_2148])).

cnf(c_14,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_553,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6916,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X1,sK5) = iProver_top
    | r2_hidden(X1,sK4) != iProver_top
    | r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK5,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6685,c_553])).

cnf(c_6944,plain,
    ( r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK5,sK3)) = iProver_top
    | r1_tarski(sK3,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_566,c_6916])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_249,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_599,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_249])).

cnf(c_646,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_599])).

cnf(c_248,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_964,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_248])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_562,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_12,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_555,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_558,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1983,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_555,c_558])).

cnf(c_2213,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_562,c_1983])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | ~ r2_hidden(sK1(X0,X1,X2),X0)
    | ~ r2_hidden(sK1(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_49,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X0) != iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK1(X0,X1,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2217,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_562,c_1983])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_563,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2242,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X1) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_563,c_1983])).

cnf(c_7132,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2213,c_49,c_2217,c_2242])).

cnf(c_7139,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = X1
    | r2_hidden(sK1(k1_xboole_0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_562,c_7132])).

cnf(c_7236,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = sK3
    | r2_hidden(X1,sK5) = iProver_top
    | r2_hidden(X1,sK4) != iProver_top
    | r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK5,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7139,c_6916])).

cnf(c_7235,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7139,c_7132])).

cnf(c_7337,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK5,sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7236,c_7235])).

cnf(c_7478,plain,
    ( r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK5,sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6944,c_18,c_646,c_964,c_7337])).

cnf(c_7479,plain,
    ( r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK5,sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_7478])).

cnf(c_7484,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X1,sK5) = iProver_top
    | r2_hidden(X1,sK4) != iProver_top
    | r2_hidden(X2,sK4) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(sK5,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7479,c_2148])).

cnf(c_15,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_552,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_176966,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X1,sK5) = iProver_top
    | r2_hidden(X2,sK5) = iProver_top
    | r2_hidden(X2,sK4) != iProver_top
    | r2_hidden(X1,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7484,c_552])).

cnf(c_177025,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X1,sK5) = iProver_top
    | r2_hidden(X1,sK4) != iProver_top
    | r2_hidden(sK0(sK4,X2),sK5) = iProver_top
    | r1_tarski(sK4,X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_566,c_176966])).

cnf(c_178008,plain,
    ( r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(sK0(sK4,X1),sK5) = iProver_top
    | r1_tarski(sK3,X2) = iProver_top
    | r1_tarski(sK4,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_566,c_177025])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_567,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_178553,plain,
    ( r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r1_tarski(sK3,X1) = iProver_top
    | r1_tarski(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_178008,c_567])).

cnf(c_16,negated_conjecture,
    ( ~ r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_20,plain,
    ( r1_tarski(sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_178943,plain,
    ( r1_tarski(sK3,X1) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_178553,c_20])).

cnf(c_178944,plain,
    ( r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r1_tarski(sK3,X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_178943])).

cnf(c_178947,plain,
    ( r2_hidden(sK0(sK4,X0),sK5) = iProver_top
    | r1_tarski(sK3,X1) = iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_566,c_178944])).

cnf(c_179457,plain,
    ( r1_tarski(sK3,X0) = iProver_top
    | r1_tarski(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_178947,c_567])).

cnf(c_179788,plain,
    ( r1_tarski(sK3,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_179457,c_20])).

cnf(c_11,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK2(X0,X1),X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_556,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1750,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK2(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_556,c_565])).

cnf(c_10,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK2(X0,X1),X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_557,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK2(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1987,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK2(X0,X1),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_557,c_1983])).

cnf(c_3916,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1750,c_1987])).

cnf(c_179808,plain,
    ( r1_xboole_0(sK3,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_179788,c_3916])).

cnf(c_179842,plain,
    ( r1_xboole_0(sK3,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_179808])).

cnf(c_171596,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(sK1(X2,X0,k1_xboole_0),X1)
    | ~ r2_hidden(sK1(X2,X0,k1_xboole_0),X0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_171597,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(sK1(X2,X0,k1_xboole_0),X1) != iProver_top
    | r2_hidden(sK1(X2,X0,k1_xboole_0),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_171596])).

cnf(c_171599,plain,
    ( r1_xboole_0(sK3,sK3) != iProver_top
    | r2_hidden(sK1(sK3,sK3,k1_xboole_0),sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_171597])).

cnf(c_647,plain,
    ( X0 != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_249])).

cnf(c_7154,plain,
    ( X0 != k3_xboole_0(X1,X2)
    | k1_xboole_0 = X0
    | k1_xboole_0 != k3_xboole_0(X1,X2) ),
    inference(instantiation,[status(thm)],[c_647])).

cnf(c_7155,plain,
    ( sK3 != k3_xboole_0(sK3,sK3)
    | k1_xboole_0 != k3_xboole_0(sK3,sK3)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_7154])).

cnf(c_7140,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r2_hidden(sK1(X0,X1,k1_xboole_0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_563,c_7132])).

cnf(c_7149,plain,
    ( k3_xboole_0(sK3,sK3) = k1_xboole_0
    | r2_hidden(sK1(sK3,sK3,k1_xboole_0),sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_7140])).

cnf(c_6085,plain,
    ( X0 != X1
    | X0 = k3_xboole_0(X2,X3)
    | k3_xboole_0(X2,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_249])).

cnf(c_6086,plain,
    ( k3_xboole_0(sK3,sK3) != sK3
    | sK3 = k3_xboole_0(sK3,sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_6085])).

cnf(c_867,plain,
    ( X0 != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_647])).

cnf(c_2013,plain,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | k1_xboole_0 = k3_xboole_0(X0,X1)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_867])).

cnf(c_2014,plain,
    ( k3_xboole_0(sK3,sK3) != k1_xboole_0
    | k1_xboole_0 = k3_xboole_0(sK3,sK3)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2013])).

cnf(c_259,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_248])).

cnf(c_50,plain,
    ( ~ r2_hidden(sK1(sK3,sK3,sK3),sK3)
    | k3_xboole_0(sK3,sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_46,plain,
    ( r2_hidden(sK1(sK3,sK3,sK3),sK3)
    | k3_xboole_0(sK3,sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_179842,c_171599,c_7155,c_7149,c_6086,c_2014,c_964,c_259,c_50,c_46,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:28:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 55.39/7.44  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 55.39/7.44  
% 55.39/7.44  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 55.39/7.44  
% 55.39/7.44  ------  iProver source info
% 55.39/7.44  
% 55.39/7.44  git: date: 2020-06-30 10:37:57 +0100
% 55.39/7.44  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 55.39/7.44  git: non_committed_changes: false
% 55.39/7.44  git: last_make_outside_of_git: false
% 55.39/7.44  
% 55.39/7.44  ------ 
% 55.39/7.44  
% 55.39/7.44  ------ Input Options
% 55.39/7.44  
% 55.39/7.44  --out_options                           all
% 55.39/7.44  --tptp_safe_out                         true
% 55.39/7.44  --problem_path                          ""
% 55.39/7.44  --include_path                          ""
% 55.39/7.44  --clausifier                            res/vclausify_rel
% 55.39/7.44  --clausifier_options                    ""
% 55.39/7.44  --stdin                                 false
% 55.39/7.44  --stats_out                             all
% 55.39/7.44  
% 55.39/7.44  ------ General Options
% 55.39/7.44  
% 55.39/7.44  --fof                                   false
% 55.39/7.44  --time_out_real                         305.
% 55.39/7.44  --time_out_virtual                      -1.
% 55.39/7.44  --symbol_type_check                     false
% 55.39/7.44  --clausify_out                          false
% 55.39/7.44  --sig_cnt_out                           false
% 55.39/7.44  --trig_cnt_out                          false
% 55.39/7.44  --trig_cnt_out_tolerance                1.
% 55.39/7.44  --trig_cnt_out_sk_spl                   false
% 55.39/7.44  --abstr_cl_out                          false
% 55.39/7.44  
% 55.39/7.44  ------ Global Options
% 55.39/7.44  
% 55.39/7.44  --schedule                              default
% 55.39/7.44  --add_important_lit                     false
% 55.39/7.44  --prop_solver_per_cl                    1000
% 55.39/7.44  --min_unsat_core                        false
% 55.39/7.44  --soft_assumptions                      false
% 55.39/7.44  --soft_lemma_size                       3
% 55.39/7.44  --prop_impl_unit_size                   0
% 55.39/7.44  --prop_impl_unit                        []
% 55.39/7.44  --share_sel_clauses                     true
% 55.39/7.44  --reset_solvers                         false
% 55.39/7.44  --bc_imp_inh                            [conj_cone]
% 55.39/7.44  --conj_cone_tolerance                   3.
% 55.39/7.44  --extra_neg_conj                        none
% 55.39/7.44  --large_theory_mode                     true
% 55.39/7.44  --prolific_symb_bound                   200
% 55.39/7.44  --lt_threshold                          2000
% 55.39/7.44  --clause_weak_htbl                      true
% 55.39/7.44  --gc_record_bc_elim                     false
% 55.39/7.44  
% 55.39/7.44  ------ Preprocessing Options
% 55.39/7.44  
% 55.39/7.44  --preprocessing_flag                    true
% 55.39/7.44  --time_out_prep_mult                    0.1
% 55.39/7.44  --splitting_mode                        input
% 55.39/7.44  --splitting_grd                         true
% 55.39/7.44  --splitting_cvd                         false
% 55.39/7.44  --splitting_cvd_svl                     false
% 55.39/7.44  --splitting_nvd                         32
% 55.39/7.44  --sub_typing                            true
% 55.39/7.44  --prep_gs_sim                           true
% 55.39/7.44  --prep_unflatten                        true
% 55.39/7.44  --prep_res_sim                          true
% 55.39/7.44  --prep_upred                            true
% 55.39/7.44  --prep_sem_filter                       exhaustive
% 55.39/7.44  --prep_sem_filter_out                   false
% 55.39/7.44  --pred_elim                             true
% 55.39/7.44  --res_sim_input                         true
% 55.39/7.44  --eq_ax_congr_red                       true
% 55.39/7.44  --pure_diseq_elim                       true
% 55.39/7.44  --brand_transform                       false
% 55.39/7.44  --non_eq_to_eq                          false
% 55.39/7.44  --prep_def_merge                        true
% 55.39/7.44  --prep_def_merge_prop_impl              false
% 55.39/7.44  --prep_def_merge_mbd                    true
% 55.39/7.44  --prep_def_merge_tr_red                 false
% 55.39/7.44  --prep_def_merge_tr_cl                  false
% 55.39/7.44  --smt_preprocessing                     true
% 55.39/7.44  --smt_ac_axioms                         fast
% 55.39/7.44  --preprocessed_out                      false
% 55.39/7.44  --preprocessed_stats                    false
% 55.39/7.44  
% 55.39/7.44  ------ Abstraction refinement Options
% 55.39/7.44  
% 55.39/7.44  --abstr_ref                             []
% 55.39/7.44  --abstr_ref_prep                        false
% 55.39/7.44  --abstr_ref_until_sat                   false
% 55.39/7.44  --abstr_ref_sig_restrict                funpre
% 55.39/7.44  --abstr_ref_af_restrict_to_split_sk     false
% 55.39/7.44  --abstr_ref_under                       []
% 55.39/7.44  
% 55.39/7.44  ------ SAT Options
% 55.39/7.44  
% 55.39/7.44  --sat_mode                              false
% 55.39/7.44  --sat_fm_restart_options                ""
% 55.39/7.44  --sat_gr_def                            false
% 55.39/7.44  --sat_epr_types                         true
% 55.39/7.44  --sat_non_cyclic_types                  false
% 55.39/7.44  --sat_finite_models                     false
% 55.39/7.44  --sat_fm_lemmas                         false
% 55.39/7.44  --sat_fm_prep                           false
% 55.39/7.44  --sat_fm_uc_incr                        true
% 55.39/7.44  --sat_out_model                         small
% 55.39/7.44  --sat_out_clauses                       false
% 55.39/7.44  
% 55.39/7.44  ------ QBF Options
% 55.39/7.44  
% 55.39/7.44  --qbf_mode                              false
% 55.39/7.44  --qbf_elim_univ                         false
% 55.39/7.44  --qbf_dom_inst                          none
% 55.39/7.44  --qbf_dom_pre_inst                      false
% 55.39/7.44  --qbf_sk_in                             false
% 55.39/7.44  --qbf_pred_elim                         true
% 55.39/7.44  --qbf_split                             512
% 55.39/7.44  
% 55.39/7.44  ------ BMC1 Options
% 55.39/7.44  
% 55.39/7.44  --bmc1_incremental                      false
% 55.39/7.44  --bmc1_axioms                           reachable_all
% 55.39/7.44  --bmc1_min_bound                        0
% 55.39/7.44  --bmc1_max_bound                        -1
% 55.39/7.44  --bmc1_max_bound_default                -1
% 55.39/7.44  --bmc1_symbol_reachability              true
% 55.39/7.44  --bmc1_property_lemmas                  false
% 55.39/7.44  --bmc1_k_induction                      false
% 55.39/7.44  --bmc1_non_equiv_states                 false
% 55.39/7.44  --bmc1_deadlock                         false
% 55.39/7.44  --bmc1_ucm                              false
% 55.39/7.44  --bmc1_add_unsat_core                   none
% 55.39/7.44  --bmc1_unsat_core_children              false
% 55.39/7.44  --bmc1_unsat_core_extrapolate_axioms    false
% 55.39/7.44  --bmc1_out_stat                         full
% 55.39/7.44  --bmc1_ground_init                      false
% 55.39/7.44  --bmc1_pre_inst_next_state              false
% 55.39/7.44  --bmc1_pre_inst_state                   false
% 55.39/7.44  --bmc1_pre_inst_reach_state             false
% 55.39/7.44  --bmc1_out_unsat_core                   false
% 55.39/7.44  --bmc1_aig_witness_out                  false
% 55.39/7.44  --bmc1_verbose                          false
% 55.39/7.44  --bmc1_dump_clauses_tptp                false
% 55.39/7.44  --bmc1_dump_unsat_core_tptp             false
% 55.39/7.44  --bmc1_dump_file                        -
% 55.39/7.44  --bmc1_ucm_expand_uc_limit              128
% 55.39/7.44  --bmc1_ucm_n_expand_iterations          6
% 55.39/7.44  --bmc1_ucm_extend_mode                  1
% 55.39/7.44  --bmc1_ucm_init_mode                    2
% 55.39/7.44  --bmc1_ucm_cone_mode                    none
% 55.39/7.44  --bmc1_ucm_reduced_relation_type        0
% 55.39/7.44  --bmc1_ucm_relax_model                  4
% 55.39/7.44  --bmc1_ucm_full_tr_after_sat            true
% 55.39/7.44  --bmc1_ucm_expand_neg_assumptions       false
% 55.39/7.44  --bmc1_ucm_layered_model                none
% 55.39/7.44  --bmc1_ucm_max_lemma_size               10
% 55.39/7.44  
% 55.39/7.44  ------ AIG Options
% 55.39/7.44  
% 55.39/7.44  --aig_mode                              false
% 55.39/7.44  
% 55.39/7.44  ------ Instantiation Options
% 55.39/7.44  
% 55.39/7.44  --instantiation_flag                    true
% 55.39/7.44  --inst_sos_flag                         true
% 55.39/7.44  --inst_sos_phase                        true
% 55.39/7.44  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.39/7.44  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.39/7.44  --inst_lit_sel_side                     num_symb
% 55.39/7.44  --inst_solver_per_active                1400
% 55.39/7.44  --inst_solver_calls_frac                1.
% 55.39/7.44  --inst_passive_queue_type               priority_queues
% 55.39/7.44  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 55.39/7.44  --inst_passive_queues_freq              [25;2]
% 55.39/7.44  --inst_dismatching                      true
% 55.39/7.44  --inst_eager_unprocessed_to_passive     true
% 55.39/7.44  --inst_prop_sim_given                   true
% 55.39/7.44  --inst_prop_sim_new                     false
% 55.39/7.44  --inst_subs_new                         false
% 55.39/7.44  --inst_eq_res_simp                      false
% 55.39/7.44  --inst_subs_given                       false
% 55.39/7.44  --inst_orphan_elimination               true
% 55.39/7.44  --inst_learning_loop_flag               true
% 55.39/7.44  --inst_learning_start                   3000
% 55.39/7.44  --inst_learning_factor                  2
% 55.39/7.44  --inst_start_prop_sim_after_learn       3
% 55.39/7.44  --inst_sel_renew                        solver
% 55.39/7.44  --inst_lit_activity_flag                true
% 55.39/7.44  --inst_restr_to_given                   false
% 55.39/7.44  --inst_activity_threshold               500
% 55.39/7.44  --inst_out_proof                        true
% 55.39/7.44  
% 55.39/7.44  ------ Resolution Options
% 55.39/7.44  
% 55.39/7.44  --resolution_flag                       true
% 55.39/7.44  --res_lit_sel                           adaptive
% 55.39/7.44  --res_lit_sel_side                      none
% 55.39/7.44  --res_ordering                          kbo
% 55.39/7.44  --res_to_prop_solver                    active
% 55.39/7.44  --res_prop_simpl_new                    false
% 55.39/7.44  --res_prop_simpl_given                  true
% 55.39/7.44  --res_passive_queue_type                priority_queues
% 55.39/7.44  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 55.39/7.44  --res_passive_queues_freq               [15;5]
% 55.39/7.44  --res_forward_subs                      full
% 55.39/7.44  --res_backward_subs                     full
% 55.39/7.44  --res_forward_subs_resolution           true
% 55.39/7.44  --res_backward_subs_resolution          true
% 55.39/7.44  --res_orphan_elimination                true
% 55.39/7.44  --res_time_limit                        2.
% 55.39/7.44  --res_out_proof                         true
% 55.39/7.44  
% 55.39/7.44  ------ Superposition Options
% 55.39/7.44  
% 55.39/7.44  --superposition_flag                    true
% 55.39/7.44  --sup_passive_queue_type                priority_queues
% 55.39/7.44  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.39/7.44  --sup_passive_queues_freq               [8;1;4]
% 55.39/7.44  --demod_completeness_check              fast
% 55.39/7.44  --demod_use_ground                      true
% 55.39/7.44  --sup_to_prop_solver                    passive
% 55.39/7.44  --sup_prop_simpl_new                    true
% 55.39/7.44  --sup_prop_simpl_given                  true
% 55.39/7.44  --sup_fun_splitting                     true
% 55.39/7.44  --sup_smt_interval                      50000
% 55.39/7.44  
% 55.39/7.44  ------ Superposition Simplification Setup
% 55.39/7.44  
% 55.39/7.44  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 55.39/7.44  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 55.39/7.44  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 55.39/7.44  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 55.39/7.44  --sup_full_triv                         [TrivRules;PropSubs]
% 55.39/7.44  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 55.39/7.44  --sup_full_bw                           [BwDemod;BwSubsumption]
% 55.39/7.44  --sup_immed_triv                        [TrivRules]
% 55.39/7.44  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.39/7.44  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.39/7.44  --sup_immed_bw_main                     []
% 55.39/7.44  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 55.39/7.44  --sup_input_triv                        [Unflattening;TrivRules]
% 55.39/7.44  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.39/7.44  --sup_input_bw                          []
% 55.39/7.44  
% 55.39/7.44  ------ Combination Options
% 55.39/7.44  
% 55.39/7.44  --comb_res_mult                         3
% 55.39/7.44  --comb_sup_mult                         2
% 55.39/7.44  --comb_inst_mult                        10
% 55.39/7.44  
% 55.39/7.44  ------ Debug Options
% 55.39/7.44  
% 55.39/7.44  --dbg_backtrace                         false
% 55.39/7.44  --dbg_dump_prop_clauses                 false
% 55.39/7.44  --dbg_dump_prop_clauses_file            -
% 55.39/7.44  --dbg_out_stat                          false
% 55.39/7.44  ------ Parsing...
% 55.39/7.44  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 55.39/7.44  
% 55.39/7.44  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 55.39/7.44  
% 55.39/7.44  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 55.39/7.44  
% 55.39/7.44  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 55.39/7.44  ------ Proving...
% 55.39/7.44  ------ Problem Properties 
% 55.39/7.44  
% 55.39/7.44  
% 55.39/7.44  clauses                                 19
% 55.39/7.44  conjectures                             3
% 55.39/7.44  EPR                                     5
% 55.39/7.44  Horn                                    13
% 55.39/7.44  unary                                   3
% 55.39/7.44  binary                                  9
% 55.39/7.44  lits                                    43
% 55.39/7.44  lits eq                                 4
% 55.39/7.44  fd_pure                                 0
% 55.39/7.44  fd_pseudo                               0
% 55.39/7.44  fd_cond                                 0
% 55.39/7.44  fd_pseudo_cond                          3
% 55.39/7.44  AC symbols                              0
% 55.39/7.44  
% 55.39/7.44  ------ Schedule dynamic 5 is on 
% 55.39/7.44  
% 55.39/7.44  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 55.39/7.44  
% 55.39/7.44  
% 55.39/7.44  ------ 
% 55.39/7.44  Current options:
% 55.39/7.44  ------ 
% 55.39/7.44  
% 55.39/7.44  ------ Input Options
% 55.39/7.44  
% 55.39/7.44  --out_options                           all
% 55.39/7.44  --tptp_safe_out                         true
% 55.39/7.44  --problem_path                          ""
% 55.39/7.44  --include_path                          ""
% 55.39/7.44  --clausifier                            res/vclausify_rel
% 55.39/7.44  --clausifier_options                    ""
% 55.39/7.44  --stdin                                 false
% 55.39/7.44  --stats_out                             all
% 55.39/7.44  
% 55.39/7.44  ------ General Options
% 55.39/7.44  
% 55.39/7.44  --fof                                   false
% 55.39/7.44  --time_out_real                         305.
% 55.39/7.44  --time_out_virtual                      -1.
% 55.39/7.44  --symbol_type_check                     false
% 55.39/7.44  --clausify_out                          false
% 55.39/7.44  --sig_cnt_out                           false
% 55.39/7.44  --trig_cnt_out                          false
% 55.39/7.44  --trig_cnt_out_tolerance                1.
% 55.39/7.44  --trig_cnt_out_sk_spl                   false
% 55.39/7.44  --abstr_cl_out                          false
% 55.39/7.44  
% 55.39/7.44  ------ Global Options
% 55.39/7.44  
% 55.39/7.44  --schedule                              default
% 55.39/7.44  --add_important_lit                     false
% 55.39/7.44  --prop_solver_per_cl                    1000
% 55.39/7.44  --min_unsat_core                        false
% 55.39/7.44  --soft_assumptions                      false
% 55.39/7.44  --soft_lemma_size                       3
% 55.39/7.44  --prop_impl_unit_size                   0
% 55.39/7.44  --prop_impl_unit                        []
% 55.39/7.44  --share_sel_clauses                     true
% 55.39/7.44  --reset_solvers                         false
% 55.39/7.44  --bc_imp_inh                            [conj_cone]
% 55.39/7.44  --conj_cone_tolerance                   3.
% 55.39/7.44  --extra_neg_conj                        none
% 55.39/7.44  --large_theory_mode                     true
% 55.39/7.44  --prolific_symb_bound                   200
% 55.39/7.44  --lt_threshold                          2000
% 55.39/7.44  --clause_weak_htbl                      true
% 55.39/7.44  --gc_record_bc_elim                     false
% 55.39/7.44  
% 55.39/7.44  ------ Preprocessing Options
% 55.39/7.44  
% 55.39/7.44  --preprocessing_flag                    true
% 55.39/7.44  --time_out_prep_mult                    0.1
% 55.39/7.44  --splitting_mode                        input
% 55.39/7.44  --splitting_grd                         true
% 55.39/7.44  --splitting_cvd                         false
% 55.39/7.44  --splitting_cvd_svl                     false
% 55.39/7.44  --splitting_nvd                         32
% 55.39/7.44  --sub_typing                            true
% 55.39/7.44  --prep_gs_sim                           true
% 55.39/7.44  --prep_unflatten                        true
% 55.39/7.44  --prep_res_sim                          true
% 55.39/7.44  --prep_upred                            true
% 55.39/7.44  --prep_sem_filter                       exhaustive
% 55.39/7.44  --prep_sem_filter_out                   false
% 55.39/7.44  --pred_elim                             true
% 55.39/7.44  --res_sim_input                         true
% 55.39/7.44  --eq_ax_congr_red                       true
% 55.39/7.44  --pure_diseq_elim                       true
% 55.39/7.44  --brand_transform                       false
% 55.39/7.44  --non_eq_to_eq                          false
% 55.39/7.44  --prep_def_merge                        true
% 55.39/7.44  --prep_def_merge_prop_impl              false
% 55.39/7.44  --prep_def_merge_mbd                    true
% 55.39/7.44  --prep_def_merge_tr_red                 false
% 55.39/7.44  --prep_def_merge_tr_cl                  false
% 55.39/7.44  --smt_preprocessing                     true
% 55.39/7.44  --smt_ac_axioms                         fast
% 55.39/7.44  --preprocessed_out                      false
% 55.39/7.44  --preprocessed_stats                    false
% 55.39/7.44  
% 55.39/7.44  ------ Abstraction refinement Options
% 55.39/7.44  
% 55.39/7.44  --abstr_ref                             []
% 55.39/7.44  --abstr_ref_prep                        false
% 55.39/7.44  --abstr_ref_until_sat                   false
% 55.39/7.44  --abstr_ref_sig_restrict                funpre
% 55.39/7.44  --abstr_ref_af_restrict_to_split_sk     false
% 55.39/7.44  --abstr_ref_under                       []
% 55.39/7.44  
% 55.39/7.44  ------ SAT Options
% 55.39/7.44  
% 55.39/7.44  --sat_mode                              false
% 55.39/7.44  --sat_fm_restart_options                ""
% 55.39/7.44  --sat_gr_def                            false
% 55.39/7.44  --sat_epr_types                         true
% 55.39/7.44  --sat_non_cyclic_types                  false
% 55.39/7.44  --sat_finite_models                     false
% 55.39/7.44  --sat_fm_lemmas                         false
% 55.39/7.44  --sat_fm_prep                           false
% 55.39/7.44  --sat_fm_uc_incr                        true
% 55.39/7.44  --sat_out_model                         small
% 55.39/7.44  --sat_out_clauses                       false
% 55.39/7.44  
% 55.39/7.44  ------ QBF Options
% 55.39/7.44  
% 55.39/7.44  --qbf_mode                              false
% 55.39/7.44  --qbf_elim_univ                         false
% 55.39/7.44  --qbf_dom_inst                          none
% 55.39/7.44  --qbf_dom_pre_inst                      false
% 55.39/7.44  --qbf_sk_in                             false
% 55.39/7.44  --qbf_pred_elim                         true
% 55.39/7.44  --qbf_split                             512
% 55.39/7.44  
% 55.39/7.44  ------ BMC1 Options
% 55.39/7.44  
% 55.39/7.44  --bmc1_incremental                      false
% 55.39/7.44  --bmc1_axioms                           reachable_all
% 55.39/7.44  --bmc1_min_bound                        0
% 55.39/7.44  --bmc1_max_bound                        -1
% 55.39/7.44  --bmc1_max_bound_default                -1
% 55.39/7.44  --bmc1_symbol_reachability              true
% 55.39/7.44  --bmc1_property_lemmas                  false
% 55.39/7.44  --bmc1_k_induction                      false
% 55.39/7.44  --bmc1_non_equiv_states                 false
% 55.39/7.44  --bmc1_deadlock                         false
% 55.39/7.44  --bmc1_ucm                              false
% 55.39/7.44  --bmc1_add_unsat_core                   none
% 55.39/7.44  --bmc1_unsat_core_children              false
% 55.39/7.44  --bmc1_unsat_core_extrapolate_axioms    false
% 55.39/7.44  --bmc1_out_stat                         full
% 55.39/7.44  --bmc1_ground_init                      false
% 55.39/7.44  --bmc1_pre_inst_next_state              false
% 55.39/7.44  --bmc1_pre_inst_state                   false
% 55.39/7.44  --bmc1_pre_inst_reach_state             false
% 55.39/7.44  --bmc1_out_unsat_core                   false
% 55.39/7.44  --bmc1_aig_witness_out                  false
% 55.39/7.44  --bmc1_verbose                          false
% 55.39/7.44  --bmc1_dump_clauses_tptp                false
% 55.39/7.44  --bmc1_dump_unsat_core_tptp             false
% 55.39/7.44  --bmc1_dump_file                        -
% 55.39/7.44  --bmc1_ucm_expand_uc_limit              128
% 55.39/7.44  --bmc1_ucm_n_expand_iterations          6
% 55.39/7.44  --bmc1_ucm_extend_mode                  1
% 55.39/7.44  --bmc1_ucm_init_mode                    2
% 55.39/7.44  --bmc1_ucm_cone_mode                    none
% 55.39/7.44  --bmc1_ucm_reduced_relation_type        0
% 55.39/7.44  --bmc1_ucm_relax_model                  4
% 55.39/7.44  --bmc1_ucm_full_tr_after_sat            true
% 55.39/7.44  --bmc1_ucm_expand_neg_assumptions       false
% 55.39/7.44  --bmc1_ucm_layered_model                none
% 55.39/7.44  --bmc1_ucm_max_lemma_size               10
% 55.39/7.44  
% 55.39/7.44  ------ AIG Options
% 55.39/7.44  
% 55.39/7.44  --aig_mode                              false
% 55.39/7.44  
% 55.39/7.44  ------ Instantiation Options
% 55.39/7.44  
% 55.39/7.44  --instantiation_flag                    true
% 55.39/7.44  --inst_sos_flag                         true
% 55.39/7.44  --inst_sos_phase                        true
% 55.39/7.44  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.39/7.44  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.39/7.44  --inst_lit_sel_side                     none
% 55.39/7.44  --inst_solver_per_active                1400
% 55.39/7.44  --inst_solver_calls_frac                1.
% 55.39/7.44  --inst_passive_queue_type               priority_queues
% 55.39/7.44  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 55.39/7.44  --inst_passive_queues_freq              [25;2]
% 55.39/7.44  --inst_dismatching                      true
% 55.39/7.44  --inst_eager_unprocessed_to_passive     true
% 55.39/7.44  --inst_prop_sim_given                   true
% 55.39/7.44  --inst_prop_sim_new                     false
% 55.39/7.44  --inst_subs_new                         false
% 55.39/7.44  --inst_eq_res_simp                      false
% 55.39/7.44  --inst_subs_given                       false
% 55.39/7.44  --inst_orphan_elimination               true
% 55.39/7.44  --inst_learning_loop_flag               true
% 55.39/7.44  --inst_learning_start                   3000
% 55.39/7.44  --inst_learning_factor                  2
% 55.39/7.44  --inst_start_prop_sim_after_learn       3
% 55.39/7.44  --inst_sel_renew                        solver
% 55.39/7.44  --inst_lit_activity_flag                true
% 55.39/7.44  --inst_restr_to_given                   false
% 55.39/7.44  --inst_activity_threshold               500
% 55.39/7.44  --inst_out_proof                        true
% 55.39/7.44  
% 55.39/7.44  ------ Resolution Options
% 55.39/7.44  
% 55.39/7.44  --resolution_flag                       false
% 55.39/7.44  --res_lit_sel                           adaptive
% 55.39/7.44  --res_lit_sel_side                      none
% 55.39/7.44  --res_ordering                          kbo
% 55.39/7.44  --res_to_prop_solver                    active
% 55.39/7.44  --res_prop_simpl_new                    false
% 55.39/7.44  --res_prop_simpl_given                  true
% 55.39/7.44  --res_passive_queue_type                priority_queues
% 55.39/7.44  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 55.39/7.44  --res_passive_queues_freq               [15;5]
% 55.39/7.44  --res_forward_subs                      full
% 55.39/7.44  --res_backward_subs                     full
% 55.39/7.44  --res_forward_subs_resolution           true
% 55.39/7.44  --res_backward_subs_resolution          true
% 55.39/7.44  --res_orphan_elimination                true
% 55.39/7.44  --res_time_limit                        2.
% 55.39/7.44  --res_out_proof                         true
% 55.39/7.44  
% 55.39/7.44  ------ Superposition Options
% 55.39/7.44  
% 55.39/7.44  --superposition_flag                    true
% 55.39/7.44  --sup_passive_queue_type                priority_queues
% 55.39/7.44  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.39/7.44  --sup_passive_queues_freq               [8;1;4]
% 55.39/7.44  --demod_completeness_check              fast
% 55.39/7.44  --demod_use_ground                      true
% 55.39/7.44  --sup_to_prop_solver                    passive
% 55.39/7.44  --sup_prop_simpl_new                    true
% 55.39/7.44  --sup_prop_simpl_given                  true
% 55.39/7.44  --sup_fun_splitting                     true
% 55.39/7.44  --sup_smt_interval                      50000
% 55.39/7.44  
% 55.39/7.44  ------ Superposition Simplification Setup
% 55.39/7.44  
% 55.39/7.44  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 55.39/7.44  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 55.39/7.44  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 55.39/7.44  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 55.39/7.44  --sup_full_triv                         [TrivRules;PropSubs]
% 55.39/7.44  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 55.39/7.44  --sup_full_bw                           [BwDemod;BwSubsumption]
% 55.39/7.44  --sup_immed_triv                        [TrivRules]
% 55.39/7.44  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.39/7.44  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.39/7.44  --sup_immed_bw_main                     []
% 55.39/7.44  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 55.39/7.44  --sup_input_triv                        [Unflattening;TrivRules]
% 55.39/7.44  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.39/7.44  --sup_input_bw                          []
% 55.39/7.44  
% 55.39/7.44  ------ Combination Options
% 55.39/7.44  
% 55.39/7.44  --comb_res_mult                         3
% 55.39/7.44  --comb_sup_mult                         2
% 55.39/7.44  --comb_inst_mult                        10
% 55.39/7.44  
% 55.39/7.44  ------ Debug Options
% 55.39/7.44  
% 55.39/7.44  --dbg_backtrace                         false
% 55.39/7.44  --dbg_dump_prop_clauses                 false
% 55.39/7.44  --dbg_dump_prop_clauses_file            -
% 55.39/7.44  --dbg_out_stat                          false
% 55.39/7.44  
% 55.39/7.44  
% 55.39/7.44  
% 55.39/7.44  
% 55.39/7.44  ------ Proving...
% 55.39/7.44  
% 55.39/7.44  
% 55.39/7.44  % SZS status Theorem for theBenchmark.p
% 55.39/7.44  
% 55.39/7.44  % SZS output start CNFRefutation for theBenchmark.p
% 55.39/7.44  
% 55.39/7.44  fof(f1,axiom,(
% 55.39/7.44    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 55.39/7.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.39/7.44  
% 55.39/7.44  fof(f9,plain,(
% 55.39/7.44    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 55.39/7.44    inference(ennf_transformation,[],[f1])).
% 55.39/7.44  
% 55.39/7.44  fof(f12,plain,(
% 55.39/7.44    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 55.39/7.44    inference(nnf_transformation,[],[f9])).
% 55.39/7.44  
% 55.39/7.44  fof(f13,plain,(
% 55.39/7.44    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 55.39/7.44    inference(rectify,[],[f12])).
% 55.39/7.44  
% 55.39/7.44  fof(f14,plain,(
% 55.39/7.44    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 55.39/7.44    introduced(choice_axiom,[])).
% 55.39/7.44  
% 55.39/7.44  fof(f15,plain,(
% 55.39/7.44    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 55.39/7.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f14])).
% 55.39/7.44  
% 55.39/7.44  fof(f28,plain,(
% 55.39/7.44    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 55.39/7.44    inference(cnf_transformation,[],[f15])).
% 55.39/7.44  
% 55.39/7.44  fof(f6,conjecture,(
% 55.39/7.44    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 55.39/7.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.39/7.44  
% 55.39/7.44  fof(f7,negated_conjecture,(
% 55.39/7.44    ~! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 55.39/7.44    inference(negated_conjecture,[],[f6])).
% 55.39/7.44  
% 55.39/7.44  fof(f11,plain,(
% 55.39/7.44    ? [X0,X1,X2] : (~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 55.39/7.44    inference(ennf_transformation,[],[f7])).
% 55.39/7.44  
% 55.39/7.44  fof(f25,plain,(
% 55.39/7.44    ? [X0,X1,X2] : (~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0) => (~r1_tarski(sK4,sK5) & (r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK3,sK5)) | r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK5,sK3))) & k1_xboole_0 != sK3)),
% 55.39/7.44    introduced(choice_axiom,[])).
% 55.39/7.44  
% 55.39/7.44  fof(f26,plain,(
% 55.39/7.44    ~r1_tarski(sK4,sK5) & (r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK3,sK5)) | r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK5,sK3))) & k1_xboole_0 != sK3),
% 55.39/7.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f11,f25])).
% 55.39/7.44  
% 55.39/7.44  fof(f44,plain,(
% 55.39/7.44    r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK3,sK5)) | r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK5,sK3))),
% 55.39/7.44    inference(cnf_transformation,[],[f26])).
% 55.39/7.44  
% 55.39/7.44  fof(f5,axiom,(
% 55.39/7.44    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 55.39/7.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.39/7.44  
% 55.39/7.44  fof(f23,plain,(
% 55.39/7.44    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 55.39/7.44    inference(nnf_transformation,[],[f5])).
% 55.39/7.44  
% 55.39/7.44  fof(f24,plain,(
% 55.39/7.44    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 55.39/7.44    inference(flattening,[],[f23])).
% 55.39/7.44  
% 55.39/7.44  fof(f42,plain,(
% 55.39/7.44    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 55.39/7.44    inference(cnf_transformation,[],[f24])).
% 55.39/7.44  
% 55.39/7.44  fof(f27,plain,(
% 55.39/7.44    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 55.39/7.44    inference(cnf_transformation,[],[f15])).
% 55.39/7.44  
% 55.39/7.44  fof(f41,plain,(
% 55.39/7.44    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 55.39/7.44    inference(cnf_transformation,[],[f24])).
% 55.39/7.44  
% 55.39/7.44  fof(f43,plain,(
% 55.39/7.44    k1_xboole_0 != sK3),
% 55.39/7.44    inference(cnf_transformation,[],[f26])).
% 55.39/7.44  
% 55.39/7.44  fof(f2,axiom,(
% 55.39/7.44    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 55.39/7.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.39/7.44  
% 55.39/7.44  fof(f16,plain,(
% 55.39/7.44    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 55.39/7.44    inference(nnf_transformation,[],[f2])).
% 55.39/7.44  
% 55.39/7.44  fof(f17,plain,(
% 55.39/7.44    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 55.39/7.44    inference(flattening,[],[f16])).
% 55.39/7.44  
% 55.39/7.44  fof(f18,plain,(
% 55.39/7.44    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 55.39/7.44    inference(rectify,[],[f17])).
% 55.39/7.44  
% 55.39/7.44  fof(f19,plain,(
% 55.39/7.44    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 55.39/7.44    introduced(choice_axiom,[])).
% 55.39/7.44  
% 55.39/7.44  fof(f20,plain,(
% 55.39/7.44    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 55.39/7.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f19])).
% 55.39/7.44  
% 55.39/7.44  fof(f33,plain,(
% 55.39/7.44    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 55.39/7.44    inference(cnf_transformation,[],[f20])).
% 55.39/7.44  
% 55.39/7.44  fof(f4,axiom,(
% 55.39/7.44    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 55.39/7.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.39/7.44  
% 55.39/7.44  fof(f39,plain,(
% 55.39/7.44    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 55.39/7.44    inference(cnf_transformation,[],[f4])).
% 55.39/7.44  
% 55.39/7.44  fof(f3,axiom,(
% 55.39/7.44    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 55.39/7.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.39/7.44  
% 55.39/7.44  fof(f8,plain,(
% 55.39/7.44    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 55.39/7.44    inference(rectify,[],[f3])).
% 55.39/7.44  
% 55.39/7.44  fof(f10,plain,(
% 55.39/7.44    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 55.39/7.44    inference(ennf_transformation,[],[f8])).
% 55.39/7.44  
% 55.39/7.44  fof(f21,plain,(
% 55.39/7.44    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 55.39/7.44    introduced(choice_axiom,[])).
% 55.39/7.44  
% 55.39/7.44  fof(f22,plain,(
% 55.39/7.44    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 55.39/7.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f21])).
% 55.39/7.44  
% 55.39/7.44  fof(f38,plain,(
% 55.39/7.44    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 55.39/7.44    inference(cnf_transformation,[],[f22])).
% 55.39/7.44  
% 55.39/7.44  fof(f35,plain,(
% 55.39/7.44    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 55.39/7.44    inference(cnf_transformation,[],[f20])).
% 55.39/7.44  
% 55.39/7.44  fof(f34,plain,(
% 55.39/7.44    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 55.39/7.44    inference(cnf_transformation,[],[f20])).
% 55.39/7.44  
% 55.39/7.44  fof(f40,plain,(
% 55.39/7.44    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 55.39/7.44    inference(cnf_transformation,[],[f24])).
% 55.39/7.44  
% 55.39/7.44  fof(f29,plain,(
% 55.39/7.44    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 55.39/7.44    inference(cnf_transformation,[],[f15])).
% 55.39/7.44  
% 55.39/7.44  fof(f45,plain,(
% 55.39/7.44    ~r1_tarski(sK4,sK5)),
% 55.39/7.44    inference(cnf_transformation,[],[f26])).
% 55.39/7.44  
% 55.39/7.44  fof(f36,plain,(
% 55.39/7.44    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 55.39/7.44    inference(cnf_transformation,[],[f22])).
% 55.39/7.44  
% 55.39/7.44  fof(f37,plain,(
% 55.39/7.44    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 55.39/7.44    inference(cnf_transformation,[],[f22])).
% 55.39/7.44  
% 55.39/7.44  cnf(c_1,plain,
% 55.39/7.44      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 55.39/7.44      inference(cnf_transformation,[],[f28]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_566,plain,
% 55.39/7.44      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 55.39/7.44      | r1_tarski(X0,X1) = iProver_top ),
% 55.39/7.44      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_17,negated_conjecture,
% 55.39/7.44      ( r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK3,sK5))
% 55.39/7.44      | r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK5,sK3)) ),
% 55.39/7.44      inference(cnf_transformation,[],[f44]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_550,plain,
% 55.39/7.44      ( r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK3,sK5)) = iProver_top
% 55.39/7.44      | r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK5,sK3)) = iProver_top ),
% 55.39/7.44      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_13,plain,
% 55.39/7.44      ( ~ r2_hidden(X0,X1)
% 55.39/7.44      | ~ r2_hidden(X2,X3)
% 55.39/7.44      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 55.39/7.44      inference(cnf_transformation,[],[f42]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_554,plain,
% 55.39/7.44      ( r2_hidden(X0,X1) != iProver_top
% 55.39/7.44      | r2_hidden(X2,X3) != iProver_top
% 55.39/7.44      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 55.39/7.44      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_2,plain,
% 55.39/7.44      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 55.39/7.44      inference(cnf_transformation,[],[f27]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_565,plain,
% 55.39/7.44      ( r2_hidden(X0,X1) != iProver_top
% 55.39/7.44      | r2_hidden(X0,X2) = iProver_top
% 55.39/7.44      | r1_tarski(X1,X2) != iProver_top ),
% 55.39/7.44      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_2148,plain,
% 55.39/7.44      ( r2_hidden(X0,X1) != iProver_top
% 55.39/7.44      | r2_hidden(X2,X3) != iProver_top
% 55.39/7.44      | r2_hidden(k4_tarski(X2,X0),X4) = iProver_top
% 55.39/7.44      | r1_tarski(k2_zfmisc_1(X3,X1),X4) != iProver_top ),
% 55.39/7.44      inference(superposition,[status(thm)],[c_554,c_565]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_6685,plain,
% 55.39/7.44      ( r2_hidden(X0,sK3) != iProver_top
% 55.39/7.44      | r2_hidden(X1,sK4) != iProver_top
% 55.39/7.44      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK3,sK5)) = iProver_top
% 55.39/7.44      | r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK5,sK3)) = iProver_top ),
% 55.39/7.44      inference(superposition,[status(thm)],[c_550,c_2148]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_14,plain,
% 55.39/7.44      ( r2_hidden(X0,X1)
% 55.39/7.44      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 55.39/7.44      inference(cnf_transformation,[],[f41]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_553,plain,
% 55.39/7.44      ( r2_hidden(X0,X1) = iProver_top
% 55.39/7.44      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 55.39/7.44      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_6916,plain,
% 55.39/7.44      ( r2_hidden(X0,sK3) != iProver_top
% 55.39/7.44      | r2_hidden(X1,sK5) = iProver_top
% 55.39/7.44      | r2_hidden(X1,sK4) != iProver_top
% 55.39/7.44      | r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK5,sK3)) = iProver_top ),
% 55.39/7.44      inference(superposition,[status(thm)],[c_6685,c_553]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_6944,plain,
% 55.39/7.44      ( r2_hidden(X0,sK5) = iProver_top
% 55.39/7.44      | r2_hidden(X0,sK4) != iProver_top
% 55.39/7.44      | r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK5,sK3)) = iProver_top
% 55.39/7.44      | r1_tarski(sK3,X1) = iProver_top ),
% 55.39/7.44      inference(superposition,[status(thm)],[c_566,c_6916]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_18,negated_conjecture,
% 55.39/7.44      ( k1_xboole_0 != sK3 ),
% 55.39/7.44      inference(cnf_transformation,[],[f43]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_249,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_599,plain,
% 55.39/7.44      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 55.39/7.44      inference(instantiation,[status(thm)],[c_249]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_646,plain,
% 55.39/7.44      ( sK3 != k1_xboole_0
% 55.39/7.44      | k1_xboole_0 = sK3
% 55.39/7.44      | k1_xboole_0 != k1_xboole_0 ),
% 55.39/7.44      inference(instantiation,[status(thm)],[c_599]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_248,plain,( X0 = X0 ),theory(equality) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_964,plain,
% 55.39/7.44      ( k1_xboole_0 = k1_xboole_0 ),
% 55.39/7.44      inference(instantiation,[status(thm)],[c_248]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_5,plain,
% 55.39/7.44      ( r2_hidden(sK1(X0,X1,X2),X0)
% 55.39/7.44      | r2_hidden(sK1(X0,X1,X2),X2)
% 55.39/7.44      | k3_xboole_0(X0,X1) = X2 ),
% 55.39/7.44      inference(cnf_transformation,[],[f33]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_562,plain,
% 55.39/7.44      ( k3_xboole_0(X0,X1) = X2
% 55.39/7.44      | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
% 55.39/7.44      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 55.39/7.44      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_12,plain,
% 55.39/7.44      ( r1_xboole_0(X0,k1_xboole_0) ),
% 55.39/7.44      inference(cnf_transformation,[],[f39]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_555,plain,
% 55.39/7.44      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 55.39/7.44      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_9,plain,
% 55.39/7.44      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 55.39/7.44      inference(cnf_transformation,[],[f38]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_558,plain,
% 55.39/7.44      ( r1_xboole_0(X0,X1) != iProver_top
% 55.39/7.44      | r2_hidden(X2,X1) != iProver_top
% 55.39/7.44      | r2_hidden(X2,X0) != iProver_top ),
% 55.39/7.44      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_1983,plain,
% 55.39/7.44      ( r2_hidden(X0,X1) != iProver_top
% 55.39/7.44      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 55.39/7.44      inference(superposition,[status(thm)],[c_555,c_558]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_2213,plain,
% 55.39/7.44      ( k3_xboole_0(X0,X1) = X2
% 55.39/7.44      | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
% 55.39/7.44      | r2_hidden(sK1(X0,X1,X2),k1_xboole_0) != iProver_top ),
% 55.39/7.44      inference(superposition,[status(thm)],[c_562,c_1983]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_3,plain,
% 55.39/7.44      ( ~ r2_hidden(sK1(X0,X1,X2),X1)
% 55.39/7.44      | ~ r2_hidden(sK1(X0,X1,X2),X0)
% 55.39/7.44      | ~ r2_hidden(sK1(X0,X1,X2),X2)
% 55.39/7.44      | k3_xboole_0(X0,X1) = X2 ),
% 55.39/7.44      inference(cnf_transformation,[],[f35]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_49,plain,
% 55.39/7.44      ( k3_xboole_0(X0,X1) = X2
% 55.39/7.44      | r2_hidden(sK1(X0,X1,X2),X0) != iProver_top
% 55.39/7.44      | r2_hidden(sK1(X0,X1,X2),X2) != iProver_top
% 55.39/7.44      | r2_hidden(sK1(X0,X1,X2),X1) != iProver_top ),
% 55.39/7.44      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_2217,plain,
% 55.39/7.44      ( k3_xboole_0(X0,X1) = X2
% 55.39/7.44      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top
% 55.39/7.44      | r2_hidden(sK1(X0,X1,X2),k1_xboole_0) != iProver_top ),
% 55.39/7.44      inference(superposition,[status(thm)],[c_562,c_1983]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_4,plain,
% 55.39/7.44      ( r2_hidden(sK1(X0,X1,X2),X1)
% 55.39/7.44      | r2_hidden(sK1(X0,X1,X2),X2)
% 55.39/7.44      | k3_xboole_0(X0,X1) = X2 ),
% 55.39/7.44      inference(cnf_transformation,[],[f34]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_563,plain,
% 55.39/7.44      ( k3_xboole_0(X0,X1) = X2
% 55.39/7.44      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top
% 55.39/7.44      | r2_hidden(sK1(X0,X1,X2),X1) = iProver_top ),
% 55.39/7.44      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_2242,plain,
% 55.39/7.44      ( k3_xboole_0(X0,X1) = X2
% 55.39/7.44      | r2_hidden(sK1(X0,X1,X2),X1) = iProver_top
% 55.39/7.44      | r2_hidden(sK1(X0,X1,X2),k1_xboole_0) != iProver_top ),
% 55.39/7.44      inference(superposition,[status(thm)],[c_563,c_1983]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_7132,plain,
% 55.39/7.44      ( k3_xboole_0(X0,X1) = X2
% 55.39/7.44      | r2_hidden(sK1(X0,X1,X2),k1_xboole_0) != iProver_top ),
% 55.39/7.44      inference(global_propositional_subsumption,
% 55.39/7.44                [status(thm)],
% 55.39/7.44                [c_2213,c_49,c_2217,c_2242]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_7139,plain,
% 55.39/7.44      ( k3_xboole_0(k1_xboole_0,X0) = X1
% 55.39/7.44      | r2_hidden(sK1(k1_xboole_0,X0,X1),X1) = iProver_top ),
% 55.39/7.44      inference(superposition,[status(thm)],[c_562,c_7132]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_7236,plain,
% 55.39/7.44      ( k3_xboole_0(k1_xboole_0,X0) = sK3
% 55.39/7.44      | r2_hidden(X1,sK5) = iProver_top
% 55.39/7.44      | r2_hidden(X1,sK4) != iProver_top
% 55.39/7.44      | r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK5,sK3)) = iProver_top ),
% 55.39/7.44      inference(superposition,[status(thm)],[c_7139,c_6916]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_7235,plain,
% 55.39/7.44      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 55.39/7.44      inference(superposition,[status(thm)],[c_7139,c_7132]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_7337,plain,
% 55.39/7.44      ( sK3 = k1_xboole_0
% 55.39/7.44      | r2_hidden(X0,sK5) = iProver_top
% 55.39/7.44      | r2_hidden(X0,sK4) != iProver_top
% 55.39/7.44      | r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK5,sK3)) = iProver_top ),
% 55.39/7.44      inference(light_normalisation,[status(thm)],[c_7236,c_7235]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_7478,plain,
% 55.39/7.44      ( r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK5,sK3)) = iProver_top
% 55.39/7.44      | r2_hidden(X0,sK4) != iProver_top
% 55.39/7.44      | r2_hidden(X0,sK5) = iProver_top ),
% 55.39/7.44      inference(global_propositional_subsumption,
% 55.39/7.44                [status(thm)],
% 55.39/7.44                [c_6944,c_18,c_646,c_964,c_7337]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_7479,plain,
% 55.39/7.44      ( r2_hidden(X0,sK5) = iProver_top
% 55.39/7.44      | r2_hidden(X0,sK4) != iProver_top
% 55.39/7.44      | r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK5,sK3)) = iProver_top ),
% 55.39/7.44      inference(renaming,[status(thm)],[c_7478]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_7484,plain,
% 55.39/7.44      ( r2_hidden(X0,sK3) != iProver_top
% 55.39/7.44      | r2_hidden(X1,sK5) = iProver_top
% 55.39/7.44      | r2_hidden(X1,sK4) != iProver_top
% 55.39/7.44      | r2_hidden(X2,sK4) != iProver_top
% 55.39/7.44      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(sK5,sK3)) = iProver_top ),
% 55.39/7.44      inference(superposition,[status(thm)],[c_7479,c_2148]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_15,plain,
% 55.39/7.44      ( r2_hidden(X0,X1)
% 55.39/7.44      | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 55.39/7.44      inference(cnf_transformation,[],[f40]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_552,plain,
% 55.39/7.44      ( r2_hidden(X0,X1) = iProver_top
% 55.39/7.44      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
% 55.39/7.44      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_176966,plain,
% 55.39/7.44      ( r2_hidden(X0,sK3) != iProver_top
% 55.39/7.44      | r2_hidden(X1,sK5) = iProver_top
% 55.39/7.44      | r2_hidden(X2,sK5) = iProver_top
% 55.39/7.44      | r2_hidden(X2,sK4) != iProver_top
% 55.39/7.44      | r2_hidden(X1,sK4) != iProver_top ),
% 55.39/7.44      inference(superposition,[status(thm)],[c_7484,c_552]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_177025,plain,
% 55.39/7.44      ( r2_hidden(X0,sK3) != iProver_top
% 55.39/7.44      | r2_hidden(X1,sK5) = iProver_top
% 55.39/7.44      | r2_hidden(X1,sK4) != iProver_top
% 55.39/7.44      | r2_hidden(sK0(sK4,X2),sK5) = iProver_top
% 55.39/7.44      | r1_tarski(sK4,X2) = iProver_top ),
% 55.39/7.44      inference(superposition,[status(thm)],[c_566,c_176966]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_178008,plain,
% 55.39/7.44      ( r2_hidden(X0,sK5) = iProver_top
% 55.39/7.44      | r2_hidden(X0,sK4) != iProver_top
% 55.39/7.44      | r2_hidden(sK0(sK4,X1),sK5) = iProver_top
% 55.39/7.44      | r1_tarski(sK3,X2) = iProver_top
% 55.39/7.44      | r1_tarski(sK4,X1) = iProver_top ),
% 55.39/7.44      inference(superposition,[status(thm)],[c_566,c_177025]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_0,plain,
% 55.39/7.44      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 55.39/7.44      inference(cnf_transformation,[],[f29]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_567,plain,
% 55.39/7.44      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 55.39/7.44      | r1_tarski(X0,X1) = iProver_top ),
% 55.39/7.44      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_178553,plain,
% 55.39/7.44      ( r2_hidden(X0,sK5) = iProver_top
% 55.39/7.44      | r2_hidden(X0,sK4) != iProver_top
% 55.39/7.44      | r1_tarski(sK3,X1) = iProver_top
% 55.39/7.44      | r1_tarski(sK4,sK5) = iProver_top ),
% 55.39/7.44      inference(superposition,[status(thm)],[c_178008,c_567]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_16,negated_conjecture,
% 55.39/7.44      ( ~ r1_tarski(sK4,sK5) ),
% 55.39/7.44      inference(cnf_transformation,[],[f45]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_20,plain,
% 55.39/7.44      ( r1_tarski(sK4,sK5) != iProver_top ),
% 55.39/7.44      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_178943,plain,
% 55.39/7.44      ( r1_tarski(sK3,X1) = iProver_top
% 55.39/7.44      | r2_hidden(X0,sK4) != iProver_top
% 55.39/7.44      | r2_hidden(X0,sK5) = iProver_top ),
% 55.39/7.44      inference(global_propositional_subsumption,
% 55.39/7.44                [status(thm)],
% 55.39/7.44                [c_178553,c_20]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_178944,plain,
% 55.39/7.44      ( r2_hidden(X0,sK5) = iProver_top
% 55.39/7.44      | r2_hidden(X0,sK4) != iProver_top
% 55.39/7.44      | r1_tarski(sK3,X1) = iProver_top ),
% 55.39/7.44      inference(renaming,[status(thm)],[c_178943]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_178947,plain,
% 55.39/7.44      ( r2_hidden(sK0(sK4,X0),sK5) = iProver_top
% 55.39/7.44      | r1_tarski(sK3,X1) = iProver_top
% 55.39/7.44      | r1_tarski(sK4,X0) = iProver_top ),
% 55.39/7.44      inference(superposition,[status(thm)],[c_566,c_178944]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_179457,plain,
% 55.39/7.44      ( r1_tarski(sK3,X0) = iProver_top
% 55.39/7.44      | r1_tarski(sK4,sK5) = iProver_top ),
% 55.39/7.44      inference(superposition,[status(thm)],[c_178947,c_567]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_179788,plain,
% 55.39/7.44      ( r1_tarski(sK3,X0) = iProver_top ),
% 55.39/7.44      inference(global_propositional_subsumption,
% 55.39/7.44                [status(thm)],
% 55.39/7.44                [c_179457,c_20]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_11,plain,
% 55.39/7.44      ( r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),X0) ),
% 55.39/7.44      inference(cnf_transformation,[],[f36]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_556,plain,
% 55.39/7.44      ( r1_xboole_0(X0,X1) = iProver_top
% 55.39/7.44      | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
% 55.39/7.44      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_1750,plain,
% 55.39/7.44      ( r1_xboole_0(X0,X1) = iProver_top
% 55.39/7.44      | r2_hidden(sK2(X0,X1),X2) = iProver_top
% 55.39/7.44      | r1_tarski(X0,X2) != iProver_top ),
% 55.39/7.44      inference(superposition,[status(thm)],[c_556,c_565]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_10,plain,
% 55.39/7.44      ( r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),X1) ),
% 55.39/7.44      inference(cnf_transformation,[],[f37]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_557,plain,
% 55.39/7.44      ( r1_xboole_0(X0,X1) = iProver_top
% 55.39/7.44      | r2_hidden(sK2(X0,X1),X1) = iProver_top ),
% 55.39/7.44      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_1987,plain,
% 55.39/7.44      ( r1_xboole_0(X0,X1) = iProver_top
% 55.39/7.44      | r2_hidden(sK2(X0,X1),k1_xboole_0) != iProver_top ),
% 55.39/7.44      inference(superposition,[status(thm)],[c_557,c_1983]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_3916,plain,
% 55.39/7.44      ( r1_xboole_0(X0,X1) = iProver_top
% 55.39/7.44      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 55.39/7.44      inference(superposition,[status(thm)],[c_1750,c_1987]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_179808,plain,
% 55.39/7.44      ( r1_xboole_0(sK3,X0) = iProver_top ),
% 55.39/7.44      inference(superposition,[status(thm)],[c_179788,c_3916]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_179842,plain,
% 55.39/7.44      ( r1_xboole_0(sK3,sK3) = iProver_top ),
% 55.39/7.44      inference(instantiation,[status(thm)],[c_179808]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_171596,plain,
% 55.39/7.44      ( ~ r1_xboole_0(X0,X1)
% 55.39/7.44      | ~ r2_hidden(sK1(X2,X0,k1_xboole_0),X1)
% 55.39/7.44      | ~ r2_hidden(sK1(X2,X0,k1_xboole_0),X0) ),
% 55.39/7.44      inference(instantiation,[status(thm)],[c_9]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_171597,plain,
% 55.39/7.44      ( r1_xboole_0(X0,X1) != iProver_top
% 55.39/7.44      | r2_hidden(sK1(X2,X0,k1_xboole_0),X1) != iProver_top
% 55.39/7.44      | r2_hidden(sK1(X2,X0,k1_xboole_0),X0) != iProver_top ),
% 55.39/7.44      inference(predicate_to_equality,[status(thm)],[c_171596]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_171599,plain,
% 55.39/7.44      ( r1_xboole_0(sK3,sK3) != iProver_top
% 55.39/7.44      | r2_hidden(sK1(sK3,sK3,k1_xboole_0),sK3) != iProver_top ),
% 55.39/7.44      inference(instantiation,[status(thm)],[c_171597]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_647,plain,
% 55.39/7.44      ( X0 != X1 | k1_xboole_0 != X1 | k1_xboole_0 = X0 ),
% 55.39/7.44      inference(instantiation,[status(thm)],[c_249]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_7154,plain,
% 55.39/7.44      ( X0 != k3_xboole_0(X1,X2)
% 55.39/7.44      | k1_xboole_0 = X0
% 55.39/7.44      | k1_xboole_0 != k3_xboole_0(X1,X2) ),
% 55.39/7.44      inference(instantiation,[status(thm)],[c_647]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_7155,plain,
% 55.39/7.44      ( sK3 != k3_xboole_0(sK3,sK3)
% 55.39/7.44      | k1_xboole_0 != k3_xboole_0(sK3,sK3)
% 55.39/7.44      | k1_xboole_0 = sK3 ),
% 55.39/7.44      inference(instantiation,[status(thm)],[c_7154]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_7140,plain,
% 55.39/7.44      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 55.39/7.44      | r2_hidden(sK1(X0,X1,k1_xboole_0),X1) = iProver_top ),
% 55.39/7.44      inference(superposition,[status(thm)],[c_563,c_7132]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_7149,plain,
% 55.39/7.44      ( k3_xboole_0(sK3,sK3) = k1_xboole_0
% 55.39/7.44      | r2_hidden(sK1(sK3,sK3,k1_xboole_0),sK3) = iProver_top ),
% 55.39/7.44      inference(instantiation,[status(thm)],[c_7140]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_6085,plain,
% 55.39/7.44      ( X0 != X1 | X0 = k3_xboole_0(X2,X3) | k3_xboole_0(X2,X3) != X1 ),
% 55.39/7.44      inference(instantiation,[status(thm)],[c_249]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_6086,plain,
% 55.39/7.44      ( k3_xboole_0(sK3,sK3) != sK3
% 55.39/7.44      | sK3 = k3_xboole_0(sK3,sK3)
% 55.39/7.44      | sK3 != sK3 ),
% 55.39/7.44      inference(instantiation,[status(thm)],[c_6085]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_867,plain,
% 55.39/7.44      ( X0 != k1_xboole_0
% 55.39/7.44      | k1_xboole_0 = X0
% 55.39/7.44      | k1_xboole_0 != k1_xboole_0 ),
% 55.39/7.44      inference(instantiation,[status(thm)],[c_647]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_2013,plain,
% 55.39/7.44      ( k3_xboole_0(X0,X1) != k1_xboole_0
% 55.39/7.44      | k1_xboole_0 = k3_xboole_0(X0,X1)
% 55.39/7.44      | k1_xboole_0 != k1_xboole_0 ),
% 55.39/7.44      inference(instantiation,[status(thm)],[c_867]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_2014,plain,
% 55.39/7.44      ( k3_xboole_0(sK3,sK3) != k1_xboole_0
% 55.39/7.44      | k1_xboole_0 = k3_xboole_0(sK3,sK3)
% 55.39/7.44      | k1_xboole_0 != k1_xboole_0 ),
% 55.39/7.44      inference(instantiation,[status(thm)],[c_2013]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_259,plain,
% 55.39/7.44      ( sK3 = sK3 ),
% 55.39/7.44      inference(instantiation,[status(thm)],[c_248]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_50,plain,
% 55.39/7.44      ( ~ r2_hidden(sK1(sK3,sK3,sK3),sK3) | k3_xboole_0(sK3,sK3) = sK3 ),
% 55.39/7.44      inference(instantiation,[status(thm)],[c_3]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(c_46,plain,
% 55.39/7.44      ( r2_hidden(sK1(sK3,sK3,sK3),sK3) | k3_xboole_0(sK3,sK3) = sK3 ),
% 55.39/7.44      inference(instantiation,[status(thm)],[c_5]) ).
% 55.39/7.44  
% 55.39/7.44  cnf(contradiction,plain,
% 55.39/7.44      ( $false ),
% 55.39/7.44      inference(minisat,
% 55.39/7.44                [status(thm)],
% 55.39/7.44                [c_179842,c_171599,c_7155,c_7149,c_6086,c_2014,c_964,
% 55.39/7.44                 c_259,c_50,c_46,c_18]) ).
% 55.39/7.44  
% 55.39/7.44  
% 55.39/7.44  % SZS output end CNFRefutation for theBenchmark.p
% 55.39/7.44  
% 55.39/7.44  ------                               Statistics
% 55.39/7.44  
% 55.39/7.44  ------ General
% 55.39/7.44  
% 55.39/7.44  abstr_ref_over_cycles:                  0
% 55.39/7.44  abstr_ref_under_cycles:                 0
% 55.39/7.44  gc_basic_clause_elim:                   0
% 55.39/7.44  forced_gc_time:                         0
% 55.39/7.44  parsing_time:                           0.011
% 55.39/7.44  unif_index_cands_time:                  0.
% 55.39/7.44  unif_index_add_time:                    0.
% 55.39/7.44  orderings_time:                         0.
% 55.39/7.44  out_proof_time:                         0.041
% 55.39/7.44  total_time:                             6.765
% 55.39/7.44  num_of_symbols:                         44
% 55.39/7.44  num_of_terms:                           202370
% 55.39/7.44  
% 55.39/7.44  ------ Preprocessing
% 55.39/7.44  
% 55.39/7.44  num_of_splits:                          0
% 55.39/7.44  num_of_split_atoms:                     0
% 55.39/7.44  num_of_reused_defs:                     0
% 55.39/7.44  num_eq_ax_congr_red:                    24
% 55.39/7.44  num_of_sem_filtered_clauses:            1
% 55.39/7.44  num_of_subtypes:                        0
% 55.39/7.44  monotx_restored_types:                  0
% 55.39/7.44  sat_num_of_epr_types:                   0
% 55.39/7.44  sat_num_of_non_cyclic_types:            0
% 55.39/7.44  sat_guarded_non_collapsed_types:        0
% 55.39/7.44  num_pure_diseq_elim:                    0
% 55.39/7.44  simp_replaced_by:                       0
% 55.39/7.44  res_preprocessed:                       70
% 55.39/7.44  prep_upred:                             0
% 55.39/7.44  prep_unflattend:                        2
% 55.39/7.44  smt_new_axioms:                         0
% 55.39/7.44  pred_elim_cands:                        3
% 55.39/7.44  pred_elim:                              0
% 55.39/7.44  pred_elim_cl:                           0
% 55.39/7.44  pred_elim_cycles:                       1
% 55.39/7.44  merged_defs:                            0
% 55.39/7.44  merged_defs_ncl:                        0
% 55.39/7.44  bin_hyper_res:                          0
% 55.39/7.44  prep_cycles:                            3
% 55.39/7.44  pred_elim_time:                         0.001
% 55.39/7.44  splitting_time:                         0.
% 55.39/7.44  sem_filter_time:                        0.
% 55.39/7.44  monotx_time:                            0.001
% 55.39/7.44  subtype_inf_time:                       0.
% 55.39/7.44  
% 55.39/7.44  ------ Problem properties
% 55.39/7.44  
% 55.39/7.44  clauses:                                19
% 55.39/7.44  conjectures:                            3
% 55.39/7.44  epr:                                    5
% 55.39/7.44  horn:                                   13
% 55.39/7.44  ground:                                 3
% 55.39/7.44  unary:                                  3
% 55.39/7.44  binary:                                 9
% 55.39/7.44  lits:                                   43
% 55.39/7.44  lits_eq:                                4
% 55.39/7.44  fd_pure:                                0
% 55.39/7.44  fd_pseudo:                              0
% 55.39/7.44  fd_cond:                                0
% 55.39/7.44  fd_pseudo_cond:                         3
% 55.39/7.44  ac_symbols:                             0
% 55.39/7.44  
% 55.39/7.44  ------ Propositional Solver
% 55.39/7.44  
% 55.39/7.44  prop_solver_calls:                      96
% 55.39/7.44  prop_fast_solver_calls:                 4068
% 55.39/7.44  smt_solver_calls:                       0
% 55.39/7.44  smt_fast_solver_calls:                  0
% 55.39/7.44  prop_num_of_clauses:                    95783
% 55.39/7.44  prop_preprocess_simplified:             167586
% 55.39/7.44  prop_fo_subsumed:                       1426
% 55.39/7.44  prop_solver_time:                       0.
% 55.39/7.44  smt_solver_time:                        0.
% 55.39/7.44  smt_fast_solver_time:                   0.
% 55.39/7.44  prop_fast_solver_time:                  0.
% 55.39/7.44  prop_unsat_core_time:                   0.014
% 55.39/7.44  
% 55.39/7.44  ------ QBF
% 55.39/7.44  
% 55.39/7.44  qbf_q_res:                              0
% 55.39/7.44  qbf_num_tautologies:                    0
% 55.39/7.44  qbf_prep_cycles:                        0
% 55.39/7.44  
% 55.39/7.44  ------ BMC1
% 55.39/7.44  
% 55.39/7.44  bmc1_current_bound:                     -1
% 55.39/7.44  bmc1_last_solved_bound:                 -1
% 55.39/7.44  bmc1_unsat_core_size:                   -1
% 55.39/7.44  bmc1_unsat_core_parents_size:           -1
% 55.39/7.44  bmc1_merge_next_fun:                    0
% 55.39/7.44  bmc1_unsat_core_clauses_time:           0.
% 55.39/7.44  
% 55.39/7.44  ------ Instantiation
% 55.39/7.44  
% 55.39/7.44  inst_num_of_clauses:                    22668
% 55.39/7.44  inst_num_in_passive:                    17497
% 55.39/7.44  inst_num_in_active:                     1740
% 55.39/7.44  inst_num_in_unprocessed:                3432
% 55.39/7.44  inst_num_of_loops:                      2100
% 55.39/7.44  inst_num_of_learning_restarts:          0
% 55.39/7.44  inst_num_moves_active_passive:          357
% 55.39/7.44  inst_lit_activity:                      0
% 55.39/7.44  inst_lit_activity_moves:                3
% 55.39/7.44  inst_num_tautologies:                   0
% 55.39/7.44  inst_num_prop_implied:                  0
% 55.39/7.44  inst_num_existing_simplified:           0
% 55.39/7.44  inst_num_eq_res_simplified:             0
% 55.39/7.44  inst_num_child_elim:                    0
% 55.39/7.44  inst_num_of_dismatching_blockings:      25822
% 55.39/7.44  inst_num_of_non_proper_insts:           12411
% 55.39/7.44  inst_num_of_duplicates:                 0
% 55.39/7.44  inst_inst_num_from_inst_to_res:         0
% 55.39/7.44  inst_dismatching_checking_time:         0.
% 55.39/7.44  
% 55.39/7.44  ------ Resolution
% 55.39/7.44  
% 55.39/7.44  res_num_of_clauses:                     0
% 55.39/7.44  res_num_in_passive:                     0
% 55.39/7.44  res_num_in_active:                      0
% 55.39/7.44  res_num_of_loops:                       73
% 55.39/7.44  res_forward_subset_subsumed:            154
% 55.39/7.44  res_backward_subset_subsumed:           2
% 55.39/7.44  res_forward_subsumed:                   0
% 55.39/7.44  res_backward_subsumed:                  0
% 55.39/7.44  res_forward_subsumption_resolution:     0
% 55.39/7.44  res_backward_subsumption_resolution:    0
% 55.39/7.44  res_clause_to_clause_subsumption:       161010
% 55.39/7.44  res_orphan_elimination:                 0
% 55.39/7.44  res_tautology_del:                      81
% 55.39/7.44  res_num_eq_res_simplified:              0
% 55.39/7.44  res_num_sel_changes:                    0
% 55.39/7.44  res_moves_from_active_to_pass:          0
% 55.39/7.44  
% 55.39/7.44  ------ Superposition
% 55.39/7.44  
% 55.39/7.44  sup_time_total:                         0.
% 55.39/7.44  sup_time_generating:                    0.
% 55.39/7.44  sup_time_sim_full:                      0.
% 55.39/7.44  sup_time_sim_immed:                     0.
% 55.39/7.44  
% 55.39/7.44  sup_num_of_clauses:                     4603
% 55.39/7.44  sup_num_in_active:                      350
% 55.39/7.44  sup_num_in_passive:                     4253
% 55.39/7.44  sup_num_of_loops:                       418
% 55.39/7.44  sup_fw_superposition:                   4611
% 55.39/7.44  sup_bw_superposition:                   4103
% 55.39/7.44  sup_immediate_simplified:               1768
% 55.39/7.44  sup_given_eliminated:                   8
% 55.39/7.44  comparisons_done:                       0
% 55.39/7.44  comparisons_avoided:                    0
% 55.39/7.44  
% 55.39/7.44  ------ Simplifications
% 55.39/7.44  
% 55.39/7.44  
% 55.39/7.44  sim_fw_subset_subsumed:                 90
% 55.39/7.44  sim_bw_subset_subsumed:                 43
% 55.39/7.44  sim_fw_subsumed:                        720
% 55.39/7.44  sim_bw_subsumed:                        205
% 55.39/7.44  sim_fw_subsumption_res:                 0
% 55.39/7.44  sim_bw_subsumption_res:                 0
% 55.39/7.44  sim_tautology_del:                      22
% 55.39/7.44  sim_eq_tautology_del:                   192
% 55.39/7.44  sim_eq_res_simp:                        16
% 55.39/7.44  sim_fw_demodulated:                     1175
% 55.39/7.44  sim_bw_demodulated:                     13
% 55.39/7.44  sim_light_normalised:                   101
% 55.39/7.44  sim_joinable_taut:                      0
% 55.39/7.44  sim_joinable_simp:                      0
% 55.39/7.44  sim_ac_normalised:                      0
% 55.39/7.44  sim_smt_subsumption:                    0
% 55.39/7.44  
%------------------------------------------------------------------------------
