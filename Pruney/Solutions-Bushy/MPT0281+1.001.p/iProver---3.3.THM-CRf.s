%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0281+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:55 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 602 expanded)
%              Number of clauses        :   61 ( 192 expanded)
%              Number of leaves         :    8 ( 112 expanded)
%              Depth                    :   27
%              Number of atoms          :  312 (2806 expanded)
%              Number of equality atoms :  127 ( 744 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f10])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f40,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f13,plain,(
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
    inference(rectify,[],[f12])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK0(X0,X1),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( r1_tarski(sK0(X0,X1),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK0(X0,X1),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r1_tarski(sK0(X0,X1),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f14])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( k1_zfmisc_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
     => r3_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_zfmisc_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
       => r3_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ~ r3_xboole_0(X0,X1)
      & k1_zfmisc_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( ~ r3_xboole_0(X0,X1)
        & k1_zfmisc_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) )
   => ( ~ r3_xboole_0(sK2,sK3)
      & k1_zfmisc_1(k2_xboole_0(sK2,sK3)) = k2_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ~ r3_xboole_0(sK2,sK3)
    & k1_zfmisc_1(k2_xboole_0(sK2,sK3)) = k2_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f9,f21])).

fof(f38,plain,(
    k1_zfmisc_1(k2_xboole_0(sK2,sK3)) = k2_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f16])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & ~ r2_hidden(sK1(X0,X1,X2),X0) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( r2_hidden(sK1(X0,X1,X2),X1)
          | r2_hidden(sK1(X0,X1,X2),X0)
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & ~ r2_hidden(sK1(X0,X1,X2),X0) )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( r2_hidden(sK1(X0,X1,X2),X1)
            | r2_hidden(sK1(X0,X1,X2),X0)
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f19])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f46,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f25,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f44,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f32])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f41,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f23])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f45,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
    <=> ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) )
     => r3_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ( ~ r1_tarski(X1,X0)
        & ~ r1_tarski(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f39,plain,(
    ~ r3_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f8])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_704,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_701,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_16,negated_conjecture,
    ( k1_zfmisc_1(k2_xboole_0(sK2,sK3)) = k2_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_12,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_694,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1031,plain,
    ( r2_hidden(X0,k1_zfmisc_1(k2_xboole_0(sK2,sK3))) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(sK3)) = iProver_top
    | r2_hidden(X0,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_694])).

cnf(c_1379,plain,
    ( r2_hidden(X0,k1_zfmisc_1(sK3)) = iProver_top
    | r2_hidden(X0,k1_zfmisc_1(sK2)) = iProver_top
    | r1_tarski(X0,k2_xboole_0(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_701,c_1031])).

cnf(c_1479,plain,
    ( r2_hidden(k2_xboole_0(sK2,sK3),k1_zfmisc_1(sK3)) = iProver_top
    | r2_hidden(k2_xboole_0(sK2,sK3),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_704,c_1379])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_700,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2043,plain,
    ( r2_hidden(k2_xboole_0(sK2,sK3),k1_zfmisc_1(sK2)) = iProver_top
    | r1_tarski(k2_xboole_0(sK2,sK3),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1479,c_700])).

cnf(c_2048,plain,
    ( r1_tarski(k2_xboole_0(sK2,sK3),sK3) = iProver_top
    | r1_tarski(k2_xboole_0(sK2,sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2043,c_700])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_705,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3643,plain,
    ( k2_xboole_0(sK2,sK3) = sK3
    | r1_tarski(k2_xboole_0(sK2,sK3),sK2) = iProver_top
    | r1_tarski(sK3,k2_xboole_0(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2048,c_705])).

cnf(c_970,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_973,plain,
    ( r1_tarski(sK3,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_970])).

cnf(c_1550,plain,
    ( r2_hidden(X0,k1_zfmisc_1(sK3))
    | ~ r1_tarski(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3007,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK3))
    | ~ r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_1550])).

cnf(c_3008,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK3)) = iProver_top
    | r1_tarski(sK3,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3007])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_696,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1096,plain,
    ( r2_hidden(X0,k1_zfmisc_1(k2_xboole_0(sK2,sK3))) = iProver_top
    | r2_hidden(X0,k1_zfmisc_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_696])).

cnf(c_1165,plain,
    ( r2_hidden(X0,k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(X0,k2_xboole_0(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1096,c_700])).

cnf(c_1471,plain,
    ( k2_xboole_0(sK2,sK3) = X0
    | r2_hidden(X0,k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(k2_xboole_0(sK2,sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1165,c_705])).

cnf(c_3644,plain,
    ( k2_xboole_0(sK2,sK3) = sK3
    | r2_hidden(sK3,k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(k2_xboole_0(sK2,sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2048,c_1471])).

cnf(c_3854,plain,
    ( r1_tarski(k2_xboole_0(sK2,sK3),sK2) = iProver_top
    | k2_xboole_0(sK2,sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3643,c_973,c_3008,c_3644])).

cnf(c_3855,plain,
    ( k2_xboole_0(sK2,sK3) = sK3
    | r1_tarski(k2_xboole_0(sK2,sK3),sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_3854])).

cnf(c_3860,plain,
    ( k2_xboole_0(sK2,sK3) = sK3
    | k2_xboole_0(sK2,sK3) = sK2
    | r1_tarski(sK2,k2_xboole_0(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3855,c_705])).

cnf(c_39,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_41,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK2)) = iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_48,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_50,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_48])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_695,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1022,plain,
    ( r2_hidden(X0,k1_zfmisc_1(k2_xboole_0(sK2,sK3))) = iProver_top
    | r2_hidden(X0,k1_zfmisc_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_695])).

cnf(c_1108,plain,
    ( r2_hidden(X0,k1_zfmisc_1(sK2)) != iProver_top
    | r1_tarski(X0,k2_xboole_0(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1022,c_700])).

cnf(c_1110,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK2)) != iProver_top
    | r1_tarski(sK2,k2_xboole_0(sK2,sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1108])).

cnf(c_3885,plain,
    ( k2_xboole_0(sK2,sK3) = sK2
    | k2_xboole_0(sK2,sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3860,c_41,c_50,c_1110])).

cnf(c_3886,plain,
    ( k2_xboole_0(sK2,sK3) = sK3
    | k2_xboole_0(sK2,sK3) = sK2 ),
    inference(renaming,[status(thm)],[c_3885])).

cnf(c_3891,plain,
    ( k2_xboole_0(sK2,sK3) = sK2
    | r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3886,c_695])).

cnf(c_14,plain,
    ( r3_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_15,negated_conjecture,
    ( ~ r3_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_211,plain,
    ( ~ r1_tarski(X0,X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_15])).

cnf(c_212,plain,
    ( ~ r1_tarski(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_211])).

cnf(c_213,plain,
    ( r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_212])).

cnf(c_3911,plain,
    ( k2_xboole_0(sK2,sK3) = sK2
    | r2_hidden(X0,k1_zfmisc_1(sK2)) != iProver_top
    | r1_tarski(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3886,c_1108])).

cnf(c_4104,plain,
    ( k2_xboole_0(sK2,sK3) = sK2
    | r2_hidden(sK2,k1_zfmisc_1(sK2)) != iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3911])).

cnf(c_4220,plain,
    ( k2_xboole_0(sK2,sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3891,c_41,c_50,c_213,c_4104])).

cnf(c_4242,plain,
    ( r2_hidden(X0,k1_zfmisc_1(sK3)) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4220,c_1096])).

cnf(c_4531,plain,
    ( r2_hidden(X0,k1_zfmisc_1(sK2)) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_701,c_4242])).

cnf(c_5466,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4531,c_700])).

cnf(c_5502,plain,
    ( r1_tarski(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_704,c_5466])).

cnf(c_13,plain,
    ( r3_xboole_0(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_218,plain,
    ( ~ r1_tarski(X0,X1)
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_15])).

cnf(c_219,plain,
    ( ~ r1_tarski(sK3,sK2) ),
    inference(unflattening,[status(thm)],[c_218])).

cnf(c_220,plain,
    ( r1_tarski(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_219])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5502,c_220])).


%------------------------------------------------------------------------------
