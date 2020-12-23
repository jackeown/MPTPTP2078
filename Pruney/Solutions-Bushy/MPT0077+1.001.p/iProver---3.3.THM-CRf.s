%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0077+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:25 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 311 expanded)
%              Number of clauses        :   56 (  99 expanded)
%              Number of leaves         :    7 (  67 expanded)
%              Depth                    :   14
%              Number of atoms          :  291 (1565 expanded)
%              Number of equality atoms :   80 ( 173 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
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

fof(f7,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f7,f14])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f11,plain,(
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
    inference(rectify,[],[f10])).

fof(f12,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & ~ r2_hidden(sK0(X0,X1,X2),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( r2_hidden(sK0(X0,X1,X2),X1)
          | r2_hidden(sK0(X0,X1,X2),X0)
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & ~ r2_hidden(sK0(X0,X1,X2),X0) )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( r2_hidden(sK0(X0,X1,X2),X1)
            | r2_hidden(sK0(X0,X1,X2),X0)
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f12])).

fof(f20,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f20])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
            & ~ ( r1_xboole_0(X0,X2)
                & r1_xboole_0(X0,X1) ) )
        & ~ ( r1_xboole_0(X0,X2)
            & r1_xboole_0(X0,X1)
            & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
        & ( ~ r1_xboole_0(X0,X2)
          | ~ r1_xboole_0(X0,X1) ) )
      | ( r1_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ( ~ r1_xboole_0(X0,X2)
            | ~ r1_xboole_0(X0,X1) ) )
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) )
   => ( ( r1_xboole_0(sK2,k2_xboole_0(sK3,sK4))
        & ( ~ r1_xboole_0(sK2,sK4)
          | ~ r1_xboole_0(sK2,sK3) ) )
      | ( r1_xboole_0(sK2,sK4)
        & r1_xboole_0(sK2,sK3)
        & ~ r1_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ( r1_xboole_0(sK2,k2_xboole_0(sK3,sK4))
      & ( ~ r1_xboole_0(sK2,sK4)
        | ~ r1_xboole_0(sK2,sK3) ) )
    | ( r1_xboole_0(sK2,sK4)
      & r1_xboole_0(sK2,sK3)
      & ~ r1_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f8,f16])).

fof(f32,plain,
    ( r1_xboole_0(sK2,k2_xboole_0(sK3,sK4))
    | r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f21,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f21])).

fof(f33,plain,
    ( r1_xboole_0(sK2,k2_xboole_0(sK3,sK4))
    | r1_xboole_0(sK2,sK4) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f19])).

fof(f28,plain,
    ( ~ r1_xboole_0(sK2,sK4)
    | ~ r1_xboole_0(sK2,sK3)
    | ~ r1_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_761,plain,
    ( ~ r1_xboole_0(X0,sK2)
    | ~ r2_hidden(sK1(sK2,k2_xboole_0(sK3,sK4)),X0)
    | ~ r2_hidden(sK1(sK2,k2_xboole_0(sK3,sK4)),sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_16406,plain,
    ( ~ r1_xboole_0(sK3,sK2)
    | ~ r2_hidden(sK1(sK2,k2_xboole_0(sK3,sK4)),sK3)
    | ~ r2_hidden(sK1(sK2,k2_xboole_0(sK3,sK4)),sK2) ),
    inference(instantiation,[status(thm)],[c_761])).

cnf(c_16402,plain,
    ( ~ r1_xboole_0(sK4,sK2)
    | ~ r2_hidden(sK1(sK2,k2_xboole_0(sK3,sK4)),sK4)
    | ~ r2_hidden(sK1(sK2,k2_xboole_0(sK3,sK4)),sK2) ),
    inference(instantiation,[status(thm)],[c_761])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_449,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_450,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_453,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_11,negated_conjecture,
    ( r1_xboole_0(sK2,k2_xboole_0(sK3,sK4))
    | r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_447,plain,
    ( r1_xboole_0(sK2,k2_xboole_0(sK3,sK4)) = iProver_top
    | r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_451,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_701,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top
    | r2_hidden(X0,k2_xboole_0(sK3,sK4)) != iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_447,c_451])).

cnf(c_1036,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_453,c_701])).

cnf(c_1230,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1036,c_451])).

cnf(c_1234,plain,
    ( r1_xboole_0(X0,sK2) = iProver_top
    | r2_hidden(sK1(X0,sK2),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_450,c_1230])).

cnf(c_6643,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_449,c_1234])).

cnf(c_6682,plain,
    ( r1_xboole_0(sK3,sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6643])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_454,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_10,negated_conjecture,
    ( r1_xboole_0(sK2,k2_xboole_0(sK3,sK4))
    | r1_xboole_0(sK2,sK4) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_448,plain,
    ( r1_xboole_0(sK2,k2_xboole_0(sK3,sK4)) = iProver_top
    | r1_xboole_0(sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_700,plain,
    ( r1_xboole_0(sK2,sK4) = iProver_top
    | r2_hidden(X0,k2_xboole_0(sK3,sK4)) != iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_448,c_451])).

cnf(c_873,plain,
    ( r1_xboole_0(sK2,sK4) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_454,c_700])).

cnf(c_1077,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_873,c_451])).

cnf(c_1082,plain,
    ( r1_xboole_0(sK2,X0) = iProver_top
    | r2_hidden(sK1(sK2,X0),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_449,c_1077])).

cnf(c_5205,plain,
    ( r1_xboole_0(sK2,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_450,c_1082])).

cnf(c_5244,plain,
    ( r1_xboole_0(sK2,sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5205])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_452,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_726,plain,
    ( r1_xboole_0(X0,k2_xboole_0(X1,X2)) = iProver_top
    | r2_hidden(sK1(X0,k2_xboole_0(X1,X2)),X2) = iProver_top
    | r2_hidden(sK1(X0,k2_xboole_0(X1,X2)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_450,c_452])).

cnf(c_2282,plain,
    ( r1_xboole_0(X0,k2_xboole_0(X1,X2)) = iProver_top
    | r2_hidden(sK1(X0,k2_xboole_0(X2,X1)),X1) = iProver_top
    | r2_hidden(sK1(X0,k2_xboole_0(X1,X2)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_726])).

cnf(c_2599,plain,
    ( r1_xboole_0(X0,k2_xboole_0(k2_xboole_0(sK3,sK4),X1)) = iProver_top
    | r1_xboole_0(sK2,sK3) = iProver_top
    | r2_hidden(sK1(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK4))),sK2) != iProver_top
    | r2_hidden(sK1(X0,k2_xboole_0(k2_xboole_0(sK3,sK4),X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2282,c_701])).

cnf(c_20,plain,
    ( r1_xboole_0(sK2,k2_xboole_0(sK3,sK4)) = iProver_top
    | r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_613,plain,
    ( r1_xboole_0(sK2,sK3)
    | r2_hidden(sK1(sK2,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_614,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top
    | r2_hidden(sK1(sK2,sK3),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_613])).

cnf(c_612,plain,
    ( r1_xboole_0(sK2,sK3)
    | r2_hidden(sK1(sK2,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_616,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top
    | r2_hidden(sK1(sK2,sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_612])).

cnf(c_1168,plain,
    ( ~ r1_xboole_0(X0,k2_xboole_0(sK3,X1))
    | ~ r2_hidden(sK1(sK2,sK3),X0)
    | ~ r2_hidden(sK1(sK2,sK3),k2_xboole_0(sK3,X1)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2241,plain,
    ( ~ r1_xboole_0(sK2,k2_xboole_0(sK3,sK4))
    | ~ r2_hidden(sK1(sK2,sK3),k2_xboole_0(sK3,sK4))
    | ~ r2_hidden(sK1(sK2,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_1168])).

cnf(c_2242,plain,
    ( r1_xboole_0(sK2,k2_xboole_0(sK3,sK4)) != iProver_top
    | r2_hidden(sK1(sK2,sK3),k2_xboole_0(sK3,sK4)) != iProver_top
    | r2_hidden(sK1(sK2,sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2241])).

cnf(c_642,plain,
    ( r2_hidden(sK1(sK2,sK3),k2_xboole_0(sK3,X0))
    | ~ r2_hidden(sK1(sK2,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3887,plain,
    ( r2_hidden(sK1(sK2,sK3),k2_xboole_0(sK3,sK4))
    | ~ r2_hidden(sK1(sK2,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_642])).

cnf(c_3888,plain,
    ( r2_hidden(sK1(sK2,sK3),k2_xboole_0(sK3,sK4)) = iProver_top
    | r2_hidden(sK1(sK2,sK3),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3887])).

cnf(c_3913,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2599,c_20,c_614,c_616,c_2242,c_3888])).

cnf(c_3915,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3913])).

cnf(c_1081,plain,
    ( r1_xboole_0(X0,sK2) = iProver_top
    | r2_hidden(sK1(X0,sK2),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_450,c_1077])).

cnf(c_1665,plain,
    ( r1_xboole_0(sK4,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_449,c_1081])).

cnf(c_1666,plain,
    ( r1_xboole_0(sK4,sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1665])).

cnf(c_781,plain,
    ( ~ r2_hidden(sK1(sK2,k2_xboole_0(sK3,sK4)),k2_xboole_0(sK3,sK4))
    | r2_hidden(sK1(sK2,k2_xboole_0(sK3,sK4)),sK4)
    | r2_hidden(sK1(sK2,k2_xboole_0(sK3,sK4)),sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_669,plain,
    ( r1_xboole_0(sK2,k2_xboole_0(sK3,sK4))
    | r2_hidden(sK1(sK2,k2_xboole_0(sK3,sK4)),sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_670,plain,
    ( r1_xboole_0(sK2,k2_xboole_0(sK3,sK4))
    | r2_hidden(sK1(sK2,k2_xboole_0(sK3,sK4)),k2_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_15,negated_conjecture,
    ( ~ r1_xboole_0(sK2,k2_xboole_0(sK3,sK4))
    | ~ r1_xboole_0(sK2,sK4)
    | ~ r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16406,c_16402,c_6682,c_5244,c_3915,c_1666,c_781,c_669,c_670,c_15])).


%------------------------------------------------------------------------------
