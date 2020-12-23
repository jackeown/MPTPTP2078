%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0003+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:10 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 295 expanded)
%              Number of clauses        :   37 (  80 expanded)
%              Number of leaves         :   11 (  73 expanded)
%              Depth                    :   15
%              Number of atoms          :  255 (1323 expanded)
%              Number of equality atoms :   61 ( 204 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).

fof(f79,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f28,conjecture,(
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

fof(f29,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ ( r1_xboole_0(X0,X1)
            & ? [X2] :
                ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) ) )
        & ~ ( ! [X2] :
                ~ ( r2_hidden(X2,X1)
                  & r2_hidden(X2,X0) )
            & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f32,plain,(
    ~ ! [X0,X1] :
        ( ~ ( r1_xboole_0(X0,X1)
            & ? [X2] :
                ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) ) )
        & ~ ( ! [X3] :
                ~ ( r2_hidden(X3,X1)
                  & r2_hidden(X3,X0) )
            & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f39,plain,(
    ? [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        & ? [X2] :
            ( r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      | ( ! [X3] :
            ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( r2_hidden(sK10,X1)
        & r2_hidden(sK10,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,
    ( ? [X0,X1] :
        ( ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
        | ( ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) )
   => ( ( r1_xboole_0(sK8,sK9)
        & ? [X2] :
            ( r2_hidden(X2,sK9)
            & r2_hidden(X2,sK8) ) )
      | ( ! [X3] :
            ( ~ r2_hidden(X3,sK9)
            | ~ r2_hidden(X3,sK8) )
        & ~ r1_xboole_0(sK8,sK9) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,
    ( ( r1_xboole_0(sK8,sK9)
      & r2_hidden(sK10,sK9)
      & r2_hidden(sK10,sK8) )
    | ( ! [X3] :
          ( ~ r2_hidden(X3,sK9)
          | ~ r2_hidden(X3,sK8) )
      & ~ r1_xboole_0(sK8,sK9) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f39,f72,f71])).

fof(f125,plain,(
    ! [X3] :
      ( r1_xboole_0(sK8,sK9)
      | ~ r2_hidden(X3,sK9)
      | ~ r2_hidden(X3,sK8) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f18,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f103,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f129,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f103,f80])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f101,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f127,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != o_0_0_xboole_0 ) ),
    inference(definition_unfolding,[],[f101,f80])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f51,plain,(
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
    inference(rectify,[],[f50])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f51,f52])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f128,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = o_0_0_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f100,f80])).

fof(f78,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f122,plain,
    ( r2_hidden(sK10,sK9)
    | ~ r1_xboole_0(sK8,sK9) ),
    inference(cnf_transformation,[],[f73])).

fof(f89,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f142,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f89])).

fof(f17,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f102,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f120,plain,
    ( r2_hidden(sK10,sK8)
    | ~ r1_xboole_0(sK8,sK9) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1914,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_44,negated_conjecture,
    ( r1_xboole_0(sK8,sK9)
    | ~ r2_hidden(X0,sK9)
    | ~ r2_hidden(X0,sK8) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_1877,plain,
    ( r1_xboole_0(sK8,sK9) = iProver_top
    | r2_hidden(X0,sK9) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_3452,plain,
    ( r1_xboole_0(sK8,sK9) = iProver_top
    | r2_hidden(sK0(sK9),sK8) != iProver_top
    | v1_xboole_0(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_1914,c_1877])).

cnf(c_27,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_24,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f127])).

cnf(c_1967,plain,
    ( r1_xboole_0(sK8,sK9)
    | k3_xboole_0(sK8,sK9) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_1968,plain,
    ( k3_xboole_0(sK8,sK9) != o_0_0_xboole_0
    | r1_xboole_0(sK8,sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1967])).

cnf(c_14,plain,
    ( r2_hidden(sK2(X0,X1,X2),X0)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2058,plain,
    ( r2_hidden(sK2(sK8,sK9,o_0_0_xboole_0),sK8)
    | r2_hidden(sK2(sK8,sK9,o_0_0_xboole_0),o_0_0_xboole_0)
    | k3_xboole_0(sK8,sK9) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_13,plain,
    ( r2_hidden(sK2(X0,X1,X2),X1)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2057,plain,
    ( r2_hidden(sK2(sK8,sK9,o_0_0_xboole_0),sK9)
    | r2_hidden(sK2(sK8,sK9,o_0_0_xboole_0),o_0_0_xboole_0)
    | k3_xboole_0(sK8,sK9) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_25,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f128])).

cnf(c_2065,plain,
    ( ~ r1_xboole_0(sK8,sK9)
    | k3_xboole_0(sK8,sK9) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2927,plain,
    ( ~ r2_hidden(sK2(sK8,sK9,o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ v1_xboole_0(o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3753,plain,
    ( r1_xboole_0(sK8,sK9)
    | ~ r2_hidden(sK2(sK8,sK9,o_0_0_xboole_0),sK9)
    | ~ r2_hidden(sK2(sK8,sK9,o_0_0_xboole_0),sK8) ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_3886,plain,
    ( r1_xboole_0(sK8,sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3452,c_27,c_1968,c_2058,c_2057,c_2065,c_2927,c_3753])).

cnf(c_47,negated_conjecture,
    ( ~ r1_xboole_0(sK8,sK9)
    | r2_hidden(sK10,sK9) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_1875,plain,
    ( r1_xboole_0(sK8,sK9) != iProver_top
    | r2_hidden(sK10,sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_3892,plain,
    ( r2_hidden(sK10,sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_3886,c_1875])).

cnf(c_1893,plain,
    ( k3_xboole_0(X0,X1) = o_0_0_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3890,plain,
    ( k3_xboole_0(sK8,sK9) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_3886,c_1893])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f142])).

cnf(c_1903,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_7237,plain,
    ( r2_hidden(X0,sK9) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top
    | r2_hidden(X0,o_0_0_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3890,c_1903])).

cnf(c_26,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_571,plain,
    ( ~ r2_hidden(X0,X1)
    | o_0_0_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_26])).

cnf(c_572,plain,
    ( ~ r2_hidden(X0,o_0_0_xboole_0) ),
    inference(unflattening,[status(thm)],[c_571])).

cnf(c_573,plain,
    ( r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_572])).

cnf(c_7316,plain,
    ( r2_hidden(X0,sK8) != iProver_top
    | r2_hidden(X0,sK9) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7237,c_573])).

cnf(c_7317,plain,
    ( r2_hidden(X0,sK9) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_7316])).

cnf(c_7325,plain,
    ( r2_hidden(sK10,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_3892,c_7317])).

cnf(c_49,negated_conjecture,
    ( ~ r1_xboole_0(sK8,sK9)
    | r2_hidden(sK10,sK8) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_50,plain,
    ( r1_xboole_0(sK8,sK9) != iProver_top
    | r2_hidden(sK10,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7325,c_3886,c_50])).

%------------------------------------------------------------------------------
