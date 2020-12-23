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
% DateTime   : Thu Dec  3 11:22:32 EST 2020

% Result     : Theorem 7.82s
% Output     : CNFRefutation 7.82s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 135 expanded)
%              Number of clauses        :   38 (  50 expanded)
%              Number of leaves         :    8 (  29 expanded)
%              Depth                    :   15
%              Number of atoms          :  272 ( 854 expanded)
%              Number of equality atoms :  115 ( 227 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
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

fof(f8,plain,(
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
    inference(flattening,[],[f7])).

fof(f9,plain,(
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
    inference(rectify,[],[f8])).

fof(f10,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f14,plain,(
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
    inference(rectify,[],[f13])).

fof(f15,plain,(
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

fof(f16,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f15])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f4])).

fof(f6,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) )
   => ( sK2 != sK3
      & k4_xboole_0(sK2,sK3) = k4_xboole_0(sK3,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( sK2 != sK3
    & k4_xboole_0(sK2,sK3) = k4_xboole_0(sK3,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f6,f17])).

fof(f32,plain,(
    k4_xboole_0(sK2,sK3) = k4_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f33,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_329,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_322,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_14,negated_conjecture,
    ( k4_xboole_0(sK2,sK3) = k4_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_12,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_320,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_407,plain,
    ( r2_hidden(X0,k4_xboole_0(sK2,sK3)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_320])).

cnf(c_582,plain,
    ( r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_322,c_407])).

cnf(c_1656,plain,
    ( k3_xboole_0(sK2,X0) = X1
    | r2_hidden(sK0(sK2,X0,X1),X1) = iProver_top
    | r2_hidden(sK0(sK2,X0,X1),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_329,c_582])).

cnf(c_35268,plain,
    ( k3_xboole_0(sK2,X0) = sK3
    | r2_hidden(sK0(sK2,X0,sK3),sK3) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_1656])).

cnf(c_35270,plain,
    ( k3_xboole_0(sK2,X0) = sK3
    | r2_hidden(sK0(sK2,X0,sK3),sK3) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_35268])).

cnf(c_35278,plain,
    ( k3_xboole_0(sK2,sK2) = sK3
    | r2_hidden(sK0(sK2,sK2,sK3),sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_35270])).

cnf(c_579,plain,
    ( r2_hidden(X0,k4_xboole_0(sK2,sK3)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_322])).

cnf(c_786,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_579,c_320])).

cnf(c_1647,plain,
    ( k3_xboole_0(X0,X1) = sK3
    | r2_hidden(sK0(X0,X1,sK3),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_329,c_786])).

cnf(c_1671,plain,
    ( k3_xboole_0(sK2,sK2) = sK3
    | r2_hidden(sK0(sK2,sK2,sK3),sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1647])).

cnf(c_137,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_419,plain,
    ( k3_xboole_0(X0,X1) != X2
    | sK2 != X2
    | sK2 = k3_xboole_0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_137])).

cnf(c_420,plain,
    ( k3_xboole_0(sK2,sK2) != sK2
    | sK2 = k3_xboole_0(sK2,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_419])).

cnf(c_344,plain,
    ( sK3 != X0
    | sK2 != X0
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_137])).

cnf(c_412,plain,
    ( sK3 != k3_xboole_0(X0,X1)
    | sK2 != k3_xboole_0(X0,X1)
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_344])).

cnf(c_413,plain,
    ( sK3 != k3_xboole_0(sK2,sK2)
    | sK2 != k3_xboole_0(sK2,sK2)
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_412])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_366,plain,
    ( ~ r2_hidden(sK0(X0,X1,sK3),X1)
    | ~ r2_hidden(sK0(X0,X1,sK3),X0)
    | ~ r2_hidden(sK0(X0,X1,sK3),sK3)
    | k3_xboole_0(X0,X1) = sK3 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_375,plain,
    ( k3_xboole_0(X0,X1) = sK3
    | r2_hidden(sK0(X0,X1,sK3),X0) != iProver_top
    | r2_hidden(sK0(X0,X1,sK3),X1) != iProver_top
    | r2_hidden(sK0(X0,X1,sK3),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_366])).

cnf(c_377,plain,
    ( k3_xboole_0(sK2,sK2) = sK3
    | r2_hidden(sK0(sK2,sK2,sK3),sK3) != iProver_top
    | r2_hidden(sK0(sK2,sK2,sK3),sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_375])).

cnf(c_136,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_356,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_136])).

cnf(c_347,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_137])).

cnf(c_348,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_347])).

cnf(c_350,plain,
    ( k3_xboole_0(X0,X1) != sK3
    | sK3 = k3_xboole_0(X0,X1)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_348])).

cnf(c_351,plain,
    ( k3_xboole_0(sK2,sK2) != sK3
    | sK3 = k3_xboole_0(sK2,sK2)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_350])).

cnf(c_143,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_136])).

cnf(c_39,plain,
    ( ~ r2_hidden(sK0(sK2,sK2,sK2),sK2)
    | k3_xboole_0(sK2,sK2) = sK2 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_35,plain,
    ( r2_hidden(sK0(sK2,sK2,sK2),sK2)
    | k3_xboole_0(sK2,sK2) = sK2 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_13,negated_conjecture,
    ( sK2 != sK3 ),
    inference(cnf_transformation,[],[f33])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_35278,c_1671,c_420,c_413,c_377,c_356,c_351,c_143,c_39,c_35,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:40:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.82/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.82/1.49  
% 7.82/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.82/1.49  
% 7.82/1.49  ------  iProver source info
% 7.82/1.49  
% 7.82/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.82/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.82/1.49  git: non_committed_changes: false
% 7.82/1.49  git: last_make_outside_of_git: false
% 7.82/1.49  
% 7.82/1.49  ------ 
% 7.82/1.49  
% 7.82/1.49  ------ Input Options
% 7.82/1.49  
% 7.82/1.49  --out_options                           all
% 7.82/1.49  --tptp_safe_out                         true
% 7.82/1.49  --problem_path                          ""
% 7.82/1.49  --include_path                          ""
% 7.82/1.49  --clausifier                            res/vclausify_rel
% 7.82/1.49  --clausifier_options                    ""
% 7.82/1.49  --stdin                                 false
% 7.82/1.49  --stats_out                             all
% 7.82/1.49  
% 7.82/1.49  ------ General Options
% 7.82/1.49  
% 7.82/1.49  --fof                                   false
% 7.82/1.49  --time_out_real                         305.
% 7.82/1.49  --time_out_virtual                      -1.
% 7.82/1.49  --symbol_type_check                     false
% 7.82/1.49  --clausify_out                          false
% 7.82/1.49  --sig_cnt_out                           false
% 7.82/1.49  --trig_cnt_out                          false
% 7.82/1.49  --trig_cnt_out_tolerance                1.
% 7.82/1.49  --trig_cnt_out_sk_spl                   false
% 7.82/1.49  --abstr_cl_out                          false
% 7.82/1.49  
% 7.82/1.49  ------ Global Options
% 7.82/1.49  
% 7.82/1.49  --schedule                              default
% 7.82/1.49  --add_important_lit                     false
% 7.82/1.49  --prop_solver_per_cl                    1000
% 7.82/1.49  --min_unsat_core                        false
% 7.82/1.49  --soft_assumptions                      false
% 7.82/1.49  --soft_lemma_size                       3
% 7.82/1.49  --prop_impl_unit_size                   0
% 7.82/1.49  --prop_impl_unit                        []
% 7.82/1.49  --share_sel_clauses                     true
% 7.82/1.49  --reset_solvers                         false
% 7.82/1.49  --bc_imp_inh                            [conj_cone]
% 7.82/1.49  --conj_cone_tolerance                   3.
% 7.82/1.49  --extra_neg_conj                        none
% 7.82/1.49  --large_theory_mode                     true
% 7.82/1.49  --prolific_symb_bound                   200
% 7.82/1.49  --lt_threshold                          2000
% 7.82/1.49  --clause_weak_htbl                      true
% 7.82/1.49  --gc_record_bc_elim                     false
% 7.82/1.49  
% 7.82/1.49  ------ Preprocessing Options
% 7.82/1.49  
% 7.82/1.49  --preprocessing_flag                    true
% 7.82/1.49  --time_out_prep_mult                    0.1
% 7.82/1.49  --splitting_mode                        input
% 7.82/1.49  --splitting_grd                         true
% 7.82/1.49  --splitting_cvd                         false
% 7.82/1.49  --splitting_cvd_svl                     false
% 7.82/1.49  --splitting_nvd                         32
% 7.82/1.49  --sub_typing                            true
% 7.82/1.49  --prep_gs_sim                           true
% 7.82/1.49  --prep_unflatten                        true
% 7.82/1.49  --prep_res_sim                          true
% 7.82/1.49  --prep_upred                            true
% 7.82/1.49  --prep_sem_filter                       exhaustive
% 7.82/1.49  --prep_sem_filter_out                   false
% 7.82/1.49  --pred_elim                             true
% 7.82/1.49  --res_sim_input                         true
% 7.82/1.49  --eq_ax_congr_red                       true
% 7.82/1.49  --pure_diseq_elim                       true
% 7.82/1.49  --brand_transform                       false
% 7.82/1.49  --non_eq_to_eq                          false
% 7.82/1.49  --prep_def_merge                        true
% 7.82/1.49  --prep_def_merge_prop_impl              false
% 7.82/1.49  --prep_def_merge_mbd                    true
% 7.82/1.49  --prep_def_merge_tr_red                 false
% 7.82/1.49  --prep_def_merge_tr_cl                  false
% 7.82/1.49  --smt_preprocessing                     true
% 7.82/1.49  --smt_ac_axioms                         fast
% 7.82/1.49  --preprocessed_out                      false
% 7.82/1.49  --preprocessed_stats                    false
% 7.82/1.49  
% 7.82/1.49  ------ Abstraction refinement Options
% 7.82/1.49  
% 7.82/1.49  --abstr_ref                             []
% 7.82/1.49  --abstr_ref_prep                        false
% 7.82/1.49  --abstr_ref_until_sat                   false
% 7.82/1.49  --abstr_ref_sig_restrict                funpre
% 7.82/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.82/1.49  --abstr_ref_under                       []
% 7.82/1.49  
% 7.82/1.49  ------ SAT Options
% 7.82/1.49  
% 7.82/1.49  --sat_mode                              false
% 7.82/1.49  --sat_fm_restart_options                ""
% 7.82/1.49  --sat_gr_def                            false
% 7.82/1.49  --sat_epr_types                         true
% 7.82/1.49  --sat_non_cyclic_types                  false
% 7.82/1.49  --sat_finite_models                     false
% 7.82/1.49  --sat_fm_lemmas                         false
% 7.82/1.49  --sat_fm_prep                           false
% 7.82/1.49  --sat_fm_uc_incr                        true
% 7.82/1.49  --sat_out_model                         small
% 7.82/1.49  --sat_out_clauses                       false
% 7.82/1.49  
% 7.82/1.49  ------ QBF Options
% 7.82/1.49  
% 7.82/1.49  --qbf_mode                              false
% 7.82/1.49  --qbf_elim_univ                         false
% 7.82/1.49  --qbf_dom_inst                          none
% 7.82/1.49  --qbf_dom_pre_inst                      false
% 7.82/1.49  --qbf_sk_in                             false
% 7.82/1.49  --qbf_pred_elim                         true
% 7.82/1.49  --qbf_split                             512
% 7.82/1.49  
% 7.82/1.49  ------ BMC1 Options
% 7.82/1.49  
% 7.82/1.49  --bmc1_incremental                      false
% 7.82/1.49  --bmc1_axioms                           reachable_all
% 7.82/1.49  --bmc1_min_bound                        0
% 7.82/1.49  --bmc1_max_bound                        -1
% 7.82/1.49  --bmc1_max_bound_default                -1
% 7.82/1.49  --bmc1_symbol_reachability              true
% 7.82/1.49  --bmc1_property_lemmas                  false
% 7.82/1.49  --bmc1_k_induction                      false
% 7.82/1.49  --bmc1_non_equiv_states                 false
% 7.82/1.49  --bmc1_deadlock                         false
% 7.82/1.49  --bmc1_ucm                              false
% 7.82/1.49  --bmc1_add_unsat_core                   none
% 7.82/1.49  --bmc1_unsat_core_children              false
% 7.82/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.82/1.49  --bmc1_out_stat                         full
% 7.82/1.49  --bmc1_ground_init                      false
% 7.82/1.49  --bmc1_pre_inst_next_state              false
% 7.82/1.49  --bmc1_pre_inst_state                   false
% 7.82/1.49  --bmc1_pre_inst_reach_state             false
% 7.82/1.49  --bmc1_out_unsat_core                   false
% 7.82/1.49  --bmc1_aig_witness_out                  false
% 7.82/1.49  --bmc1_verbose                          false
% 7.82/1.49  --bmc1_dump_clauses_tptp                false
% 7.82/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.82/1.49  --bmc1_dump_file                        -
% 7.82/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.82/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.82/1.49  --bmc1_ucm_extend_mode                  1
% 7.82/1.49  --bmc1_ucm_init_mode                    2
% 7.82/1.49  --bmc1_ucm_cone_mode                    none
% 7.82/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.82/1.49  --bmc1_ucm_relax_model                  4
% 7.82/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.82/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.82/1.49  --bmc1_ucm_layered_model                none
% 7.82/1.49  --bmc1_ucm_max_lemma_size               10
% 7.82/1.49  
% 7.82/1.49  ------ AIG Options
% 7.82/1.49  
% 7.82/1.49  --aig_mode                              false
% 7.82/1.49  
% 7.82/1.49  ------ Instantiation Options
% 7.82/1.49  
% 7.82/1.49  --instantiation_flag                    true
% 7.82/1.49  --inst_sos_flag                         true
% 7.82/1.49  --inst_sos_phase                        true
% 7.82/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.82/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.82/1.49  --inst_lit_sel_side                     num_symb
% 7.82/1.49  --inst_solver_per_active                1400
% 7.82/1.49  --inst_solver_calls_frac                1.
% 7.82/1.49  --inst_passive_queue_type               priority_queues
% 7.82/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.82/1.49  --inst_passive_queues_freq              [25;2]
% 7.82/1.49  --inst_dismatching                      true
% 7.82/1.49  --inst_eager_unprocessed_to_passive     true
% 7.82/1.49  --inst_prop_sim_given                   true
% 7.82/1.49  --inst_prop_sim_new                     false
% 7.82/1.49  --inst_subs_new                         false
% 7.82/1.49  --inst_eq_res_simp                      false
% 7.82/1.49  --inst_subs_given                       false
% 7.82/1.49  --inst_orphan_elimination               true
% 7.82/1.49  --inst_learning_loop_flag               true
% 7.82/1.49  --inst_learning_start                   3000
% 7.82/1.49  --inst_learning_factor                  2
% 7.82/1.49  --inst_start_prop_sim_after_learn       3
% 7.82/1.49  --inst_sel_renew                        solver
% 7.82/1.49  --inst_lit_activity_flag                true
% 7.82/1.49  --inst_restr_to_given                   false
% 7.82/1.49  --inst_activity_threshold               500
% 7.82/1.49  --inst_out_proof                        true
% 7.82/1.49  
% 7.82/1.49  ------ Resolution Options
% 7.82/1.49  
% 7.82/1.49  --resolution_flag                       true
% 7.82/1.49  --res_lit_sel                           adaptive
% 7.82/1.49  --res_lit_sel_side                      none
% 7.82/1.49  --res_ordering                          kbo
% 7.82/1.49  --res_to_prop_solver                    active
% 7.82/1.49  --res_prop_simpl_new                    false
% 7.82/1.49  --res_prop_simpl_given                  true
% 7.82/1.49  --res_passive_queue_type                priority_queues
% 7.82/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.82/1.49  --res_passive_queues_freq               [15;5]
% 7.82/1.49  --res_forward_subs                      full
% 7.82/1.49  --res_backward_subs                     full
% 7.82/1.49  --res_forward_subs_resolution           true
% 7.82/1.49  --res_backward_subs_resolution          true
% 7.82/1.49  --res_orphan_elimination                true
% 7.82/1.49  --res_time_limit                        2.
% 7.82/1.49  --res_out_proof                         true
% 7.82/1.49  
% 7.82/1.49  ------ Superposition Options
% 7.82/1.49  
% 7.82/1.49  --superposition_flag                    true
% 7.82/1.49  --sup_passive_queue_type                priority_queues
% 7.82/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.82/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.82/1.49  --demod_completeness_check              fast
% 7.82/1.49  --demod_use_ground                      true
% 7.82/1.49  --sup_to_prop_solver                    passive
% 7.82/1.49  --sup_prop_simpl_new                    true
% 7.82/1.49  --sup_prop_simpl_given                  true
% 7.82/1.49  --sup_fun_splitting                     true
% 7.82/1.49  --sup_smt_interval                      50000
% 7.82/1.49  
% 7.82/1.49  ------ Superposition Simplification Setup
% 7.82/1.49  
% 7.82/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.82/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.82/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.82/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.82/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.82/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.82/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.82/1.49  --sup_immed_triv                        [TrivRules]
% 7.82/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.82/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.82/1.49  --sup_immed_bw_main                     []
% 7.82/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.82/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.82/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.82/1.49  --sup_input_bw                          []
% 7.82/1.49  
% 7.82/1.49  ------ Combination Options
% 7.82/1.49  
% 7.82/1.49  --comb_res_mult                         3
% 7.82/1.49  --comb_sup_mult                         2
% 7.82/1.49  --comb_inst_mult                        10
% 7.82/1.49  
% 7.82/1.49  ------ Debug Options
% 7.82/1.49  
% 7.82/1.49  --dbg_backtrace                         false
% 7.82/1.49  --dbg_dump_prop_clauses                 false
% 7.82/1.49  --dbg_dump_prop_clauses_file            -
% 7.82/1.49  --dbg_out_stat                          false
% 7.82/1.49  ------ Parsing...
% 7.82/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.82/1.49  
% 7.82/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.82/1.49  
% 7.82/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.82/1.49  
% 7.82/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.82/1.49  ------ Proving...
% 7.82/1.49  ------ Problem Properties 
% 7.82/1.49  
% 7.82/1.49  
% 7.82/1.49  clauses                                 15
% 7.82/1.49  conjectures                             2
% 7.82/1.49  EPR                                     1
% 7.82/1.49  Horn                                    9
% 7.82/1.49  unary                                   3
% 7.82/1.49  binary                                  4
% 7.82/1.49  lits                                    37
% 7.82/1.49  lits eq                                 9
% 7.82/1.49  fd_pure                                 0
% 7.82/1.49  fd_pseudo                               0
% 7.82/1.49  fd_cond                                 0
% 7.82/1.49  fd_pseudo_cond                          6
% 7.82/1.49  AC symbols                              0
% 7.82/1.49  
% 7.82/1.49  ------ Schedule dynamic 5 is on 
% 7.82/1.49  
% 7.82/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.82/1.49  
% 7.82/1.49  
% 7.82/1.49  ------ 
% 7.82/1.49  Current options:
% 7.82/1.49  ------ 
% 7.82/1.49  
% 7.82/1.49  ------ Input Options
% 7.82/1.49  
% 7.82/1.49  --out_options                           all
% 7.82/1.49  --tptp_safe_out                         true
% 7.82/1.49  --problem_path                          ""
% 7.82/1.49  --include_path                          ""
% 7.82/1.49  --clausifier                            res/vclausify_rel
% 7.82/1.49  --clausifier_options                    ""
% 7.82/1.49  --stdin                                 false
% 7.82/1.49  --stats_out                             all
% 7.82/1.49  
% 7.82/1.49  ------ General Options
% 7.82/1.49  
% 7.82/1.49  --fof                                   false
% 7.82/1.49  --time_out_real                         305.
% 7.82/1.49  --time_out_virtual                      -1.
% 7.82/1.49  --symbol_type_check                     false
% 7.82/1.49  --clausify_out                          false
% 7.82/1.49  --sig_cnt_out                           false
% 7.82/1.49  --trig_cnt_out                          false
% 7.82/1.49  --trig_cnt_out_tolerance                1.
% 7.82/1.49  --trig_cnt_out_sk_spl                   false
% 7.82/1.49  --abstr_cl_out                          false
% 7.82/1.49  
% 7.82/1.49  ------ Global Options
% 7.82/1.49  
% 7.82/1.49  --schedule                              default
% 7.82/1.49  --add_important_lit                     false
% 7.82/1.49  --prop_solver_per_cl                    1000
% 7.82/1.49  --min_unsat_core                        false
% 7.82/1.49  --soft_assumptions                      false
% 7.82/1.49  --soft_lemma_size                       3
% 7.82/1.49  --prop_impl_unit_size                   0
% 7.82/1.49  --prop_impl_unit                        []
% 7.82/1.49  --share_sel_clauses                     true
% 7.82/1.49  --reset_solvers                         false
% 7.82/1.49  --bc_imp_inh                            [conj_cone]
% 7.82/1.49  --conj_cone_tolerance                   3.
% 7.82/1.49  --extra_neg_conj                        none
% 7.82/1.49  --large_theory_mode                     true
% 7.82/1.49  --prolific_symb_bound                   200
% 7.82/1.49  --lt_threshold                          2000
% 7.82/1.49  --clause_weak_htbl                      true
% 7.82/1.49  --gc_record_bc_elim                     false
% 7.82/1.49  
% 7.82/1.49  ------ Preprocessing Options
% 7.82/1.49  
% 7.82/1.49  --preprocessing_flag                    true
% 7.82/1.49  --time_out_prep_mult                    0.1
% 7.82/1.49  --splitting_mode                        input
% 7.82/1.49  --splitting_grd                         true
% 7.82/1.49  --splitting_cvd                         false
% 7.82/1.49  --splitting_cvd_svl                     false
% 7.82/1.49  --splitting_nvd                         32
% 7.82/1.49  --sub_typing                            true
% 7.82/1.49  --prep_gs_sim                           true
% 7.82/1.49  --prep_unflatten                        true
% 7.82/1.49  --prep_res_sim                          true
% 7.82/1.49  --prep_upred                            true
% 7.82/1.49  --prep_sem_filter                       exhaustive
% 7.82/1.49  --prep_sem_filter_out                   false
% 7.82/1.49  --pred_elim                             true
% 7.82/1.49  --res_sim_input                         true
% 7.82/1.49  --eq_ax_congr_red                       true
% 7.82/1.49  --pure_diseq_elim                       true
% 7.82/1.49  --brand_transform                       false
% 7.82/1.49  --non_eq_to_eq                          false
% 7.82/1.49  --prep_def_merge                        true
% 7.82/1.49  --prep_def_merge_prop_impl              false
% 7.82/1.49  --prep_def_merge_mbd                    true
% 7.82/1.49  --prep_def_merge_tr_red                 false
% 7.82/1.49  --prep_def_merge_tr_cl                  false
% 7.82/1.49  --smt_preprocessing                     true
% 7.82/1.49  --smt_ac_axioms                         fast
% 7.82/1.49  --preprocessed_out                      false
% 7.82/1.49  --preprocessed_stats                    false
% 7.82/1.49  
% 7.82/1.49  ------ Abstraction refinement Options
% 7.82/1.49  
% 7.82/1.49  --abstr_ref                             []
% 7.82/1.49  --abstr_ref_prep                        false
% 7.82/1.49  --abstr_ref_until_sat                   false
% 7.82/1.49  --abstr_ref_sig_restrict                funpre
% 7.82/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.82/1.49  --abstr_ref_under                       []
% 7.82/1.49  
% 7.82/1.49  ------ SAT Options
% 7.82/1.49  
% 7.82/1.49  --sat_mode                              false
% 7.82/1.49  --sat_fm_restart_options                ""
% 7.82/1.49  --sat_gr_def                            false
% 7.82/1.49  --sat_epr_types                         true
% 7.82/1.49  --sat_non_cyclic_types                  false
% 7.82/1.49  --sat_finite_models                     false
% 7.82/1.49  --sat_fm_lemmas                         false
% 7.82/1.49  --sat_fm_prep                           false
% 7.82/1.49  --sat_fm_uc_incr                        true
% 7.82/1.49  --sat_out_model                         small
% 7.82/1.49  --sat_out_clauses                       false
% 7.82/1.49  
% 7.82/1.49  ------ QBF Options
% 7.82/1.49  
% 7.82/1.49  --qbf_mode                              false
% 7.82/1.49  --qbf_elim_univ                         false
% 7.82/1.49  --qbf_dom_inst                          none
% 7.82/1.49  --qbf_dom_pre_inst                      false
% 7.82/1.49  --qbf_sk_in                             false
% 7.82/1.49  --qbf_pred_elim                         true
% 7.82/1.49  --qbf_split                             512
% 7.82/1.49  
% 7.82/1.49  ------ BMC1 Options
% 7.82/1.49  
% 7.82/1.49  --bmc1_incremental                      false
% 7.82/1.49  --bmc1_axioms                           reachable_all
% 7.82/1.49  --bmc1_min_bound                        0
% 7.82/1.49  --bmc1_max_bound                        -1
% 7.82/1.49  --bmc1_max_bound_default                -1
% 7.82/1.49  --bmc1_symbol_reachability              true
% 7.82/1.49  --bmc1_property_lemmas                  false
% 7.82/1.49  --bmc1_k_induction                      false
% 7.82/1.49  --bmc1_non_equiv_states                 false
% 7.82/1.49  --bmc1_deadlock                         false
% 7.82/1.49  --bmc1_ucm                              false
% 7.82/1.49  --bmc1_add_unsat_core                   none
% 7.82/1.49  --bmc1_unsat_core_children              false
% 7.82/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.82/1.49  --bmc1_out_stat                         full
% 7.82/1.49  --bmc1_ground_init                      false
% 7.82/1.49  --bmc1_pre_inst_next_state              false
% 7.82/1.49  --bmc1_pre_inst_state                   false
% 7.82/1.49  --bmc1_pre_inst_reach_state             false
% 7.82/1.49  --bmc1_out_unsat_core                   false
% 7.82/1.49  --bmc1_aig_witness_out                  false
% 7.82/1.49  --bmc1_verbose                          false
% 7.82/1.49  --bmc1_dump_clauses_tptp                false
% 7.82/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.82/1.49  --bmc1_dump_file                        -
% 7.82/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.82/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.82/1.49  --bmc1_ucm_extend_mode                  1
% 7.82/1.49  --bmc1_ucm_init_mode                    2
% 7.82/1.49  --bmc1_ucm_cone_mode                    none
% 7.82/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.82/1.49  --bmc1_ucm_relax_model                  4
% 7.82/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.82/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.82/1.49  --bmc1_ucm_layered_model                none
% 7.82/1.49  --bmc1_ucm_max_lemma_size               10
% 7.82/1.49  
% 7.82/1.49  ------ AIG Options
% 7.82/1.49  
% 7.82/1.49  --aig_mode                              false
% 7.82/1.49  
% 7.82/1.49  ------ Instantiation Options
% 7.82/1.49  
% 7.82/1.49  --instantiation_flag                    true
% 7.82/1.49  --inst_sos_flag                         true
% 7.82/1.49  --inst_sos_phase                        true
% 7.82/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.82/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.82/1.49  --inst_lit_sel_side                     none
% 7.82/1.49  --inst_solver_per_active                1400
% 7.82/1.49  --inst_solver_calls_frac                1.
% 7.82/1.49  --inst_passive_queue_type               priority_queues
% 7.82/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.82/1.49  --inst_passive_queues_freq              [25;2]
% 7.82/1.49  --inst_dismatching                      true
% 7.82/1.49  --inst_eager_unprocessed_to_passive     true
% 7.82/1.49  --inst_prop_sim_given                   true
% 7.82/1.49  --inst_prop_sim_new                     false
% 7.82/1.49  --inst_subs_new                         false
% 7.82/1.49  --inst_eq_res_simp                      false
% 7.82/1.49  --inst_subs_given                       false
% 7.82/1.49  --inst_orphan_elimination               true
% 7.82/1.49  --inst_learning_loop_flag               true
% 7.82/1.49  --inst_learning_start                   3000
% 7.82/1.49  --inst_learning_factor                  2
% 7.82/1.49  --inst_start_prop_sim_after_learn       3
% 7.82/1.49  --inst_sel_renew                        solver
% 7.82/1.49  --inst_lit_activity_flag                true
% 7.82/1.49  --inst_restr_to_given                   false
% 7.82/1.49  --inst_activity_threshold               500
% 7.82/1.49  --inst_out_proof                        true
% 7.82/1.49  
% 7.82/1.49  ------ Resolution Options
% 7.82/1.49  
% 7.82/1.49  --resolution_flag                       false
% 7.82/1.49  --res_lit_sel                           adaptive
% 7.82/1.49  --res_lit_sel_side                      none
% 7.82/1.49  --res_ordering                          kbo
% 7.82/1.49  --res_to_prop_solver                    active
% 7.82/1.49  --res_prop_simpl_new                    false
% 7.82/1.49  --res_prop_simpl_given                  true
% 7.82/1.49  --res_passive_queue_type                priority_queues
% 7.82/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.82/1.49  --res_passive_queues_freq               [15;5]
% 7.82/1.49  --res_forward_subs                      full
% 7.82/1.49  --res_backward_subs                     full
% 7.82/1.49  --res_forward_subs_resolution           true
% 7.82/1.49  --res_backward_subs_resolution          true
% 7.82/1.49  --res_orphan_elimination                true
% 7.82/1.49  --res_time_limit                        2.
% 7.82/1.49  --res_out_proof                         true
% 7.82/1.49  
% 7.82/1.49  ------ Superposition Options
% 7.82/1.49  
% 7.82/1.49  --superposition_flag                    true
% 7.82/1.49  --sup_passive_queue_type                priority_queues
% 7.82/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.82/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.82/1.49  --demod_completeness_check              fast
% 7.82/1.49  --demod_use_ground                      true
% 7.82/1.49  --sup_to_prop_solver                    passive
% 7.82/1.49  --sup_prop_simpl_new                    true
% 7.82/1.49  --sup_prop_simpl_given                  true
% 7.82/1.49  --sup_fun_splitting                     true
% 7.82/1.49  --sup_smt_interval                      50000
% 7.82/1.49  
% 7.82/1.49  ------ Superposition Simplification Setup
% 7.82/1.49  
% 7.82/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.82/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.82/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.82/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.82/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.82/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.82/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.82/1.49  --sup_immed_triv                        [TrivRules]
% 7.82/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.82/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.82/1.49  --sup_immed_bw_main                     []
% 7.82/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.82/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.82/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.82/1.49  --sup_input_bw                          []
% 7.82/1.49  
% 7.82/1.49  ------ Combination Options
% 7.82/1.49  
% 7.82/1.49  --comb_res_mult                         3
% 7.82/1.49  --comb_sup_mult                         2
% 7.82/1.49  --comb_inst_mult                        10
% 7.82/1.49  
% 7.82/1.49  ------ Debug Options
% 7.82/1.49  
% 7.82/1.49  --dbg_backtrace                         false
% 7.82/1.49  --dbg_dump_prop_clauses                 false
% 7.82/1.49  --dbg_dump_prop_clauses_file            -
% 7.82/1.49  --dbg_out_stat                          false
% 7.82/1.49  
% 7.82/1.49  
% 7.82/1.49  
% 7.82/1.49  
% 7.82/1.49  ------ Proving...
% 7.82/1.49  
% 7.82/1.49  
% 7.82/1.49  % SZS status Theorem for theBenchmark.p
% 7.82/1.49  
% 7.82/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.82/1.49  
% 7.82/1.49  fof(f2,axiom,(
% 7.82/1.49    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f7,plain,(
% 7.82/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.82/1.49    inference(nnf_transformation,[],[f2])).
% 7.82/1.49  
% 7.82/1.49  fof(f8,plain,(
% 7.82/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.82/1.49    inference(flattening,[],[f7])).
% 7.82/1.49  
% 7.82/1.49  fof(f9,plain,(
% 7.82/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.82/1.49    inference(rectify,[],[f8])).
% 7.82/1.49  
% 7.82/1.49  fof(f10,plain,(
% 7.82/1.49    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.82/1.49    introduced(choice_axiom,[])).
% 7.82/1.49  
% 7.82/1.49  fof(f11,plain,(
% 7.82/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.82/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).
% 7.82/1.49  
% 7.82/1.49  fof(f23,plain,(
% 7.82/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.82/1.49    inference(cnf_transformation,[],[f11])).
% 7.82/1.49  
% 7.82/1.49  fof(f3,axiom,(
% 7.82/1.49    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f12,plain,(
% 7.82/1.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.82/1.49    inference(nnf_transformation,[],[f3])).
% 7.82/1.49  
% 7.82/1.49  fof(f13,plain,(
% 7.82/1.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.82/1.49    inference(flattening,[],[f12])).
% 7.82/1.49  
% 7.82/1.49  fof(f14,plain,(
% 7.82/1.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.82/1.49    inference(rectify,[],[f13])).
% 7.82/1.49  
% 7.82/1.49  fof(f15,plain,(
% 7.82/1.49    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 7.82/1.49    introduced(choice_axiom,[])).
% 7.82/1.49  
% 7.82/1.49  fof(f16,plain,(
% 7.82/1.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.82/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f15])).
% 7.82/1.49  
% 7.82/1.49  fof(f28,plain,(
% 7.82/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 7.82/1.49    inference(cnf_transformation,[],[f16])).
% 7.82/1.49  
% 7.82/1.49  fof(f37,plain,(
% 7.82/1.49    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 7.82/1.49    inference(equality_resolution,[],[f28])).
% 7.82/1.49  
% 7.82/1.49  fof(f4,conjecture,(
% 7.82/1.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 7.82/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.49  
% 7.82/1.49  fof(f5,negated_conjecture,(
% 7.82/1.49    ~! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 7.82/1.49    inference(negated_conjecture,[],[f4])).
% 7.82/1.49  
% 7.82/1.49  fof(f6,plain,(
% 7.82/1.49    ? [X0,X1] : (X0 != X1 & k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0))),
% 7.82/1.49    inference(ennf_transformation,[],[f5])).
% 7.82/1.49  
% 7.82/1.49  fof(f17,plain,(
% 7.82/1.49    ? [X0,X1] : (X0 != X1 & k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)) => (sK2 != sK3 & k4_xboole_0(sK2,sK3) = k4_xboole_0(sK3,sK2))),
% 7.82/1.49    introduced(choice_axiom,[])).
% 7.82/1.49  
% 7.82/1.49  fof(f18,plain,(
% 7.82/1.49    sK2 != sK3 & k4_xboole_0(sK2,sK3) = k4_xboole_0(sK3,sK2)),
% 7.82/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f6,f17])).
% 7.82/1.49  
% 7.82/1.49  fof(f32,plain,(
% 7.82/1.49    k4_xboole_0(sK2,sK3) = k4_xboole_0(sK3,sK2)),
% 7.82/1.49    inference(cnf_transformation,[],[f18])).
% 7.82/1.49  
% 7.82/1.49  fof(f26,plain,(
% 7.82/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.82/1.49    inference(cnf_transformation,[],[f16])).
% 7.82/1.49  
% 7.82/1.49  fof(f39,plain,(
% 7.82/1.49    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 7.82/1.49    inference(equality_resolution,[],[f26])).
% 7.82/1.49  
% 7.82/1.49  fof(f25,plain,(
% 7.82/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.82/1.49    inference(cnf_transformation,[],[f11])).
% 7.82/1.49  
% 7.82/1.49  fof(f33,plain,(
% 7.82/1.49    sK2 != sK3),
% 7.82/1.49    inference(cnf_transformation,[],[f18])).
% 7.82/1.49  
% 7.82/1.49  cnf(c_3,plain,
% 7.82/1.49      ( r2_hidden(sK0(X0,X1,X2),X0)
% 7.82/1.49      | r2_hidden(sK0(X0,X1,X2),X2)
% 7.82/1.49      | k3_xboole_0(X0,X1) = X2 ),
% 7.82/1.49      inference(cnf_transformation,[],[f23]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_329,plain,
% 7.82/1.49      ( k3_xboole_0(X0,X1) = X2
% 7.82/1.49      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 7.82/1.49      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 7.82/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_10,plain,
% 7.82/1.49      ( ~ r2_hidden(X0,X1)
% 7.82/1.49      | r2_hidden(X0,X2)
% 7.82/1.49      | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 7.82/1.49      inference(cnf_transformation,[],[f37]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_322,plain,
% 7.82/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.82/1.49      | r2_hidden(X0,X2) = iProver_top
% 7.82/1.49      | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
% 7.82/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_14,negated_conjecture,
% 7.82/1.49      ( k4_xboole_0(sK2,sK3) = k4_xboole_0(sK3,sK2) ),
% 7.82/1.49      inference(cnf_transformation,[],[f32]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_12,plain,
% 7.82/1.49      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 7.82/1.49      inference(cnf_transformation,[],[f39]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_320,plain,
% 7.82/1.49      ( r2_hidden(X0,X1) = iProver_top
% 7.82/1.49      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 7.82/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_407,plain,
% 7.82/1.49      ( r2_hidden(X0,k4_xboole_0(sK2,sK3)) != iProver_top
% 7.82/1.49      | r2_hidden(X0,sK3) = iProver_top ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_14,c_320]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_582,plain,
% 7.82/1.49      ( r2_hidden(X0,sK3) = iProver_top
% 7.82/1.49      | r2_hidden(X0,sK2) != iProver_top ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_322,c_407]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1656,plain,
% 7.82/1.49      ( k3_xboole_0(sK2,X0) = X1
% 7.82/1.49      | r2_hidden(sK0(sK2,X0,X1),X1) = iProver_top
% 7.82/1.49      | r2_hidden(sK0(sK2,X0,X1),sK3) = iProver_top ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_329,c_582]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_35268,plain,
% 7.82/1.49      ( k3_xboole_0(sK2,X0) = sK3
% 7.82/1.49      | r2_hidden(sK0(sK2,X0,sK3),sK3) = iProver_top
% 7.82/1.49      | iProver_top != iProver_top ),
% 7.82/1.49      inference(equality_factoring,[status(thm)],[c_1656]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_35270,plain,
% 7.82/1.49      ( k3_xboole_0(sK2,X0) = sK3
% 7.82/1.49      | r2_hidden(sK0(sK2,X0,sK3),sK3) = iProver_top ),
% 7.82/1.49      inference(equality_resolution_simp,[status(thm)],[c_35268]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_35278,plain,
% 7.82/1.49      ( k3_xboole_0(sK2,sK2) = sK3
% 7.82/1.49      | r2_hidden(sK0(sK2,sK2,sK3),sK3) = iProver_top ),
% 7.82/1.49      inference(instantiation,[status(thm)],[c_35270]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_579,plain,
% 7.82/1.49      ( r2_hidden(X0,k4_xboole_0(sK2,sK3)) = iProver_top
% 7.82/1.49      | r2_hidden(X0,sK3) != iProver_top
% 7.82/1.49      | r2_hidden(X0,sK2) = iProver_top ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_14,c_322]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_786,plain,
% 7.82/1.49      ( r2_hidden(X0,sK3) != iProver_top
% 7.82/1.49      | r2_hidden(X0,sK2) = iProver_top ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_579,c_320]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1647,plain,
% 7.82/1.49      ( k3_xboole_0(X0,X1) = sK3
% 7.82/1.49      | r2_hidden(sK0(X0,X1,sK3),X0) = iProver_top
% 7.82/1.49      | r2_hidden(sK0(X0,X1,sK3),sK2) = iProver_top ),
% 7.82/1.49      inference(superposition,[status(thm)],[c_329,c_786]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1671,plain,
% 7.82/1.49      ( k3_xboole_0(sK2,sK2) = sK3
% 7.82/1.49      | r2_hidden(sK0(sK2,sK2,sK3),sK2) = iProver_top ),
% 7.82/1.49      inference(instantiation,[status(thm)],[c_1647]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_137,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_419,plain,
% 7.82/1.49      ( k3_xboole_0(X0,X1) != X2 | sK2 != X2 | sK2 = k3_xboole_0(X0,X1) ),
% 7.82/1.49      inference(instantiation,[status(thm)],[c_137]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_420,plain,
% 7.82/1.49      ( k3_xboole_0(sK2,sK2) != sK2
% 7.82/1.49      | sK2 = k3_xboole_0(sK2,sK2)
% 7.82/1.49      | sK2 != sK2 ),
% 7.82/1.49      inference(instantiation,[status(thm)],[c_419]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_344,plain,
% 7.82/1.49      ( sK3 != X0 | sK2 != X0 | sK2 = sK3 ),
% 7.82/1.49      inference(instantiation,[status(thm)],[c_137]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_412,plain,
% 7.82/1.49      ( sK3 != k3_xboole_0(X0,X1)
% 7.82/1.49      | sK2 != k3_xboole_0(X0,X1)
% 7.82/1.49      | sK2 = sK3 ),
% 7.82/1.49      inference(instantiation,[status(thm)],[c_344]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_413,plain,
% 7.82/1.49      ( sK3 != k3_xboole_0(sK2,sK2)
% 7.82/1.49      | sK2 != k3_xboole_0(sK2,sK2)
% 7.82/1.49      | sK2 = sK3 ),
% 7.82/1.49      inference(instantiation,[status(thm)],[c_412]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_1,plain,
% 7.82/1.49      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 7.82/1.49      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 7.82/1.49      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 7.82/1.49      | k3_xboole_0(X0,X1) = X2 ),
% 7.82/1.49      inference(cnf_transformation,[],[f25]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_366,plain,
% 7.82/1.49      ( ~ r2_hidden(sK0(X0,X1,sK3),X1)
% 7.82/1.49      | ~ r2_hidden(sK0(X0,X1,sK3),X0)
% 7.82/1.49      | ~ r2_hidden(sK0(X0,X1,sK3),sK3)
% 7.82/1.49      | k3_xboole_0(X0,X1) = sK3 ),
% 7.82/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_375,plain,
% 7.82/1.49      ( k3_xboole_0(X0,X1) = sK3
% 7.82/1.49      | r2_hidden(sK0(X0,X1,sK3),X0) != iProver_top
% 7.82/1.49      | r2_hidden(sK0(X0,X1,sK3),X1) != iProver_top
% 7.82/1.49      | r2_hidden(sK0(X0,X1,sK3),sK3) != iProver_top ),
% 7.82/1.49      inference(predicate_to_equality,[status(thm)],[c_366]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_377,plain,
% 7.82/1.49      ( k3_xboole_0(sK2,sK2) = sK3
% 7.82/1.49      | r2_hidden(sK0(sK2,sK2,sK3),sK3) != iProver_top
% 7.82/1.49      | r2_hidden(sK0(sK2,sK2,sK3),sK2) != iProver_top ),
% 7.82/1.49      inference(instantiation,[status(thm)],[c_375]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_136,plain,( X0 = X0 ),theory(equality) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_356,plain,
% 7.82/1.49      ( sK3 = sK3 ),
% 7.82/1.49      inference(instantiation,[status(thm)],[c_136]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_347,plain,
% 7.82/1.49      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 7.82/1.49      inference(instantiation,[status(thm)],[c_137]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_348,plain,
% 7.82/1.49      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 7.82/1.49      inference(instantiation,[status(thm)],[c_347]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_350,plain,
% 7.82/1.49      ( k3_xboole_0(X0,X1) != sK3
% 7.82/1.49      | sK3 = k3_xboole_0(X0,X1)
% 7.82/1.49      | sK3 != sK3 ),
% 7.82/1.49      inference(instantiation,[status(thm)],[c_348]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_351,plain,
% 7.82/1.49      ( k3_xboole_0(sK2,sK2) != sK3
% 7.82/1.49      | sK3 = k3_xboole_0(sK2,sK2)
% 7.82/1.49      | sK3 != sK3 ),
% 7.82/1.49      inference(instantiation,[status(thm)],[c_350]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_143,plain,
% 7.82/1.49      ( sK2 = sK2 ),
% 7.82/1.49      inference(instantiation,[status(thm)],[c_136]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_39,plain,
% 7.82/1.49      ( ~ r2_hidden(sK0(sK2,sK2,sK2),sK2) | k3_xboole_0(sK2,sK2) = sK2 ),
% 7.82/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_35,plain,
% 7.82/1.49      ( r2_hidden(sK0(sK2,sK2,sK2),sK2) | k3_xboole_0(sK2,sK2) = sK2 ),
% 7.82/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(c_13,negated_conjecture,
% 7.82/1.49      ( sK2 != sK3 ),
% 7.82/1.49      inference(cnf_transformation,[],[f33]) ).
% 7.82/1.49  
% 7.82/1.49  cnf(contradiction,plain,
% 7.82/1.49      ( $false ),
% 7.82/1.49      inference(minisat,
% 7.82/1.49                [status(thm)],
% 7.82/1.49                [c_35278,c_1671,c_420,c_413,c_377,c_356,c_351,c_143,c_39,
% 7.82/1.49                 c_35,c_13]) ).
% 7.82/1.49  
% 7.82/1.49  
% 7.82/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.82/1.49  
% 7.82/1.49  ------                               Statistics
% 7.82/1.49  
% 7.82/1.49  ------ General
% 7.82/1.49  
% 7.82/1.49  abstr_ref_over_cycles:                  0
% 7.82/1.49  abstr_ref_under_cycles:                 0
% 7.82/1.49  gc_basic_clause_elim:                   0
% 7.82/1.49  forced_gc_time:                         0
% 7.82/1.49  parsing_time:                           0.008
% 7.82/1.49  unif_index_cands_time:                  0.
% 7.82/1.49  unif_index_add_time:                    0.
% 7.82/1.49  orderings_time:                         0.
% 7.82/1.49  out_proof_time:                         0.009
% 7.82/1.49  total_time:                             0.908
% 7.82/1.49  num_of_symbols:                         39
% 7.82/1.49  num_of_terms:                           38977
% 7.82/1.49  
% 7.82/1.49  ------ Preprocessing
% 7.82/1.49  
% 7.82/1.49  num_of_splits:                          0
% 7.82/1.49  num_of_split_atoms:                     1
% 7.82/1.49  num_of_reused_defs:                     0
% 7.82/1.49  num_eq_ax_congr_red:                    16
% 7.82/1.49  num_of_sem_filtered_clauses:            1
% 7.82/1.49  num_of_subtypes:                        0
% 7.82/1.49  monotx_restored_types:                  0
% 7.82/1.49  sat_num_of_epr_types:                   0
% 7.82/1.49  sat_num_of_non_cyclic_types:            0
% 7.82/1.49  sat_guarded_non_collapsed_types:        0
% 7.82/1.49  num_pure_diseq_elim:                    0
% 7.82/1.49  simp_replaced_by:                       0
% 7.82/1.49  res_preprocessed:                       54
% 7.82/1.49  prep_upred:                             0
% 7.82/1.49  prep_unflattend:                        0
% 7.82/1.49  smt_new_axioms:                         0
% 7.82/1.49  pred_elim_cands:                        1
% 7.82/1.49  pred_elim:                              0
% 7.82/1.49  pred_elim_cl:                           0
% 7.82/1.49  pred_elim_cycles:                       1
% 7.82/1.49  merged_defs:                            0
% 7.82/1.49  merged_defs_ncl:                        0
% 7.82/1.49  bin_hyper_res:                          0
% 7.82/1.49  prep_cycles:                            3
% 7.82/1.49  pred_elim_time:                         0.
% 7.82/1.49  splitting_time:                         0.
% 7.82/1.49  sem_filter_time:                        0.
% 7.82/1.49  monotx_time:                            0.
% 7.82/1.49  subtype_inf_time:                       0.
% 7.82/1.49  
% 7.82/1.49  ------ Problem properties
% 7.82/1.49  
% 7.82/1.49  clauses:                                15
% 7.82/1.49  conjectures:                            2
% 7.82/1.49  epr:                                    1
% 7.82/1.49  horn:                                   9
% 7.82/1.49  ground:                                 2
% 7.82/1.49  unary:                                  3
% 7.82/1.49  binary:                                 4
% 7.82/1.49  lits:                                   37
% 7.82/1.49  lits_eq:                                9
% 7.82/1.49  fd_pure:                                0
% 7.82/1.49  fd_pseudo:                              0
% 7.82/1.49  fd_cond:                                0
% 7.82/1.49  fd_pseudo_cond:                         6
% 7.82/1.49  ac_symbols:                             0
% 7.82/1.49  
% 7.82/1.49  ------ Propositional Solver
% 7.82/1.49  
% 7.82/1.49  prop_solver_calls:                      31
% 7.82/1.49  prop_fast_solver_calls:                 924
% 7.82/1.49  smt_solver_calls:                       0
% 7.82/1.49  smt_fast_solver_calls:                  0
% 7.82/1.49  prop_num_of_clauses:                    11445
% 7.82/1.49  prop_preprocess_simplified:             24838
% 7.82/1.49  prop_fo_subsumed:                       15
% 7.82/1.49  prop_solver_time:                       0.
% 7.82/1.49  smt_solver_time:                        0.
% 7.82/1.49  smt_fast_solver_time:                   0.
% 7.82/1.49  prop_fast_solver_time:                  0.
% 7.82/1.49  prop_unsat_core_time:                   0.001
% 7.82/1.49  
% 7.82/1.49  ------ QBF
% 7.82/1.49  
% 7.82/1.49  qbf_q_res:                              0
% 7.82/1.49  qbf_num_tautologies:                    0
% 7.82/1.49  qbf_prep_cycles:                        0
% 7.82/1.49  
% 7.82/1.49  ------ BMC1
% 7.82/1.49  
% 7.82/1.49  bmc1_current_bound:                     -1
% 7.82/1.49  bmc1_last_solved_bound:                 -1
% 7.82/1.49  bmc1_unsat_core_size:                   -1
% 7.82/1.49  bmc1_unsat_core_parents_size:           -1
% 7.82/1.49  bmc1_merge_next_fun:                    0
% 7.82/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.82/1.49  
% 7.82/1.49  ------ Instantiation
% 7.82/1.49  
% 7.82/1.49  inst_num_of_clauses:                    3172
% 7.82/1.49  inst_num_in_passive:                    2166
% 7.82/1.49  inst_num_in_active:                     881
% 7.82/1.49  inst_num_in_unprocessed:                125
% 7.82/1.49  inst_num_of_loops:                      1250
% 7.82/1.49  inst_num_of_learning_restarts:          0
% 7.82/1.49  inst_num_moves_active_passive:          363
% 7.82/1.49  inst_lit_activity:                      0
% 7.82/1.49  inst_lit_activity_moves:                0
% 7.82/1.49  inst_num_tautologies:                   0
% 7.82/1.49  inst_num_prop_implied:                  0
% 7.82/1.49  inst_num_existing_simplified:           0
% 7.82/1.49  inst_num_eq_res_simplified:             0
% 7.82/1.49  inst_num_child_elim:                    0
% 7.82/1.49  inst_num_of_dismatching_blockings:      6941
% 7.82/1.49  inst_num_of_non_proper_insts:           4796
% 7.82/1.49  inst_num_of_duplicates:                 0
% 7.82/1.49  inst_inst_num_from_inst_to_res:         0
% 7.82/1.49  inst_dismatching_checking_time:         0.
% 7.82/1.49  
% 7.82/1.49  ------ Resolution
% 7.82/1.49  
% 7.82/1.49  res_num_of_clauses:                     0
% 7.82/1.49  res_num_in_passive:                     0
% 7.82/1.49  res_num_in_active:                      0
% 7.82/1.49  res_num_of_loops:                       57
% 7.82/1.49  res_forward_subset_subsumed:            290
% 7.82/1.49  res_backward_subset_subsumed:           0
% 7.82/1.49  res_forward_subsumed:                   0
% 7.82/1.49  res_backward_subsumed:                  0
% 7.82/1.49  res_forward_subsumption_resolution:     0
% 7.82/1.49  res_backward_subsumption_resolution:    0
% 7.82/1.49  res_clause_to_clause_subsumption:       9569
% 7.82/1.49  res_orphan_elimination:                 0
% 7.82/1.49  res_tautology_del:                      709
% 7.82/1.49  res_num_eq_res_simplified:              0
% 7.82/1.49  res_num_sel_changes:                    0
% 7.82/1.49  res_moves_from_active_to_pass:          0
% 7.82/1.49  
% 7.82/1.49  ------ Superposition
% 7.82/1.49  
% 7.82/1.49  sup_time_total:                         0.
% 7.82/1.49  sup_time_generating:                    0.
% 7.82/1.49  sup_time_sim_full:                      0.
% 7.82/1.49  sup_time_sim_immed:                     0.
% 7.82/1.49  
% 7.82/1.49  sup_num_of_clauses:                     876
% 7.82/1.49  sup_num_in_active:                      209
% 7.82/1.49  sup_num_in_passive:                     667
% 7.82/1.49  sup_num_of_loops:                       249
% 7.82/1.49  sup_fw_superposition:                   864
% 7.82/1.49  sup_bw_superposition:                   1373
% 7.82/1.49  sup_immediate_simplified:               995
% 7.82/1.49  sup_given_eliminated:                   2
% 7.82/1.49  comparisons_done:                       0
% 7.82/1.49  comparisons_avoided:                    0
% 7.82/1.49  
% 7.82/1.49  ------ Simplifications
% 7.82/1.49  
% 7.82/1.49  
% 7.82/1.49  sim_fw_subset_subsumed:                 192
% 7.82/1.49  sim_bw_subset_subsumed:                 54
% 7.82/1.49  sim_fw_subsumed:                        303
% 7.82/1.49  sim_bw_subsumed:                        12
% 7.82/1.49  sim_fw_subsumption_res:                 0
% 7.82/1.49  sim_bw_subsumption_res:                 0
% 7.82/1.49  sim_tautology_del:                      33
% 7.82/1.49  sim_eq_tautology_del:                   171
% 7.82/1.49  sim_eq_res_simp:                        35
% 7.82/1.49  sim_fw_demodulated:                     406
% 7.82/1.49  sim_bw_demodulated:                     33
% 7.82/1.49  sim_light_normalised:                   329
% 7.82/1.49  sim_joinable_taut:                      0
% 7.82/1.49  sim_joinable_simp:                      0
% 7.82/1.49  sim_ac_normalised:                      0
% 7.82/1.49  sim_smt_subsumption:                    0
% 7.82/1.49  
%------------------------------------------------------------------------------
