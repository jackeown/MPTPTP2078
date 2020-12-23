%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0213+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:44 EST 2020

% Result     : Theorem 0.85s
% Output     : CNFRefutation 0.85s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 357 expanded)
%              Number of clauses        :   31 ( 105 expanded)
%              Number of leaves         :    8 ( 111 expanded)
%              Depth                    :   22
%              Number of atoms          :  134 (1986 expanded)
%              Number of equality atoms :   47 ( 305 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   14 (   1 average)
%              Maximal term depth       :   14 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f10])).

fof(f14,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK2(X0,X5),X0)
        & r2_hidden(X5,sK2(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK1(X0,X1),X0)
        & r2_hidden(X2,sK1(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK0(X0,X1),X3) )
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK0(X0,X1),X4) )
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK0(X0,X1),X3) )
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( ( r2_hidden(sK1(X0,X1),X0)
              & r2_hidden(sK0(X0,X1),sK1(X0,X1)) )
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK2(X0,X5),X0)
                & r2_hidden(X5,sK2(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f14,f13,f12])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK1(X0,X1),X0)
      | r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f17,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK2(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f27,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK2(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f17])).

fof(f5,conjecture,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(negated_conjecture,[],[f5])).

fof(f7,plain,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(flattening,[],[f6])).

fof(f25,plain,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

cnf(c_1,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | r2_hidden(sK0(X0,X1),X1)
    | k3_tarski(X0) = X1 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_303,plain,
    ( k3_tarski(X0) = X1
    | r2_hidden(sK1(X0,X1),X0) = iProver_top
    | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_113,plain,
    ( ~ r2_hidden(X0,X1)
    | o_0_0_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_8])).

cnf(c_114,plain,
    ( ~ r2_hidden(X0,o_0_0_xboole_0) ),
    inference(unflattening,[status(thm)],[c_113])).

cnf(c_298,plain,
    ( r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_114])).

cnf(c_648,plain,
    ( k3_tarski(X0) = o_0_0_xboole_0
    | r2_hidden(sK1(X0,o_0_0_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_303,c_298])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k3_tarski(X1))
    | r2_hidden(sK2(X1,X0),X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_300,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | r2_hidden(sK2(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_486,plain,
    ( r2_hidden(X0,k3_tarski(o_0_0_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_300,c_298])).

cnf(c_492,plain,
    ( r2_hidden(X0,k3_tarski(k3_tarski(o_0_0_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_300,c_486])).

cnf(c_568,plain,
    ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(o_0_0_xboole_0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_300,c_492])).

cnf(c_574,plain,
    ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(o_0_0_xboole_0))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_300,c_568])).

cnf(c_969,plain,
    ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(o_0_0_xboole_0)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_300,c_574])).

cnf(c_993,plain,
    ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(o_0_0_xboole_0))))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_300,c_969])).

cnf(c_1155,plain,
    ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(o_0_0_xboole_0)))))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_300,c_993])).

cnf(c_1179,plain,
    ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(o_0_0_xboole_0))))))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_300,c_1155])).

cnf(c_1325,plain,
    ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(o_0_0_xboole_0)))))))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_300,c_1179])).

cnf(c_1349,plain,
    ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(o_0_0_xboole_0))))))))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_300,c_1325])).

cnf(c_1458,plain,
    ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(o_0_0_xboole_0)))))))))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_300,c_1349])).

cnf(c_1728,plain,
    ( k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(o_0_0_xboole_0)))))))))))) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_648,c_1458])).

cnf(c_1482,plain,
    ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(o_0_0_xboole_0))))))))))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_300,c_1458])).

cnf(c_1729,plain,
    ( k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(o_0_0_xboole_0))))))))))))) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_648,c_1482])).

cnf(c_1733,plain,
    ( k3_tarski(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1728,c_1729])).

cnf(c_9,negated_conjecture,
    ( k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_7,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_108,plain,
    ( k1_xboole_0 = X0
    | o_0_0_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_7])).

cnf(c_109,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(unflattening,[status(thm)],[c_108])).

cnf(c_307,plain,
    ( k3_tarski(o_0_0_xboole_0) != o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9,c_109])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1733,c_307])).


%------------------------------------------------------------------------------
