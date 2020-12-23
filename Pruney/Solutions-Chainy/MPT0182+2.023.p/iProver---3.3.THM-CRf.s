%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:27:43 EST 2020

% Result     : Theorem 15.80s
% Output     : CNFRefutation 15.80s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 137 expanded)
%              Number of clauses        :   47 (  52 expanded)
%              Number of leaves         :    5 (  23 expanded)
%              Depth                    :   12
%              Number of atoms          :  283 (1095 expanded)
%              Number of equality atoms :  194 ( 822 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f6,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f7,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f6])).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f7])).

fof(f9,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK0(X0,X1,X2,X3) != X2
            & sK0(X0,X1,X2,X3) != X1
            & sK0(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
        & ( sK0(X0,X1,X2,X3) = X2
          | sK0(X0,X1,X2,X3) = X1
          | sK0(X0,X1,X2,X3) = X0
          | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK0(X0,X1,X2,X3) != X2
              & sK0(X0,X1,X2,X3) != X1
              & sK0(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
          & ( sK0(X0,X1,X2,X3) = X2
            | sK0(X0,X1,X2,X3) = X1
            | sK0(X0,X1,X2,X3) = X0
            | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f9])).

fof(f13,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k1_enumset1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f13])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK0(X0,X1,X2,X3) != X1
      | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f14,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f14])).

fof(f27,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k1_enumset1(X5,X1,X2)) ),
    inference(equality_resolution,[],[f26])).

fof(f15,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f15])).

fof(f25,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k1_enumset1(X0,X5,X2)) ),
    inference(equality_resolution,[],[f24])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK0(X0,X1,X2,X3) != X0
      | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f16,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f16])).

fof(f23,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k1_enumset1(X0,X1,X5)) ),
    inference(equality_resolution,[],[f22])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK0(X0,X1,X2,X3) != X2
      | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK0(X0,X1,X2,X3) = X2
      | sK0(X0,X1,X2,X3) = X1
      | sK0(X0,X1,X2,X3) = X0
      | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    inference(negated_conjecture,[],[f2])).

fof(f5,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2)
   => k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK2,sK1,sK3) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK2,sK1,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f5,f11])).

fof(f21,plain,(
    k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK2,sK1,sK3) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_38650,plain,
    ( ~ r2_hidden(sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)),k1_enumset1(X0,X1,sK3))
    | sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) = X0
    | sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) = X1
    | sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_38773,plain,
    ( ~ r2_hidden(sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)),k1_enumset1(sK2,sK1,sK3))
    | sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) = sK3
    | sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) = sK2
    | sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) = sK1 ),
    inference(instantiation,[status(thm)],[c_38650])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2,X3),X3)
    | sK0(X0,X1,X2,X3) != X1
    | k1_enumset1(X0,X1,X2) = X3 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_38627,plain,
    ( ~ r2_hidden(sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)),k1_enumset1(sK2,sK1,sK3))
    | sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) != sK2
    | k1_enumset1(sK1,sK2,sK3) = k1_enumset1(sK2,sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_38628,plain,
    ( sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) != sK2
    | k1_enumset1(sK1,sK2,sK3) = k1_enumset1(sK2,sK1,sK3)
    | r2_hidden(sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)),k1_enumset1(sK2,sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38627])).

cnf(c_6,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_33341,plain,
    ( r2_hidden(sK2,k1_enumset1(sK2,sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_33342,plain,
    ( r2_hidden(sK2,k1_enumset1(sK2,sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33341])).

cnf(c_5,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X0,X2)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_33012,plain,
    ( r2_hidden(sK1,k1_enumset1(sK2,sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_33013,plain,
    ( r2_hidden(sK1,k1_enumset1(sK2,sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33012])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2,X3),X3)
    | sK0(X0,X1,X2,X3) != X0
    | k1_enumset1(X0,X1,X2) = X3 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_10168,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2,k1_enumset1(X3,X0,X2)),k1_enumset1(X3,X0,X2))
    | sK0(X0,X1,X2,k1_enumset1(X3,X0,X2)) != X0
    | k1_enumset1(X0,X1,X2) = k1_enumset1(X3,X0,X2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_13845,plain,
    ( ~ r2_hidden(sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)),k1_enumset1(sK2,sK1,sK3))
    | sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) != sK1
    | k1_enumset1(sK1,sK2,sK3) = k1_enumset1(sK2,sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_10168])).

cnf(c_13846,plain,
    ( sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) != sK1
    | k1_enumset1(sK1,sK2,sK3) = k1_enumset1(sK2,sK1,sK3)
    | r2_hidden(sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)),k1_enumset1(sK2,sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13845])).

cnf(c_74,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_6599,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k1_enumset1(X2,X3,X4))
    | X0 != X2
    | X1 != k1_enumset1(X2,X3,X4) ),
    inference(instantiation,[status(thm)],[c_74])).

cnf(c_6636,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X0,X1,X2))
    | r2_hidden(X3,k1_enumset1(X0,X1,X2))
    | X3 != X0
    | k1_enumset1(X0,X1,X2) != k1_enumset1(X0,X1,X2) ),
    inference(instantiation,[status(thm)],[c_6599])).

cnf(c_6637,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X0,X1,X2))
    | r2_hidden(X3,k1_enumset1(X0,X1,X2))
    | X3 != X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6636])).

cnf(c_6755,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X0,X1,X2))
    | r2_hidden(sK0(X3,X4,X5,k1_enumset1(X0,X1,X2)),k1_enumset1(X0,X1,X2))
    | sK0(X3,X4,X5,k1_enumset1(X0,X1,X2)) != X0 ),
    inference(instantiation,[status(thm)],[c_6637])).

cnf(c_13474,plain,
    ( r2_hidden(sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)),k1_enumset1(sK2,sK1,sK3))
    | ~ r2_hidden(sK2,k1_enumset1(sK2,sK1,sK3))
    | sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) != sK2 ),
    inference(instantiation,[status(thm)],[c_6755])).

cnf(c_13475,plain,
    ( sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) != sK2
    | r2_hidden(sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)),k1_enumset1(sK2,sK1,sK3)) = iProver_top
    | r2_hidden(sK2,k1_enumset1(sK2,sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13474])).

cnf(c_6596,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k1_enumset1(X3,X2,X4))
    | X0 != X2
    | X1 != k1_enumset1(X3,X2,X4) ),
    inference(instantiation,[status(thm)],[c_74])).

cnf(c_6625,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X0,X2))
    | r2_hidden(X3,k1_enumset1(X1,X0,X2))
    | X3 != X0
    | k1_enumset1(X1,X0,X2) != k1_enumset1(X1,X0,X2) ),
    inference(instantiation,[status(thm)],[c_6596])).

cnf(c_6626,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X0,X2))
    | r2_hidden(X3,k1_enumset1(X1,X0,X2))
    | X3 != X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6625])).

cnf(c_6718,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X0,X2))
    | r2_hidden(sK0(X3,X4,X5,k1_enumset1(X1,X0,X2)),k1_enumset1(X1,X0,X2))
    | sK0(X3,X4,X5,k1_enumset1(X1,X0,X2)) != X0 ),
    inference(instantiation,[status(thm)],[c_6626])).

cnf(c_13471,plain,
    ( r2_hidden(sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)),k1_enumset1(sK2,sK1,sK3))
    | ~ r2_hidden(sK1,k1_enumset1(sK2,sK1,sK3))
    | sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) != sK1 ),
    inference(instantiation,[status(thm)],[c_6718])).

cnf(c_13472,plain,
    ( sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) != sK1
    | r2_hidden(sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)),k1_enumset1(sK2,sK1,sK3)) = iProver_top
    | r2_hidden(sK1,k1_enumset1(sK2,sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13471])).

cnf(c_4,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_11154,plain,
    ( r2_hidden(sK3,k1_enumset1(sK2,sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_11155,plain,
    ( r2_hidden(sK3,k1_enumset1(sK2,sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11154])).

cnf(c_6593,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k1_enumset1(X3,X4,X2))
    | X0 != X2
    | X1 != k1_enumset1(X3,X4,X2) ),
    inference(instantiation,[status(thm)],[c_74])).

cnf(c_6613,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X2,X0))
    | r2_hidden(X3,k1_enumset1(X1,X2,X0))
    | X3 != X0
    | k1_enumset1(X1,X2,X0) != k1_enumset1(X1,X2,X0) ),
    inference(instantiation,[status(thm)],[c_6593])).

cnf(c_6614,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X2,X0))
    | r2_hidden(X3,k1_enumset1(X1,X2,X0))
    | X3 != X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6613])).

cnf(c_6693,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X2,X0))
    | r2_hidden(sK0(X3,X4,X5,k1_enumset1(X1,X2,X0)),k1_enumset1(X1,X2,X0))
    | sK0(X3,X4,X5,k1_enumset1(X1,X2,X0)) != X0 ),
    inference(instantiation,[status(thm)],[c_6614])).

cnf(c_9776,plain,
    ( r2_hidden(sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)),k1_enumset1(sK2,sK1,sK3))
    | ~ r2_hidden(sK3,k1_enumset1(sK2,sK1,sK3))
    | sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) != sK3 ),
    inference(instantiation,[status(thm)],[c_6693])).

cnf(c_9777,plain,
    ( sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) != sK3
    | r2_hidden(sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)),k1_enumset1(sK2,sK1,sK3)) = iProver_top
    | r2_hidden(sK3,k1_enumset1(sK2,sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9776])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2,X3),X3)
    | sK0(X0,X1,X2,X3) != X2
    | k1_enumset1(X0,X1,X2) = X3 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_9773,plain,
    ( ~ r2_hidden(sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)),k1_enumset1(sK2,sK1,sK3))
    | sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) != sK3
    | k1_enumset1(sK1,sK2,sK3) = k1_enumset1(sK2,sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_9774,plain,
    ( sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) != sK3
    | k1_enumset1(sK1,sK2,sK3) = k1_enumset1(sK2,sK1,sK3)
    | r2_hidden(sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)),k1_enumset1(sK2,sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9773])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2,X3),X3)
    | sK0(X0,X1,X2,X3) = X2
    | sK0(X0,X1,X2,X3) = X1
    | sK0(X0,X1,X2,X3) = X0
    | k1_enumset1(X0,X1,X2) = X3 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_6746,plain,
    ( r2_hidden(sK0(X0,X1,X2,k1_enumset1(X3,X0,X4)),k1_enumset1(X3,X0,X4))
    | sK0(X0,X1,X2,k1_enumset1(X3,X0,X4)) = X2
    | sK0(X0,X1,X2,k1_enumset1(X3,X0,X4)) = X1
    | sK0(X0,X1,X2,k1_enumset1(X3,X0,X4)) = X0
    | k1_enumset1(X0,X1,X2) = k1_enumset1(X3,X0,X4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_8423,plain,
    ( r2_hidden(sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)),k1_enumset1(sK2,sK1,sK3))
    | sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) = sK3
    | sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) = sK2
    | sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) = sK1
    | k1_enumset1(sK1,sK2,sK3) = k1_enumset1(sK2,sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_6746])).

cnf(c_8424,plain,
    ( sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) = sK3
    | sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) = sK2
    | sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) = sK1
    | k1_enumset1(sK1,sK2,sK3) = k1_enumset1(sK2,sK1,sK3)
    | r2_hidden(sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)),k1_enumset1(sK2,sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8423])).

cnf(c_8,negated_conjecture,
    ( k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK2,sK1,sK3) ),
    inference(cnf_transformation,[],[f21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_38773,c_38628,c_33342,c_33013,c_13846,c_13475,c_13472,c_11155,c_9777,c_9774,c_8424,c_8423,c_8])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:08:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.80/2.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.80/2.49  
% 15.80/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.80/2.49  
% 15.80/2.49  ------  iProver source info
% 15.80/2.49  
% 15.80/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.80/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.80/2.49  git: non_committed_changes: false
% 15.80/2.49  git: last_make_outside_of_git: false
% 15.80/2.49  
% 15.80/2.49  ------ 
% 15.80/2.49  ------ Parsing...
% 15.80/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.80/2.49  
% 15.80/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 15.80/2.49  
% 15.80/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.80/2.49  
% 15.80/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.80/2.49  ------ Proving...
% 15.80/2.49  ------ Problem Properties 
% 15.80/2.49  
% 15.80/2.49  
% 15.80/2.49  clauses                                 9
% 15.80/2.49  conjectures                             1
% 15.80/2.49  EPR                                     0
% 15.80/2.49  Horn                                    7
% 15.80/2.49  unary                                   4
% 15.80/2.49  binary                                  0
% 15.80/2.49  lits                                    22
% 15.80/2.49  lits eq                                 14
% 15.80/2.49  fd_pure                                 0
% 15.80/2.49  fd_pseudo                               0
% 15.80/2.49  fd_cond                                 0
% 15.80/2.49  fd_pseudo_cond                          4
% 15.80/2.49  AC symbols                              0
% 15.80/2.49  
% 15.80/2.49  ------ Input Options Time Limit: Unbounded
% 15.80/2.49  
% 15.80/2.49  
% 15.80/2.49  
% 15.80/2.49  
% 15.80/2.49  ------ Preprocessing...
% 15.80/2.49  
% 15.80/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 15.80/2.49  Current options:
% 15.80/2.49  ------ 
% 15.80/2.49  
% 15.80/2.49  
% 15.80/2.49  
% 15.80/2.49  
% 15.80/2.49  ------ Proving...
% 15.80/2.49  
% 15.80/2.49  
% 15.80/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.80/2.49  
% 15.80/2.49  ------ Proving...
% 15.80/2.49  
% 15.80/2.49  
% 15.80/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.80/2.49  
% 15.80/2.49  ------ Proving...
% 15.80/2.49  
% 15.80/2.49  
% 15.80/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.80/2.49  
% 15.80/2.49  ------ Proving...
% 15.80/2.49  
% 15.80/2.49  
% 15.80/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.80/2.49  
% 15.80/2.49  ------ Proving...
% 15.80/2.49  
% 15.80/2.49  
% 15.80/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.80/2.49  
% 15.80/2.49  ------ Proving...
% 15.80/2.49  
% 15.80/2.49  
% 15.80/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.80/2.49  
% 15.80/2.49  ------ Proving...
% 15.80/2.49  
% 15.80/2.49  
% 15.80/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.80/2.49  
% 15.80/2.49  ------ Proving...
% 15.80/2.49  
% 15.80/2.49  
% 15.80/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.80/2.49  
% 15.80/2.49  ------ Proving...
% 15.80/2.49  
% 15.80/2.49  
% 15.80/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.80/2.49  
% 15.80/2.49  ------ Proving...
% 15.80/2.49  
% 15.80/2.49  
% 15.80/2.49  % SZS status Theorem for theBenchmark.p
% 15.80/2.49  
% 15.80/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.80/2.49  
% 15.80/2.49  fof(f1,axiom,(
% 15.80/2.49    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 15.80/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.80/2.49  
% 15.80/2.49  fof(f4,plain,(
% 15.80/2.49    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 15.80/2.49    inference(ennf_transformation,[],[f1])).
% 15.80/2.49  
% 15.80/2.49  fof(f6,plain,(
% 15.80/2.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 15.80/2.49    inference(nnf_transformation,[],[f4])).
% 15.80/2.49  
% 15.80/2.49  fof(f7,plain,(
% 15.80/2.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 15.80/2.49    inference(flattening,[],[f6])).
% 15.80/2.49  
% 15.80/2.49  fof(f8,plain,(
% 15.80/2.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 15.80/2.49    inference(rectify,[],[f7])).
% 15.80/2.49  
% 15.80/2.49  fof(f9,plain,(
% 15.80/2.49    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 15.80/2.49    introduced(choice_axiom,[])).
% 15.80/2.49  
% 15.80/2.49  fof(f10,plain,(
% 15.80/2.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 15.80/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f9])).
% 15.80/2.49  
% 15.80/2.49  fof(f13,plain,(
% 15.80/2.49    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 15.80/2.49    inference(cnf_transformation,[],[f10])).
% 15.80/2.49  
% 15.80/2.49  fof(f28,plain,(
% 15.80/2.49    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k1_enumset1(X0,X1,X2))) )),
% 15.80/2.49    inference(equality_resolution,[],[f13])).
% 15.80/2.49  
% 15.80/2.49  fof(f19,plain,(
% 15.80/2.49    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK0(X0,X1,X2,X3) != X1 | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) )),
% 15.80/2.49    inference(cnf_transformation,[],[f10])).
% 15.80/2.49  
% 15.80/2.49  fof(f14,plain,(
% 15.80/2.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 15.80/2.49    inference(cnf_transformation,[],[f10])).
% 15.80/2.49  
% 15.80/2.49  fof(f26,plain,(
% 15.80/2.49    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X5,X1,X2) != X3) )),
% 15.80/2.49    inference(equality_resolution,[],[f14])).
% 15.80/2.49  
% 15.80/2.49  fof(f27,plain,(
% 15.80/2.49    ( ! [X2,X5,X1] : (r2_hidden(X5,k1_enumset1(X5,X1,X2))) )),
% 15.80/2.49    inference(equality_resolution,[],[f26])).
% 15.80/2.49  
% 15.80/2.49  fof(f15,plain,(
% 15.80/2.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 15.80/2.49    inference(cnf_transformation,[],[f10])).
% 15.80/2.49  
% 15.80/2.49  fof(f24,plain,(
% 15.80/2.49    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k1_enumset1(X0,X5,X2) != X3) )),
% 15.80/2.49    inference(equality_resolution,[],[f15])).
% 15.80/2.49  
% 15.80/2.49  fof(f25,plain,(
% 15.80/2.49    ( ! [X2,X0,X5] : (r2_hidden(X5,k1_enumset1(X0,X5,X2))) )),
% 15.80/2.49    inference(equality_resolution,[],[f24])).
% 15.80/2.49  
% 15.80/2.49  fof(f18,plain,(
% 15.80/2.49    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK0(X0,X1,X2,X3) != X0 | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) )),
% 15.80/2.49    inference(cnf_transformation,[],[f10])).
% 15.80/2.49  
% 15.80/2.49  fof(f16,plain,(
% 15.80/2.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 15.80/2.49    inference(cnf_transformation,[],[f10])).
% 15.80/2.49  
% 15.80/2.49  fof(f22,plain,(
% 15.80/2.49    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X0,X1,X5) != X3) )),
% 15.80/2.49    inference(equality_resolution,[],[f16])).
% 15.80/2.49  
% 15.80/2.49  fof(f23,plain,(
% 15.80/2.49    ( ! [X0,X5,X1] : (r2_hidden(X5,k1_enumset1(X0,X1,X5))) )),
% 15.80/2.49    inference(equality_resolution,[],[f22])).
% 15.80/2.49  
% 15.80/2.49  fof(f20,plain,(
% 15.80/2.49    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK0(X0,X1,X2,X3) != X2 | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) )),
% 15.80/2.49    inference(cnf_transformation,[],[f10])).
% 15.80/2.49  
% 15.80/2.49  fof(f17,plain,(
% 15.80/2.49    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)) )),
% 15.80/2.49    inference(cnf_transformation,[],[f10])).
% 15.80/2.49  
% 15.80/2.49  fof(f2,conjecture,(
% 15.80/2.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)),
% 15.80/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.80/2.49  
% 15.80/2.49  fof(f3,negated_conjecture,(
% 15.80/2.49    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)),
% 15.80/2.49    inference(negated_conjecture,[],[f2])).
% 15.80/2.49  
% 15.80/2.49  fof(f5,plain,(
% 15.80/2.49    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2)),
% 15.80/2.49    inference(ennf_transformation,[],[f3])).
% 15.80/2.49  
% 15.80/2.49  fof(f11,plain,(
% 15.80/2.49    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2) => k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK2,sK1,sK3)),
% 15.80/2.49    introduced(choice_axiom,[])).
% 15.80/2.49  
% 15.80/2.49  fof(f12,plain,(
% 15.80/2.49    k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK2,sK1,sK3)),
% 15.80/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f5,f11])).
% 15.80/2.49  
% 15.80/2.49  fof(f21,plain,(
% 15.80/2.49    k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK2,sK1,sK3)),
% 15.80/2.49    inference(cnf_transformation,[],[f12])).
% 15.80/2.49  
% 15.80/2.49  cnf(c_7,plain,
% 15.80/2.49      ( ~ r2_hidden(X0,k1_enumset1(X1,X2,X3))
% 15.80/2.49      | X0 = X1
% 15.80/2.49      | X0 = X2
% 15.80/2.49      | X0 = X3 ),
% 15.80/2.49      inference(cnf_transformation,[],[f28]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_38650,plain,
% 15.80/2.49      ( ~ r2_hidden(sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)),k1_enumset1(X0,X1,sK3))
% 15.80/2.49      | sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) = X0
% 15.80/2.49      | sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) = X1
% 15.80/2.49      | sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) = sK3 ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_7]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_38773,plain,
% 15.80/2.49      ( ~ r2_hidden(sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)),k1_enumset1(sK2,sK1,sK3))
% 15.80/2.49      | sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) = sK3
% 15.80/2.49      | sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) = sK2
% 15.80/2.49      | sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) = sK1 ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_38650]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_1,plain,
% 15.80/2.49      ( ~ r2_hidden(sK0(X0,X1,X2,X3),X3)
% 15.80/2.49      | sK0(X0,X1,X2,X3) != X1
% 15.80/2.49      | k1_enumset1(X0,X1,X2) = X3 ),
% 15.80/2.49      inference(cnf_transformation,[],[f19]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_38627,plain,
% 15.80/2.49      ( ~ r2_hidden(sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)),k1_enumset1(sK2,sK1,sK3))
% 15.80/2.49      | sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) != sK2
% 15.80/2.49      | k1_enumset1(sK1,sK2,sK3) = k1_enumset1(sK2,sK1,sK3) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_1]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_38628,plain,
% 15.80/2.49      ( sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) != sK2
% 15.80/2.49      | k1_enumset1(sK1,sK2,sK3) = k1_enumset1(sK2,sK1,sK3)
% 15.80/2.49      | r2_hidden(sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)),k1_enumset1(sK2,sK1,sK3)) != iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_38627]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6,plain,
% 15.80/2.49      ( r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
% 15.80/2.49      inference(cnf_transformation,[],[f27]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_33341,plain,
% 15.80/2.49      ( r2_hidden(sK2,k1_enumset1(sK2,sK1,sK3)) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_6]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_33342,plain,
% 15.80/2.49      ( r2_hidden(sK2,k1_enumset1(sK2,sK1,sK3)) = iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_33341]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_5,plain,
% 15.80/2.49      ( r2_hidden(X0,k1_enumset1(X1,X0,X2)) ),
% 15.80/2.49      inference(cnf_transformation,[],[f25]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_33012,plain,
% 15.80/2.49      ( r2_hidden(sK1,k1_enumset1(sK2,sK1,sK3)) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_5]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_33013,plain,
% 15.80/2.49      ( r2_hidden(sK1,k1_enumset1(sK2,sK1,sK3)) = iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_33012]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_2,plain,
% 15.80/2.49      ( ~ r2_hidden(sK0(X0,X1,X2,X3),X3)
% 15.80/2.49      | sK0(X0,X1,X2,X3) != X0
% 15.80/2.49      | k1_enumset1(X0,X1,X2) = X3 ),
% 15.80/2.49      inference(cnf_transformation,[],[f18]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_10168,plain,
% 15.80/2.49      ( ~ r2_hidden(sK0(X0,X1,X2,k1_enumset1(X3,X0,X2)),k1_enumset1(X3,X0,X2))
% 15.80/2.49      | sK0(X0,X1,X2,k1_enumset1(X3,X0,X2)) != X0
% 15.80/2.49      | k1_enumset1(X0,X1,X2) = k1_enumset1(X3,X0,X2) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_2]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_13845,plain,
% 15.80/2.49      ( ~ r2_hidden(sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)),k1_enumset1(sK2,sK1,sK3))
% 15.80/2.49      | sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) != sK1
% 15.80/2.49      | k1_enumset1(sK1,sK2,sK3) = k1_enumset1(sK2,sK1,sK3) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_10168]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_13846,plain,
% 15.80/2.49      ( sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) != sK1
% 15.80/2.49      | k1_enumset1(sK1,sK2,sK3) = k1_enumset1(sK2,sK1,sK3)
% 15.80/2.49      | r2_hidden(sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)),k1_enumset1(sK2,sK1,sK3)) != iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_13845]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_74,plain,
% 15.80/2.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.80/2.49      theory(equality) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6599,plain,
% 15.80/2.49      ( r2_hidden(X0,X1)
% 15.80/2.49      | ~ r2_hidden(X2,k1_enumset1(X2,X3,X4))
% 15.80/2.49      | X0 != X2
% 15.80/2.49      | X1 != k1_enumset1(X2,X3,X4) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_74]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6636,plain,
% 15.80/2.49      ( ~ r2_hidden(X0,k1_enumset1(X0,X1,X2))
% 15.80/2.49      | r2_hidden(X3,k1_enumset1(X0,X1,X2))
% 15.80/2.49      | X3 != X0
% 15.80/2.49      | k1_enumset1(X0,X1,X2) != k1_enumset1(X0,X1,X2) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_6599]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6637,plain,
% 15.80/2.49      ( ~ r2_hidden(X0,k1_enumset1(X0,X1,X2))
% 15.80/2.49      | r2_hidden(X3,k1_enumset1(X0,X1,X2))
% 15.80/2.49      | X3 != X0 ),
% 15.80/2.49      inference(equality_resolution_simp,[status(thm)],[c_6636]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6755,plain,
% 15.80/2.49      ( ~ r2_hidden(X0,k1_enumset1(X0,X1,X2))
% 15.80/2.49      | r2_hidden(sK0(X3,X4,X5,k1_enumset1(X0,X1,X2)),k1_enumset1(X0,X1,X2))
% 15.80/2.49      | sK0(X3,X4,X5,k1_enumset1(X0,X1,X2)) != X0 ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_6637]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_13474,plain,
% 15.80/2.49      ( r2_hidden(sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)),k1_enumset1(sK2,sK1,sK3))
% 15.80/2.49      | ~ r2_hidden(sK2,k1_enumset1(sK2,sK1,sK3))
% 15.80/2.49      | sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) != sK2 ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_6755]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_13475,plain,
% 15.80/2.49      ( sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) != sK2
% 15.80/2.49      | r2_hidden(sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)),k1_enumset1(sK2,sK1,sK3)) = iProver_top
% 15.80/2.49      | r2_hidden(sK2,k1_enumset1(sK2,sK1,sK3)) != iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_13474]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6596,plain,
% 15.80/2.49      ( r2_hidden(X0,X1)
% 15.80/2.49      | ~ r2_hidden(X2,k1_enumset1(X3,X2,X4))
% 15.80/2.49      | X0 != X2
% 15.80/2.49      | X1 != k1_enumset1(X3,X2,X4) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_74]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6625,plain,
% 15.80/2.49      ( ~ r2_hidden(X0,k1_enumset1(X1,X0,X2))
% 15.80/2.49      | r2_hidden(X3,k1_enumset1(X1,X0,X2))
% 15.80/2.49      | X3 != X0
% 15.80/2.49      | k1_enumset1(X1,X0,X2) != k1_enumset1(X1,X0,X2) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_6596]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6626,plain,
% 15.80/2.49      ( ~ r2_hidden(X0,k1_enumset1(X1,X0,X2))
% 15.80/2.49      | r2_hidden(X3,k1_enumset1(X1,X0,X2))
% 15.80/2.49      | X3 != X0 ),
% 15.80/2.49      inference(equality_resolution_simp,[status(thm)],[c_6625]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6718,plain,
% 15.80/2.49      ( ~ r2_hidden(X0,k1_enumset1(X1,X0,X2))
% 15.80/2.49      | r2_hidden(sK0(X3,X4,X5,k1_enumset1(X1,X0,X2)),k1_enumset1(X1,X0,X2))
% 15.80/2.49      | sK0(X3,X4,X5,k1_enumset1(X1,X0,X2)) != X0 ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_6626]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_13471,plain,
% 15.80/2.49      ( r2_hidden(sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)),k1_enumset1(sK2,sK1,sK3))
% 15.80/2.49      | ~ r2_hidden(sK1,k1_enumset1(sK2,sK1,sK3))
% 15.80/2.49      | sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) != sK1 ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_6718]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_13472,plain,
% 15.80/2.49      ( sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) != sK1
% 15.80/2.49      | r2_hidden(sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)),k1_enumset1(sK2,sK1,sK3)) = iProver_top
% 15.80/2.49      | r2_hidden(sK1,k1_enumset1(sK2,sK1,sK3)) != iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_13471]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_4,plain,
% 15.80/2.49      ( r2_hidden(X0,k1_enumset1(X1,X2,X0)) ),
% 15.80/2.49      inference(cnf_transformation,[],[f23]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_11154,plain,
% 15.80/2.49      ( r2_hidden(sK3,k1_enumset1(sK2,sK1,sK3)) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_4]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_11155,plain,
% 15.80/2.49      ( r2_hidden(sK3,k1_enumset1(sK2,sK1,sK3)) = iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_11154]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6593,plain,
% 15.80/2.49      ( r2_hidden(X0,X1)
% 15.80/2.49      | ~ r2_hidden(X2,k1_enumset1(X3,X4,X2))
% 15.80/2.49      | X0 != X2
% 15.80/2.49      | X1 != k1_enumset1(X3,X4,X2) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_74]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6613,plain,
% 15.80/2.49      ( ~ r2_hidden(X0,k1_enumset1(X1,X2,X0))
% 15.80/2.49      | r2_hidden(X3,k1_enumset1(X1,X2,X0))
% 15.80/2.49      | X3 != X0
% 15.80/2.49      | k1_enumset1(X1,X2,X0) != k1_enumset1(X1,X2,X0) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_6593]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6614,plain,
% 15.80/2.49      ( ~ r2_hidden(X0,k1_enumset1(X1,X2,X0))
% 15.80/2.49      | r2_hidden(X3,k1_enumset1(X1,X2,X0))
% 15.80/2.49      | X3 != X0 ),
% 15.80/2.49      inference(equality_resolution_simp,[status(thm)],[c_6613]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6693,plain,
% 15.80/2.49      ( ~ r2_hidden(X0,k1_enumset1(X1,X2,X0))
% 15.80/2.49      | r2_hidden(sK0(X3,X4,X5,k1_enumset1(X1,X2,X0)),k1_enumset1(X1,X2,X0))
% 15.80/2.49      | sK0(X3,X4,X5,k1_enumset1(X1,X2,X0)) != X0 ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_6614]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_9776,plain,
% 15.80/2.49      ( r2_hidden(sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)),k1_enumset1(sK2,sK1,sK3))
% 15.80/2.49      | ~ r2_hidden(sK3,k1_enumset1(sK2,sK1,sK3))
% 15.80/2.49      | sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) != sK3 ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_6693]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_9777,plain,
% 15.80/2.49      ( sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) != sK3
% 15.80/2.49      | r2_hidden(sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)),k1_enumset1(sK2,sK1,sK3)) = iProver_top
% 15.80/2.49      | r2_hidden(sK3,k1_enumset1(sK2,sK1,sK3)) != iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_9776]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_0,plain,
% 15.80/2.49      ( ~ r2_hidden(sK0(X0,X1,X2,X3),X3)
% 15.80/2.49      | sK0(X0,X1,X2,X3) != X2
% 15.80/2.49      | k1_enumset1(X0,X1,X2) = X3 ),
% 15.80/2.49      inference(cnf_transformation,[],[f20]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_9773,plain,
% 15.80/2.49      ( ~ r2_hidden(sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)),k1_enumset1(sK2,sK1,sK3))
% 15.80/2.49      | sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) != sK3
% 15.80/2.49      | k1_enumset1(sK1,sK2,sK3) = k1_enumset1(sK2,sK1,sK3) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_0]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_9774,plain,
% 15.80/2.49      ( sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) != sK3
% 15.80/2.49      | k1_enumset1(sK1,sK2,sK3) = k1_enumset1(sK2,sK1,sK3)
% 15.80/2.49      | r2_hidden(sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)),k1_enumset1(sK2,sK1,sK3)) != iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_9773]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_3,plain,
% 15.80/2.49      ( r2_hidden(sK0(X0,X1,X2,X3),X3)
% 15.80/2.49      | sK0(X0,X1,X2,X3) = X2
% 15.80/2.49      | sK0(X0,X1,X2,X3) = X1
% 15.80/2.49      | sK0(X0,X1,X2,X3) = X0
% 15.80/2.49      | k1_enumset1(X0,X1,X2) = X3 ),
% 15.80/2.49      inference(cnf_transformation,[],[f17]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6746,plain,
% 15.80/2.49      ( r2_hidden(sK0(X0,X1,X2,k1_enumset1(X3,X0,X4)),k1_enumset1(X3,X0,X4))
% 15.80/2.49      | sK0(X0,X1,X2,k1_enumset1(X3,X0,X4)) = X2
% 15.80/2.49      | sK0(X0,X1,X2,k1_enumset1(X3,X0,X4)) = X1
% 15.80/2.49      | sK0(X0,X1,X2,k1_enumset1(X3,X0,X4)) = X0
% 15.80/2.49      | k1_enumset1(X0,X1,X2) = k1_enumset1(X3,X0,X4) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_3]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_8423,plain,
% 15.80/2.49      ( r2_hidden(sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)),k1_enumset1(sK2,sK1,sK3))
% 15.80/2.49      | sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) = sK3
% 15.80/2.49      | sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) = sK2
% 15.80/2.49      | sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) = sK1
% 15.80/2.49      | k1_enumset1(sK1,sK2,sK3) = k1_enumset1(sK2,sK1,sK3) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_6746]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_8424,plain,
% 15.80/2.49      ( sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) = sK3
% 15.80/2.49      | sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) = sK2
% 15.80/2.49      | sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)) = sK1
% 15.80/2.49      | k1_enumset1(sK1,sK2,sK3) = k1_enumset1(sK2,sK1,sK3)
% 15.80/2.49      | r2_hidden(sK0(sK1,sK2,sK3,k1_enumset1(sK2,sK1,sK3)),k1_enumset1(sK2,sK1,sK3)) = iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_8423]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_8,negated_conjecture,
% 15.80/2.49      ( k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK2,sK1,sK3) ),
% 15.80/2.49      inference(cnf_transformation,[],[f21]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(contradiction,plain,
% 15.80/2.49      ( $false ),
% 15.80/2.49      inference(minisat,
% 15.80/2.49                [status(thm)],
% 15.80/2.49                [c_38773,c_38628,c_33342,c_33013,c_13846,c_13475,c_13472,
% 15.80/2.49                 c_11155,c_9777,c_9774,c_8424,c_8423,c_8]) ).
% 15.80/2.49  
% 15.80/2.49  
% 15.80/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.80/2.49  
% 15.80/2.49  ------                               Statistics
% 15.80/2.49  
% 15.80/2.49  ------ Selected
% 15.80/2.49  
% 15.80/2.49  total_time:                             1.74
% 15.80/2.49  
%------------------------------------------------------------------------------
