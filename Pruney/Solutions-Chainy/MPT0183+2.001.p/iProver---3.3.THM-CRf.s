%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:27:44 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 3.95s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 787 expanded)
%              Number of clauses        :   57 ( 182 expanded)
%              Number of leaves         :    8 ( 191 expanded)
%              Depth                    :   18
%              Number of atoms          :  346 (4517 expanded)
%              Number of equality atoms :  250 (3526 expanded)
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

fof(f5,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f1])).

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
    inference(nnf_transformation,[],[f5])).

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
    inference(flattening,[],[f7])).

fof(f9,plain,(
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
    inference(rectify,[],[f8])).

fof(f10,plain,(
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

fof(f11,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).

fof(f17,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f17,f22])).

fof(f33,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f28])).

fof(f34,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f33])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK0(X0,X1,X2,X3) = X2
      | sK0(X0,X1,X2,X3) = X1
      | sK0(X0,X1,X2,X3) = X0
      | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_enumset1(X0,X0,X1,X2) = X3
      | sK0(X0,X1,X2,X3) = X2
      | sK0(X0,X1,X2,X3) = X1
      | sK0(X0,X1,X2,X3) = X0
      | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ),
    inference(definition_unfolding,[],[f18,f22])).

fof(f3,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(negated_conjecture,[],[f3])).

fof(f6,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X2,X0) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X2,X0)
   => k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK2,sK3,sK1) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK2,sK3,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f6,f12])).

fof(f23,plain,(
    k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK2,sK3,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f32,plain,(
    k2_enumset1(sK1,sK1,sK2,sK3) != k2_enumset1(sK2,sK2,sK3,sK1) ),
    inference(definition_unfolding,[],[f23,f22,f22])).

fof(f14,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f14,f22])).

fof(f39,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK0(X0,X1,X2,X3) != X2
      | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_enumset1(X0,X0,X1,X2) = X3
      | sK0(X0,X1,X2,X3) != X2
      | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) ) ),
    inference(definition_unfolding,[],[f21,f22])).

fof(f16,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f16,f22])).

fof(f35,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f29])).

fof(f36,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k2_enumset1(X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f35])).

fof(f15,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f15,f22])).

fof(f37,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f30])).

fof(f38,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k2_enumset1(X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f37])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK0(X0,X1,X2,X3) != X1
      | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_enumset1(X0,X0,X1,X2) = X3
      | sK0(X0,X1,X2,X3) != X1
      | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) ) ),
    inference(definition_unfolding,[],[f20,f22])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK0(X0,X1,X2,X3) != X0
      | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_enumset1(X0,X0,X1,X2) = X3
      | sK0(X0,X1,X2,X3) != X0
      | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) ) ),
    inference(definition_unfolding,[],[f19,f22])).

cnf(c_4,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_10280,plain,
    ( r2_hidden(sK1,k2_enumset1(sK2,sK2,sK3,sK1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_74,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_6567,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k2_enumset1(X3,X3,X4,X2))
    | X0 != X2
    | X1 != k2_enumset1(X3,X3,X4,X2) ),
    inference(instantiation,[status(thm)],[c_74])).

cnf(c_6590,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X0))
    | r2_hidden(X3,k2_enumset1(X1,X1,X2,X0))
    | X3 != X0
    | k2_enumset1(X1,X1,X2,X0) != k2_enumset1(X1,X1,X2,X0) ),
    inference(instantiation,[status(thm)],[c_6567])).

cnf(c_6591,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X0))
    | r2_hidden(X3,k2_enumset1(X1,X1,X2,X0))
    | X3 != X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6590])).

cnf(c_6682,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X0))
    | r2_hidden(sK0(X3,X4,X5,k2_enumset1(X1,X1,X2,X0)),k2_enumset1(X1,X1,X2,X0))
    | sK0(X3,X4,X5,k2_enumset1(X1,X1,X2,X0)) != X0 ),
    inference(instantiation,[status(thm)],[c_6591])).

cnf(c_10263,plain,
    ( r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)),k2_enumset1(sK2,sK2,sK3,sK1))
    | ~ r2_hidden(sK1,k2_enumset1(sK2,sK2,sK3,sK1))
    | sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) != sK1 ),
    inference(instantiation,[status(thm)],[c_6682])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2,X3),X3)
    | sK0(X0,X1,X2,X3) = X2
    | sK0(X0,X1,X2,X3) = X1
    | sK0(X0,X1,X2,X3) = X0
    | k2_enumset1(X0,X0,X1,X2) = X3 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_8,negated_conjecture,
    ( k2_enumset1(sK1,sK1,sK2,sK3) != k2_enumset1(sK2,sK2,sK3,sK1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_7000,plain,
    ( r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)),k2_enumset1(sK2,sK2,sK3,sK1))
    | sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK3
    | sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK2
    | sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK1 ),
    inference(resolution,[status(thm)],[c_3,c_8])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_7042,plain,
    ( sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK3
    | sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK2
    | sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7000,c_7])).

cnf(c_71,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_6658,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_74,c_71])).

cnf(c_7054,plain,
    ( r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)),X0)
    | ~ r2_hidden(sK3,X0)
    | sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK2
    | sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK1 ),
    inference(resolution,[status(thm)],[c_7042,c_6658])).

cnf(c_7001,plain,
    ( sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK3
    | sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK2
    | sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK1
    | r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)),k2_enumset1(sK2,sK2,sK3,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7000])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2,X3),X3)
    | sK0(X0,X1,X2,X3) != X2
    | k2_enumset1(X0,X0,X1,X2) = X3 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_7052,plain,
    ( ~ r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)),k2_enumset1(sK2,sK2,sK3,sK1))
    | sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK2
    | sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK1
    | k2_enumset1(sK1,sK1,sK2,sK3) = k2_enumset1(sK2,sK2,sK3,sK1) ),
    inference(resolution,[status(thm)],[c_7042,c_0])).

cnf(c_7053,plain,
    ( sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK2
    | sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK1
    | k2_enumset1(sK1,sK1,sK2,sK3) = k2_enumset1(sK2,sK2,sK3,sK1)
    | r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)),k2_enumset1(sK2,sK2,sK3,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7052])).

cnf(c_6570,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k2_enumset1(X3,X3,X2,X4))
    | X0 != X2
    | X1 != k2_enumset1(X3,X3,X2,X4) ),
    inference(instantiation,[status(thm)],[c_74])).

cnf(c_6601,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X0,X2))
    | r2_hidden(X3,k2_enumset1(X1,X1,X0,X2))
    | X3 != X0
    | k2_enumset1(X1,X1,X0,X2) != k2_enumset1(X1,X1,X0,X2) ),
    inference(instantiation,[status(thm)],[c_6570])).

cnf(c_6602,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X0,X2))
    | r2_hidden(X3,k2_enumset1(X1,X1,X0,X2))
    | X3 != X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6601])).

cnf(c_6717,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X0,X2))
    | r2_hidden(sK0(X3,X4,X5,k2_enumset1(X1,X1,X0,X2)),k2_enumset1(X1,X1,X0,X2))
    | sK0(X3,X4,X5,k2_enumset1(X1,X1,X0,X2)) != X0 ),
    inference(instantiation,[status(thm)],[c_6602])).

cnf(c_7166,plain,
    ( r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)),k2_enumset1(sK2,sK2,sK3,sK1))
    | ~ r2_hidden(sK3,k2_enumset1(sK2,sK2,sK3,sK1))
    | sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) != sK3 ),
    inference(instantiation,[status(thm)],[c_6717])).

cnf(c_7167,plain,
    ( sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) != sK3
    | r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)),k2_enumset1(sK2,sK2,sK3,sK1)) = iProver_top
    | r2_hidden(sK3,k2_enumset1(sK2,sK2,sK3,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7166])).

cnf(c_5,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_8814,plain,
    ( r2_hidden(sK3,k2_enumset1(sK2,sK2,sK3,sK1)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_8815,plain,
    ( r2_hidden(sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8814])).

cnf(c_9265,plain,
    ( sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK2
    | sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7054,c_8,c_7001,c_7053,c_7167,c_8815])).

cnf(c_72,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2013,plain,
    ( k2_enumset1(sK2,sK2,sK3,sK1) != X0
    | k2_enumset1(sK1,sK1,sK2,sK3) != X0
    | k2_enumset1(sK1,sK1,sK2,sK3) = k2_enumset1(sK2,sK2,sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_72])).

cnf(c_2483,plain,
    ( k2_enumset1(sK2,sK2,sK3,sK1) != k2_enumset1(X0,X1,X2,X3)
    | k2_enumset1(sK1,sK1,sK2,sK3) != k2_enumset1(X0,X1,X2,X3)
    | k2_enumset1(sK1,sK1,sK2,sK3) = k2_enumset1(sK2,sK2,sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_2013])).

cnf(c_2590,plain,
    ( k2_enumset1(sK2,sK2,sK3,sK1) != k2_enumset1(sK1,sK1,sK2,sK3)
    | k2_enumset1(sK1,sK1,sK2,sK3) = k2_enumset1(sK2,sK2,sK3,sK1)
    | k2_enumset1(sK1,sK1,sK2,sK3) != k2_enumset1(sK1,sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2483])).

cnf(c_2591,plain,
    ( k2_enumset1(sK2,sK2,sK3,sK1) != k2_enumset1(sK1,sK1,sK2,sK3)
    | k2_enumset1(sK1,sK1,sK2,sK3) = k2_enumset1(sK2,sK2,sK3,sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_2590])).

cnf(c_6573,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k2_enumset1(X2,X2,X3,X4))
    | X0 != X2
    | X1 != k2_enumset1(X2,X2,X3,X4) ),
    inference(instantiation,[status(thm)],[c_74])).

cnf(c_6611,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X0,X0,X1,X2))
    | r2_hidden(X3,k2_enumset1(X0,X0,X1,X2))
    | X3 != X0
    | k2_enumset1(X0,X0,X1,X2) != k2_enumset1(X0,X0,X1,X2) ),
    inference(instantiation,[status(thm)],[c_6573])).

cnf(c_6612,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X0,X0,X1,X2))
    | r2_hidden(X3,k2_enumset1(X0,X0,X1,X2))
    | X3 != X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6611])).

cnf(c_6727,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X0,X0,X1,X2))
    | r2_hidden(sK0(X3,X4,X5,k2_enumset1(X0,X0,X1,X2)),k2_enumset1(X0,X0,X1,X2))
    | sK0(X3,X4,X5,k2_enumset1(X0,X0,X1,X2)) != X0 ),
    inference(instantiation,[status(thm)],[c_6612])).

cnf(c_9279,plain,
    ( r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)),k2_enumset1(sK2,sK2,sK3,sK1))
    | ~ r2_hidden(sK2,k2_enumset1(sK2,sK2,sK3,sK1))
    | sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) != sK2 ),
    inference(instantiation,[status(thm)],[c_6727])).

cnf(c_9280,plain,
    ( sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) != sK2
    | r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)),k2_enumset1(sK2,sK2,sK3,sK1)) = iProver_top
    | r2_hidden(sK2,k2_enumset1(sK2,sK2,sK3,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9279])).

cnf(c_6,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_9352,plain,
    ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK3,sK1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_9353,plain,
    ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK3,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9352])).

cnf(c_6477,plain,
    ( sK0(X0,X1,X2,X3) = X2
    | sK0(X0,X1,X2,X3) = X1
    | sK0(X0,X1,X2,X3) = X0
    | k2_enumset1(X0,X0,X1,X2) = X3
    | r2_hidden(sK0(X0,X1,X2,X3),X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6473,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | r2_hidden(X0,k2_enumset1(X1,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_7192,plain,
    ( sK0(X0,X1,X2,k2_enumset1(X3,X3,X4,X5)) = X5
    | sK0(X0,X1,X2,k2_enumset1(X3,X3,X4,X5)) = X4
    | sK0(X0,X1,X2,k2_enumset1(X3,X3,X4,X5)) = X3
    | sK0(X0,X1,X2,k2_enumset1(X3,X3,X4,X5)) = X2
    | sK0(X0,X1,X2,k2_enumset1(X3,X3,X4,X5)) = X1
    | sK0(X0,X1,X2,k2_enumset1(X3,X3,X4,X5)) = X0
    | k2_enumset1(X3,X3,X4,X5) = k2_enumset1(X0,X0,X1,X2) ),
    inference(superposition,[status(thm)],[c_6477,c_6473])).

cnf(c_7251,plain,
    ( sK0(X0,X1,X2,k2_enumset1(sK2,sK2,sK3,sK1)) = X2
    | sK0(X0,X1,X2,k2_enumset1(sK2,sK2,sK3,sK1)) = X1
    | sK0(X0,X1,X2,k2_enumset1(sK2,sK2,sK3,sK1)) = X0
    | sK0(X0,X1,X2,k2_enumset1(sK2,sK2,sK3,sK1)) = sK3
    | sK0(X0,X1,X2,k2_enumset1(sK2,sK2,sK3,sK1)) = sK2
    | sK0(X0,X1,X2,k2_enumset1(sK2,sK2,sK3,sK1)) = sK1
    | k2_enumset1(X0,X0,X1,X2) != k2_enumset1(sK1,sK1,sK2,sK3) ),
    inference(superposition,[status(thm)],[c_7192,c_8])).

cnf(c_8931,plain,
    ( sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK3
    | sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK2
    | sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK1 ),
    inference(equality_resolution,[status(thm)],[c_7251])).

cnf(c_9371,plain,
    ( sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK2
    | sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8931,c_8,c_7001,c_7053,c_7167,c_8815])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2,X3),X3)
    | sK0(X0,X1,X2,X3) != X1
    | k2_enumset1(X0,X0,X1,X2) = X3 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_6479,plain,
    ( sK0(X0,X1,X2,X3) != X1
    | k2_enumset1(X0,X0,X1,X2) = X3
    | r2_hidden(sK0(X0,X1,X2,X3),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9383,plain,
    ( sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK1
    | k2_enumset1(sK2,sK2,sK3,sK1) = k2_enumset1(sK1,sK1,sK2,sK3)
    | r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)),k2_enumset1(sK2,sK2,sK3,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9371,c_6479])).

cnf(c_9512,plain,
    ( sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9265,c_8,c_2591,c_9280,c_9353,c_9383])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2,X3),X3)
    | sK0(X0,X1,X2,X3) != X0
    | k2_enumset1(X0,X0,X1,X2) = X3 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_9518,plain,
    ( ~ r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)),k2_enumset1(sK2,sK2,sK3,sK1))
    | k2_enumset1(sK1,sK1,sK2,sK3) = k2_enumset1(sK2,sK2,sK3,sK1) ),
    inference(resolution,[status(thm)],[c_9512,c_2])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10280,c_10263,c_9518,c_9512,c_8])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:19:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.95/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/1.00  
% 3.95/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.95/1.00  
% 3.95/1.00  ------  iProver source info
% 3.95/1.00  
% 3.95/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.95/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.95/1.00  git: non_committed_changes: false
% 3.95/1.00  git: last_make_outside_of_git: false
% 3.95/1.00  
% 3.95/1.00  ------ 
% 3.95/1.00  ------ Parsing...
% 3.95/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.95/1.00  
% 3.95/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.95/1.00  
% 3.95/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.95/1.00  
% 3.95/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.95/1.00  ------ Proving...
% 3.95/1.00  ------ Problem Properties 
% 3.95/1.00  
% 3.95/1.00  
% 3.95/1.00  clauses                                 9
% 3.95/1.00  conjectures                             1
% 3.95/1.00  EPR                                     0
% 3.95/1.00  Horn                                    7
% 3.95/1.00  unary                                   4
% 3.95/1.00  binary                                  0
% 3.95/1.00  lits                                    22
% 3.95/1.00  lits eq                                 14
% 3.95/1.00  fd_pure                                 0
% 3.95/1.00  fd_pseudo                               0
% 3.95/1.00  fd_cond                                 0
% 3.95/1.00  fd_pseudo_cond                          4
% 3.95/1.00  AC symbols                              0
% 3.95/1.00  
% 3.95/1.00  ------ Input Options Time Limit: Unbounded
% 3.95/1.00  
% 3.95/1.00  
% 3.95/1.00  
% 3.95/1.00  
% 3.95/1.00  ------ Preprocessing...
% 3.95/1.00  
% 3.95/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 3.95/1.00  Current options:
% 3.95/1.00  ------ 
% 3.95/1.00  
% 3.95/1.00  
% 3.95/1.00  
% 3.95/1.00  
% 3.95/1.00  ------ Proving...
% 3.95/1.00  
% 3.95/1.00  
% 3.95/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.95/1.00  
% 3.95/1.00  ------ Proving...
% 3.95/1.00  
% 3.95/1.00  
% 3.95/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.95/1.00  
% 3.95/1.00  ------ Proving...
% 3.95/1.00  
% 3.95/1.00  
% 3.95/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.95/1.00  
% 3.95/1.00  ------ Proving...
% 3.95/1.00  
% 3.95/1.00  
% 3.95/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.95/1.00  
% 3.95/1.00  ------ Proving...
% 3.95/1.00  
% 3.95/1.00  
% 3.95/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.95/1.00  
% 3.95/1.00  ------ Proving...
% 3.95/1.00  
% 3.95/1.00  
% 3.95/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.95/1.00  
% 3.95/1.00  ------ Proving...
% 3.95/1.00  
% 3.95/1.00  
% 3.95/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.95/1.00  
% 3.95/1.00  ------ Proving...
% 3.95/1.00  
% 3.95/1.00  
% 3.95/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.95/1.00  
% 3.95/1.00  ------ Proving...
% 3.95/1.00  
% 3.95/1.00  
% 3.95/1.00  % SZS status Theorem for theBenchmark.p
% 3.95/1.00  
% 3.95/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.95/1.00  
% 3.95/1.00  fof(f1,axiom,(
% 3.95/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.95/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/1.00  
% 3.95/1.00  fof(f5,plain,(
% 3.95/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.95/1.00    inference(ennf_transformation,[],[f1])).
% 3.95/1.00  
% 3.95/1.00  fof(f7,plain,(
% 3.95/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.95/1.00    inference(nnf_transformation,[],[f5])).
% 3.95/1.00  
% 3.95/1.00  fof(f8,plain,(
% 3.95/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.95/1.00    inference(flattening,[],[f7])).
% 3.95/1.00  
% 3.95/1.00  fof(f9,plain,(
% 3.95/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.95/1.00    inference(rectify,[],[f8])).
% 3.95/1.00  
% 3.95/1.00  fof(f10,plain,(
% 3.95/1.00    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 3.95/1.00    introduced(choice_axiom,[])).
% 3.95/1.00  
% 3.95/1.00  fof(f11,plain,(
% 3.95/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.95/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).
% 3.95/1.00  
% 3.95/1.00  fof(f17,plain,(
% 3.95/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.95/1.00    inference(cnf_transformation,[],[f11])).
% 3.95/1.00  
% 3.95/1.00  fof(f2,axiom,(
% 3.95/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.95/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/1.00  
% 3.95/1.00  fof(f22,plain,(
% 3.95/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.95/1.00    inference(cnf_transformation,[],[f2])).
% 3.95/1.00  
% 3.95/1.00  fof(f28,plain,(
% 3.95/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 3.95/1.00    inference(definition_unfolding,[],[f17,f22])).
% 3.95/1.00  
% 3.95/1.00  fof(f33,plain,(
% 3.95/1.00    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 3.95/1.00    inference(equality_resolution,[],[f28])).
% 3.95/1.00  
% 3.95/1.00  fof(f34,plain,(
% 3.95/1.00    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 3.95/1.00    inference(equality_resolution,[],[f33])).
% 3.95/1.00  
% 3.95/1.00  fof(f18,plain,(
% 3.95/1.00    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)) )),
% 3.95/1.00    inference(cnf_transformation,[],[f11])).
% 3.95/1.00  
% 3.95/1.00  fof(f27,plain,(
% 3.95/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X0,X1,X2) = X3 | sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)) )),
% 3.95/1.00    inference(definition_unfolding,[],[f18,f22])).
% 3.95/1.00  
% 3.95/1.00  fof(f3,conjecture,(
% 3.95/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 3.95/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/1.00  
% 3.95/1.00  fof(f4,negated_conjecture,(
% 3.95/1.00    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 3.95/1.00    inference(negated_conjecture,[],[f3])).
% 3.95/1.00  
% 3.95/1.00  fof(f6,plain,(
% 3.95/1.00    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X2,X0)),
% 3.95/1.00    inference(ennf_transformation,[],[f4])).
% 3.95/1.00  
% 3.95/1.00  fof(f12,plain,(
% 3.95/1.00    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X2,X0) => k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK2,sK3,sK1)),
% 3.95/1.00    introduced(choice_axiom,[])).
% 3.95/1.00  
% 3.95/1.00  fof(f13,plain,(
% 3.95/1.00    k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK2,sK3,sK1)),
% 3.95/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f6,f12])).
% 3.95/1.00  
% 3.95/1.00  fof(f23,plain,(
% 3.95/1.00    k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK2,sK3,sK1)),
% 3.95/1.00    inference(cnf_transformation,[],[f13])).
% 3.95/1.00  
% 3.95/1.00  fof(f32,plain,(
% 3.95/1.00    k2_enumset1(sK1,sK1,sK2,sK3) != k2_enumset1(sK2,sK2,sK3,sK1)),
% 3.95/1.00    inference(definition_unfolding,[],[f23,f22,f22])).
% 3.95/1.00  
% 3.95/1.00  fof(f14,plain,(
% 3.95/1.00    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.95/1.00    inference(cnf_transformation,[],[f11])).
% 3.95/1.00  
% 3.95/1.00  fof(f31,plain,(
% 3.95/1.00    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 3.95/1.00    inference(definition_unfolding,[],[f14,f22])).
% 3.95/1.00  
% 3.95/1.00  fof(f39,plain,(
% 3.95/1.00    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))) )),
% 3.95/1.00    inference(equality_resolution,[],[f31])).
% 3.95/1.00  
% 3.95/1.00  fof(f21,plain,(
% 3.95/1.00    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK0(X0,X1,X2,X3) != X2 | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) )),
% 3.95/1.00    inference(cnf_transformation,[],[f11])).
% 3.95/1.00  
% 3.95/1.00  fof(f24,plain,(
% 3.95/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X0,X1,X2) = X3 | sK0(X0,X1,X2,X3) != X2 | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) )),
% 3.95/1.00    inference(definition_unfolding,[],[f21,f22])).
% 3.95/1.00  
% 3.95/1.00  fof(f16,plain,(
% 3.95/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.95/1.00    inference(cnf_transformation,[],[f11])).
% 3.95/1.00  
% 3.95/1.00  fof(f29,plain,(
% 3.95/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 3.95/1.00    inference(definition_unfolding,[],[f16,f22])).
% 3.95/1.00  
% 3.95/1.00  fof(f35,plain,(
% 3.95/1.00    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X5,X2) != X3) )),
% 3.95/1.00    inference(equality_resolution,[],[f29])).
% 3.95/1.00  
% 3.95/1.00  fof(f36,plain,(
% 3.95/1.00    ( ! [X2,X0,X5] : (r2_hidden(X5,k2_enumset1(X0,X0,X5,X2))) )),
% 3.95/1.00    inference(equality_resolution,[],[f35])).
% 3.95/1.00  
% 3.95/1.00  fof(f15,plain,(
% 3.95/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.95/1.00    inference(cnf_transformation,[],[f11])).
% 3.95/1.00  
% 3.95/1.00  fof(f30,plain,(
% 3.95/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 3.95/1.00    inference(definition_unfolding,[],[f15,f22])).
% 3.95/1.00  
% 3.95/1.00  fof(f37,plain,(
% 3.95/1.00    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X5,X5,X1,X2) != X3) )),
% 3.95/1.00    inference(equality_resolution,[],[f30])).
% 3.95/1.00  
% 3.95/1.00  fof(f38,plain,(
% 3.95/1.00    ( ! [X2,X5,X1] : (r2_hidden(X5,k2_enumset1(X5,X5,X1,X2))) )),
% 3.95/1.00    inference(equality_resolution,[],[f37])).
% 3.95/1.00  
% 3.95/1.00  fof(f20,plain,(
% 3.95/1.00    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK0(X0,X1,X2,X3) != X1 | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) )),
% 3.95/1.00    inference(cnf_transformation,[],[f11])).
% 3.95/1.00  
% 3.95/1.00  fof(f25,plain,(
% 3.95/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X0,X1,X2) = X3 | sK0(X0,X1,X2,X3) != X1 | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) )),
% 3.95/1.00    inference(definition_unfolding,[],[f20,f22])).
% 3.95/1.00  
% 3.95/1.00  fof(f19,plain,(
% 3.95/1.00    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK0(X0,X1,X2,X3) != X0 | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) )),
% 3.95/1.00    inference(cnf_transformation,[],[f11])).
% 3.95/1.00  
% 3.95/1.00  fof(f26,plain,(
% 3.95/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X0,X1,X2) = X3 | sK0(X0,X1,X2,X3) != X0 | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) )),
% 3.95/1.00    inference(definition_unfolding,[],[f19,f22])).
% 3.95/1.00  
% 3.95/1.00  cnf(c_4,plain,
% 3.95/1.00      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
% 3.95/1.00      inference(cnf_transformation,[],[f34]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_10280,plain,
% 3.95/1.00      ( r2_hidden(sK1,k2_enumset1(sK2,sK2,sK3,sK1)) ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_74,plain,
% 3.95/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.95/1.00      theory(equality) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_6567,plain,
% 3.95/1.00      ( r2_hidden(X0,X1)
% 3.95/1.00      | ~ r2_hidden(X2,k2_enumset1(X3,X3,X4,X2))
% 3.95/1.00      | X0 != X2
% 3.95/1.00      | X1 != k2_enumset1(X3,X3,X4,X2) ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_74]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_6590,plain,
% 3.95/1.00      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X0))
% 3.95/1.00      | r2_hidden(X3,k2_enumset1(X1,X1,X2,X0))
% 3.95/1.00      | X3 != X0
% 3.95/1.00      | k2_enumset1(X1,X1,X2,X0) != k2_enumset1(X1,X1,X2,X0) ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_6567]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_6591,plain,
% 3.95/1.00      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X0))
% 3.95/1.00      | r2_hidden(X3,k2_enumset1(X1,X1,X2,X0))
% 3.95/1.00      | X3 != X0 ),
% 3.95/1.00      inference(equality_resolution_simp,[status(thm)],[c_6590]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_6682,plain,
% 3.95/1.00      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X0))
% 3.95/1.00      | r2_hidden(sK0(X3,X4,X5,k2_enumset1(X1,X1,X2,X0)),k2_enumset1(X1,X1,X2,X0))
% 3.95/1.00      | sK0(X3,X4,X5,k2_enumset1(X1,X1,X2,X0)) != X0 ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_6591]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_10263,plain,
% 3.95/1.00      ( r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)),k2_enumset1(sK2,sK2,sK3,sK1))
% 3.95/1.00      | ~ r2_hidden(sK1,k2_enumset1(sK2,sK2,sK3,sK1))
% 3.95/1.00      | sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) != sK1 ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_6682]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_3,plain,
% 3.95/1.00      ( r2_hidden(sK0(X0,X1,X2,X3),X3)
% 3.95/1.00      | sK0(X0,X1,X2,X3) = X2
% 3.95/1.00      | sK0(X0,X1,X2,X3) = X1
% 3.95/1.00      | sK0(X0,X1,X2,X3) = X0
% 3.95/1.00      | k2_enumset1(X0,X0,X1,X2) = X3 ),
% 3.95/1.00      inference(cnf_transformation,[],[f27]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_8,negated_conjecture,
% 3.95/1.00      ( k2_enumset1(sK1,sK1,sK2,sK3) != k2_enumset1(sK2,sK2,sK3,sK1) ),
% 3.95/1.00      inference(cnf_transformation,[],[f32]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_7000,plain,
% 3.95/1.00      ( r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)),k2_enumset1(sK2,sK2,sK3,sK1))
% 3.95/1.00      | sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK3
% 3.95/1.00      | sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK2
% 3.95/1.00      | sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK1 ),
% 3.95/1.00      inference(resolution,[status(thm)],[c_3,c_8]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_7,plain,
% 3.95/1.00      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
% 3.95/1.00      | X0 = X1
% 3.95/1.00      | X0 = X2
% 3.95/1.00      | X0 = X3 ),
% 3.95/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_7042,plain,
% 3.95/1.00      ( sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK3
% 3.95/1.00      | sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK2
% 3.95/1.00      | sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK1 ),
% 3.95/1.00      inference(forward_subsumption_resolution,
% 3.95/1.00                [status(thm)],
% 3.95/1.00                [c_7000,c_7]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_71,plain,( X0 = X0 ),theory(equality) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_6658,plain,
% 3.95/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 3.95/1.00      inference(resolution,[status(thm)],[c_74,c_71]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_7054,plain,
% 3.95/1.00      ( r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)),X0)
% 3.95/1.00      | ~ r2_hidden(sK3,X0)
% 3.95/1.00      | sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK2
% 3.95/1.00      | sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK1 ),
% 3.95/1.00      inference(resolution,[status(thm)],[c_7042,c_6658]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_7001,plain,
% 3.95/1.00      ( sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK3
% 3.95/1.00      | sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK2
% 3.95/1.00      | sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK1
% 3.95/1.00      | r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)),k2_enumset1(sK2,sK2,sK3,sK1)) = iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_7000]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_0,plain,
% 3.95/1.00      ( ~ r2_hidden(sK0(X0,X1,X2,X3),X3)
% 3.95/1.00      | sK0(X0,X1,X2,X3) != X2
% 3.95/1.00      | k2_enumset1(X0,X0,X1,X2) = X3 ),
% 3.95/1.00      inference(cnf_transformation,[],[f24]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_7052,plain,
% 3.95/1.00      ( ~ r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)),k2_enumset1(sK2,sK2,sK3,sK1))
% 3.95/1.00      | sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK2
% 3.95/1.00      | sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK1
% 3.95/1.00      | k2_enumset1(sK1,sK1,sK2,sK3) = k2_enumset1(sK2,sK2,sK3,sK1) ),
% 3.95/1.00      inference(resolution,[status(thm)],[c_7042,c_0]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_7053,plain,
% 3.95/1.00      ( sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK2
% 3.95/1.00      | sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK1
% 3.95/1.00      | k2_enumset1(sK1,sK1,sK2,sK3) = k2_enumset1(sK2,sK2,sK3,sK1)
% 3.95/1.00      | r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)),k2_enumset1(sK2,sK2,sK3,sK1)) != iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_7052]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_6570,plain,
% 3.95/1.00      ( r2_hidden(X0,X1)
% 3.95/1.00      | ~ r2_hidden(X2,k2_enumset1(X3,X3,X2,X4))
% 3.95/1.00      | X0 != X2
% 3.95/1.00      | X1 != k2_enumset1(X3,X3,X2,X4) ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_74]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_6601,plain,
% 3.95/1.00      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X0,X2))
% 3.95/1.00      | r2_hidden(X3,k2_enumset1(X1,X1,X0,X2))
% 3.95/1.00      | X3 != X0
% 3.95/1.00      | k2_enumset1(X1,X1,X0,X2) != k2_enumset1(X1,X1,X0,X2) ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_6570]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_6602,plain,
% 3.95/1.00      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X0,X2))
% 3.95/1.00      | r2_hidden(X3,k2_enumset1(X1,X1,X0,X2))
% 3.95/1.00      | X3 != X0 ),
% 3.95/1.00      inference(equality_resolution_simp,[status(thm)],[c_6601]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_6717,plain,
% 3.95/1.00      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X0,X2))
% 3.95/1.00      | r2_hidden(sK0(X3,X4,X5,k2_enumset1(X1,X1,X0,X2)),k2_enumset1(X1,X1,X0,X2))
% 3.95/1.00      | sK0(X3,X4,X5,k2_enumset1(X1,X1,X0,X2)) != X0 ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_6602]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_7166,plain,
% 3.95/1.00      ( r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)),k2_enumset1(sK2,sK2,sK3,sK1))
% 3.95/1.00      | ~ r2_hidden(sK3,k2_enumset1(sK2,sK2,sK3,sK1))
% 3.95/1.00      | sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) != sK3 ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_6717]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_7167,plain,
% 3.95/1.00      ( sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) != sK3
% 3.95/1.00      | r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)),k2_enumset1(sK2,sK2,sK3,sK1)) = iProver_top
% 3.95/1.00      | r2_hidden(sK3,k2_enumset1(sK2,sK2,sK3,sK1)) != iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_7166]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_5,plain,
% 3.95/1.00      ( r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) ),
% 3.95/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_8814,plain,
% 3.95/1.00      ( r2_hidden(sK3,k2_enumset1(sK2,sK2,sK3,sK1)) ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_8815,plain,
% 3.95/1.00      ( r2_hidden(sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_8814]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_9265,plain,
% 3.95/1.00      ( sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK2
% 3.95/1.00      | sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK1 ),
% 3.95/1.00      inference(global_propositional_subsumption,
% 3.95/1.00                [status(thm)],
% 3.95/1.00                [c_7054,c_8,c_7001,c_7053,c_7167,c_8815]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_72,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_2013,plain,
% 3.95/1.00      ( k2_enumset1(sK2,sK2,sK3,sK1) != X0
% 3.95/1.00      | k2_enumset1(sK1,sK1,sK2,sK3) != X0
% 3.95/1.00      | k2_enumset1(sK1,sK1,sK2,sK3) = k2_enumset1(sK2,sK2,sK3,sK1) ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_72]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_2483,plain,
% 3.95/1.00      ( k2_enumset1(sK2,sK2,sK3,sK1) != k2_enumset1(X0,X1,X2,X3)
% 3.95/1.00      | k2_enumset1(sK1,sK1,sK2,sK3) != k2_enumset1(X0,X1,X2,X3)
% 3.95/1.00      | k2_enumset1(sK1,sK1,sK2,sK3) = k2_enumset1(sK2,sK2,sK3,sK1) ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_2013]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_2590,plain,
% 3.95/1.00      ( k2_enumset1(sK2,sK2,sK3,sK1) != k2_enumset1(sK1,sK1,sK2,sK3)
% 3.95/1.00      | k2_enumset1(sK1,sK1,sK2,sK3) = k2_enumset1(sK2,sK2,sK3,sK1)
% 3.95/1.00      | k2_enumset1(sK1,sK1,sK2,sK3) != k2_enumset1(sK1,sK1,sK2,sK3) ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_2483]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_2591,plain,
% 3.95/1.00      ( k2_enumset1(sK2,sK2,sK3,sK1) != k2_enumset1(sK1,sK1,sK2,sK3)
% 3.95/1.00      | k2_enumset1(sK1,sK1,sK2,sK3) = k2_enumset1(sK2,sK2,sK3,sK1) ),
% 3.95/1.00      inference(equality_resolution_simp,[status(thm)],[c_2590]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_6573,plain,
% 3.95/1.00      ( r2_hidden(X0,X1)
% 3.95/1.00      | ~ r2_hidden(X2,k2_enumset1(X2,X2,X3,X4))
% 3.95/1.00      | X0 != X2
% 3.95/1.00      | X1 != k2_enumset1(X2,X2,X3,X4) ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_74]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_6611,plain,
% 3.95/1.00      ( ~ r2_hidden(X0,k2_enumset1(X0,X0,X1,X2))
% 3.95/1.00      | r2_hidden(X3,k2_enumset1(X0,X0,X1,X2))
% 3.95/1.00      | X3 != X0
% 3.95/1.00      | k2_enumset1(X0,X0,X1,X2) != k2_enumset1(X0,X0,X1,X2) ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_6573]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_6612,plain,
% 3.95/1.00      ( ~ r2_hidden(X0,k2_enumset1(X0,X0,X1,X2))
% 3.95/1.00      | r2_hidden(X3,k2_enumset1(X0,X0,X1,X2))
% 3.95/1.00      | X3 != X0 ),
% 3.95/1.00      inference(equality_resolution_simp,[status(thm)],[c_6611]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_6727,plain,
% 3.95/1.00      ( ~ r2_hidden(X0,k2_enumset1(X0,X0,X1,X2))
% 3.95/1.00      | r2_hidden(sK0(X3,X4,X5,k2_enumset1(X0,X0,X1,X2)),k2_enumset1(X0,X0,X1,X2))
% 3.95/1.00      | sK0(X3,X4,X5,k2_enumset1(X0,X0,X1,X2)) != X0 ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_6612]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_9279,plain,
% 3.95/1.00      ( r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)),k2_enumset1(sK2,sK2,sK3,sK1))
% 3.95/1.00      | ~ r2_hidden(sK2,k2_enumset1(sK2,sK2,sK3,sK1))
% 3.95/1.00      | sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) != sK2 ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_6727]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_9280,plain,
% 3.95/1.00      ( sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) != sK2
% 3.95/1.00      | r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)),k2_enumset1(sK2,sK2,sK3,sK1)) = iProver_top
% 3.95/1.00      | r2_hidden(sK2,k2_enumset1(sK2,sK2,sK3,sK1)) != iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_9279]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_6,plain,
% 3.95/1.00      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
% 3.95/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_9352,plain,
% 3.95/1.00      ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK3,sK1)) ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_9353,plain,
% 3.95/1.00      ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK3,sK1)) = iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_9352]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_6477,plain,
% 3.95/1.00      ( sK0(X0,X1,X2,X3) = X2
% 3.95/1.00      | sK0(X0,X1,X2,X3) = X1
% 3.95/1.00      | sK0(X0,X1,X2,X3) = X0
% 3.95/1.00      | k2_enumset1(X0,X0,X1,X2) = X3
% 3.95/1.00      | r2_hidden(sK0(X0,X1,X2,X3),X3) = iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_6473,plain,
% 3.95/1.00      ( X0 = X1
% 3.95/1.00      | X0 = X2
% 3.95/1.00      | X0 = X3
% 3.95/1.00      | r2_hidden(X0,k2_enumset1(X1,X1,X2,X3)) != iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_7192,plain,
% 3.95/1.00      ( sK0(X0,X1,X2,k2_enumset1(X3,X3,X4,X5)) = X5
% 3.95/1.00      | sK0(X0,X1,X2,k2_enumset1(X3,X3,X4,X5)) = X4
% 3.95/1.00      | sK0(X0,X1,X2,k2_enumset1(X3,X3,X4,X5)) = X3
% 3.95/1.00      | sK0(X0,X1,X2,k2_enumset1(X3,X3,X4,X5)) = X2
% 3.95/1.00      | sK0(X0,X1,X2,k2_enumset1(X3,X3,X4,X5)) = X1
% 3.95/1.00      | sK0(X0,X1,X2,k2_enumset1(X3,X3,X4,X5)) = X0
% 3.95/1.00      | k2_enumset1(X3,X3,X4,X5) = k2_enumset1(X0,X0,X1,X2) ),
% 3.95/1.00      inference(superposition,[status(thm)],[c_6477,c_6473]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_7251,plain,
% 3.95/1.00      ( sK0(X0,X1,X2,k2_enumset1(sK2,sK2,sK3,sK1)) = X2
% 3.95/1.00      | sK0(X0,X1,X2,k2_enumset1(sK2,sK2,sK3,sK1)) = X1
% 3.95/1.00      | sK0(X0,X1,X2,k2_enumset1(sK2,sK2,sK3,sK1)) = X0
% 3.95/1.00      | sK0(X0,X1,X2,k2_enumset1(sK2,sK2,sK3,sK1)) = sK3
% 3.95/1.00      | sK0(X0,X1,X2,k2_enumset1(sK2,sK2,sK3,sK1)) = sK2
% 3.95/1.00      | sK0(X0,X1,X2,k2_enumset1(sK2,sK2,sK3,sK1)) = sK1
% 3.95/1.00      | k2_enumset1(X0,X0,X1,X2) != k2_enumset1(sK1,sK1,sK2,sK3) ),
% 3.95/1.00      inference(superposition,[status(thm)],[c_7192,c_8]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_8931,plain,
% 3.95/1.00      ( sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK3
% 3.95/1.00      | sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK2
% 3.95/1.00      | sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK1 ),
% 3.95/1.00      inference(equality_resolution,[status(thm)],[c_7251]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_9371,plain,
% 3.95/1.00      ( sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK2
% 3.95/1.00      | sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK1 ),
% 3.95/1.00      inference(global_propositional_subsumption,
% 3.95/1.00                [status(thm)],
% 3.95/1.00                [c_8931,c_8,c_7001,c_7053,c_7167,c_8815]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_1,plain,
% 3.95/1.00      ( ~ r2_hidden(sK0(X0,X1,X2,X3),X3)
% 3.95/1.00      | sK0(X0,X1,X2,X3) != X1
% 3.95/1.00      | k2_enumset1(X0,X0,X1,X2) = X3 ),
% 3.95/1.00      inference(cnf_transformation,[],[f25]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_6479,plain,
% 3.95/1.00      ( sK0(X0,X1,X2,X3) != X1
% 3.95/1.00      | k2_enumset1(X0,X0,X1,X2) = X3
% 3.95/1.00      | r2_hidden(sK0(X0,X1,X2,X3),X3) != iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_9383,plain,
% 3.95/1.00      ( sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK1
% 3.95/1.00      | k2_enumset1(sK2,sK2,sK3,sK1) = k2_enumset1(sK1,sK1,sK2,sK3)
% 3.95/1.00      | r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)),k2_enumset1(sK2,sK2,sK3,sK1)) != iProver_top ),
% 3.95/1.00      inference(superposition,[status(thm)],[c_9371,c_6479]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_9512,plain,
% 3.95/1.00      ( sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)) = sK1 ),
% 3.95/1.00      inference(global_propositional_subsumption,
% 3.95/1.00                [status(thm)],
% 3.95/1.00                [c_9265,c_8,c_2591,c_9280,c_9353,c_9383]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_2,plain,
% 3.95/1.00      ( ~ r2_hidden(sK0(X0,X1,X2,X3),X3)
% 3.95/1.00      | sK0(X0,X1,X2,X3) != X0
% 3.95/1.00      | k2_enumset1(X0,X0,X1,X2) = X3 ),
% 3.95/1.00      inference(cnf_transformation,[],[f26]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_9518,plain,
% 3.95/1.00      ( ~ r2_hidden(sK0(sK1,sK2,sK3,k2_enumset1(sK2,sK2,sK3,sK1)),k2_enumset1(sK2,sK2,sK3,sK1))
% 3.95/1.00      | k2_enumset1(sK1,sK1,sK2,sK3) = k2_enumset1(sK2,sK2,sK3,sK1) ),
% 3.95/1.00      inference(resolution,[status(thm)],[c_9512,c_2]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(contradiction,plain,
% 3.95/1.00      ( $false ),
% 3.95/1.00      inference(minisat,[status(thm)],[c_10280,c_10263,c_9518,c_9512,c_8]) ).
% 3.95/1.00  
% 3.95/1.00  
% 3.95/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.95/1.00  
% 3.95/1.00  ------                               Statistics
% 3.95/1.00  
% 3.95/1.00  ------ Selected
% 3.95/1.00  
% 3.95/1.00  total_time:                             0.423
% 3.95/1.00  
%------------------------------------------------------------------------------
