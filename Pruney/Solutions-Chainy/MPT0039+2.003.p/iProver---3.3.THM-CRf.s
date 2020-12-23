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

% Result     : Theorem 7.73s
% Output     : CNFRefutation 7.73s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 331 expanded)
%              Number of clauses        :   54 ( 113 expanded)
%              Number of leaves         :    6 (  65 expanded)
%              Depth                    :   20
%              Number of atoms          :  242 (2125 expanded)
%              Number of equality atoms :  133 ( 521 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
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

fof(f7,plain,(
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
    inference(flattening,[],[f6])).

fof(f8,plain,(
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
    inference(rectify,[],[f7])).

fof(f9,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f9])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f3])).

fof(f5,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) )
   => ( sK1 != sK2
      & k4_xboole_0(sK1,sK2) = k4_xboole_0(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( sK1 != sK2
    & k4_xboole_0(sK1,sK2) = k4_xboole_0(sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f5,f11])).

fof(f19,plain,(
    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f15,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f15])).

fof(f14,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f14])).

fof(f13,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f13])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f20,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f12])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_182,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_7,negated_conjecture,
    ( k4_xboole_0(sK1,sK2) = k4_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_181,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_395,plain,
    ( r2_hidden(X0,k4_xboole_0(sK1,sK2)) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(X0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_181])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_180,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_338,plain,
    ( r2_hidden(X0,k4_xboole_0(sK1,sK2)) != iProver_top
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_180])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_179,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_345,plain,
    ( r2_hidden(X0,k4_xboole_0(sK1,sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_338,c_179])).

cnf(c_416,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(X0,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_395,c_345])).

cnf(c_526,plain,
    ( k4_xboole_0(X0,X1) = sK2
    | r2_hidden(sK0(X0,X1,sK2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,sK2),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_182,c_416])).

cnf(c_1039,plain,
    ( k4_xboole_0(sK1,X0) = sK2
    | r2_hidden(sK0(sK1,X0,sK2),sK1) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_526])).

cnf(c_1041,plain,
    ( k4_xboole_0(sK1,X0) = sK2
    | r2_hidden(sK0(sK1,X0,sK2),sK1) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1039])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_184,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_22139,plain,
    ( k4_xboole_0(sK1,X0) = sK2
    | r2_hidden(sK0(sK1,X0,sK2),X0) = iProver_top
    | r2_hidden(sK0(sK1,X0,sK2),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1041,c_184])).

cnf(c_398,plain,
    ( r2_hidden(X0,sK2) = iProver_top
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_181,c_345])).

cnf(c_728,plain,
    ( k4_xboole_0(sK1,X0) = X1
    | r2_hidden(sK0(sK1,X0,X1),X1) = iProver_top
    | r2_hidden(sK0(sK1,X0,X1),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_182,c_398])).

cnf(c_13710,plain,
    ( k4_xboole_0(sK1,X0) = sK2
    | r2_hidden(sK0(sK1,X0,sK2),sK2) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_728])).

cnf(c_13712,plain,
    ( k4_xboole_0(sK1,X0) = sK2
    | r2_hidden(sK0(sK1,X0,sK2),sK2) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_13710])).

cnf(c_36268,plain,
    ( r2_hidden(sK0(sK1,X0,sK2),X0) = iProver_top
    | k4_xboole_0(sK1,X0) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_22139,c_13712])).

cnf(c_36269,plain,
    ( k4_xboole_0(sK1,X0) = sK2
    | r2_hidden(sK0(sK1,X0,sK2),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_36268])).

cnf(c_36277,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(X0,X1)) = sK2
    | r2_hidden(sK0(sK1,k4_xboole_0(X0,X1),sK2),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_36269,c_180])).

cnf(c_36301,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)) = sK2
    | r2_hidden(sK0(sK1,k4_xboole_0(sK1,sK1),sK2),sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_36277])).

cnf(c_36276,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(X0,X1)) = sK2
    | r2_hidden(sK0(sK1,k4_xboole_0(X0,X1),sK2),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_36269,c_179])).

cnf(c_36298,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)) = sK2
    | r2_hidden(sK0(sK1,k4_xboole_0(sK1,sK1),sK2),sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_36276])).

cnf(c_71,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_236,plain,
    ( sK2 != X0
    | sK1 != X0
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_71])).

cnf(c_275,plain,
    ( sK2 != k4_xboole_0(X0,X1)
    | sK1 != k4_xboole_0(X0,X1)
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_236])).

cnf(c_21498,plain,
    ( sK2 != k4_xboole_0(X0,k4_xboole_0(X1,X2))
    | sK1 != k4_xboole_0(X0,k4_xboole_0(X1,X2))
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_275])).

cnf(c_21499,plain,
    ( sK2 != k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))
    | sK1 != k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_21498])).

cnf(c_446,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | ~ r2_hidden(sK0(X0,X1,X2),k4_xboole_0(X3,X2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_8615,plain,
    ( ~ r2_hidden(sK0(X0,k4_xboole_0(X1,X2),X2),X2)
    | ~ r2_hidden(sK0(X0,k4_xboole_0(X1,X2),X2),k4_xboole_0(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_446])).

cnf(c_8617,plain,
    ( ~ r2_hidden(sK0(sK1,k4_xboole_0(sK1,sK1),sK1),k4_xboole_0(sK1,sK1))
    | ~ r2_hidden(sK0(sK1,k4_xboole_0(sK1,sK1),sK1),sK1) ),
    inference(instantiation,[status(thm)],[c_8615])).

cnf(c_299,plain,
    ( k4_xboole_0(X0,X1) != X2
    | sK1 != X2
    | sK1 = k4_xboole_0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_71])).

cnf(c_3454,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X2)) != X3
    | sK1 != X3
    | sK1 = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_299])).

cnf(c_3455,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)) != sK1
    | sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_3454])).

cnf(c_241,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_71])).

cnf(c_242,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_241])).

cnf(c_247,plain,
    ( k4_xboole_0(X0,X1) != sK2
    | sK2 = k4_xboole_0(X0,X1)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_242])).

cnf(c_2401,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X2)) != sK2
    | sK2 = k4_xboole_0(X0,k4_xboole_0(X1,X2))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_247])).

cnf(c_2406,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)) != sK2
    | sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2401])).

cnf(c_877,plain,
    ( r2_hidden(sK0(X0,k4_xboole_0(X1,X2),X3),X0)
    | r2_hidden(sK0(X0,k4_xboole_0(X1,X2),X3),X3)
    | k4_xboole_0(X0,k4_xboole_0(X1,X2)) = X3 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_879,plain,
    ( r2_hidden(sK0(sK1,k4_xboole_0(sK1,sK1),sK1),sK1)
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_877])).

cnf(c_492,plain,
    ( ~ r2_hidden(sK0(X0,k4_xboole_0(X1,X2),X3),X0)
    | ~ r2_hidden(sK0(X0,k4_xboole_0(X1,X2),X3),X3)
    | r2_hidden(sK0(X0,k4_xboole_0(X1,X2),X3),k4_xboole_0(X1,X2))
    | k4_xboole_0(X0,k4_xboole_0(X1,X2)) = X3 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_495,plain,
    ( r2_hidden(sK0(sK1,k4_xboole_0(sK1,sK1),sK1),k4_xboole_0(sK1,sK1))
    | ~ r2_hidden(sK0(sK1,k4_xboole_0(sK1,sK1),sK1),sK1)
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_492])).

cnf(c_70,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_243,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_70])).

cnf(c_77,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_70])).

cnf(c_6,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_36301,c_36298,c_21499,c_8617,c_3455,c_2406,c_879,c_495,c_243,c_77,c_6])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:00:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.73/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.73/1.51  
% 7.73/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.73/1.51  
% 7.73/1.51  ------  iProver source info
% 7.73/1.51  
% 7.73/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.73/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.73/1.51  git: non_committed_changes: false
% 7.73/1.51  git: last_make_outside_of_git: false
% 7.73/1.51  
% 7.73/1.51  ------ 
% 7.73/1.51  
% 7.73/1.51  ------ Input Options
% 7.73/1.51  
% 7.73/1.51  --out_options                           all
% 7.73/1.51  --tptp_safe_out                         true
% 7.73/1.51  --problem_path                          ""
% 7.73/1.51  --include_path                          ""
% 7.73/1.51  --clausifier                            res/vclausify_rel
% 7.73/1.51  --clausifier_options                    --mode clausify
% 7.73/1.51  --stdin                                 false
% 7.73/1.51  --stats_out                             all
% 7.73/1.51  
% 7.73/1.51  ------ General Options
% 7.73/1.51  
% 7.73/1.51  --fof                                   false
% 7.73/1.51  --time_out_real                         305.
% 7.73/1.51  --time_out_virtual                      -1.
% 7.73/1.51  --symbol_type_check                     false
% 7.73/1.51  --clausify_out                          false
% 7.73/1.51  --sig_cnt_out                           false
% 7.73/1.51  --trig_cnt_out                          false
% 7.73/1.51  --trig_cnt_out_tolerance                1.
% 7.73/1.51  --trig_cnt_out_sk_spl                   false
% 7.73/1.51  --abstr_cl_out                          false
% 7.73/1.51  
% 7.73/1.51  ------ Global Options
% 7.73/1.51  
% 7.73/1.51  --schedule                              default
% 7.73/1.51  --add_important_lit                     false
% 7.73/1.51  --prop_solver_per_cl                    1000
% 7.73/1.51  --min_unsat_core                        false
% 7.73/1.51  --soft_assumptions                      false
% 7.73/1.51  --soft_lemma_size                       3
% 7.73/1.51  --prop_impl_unit_size                   0
% 7.73/1.51  --prop_impl_unit                        []
% 7.73/1.51  --share_sel_clauses                     true
% 7.73/1.51  --reset_solvers                         false
% 7.73/1.51  --bc_imp_inh                            [conj_cone]
% 7.73/1.51  --conj_cone_tolerance                   3.
% 7.73/1.51  --extra_neg_conj                        none
% 7.73/1.51  --large_theory_mode                     true
% 7.73/1.51  --prolific_symb_bound                   200
% 7.73/1.51  --lt_threshold                          2000
% 7.73/1.51  --clause_weak_htbl                      true
% 7.73/1.51  --gc_record_bc_elim                     false
% 7.73/1.51  
% 7.73/1.51  ------ Preprocessing Options
% 7.73/1.51  
% 7.73/1.51  --preprocessing_flag                    true
% 7.73/1.51  --time_out_prep_mult                    0.1
% 7.73/1.51  --splitting_mode                        input
% 7.73/1.51  --splitting_grd                         true
% 7.73/1.51  --splitting_cvd                         false
% 7.73/1.51  --splitting_cvd_svl                     false
% 7.73/1.51  --splitting_nvd                         32
% 7.73/1.51  --sub_typing                            true
% 7.73/1.51  --prep_gs_sim                           true
% 7.73/1.51  --prep_unflatten                        true
% 7.73/1.51  --prep_res_sim                          true
% 7.73/1.51  --prep_upred                            true
% 7.73/1.51  --prep_sem_filter                       exhaustive
% 7.73/1.51  --prep_sem_filter_out                   false
% 7.73/1.51  --pred_elim                             true
% 7.73/1.51  --res_sim_input                         true
% 7.73/1.51  --eq_ax_congr_red                       true
% 7.73/1.51  --pure_diseq_elim                       true
% 7.73/1.51  --brand_transform                       false
% 7.73/1.51  --non_eq_to_eq                          false
% 7.73/1.51  --prep_def_merge                        true
% 7.73/1.51  --prep_def_merge_prop_impl              false
% 7.73/1.51  --prep_def_merge_mbd                    true
% 7.73/1.51  --prep_def_merge_tr_red                 false
% 7.73/1.51  --prep_def_merge_tr_cl                  false
% 7.73/1.51  --smt_preprocessing                     true
% 7.73/1.51  --smt_ac_axioms                         fast
% 7.73/1.51  --preprocessed_out                      false
% 7.73/1.51  --preprocessed_stats                    false
% 7.73/1.51  
% 7.73/1.51  ------ Abstraction refinement Options
% 7.73/1.51  
% 7.73/1.51  --abstr_ref                             []
% 7.73/1.51  --abstr_ref_prep                        false
% 7.73/1.51  --abstr_ref_until_sat                   false
% 7.73/1.51  --abstr_ref_sig_restrict                funpre
% 7.73/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.73/1.51  --abstr_ref_under                       []
% 7.73/1.51  
% 7.73/1.51  ------ SAT Options
% 7.73/1.51  
% 7.73/1.51  --sat_mode                              false
% 7.73/1.51  --sat_fm_restart_options                ""
% 7.73/1.51  --sat_gr_def                            false
% 7.73/1.51  --sat_epr_types                         true
% 7.73/1.51  --sat_non_cyclic_types                  false
% 7.73/1.51  --sat_finite_models                     false
% 7.73/1.51  --sat_fm_lemmas                         false
% 7.73/1.51  --sat_fm_prep                           false
% 7.73/1.51  --sat_fm_uc_incr                        true
% 7.73/1.51  --sat_out_model                         small
% 7.73/1.51  --sat_out_clauses                       false
% 7.73/1.51  
% 7.73/1.51  ------ QBF Options
% 7.73/1.51  
% 7.73/1.51  --qbf_mode                              false
% 7.73/1.51  --qbf_elim_univ                         false
% 7.73/1.51  --qbf_dom_inst                          none
% 7.73/1.51  --qbf_dom_pre_inst                      false
% 7.73/1.51  --qbf_sk_in                             false
% 7.73/1.51  --qbf_pred_elim                         true
% 7.73/1.51  --qbf_split                             512
% 7.73/1.51  
% 7.73/1.51  ------ BMC1 Options
% 7.73/1.51  
% 7.73/1.51  --bmc1_incremental                      false
% 7.73/1.51  --bmc1_axioms                           reachable_all
% 7.73/1.51  --bmc1_min_bound                        0
% 7.73/1.51  --bmc1_max_bound                        -1
% 7.73/1.51  --bmc1_max_bound_default                -1
% 7.73/1.51  --bmc1_symbol_reachability              true
% 7.73/1.51  --bmc1_property_lemmas                  false
% 7.73/1.51  --bmc1_k_induction                      false
% 7.73/1.51  --bmc1_non_equiv_states                 false
% 7.73/1.51  --bmc1_deadlock                         false
% 7.73/1.51  --bmc1_ucm                              false
% 7.73/1.51  --bmc1_add_unsat_core                   none
% 7.73/1.51  --bmc1_unsat_core_children              false
% 7.73/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.73/1.51  --bmc1_out_stat                         full
% 7.73/1.51  --bmc1_ground_init                      false
% 7.73/1.51  --bmc1_pre_inst_next_state              false
% 7.73/1.51  --bmc1_pre_inst_state                   false
% 7.73/1.51  --bmc1_pre_inst_reach_state             false
% 7.73/1.51  --bmc1_out_unsat_core                   false
% 7.73/1.51  --bmc1_aig_witness_out                  false
% 7.73/1.51  --bmc1_verbose                          false
% 7.73/1.51  --bmc1_dump_clauses_tptp                false
% 7.73/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.73/1.51  --bmc1_dump_file                        -
% 7.73/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.73/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.73/1.51  --bmc1_ucm_extend_mode                  1
% 7.73/1.51  --bmc1_ucm_init_mode                    2
% 7.73/1.51  --bmc1_ucm_cone_mode                    none
% 7.73/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.73/1.51  --bmc1_ucm_relax_model                  4
% 7.73/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.73/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.73/1.51  --bmc1_ucm_layered_model                none
% 7.73/1.51  --bmc1_ucm_max_lemma_size               10
% 7.73/1.51  
% 7.73/1.51  ------ AIG Options
% 7.73/1.51  
% 7.73/1.51  --aig_mode                              false
% 7.73/1.51  
% 7.73/1.51  ------ Instantiation Options
% 7.73/1.51  
% 7.73/1.51  --instantiation_flag                    true
% 7.73/1.51  --inst_sos_flag                         false
% 7.73/1.51  --inst_sos_phase                        true
% 7.73/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.73/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.73/1.51  --inst_lit_sel_side                     num_symb
% 7.73/1.51  --inst_solver_per_active                1400
% 7.73/1.51  --inst_solver_calls_frac                1.
% 7.73/1.51  --inst_passive_queue_type               priority_queues
% 7.73/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.73/1.51  --inst_passive_queues_freq              [25;2]
% 7.73/1.51  --inst_dismatching                      true
% 7.73/1.51  --inst_eager_unprocessed_to_passive     true
% 7.73/1.51  --inst_prop_sim_given                   true
% 7.73/1.51  --inst_prop_sim_new                     false
% 7.73/1.51  --inst_subs_new                         false
% 7.73/1.51  --inst_eq_res_simp                      false
% 7.73/1.51  --inst_subs_given                       false
% 7.73/1.51  --inst_orphan_elimination               true
% 7.73/1.51  --inst_learning_loop_flag               true
% 7.73/1.51  --inst_learning_start                   3000
% 7.73/1.51  --inst_learning_factor                  2
% 7.73/1.51  --inst_start_prop_sim_after_learn       3
% 7.73/1.51  --inst_sel_renew                        solver
% 7.73/1.51  --inst_lit_activity_flag                true
% 7.73/1.51  --inst_restr_to_given                   false
% 7.73/1.51  --inst_activity_threshold               500
% 7.73/1.51  --inst_out_proof                        true
% 7.73/1.51  
% 7.73/1.51  ------ Resolution Options
% 7.73/1.51  
% 7.73/1.51  --resolution_flag                       true
% 7.73/1.51  --res_lit_sel                           adaptive
% 7.73/1.51  --res_lit_sel_side                      none
% 7.73/1.51  --res_ordering                          kbo
% 7.73/1.51  --res_to_prop_solver                    active
% 7.73/1.51  --res_prop_simpl_new                    false
% 7.73/1.51  --res_prop_simpl_given                  true
% 7.73/1.51  --res_passive_queue_type                priority_queues
% 7.73/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.73/1.51  --res_passive_queues_freq               [15;5]
% 7.73/1.51  --res_forward_subs                      full
% 7.73/1.51  --res_backward_subs                     full
% 7.73/1.51  --res_forward_subs_resolution           true
% 7.73/1.51  --res_backward_subs_resolution          true
% 7.73/1.51  --res_orphan_elimination                true
% 7.73/1.51  --res_time_limit                        2.
% 7.73/1.51  --res_out_proof                         true
% 7.73/1.51  
% 7.73/1.51  ------ Superposition Options
% 7.73/1.51  
% 7.73/1.51  --superposition_flag                    true
% 7.73/1.51  --sup_passive_queue_type                priority_queues
% 7.73/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.73/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.73/1.51  --demod_completeness_check              fast
% 7.73/1.51  --demod_use_ground                      true
% 7.73/1.51  --sup_to_prop_solver                    passive
% 7.73/1.51  --sup_prop_simpl_new                    true
% 7.73/1.51  --sup_prop_simpl_given                  true
% 7.73/1.51  --sup_fun_splitting                     false
% 7.73/1.51  --sup_smt_interval                      50000
% 7.73/1.51  
% 7.73/1.51  ------ Superposition Simplification Setup
% 7.73/1.51  
% 7.73/1.51  --sup_indices_passive                   []
% 7.73/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.73/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.73/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.73/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.73/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.73/1.51  --sup_full_bw                           [BwDemod]
% 7.73/1.51  --sup_immed_triv                        [TrivRules]
% 7.73/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.73/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.73/1.51  --sup_immed_bw_main                     []
% 7.73/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.73/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.73/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.73/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.73/1.51  
% 7.73/1.51  ------ Combination Options
% 7.73/1.51  
% 7.73/1.51  --comb_res_mult                         3
% 7.73/1.51  --comb_sup_mult                         2
% 7.73/1.51  --comb_inst_mult                        10
% 7.73/1.51  
% 7.73/1.51  ------ Debug Options
% 7.73/1.51  
% 7.73/1.51  --dbg_backtrace                         false
% 7.73/1.51  --dbg_dump_prop_clauses                 false
% 7.73/1.51  --dbg_dump_prop_clauses_file            -
% 7.73/1.51  --dbg_out_stat                          false
% 7.73/1.51  ------ Parsing...
% 7.73/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.73/1.51  
% 7.73/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.73/1.51  
% 7.73/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.73/1.51  
% 7.73/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.51  ------ Proving...
% 7.73/1.51  ------ Problem Properties 
% 7.73/1.51  
% 7.73/1.51  
% 7.73/1.51  clauses                                 8
% 7.73/1.51  conjectures                             2
% 7.73/1.51  EPR                                     1
% 7.73/1.51  Horn                                    4
% 7.73/1.51  unary                                   2
% 7.73/1.51  binary                                  2
% 7.73/1.51  lits                                    19
% 7.73/1.51  lits eq                                 5
% 7.73/1.51  fd_pure                                 0
% 7.73/1.51  fd_pseudo                               0
% 7.73/1.51  fd_cond                                 0
% 7.73/1.51  fd_pseudo_cond                          3
% 7.73/1.51  AC symbols                              0
% 7.73/1.51  
% 7.73/1.51  ------ Schedule dynamic 5 is on 
% 7.73/1.51  
% 7.73/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.73/1.51  
% 7.73/1.51  
% 7.73/1.51  ------ 
% 7.73/1.51  Current options:
% 7.73/1.51  ------ 
% 7.73/1.51  
% 7.73/1.51  ------ Input Options
% 7.73/1.51  
% 7.73/1.51  --out_options                           all
% 7.73/1.51  --tptp_safe_out                         true
% 7.73/1.51  --problem_path                          ""
% 7.73/1.51  --include_path                          ""
% 7.73/1.51  --clausifier                            res/vclausify_rel
% 7.73/1.51  --clausifier_options                    --mode clausify
% 7.73/1.51  --stdin                                 false
% 7.73/1.51  --stats_out                             all
% 7.73/1.51  
% 7.73/1.51  ------ General Options
% 7.73/1.51  
% 7.73/1.51  --fof                                   false
% 7.73/1.51  --time_out_real                         305.
% 7.73/1.51  --time_out_virtual                      -1.
% 7.73/1.51  --symbol_type_check                     false
% 7.73/1.51  --clausify_out                          false
% 7.73/1.51  --sig_cnt_out                           false
% 7.73/1.51  --trig_cnt_out                          false
% 7.73/1.51  --trig_cnt_out_tolerance                1.
% 7.73/1.51  --trig_cnt_out_sk_spl                   false
% 7.73/1.51  --abstr_cl_out                          false
% 7.73/1.51  
% 7.73/1.51  ------ Global Options
% 7.73/1.51  
% 7.73/1.51  --schedule                              default
% 7.73/1.51  --add_important_lit                     false
% 7.73/1.51  --prop_solver_per_cl                    1000
% 7.73/1.51  --min_unsat_core                        false
% 7.73/1.51  --soft_assumptions                      false
% 7.73/1.51  --soft_lemma_size                       3
% 7.73/1.51  --prop_impl_unit_size                   0
% 7.73/1.51  --prop_impl_unit                        []
% 7.73/1.51  --share_sel_clauses                     true
% 7.73/1.51  --reset_solvers                         false
% 7.73/1.51  --bc_imp_inh                            [conj_cone]
% 7.73/1.51  --conj_cone_tolerance                   3.
% 7.73/1.51  --extra_neg_conj                        none
% 7.73/1.51  --large_theory_mode                     true
% 7.73/1.51  --prolific_symb_bound                   200
% 7.73/1.51  --lt_threshold                          2000
% 7.73/1.51  --clause_weak_htbl                      true
% 7.73/1.51  --gc_record_bc_elim                     false
% 7.73/1.51  
% 7.73/1.51  ------ Preprocessing Options
% 7.73/1.51  
% 7.73/1.51  --preprocessing_flag                    true
% 7.73/1.51  --time_out_prep_mult                    0.1
% 7.73/1.51  --splitting_mode                        input
% 7.73/1.51  --splitting_grd                         true
% 7.73/1.51  --splitting_cvd                         false
% 7.73/1.51  --splitting_cvd_svl                     false
% 7.73/1.51  --splitting_nvd                         32
% 7.73/1.51  --sub_typing                            true
% 7.73/1.51  --prep_gs_sim                           true
% 7.73/1.51  --prep_unflatten                        true
% 7.73/1.51  --prep_res_sim                          true
% 7.73/1.51  --prep_upred                            true
% 7.73/1.51  --prep_sem_filter                       exhaustive
% 7.73/1.51  --prep_sem_filter_out                   false
% 7.73/1.51  --pred_elim                             true
% 7.73/1.51  --res_sim_input                         true
% 7.73/1.51  --eq_ax_congr_red                       true
% 7.73/1.51  --pure_diseq_elim                       true
% 7.73/1.51  --brand_transform                       false
% 7.73/1.51  --non_eq_to_eq                          false
% 7.73/1.51  --prep_def_merge                        true
% 7.73/1.51  --prep_def_merge_prop_impl              false
% 7.73/1.51  --prep_def_merge_mbd                    true
% 7.73/1.51  --prep_def_merge_tr_red                 false
% 7.73/1.51  --prep_def_merge_tr_cl                  false
% 7.73/1.51  --smt_preprocessing                     true
% 7.73/1.51  --smt_ac_axioms                         fast
% 7.73/1.51  --preprocessed_out                      false
% 7.73/1.51  --preprocessed_stats                    false
% 7.73/1.51  
% 7.73/1.51  ------ Abstraction refinement Options
% 7.73/1.51  
% 7.73/1.51  --abstr_ref                             []
% 7.73/1.51  --abstr_ref_prep                        false
% 7.73/1.51  --abstr_ref_until_sat                   false
% 7.73/1.51  --abstr_ref_sig_restrict                funpre
% 7.73/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.73/1.51  --abstr_ref_under                       []
% 7.73/1.51  
% 7.73/1.51  ------ SAT Options
% 7.73/1.51  
% 7.73/1.51  --sat_mode                              false
% 7.73/1.51  --sat_fm_restart_options                ""
% 7.73/1.51  --sat_gr_def                            false
% 7.73/1.51  --sat_epr_types                         true
% 7.73/1.51  --sat_non_cyclic_types                  false
% 7.73/1.51  --sat_finite_models                     false
% 7.73/1.51  --sat_fm_lemmas                         false
% 7.73/1.51  --sat_fm_prep                           false
% 7.73/1.51  --sat_fm_uc_incr                        true
% 7.73/1.51  --sat_out_model                         small
% 7.73/1.51  --sat_out_clauses                       false
% 7.73/1.51  
% 7.73/1.51  ------ QBF Options
% 7.73/1.51  
% 7.73/1.51  --qbf_mode                              false
% 7.73/1.51  --qbf_elim_univ                         false
% 7.73/1.51  --qbf_dom_inst                          none
% 7.73/1.51  --qbf_dom_pre_inst                      false
% 7.73/1.51  --qbf_sk_in                             false
% 7.73/1.51  --qbf_pred_elim                         true
% 7.73/1.51  --qbf_split                             512
% 7.73/1.51  
% 7.73/1.51  ------ BMC1 Options
% 7.73/1.51  
% 7.73/1.51  --bmc1_incremental                      false
% 7.73/1.51  --bmc1_axioms                           reachable_all
% 7.73/1.51  --bmc1_min_bound                        0
% 7.73/1.51  --bmc1_max_bound                        -1
% 7.73/1.51  --bmc1_max_bound_default                -1
% 7.73/1.51  --bmc1_symbol_reachability              true
% 7.73/1.51  --bmc1_property_lemmas                  false
% 7.73/1.51  --bmc1_k_induction                      false
% 7.73/1.51  --bmc1_non_equiv_states                 false
% 7.73/1.51  --bmc1_deadlock                         false
% 7.73/1.51  --bmc1_ucm                              false
% 7.73/1.51  --bmc1_add_unsat_core                   none
% 7.73/1.51  --bmc1_unsat_core_children              false
% 7.73/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.73/1.51  --bmc1_out_stat                         full
% 7.73/1.51  --bmc1_ground_init                      false
% 7.73/1.51  --bmc1_pre_inst_next_state              false
% 7.73/1.51  --bmc1_pre_inst_state                   false
% 7.73/1.51  --bmc1_pre_inst_reach_state             false
% 7.73/1.51  --bmc1_out_unsat_core                   false
% 7.73/1.51  --bmc1_aig_witness_out                  false
% 7.73/1.51  --bmc1_verbose                          false
% 7.73/1.51  --bmc1_dump_clauses_tptp                false
% 7.73/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.73/1.51  --bmc1_dump_file                        -
% 7.73/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.73/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.73/1.51  --bmc1_ucm_extend_mode                  1
% 7.73/1.51  --bmc1_ucm_init_mode                    2
% 7.73/1.51  --bmc1_ucm_cone_mode                    none
% 7.73/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.73/1.51  --bmc1_ucm_relax_model                  4
% 7.73/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.73/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.73/1.51  --bmc1_ucm_layered_model                none
% 7.73/1.51  --bmc1_ucm_max_lemma_size               10
% 7.73/1.51  
% 7.73/1.51  ------ AIG Options
% 7.73/1.51  
% 7.73/1.51  --aig_mode                              false
% 7.73/1.51  
% 7.73/1.51  ------ Instantiation Options
% 7.73/1.51  
% 7.73/1.51  --instantiation_flag                    true
% 7.73/1.51  --inst_sos_flag                         false
% 7.73/1.51  --inst_sos_phase                        true
% 7.73/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.73/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.73/1.51  --inst_lit_sel_side                     none
% 7.73/1.51  --inst_solver_per_active                1400
% 7.73/1.51  --inst_solver_calls_frac                1.
% 7.73/1.51  --inst_passive_queue_type               priority_queues
% 7.73/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.73/1.51  --inst_passive_queues_freq              [25;2]
% 7.73/1.51  --inst_dismatching                      true
% 7.73/1.51  --inst_eager_unprocessed_to_passive     true
% 7.73/1.51  --inst_prop_sim_given                   true
% 7.73/1.51  --inst_prop_sim_new                     false
% 7.73/1.51  --inst_subs_new                         false
% 7.73/1.51  --inst_eq_res_simp                      false
% 7.73/1.51  --inst_subs_given                       false
% 7.73/1.51  --inst_orphan_elimination               true
% 7.73/1.51  --inst_learning_loop_flag               true
% 7.73/1.51  --inst_learning_start                   3000
% 7.73/1.51  --inst_learning_factor                  2
% 7.73/1.51  --inst_start_prop_sim_after_learn       3
% 7.73/1.51  --inst_sel_renew                        solver
% 7.73/1.51  --inst_lit_activity_flag                true
% 7.73/1.51  --inst_restr_to_given                   false
% 7.73/1.51  --inst_activity_threshold               500
% 7.73/1.51  --inst_out_proof                        true
% 7.73/1.51  
% 7.73/1.51  ------ Resolution Options
% 7.73/1.51  
% 7.73/1.51  --resolution_flag                       false
% 7.73/1.51  --res_lit_sel                           adaptive
% 7.73/1.51  --res_lit_sel_side                      none
% 7.73/1.51  --res_ordering                          kbo
% 7.73/1.51  --res_to_prop_solver                    active
% 7.73/1.51  --res_prop_simpl_new                    false
% 7.73/1.51  --res_prop_simpl_given                  true
% 7.73/1.51  --res_passive_queue_type                priority_queues
% 7.73/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.73/1.51  --res_passive_queues_freq               [15;5]
% 7.73/1.51  --res_forward_subs                      full
% 7.73/1.51  --res_backward_subs                     full
% 7.73/1.51  --res_forward_subs_resolution           true
% 7.73/1.51  --res_backward_subs_resolution          true
% 7.73/1.51  --res_orphan_elimination                true
% 7.73/1.51  --res_time_limit                        2.
% 7.73/1.51  --res_out_proof                         true
% 7.73/1.51  
% 7.73/1.51  ------ Superposition Options
% 7.73/1.51  
% 7.73/1.51  --superposition_flag                    true
% 7.73/1.51  --sup_passive_queue_type                priority_queues
% 7.73/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.73/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.73/1.51  --demod_completeness_check              fast
% 7.73/1.51  --demod_use_ground                      true
% 7.73/1.51  --sup_to_prop_solver                    passive
% 7.73/1.51  --sup_prop_simpl_new                    true
% 7.73/1.51  --sup_prop_simpl_given                  true
% 7.73/1.51  --sup_fun_splitting                     false
% 7.73/1.51  --sup_smt_interval                      50000
% 7.73/1.51  
% 7.73/1.51  ------ Superposition Simplification Setup
% 7.73/1.51  
% 7.73/1.51  --sup_indices_passive                   []
% 7.73/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.73/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.73/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.73/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.73/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.73/1.51  --sup_full_bw                           [BwDemod]
% 7.73/1.51  --sup_immed_triv                        [TrivRules]
% 7.73/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.73/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.73/1.51  --sup_immed_bw_main                     []
% 7.73/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.73/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.73/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.73/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.73/1.51  
% 7.73/1.51  ------ Combination Options
% 7.73/1.51  
% 7.73/1.51  --comb_res_mult                         3
% 7.73/1.51  --comb_sup_mult                         2
% 7.73/1.51  --comb_inst_mult                        10
% 7.73/1.51  
% 7.73/1.51  ------ Debug Options
% 7.73/1.51  
% 7.73/1.51  --dbg_backtrace                         false
% 7.73/1.51  --dbg_dump_prop_clauses                 false
% 7.73/1.51  --dbg_dump_prop_clauses_file            -
% 7.73/1.51  --dbg_out_stat                          false
% 7.73/1.51  
% 7.73/1.51  
% 7.73/1.51  
% 7.73/1.51  
% 7.73/1.51  ------ Proving...
% 7.73/1.51  
% 7.73/1.51  
% 7.73/1.51  % SZS status Theorem for theBenchmark.p
% 7.73/1.51  
% 7.73/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.73/1.51  
% 7.73/1.51  fof(f2,axiom,(
% 7.73/1.51    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.73/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.51  
% 7.73/1.51  fof(f6,plain,(
% 7.73/1.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.73/1.51    inference(nnf_transformation,[],[f2])).
% 7.73/1.51  
% 7.73/1.51  fof(f7,plain,(
% 7.73/1.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.73/1.51    inference(flattening,[],[f6])).
% 7.73/1.51  
% 7.73/1.51  fof(f8,plain,(
% 7.73/1.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.73/1.51    inference(rectify,[],[f7])).
% 7.73/1.51  
% 7.73/1.51  fof(f9,plain,(
% 7.73/1.51    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.73/1.51    introduced(choice_axiom,[])).
% 7.73/1.51  
% 7.73/1.51  fof(f10,plain,(
% 7.73/1.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.73/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f9])).
% 7.73/1.51  
% 7.73/1.51  fof(f16,plain,(
% 7.73/1.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.73/1.51    inference(cnf_transformation,[],[f10])).
% 7.73/1.51  
% 7.73/1.51  fof(f3,conjecture,(
% 7.73/1.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 7.73/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.73/1.51  
% 7.73/1.51  fof(f4,negated_conjecture,(
% 7.73/1.51    ~! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 7.73/1.51    inference(negated_conjecture,[],[f3])).
% 7.73/1.51  
% 7.73/1.51  fof(f5,plain,(
% 7.73/1.51    ? [X0,X1] : (X0 != X1 & k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0))),
% 7.73/1.51    inference(ennf_transformation,[],[f4])).
% 7.73/1.51  
% 7.73/1.51  fof(f11,plain,(
% 7.73/1.51    ? [X0,X1] : (X0 != X1 & k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)) => (sK1 != sK2 & k4_xboole_0(sK1,sK2) = k4_xboole_0(sK2,sK1))),
% 7.73/1.51    introduced(choice_axiom,[])).
% 7.73/1.51  
% 7.73/1.51  fof(f12,plain,(
% 7.73/1.51    sK1 != sK2 & k4_xboole_0(sK1,sK2) = k4_xboole_0(sK2,sK1)),
% 7.73/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f5,f11])).
% 7.73/1.51  
% 7.73/1.51  fof(f19,plain,(
% 7.73/1.51    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK2,sK1)),
% 7.73/1.51    inference(cnf_transformation,[],[f12])).
% 7.73/1.51  
% 7.73/1.51  fof(f15,plain,(
% 7.73/1.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 7.73/1.51    inference(cnf_transformation,[],[f10])).
% 7.73/1.51  
% 7.73/1.51  fof(f21,plain,(
% 7.73/1.51    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 7.73/1.51    inference(equality_resolution,[],[f15])).
% 7.73/1.51  
% 7.73/1.51  fof(f14,plain,(
% 7.73/1.51    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.73/1.51    inference(cnf_transformation,[],[f10])).
% 7.73/1.51  
% 7.73/1.51  fof(f22,plain,(
% 7.73/1.51    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 7.73/1.51    inference(equality_resolution,[],[f14])).
% 7.73/1.51  
% 7.73/1.51  fof(f13,plain,(
% 7.73/1.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.73/1.51    inference(cnf_transformation,[],[f10])).
% 7.73/1.51  
% 7.73/1.51  fof(f23,plain,(
% 7.73/1.51    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 7.73/1.51    inference(equality_resolution,[],[f13])).
% 7.73/1.51  
% 7.73/1.51  fof(f18,plain,(
% 7.73/1.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.73/1.51    inference(cnf_transformation,[],[f10])).
% 7.73/1.51  
% 7.73/1.51  fof(f20,plain,(
% 7.73/1.51    sK1 != sK2),
% 7.73/1.51    inference(cnf_transformation,[],[f12])).
% 7.73/1.51  
% 7.73/1.51  cnf(c_2,plain,
% 7.73/1.51      ( r2_hidden(sK0(X0,X1,X2),X0)
% 7.73/1.51      | r2_hidden(sK0(X0,X1,X2),X2)
% 7.73/1.51      | k4_xboole_0(X0,X1) = X2 ),
% 7.73/1.51      inference(cnf_transformation,[],[f16]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_182,plain,
% 7.73/1.51      ( k4_xboole_0(X0,X1) = X2
% 7.73/1.51      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 7.73/1.51      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 7.73/1.51      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_7,negated_conjecture,
% 7.73/1.51      ( k4_xboole_0(sK1,sK2) = k4_xboole_0(sK2,sK1) ),
% 7.73/1.51      inference(cnf_transformation,[],[f19]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_3,plain,
% 7.73/1.51      ( ~ r2_hidden(X0,X1)
% 7.73/1.51      | r2_hidden(X0,X2)
% 7.73/1.51      | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 7.73/1.51      inference(cnf_transformation,[],[f21]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_181,plain,
% 7.73/1.51      ( r2_hidden(X0,X1) != iProver_top
% 7.73/1.51      | r2_hidden(X0,X2) = iProver_top
% 7.73/1.51      | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
% 7.73/1.51      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_395,plain,
% 7.73/1.51      ( r2_hidden(X0,k4_xboole_0(sK1,sK2)) = iProver_top
% 7.73/1.51      | r2_hidden(X0,sK2) != iProver_top
% 7.73/1.51      | r2_hidden(X0,sK1) = iProver_top ),
% 7.73/1.51      inference(superposition,[status(thm)],[c_7,c_181]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_4,plain,
% 7.73/1.51      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 7.73/1.51      inference(cnf_transformation,[],[f22]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_180,plain,
% 7.73/1.51      ( r2_hidden(X0,X1) != iProver_top
% 7.73/1.51      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 7.73/1.51      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_338,plain,
% 7.73/1.51      ( r2_hidden(X0,k4_xboole_0(sK1,sK2)) != iProver_top
% 7.73/1.51      | r2_hidden(X0,sK1) != iProver_top ),
% 7.73/1.51      inference(superposition,[status(thm)],[c_7,c_180]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_5,plain,
% 7.73/1.51      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 7.73/1.51      inference(cnf_transformation,[],[f23]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_179,plain,
% 7.73/1.51      ( r2_hidden(X0,X1) = iProver_top
% 7.73/1.51      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 7.73/1.51      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_345,plain,
% 7.73/1.51      ( r2_hidden(X0,k4_xboole_0(sK1,sK2)) != iProver_top ),
% 7.73/1.51      inference(forward_subsumption_resolution,
% 7.73/1.51                [status(thm)],
% 7.73/1.51                [c_338,c_179]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_416,plain,
% 7.73/1.51      ( r2_hidden(X0,sK2) != iProver_top
% 7.73/1.51      | r2_hidden(X0,sK1) = iProver_top ),
% 7.73/1.51      inference(global_propositional_subsumption,
% 7.73/1.51                [status(thm)],
% 7.73/1.51                [c_395,c_345]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_526,plain,
% 7.73/1.51      ( k4_xboole_0(X0,X1) = sK2
% 7.73/1.51      | r2_hidden(sK0(X0,X1,sK2),X0) = iProver_top
% 7.73/1.51      | r2_hidden(sK0(X0,X1,sK2),sK1) = iProver_top ),
% 7.73/1.51      inference(superposition,[status(thm)],[c_182,c_416]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_1039,plain,
% 7.73/1.51      ( k4_xboole_0(sK1,X0) = sK2
% 7.73/1.51      | r2_hidden(sK0(sK1,X0,sK2),sK1) = iProver_top
% 7.73/1.51      | iProver_top != iProver_top ),
% 7.73/1.51      inference(equality_factoring,[status(thm)],[c_526]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_1041,plain,
% 7.73/1.51      ( k4_xboole_0(sK1,X0) = sK2
% 7.73/1.51      | r2_hidden(sK0(sK1,X0,sK2),sK1) = iProver_top ),
% 7.73/1.51      inference(equality_resolution_simp,[status(thm)],[c_1039]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_0,plain,
% 7.73/1.51      ( ~ r2_hidden(sK0(X0,X1,X2),X0)
% 7.73/1.51      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 7.73/1.51      | r2_hidden(sK0(X0,X1,X2),X1)
% 7.73/1.51      | k4_xboole_0(X0,X1) = X2 ),
% 7.73/1.51      inference(cnf_transformation,[],[f18]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_184,plain,
% 7.73/1.51      ( k4_xboole_0(X0,X1) = X2
% 7.73/1.51      | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
% 7.73/1.51      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
% 7.73/1.51      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
% 7.73/1.51      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_22139,plain,
% 7.73/1.51      ( k4_xboole_0(sK1,X0) = sK2
% 7.73/1.51      | r2_hidden(sK0(sK1,X0,sK2),X0) = iProver_top
% 7.73/1.51      | r2_hidden(sK0(sK1,X0,sK2),sK2) != iProver_top ),
% 7.73/1.51      inference(superposition,[status(thm)],[c_1041,c_184]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_398,plain,
% 7.73/1.51      ( r2_hidden(X0,sK2) = iProver_top
% 7.73/1.51      | r2_hidden(X0,sK1) != iProver_top ),
% 7.73/1.51      inference(superposition,[status(thm)],[c_181,c_345]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_728,plain,
% 7.73/1.51      ( k4_xboole_0(sK1,X0) = X1
% 7.73/1.51      | r2_hidden(sK0(sK1,X0,X1),X1) = iProver_top
% 7.73/1.51      | r2_hidden(sK0(sK1,X0,X1),sK2) = iProver_top ),
% 7.73/1.51      inference(superposition,[status(thm)],[c_182,c_398]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_13710,plain,
% 7.73/1.51      ( k4_xboole_0(sK1,X0) = sK2
% 7.73/1.51      | r2_hidden(sK0(sK1,X0,sK2),sK2) = iProver_top
% 7.73/1.51      | iProver_top != iProver_top ),
% 7.73/1.51      inference(equality_factoring,[status(thm)],[c_728]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_13712,plain,
% 7.73/1.51      ( k4_xboole_0(sK1,X0) = sK2
% 7.73/1.51      | r2_hidden(sK0(sK1,X0,sK2),sK2) = iProver_top ),
% 7.73/1.51      inference(equality_resolution_simp,[status(thm)],[c_13710]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_36268,plain,
% 7.73/1.51      ( r2_hidden(sK0(sK1,X0,sK2),X0) = iProver_top
% 7.73/1.51      | k4_xboole_0(sK1,X0) = sK2 ),
% 7.73/1.51      inference(global_propositional_subsumption,
% 7.73/1.51                [status(thm)],
% 7.73/1.51                [c_22139,c_13712]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_36269,plain,
% 7.73/1.51      ( k4_xboole_0(sK1,X0) = sK2
% 7.73/1.51      | r2_hidden(sK0(sK1,X0,sK2),X0) = iProver_top ),
% 7.73/1.51      inference(renaming,[status(thm)],[c_36268]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_36277,plain,
% 7.73/1.51      ( k4_xboole_0(sK1,k4_xboole_0(X0,X1)) = sK2
% 7.73/1.51      | r2_hidden(sK0(sK1,k4_xboole_0(X0,X1),sK2),X1) != iProver_top ),
% 7.73/1.51      inference(superposition,[status(thm)],[c_36269,c_180]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_36301,plain,
% 7.73/1.51      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)) = sK2
% 7.73/1.51      | r2_hidden(sK0(sK1,k4_xboole_0(sK1,sK1),sK2),sK1) != iProver_top ),
% 7.73/1.51      inference(instantiation,[status(thm)],[c_36277]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_36276,plain,
% 7.73/1.51      ( k4_xboole_0(sK1,k4_xboole_0(X0,X1)) = sK2
% 7.73/1.51      | r2_hidden(sK0(sK1,k4_xboole_0(X0,X1),sK2),X0) = iProver_top ),
% 7.73/1.51      inference(superposition,[status(thm)],[c_36269,c_179]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_36298,plain,
% 7.73/1.51      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)) = sK2
% 7.73/1.51      | r2_hidden(sK0(sK1,k4_xboole_0(sK1,sK1),sK2),sK1) = iProver_top ),
% 7.73/1.51      inference(instantiation,[status(thm)],[c_36276]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_71,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_236,plain,
% 7.73/1.51      ( sK2 != X0 | sK1 != X0 | sK1 = sK2 ),
% 7.73/1.51      inference(instantiation,[status(thm)],[c_71]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_275,plain,
% 7.73/1.51      ( sK2 != k4_xboole_0(X0,X1)
% 7.73/1.51      | sK1 != k4_xboole_0(X0,X1)
% 7.73/1.51      | sK1 = sK2 ),
% 7.73/1.51      inference(instantiation,[status(thm)],[c_236]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_21498,plain,
% 7.73/1.51      ( sK2 != k4_xboole_0(X0,k4_xboole_0(X1,X2))
% 7.73/1.51      | sK1 != k4_xboole_0(X0,k4_xboole_0(X1,X2))
% 7.73/1.51      | sK1 = sK2 ),
% 7.73/1.51      inference(instantiation,[status(thm)],[c_275]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_21499,plain,
% 7.73/1.51      ( sK2 != k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))
% 7.73/1.51      | sK1 != k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))
% 7.73/1.51      | sK1 = sK2 ),
% 7.73/1.51      inference(instantiation,[status(thm)],[c_21498]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_446,plain,
% 7.73/1.51      ( ~ r2_hidden(sK0(X0,X1,X2),X2)
% 7.73/1.51      | ~ r2_hidden(sK0(X0,X1,X2),k4_xboole_0(X3,X2)) ),
% 7.73/1.51      inference(instantiation,[status(thm)],[c_4]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_8615,plain,
% 7.73/1.51      ( ~ r2_hidden(sK0(X0,k4_xboole_0(X1,X2),X2),X2)
% 7.73/1.51      | ~ r2_hidden(sK0(X0,k4_xboole_0(X1,X2),X2),k4_xboole_0(X1,X2)) ),
% 7.73/1.51      inference(instantiation,[status(thm)],[c_446]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_8617,plain,
% 7.73/1.51      ( ~ r2_hidden(sK0(sK1,k4_xboole_0(sK1,sK1),sK1),k4_xboole_0(sK1,sK1))
% 7.73/1.51      | ~ r2_hidden(sK0(sK1,k4_xboole_0(sK1,sK1),sK1),sK1) ),
% 7.73/1.51      inference(instantiation,[status(thm)],[c_8615]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_299,plain,
% 7.73/1.51      ( k4_xboole_0(X0,X1) != X2 | sK1 != X2 | sK1 = k4_xboole_0(X0,X1) ),
% 7.73/1.51      inference(instantiation,[status(thm)],[c_71]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_3454,plain,
% 7.73/1.51      ( k4_xboole_0(X0,k4_xboole_0(X1,X2)) != X3
% 7.73/1.51      | sK1 != X3
% 7.73/1.51      | sK1 = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 7.73/1.51      inference(instantiation,[status(thm)],[c_299]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_3455,plain,
% 7.73/1.51      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)) != sK1
% 7.73/1.51      | sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))
% 7.73/1.51      | sK1 != sK1 ),
% 7.73/1.51      inference(instantiation,[status(thm)],[c_3454]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_241,plain,
% 7.73/1.51      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 7.73/1.51      inference(instantiation,[status(thm)],[c_71]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_242,plain,
% 7.73/1.51      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 7.73/1.51      inference(instantiation,[status(thm)],[c_241]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_247,plain,
% 7.73/1.51      ( k4_xboole_0(X0,X1) != sK2
% 7.73/1.51      | sK2 = k4_xboole_0(X0,X1)
% 7.73/1.51      | sK2 != sK2 ),
% 7.73/1.51      inference(instantiation,[status(thm)],[c_242]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_2401,plain,
% 7.73/1.51      ( k4_xboole_0(X0,k4_xboole_0(X1,X2)) != sK2
% 7.73/1.51      | sK2 = k4_xboole_0(X0,k4_xboole_0(X1,X2))
% 7.73/1.51      | sK2 != sK2 ),
% 7.73/1.51      inference(instantiation,[status(thm)],[c_247]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_2406,plain,
% 7.73/1.51      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)) != sK2
% 7.73/1.51      | sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))
% 7.73/1.51      | sK2 != sK2 ),
% 7.73/1.51      inference(instantiation,[status(thm)],[c_2401]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_877,plain,
% 7.73/1.51      ( r2_hidden(sK0(X0,k4_xboole_0(X1,X2),X3),X0)
% 7.73/1.51      | r2_hidden(sK0(X0,k4_xboole_0(X1,X2),X3),X3)
% 7.73/1.51      | k4_xboole_0(X0,k4_xboole_0(X1,X2)) = X3 ),
% 7.73/1.51      inference(instantiation,[status(thm)],[c_2]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_879,plain,
% 7.73/1.51      ( r2_hidden(sK0(sK1,k4_xboole_0(sK1,sK1),sK1),sK1)
% 7.73/1.51      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)) = sK1 ),
% 7.73/1.51      inference(instantiation,[status(thm)],[c_877]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_492,plain,
% 7.73/1.51      ( ~ r2_hidden(sK0(X0,k4_xboole_0(X1,X2),X3),X0)
% 7.73/1.51      | ~ r2_hidden(sK0(X0,k4_xboole_0(X1,X2),X3),X3)
% 7.73/1.51      | r2_hidden(sK0(X0,k4_xboole_0(X1,X2),X3),k4_xboole_0(X1,X2))
% 7.73/1.51      | k4_xboole_0(X0,k4_xboole_0(X1,X2)) = X3 ),
% 7.73/1.51      inference(instantiation,[status(thm)],[c_0]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_495,plain,
% 7.73/1.51      ( r2_hidden(sK0(sK1,k4_xboole_0(sK1,sK1),sK1),k4_xboole_0(sK1,sK1))
% 7.73/1.51      | ~ r2_hidden(sK0(sK1,k4_xboole_0(sK1,sK1),sK1),sK1)
% 7.73/1.51      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)) = sK1 ),
% 7.73/1.51      inference(instantiation,[status(thm)],[c_492]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_70,plain,( X0 = X0 ),theory(equality) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_243,plain,
% 7.73/1.51      ( sK2 = sK2 ),
% 7.73/1.51      inference(instantiation,[status(thm)],[c_70]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_77,plain,
% 7.73/1.51      ( sK1 = sK1 ),
% 7.73/1.51      inference(instantiation,[status(thm)],[c_70]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(c_6,negated_conjecture,
% 7.73/1.51      ( sK1 != sK2 ),
% 7.73/1.51      inference(cnf_transformation,[],[f20]) ).
% 7.73/1.51  
% 7.73/1.51  cnf(contradiction,plain,
% 7.73/1.51      ( $false ),
% 7.73/1.51      inference(minisat,
% 7.73/1.51                [status(thm)],
% 7.73/1.51                [c_36301,c_36298,c_21499,c_8617,c_3455,c_2406,c_879,
% 7.73/1.51                 c_495,c_243,c_77,c_6]) ).
% 7.73/1.51  
% 7.73/1.51  
% 7.73/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.73/1.51  
% 7.73/1.51  ------                               Statistics
% 7.73/1.51  
% 7.73/1.51  ------ General
% 7.73/1.51  
% 7.73/1.51  abstr_ref_over_cycles:                  0
% 7.73/1.51  abstr_ref_under_cycles:                 0
% 7.73/1.51  gc_basic_clause_elim:                   0
% 7.73/1.51  forced_gc_time:                         0
% 7.73/1.51  parsing_time:                           0.006
% 7.73/1.51  unif_index_cands_time:                  0.
% 7.73/1.51  unif_index_add_time:                    0.
% 7.73/1.51  orderings_time:                         0.
% 7.73/1.51  out_proof_time:                         0.006
% 7.73/1.51  total_time:                             0.805
% 7.73/1.51  num_of_symbols:                         36
% 7.73/1.51  num_of_terms:                           34232
% 7.73/1.51  
% 7.73/1.51  ------ Preprocessing
% 7.73/1.51  
% 7.73/1.51  num_of_splits:                          0
% 7.73/1.51  num_of_split_atoms:                     0
% 7.73/1.51  num_of_reused_defs:                     0
% 7.73/1.51  num_eq_ax_congr_red:                    6
% 7.73/1.51  num_of_sem_filtered_clauses:            1
% 7.73/1.51  num_of_subtypes:                        0
% 7.73/1.51  monotx_restored_types:                  0
% 7.73/1.51  sat_num_of_epr_types:                   0
% 7.73/1.51  sat_num_of_non_cyclic_types:            0
% 7.73/1.51  sat_guarded_non_collapsed_types:        0
% 7.73/1.51  num_pure_diseq_elim:                    0
% 7.73/1.51  simp_replaced_by:                       0
% 7.73/1.51  res_preprocessed:                       33
% 7.73/1.51  prep_upred:                             0
% 7.73/1.51  prep_unflattend:                        0
% 7.73/1.51  smt_new_axioms:                         0
% 7.73/1.51  pred_elim_cands:                        1
% 7.73/1.51  pred_elim:                              0
% 7.73/1.51  pred_elim_cl:                           0
% 7.73/1.51  pred_elim_cycles:                       1
% 7.73/1.51  merged_defs:                            0
% 7.73/1.51  merged_defs_ncl:                        0
% 7.73/1.51  bin_hyper_res:                          0
% 7.73/1.51  prep_cycles:                            3
% 7.73/1.51  pred_elim_time:                         0.
% 7.73/1.51  splitting_time:                         0.
% 7.73/1.51  sem_filter_time:                        0.
% 7.73/1.51  monotx_time:                            0.
% 7.73/1.51  subtype_inf_time:                       0.
% 7.73/1.51  
% 7.73/1.51  ------ Problem properties
% 7.73/1.51  
% 7.73/1.51  clauses:                                8
% 7.73/1.51  conjectures:                            2
% 7.73/1.51  epr:                                    1
% 7.73/1.51  horn:                                   4
% 7.73/1.51  ground:                                 2
% 7.73/1.51  unary:                                  2
% 7.73/1.51  binary:                                 2
% 7.73/1.51  lits:                                   19
% 7.73/1.51  lits_eq:                                5
% 7.73/1.51  fd_pure:                                0
% 7.73/1.51  fd_pseudo:                              0
% 7.73/1.51  fd_cond:                                0
% 7.73/1.51  fd_pseudo_cond:                         3
% 7.73/1.51  ac_symbols:                             0
% 7.73/1.51  
% 7.73/1.51  ------ Propositional Solver
% 7.73/1.51  
% 7.73/1.51  prop_solver_calls:                      26
% 7.73/1.51  prop_fast_solver_calls:                 559
% 7.73/1.51  smt_solver_calls:                       0
% 7.73/1.51  smt_fast_solver_calls:                  0
% 7.73/1.51  prop_num_of_clauses:                    6653
% 7.73/1.51  prop_preprocess_simplified:             12161
% 7.73/1.51  prop_fo_subsumed:                       5
% 7.73/1.51  prop_solver_time:                       0.
% 7.73/1.51  smt_solver_time:                        0.
% 7.73/1.51  smt_fast_solver_time:                   0.
% 7.73/1.51  prop_fast_solver_time:                  0.
% 7.73/1.51  prop_unsat_core_time:                   0.
% 7.73/1.51  
% 7.73/1.51  ------ QBF
% 7.73/1.51  
% 7.73/1.51  qbf_q_res:                              0
% 7.73/1.51  qbf_num_tautologies:                    0
% 7.73/1.51  qbf_prep_cycles:                        0
% 7.73/1.51  
% 7.73/1.51  ------ BMC1
% 7.73/1.51  
% 7.73/1.51  bmc1_current_bound:                     -1
% 7.73/1.51  bmc1_last_solved_bound:                 -1
% 7.73/1.51  bmc1_unsat_core_size:                   -1
% 7.73/1.51  bmc1_unsat_core_parents_size:           -1
% 7.73/1.51  bmc1_merge_next_fun:                    0
% 7.73/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.73/1.51  
% 7.73/1.51  ------ Instantiation
% 7.73/1.51  
% 7.73/1.51  inst_num_of_clauses:                    1670
% 7.73/1.51  inst_num_in_passive:                    359
% 7.73/1.51  inst_num_in_active:                     638
% 7.73/1.51  inst_num_in_unprocessed:                673
% 7.73/1.51  inst_num_of_loops:                      810
% 7.73/1.51  inst_num_of_learning_restarts:          0
% 7.73/1.51  inst_num_moves_active_passive:          166
% 7.73/1.51  inst_lit_activity:                      0
% 7.73/1.51  inst_lit_activity_moves:                0
% 7.73/1.51  inst_num_tautologies:                   0
% 7.73/1.51  inst_num_prop_implied:                  0
% 7.73/1.51  inst_num_existing_simplified:           0
% 7.73/1.51  inst_num_eq_res_simplified:             0
% 7.73/1.51  inst_num_child_elim:                    0
% 7.73/1.51  inst_num_of_dismatching_blockings:      6244
% 7.73/1.51  inst_num_of_non_proper_insts:           3460
% 7.73/1.51  inst_num_of_duplicates:                 0
% 7.73/1.51  inst_inst_num_from_inst_to_res:         0
% 7.73/1.51  inst_dismatching_checking_time:         0.
% 7.73/1.51  
% 7.73/1.51  ------ Resolution
% 7.73/1.51  
% 7.73/1.51  res_num_of_clauses:                     0
% 7.73/1.51  res_num_in_passive:                     0
% 7.73/1.51  res_num_in_active:                      0
% 7.73/1.51  res_num_of_loops:                       36
% 7.73/1.51  res_forward_subset_subsumed:            481
% 7.73/1.51  res_backward_subset_subsumed:           0
% 7.73/1.51  res_forward_subsumed:                   0
% 7.73/1.51  res_backward_subsumed:                  0
% 7.73/1.51  res_forward_subsumption_resolution:     0
% 7.73/1.51  res_backward_subsumption_resolution:    0
% 7.73/1.51  res_clause_to_clause_subsumption:       21433
% 7.73/1.51  res_orphan_elimination:                 0
% 7.73/1.51  res_tautology_del:                      1157
% 7.73/1.51  res_num_eq_res_simplified:              0
% 7.73/1.51  res_num_sel_changes:                    0
% 7.73/1.51  res_moves_from_active_to_pass:          0
% 7.73/1.51  
% 7.73/1.51  ------ Superposition
% 7.73/1.51  
% 7.73/1.51  sup_time_total:                         0.
% 7.73/1.51  sup_time_generating:                    0.
% 7.73/1.51  sup_time_sim_full:                      0.
% 7.73/1.51  sup_time_sim_immed:                     0.
% 7.73/1.51  
% 7.73/1.51  sup_num_of_clauses:                     745
% 7.73/1.51  sup_num_in_active:                      152
% 7.73/1.51  sup_num_in_passive:                     593
% 7.73/1.51  sup_num_of_loops:                       161
% 7.73/1.51  sup_fw_superposition:                   1981
% 7.73/1.51  sup_bw_superposition:                   1961
% 7.73/1.51  sup_immediate_simplified:               2541
% 7.73/1.51  sup_given_eliminated:                   4
% 7.73/1.51  comparisons_done:                       0
% 7.73/1.51  comparisons_avoided:                    0
% 7.73/1.51  
% 7.73/1.51  ------ Simplifications
% 7.73/1.51  
% 7.73/1.51  
% 7.73/1.51  sim_fw_subset_subsumed:                 586
% 7.73/1.51  sim_bw_subset_subsumed:                 11
% 7.73/1.51  sim_fw_subsumed:                        842
% 7.73/1.51  sim_bw_subsumed:                        38
% 7.73/1.51  sim_fw_subsumption_res:                 12
% 7.73/1.51  sim_bw_subsumption_res:                 2
% 7.73/1.51  sim_tautology_del:                      40
% 7.73/1.51  sim_eq_tautology_del:                   259
% 7.73/1.51  sim_eq_res_simp:                        18
% 7.73/1.51  sim_fw_demodulated:                     813
% 7.73/1.51  sim_bw_demodulated:                     17
% 7.73/1.51  sim_light_normalised:                   894
% 7.73/1.51  sim_joinable_taut:                      0
% 7.73/1.51  sim_joinable_simp:                      0
% 7.73/1.51  sim_ac_normalised:                      0
% 7.73/1.51  sim_smt_subsumption:                    0
% 7.73/1.51  
%------------------------------------------------------------------------------
