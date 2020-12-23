%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:33 EST 2020

% Result     : Theorem 7.69s
% Output     : CNFRefutation 7.69s
% Verified   : 
% Statistics : Number of formulae       :   87 (1123 expanded)
%              Number of clauses        :   61 ( 341 expanded)
%              Number of leaves         :    8 ( 229 expanded)
%              Depth                    :   24
%              Number of atoms          :  262 (6366 expanded)
%              Number of equality atoms :  147 (1603 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f1])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f7])).

fof(f9,plain,(
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
    inference(rectify,[],[f8])).

fof(f10,plain,(
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

fof(f11,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f5,f12])).

fof(f22,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

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

fof(f6,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) )
   => ( sK2 != sK3
      & k4_xboole_0(sK2,sK3) = k4_xboole_0(sK3,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( sK2 != sK3
    & k4_xboole_0(sK2,sK3) = k4_xboole_0(sK3,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f6,f14])).

fof(f23,plain,(
    k4_xboole_0(sK2,sK3) = k4_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f17,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f17])).

fof(f16,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f16])).

fof(f18,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f18])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f24,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f15])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_211,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_207,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8,negated_conjecture,
    ( k4_xboole_0(sK2,sK3) = k4_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_209,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_369,plain,
    ( r2_hidden(X0,k4_xboole_0(sK2,sK3)) != iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_209])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_208,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_376,plain,
    ( r2_hidden(X0,k4_xboole_0(sK2,sK3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_369,c_208])).

cnf(c_417,plain,
    ( k4_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_207,c_376])).

cnf(c_436,plain,
    ( k4_xboole_0(sK3,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_417,c_8])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_210,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_523,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK2) = iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_436,c_210])).

cnf(c_435,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_417,c_376])).

cnf(c_740,plain,
    ( r2_hidden(X0,sK2) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_523,c_435])).

cnf(c_741,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_740])).

cnf(c_749,plain,
    ( k4_xboole_0(X0,X1) = sK3
    | r2_hidden(sK0(X0,X1,sK3),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_211,c_741])).

cnf(c_2319,plain,
    ( k4_xboole_0(sK2,X0) = sK3
    | r2_hidden(sK0(sK2,X0,sK3),sK2) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_749])).

cnf(c_2321,plain,
    ( k4_xboole_0(sK2,X0) = sK3
    | r2_hidden(sK0(sK2,X0,sK3),sK2) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2319])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_213,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_26205,plain,
    ( k4_xboole_0(sK2,X0) = sK3
    | r2_hidden(sK0(sK2,X0,sK3),X0) = iProver_top
    | r2_hidden(sK0(sK2,X0,sK3),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2321,c_213])).

cnf(c_510,plain,
    ( r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_417,c_210])).

cnf(c_2641,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_510,c_435])).

cnf(c_2642,plain,
    ( r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2641])).

cnf(c_2652,plain,
    ( k4_xboole_0(sK2,X0) = sK3
    | r2_hidden(sK0(sK2,X0,sK3),sK3) = iProver_top
    | r2_hidden(sK0(sK2,X0,sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_749,c_2642])).

cnf(c_2707,plain,
    ( k4_xboole_0(sK2,X0) = sK3
    | r2_hidden(sK0(sK2,X0,sK3),sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2652,c_2642])).

cnf(c_31733,plain,
    ( r2_hidden(sK0(sK2,X0,sK3),X0) = iProver_top
    | k4_xboole_0(sK2,X0) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_26205,c_2707])).

cnf(c_31734,plain,
    ( k4_xboole_0(sK2,X0) = sK3
    | r2_hidden(sK0(sK2,X0,sK3),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_31733])).

cnf(c_31742,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(X0,X1)) = sK3
    | r2_hidden(sK0(sK2,k4_xboole_0(X0,X1),sK3),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_31734,c_209])).

cnf(c_31771,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)) = sK3
    | r2_hidden(sK0(sK2,k4_xboole_0(sK2,sK2),sK3),sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_31742])).

cnf(c_31741,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(X0,X1)) = sK3
    | r2_hidden(sK0(sK2,k4_xboole_0(X0,X1),sK3),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_31734,c_208])).

cnf(c_31768,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)) = sK3
    | r2_hidden(sK0(sK2,k4_xboole_0(sK2,sK2),sK3),sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_31741])).

cnf(c_83,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_271,plain,
    ( sK3 != X0
    | sK2 != X0
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_83])).

cnf(c_354,plain,
    ( sK3 != k4_xboole_0(X0,X1)
    | sK2 != k4_xboole_0(X0,X1)
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_271])).

cnf(c_21320,plain,
    ( sK3 != k4_xboole_0(X0,k4_xboole_0(X1,X2))
    | sK2 != k4_xboole_0(X0,k4_xboole_0(X1,X2))
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_354])).

cnf(c_21321,plain,
    ( sK3 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK2))
    | sK2 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK2))
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_21320])).

cnf(c_572,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),k4_xboole_0(X3,X0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_9544,plain,
    ( ~ r2_hidden(sK0(X0,k4_xboole_0(X1,X0),X2),X0)
    | ~ r2_hidden(sK0(X0,k4_xboole_0(X1,X0),X2),k4_xboole_0(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_572])).

cnf(c_9546,plain,
    ( ~ r2_hidden(sK0(sK2,k4_xboole_0(sK2,sK2),sK2),k4_xboole_0(sK2,sK2))
    | ~ r2_hidden(sK0(sK2,k4_xboole_0(sK2,sK2),sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_9544])).

cnf(c_381,plain,
    ( k4_xboole_0(X0,X1) != X2
    | sK2 != X2
    | sK2 = k4_xboole_0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_83])).

cnf(c_6911,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X2)) != X3
    | sK2 != X3
    | sK2 = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_381])).

cnf(c_6912,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)) != sK2
    | sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK2))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_6911])).

cnf(c_276,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_83])).

cnf(c_277,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_276])).

cnf(c_282,plain,
    ( k4_xboole_0(X0,X1) != sK3
    | sK3 = k4_xboole_0(X0,X1)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_277])).

cnf(c_3932,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) != sK3
    | sK3 = k4_xboole_0(X0,k4_xboole_0(X1,X0))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_282])).

cnf(c_3933,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)) != sK3
    | sK3 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK2))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3932])).

cnf(c_2167,plain,
    ( r2_hidden(sK0(X0,k4_xboole_0(X1,X2),X0),X0)
    | k4_xboole_0(X0,k4_xboole_0(X1,X2)) = X0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2169,plain,
    ( r2_hidden(sK0(sK2,k4_xboole_0(sK2,sK2),sK2),sK2)
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_2167])).

cnf(c_822,plain,
    ( ~ r2_hidden(sK0(X0,k4_xboole_0(X1,X2),X3),X3)
    | ~ r2_hidden(sK0(X0,k4_xboole_0(X1,X2),X3),X0)
    | r2_hidden(sK0(X0,k4_xboole_0(X1,X2),X3),k4_xboole_0(X1,X2))
    | k4_xboole_0(X0,k4_xboole_0(X1,X2)) = X3 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_825,plain,
    ( r2_hidden(sK0(sK2,k4_xboole_0(sK2,sK2),sK2),k4_xboole_0(sK2,sK2))
    | ~ r2_hidden(sK0(sK2,k4_xboole_0(sK2,sK2),sK2),sK2)
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_822])).

cnf(c_82,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_278,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_82])).

cnf(c_89,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_82])).

cnf(c_7,negated_conjecture,
    ( sK2 != sK3 ),
    inference(cnf_transformation,[],[f24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_31771,c_31768,c_21321,c_9546,c_6912,c_3933,c_2169,c_825,c_278,c_89,c_7])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:27:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.69/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.69/1.48  
% 7.69/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.69/1.48  
% 7.69/1.48  ------  iProver source info
% 7.69/1.48  
% 7.69/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.69/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.69/1.48  git: non_committed_changes: false
% 7.69/1.48  git: last_make_outside_of_git: false
% 7.69/1.48  
% 7.69/1.48  ------ 
% 7.69/1.48  
% 7.69/1.48  ------ Input Options
% 7.69/1.48  
% 7.69/1.48  --out_options                           all
% 7.69/1.48  --tptp_safe_out                         true
% 7.69/1.48  --problem_path                          ""
% 7.69/1.48  --include_path                          ""
% 7.69/1.48  --clausifier                            res/vclausify_rel
% 7.69/1.48  --clausifier_options                    --mode clausify
% 7.69/1.48  --stdin                                 false
% 7.69/1.48  --stats_out                             all
% 7.69/1.48  
% 7.69/1.48  ------ General Options
% 7.69/1.48  
% 7.69/1.48  --fof                                   false
% 7.69/1.48  --time_out_real                         305.
% 7.69/1.48  --time_out_virtual                      -1.
% 7.69/1.48  --symbol_type_check                     false
% 7.69/1.48  --clausify_out                          false
% 7.69/1.48  --sig_cnt_out                           false
% 7.69/1.48  --trig_cnt_out                          false
% 7.69/1.48  --trig_cnt_out_tolerance                1.
% 7.69/1.48  --trig_cnt_out_sk_spl                   false
% 7.69/1.48  --abstr_cl_out                          false
% 7.69/1.48  
% 7.69/1.48  ------ Global Options
% 7.69/1.48  
% 7.69/1.48  --schedule                              default
% 7.69/1.48  --add_important_lit                     false
% 7.69/1.48  --prop_solver_per_cl                    1000
% 7.69/1.48  --min_unsat_core                        false
% 7.69/1.48  --soft_assumptions                      false
% 7.69/1.48  --soft_lemma_size                       3
% 7.69/1.48  --prop_impl_unit_size                   0
% 7.69/1.48  --prop_impl_unit                        []
% 7.69/1.48  --share_sel_clauses                     true
% 7.69/1.48  --reset_solvers                         false
% 7.69/1.48  --bc_imp_inh                            [conj_cone]
% 7.69/1.48  --conj_cone_tolerance                   3.
% 7.69/1.48  --extra_neg_conj                        none
% 7.69/1.48  --large_theory_mode                     true
% 7.69/1.48  --prolific_symb_bound                   200
% 7.69/1.48  --lt_threshold                          2000
% 7.69/1.48  --clause_weak_htbl                      true
% 7.69/1.48  --gc_record_bc_elim                     false
% 7.69/1.48  
% 7.69/1.48  ------ Preprocessing Options
% 7.69/1.48  
% 7.69/1.48  --preprocessing_flag                    true
% 7.69/1.48  --time_out_prep_mult                    0.1
% 7.69/1.48  --splitting_mode                        input
% 7.69/1.48  --splitting_grd                         true
% 7.69/1.48  --splitting_cvd                         false
% 7.69/1.48  --splitting_cvd_svl                     false
% 7.69/1.48  --splitting_nvd                         32
% 7.69/1.48  --sub_typing                            true
% 7.69/1.48  --prep_gs_sim                           true
% 7.69/1.48  --prep_unflatten                        true
% 7.69/1.48  --prep_res_sim                          true
% 7.69/1.48  --prep_upred                            true
% 7.69/1.48  --prep_sem_filter                       exhaustive
% 7.69/1.48  --prep_sem_filter_out                   false
% 7.69/1.48  --pred_elim                             true
% 7.69/1.48  --res_sim_input                         true
% 7.69/1.48  --eq_ax_congr_red                       true
% 7.69/1.48  --pure_diseq_elim                       true
% 7.69/1.48  --brand_transform                       false
% 7.69/1.48  --non_eq_to_eq                          false
% 7.69/1.48  --prep_def_merge                        true
% 7.69/1.48  --prep_def_merge_prop_impl              false
% 7.69/1.48  --prep_def_merge_mbd                    true
% 7.69/1.48  --prep_def_merge_tr_red                 false
% 7.69/1.48  --prep_def_merge_tr_cl                  false
% 7.69/1.48  --smt_preprocessing                     true
% 7.69/1.48  --smt_ac_axioms                         fast
% 7.69/1.48  --preprocessed_out                      false
% 7.69/1.48  --preprocessed_stats                    false
% 7.69/1.48  
% 7.69/1.48  ------ Abstraction refinement Options
% 7.69/1.48  
% 7.69/1.48  --abstr_ref                             []
% 7.69/1.48  --abstr_ref_prep                        false
% 7.69/1.48  --abstr_ref_until_sat                   false
% 7.69/1.48  --abstr_ref_sig_restrict                funpre
% 7.69/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.69/1.48  --abstr_ref_under                       []
% 7.69/1.48  
% 7.69/1.48  ------ SAT Options
% 7.69/1.48  
% 7.69/1.48  --sat_mode                              false
% 7.69/1.48  --sat_fm_restart_options                ""
% 7.69/1.48  --sat_gr_def                            false
% 7.69/1.48  --sat_epr_types                         true
% 7.69/1.48  --sat_non_cyclic_types                  false
% 7.69/1.48  --sat_finite_models                     false
% 7.69/1.48  --sat_fm_lemmas                         false
% 7.69/1.48  --sat_fm_prep                           false
% 7.69/1.48  --sat_fm_uc_incr                        true
% 7.69/1.48  --sat_out_model                         small
% 7.69/1.48  --sat_out_clauses                       false
% 7.69/1.48  
% 7.69/1.48  ------ QBF Options
% 7.69/1.48  
% 7.69/1.48  --qbf_mode                              false
% 7.69/1.48  --qbf_elim_univ                         false
% 7.69/1.48  --qbf_dom_inst                          none
% 7.69/1.48  --qbf_dom_pre_inst                      false
% 7.69/1.48  --qbf_sk_in                             false
% 7.69/1.48  --qbf_pred_elim                         true
% 7.69/1.48  --qbf_split                             512
% 7.69/1.48  
% 7.69/1.48  ------ BMC1 Options
% 7.69/1.48  
% 7.69/1.48  --bmc1_incremental                      false
% 7.69/1.48  --bmc1_axioms                           reachable_all
% 7.69/1.48  --bmc1_min_bound                        0
% 7.69/1.48  --bmc1_max_bound                        -1
% 7.69/1.48  --bmc1_max_bound_default                -1
% 7.69/1.48  --bmc1_symbol_reachability              true
% 7.69/1.48  --bmc1_property_lemmas                  false
% 7.69/1.48  --bmc1_k_induction                      false
% 7.69/1.48  --bmc1_non_equiv_states                 false
% 7.69/1.48  --bmc1_deadlock                         false
% 7.69/1.48  --bmc1_ucm                              false
% 7.69/1.48  --bmc1_add_unsat_core                   none
% 7.69/1.48  --bmc1_unsat_core_children              false
% 7.69/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.69/1.48  --bmc1_out_stat                         full
% 7.69/1.48  --bmc1_ground_init                      false
% 7.69/1.48  --bmc1_pre_inst_next_state              false
% 7.69/1.48  --bmc1_pre_inst_state                   false
% 7.69/1.48  --bmc1_pre_inst_reach_state             false
% 7.69/1.48  --bmc1_out_unsat_core                   false
% 7.69/1.48  --bmc1_aig_witness_out                  false
% 7.69/1.48  --bmc1_verbose                          false
% 7.69/1.48  --bmc1_dump_clauses_tptp                false
% 7.69/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.69/1.48  --bmc1_dump_file                        -
% 7.69/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.69/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.69/1.48  --bmc1_ucm_extend_mode                  1
% 7.69/1.48  --bmc1_ucm_init_mode                    2
% 7.69/1.48  --bmc1_ucm_cone_mode                    none
% 7.69/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.69/1.48  --bmc1_ucm_relax_model                  4
% 7.69/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.69/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.69/1.48  --bmc1_ucm_layered_model                none
% 7.69/1.48  --bmc1_ucm_max_lemma_size               10
% 7.69/1.48  
% 7.69/1.48  ------ AIG Options
% 7.69/1.48  
% 7.69/1.48  --aig_mode                              false
% 7.69/1.48  
% 7.69/1.48  ------ Instantiation Options
% 7.69/1.48  
% 7.69/1.48  --instantiation_flag                    true
% 7.69/1.48  --inst_sos_flag                         false
% 7.69/1.48  --inst_sos_phase                        true
% 7.69/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.69/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.69/1.48  --inst_lit_sel_side                     num_symb
% 7.69/1.48  --inst_solver_per_active                1400
% 7.69/1.48  --inst_solver_calls_frac                1.
% 7.69/1.48  --inst_passive_queue_type               priority_queues
% 7.69/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.69/1.48  --inst_passive_queues_freq              [25;2]
% 7.69/1.48  --inst_dismatching                      true
% 7.69/1.48  --inst_eager_unprocessed_to_passive     true
% 7.69/1.48  --inst_prop_sim_given                   true
% 7.69/1.48  --inst_prop_sim_new                     false
% 7.69/1.48  --inst_subs_new                         false
% 7.69/1.48  --inst_eq_res_simp                      false
% 7.69/1.48  --inst_subs_given                       false
% 7.69/1.48  --inst_orphan_elimination               true
% 7.69/1.48  --inst_learning_loop_flag               true
% 7.69/1.48  --inst_learning_start                   3000
% 7.69/1.48  --inst_learning_factor                  2
% 7.69/1.48  --inst_start_prop_sim_after_learn       3
% 7.69/1.48  --inst_sel_renew                        solver
% 7.69/1.48  --inst_lit_activity_flag                true
% 7.69/1.48  --inst_restr_to_given                   false
% 7.69/1.48  --inst_activity_threshold               500
% 7.69/1.48  --inst_out_proof                        true
% 7.69/1.48  
% 7.69/1.48  ------ Resolution Options
% 7.69/1.48  
% 7.69/1.48  --resolution_flag                       true
% 7.69/1.48  --res_lit_sel                           adaptive
% 7.69/1.48  --res_lit_sel_side                      none
% 7.69/1.48  --res_ordering                          kbo
% 7.69/1.48  --res_to_prop_solver                    active
% 7.69/1.48  --res_prop_simpl_new                    false
% 7.69/1.48  --res_prop_simpl_given                  true
% 7.69/1.48  --res_passive_queue_type                priority_queues
% 7.69/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.69/1.48  --res_passive_queues_freq               [15;5]
% 7.69/1.48  --res_forward_subs                      full
% 7.69/1.48  --res_backward_subs                     full
% 7.69/1.48  --res_forward_subs_resolution           true
% 7.69/1.48  --res_backward_subs_resolution          true
% 7.69/1.48  --res_orphan_elimination                true
% 7.69/1.48  --res_time_limit                        2.
% 7.69/1.48  --res_out_proof                         true
% 7.69/1.48  
% 7.69/1.48  ------ Superposition Options
% 7.69/1.48  
% 7.69/1.48  --superposition_flag                    true
% 7.69/1.48  --sup_passive_queue_type                priority_queues
% 7.69/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.69/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.69/1.48  --demod_completeness_check              fast
% 7.69/1.48  --demod_use_ground                      true
% 7.69/1.48  --sup_to_prop_solver                    passive
% 7.69/1.48  --sup_prop_simpl_new                    true
% 7.69/1.48  --sup_prop_simpl_given                  true
% 7.69/1.48  --sup_fun_splitting                     false
% 7.69/1.48  --sup_smt_interval                      50000
% 7.69/1.48  
% 7.69/1.48  ------ Superposition Simplification Setup
% 7.69/1.48  
% 7.69/1.48  --sup_indices_passive                   []
% 7.69/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.69/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.69/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.69/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.69/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.69/1.48  --sup_full_bw                           [BwDemod]
% 7.69/1.48  --sup_immed_triv                        [TrivRules]
% 7.69/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.69/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.69/1.48  --sup_immed_bw_main                     []
% 7.69/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.69/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.69/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.69/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.69/1.48  
% 7.69/1.48  ------ Combination Options
% 7.69/1.48  
% 7.69/1.48  --comb_res_mult                         3
% 7.69/1.48  --comb_sup_mult                         2
% 7.69/1.48  --comb_inst_mult                        10
% 7.69/1.48  
% 7.69/1.48  ------ Debug Options
% 7.69/1.48  
% 7.69/1.48  --dbg_backtrace                         false
% 7.69/1.48  --dbg_dump_prop_clauses                 false
% 7.69/1.48  --dbg_dump_prop_clauses_file            -
% 7.69/1.48  --dbg_out_stat                          false
% 7.69/1.48  ------ Parsing...
% 7.69/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.69/1.48  
% 7.69/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.69/1.48  
% 7.69/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.69/1.48  
% 7.69/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.69/1.48  ------ Proving...
% 7.69/1.48  ------ Problem Properties 
% 7.69/1.48  
% 7.69/1.48  
% 7.69/1.48  clauses                                 9
% 7.69/1.48  conjectures                             2
% 7.69/1.48  EPR                                     1
% 7.69/1.48  Horn                                    4
% 7.69/1.48  unary                                   2
% 7.69/1.48  binary                                  3
% 7.69/1.48  lits                                    21
% 7.69/1.48  lits eq                                 6
% 7.69/1.48  fd_pure                                 0
% 7.69/1.48  fd_pseudo                               0
% 7.69/1.48  fd_cond                                 1
% 7.69/1.48  fd_pseudo_cond                          3
% 7.69/1.48  AC symbols                              0
% 7.69/1.48  
% 7.69/1.48  ------ Schedule dynamic 5 is on 
% 7.69/1.48  
% 7.69/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.69/1.48  
% 7.69/1.48  
% 7.69/1.48  ------ 
% 7.69/1.48  Current options:
% 7.69/1.48  ------ 
% 7.69/1.48  
% 7.69/1.48  ------ Input Options
% 7.69/1.48  
% 7.69/1.48  --out_options                           all
% 7.69/1.48  --tptp_safe_out                         true
% 7.69/1.48  --problem_path                          ""
% 7.69/1.48  --include_path                          ""
% 7.69/1.48  --clausifier                            res/vclausify_rel
% 7.69/1.48  --clausifier_options                    --mode clausify
% 7.69/1.48  --stdin                                 false
% 7.69/1.48  --stats_out                             all
% 7.69/1.48  
% 7.69/1.48  ------ General Options
% 7.69/1.48  
% 7.69/1.48  --fof                                   false
% 7.69/1.48  --time_out_real                         305.
% 7.69/1.48  --time_out_virtual                      -1.
% 7.69/1.48  --symbol_type_check                     false
% 7.69/1.48  --clausify_out                          false
% 7.69/1.48  --sig_cnt_out                           false
% 7.69/1.48  --trig_cnt_out                          false
% 7.69/1.48  --trig_cnt_out_tolerance                1.
% 7.69/1.48  --trig_cnt_out_sk_spl                   false
% 7.69/1.48  --abstr_cl_out                          false
% 7.69/1.48  
% 7.69/1.48  ------ Global Options
% 7.69/1.48  
% 7.69/1.48  --schedule                              default
% 7.69/1.48  --add_important_lit                     false
% 7.69/1.48  --prop_solver_per_cl                    1000
% 7.69/1.48  --min_unsat_core                        false
% 7.69/1.48  --soft_assumptions                      false
% 7.69/1.48  --soft_lemma_size                       3
% 7.69/1.48  --prop_impl_unit_size                   0
% 7.69/1.48  --prop_impl_unit                        []
% 7.69/1.48  --share_sel_clauses                     true
% 7.69/1.48  --reset_solvers                         false
% 7.69/1.48  --bc_imp_inh                            [conj_cone]
% 7.69/1.48  --conj_cone_tolerance                   3.
% 7.69/1.48  --extra_neg_conj                        none
% 7.69/1.48  --large_theory_mode                     true
% 7.69/1.48  --prolific_symb_bound                   200
% 7.69/1.48  --lt_threshold                          2000
% 7.69/1.48  --clause_weak_htbl                      true
% 7.69/1.48  --gc_record_bc_elim                     false
% 7.69/1.48  
% 7.69/1.48  ------ Preprocessing Options
% 7.69/1.48  
% 7.69/1.48  --preprocessing_flag                    true
% 7.69/1.48  --time_out_prep_mult                    0.1
% 7.69/1.48  --splitting_mode                        input
% 7.69/1.48  --splitting_grd                         true
% 7.69/1.48  --splitting_cvd                         false
% 7.69/1.48  --splitting_cvd_svl                     false
% 7.69/1.48  --splitting_nvd                         32
% 7.69/1.48  --sub_typing                            true
% 7.69/1.48  --prep_gs_sim                           true
% 7.69/1.48  --prep_unflatten                        true
% 7.69/1.48  --prep_res_sim                          true
% 7.69/1.48  --prep_upred                            true
% 7.69/1.48  --prep_sem_filter                       exhaustive
% 7.69/1.48  --prep_sem_filter_out                   false
% 7.69/1.48  --pred_elim                             true
% 7.69/1.48  --res_sim_input                         true
% 7.69/1.48  --eq_ax_congr_red                       true
% 7.69/1.48  --pure_diseq_elim                       true
% 7.69/1.48  --brand_transform                       false
% 7.69/1.48  --non_eq_to_eq                          false
% 7.69/1.48  --prep_def_merge                        true
% 7.69/1.48  --prep_def_merge_prop_impl              false
% 7.69/1.48  --prep_def_merge_mbd                    true
% 7.69/1.48  --prep_def_merge_tr_red                 false
% 7.69/1.48  --prep_def_merge_tr_cl                  false
% 7.69/1.48  --smt_preprocessing                     true
% 7.69/1.48  --smt_ac_axioms                         fast
% 7.69/1.48  --preprocessed_out                      false
% 7.69/1.48  --preprocessed_stats                    false
% 7.69/1.48  
% 7.69/1.48  ------ Abstraction refinement Options
% 7.69/1.48  
% 7.69/1.48  --abstr_ref                             []
% 7.69/1.48  --abstr_ref_prep                        false
% 7.69/1.48  --abstr_ref_until_sat                   false
% 7.69/1.48  --abstr_ref_sig_restrict                funpre
% 7.69/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.69/1.48  --abstr_ref_under                       []
% 7.69/1.48  
% 7.69/1.48  ------ SAT Options
% 7.69/1.48  
% 7.69/1.48  --sat_mode                              false
% 7.69/1.48  --sat_fm_restart_options                ""
% 7.69/1.48  --sat_gr_def                            false
% 7.69/1.48  --sat_epr_types                         true
% 7.69/1.48  --sat_non_cyclic_types                  false
% 7.69/1.48  --sat_finite_models                     false
% 7.69/1.48  --sat_fm_lemmas                         false
% 7.69/1.48  --sat_fm_prep                           false
% 7.69/1.48  --sat_fm_uc_incr                        true
% 7.69/1.48  --sat_out_model                         small
% 7.69/1.48  --sat_out_clauses                       false
% 7.69/1.48  
% 7.69/1.48  ------ QBF Options
% 7.69/1.48  
% 7.69/1.48  --qbf_mode                              false
% 7.69/1.48  --qbf_elim_univ                         false
% 7.69/1.48  --qbf_dom_inst                          none
% 7.69/1.48  --qbf_dom_pre_inst                      false
% 7.69/1.48  --qbf_sk_in                             false
% 7.69/1.48  --qbf_pred_elim                         true
% 7.69/1.48  --qbf_split                             512
% 7.69/1.48  
% 7.69/1.48  ------ BMC1 Options
% 7.69/1.48  
% 7.69/1.48  --bmc1_incremental                      false
% 7.69/1.48  --bmc1_axioms                           reachable_all
% 7.69/1.48  --bmc1_min_bound                        0
% 7.69/1.48  --bmc1_max_bound                        -1
% 7.69/1.48  --bmc1_max_bound_default                -1
% 7.69/1.48  --bmc1_symbol_reachability              true
% 7.69/1.48  --bmc1_property_lemmas                  false
% 7.69/1.48  --bmc1_k_induction                      false
% 7.69/1.48  --bmc1_non_equiv_states                 false
% 7.69/1.48  --bmc1_deadlock                         false
% 7.69/1.48  --bmc1_ucm                              false
% 7.69/1.48  --bmc1_add_unsat_core                   none
% 7.69/1.48  --bmc1_unsat_core_children              false
% 7.69/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.69/1.48  --bmc1_out_stat                         full
% 7.69/1.48  --bmc1_ground_init                      false
% 7.69/1.48  --bmc1_pre_inst_next_state              false
% 7.69/1.48  --bmc1_pre_inst_state                   false
% 7.69/1.48  --bmc1_pre_inst_reach_state             false
% 7.69/1.48  --bmc1_out_unsat_core                   false
% 7.69/1.48  --bmc1_aig_witness_out                  false
% 7.69/1.48  --bmc1_verbose                          false
% 7.69/1.48  --bmc1_dump_clauses_tptp                false
% 7.69/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.69/1.48  --bmc1_dump_file                        -
% 7.69/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.69/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.69/1.48  --bmc1_ucm_extend_mode                  1
% 7.69/1.48  --bmc1_ucm_init_mode                    2
% 7.69/1.48  --bmc1_ucm_cone_mode                    none
% 7.69/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.69/1.48  --bmc1_ucm_relax_model                  4
% 7.69/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.69/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.69/1.48  --bmc1_ucm_layered_model                none
% 7.69/1.48  --bmc1_ucm_max_lemma_size               10
% 7.69/1.48  
% 7.69/1.48  ------ AIG Options
% 7.69/1.48  
% 7.69/1.48  --aig_mode                              false
% 7.69/1.48  
% 7.69/1.48  ------ Instantiation Options
% 7.69/1.48  
% 7.69/1.48  --instantiation_flag                    true
% 7.69/1.48  --inst_sos_flag                         false
% 7.69/1.48  --inst_sos_phase                        true
% 7.69/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.69/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.69/1.48  --inst_lit_sel_side                     none
% 7.69/1.48  --inst_solver_per_active                1400
% 7.69/1.48  --inst_solver_calls_frac                1.
% 7.69/1.48  --inst_passive_queue_type               priority_queues
% 7.69/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.69/1.48  --inst_passive_queues_freq              [25;2]
% 7.69/1.48  --inst_dismatching                      true
% 7.69/1.48  --inst_eager_unprocessed_to_passive     true
% 7.69/1.48  --inst_prop_sim_given                   true
% 7.69/1.48  --inst_prop_sim_new                     false
% 7.69/1.48  --inst_subs_new                         false
% 7.69/1.48  --inst_eq_res_simp                      false
% 7.69/1.48  --inst_subs_given                       false
% 7.69/1.48  --inst_orphan_elimination               true
% 7.69/1.48  --inst_learning_loop_flag               true
% 7.69/1.48  --inst_learning_start                   3000
% 7.69/1.48  --inst_learning_factor                  2
% 7.69/1.48  --inst_start_prop_sim_after_learn       3
% 7.69/1.48  --inst_sel_renew                        solver
% 7.69/1.48  --inst_lit_activity_flag                true
% 7.69/1.48  --inst_restr_to_given                   false
% 7.69/1.48  --inst_activity_threshold               500
% 7.69/1.48  --inst_out_proof                        true
% 7.69/1.48  
% 7.69/1.48  ------ Resolution Options
% 7.69/1.48  
% 7.69/1.48  --resolution_flag                       false
% 7.69/1.48  --res_lit_sel                           adaptive
% 7.69/1.48  --res_lit_sel_side                      none
% 7.69/1.48  --res_ordering                          kbo
% 7.69/1.48  --res_to_prop_solver                    active
% 7.69/1.48  --res_prop_simpl_new                    false
% 7.69/1.48  --res_prop_simpl_given                  true
% 7.69/1.48  --res_passive_queue_type                priority_queues
% 7.69/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.69/1.48  --res_passive_queues_freq               [15;5]
% 7.69/1.48  --res_forward_subs                      full
% 7.69/1.48  --res_backward_subs                     full
% 7.69/1.48  --res_forward_subs_resolution           true
% 7.69/1.48  --res_backward_subs_resolution          true
% 7.69/1.48  --res_orphan_elimination                true
% 7.69/1.48  --res_time_limit                        2.
% 7.69/1.48  --res_out_proof                         true
% 7.69/1.48  
% 7.69/1.48  ------ Superposition Options
% 7.69/1.48  
% 7.69/1.48  --superposition_flag                    true
% 7.69/1.48  --sup_passive_queue_type                priority_queues
% 7.69/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.69/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.69/1.48  --demod_completeness_check              fast
% 7.69/1.48  --demod_use_ground                      true
% 7.69/1.48  --sup_to_prop_solver                    passive
% 7.69/1.48  --sup_prop_simpl_new                    true
% 7.69/1.48  --sup_prop_simpl_given                  true
% 7.69/1.48  --sup_fun_splitting                     false
% 7.69/1.48  --sup_smt_interval                      50000
% 7.69/1.48  
% 7.69/1.48  ------ Superposition Simplification Setup
% 7.69/1.48  
% 7.69/1.48  --sup_indices_passive                   []
% 7.69/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.69/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.69/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.69/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.69/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.69/1.48  --sup_full_bw                           [BwDemod]
% 7.69/1.48  --sup_immed_triv                        [TrivRules]
% 7.69/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.69/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.69/1.48  --sup_immed_bw_main                     []
% 7.69/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.69/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.69/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.69/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.69/1.48  
% 7.69/1.48  ------ Combination Options
% 7.69/1.48  
% 7.69/1.48  --comb_res_mult                         3
% 7.69/1.48  --comb_sup_mult                         2
% 7.69/1.48  --comb_inst_mult                        10
% 7.69/1.48  
% 7.69/1.48  ------ Debug Options
% 7.69/1.48  
% 7.69/1.48  --dbg_backtrace                         false
% 7.69/1.48  --dbg_dump_prop_clauses                 false
% 7.69/1.48  --dbg_dump_prop_clauses_file            -
% 7.69/1.48  --dbg_out_stat                          false
% 7.69/1.48  
% 7.69/1.48  
% 7.69/1.48  
% 7.69/1.48  
% 7.69/1.48  ------ Proving...
% 7.69/1.48  
% 7.69/1.48  
% 7.69/1.48  % SZS status Theorem for theBenchmark.p
% 7.69/1.48  
% 7.69/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.69/1.48  
% 7.69/1.48  fof(f1,axiom,(
% 7.69/1.48    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.69/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.69/1.48  
% 7.69/1.48  fof(f7,plain,(
% 7.69/1.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.69/1.48    inference(nnf_transformation,[],[f1])).
% 7.69/1.48  
% 7.69/1.48  fof(f8,plain,(
% 7.69/1.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.69/1.48    inference(flattening,[],[f7])).
% 7.69/1.48  
% 7.69/1.48  fof(f9,plain,(
% 7.69/1.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.69/1.48    inference(rectify,[],[f8])).
% 7.69/1.48  
% 7.69/1.48  fof(f10,plain,(
% 7.69/1.48    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.69/1.48    introduced(choice_axiom,[])).
% 7.69/1.48  
% 7.69/1.48  fof(f11,plain,(
% 7.69/1.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.69/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).
% 7.69/1.48  
% 7.69/1.48  fof(f19,plain,(
% 7.69/1.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.69/1.48    inference(cnf_transformation,[],[f11])).
% 7.69/1.48  
% 7.69/1.48  fof(f2,axiom,(
% 7.69/1.48    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 7.69/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.69/1.48  
% 7.69/1.48  fof(f5,plain,(
% 7.69/1.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 7.69/1.48    inference(ennf_transformation,[],[f2])).
% 7.69/1.48  
% 7.69/1.48  fof(f12,plain,(
% 7.69/1.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 7.69/1.48    introduced(choice_axiom,[])).
% 7.69/1.48  
% 7.69/1.48  fof(f13,plain,(
% 7.69/1.48    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 7.69/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f5,f12])).
% 7.69/1.48  
% 7.69/1.48  fof(f22,plain,(
% 7.69/1.48    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 7.69/1.48    inference(cnf_transformation,[],[f13])).
% 7.69/1.48  
% 7.69/1.48  fof(f3,conjecture,(
% 7.69/1.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 7.69/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.69/1.48  
% 7.69/1.48  fof(f4,negated_conjecture,(
% 7.69/1.48    ~! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 7.69/1.48    inference(negated_conjecture,[],[f3])).
% 7.69/1.48  
% 7.69/1.48  fof(f6,plain,(
% 7.69/1.48    ? [X0,X1] : (X0 != X1 & k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0))),
% 7.69/1.48    inference(ennf_transformation,[],[f4])).
% 7.69/1.48  
% 7.69/1.48  fof(f14,plain,(
% 7.69/1.48    ? [X0,X1] : (X0 != X1 & k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)) => (sK2 != sK3 & k4_xboole_0(sK2,sK3) = k4_xboole_0(sK3,sK2))),
% 7.69/1.48    introduced(choice_axiom,[])).
% 7.69/1.48  
% 7.69/1.48  fof(f15,plain,(
% 7.69/1.48    sK2 != sK3 & k4_xboole_0(sK2,sK3) = k4_xboole_0(sK3,sK2)),
% 7.69/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f6,f14])).
% 7.69/1.48  
% 7.69/1.48  fof(f23,plain,(
% 7.69/1.48    k4_xboole_0(sK2,sK3) = k4_xboole_0(sK3,sK2)),
% 7.69/1.48    inference(cnf_transformation,[],[f15])).
% 7.69/1.48  
% 7.69/1.48  fof(f17,plain,(
% 7.69/1.48    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.69/1.48    inference(cnf_transformation,[],[f11])).
% 7.69/1.48  
% 7.69/1.48  fof(f26,plain,(
% 7.69/1.48    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 7.69/1.48    inference(equality_resolution,[],[f17])).
% 7.69/1.48  
% 7.69/1.48  fof(f16,plain,(
% 7.69/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.69/1.48    inference(cnf_transformation,[],[f11])).
% 7.69/1.48  
% 7.69/1.48  fof(f27,plain,(
% 7.69/1.48    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 7.69/1.48    inference(equality_resolution,[],[f16])).
% 7.69/1.48  
% 7.69/1.48  fof(f18,plain,(
% 7.69/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 7.69/1.48    inference(cnf_transformation,[],[f11])).
% 7.69/1.48  
% 7.69/1.48  fof(f25,plain,(
% 7.69/1.48    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 7.69/1.48    inference(equality_resolution,[],[f18])).
% 7.69/1.48  
% 7.69/1.48  fof(f21,plain,(
% 7.69/1.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.69/1.48    inference(cnf_transformation,[],[f11])).
% 7.69/1.48  
% 7.69/1.48  fof(f24,plain,(
% 7.69/1.48    sK2 != sK3),
% 7.69/1.48    inference(cnf_transformation,[],[f15])).
% 7.69/1.48  
% 7.69/1.48  cnf(c_2,plain,
% 7.69/1.48      ( r2_hidden(sK0(X0,X1,X2),X0)
% 7.69/1.48      | r2_hidden(sK0(X0,X1,X2),X2)
% 7.69/1.48      | k4_xboole_0(X0,X1) = X2 ),
% 7.69/1.48      inference(cnf_transformation,[],[f19]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_211,plain,
% 7.69/1.48      ( k4_xboole_0(X0,X1) = X2
% 7.69/1.48      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 7.69/1.48      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 7.69/1.48      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_6,plain,
% 7.69/1.48      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 7.69/1.48      inference(cnf_transformation,[],[f22]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_207,plain,
% 7.69/1.48      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 7.69/1.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_8,negated_conjecture,
% 7.69/1.48      ( k4_xboole_0(sK2,sK3) = k4_xboole_0(sK3,sK2) ),
% 7.69/1.48      inference(cnf_transformation,[],[f23]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_4,plain,
% 7.69/1.48      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 7.69/1.48      inference(cnf_transformation,[],[f26]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_209,plain,
% 7.69/1.48      ( r2_hidden(X0,X1) != iProver_top
% 7.69/1.48      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 7.69/1.48      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_369,plain,
% 7.69/1.48      ( r2_hidden(X0,k4_xboole_0(sK2,sK3)) != iProver_top
% 7.69/1.48      | r2_hidden(X0,sK2) != iProver_top ),
% 7.69/1.48      inference(superposition,[status(thm)],[c_8,c_209]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_5,plain,
% 7.69/1.48      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 7.69/1.48      inference(cnf_transformation,[],[f27]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_208,plain,
% 7.69/1.48      ( r2_hidden(X0,X1) = iProver_top
% 7.69/1.48      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 7.69/1.48      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_376,plain,
% 7.69/1.48      ( r2_hidden(X0,k4_xboole_0(sK2,sK3)) != iProver_top ),
% 7.69/1.48      inference(forward_subsumption_resolution,
% 7.69/1.48                [status(thm)],
% 7.69/1.48                [c_369,c_208]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_417,plain,
% 7.69/1.48      ( k4_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 7.69/1.48      inference(superposition,[status(thm)],[c_207,c_376]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_436,plain,
% 7.69/1.48      ( k4_xboole_0(sK3,sK2) = k1_xboole_0 ),
% 7.69/1.48      inference(demodulation,[status(thm)],[c_417,c_8]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_3,plain,
% 7.69/1.48      ( ~ r2_hidden(X0,X1)
% 7.69/1.48      | r2_hidden(X0,X2)
% 7.69/1.48      | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 7.69/1.48      inference(cnf_transformation,[],[f25]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_210,plain,
% 7.69/1.48      ( r2_hidden(X0,X1) != iProver_top
% 7.69/1.48      | r2_hidden(X0,X2) = iProver_top
% 7.69/1.48      | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
% 7.69/1.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_523,plain,
% 7.69/1.48      ( r2_hidden(X0,sK3) != iProver_top
% 7.69/1.48      | r2_hidden(X0,sK2) = iProver_top
% 7.69/1.48      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 7.69/1.48      inference(superposition,[status(thm)],[c_436,c_210]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_435,plain,
% 7.69/1.48      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.69/1.48      inference(demodulation,[status(thm)],[c_417,c_376]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_740,plain,
% 7.69/1.48      ( r2_hidden(X0,sK2) = iProver_top
% 7.69/1.48      | r2_hidden(X0,sK3) != iProver_top ),
% 7.69/1.48      inference(global_propositional_subsumption,
% 7.69/1.48                [status(thm)],
% 7.69/1.48                [c_523,c_435]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_741,plain,
% 7.69/1.48      ( r2_hidden(X0,sK3) != iProver_top
% 7.69/1.48      | r2_hidden(X0,sK2) = iProver_top ),
% 7.69/1.48      inference(renaming,[status(thm)],[c_740]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_749,plain,
% 7.69/1.48      ( k4_xboole_0(X0,X1) = sK3
% 7.69/1.48      | r2_hidden(sK0(X0,X1,sK3),X0) = iProver_top
% 7.69/1.48      | r2_hidden(sK0(X0,X1,sK3),sK2) = iProver_top ),
% 7.69/1.48      inference(superposition,[status(thm)],[c_211,c_741]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_2319,plain,
% 7.69/1.48      ( k4_xboole_0(sK2,X0) = sK3
% 7.69/1.48      | r2_hidden(sK0(sK2,X0,sK3),sK2) = iProver_top
% 7.69/1.48      | iProver_top != iProver_top ),
% 7.69/1.48      inference(equality_factoring,[status(thm)],[c_749]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_2321,plain,
% 7.69/1.48      ( k4_xboole_0(sK2,X0) = sK3
% 7.69/1.48      | r2_hidden(sK0(sK2,X0,sK3),sK2) = iProver_top ),
% 7.69/1.48      inference(equality_resolution_simp,[status(thm)],[c_2319]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_0,plain,
% 7.69/1.48      ( ~ r2_hidden(sK0(X0,X1,X2),X0)
% 7.69/1.48      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 7.69/1.48      | r2_hidden(sK0(X0,X1,X2),X1)
% 7.69/1.48      | k4_xboole_0(X0,X1) = X2 ),
% 7.69/1.48      inference(cnf_transformation,[],[f21]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_213,plain,
% 7.69/1.48      ( k4_xboole_0(X0,X1) = X2
% 7.69/1.48      | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
% 7.69/1.48      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
% 7.69/1.48      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
% 7.69/1.48      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_26205,plain,
% 7.69/1.48      ( k4_xboole_0(sK2,X0) = sK3
% 7.69/1.48      | r2_hidden(sK0(sK2,X0,sK3),X0) = iProver_top
% 7.69/1.48      | r2_hidden(sK0(sK2,X0,sK3),sK3) != iProver_top ),
% 7.69/1.48      inference(superposition,[status(thm)],[c_2321,c_213]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_510,plain,
% 7.69/1.48      ( r2_hidden(X0,sK3) = iProver_top
% 7.69/1.48      | r2_hidden(X0,sK2) != iProver_top
% 7.69/1.48      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 7.69/1.48      inference(superposition,[status(thm)],[c_417,c_210]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_2641,plain,
% 7.69/1.48      ( r2_hidden(X0,sK2) != iProver_top
% 7.69/1.48      | r2_hidden(X0,sK3) = iProver_top ),
% 7.69/1.48      inference(global_propositional_subsumption,
% 7.69/1.48                [status(thm)],
% 7.69/1.48                [c_510,c_435]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_2642,plain,
% 7.69/1.48      ( r2_hidden(X0,sK3) = iProver_top
% 7.69/1.48      | r2_hidden(X0,sK2) != iProver_top ),
% 7.69/1.48      inference(renaming,[status(thm)],[c_2641]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_2652,plain,
% 7.69/1.48      ( k4_xboole_0(sK2,X0) = sK3
% 7.69/1.48      | r2_hidden(sK0(sK2,X0,sK3),sK3) = iProver_top
% 7.69/1.48      | r2_hidden(sK0(sK2,X0,sK3),sK2) = iProver_top ),
% 7.69/1.48      inference(superposition,[status(thm)],[c_749,c_2642]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_2707,plain,
% 7.69/1.48      ( k4_xboole_0(sK2,X0) = sK3
% 7.69/1.48      | r2_hidden(sK0(sK2,X0,sK3),sK3) = iProver_top ),
% 7.69/1.48      inference(forward_subsumption_resolution,
% 7.69/1.48                [status(thm)],
% 7.69/1.48                [c_2652,c_2642]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_31733,plain,
% 7.69/1.48      ( r2_hidden(sK0(sK2,X0,sK3),X0) = iProver_top
% 7.69/1.48      | k4_xboole_0(sK2,X0) = sK3 ),
% 7.69/1.48      inference(global_propositional_subsumption,
% 7.69/1.48                [status(thm)],
% 7.69/1.48                [c_26205,c_2707]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_31734,plain,
% 7.69/1.48      ( k4_xboole_0(sK2,X0) = sK3
% 7.69/1.48      | r2_hidden(sK0(sK2,X0,sK3),X0) = iProver_top ),
% 7.69/1.48      inference(renaming,[status(thm)],[c_31733]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_31742,plain,
% 7.69/1.48      ( k4_xboole_0(sK2,k4_xboole_0(X0,X1)) = sK3
% 7.69/1.48      | r2_hidden(sK0(sK2,k4_xboole_0(X0,X1),sK3),X1) != iProver_top ),
% 7.69/1.48      inference(superposition,[status(thm)],[c_31734,c_209]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_31771,plain,
% 7.69/1.48      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)) = sK3
% 7.69/1.48      | r2_hidden(sK0(sK2,k4_xboole_0(sK2,sK2),sK3),sK2) != iProver_top ),
% 7.69/1.48      inference(instantiation,[status(thm)],[c_31742]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_31741,plain,
% 7.69/1.48      ( k4_xboole_0(sK2,k4_xboole_0(X0,X1)) = sK3
% 7.69/1.48      | r2_hidden(sK0(sK2,k4_xboole_0(X0,X1),sK3),X0) = iProver_top ),
% 7.69/1.48      inference(superposition,[status(thm)],[c_31734,c_208]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_31768,plain,
% 7.69/1.48      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)) = sK3
% 7.69/1.48      | r2_hidden(sK0(sK2,k4_xboole_0(sK2,sK2),sK3),sK2) = iProver_top ),
% 7.69/1.48      inference(instantiation,[status(thm)],[c_31741]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_83,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_271,plain,
% 7.69/1.48      ( sK3 != X0 | sK2 != X0 | sK2 = sK3 ),
% 7.69/1.48      inference(instantiation,[status(thm)],[c_83]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_354,plain,
% 7.69/1.48      ( sK3 != k4_xboole_0(X0,X1)
% 7.69/1.48      | sK2 != k4_xboole_0(X0,X1)
% 7.69/1.48      | sK2 = sK3 ),
% 7.69/1.48      inference(instantiation,[status(thm)],[c_271]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_21320,plain,
% 7.69/1.48      ( sK3 != k4_xboole_0(X0,k4_xboole_0(X1,X2))
% 7.69/1.48      | sK2 != k4_xboole_0(X0,k4_xboole_0(X1,X2))
% 7.69/1.48      | sK2 = sK3 ),
% 7.69/1.48      inference(instantiation,[status(thm)],[c_354]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_21321,plain,
% 7.69/1.48      ( sK3 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK2))
% 7.69/1.48      | sK2 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK2))
% 7.69/1.48      | sK2 = sK3 ),
% 7.69/1.48      inference(instantiation,[status(thm)],[c_21320]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_572,plain,
% 7.69/1.48      ( ~ r2_hidden(sK0(X0,X1,X2),X0)
% 7.69/1.48      | ~ r2_hidden(sK0(X0,X1,X2),k4_xboole_0(X3,X0)) ),
% 7.69/1.48      inference(instantiation,[status(thm)],[c_4]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_9544,plain,
% 7.69/1.48      ( ~ r2_hidden(sK0(X0,k4_xboole_0(X1,X0),X2),X0)
% 7.69/1.48      | ~ r2_hidden(sK0(X0,k4_xboole_0(X1,X0),X2),k4_xboole_0(X1,X0)) ),
% 7.69/1.48      inference(instantiation,[status(thm)],[c_572]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_9546,plain,
% 7.69/1.48      ( ~ r2_hidden(sK0(sK2,k4_xboole_0(sK2,sK2),sK2),k4_xboole_0(sK2,sK2))
% 7.69/1.48      | ~ r2_hidden(sK0(sK2,k4_xboole_0(sK2,sK2),sK2),sK2) ),
% 7.69/1.48      inference(instantiation,[status(thm)],[c_9544]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_381,plain,
% 7.69/1.48      ( k4_xboole_0(X0,X1) != X2 | sK2 != X2 | sK2 = k4_xboole_0(X0,X1) ),
% 7.69/1.48      inference(instantiation,[status(thm)],[c_83]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_6911,plain,
% 7.69/1.48      ( k4_xboole_0(X0,k4_xboole_0(X1,X2)) != X3
% 7.69/1.48      | sK2 != X3
% 7.69/1.48      | sK2 = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 7.69/1.48      inference(instantiation,[status(thm)],[c_381]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_6912,plain,
% 7.69/1.48      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)) != sK2
% 7.69/1.48      | sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK2))
% 7.69/1.48      | sK2 != sK2 ),
% 7.69/1.48      inference(instantiation,[status(thm)],[c_6911]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_276,plain,
% 7.69/1.48      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 7.69/1.48      inference(instantiation,[status(thm)],[c_83]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_277,plain,
% 7.69/1.48      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 7.69/1.48      inference(instantiation,[status(thm)],[c_276]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_282,plain,
% 7.69/1.48      ( k4_xboole_0(X0,X1) != sK3
% 7.69/1.48      | sK3 = k4_xboole_0(X0,X1)
% 7.69/1.48      | sK3 != sK3 ),
% 7.69/1.48      inference(instantiation,[status(thm)],[c_277]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_3932,plain,
% 7.69/1.48      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) != sK3
% 7.69/1.48      | sK3 = k4_xboole_0(X0,k4_xboole_0(X1,X0))
% 7.69/1.48      | sK3 != sK3 ),
% 7.69/1.48      inference(instantiation,[status(thm)],[c_282]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_3933,plain,
% 7.69/1.48      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)) != sK3
% 7.69/1.48      | sK3 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK2))
% 7.69/1.48      | sK3 != sK3 ),
% 7.69/1.48      inference(instantiation,[status(thm)],[c_3932]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_2167,plain,
% 7.69/1.48      ( r2_hidden(sK0(X0,k4_xboole_0(X1,X2),X0),X0)
% 7.69/1.48      | k4_xboole_0(X0,k4_xboole_0(X1,X2)) = X0 ),
% 7.69/1.48      inference(instantiation,[status(thm)],[c_2]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_2169,plain,
% 7.69/1.48      ( r2_hidden(sK0(sK2,k4_xboole_0(sK2,sK2),sK2),sK2)
% 7.69/1.48      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)) = sK2 ),
% 7.69/1.48      inference(instantiation,[status(thm)],[c_2167]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_822,plain,
% 7.69/1.48      ( ~ r2_hidden(sK0(X0,k4_xboole_0(X1,X2),X3),X3)
% 7.69/1.48      | ~ r2_hidden(sK0(X0,k4_xboole_0(X1,X2),X3),X0)
% 7.69/1.48      | r2_hidden(sK0(X0,k4_xboole_0(X1,X2),X3),k4_xboole_0(X1,X2))
% 7.69/1.48      | k4_xboole_0(X0,k4_xboole_0(X1,X2)) = X3 ),
% 7.69/1.48      inference(instantiation,[status(thm)],[c_0]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_825,plain,
% 7.69/1.48      ( r2_hidden(sK0(sK2,k4_xboole_0(sK2,sK2),sK2),k4_xboole_0(sK2,sK2))
% 7.69/1.48      | ~ r2_hidden(sK0(sK2,k4_xboole_0(sK2,sK2),sK2),sK2)
% 7.69/1.48      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)) = sK2 ),
% 7.69/1.48      inference(instantiation,[status(thm)],[c_822]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_82,plain,( X0 = X0 ),theory(equality) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_278,plain,
% 7.69/1.48      ( sK3 = sK3 ),
% 7.69/1.48      inference(instantiation,[status(thm)],[c_82]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_89,plain,
% 7.69/1.48      ( sK2 = sK2 ),
% 7.69/1.48      inference(instantiation,[status(thm)],[c_82]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(c_7,negated_conjecture,
% 7.69/1.48      ( sK2 != sK3 ),
% 7.69/1.48      inference(cnf_transformation,[],[f24]) ).
% 7.69/1.48  
% 7.69/1.48  cnf(contradiction,plain,
% 7.69/1.48      ( $false ),
% 7.69/1.48      inference(minisat,
% 7.69/1.48                [status(thm)],
% 7.69/1.48                [c_31771,c_31768,c_21321,c_9546,c_6912,c_3933,c_2169,
% 7.69/1.48                 c_825,c_278,c_89,c_7]) ).
% 7.69/1.48  
% 7.69/1.48  
% 7.69/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.69/1.48  
% 7.69/1.48  ------                               Statistics
% 7.69/1.48  
% 7.69/1.48  ------ General
% 7.69/1.48  
% 7.69/1.48  abstr_ref_over_cycles:                  0
% 7.69/1.48  abstr_ref_under_cycles:                 0
% 7.69/1.48  gc_basic_clause_elim:                   0
% 7.69/1.48  forced_gc_time:                         0
% 7.69/1.48  parsing_time:                           0.006
% 7.69/1.48  unif_index_cands_time:                  0.
% 7.69/1.48  unif_index_add_time:                    0.
% 7.69/1.48  orderings_time:                         0.
% 7.69/1.48  out_proof_time:                         0.008
% 7.69/1.48  total_time:                             0.657
% 7.69/1.48  num_of_symbols:                         38
% 7.69/1.48  num_of_terms:                           28399
% 7.69/1.48  
% 7.69/1.48  ------ Preprocessing
% 7.69/1.48  
% 7.69/1.48  num_of_splits:                          0
% 7.69/1.48  num_of_split_atoms:                     0
% 7.69/1.48  num_of_reused_defs:                     0
% 7.69/1.48  num_eq_ax_congr_red:                    8
% 7.69/1.48  num_of_sem_filtered_clauses:            1
% 7.69/1.48  num_of_subtypes:                        0
% 7.69/1.48  monotx_restored_types:                  0
% 7.69/1.48  sat_num_of_epr_types:                   0
% 7.69/1.48  sat_num_of_non_cyclic_types:            0
% 7.69/1.48  sat_guarded_non_collapsed_types:        0
% 7.69/1.48  num_pure_diseq_elim:                    0
% 7.69/1.48  simp_replaced_by:                       0
% 7.69/1.48  res_preprocessed:                       36
% 7.69/1.48  prep_upred:                             0
% 7.69/1.48  prep_unflattend:                        0
% 7.69/1.48  smt_new_axioms:                         0
% 7.69/1.48  pred_elim_cands:                        1
% 7.69/1.48  pred_elim:                              0
% 7.69/1.48  pred_elim_cl:                           0
% 7.69/1.48  pred_elim_cycles:                       1
% 7.69/1.48  merged_defs:                            0
% 7.69/1.48  merged_defs_ncl:                        0
% 7.69/1.48  bin_hyper_res:                          0
% 7.69/1.48  prep_cycles:                            3
% 7.69/1.48  pred_elim_time:                         0.
% 7.69/1.48  splitting_time:                         0.
% 7.69/1.48  sem_filter_time:                        0.
% 7.69/1.48  monotx_time:                            0.
% 7.69/1.48  subtype_inf_time:                       0.
% 7.69/1.48  
% 7.69/1.48  ------ Problem properties
% 7.69/1.48  
% 7.69/1.48  clauses:                                9
% 7.69/1.48  conjectures:                            2
% 7.69/1.48  epr:                                    1
% 7.69/1.48  horn:                                   4
% 7.69/1.48  ground:                                 2
% 7.69/1.48  unary:                                  2
% 7.69/1.48  binary:                                 3
% 7.69/1.48  lits:                                   21
% 7.69/1.48  lits_eq:                                6
% 7.69/1.48  fd_pure:                                0
% 7.69/1.48  fd_pseudo:                              0
% 7.69/1.48  fd_cond:                                1
% 7.69/1.48  fd_pseudo_cond:                         3
% 7.69/1.48  ac_symbols:                             0
% 7.69/1.48  
% 7.69/1.48  ------ Propositional Solver
% 7.69/1.48  
% 7.69/1.48  prop_solver_calls:                      30
% 7.69/1.48  prop_fast_solver_calls:                 701
% 7.69/1.48  smt_solver_calls:                       0
% 7.69/1.48  smt_fast_solver_calls:                  0
% 7.69/1.48  prop_num_of_clauses:                    6667
% 7.69/1.48  prop_preprocess_simplified:             10990
% 7.69/1.48  prop_fo_subsumed:                       10
% 7.69/1.48  prop_solver_time:                       0.
% 7.69/1.48  smt_solver_time:                        0.
% 7.69/1.48  smt_fast_solver_time:                   0.
% 7.69/1.48  prop_fast_solver_time:                  0.
% 7.69/1.48  prop_unsat_core_time:                   0.001
% 7.69/1.48  
% 7.69/1.48  ------ QBF
% 7.69/1.48  
% 7.69/1.48  qbf_q_res:                              0
% 7.69/1.48  qbf_num_tautologies:                    0
% 7.69/1.48  qbf_prep_cycles:                        0
% 7.69/1.48  
% 7.69/1.48  ------ BMC1
% 7.69/1.48  
% 7.69/1.48  bmc1_current_bound:                     -1
% 7.69/1.48  bmc1_last_solved_bound:                 -1
% 7.69/1.48  bmc1_unsat_core_size:                   -1
% 7.69/1.48  bmc1_unsat_core_parents_size:           -1
% 7.69/1.48  bmc1_merge_next_fun:                    0
% 7.69/1.48  bmc1_unsat_core_clauses_time:           0.
% 7.69/1.48  
% 7.69/1.48  ------ Instantiation
% 7.69/1.48  
% 7.69/1.48  inst_num_of_clauses:                    1712
% 7.69/1.48  inst_num_in_passive:                    315
% 7.69/1.48  inst_num_in_active:                     761
% 7.69/1.48  inst_num_in_unprocessed:                636
% 7.69/1.48  inst_num_of_loops:                      1090
% 7.69/1.48  inst_num_of_learning_restarts:          0
% 7.69/1.48  inst_num_moves_active_passive:          320
% 7.69/1.48  inst_lit_activity:                      0
% 7.69/1.48  inst_lit_activity_moves:                0
% 7.69/1.48  inst_num_tautologies:                   0
% 7.69/1.48  inst_num_prop_implied:                  0
% 7.69/1.48  inst_num_existing_simplified:           0
% 7.69/1.48  inst_num_eq_res_simplified:             0
% 7.69/1.48  inst_num_child_elim:                    0
% 7.69/1.48  inst_num_of_dismatching_blockings:      4693
% 7.69/1.48  inst_num_of_non_proper_insts:           3252
% 7.69/1.48  inst_num_of_duplicates:                 0
% 7.69/1.48  inst_inst_num_from_inst_to_res:         0
% 7.69/1.48  inst_dismatching_checking_time:         0.
% 7.69/1.48  
% 7.69/1.48  ------ Resolution
% 7.69/1.48  
% 7.69/1.48  res_num_of_clauses:                     0
% 7.69/1.48  res_num_in_passive:                     0
% 7.69/1.48  res_num_in_active:                      0
% 7.69/1.48  res_num_of_loops:                       39
% 7.69/1.48  res_forward_subset_subsumed:            351
% 7.69/1.48  res_backward_subset_subsumed:           0
% 7.69/1.48  res_forward_subsumed:                   0
% 7.69/1.48  res_backward_subsumed:                  0
% 7.69/1.48  res_forward_subsumption_resolution:     0
% 7.69/1.48  res_backward_subsumption_resolution:    0
% 7.69/1.48  res_clause_to_clause_subsumption:       11342
% 7.69/1.48  res_orphan_elimination:                 0
% 7.69/1.48  res_tautology_del:                      698
% 7.69/1.48  res_num_eq_res_simplified:              0
% 7.69/1.48  res_num_sel_changes:                    0
% 7.69/1.48  res_moves_from_active_to_pass:          0
% 7.69/1.48  
% 7.69/1.48  ------ Superposition
% 7.69/1.48  
% 7.69/1.48  sup_time_total:                         0.
% 7.69/1.48  sup_time_generating:                    0.
% 7.69/1.48  sup_time_sim_full:                      0.
% 7.69/1.48  sup_time_sim_immed:                     0.
% 7.69/1.48  
% 7.69/1.48  sup_num_of_clauses:                     659
% 7.69/1.48  sup_num_in_active:                      207
% 7.69/1.48  sup_num_in_passive:                     452
% 7.69/1.48  sup_num_of_loops:                       217
% 7.69/1.48  sup_fw_superposition:                   1702
% 7.69/1.48  sup_bw_superposition:                   1439
% 7.69/1.48  sup_immediate_simplified:               2053
% 7.69/1.48  sup_given_eliminated:                   2
% 7.69/1.48  comparisons_done:                       0
% 7.69/1.48  comparisons_avoided:                    0
% 7.69/1.48  
% 7.69/1.48  ------ Simplifications
% 7.69/1.48  
% 7.69/1.48  
% 7.69/1.48  sim_fw_subset_subsumed:                 432
% 7.69/1.48  sim_bw_subset_subsumed:                 11
% 7.69/1.48  sim_fw_subsumed:                        511
% 7.69/1.48  sim_bw_subsumed:                        20
% 7.69/1.48  sim_fw_subsumption_res:                 15
% 7.69/1.48  sim_bw_subsumption_res:                 0
% 7.69/1.48  sim_tautology_del:                      36
% 7.69/1.48  sim_eq_tautology_del:                   554
% 7.69/1.48  sim_eq_res_simp:                        15
% 7.69/1.48  sim_fw_demodulated:                     672
% 7.69/1.48  sim_bw_demodulated:                     9
% 7.69/1.48  sim_light_normalised:                   948
% 7.69/1.48  sim_joinable_taut:                      0
% 7.69/1.48  sim_joinable_simp:                      0
% 7.69/1.48  sim_ac_normalised:                      0
% 7.69/1.48  sim_smt_subsumption:                    0
% 7.69/1.48  
%------------------------------------------------------------------------------
