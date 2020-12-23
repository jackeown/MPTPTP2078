%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:31:07 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 248 expanded)
%              Number of clauses        :   28 (  38 expanded)
%              Number of leaves         :   14 (  69 expanded)
%              Depth                    :   14
%              Number of atoms          :  212 ( 704 expanded)
%              Number of equality atoms :  144 ( 520 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f20])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK1(X0,X1,X2) != X1
            & sK1(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( sK1(X0,X1,X2) = X1
          | sK1(X0,X1,X2) = X0
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK1(X0,X1,X2) != X1
              & sK1(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( sK1(X0,X1,X2) = X1
            | sK1(X0,X1,X2) = X0
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f23])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f51])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k3_enumset1(X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f38,f52])).

fof(f71,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k3_enumset1(X0,X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f61])).

fof(f72,plain,(
    ! [X4,X0] : r2_hidden(X4,k3_enumset1(X0,X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f71])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f25])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f42,f52])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k3_enumset1(X1,X1,X1,X1,X1) = X0
      | o_0_0_xboole_0 = X0
      | ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f46,f53,f30,f53])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => X0 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f11])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) )
   => ( sK2 != sK4
      & r1_tarski(k2_tarski(sK2,sK3),k1_tarski(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( sK2 != sK4
    & r1_tarski(k2_tarski(sK2,sK3),k1_tarski(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f15,f27])).

fof(f49,plain,(
    r1_tarski(k2_tarski(sK2,sK3),k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f28])).

fof(f67,plain,(
    r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(definition_unfolding,[],[f49,f52,f53])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k3_enumset1(X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f36,f52])).

fof(f75,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k3_enumset1(X0,X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f50,plain,(
    sK2 != sK4 ),
    inference(cnf_transformation,[],[f28])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k3_enumset1(X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f37,f52])).

fof(f73,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k3_enumset1(X4,X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f62])).

fof(f74,plain,(
    ! [X4,X1] : r2_hidden(X4,k3_enumset1(X4,X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f73])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_9,plain,
    ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1219,plain,
    ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
    | k3_enumset1(X1,X1,X1,X1,X1) = X0
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_189,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = X1
    | k3_enumset1(X0,X0,X0,X0,X0) != k3_enumset1(sK4,sK4,sK4,sK4,sK4)
    | k3_enumset1(sK2,sK2,sK2,sK2,sK3) != X1
    | o_0_0_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_16])).

cnf(c_190,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) != k3_enumset1(sK4,sK4,sK4,sK4,sK4)
    | k3_enumset1(X0,X0,X0,X0,X0) = k3_enumset1(sK2,sK2,sK2,sK2,sK3)
    | o_0_0_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_189])).

cnf(c_1327,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_enumset1(sK2,sK2,sK2,sK2,sK3)
    | k3_enumset1(sK2,sK2,sK2,sK2,sK3) = o_0_0_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_190])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1217,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1624,plain,
    ( k3_enumset1(sK2,sK2,sK2,sK2,sK3) = o_0_0_xboole_0
    | sK4 = X0
    | r2_hidden(X0,k3_enumset1(sK2,sK2,sK2,sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1327,c_1217])).

cnf(c_2094,plain,
    ( k3_enumset1(sK2,sK2,sK2,sK2,sK3) = o_0_0_xboole_0
    | sK3 = sK4 ),
    inference(superposition,[status(thm)],[c_1219,c_1624])).

cnf(c_15,negated_conjecture,
    ( sK2 != sK4 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1040,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1305,plain,
    ( sK4 != X0
    | sK2 != X0
    | sK2 = sK4 ),
    inference(instantiation,[status(thm)],[c_1040])).

cnf(c_1334,plain,
    ( sK4 != sK2
    | sK2 = sK4
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1305])).

cnf(c_1039,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1335,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1039])).

cnf(c_10,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1218,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2095,plain,
    ( k3_enumset1(sK2,sK2,sK2,sK2,sK3) = o_0_0_xboole_0
    | sK4 = sK2 ),
    inference(superposition,[status(thm)],[c_1218,c_1624])).

cnf(c_2113,plain,
    ( k3_enumset1(sK2,sK2,sK2,sK2,sK3) = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2094,c_15,c_1334,c_1335,c_2095])).

cnf(c_2118,plain,
    ( r2_hidden(sK3,o_0_0_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2113,c_1219])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_174,plain,
    ( ~ r2_hidden(X0,X1)
    | o_0_0_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_175,plain,
    ( ~ r2_hidden(X0,o_0_0_xboole_0) ),
    inference(unflattening,[status(thm)],[c_174])).

cnf(c_1216,plain,
    ( r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_175])).

cnf(c_2329,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2118,c_1216])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:07:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 1.63/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.00  
% 1.63/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.63/1.00  
% 1.63/1.00  ------  iProver source info
% 1.63/1.00  
% 1.63/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.63/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.63/1.00  git: non_committed_changes: false
% 1.63/1.00  git: last_make_outside_of_git: false
% 1.63/1.00  
% 1.63/1.00  ------ 
% 1.63/1.00  
% 1.63/1.00  ------ Input Options
% 1.63/1.00  
% 1.63/1.00  --out_options                           all
% 1.63/1.00  --tptp_safe_out                         true
% 1.63/1.00  --problem_path                          ""
% 1.63/1.00  --include_path                          ""
% 1.63/1.00  --clausifier                            res/vclausify_rel
% 1.63/1.00  --clausifier_options                    --mode clausify
% 1.63/1.00  --stdin                                 false
% 1.63/1.00  --stats_out                             all
% 1.63/1.00  
% 1.63/1.00  ------ General Options
% 1.63/1.00  
% 1.63/1.00  --fof                                   false
% 1.63/1.00  --time_out_real                         305.
% 1.63/1.00  --time_out_virtual                      -1.
% 1.63/1.00  --symbol_type_check                     false
% 1.63/1.00  --clausify_out                          false
% 1.63/1.00  --sig_cnt_out                           false
% 1.63/1.00  --trig_cnt_out                          false
% 1.63/1.00  --trig_cnt_out_tolerance                1.
% 1.63/1.00  --trig_cnt_out_sk_spl                   false
% 1.63/1.00  --abstr_cl_out                          false
% 1.63/1.00  
% 1.63/1.00  ------ Global Options
% 1.63/1.00  
% 1.63/1.00  --schedule                              default
% 1.63/1.00  --add_important_lit                     false
% 1.63/1.00  --prop_solver_per_cl                    1000
% 1.63/1.00  --min_unsat_core                        false
% 1.63/1.00  --soft_assumptions                      false
% 1.63/1.00  --soft_lemma_size                       3
% 1.63/1.00  --prop_impl_unit_size                   0
% 1.63/1.00  --prop_impl_unit                        []
% 1.63/1.00  --share_sel_clauses                     true
% 1.63/1.00  --reset_solvers                         false
% 1.63/1.00  --bc_imp_inh                            [conj_cone]
% 1.63/1.00  --conj_cone_tolerance                   3.
% 1.63/1.00  --extra_neg_conj                        none
% 1.63/1.00  --large_theory_mode                     true
% 1.63/1.00  --prolific_symb_bound                   200
% 1.63/1.00  --lt_threshold                          2000
% 1.63/1.00  --clause_weak_htbl                      true
% 1.63/1.00  --gc_record_bc_elim                     false
% 1.63/1.00  
% 1.63/1.00  ------ Preprocessing Options
% 1.63/1.00  
% 1.63/1.00  --preprocessing_flag                    true
% 1.63/1.00  --time_out_prep_mult                    0.1
% 1.63/1.00  --splitting_mode                        input
% 1.63/1.00  --splitting_grd                         true
% 1.63/1.00  --splitting_cvd                         false
% 1.63/1.00  --splitting_cvd_svl                     false
% 1.63/1.00  --splitting_nvd                         32
% 1.63/1.00  --sub_typing                            true
% 1.63/1.00  --prep_gs_sim                           true
% 1.63/1.00  --prep_unflatten                        true
% 1.63/1.00  --prep_res_sim                          true
% 1.63/1.00  --prep_upred                            true
% 1.63/1.00  --prep_sem_filter                       exhaustive
% 1.63/1.00  --prep_sem_filter_out                   false
% 1.63/1.00  --pred_elim                             true
% 1.63/1.00  --res_sim_input                         true
% 1.63/1.00  --eq_ax_congr_red                       true
% 1.63/1.00  --pure_diseq_elim                       true
% 1.63/1.00  --brand_transform                       false
% 1.63/1.00  --non_eq_to_eq                          false
% 1.63/1.00  --prep_def_merge                        true
% 1.63/1.00  --prep_def_merge_prop_impl              false
% 1.63/1.00  --prep_def_merge_mbd                    true
% 1.63/1.00  --prep_def_merge_tr_red                 false
% 1.63/1.00  --prep_def_merge_tr_cl                  false
% 1.63/1.00  --smt_preprocessing                     true
% 1.63/1.00  --smt_ac_axioms                         fast
% 1.63/1.00  --preprocessed_out                      false
% 1.63/1.00  --preprocessed_stats                    false
% 1.63/1.00  
% 1.63/1.00  ------ Abstraction refinement Options
% 1.63/1.00  
% 1.63/1.00  --abstr_ref                             []
% 1.63/1.00  --abstr_ref_prep                        false
% 1.63/1.00  --abstr_ref_until_sat                   false
% 1.63/1.00  --abstr_ref_sig_restrict                funpre
% 1.63/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.63/1.00  --abstr_ref_under                       []
% 1.63/1.00  
% 1.63/1.00  ------ SAT Options
% 1.63/1.00  
% 1.63/1.00  --sat_mode                              false
% 1.63/1.00  --sat_fm_restart_options                ""
% 1.63/1.00  --sat_gr_def                            false
% 1.63/1.00  --sat_epr_types                         true
% 1.63/1.00  --sat_non_cyclic_types                  false
% 1.63/1.00  --sat_finite_models                     false
% 1.63/1.00  --sat_fm_lemmas                         false
% 1.63/1.00  --sat_fm_prep                           false
% 1.63/1.00  --sat_fm_uc_incr                        true
% 1.63/1.00  --sat_out_model                         small
% 1.63/1.00  --sat_out_clauses                       false
% 1.63/1.00  
% 1.63/1.00  ------ QBF Options
% 1.63/1.00  
% 1.63/1.00  --qbf_mode                              false
% 1.63/1.00  --qbf_elim_univ                         false
% 1.63/1.00  --qbf_dom_inst                          none
% 1.63/1.00  --qbf_dom_pre_inst                      false
% 1.63/1.00  --qbf_sk_in                             false
% 1.63/1.00  --qbf_pred_elim                         true
% 1.63/1.00  --qbf_split                             512
% 1.63/1.00  
% 1.63/1.00  ------ BMC1 Options
% 1.63/1.00  
% 1.63/1.00  --bmc1_incremental                      false
% 1.63/1.00  --bmc1_axioms                           reachable_all
% 1.63/1.00  --bmc1_min_bound                        0
% 1.63/1.00  --bmc1_max_bound                        -1
% 1.63/1.00  --bmc1_max_bound_default                -1
% 1.63/1.00  --bmc1_symbol_reachability              true
% 1.63/1.00  --bmc1_property_lemmas                  false
% 1.63/1.00  --bmc1_k_induction                      false
% 1.63/1.00  --bmc1_non_equiv_states                 false
% 1.63/1.00  --bmc1_deadlock                         false
% 1.63/1.00  --bmc1_ucm                              false
% 1.63/1.00  --bmc1_add_unsat_core                   none
% 1.63/1.00  --bmc1_unsat_core_children              false
% 1.63/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.63/1.00  --bmc1_out_stat                         full
% 1.63/1.00  --bmc1_ground_init                      false
% 1.63/1.00  --bmc1_pre_inst_next_state              false
% 1.63/1.00  --bmc1_pre_inst_state                   false
% 1.63/1.00  --bmc1_pre_inst_reach_state             false
% 1.63/1.00  --bmc1_out_unsat_core                   false
% 1.63/1.00  --bmc1_aig_witness_out                  false
% 1.63/1.00  --bmc1_verbose                          false
% 1.63/1.00  --bmc1_dump_clauses_tptp                false
% 1.63/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.63/1.00  --bmc1_dump_file                        -
% 1.63/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.63/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.63/1.00  --bmc1_ucm_extend_mode                  1
% 1.63/1.00  --bmc1_ucm_init_mode                    2
% 1.63/1.00  --bmc1_ucm_cone_mode                    none
% 1.63/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.63/1.00  --bmc1_ucm_relax_model                  4
% 1.63/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.63/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.63/1.00  --bmc1_ucm_layered_model                none
% 1.63/1.00  --bmc1_ucm_max_lemma_size               10
% 1.63/1.00  
% 1.63/1.00  ------ AIG Options
% 1.63/1.00  
% 1.63/1.00  --aig_mode                              false
% 1.63/1.00  
% 1.63/1.00  ------ Instantiation Options
% 1.63/1.00  
% 1.63/1.00  --instantiation_flag                    true
% 1.63/1.00  --inst_sos_flag                         false
% 1.63/1.00  --inst_sos_phase                        true
% 1.63/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.63/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.63/1.00  --inst_lit_sel_side                     num_symb
% 1.63/1.00  --inst_solver_per_active                1400
% 1.63/1.00  --inst_solver_calls_frac                1.
% 1.63/1.00  --inst_passive_queue_type               priority_queues
% 1.63/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.63/1.00  --inst_passive_queues_freq              [25;2]
% 1.63/1.00  --inst_dismatching                      true
% 1.63/1.00  --inst_eager_unprocessed_to_passive     true
% 1.63/1.00  --inst_prop_sim_given                   true
% 1.63/1.00  --inst_prop_sim_new                     false
% 1.63/1.00  --inst_subs_new                         false
% 1.63/1.00  --inst_eq_res_simp                      false
% 1.63/1.00  --inst_subs_given                       false
% 1.63/1.00  --inst_orphan_elimination               true
% 1.63/1.00  --inst_learning_loop_flag               true
% 1.63/1.00  --inst_learning_start                   3000
% 1.63/1.00  --inst_learning_factor                  2
% 1.63/1.00  --inst_start_prop_sim_after_learn       3
% 1.63/1.00  --inst_sel_renew                        solver
% 1.63/1.00  --inst_lit_activity_flag                true
% 1.63/1.00  --inst_restr_to_given                   false
% 1.63/1.00  --inst_activity_threshold               500
% 1.63/1.00  --inst_out_proof                        true
% 1.63/1.00  
% 1.63/1.00  ------ Resolution Options
% 1.63/1.00  
% 1.63/1.00  --resolution_flag                       true
% 1.63/1.00  --res_lit_sel                           adaptive
% 1.63/1.00  --res_lit_sel_side                      none
% 1.63/1.00  --res_ordering                          kbo
% 1.63/1.00  --res_to_prop_solver                    active
% 1.63/1.00  --res_prop_simpl_new                    false
% 1.63/1.00  --res_prop_simpl_given                  true
% 1.63/1.00  --res_passive_queue_type                priority_queues
% 1.63/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.63/1.00  --res_passive_queues_freq               [15;5]
% 1.63/1.00  --res_forward_subs                      full
% 1.63/1.00  --res_backward_subs                     full
% 1.63/1.00  --res_forward_subs_resolution           true
% 1.63/1.00  --res_backward_subs_resolution          true
% 1.63/1.00  --res_orphan_elimination                true
% 1.63/1.00  --res_time_limit                        2.
% 1.63/1.00  --res_out_proof                         true
% 1.63/1.00  
% 1.63/1.00  ------ Superposition Options
% 1.63/1.00  
% 1.63/1.00  --superposition_flag                    true
% 1.63/1.00  --sup_passive_queue_type                priority_queues
% 1.63/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.63/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.63/1.00  --demod_completeness_check              fast
% 1.63/1.00  --demod_use_ground                      true
% 1.63/1.00  --sup_to_prop_solver                    passive
% 1.63/1.00  --sup_prop_simpl_new                    true
% 1.63/1.00  --sup_prop_simpl_given                  true
% 1.63/1.00  --sup_fun_splitting                     false
% 1.63/1.00  --sup_smt_interval                      50000
% 1.63/1.00  
% 1.63/1.00  ------ Superposition Simplification Setup
% 1.63/1.00  
% 1.63/1.00  --sup_indices_passive                   []
% 1.63/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.63/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.63/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.63/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.63/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.63/1.00  --sup_full_bw                           [BwDemod]
% 1.63/1.00  --sup_immed_triv                        [TrivRules]
% 1.63/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.63/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.63/1.00  --sup_immed_bw_main                     []
% 1.63/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.63/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.63/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.63/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.63/1.00  
% 1.63/1.00  ------ Combination Options
% 1.63/1.00  
% 1.63/1.00  --comb_res_mult                         3
% 1.63/1.00  --comb_sup_mult                         2
% 1.63/1.00  --comb_inst_mult                        10
% 1.63/1.00  
% 1.63/1.00  ------ Debug Options
% 1.63/1.00  
% 1.63/1.00  --dbg_backtrace                         false
% 1.63/1.00  --dbg_dump_prop_clauses                 false
% 1.63/1.00  --dbg_dump_prop_clauses_file            -
% 1.63/1.00  --dbg_out_stat                          false
% 1.63/1.00  ------ Parsing...
% 1.63/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.63/1.00  
% 1.63/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 1.63/1.00  
% 1.63/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.63/1.00  
% 1.63/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.63/1.00  ------ Proving...
% 1.63/1.00  ------ Problem Properties 
% 1.63/1.00  
% 1.63/1.00  
% 1.63/1.00  clauses                                 13
% 1.63/1.00  conjectures                             1
% 1.63/1.00  EPR                                     2
% 1.63/1.00  Horn                                    9
% 1.63/1.00  unary                                   5
% 1.63/1.00  binary                                  1
% 1.63/1.00  lits                                    29
% 1.63/1.00  lits eq                                 18
% 1.63/1.00  fd_pure                                 0
% 1.63/1.00  fd_pseudo                               0
% 1.63/1.00  fd_cond                                 0
% 1.63/1.00  fd_pseudo_cond                          5
% 1.63/1.00  AC symbols                              0
% 1.63/1.00  
% 1.63/1.00  ------ Schedule dynamic 5 is on 
% 1.63/1.00  
% 1.63/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.63/1.00  
% 1.63/1.00  
% 1.63/1.00  ------ 
% 1.63/1.00  Current options:
% 1.63/1.00  ------ 
% 1.63/1.00  
% 1.63/1.00  ------ Input Options
% 1.63/1.00  
% 1.63/1.00  --out_options                           all
% 1.63/1.00  --tptp_safe_out                         true
% 1.63/1.00  --problem_path                          ""
% 1.63/1.00  --include_path                          ""
% 1.63/1.00  --clausifier                            res/vclausify_rel
% 1.63/1.00  --clausifier_options                    --mode clausify
% 1.63/1.00  --stdin                                 false
% 1.63/1.00  --stats_out                             all
% 1.63/1.00  
% 1.63/1.00  ------ General Options
% 1.63/1.00  
% 1.63/1.00  --fof                                   false
% 1.63/1.00  --time_out_real                         305.
% 1.63/1.00  --time_out_virtual                      -1.
% 1.63/1.00  --symbol_type_check                     false
% 1.63/1.00  --clausify_out                          false
% 1.63/1.00  --sig_cnt_out                           false
% 1.63/1.00  --trig_cnt_out                          false
% 1.63/1.00  --trig_cnt_out_tolerance                1.
% 1.63/1.00  --trig_cnt_out_sk_spl                   false
% 1.63/1.00  --abstr_cl_out                          false
% 1.63/1.00  
% 1.63/1.00  ------ Global Options
% 1.63/1.00  
% 1.63/1.00  --schedule                              default
% 1.63/1.00  --add_important_lit                     false
% 1.63/1.00  --prop_solver_per_cl                    1000
% 1.63/1.00  --min_unsat_core                        false
% 1.63/1.00  --soft_assumptions                      false
% 1.63/1.00  --soft_lemma_size                       3
% 1.63/1.00  --prop_impl_unit_size                   0
% 1.63/1.00  --prop_impl_unit                        []
% 1.63/1.00  --share_sel_clauses                     true
% 1.63/1.00  --reset_solvers                         false
% 1.63/1.00  --bc_imp_inh                            [conj_cone]
% 1.63/1.00  --conj_cone_tolerance                   3.
% 1.63/1.00  --extra_neg_conj                        none
% 1.63/1.00  --large_theory_mode                     true
% 1.63/1.00  --prolific_symb_bound                   200
% 1.63/1.00  --lt_threshold                          2000
% 1.63/1.00  --clause_weak_htbl                      true
% 1.63/1.00  --gc_record_bc_elim                     false
% 1.63/1.00  
% 1.63/1.00  ------ Preprocessing Options
% 1.63/1.00  
% 1.63/1.00  --preprocessing_flag                    true
% 1.63/1.00  --time_out_prep_mult                    0.1
% 1.63/1.00  --splitting_mode                        input
% 1.63/1.00  --splitting_grd                         true
% 1.63/1.00  --splitting_cvd                         false
% 1.63/1.00  --splitting_cvd_svl                     false
% 1.63/1.00  --splitting_nvd                         32
% 1.63/1.00  --sub_typing                            true
% 1.63/1.00  --prep_gs_sim                           true
% 1.63/1.00  --prep_unflatten                        true
% 1.63/1.00  --prep_res_sim                          true
% 1.63/1.00  --prep_upred                            true
% 1.63/1.00  --prep_sem_filter                       exhaustive
% 1.63/1.00  --prep_sem_filter_out                   false
% 1.63/1.00  --pred_elim                             true
% 1.63/1.00  --res_sim_input                         true
% 1.63/1.00  --eq_ax_congr_red                       true
% 1.63/1.00  --pure_diseq_elim                       true
% 1.63/1.00  --brand_transform                       false
% 1.63/1.00  --non_eq_to_eq                          false
% 1.63/1.00  --prep_def_merge                        true
% 1.63/1.00  --prep_def_merge_prop_impl              false
% 1.63/1.00  --prep_def_merge_mbd                    true
% 1.63/1.00  --prep_def_merge_tr_red                 false
% 1.63/1.00  --prep_def_merge_tr_cl                  false
% 1.63/1.00  --smt_preprocessing                     true
% 1.63/1.00  --smt_ac_axioms                         fast
% 1.63/1.00  --preprocessed_out                      false
% 1.63/1.00  --preprocessed_stats                    false
% 1.63/1.00  
% 1.63/1.00  ------ Abstraction refinement Options
% 1.63/1.00  
% 1.63/1.00  --abstr_ref                             []
% 1.63/1.00  --abstr_ref_prep                        false
% 1.63/1.00  --abstr_ref_until_sat                   false
% 1.63/1.00  --abstr_ref_sig_restrict                funpre
% 1.63/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.63/1.00  --abstr_ref_under                       []
% 1.63/1.00  
% 1.63/1.00  ------ SAT Options
% 1.63/1.00  
% 1.63/1.00  --sat_mode                              false
% 1.63/1.00  --sat_fm_restart_options                ""
% 1.63/1.00  --sat_gr_def                            false
% 1.63/1.00  --sat_epr_types                         true
% 1.63/1.00  --sat_non_cyclic_types                  false
% 1.63/1.00  --sat_finite_models                     false
% 1.63/1.00  --sat_fm_lemmas                         false
% 1.63/1.00  --sat_fm_prep                           false
% 1.63/1.00  --sat_fm_uc_incr                        true
% 1.63/1.00  --sat_out_model                         small
% 1.63/1.00  --sat_out_clauses                       false
% 1.63/1.00  
% 1.63/1.00  ------ QBF Options
% 1.63/1.00  
% 1.63/1.00  --qbf_mode                              false
% 1.63/1.00  --qbf_elim_univ                         false
% 1.63/1.00  --qbf_dom_inst                          none
% 1.63/1.00  --qbf_dom_pre_inst                      false
% 1.63/1.00  --qbf_sk_in                             false
% 1.63/1.00  --qbf_pred_elim                         true
% 1.63/1.00  --qbf_split                             512
% 1.63/1.00  
% 1.63/1.00  ------ BMC1 Options
% 1.63/1.00  
% 1.63/1.00  --bmc1_incremental                      false
% 1.63/1.00  --bmc1_axioms                           reachable_all
% 1.63/1.00  --bmc1_min_bound                        0
% 1.63/1.00  --bmc1_max_bound                        -1
% 1.63/1.00  --bmc1_max_bound_default                -1
% 1.63/1.00  --bmc1_symbol_reachability              true
% 1.63/1.00  --bmc1_property_lemmas                  false
% 1.63/1.00  --bmc1_k_induction                      false
% 1.63/1.00  --bmc1_non_equiv_states                 false
% 1.63/1.00  --bmc1_deadlock                         false
% 1.63/1.00  --bmc1_ucm                              false
% 1.63/1.00  --bmc1_add_unsat_core                   none
% 1.63/1.00  --bmc1_unsat_core_children              false
% 1.63/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.63/1.00  --bmc1_out_stat                         full
% 1.63/1.00  --bmc1_ground_init                      false
% 1.63/1.00  --bmc1_pre_inst_next_state              false
% 1.63/1.00  --bmc1_pre_inst_state                   false
% 1.63/1.00  --bmc1_pre_inst_reach_state             false
% 1.63/1.00  --bmc1_out_unsat_core                   false
% 1.63/1.00  --bmc1_aig_witness_out                  false
% 1.63/1.00  --bmc1_verbose                          false
% 1.63/1.00  --bmc1_dump_clauses_tptp                false
% 1.63/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.63/1.00  --bmc1_dump_file                        -
% 1.63/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.63/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.63/1.00  --bmc1_ucm_extend_mode                  1
% 1.63/1.00  --bmc1_ucm_init_mode                    2
% 1.63/1.00  --bmc1_ucm_cone_mode                    none
% 1.63/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.63/1.00  --bmc1_ucm_relax_model                  4
% 1.63/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.63/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.63/1.00  --bmc1_ucm_layered_model                none
% 1.63/1.00  --bmc1_ucm_max_lemma_size               10
% 1.63/1.00  
% 1.63/1.00  ------ AIG Options
% 1.63/1.00  
% 1.63/1.00  --aig_mode                              false
% 1.63/1.00  
% 1.63/1.00  ------ Instantiation Options
% 1.63/1.00  
% 1.63/1.00  --instantiation_flag                    true
% 1.63/1.00  --inst_sos_flag                         false
% 1.63/1.00  --inst_sos_phase                        true
% 1.63/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.63/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.63/1.00  --inst_lit_sel_side                     none
% 1.63/1.00  --inst_solver_per_active                1400
% 1.63/1.00  --inst_solver_calls_frac                1.
% 1.63/1.00  --inst_passive_queue_type               priority_queues
% 1.63/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.63/1.00  --inst_passive_queues_freq              [25;2]
% 1.63/1.00  --inst_dismatching                      true
% 1.63/1.00  --inst_eager_unprocessed_to_passive     true
% 1.63/1.00  --inst_prop_sim_given                   true
% 1.63/1.00  --inst_prop_sim_new                     false
% 1.63/1.00  --inst_subs_new                         false
% 1.63/1.00  --inst_eq_res_simp                      false
% 1.63/1.00  --inst_subs_given                       false
% 1.63/1.00  --inst_orphan_elimination               true
% 1.63/1.00  --inst_learning_loop_flag               true
% 1.63/1.00  --inst_learning_start                   3000
% 1.63/1.00  --inst_learning_factor                  2
% 1.63/1.00  --inst_start_prop_sim_after_learn       3
% 1.63/1.00  --inst_sel_renew                        solver
% 1.63/1.00  --inst_lit_activity_flag                true
% 1.63/1.00  --inst_restr_to_given                   false
% 1.63/1.00  --inst_activity_threshold               500
% 1.63/1.00  --inst_out_proof                        true
% 1.63/1.00  
% 1.63/1.00  ------ Resolution Options
% 1.63/1.00  
% 1.63/1.00  --resolution_flag                       false
% 1.63/1.00  --res_lit_sel                           adaptive
% 1.63/1.00  --res_lit_sel_side                      none
% 1.63/1.00  --res_ordering                          kbo
% 1.63/1.00  --res_to_prop_solver                    active
% 1.63/1.00  --res_prop_simpl_new                    false
% 1.63/1.00  --res_prop_simpl_given                  true
% 1.63/1.00  --res_passive_queue_type                priority_queues
% 1.63/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.63/1.00  --res_passive_queues_freq               [15;5]
% 1.63/1.00  --res_forward_subs                      full
% 1.63/1.00  --res_backward_subs                     full
% 1.63/1.00  --res_forward_subs_resolution           true
% 1.63/1.00  --res_backward_subs_resolution          true
% 1.63/1.00  --res_orphan_elimination                true
% 1.63/1.00  --res_time_limit                        2.
% 1.63/1.00  --res_out_proof                         true
% 1.63/1.00  
% 1.63/1.00  ------ Superposition Options
% 1.63/1.00  
% 1.63/1.00  --superposition_flag                    true
% 1.63/1.00  --sup_passive_queue_type                priority_queues
% 1.63/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.63/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.63/1.00  --demod_completeness_check              fast
% 1.63/1.00  --demod_use_ground                      true
% 1.63/1.00  --sup_to_prop_solver                    passive
% 1.63/1.00  --sup_prop_simpl_new                    true
% 1.63/1.00  --sup_prop_simpl_given                  true
% 1.63/1.00  --sup_fun_splitting                     false
% 1.63/1.00  --sup_smt_interval                      50000
% 1.63/1.00  
% 1.63/1.00  ------ Superposition Simplification Setup
% 1.63/1.00  
% 1.63/1.00  --sup_indices_passive                   []
% 1.63/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.63/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.63/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.63/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.63/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.63/1.00  --sup_full_bw                           [BwDemod]
% 1.63/1.00  --sup_immed_triv                        [TrivRules]
% 1.63/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.63/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.63/1.00  --sup_immed_bw_main                     []
% 1.63/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.63/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.63/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.63/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.63/1.00  
% 1.63/1.00  ------ Combination Options
% 1.63/1.00  
% 1.63/1.00  --comb_res_mult                         3
% 1.63/1.00  --comb_sup_mult                         2
% 1.63/1.00  --comb_inst_mult                        10
% 1.63/1.00  
% 1.63/1.00  ------ Debug Options
% 1.63/1.00  
% 1.63/1.00  --dbg_backtrace                         false
% 1.63/1.00  --dbg_dump_prop_clauses                 false
% 1.63/1.00  --dbg_dump_prop_clauses_file            -
% 1.63/1.00  --dbg_out_stat                          false
% 1.63/1.00  
% 1.63/1.00  
% 1.63/1.00  
% 1.63/1.00  
% 1.63/1.00  ------ Proving...
% 1.63/1.00  
% 1.63/1.00  
% 1.63/1.00  % SZS status Theorem for theBenchmark.p
% 1.63/1.00  
% 1.63/1.00   Resolution empty clause
% 1.63/1.00  
% 1.63/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.63/1.00  
% 1.63/1.00  fof(f5,axiom,(
% 1.63/1.00    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.63/1.00  
% 1.63/1.00  fof(f20,plain,(
% 1.63/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.63/1.00    inference(nnf_transformation,[],[f5])).
% 1.63/1.00  
% 1.63/1.00  fof(f21,plain,(
% 1.63/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.63/1.00    inference(flattening,[],[f20])).
% 1.63/1.00  
% 1.63/1.00  fof(f22,plain,(
% 1.63/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.63/1.00    inference(rectify,[],[f21])).
% 1.63/1.00  
% 1.63/1.00  fof(f23,plain,(
% 1.63/1.00    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 1.63/1.00    introduced(choice_axiom,[])).
% 1.63/1.00  
% 1.63/1.00  fof(f24,plain,(
% 1.63/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.63/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f23])).
% 1.63/1.00  
% 1.63/1.00  fof(f38,plain,(
% 1.63/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.63/1.00    inference(cnf_transformation,[],[f24])).
% 1.63/1.00  
% 1.63/1.00  fof(f7,axiom,(
% 1.63/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.63/1.00  
% 1.63/1.00  fof(f43,plain,(
% 1.63/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.63/1.00    inference(cnf_transformation,[],[f7])).
% 1.63/1.00  
% 1.63/1.00  fof(f8,axiom,(
% 1.63/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.63/1.00  
% 1.63/1.00  fof(f44,plain,(
% 1.63/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.63/1.00    inference(cnf_transformation,[],[f8])).
% 1.63/1.00  
% 1.63/1.00  fof(f9,axiom,(
% 1.63/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.63/1.00  
% 1.63/1.00  fof(f45,plain,(
% 1.63/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.63/1.00    inference(cnf_transformation,[],[f9])).
% 1.63/1.00  
% 1.63/1.00  fof(f51,plain,(
% 1.63/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.63/1.00    inference(definition_unfolding,[],[f44,f45])).
% 1.63/1.00  
% 1.63/1.00  fof(f52,plain,(
% 1.63/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.63/1.00    inference(definition_unfolding,[],[f43,f51])).
% 1.63/1.00  
% 1.63/1.00  fof(f61,plain,(
% 1.63/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k3_enumset1(X0,X0,X0,X0,X1) != X2) )),
% 1.63/1.00    inference(definition_unfolding,[],[f38,f52])).
% 1.63/1.00  
% 1.63/1.00  fof(f71,plain,(
% 1.63/1.00    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k3_enumset1(X0,X0,X0,X0,X4) != X2) )),
% 1.63/1.00    inference(equality_resolution,[],[f61])).
% 1.63/1.00  
% 1.63/1.00  fof(f72,plain,(
% 1.63/1.00    ( ! [X4,X0] : (r2_hidden(X4,k3_enumset1(X0,X0,X0,X0,X4))) )),
% 1.63/1.00    inference(equality_resolution,[],[f71])).
% 1.63/1.00  
% 1.63/1.00  fof(f10,axiom,(
% 1.63/1.00    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.63/1.00  
% 1.63/1.00  fof(f25,plain,(
% 1.63/1.00    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.63/1.00    inference(nnf_transformation,[],[f10])).
% 1.63/1.00  
% 1.63/1.00  fof(f26,plain,(
% 1.63/1.00    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.63/1.00    inference(flattening,[],[f25])).
% 1.63/1.00  
% 1.63/1.00  fof(f46,plain,(
% 1.63/1.00    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.63/1.00    inference(cnf_transformation,[],[f26])).
% 1.63/1.00  
% 1.63/1.00  fof(f2,axiom,(
% 1.63/1.00    k1_xboole_0 = o_0_0_xboole_0),
% 1.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.63/1.00  
% 1.63/1.00  fof(f30,plain,(
% 1.63/1.00    k1_xboole_0 = o_0_0_xboole_0),
% 1.63/1.00    inference(cnf_transformation,[],[f2])).
% 1.63/1.00  
% 1.63/1.00  fof(f6,axiom,(
% 1.63/1.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.63/1.00  
% 1.63/1.00  fof(f42,plain,(
% 1.63/1.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.63/1.00    inference(cnf_transformation,[],[f6])).
% 1.63/1.00  
% 1.63/1.00  fof(f53,plain,(
% 1.63/1.00    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.63/1.00    inference(definition_unfolding,[],[f42,f52])).
% 1.63/1.00  
% 1.63/1.00  fof(f66,plain,(
% 1.63/1.00    ( ! [X0,X1] : (k3_enumset1(X1,X1,X1,X1,X1) = X0 | o_0_0_xboole_0 = X0 | ~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))) )),
% 1.63/1.00    inference(definition_unfolding,[],[f46,f53,f30,f53])).
% 1.63/1.00  
% 1.63/1.00  fof(f11,conjecture,(
% 1.63/1.00    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 1.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.63/1.00  
% 1.63/1.00  fof(f12,negated_conjecture,(
% 1.63/1.00    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 1.63/1.00    inference(negated_conjecture,[],[f11])).
% 1.63/1.00  
% 1.63/1.00  fof(f15,plain,(
% 1.63/1.00    ? [X0,X1,X2] : (X0 != X2 & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 1.63/1.00    inference(ennf_transformation,[],[f12])).
% 1.63/1.00  
% 1.63/1.00  fof(f27,plain,(
% 1.63/1.00    ? [X0,X1,X2] : (X0 != X2 & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))) => (sK2 != sK4 & r1_tarski(k2_tarski(sK2,sK3),k1_tarski(sK4)))),
% 1.63/1.00    introduced(choice_axiom,[])).
% 1.63/1.00  
% 1.63/1.00  fof(f28,plain,(
% 1.63/1.00    sK2 != sK4 & r1_tarski(k2_tarski(sK2,sK3),k1_tarski(sK4))),
% 1.63/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f15,f27])).
% 1.63/1.00  
% 1.63/1.00  fof(f49,plain,(
% 1.63/1.00    r1_tarski(k2_tarski(sK2,sK3),k1_tarski(sK4))),
% 1.63/1.00    inference(cnf_transformation,[],[f28])).
% 1.63/1.00  
% 1.63/1.00  fof(f67,plain,(
% 1.63/1.00    r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4))),
% 1.63/1.00    inference(definition_unfolding,[],[f49,f52,f53])).
% 1.63/1.00  
% 1.63/1.00  fof(f36,plain,(
% 1.63/1.00    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 1.63/1.00    inference(cnf_transformation,[],[f24])).
% 1.63/1.00  
% 1.63/1.00  fof(f63,plain,(
% 1.63/1.00    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k3_enumset1(X0,X0,X0,X0,X1) != X2) )),
% 1.63/1.00    inference(definition_unfolding,[],[f36,f52])).
% 1.63/1.00  
% 1.63/1.00  fof(f75,plain,(
% 1.63/1.00    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.63/1.00    inference(equality_resolution,[],[f63])).
% 1.63/1.00  
% 1.63/1.00  fof(f50,plain,(
% 1.63/1.00    sK2 != sK4),
% 1.63/1.00    inference(cnf_transformation,[],[f28])).
% 1.63/1.00  
% 1.63/1.00  fof(f37,plain,(
% 1.63/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.63/1.00    inference(cnf_transformation,[],[f24])).
% 1.63/1.00  
% 1.63/1.00  fof(f62,plain,(
% 1.63/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k3_enumset1(X0,X0,X0,X0,X1) != X2) )),
% 1.63/1.00    inference(definition_unfolding,[],[f37,f52])).
% 1.63/1.00  
% 1.63/1.00  fof(f73,plain,(
% 1.63/1.00    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k3_enumset1(X4,X4,X4,X4,X1) != X2) )),
% 1.63/1.00    inference(equality_resolution,[],[f62])).
% 1.63/1.00  
% 1.63/1.00  fof(f74,plain,(
% 1.63/1.00    ( ! [X4,X1] : (r2_hidden(X4,k3_enumset1(X4,X4,X4,X4,X1))) )),
% 1.63/1.00    inference(equality_resolution,[],[f73])).
% 1.63/1.00  
% 1.63/1.00  fof(f1,axiom,(
% 1.63/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.63/1.00  
% 1.63/1.00  fof(f13,plain,(
% 1.63/1.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 1.63/1.00    inference(unused_predicate_definition_removal,[],[f1])).
% 1.63/1.00  
% 1.63/1.00  fof(f14,plain,(
% 1.63/1.00    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 1.63/1.00    inference(ennf_transformation,[],[f13])).
% 1.63/1.00  
% 1.63/1.00  fof(f29,plain,(
% 1.63/1.00    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.63/1.00    inference(cnf_transformation,[],[f14])).
% 1.63/1.00  
% 1.63/1.00  fof(f3,axiom,(
% 1.63/1.00    v1_xboole_0(o_0_0_xboole_0)),
% 1.63/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.63/1.00  
% 1.63/1.00  fof(f31,plain,(
% 1.63/1.00    v1_xboole_0(o_0_0_xboole_0)),
% 1.63/1.00    inference(cnf_transformation,[],[f3])).
% 1.63/1.00  
% 1.63/1.00  cnf(c_9,plain,
% 1.63/1.00      ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X0)) ),
% 1.63/1.00      inference(cnf_transformation,[],[f72]) ).
% 1.63/1.00  
% 1.63/1.00  cnf(c_1219,plain,
% 1.63/1.00      ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X0)) = iProver_top ),
% 1.63/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.63/1.00  
% 1.63/1.00  cnf(c_14,plain,
% 1.63/1.00      ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
% 1.63/1.00      | k3_enumset1(X1,X1,X1,X1,X1) = X0
% 1.63/1.00      | o_0_0_xboole_0 = X0 ),
% 1.63/1.00      inference(cnf_transformation,[],[f66]) ).
% 1.63/1.00  
% 1.63/1.00  cnf(c_16,negated_conjecture,
% 1.63/1.00      ( r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
% 1.63/1.00      inference(cnf_transformation,[],[f67]) ).
% 1.63/1.00  
% 1.63/1.00  cnf(c_189,plain,
% 1.63/1.00      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
% 1.63/1.00      | k3_enumset1(X0,X0,X0,X0,X0) != k3_enumset1(sK4,sK4,sK4,sK4,sK4)
% 1.63/1.00      | k3_enumset1(sK2,sK2,sK2,sK2,sK3) != X1
% 1.63/1.00      | o_0_0_xboole_0 = X1 ),
% 1.63/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_16]) ).
% 1.63/1.00  
% 1.63/1.00  cnf(c_190,plain,
% 1.63/1.00      ( k3_enumset1(X0,X0,X0,X0,X0) != k3_enumset1(sK4,sK4,sK4,sK4,sK4)
% 1.63/1.00      | k3_enumset1(X0,X0,X0,X0,X0) = k3_enumset1(sK2,sK2,sK2,sK2,sK3)
% 1.63/1.00      | o_0_0_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK3) ),
% 1.63/1.00      inference(unflattening,[status(thm)],[c_189]) ).
% 1.63/1.00  
% 1.63/1.00  cnf(c_1327,plain,
% 1.63/1.00      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_enumset1(sK2,sK2,sK2,sK2,sK3)
% 1.63/1.00      | k3_enumset1(sK2,sK2,sK2,sK2,sK3) = o_0_0_xboole_0 ),
% 1.63/1.00      inference(equality_resolution,[status(thm)],[c_190]) ).
% 1.63/1.00  
% 1.63/1.00  cnf(c_11,plain,
% 1.63/1.00      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 1.63/1.00      inference(cnf_transformation,[],[f75]) ).
% 1.63/1.00  
% 1.63/1.00  cnf(c_1217,plain,
% 1.63/1.00      ( X0 = X1
% 1.63/1.00      | X0 = X2
% 1.63/1.00      | r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X2)) != iProver_top ),
% 1.63/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.63/1.00  
% 1.63/1.00  cnf(c_1624,plain,
% 1.63/1.00      ( k3_enumset1(sK2,sK2,sK2,sK2,sK3) = o_0_0_xboole_0
% 1.63/1.00      | sK4 = X0
% 1.63/1.00      | r2_hidden(X0,k3_enumset1(sK2,sK2,sK2,sK2,sK3)) != iProver_top ),
% 1.63/1.00      inference(superposition,[status(thm)],[c_1327,c_1217]) ).
% 1.63/1.00  
% 1.63/1.00  cnf(c_2094,plain,
% 1.63/1.00      ( k3_enumset1(sK2,sK2,sK2,sK2,sK3) = o_0_0_xboole_0 | sK3 = sK4 ),
% 1.63/1.00      inference(superposition,[status(thm)],[c_1219,c_1624]) ).
% 1.63/1.00  
% 1.63/1.00  cnf(c_15,negated_conjecture,
% 1.63/1.00      ( sK2 != sK4 ),
% 1.63/1.00      inference(cnf_transformation,[],[f50]) ).
% 1.63/1.00  
% 1.63/1.00  cnf(c_1040,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.63/1.00  
% 1.63/1.00  cnf(c_1305,plain,
% 1.63/1.00      ( sK4 != X0 | sK2 != X0 | sK2 = sK4 ),
% 1.63/1.00      inference(instantiation,[status(thm)],[c_1040]) ).
% 1.63/1.00  
% 1.63/1.00  cnf(c_1334,plain,
% 1.63/1.00      ( sK4 != sK2 | sK2 = sK4 | sK2 != sK2 ),
% 1.63/1.00      inference(instantiation,[status(thm)],[c_1305]) ).
% 1.63/1.00  
% 1.63/1.00  cnf(c_1039,plain,( X0 = X0 ),theory(equality) ).
% 1.63/1.00  
% 1.63/1.00  cnf(c_1335,plain,
% 1.63/1.00      ( sK2 = sK2 ),
% 1.63/1.00      inference(instantiation,[status(thm)],[c_1039]) ).
% 1.63/1.00  
% 1.63/1.00  cnf(c_10,plain,
% 1.63/1.00      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X1)) ),
% 1.63/1.00      inference(cnf_transformation,[],[f74]) ).
% 1.63/1.00  
% 1.63/1.00  cnf(c_1218,plain,
% 1.63/1.00      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X1)) = iProver_top ),
% 1.63/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.63/1.00  
% 1.63/1.00  cnf(c_2095,plain,
% 1.63/1.00      ( k3_enumset1(sK2,sK2,sK2,sK2,sK3) = o_0_0_xboole_0 | sK4 = sK2 ),
% 1.63/1.00      inference(superposition,[status(thm)],[c_1218,c_1624]) ).
% 1.63/1.00  
% 1.63/1.00  cnf(c_2113,plain,
% 1.63/1.00      ( k3_enumset1(sK2,sK2,sK2,sK2,sK3) = o_0_0_xboole_0 ),
% 1.63/1.00      inference(global_propositional_subsumption,
% 1.63/1.00                [status(thm)],
% 1.63/1.00                [c_2094,c_15,c_1334,c_1335,c_2095]) ).
% 1.63/1.00  
% 1.63/1.00  cnf(c_2118,plain,
% 1.63/1.00      ( r2_hidden(sK3,o_0_0_xboole_0) = iProver_top ),
% 1.63/1.00      inference(superposition,[status(thm)],[c_2113,c_1219]) ).
% 1.63/1.00  
% 1.63/1.00  cnf(c_0,plain,
% 1.63/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 1.63/1.00      inference(cnf_transformation,[],[f29]) ).
% 1.63/1.00  
% 1.63/1.00  cnf(c_1,plain,
% 1.63/1.00      ( v1_xboole_0(o_0_0_xboole_0) ),
% 1.63/1.00      inference(cnf_transformation,[],[f31]) ).
% 1.63/1.00  
% 1.63/1.00  cnf(c_174,plain,
% 1.63/1.00      ( ~ r2_hidden(X0,X1) | o_0_0_xboole_0 != X1 ),
% 1.63/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 1.63/1.00  
% 1.63/1.00  cnf(c_175,plain,
% 1.63/1.00      ( ~ r2_hidden(X0,o_0_0_xboole_0) ),
% 1.63/1.00      inference(unflattening,[status(thm)],[c_174]) ).
% 1.63/1.00  
% 1.63/1.00  cnf(c_1216,plain,
% 1.63/1.00      ( r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
% 1.63/1.00      inference(predicate_to_equality,[status(thm)],[c_175]) ).
% 1.63/1.00  
% 1.63/1.00  cnf(c_2329,plain,
% 1.63/1.00      ( $false ),
% 1.63/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_2118,c_1216]) ).
% 1.63/1.00  
% 1.63/1.00  
% 1.63/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.63/1.00  
% 1.63/1.00  ------                               Statistics
% 1.63/1.00  
% 1.63/1.00  ------ General
% 1.63/1.00  
% 1.63/1.00  abstr_ref_over_cycles:                  0
% 1.63/1.00  abstr_ref_under_cycles:                 0
% 1.63/1.00  gc_basic_clause_elim:                   0
% 1.63/1.00  forced_gc_time:                         0
% 1.63/1.00  parsing_time:                           0.009
% 1.63/1.00  unif_index_cands_time:                  0.
% 1.63/1.00  unif_index_add_time:                    0.
% 1.63/1.00  orderings_time:                         0.
% 1.63/1.00  out_proof_time:                         0.009
% 1.63/1.00  total_time:                             0.101
% 1.63/1.00  num_of_symbols:                         41
% 1.63/1.00  num_of_terms:                           2099
% 1.63/1.00  
% 1.63/1.00  ------ Preprocessing
% 1.63/1.00  
% 1.63/1.00  num_of_splits:                          0
% 1.63/1.00  num_of_split_atoms:                     0
% 1.63/1.00  num_of_reused_defs:                     0
% 1.63/1.00  num_eq_ax_congr_red:                    15
% 1.63/1.00  num_of_sem_filtered_clauses:            1
% 1.63/1.00  num_of_subtypes:                        0
% 1.63/1.00  monotx_restored_types:                  0
% 1.63/1.00  sat_num_of_epr_types:                   0
% 1.63/1.00  sat_num_of_non_cyclic_types:            0
% 1.63/1.00  sat_guarded_non_collapsed_types:        0
% 1.63/1.00  num_pure_diseq_elim:                    0
% 1.63/1.00  simp_replaced_by:                       0
% 1.63/1.00  res_preprocessed:                       65
% 1.63/1.00  prep_upred:                             0
% 1.63/1.00  prep_unflattend:                        70
% 1.63/1.00  smt_new_axioms:                         0
% 1.63/1.00  pred_elim_cands:                        1
% 1.63/1.00  pred_elim:                              2
% 1.63/1.00  pred_elim_cl:                           4
% 1.63/1.00  pred_elim_cycles:                       4
% 1.63/1.00  merged_defs:                            0
% 1.63/1.00  merged_defs_ncl:                        0
% 1.63/1.00  bin_hyper_res:                          0
% 1.63/1.00  prep_cycles:                            4
% 1.63/1.00  pred_elim_time:                         0.01
% 1.63/1.00  splitting_time:                         0.
% 1.63/1.00  sem_filter_time:                        0.
% 1.63/1.00  monotx_time:                            0.
% 1.63/1.00  subtype_inf_time:                       0.
% 1.63/1.00  
% 1.63/1.00  ------ Problem properties
% 1.63/1.00  
% 1.63/1.00  clauses:                                13
% 1.63/1.00  conjectures:                            1
% 1.63/1.00  epr:                                    2
% 1.63/1.00  horn:                                   9
% 1.63/1.00  ground:                                 1
% 1.63/1.00  unary:                                  5
% 1.63/1.00  binary:                                 1
% 1.63/1.00  lits:                                   29
% 1.63/1.00  lits_eq:                                18
% 1.63/1.00  fd_pure:                                0
% 1.63/1.00  fd_pseudo:                              0
% 1.63/1.00  fd_cond:                                0
% 1.63/1.00  fd_pseudo_cond:                         5
% 1.63/1.00  ac_symbols:                             0
% 1.63/1.00  
% 1.63/1.00  ------ Propositional Solver
% 1.63/1.00  
% 1.63/1.00  prop_solver_calls:                      26
% 1.63/1.00  prop_fast_solver_calls:                 506
% 1.63/1.00  smt_solver_calls:                       0
% 1.63/1.00  smt_fast_solver_calls:                  0
% 1.63/1.00  prop_num_of_clauses:                    461
% 1.63/1.00  prop_preprocess_simplified:             3164
% 1.63/1.00  prop_fo_subsumed:                       6
% 1.63/1.00  prop_solver_time:                       0.
% 1.63/1.00  smt_solver_time:                        0.
% 1.63/1.00  smt_fast_solver_time:                   0.
% 1.63/1.00  prop_fast_solver_time:                  0.
% 1.63/1.00  prop_unsat_core_time:                   0.
% 1.63/1.00  
% 1.63/1.00  ------ QBF
% 1.63/1.00  
% 1.63/1.00  qbf_q_res:                              0
% 1.63/1.00  qbf_num_tautologies:                    0
% 1.63/1.00  qbf_prep_cycles:                        0
% 1.63/1.00  
% 1.63/1.00  ------ BMC1
% 1.63/1.00  
% 1.63/1.00  bmc1_current_bound:                     -1
% 1.63/1.00  bmc1_last_solved_bound:                 -1
% 1.63/1.00  bmc1_unsat_core_size:                   -1
% 1.63/1.00  bmc1_unsat_core_parents_size:           -1
% 1.63/1.00  bmc1_merge_next_fun:                    0
% 1.63/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.63/1.00  
% 1.63/1.00  ------ Instantiation
% 1.63/1.00  
% 1.63/1.00  inst_num_of_clauses:                    167
% 1.63/1.00  inst_num_in_passive:                    94
% 1.63/1.00  inst_num_in_active:                     73
% 1.63/1.00  inst_num_in_unprocessed:                0
% 1.63/1.00  inst_num_of_loops:                      80
% 1.63/1.00  inst_num_of_learning_restarts:          0
% 1.63/1.00  inst_num_moves_active_passive:          6
% 1.63/1.00  inst_lit_activity:                      0
% 1.63/1.00  inst_lit_activity_moves:                0
% 1.63/1.00  inst_num_tautologies:                   0
% 1.63/1.00  inst_num_prop_implied:                  0
% 1.63/1.00  inst_num_existing_simplified:           0
% 1.63/1.00  inst_num_eq_res_simplified:             0
% 1.63/1.00  inst_num_child_elim:                    0
% 1.63/1.00  inst_num_of_dismatching_blockings:      120
% 1.63/1.00  inst_num_of_non_proper_insts:           246
% 1.63/1.00  inst_num_of_duplicates:                 0
% 1.63/1.00  inst_inst_num_from_inst_to_res:         0
% 1.63/1.00  inst_dismatching_checking_time:         0.
% 1.63/1.00  
% 1.63/1.00  ------ Resolution
% 1.63/1.00  
% 1.63/1.00  res_num_of_clauses:                     0
% 1.63/1.00  res_num_in_passive:                     0
% 1.63/1.00  res_num_in_active:                      0
% 1.63/1.00  res_num_of_loops:                       69
% 1.63/1.00  res_forward_subset_subsumed:            24
% 1.63/1.00  res_backward_subset_subsumed:           0
% 1.63/1.00  res_forward_subsumed:                   0
% 1.63/1.00  res_backward_subsumed:                  4
% 1.63/1.00  res_forward_subsumption_resolution:     0
% 1.63/1.00  res_backward_subsumption_resolution:    2
% 1.63/1.00  res_clause_to_clause_subsumption:       155
% 1.63/1.00  res_orphan_elimination:                 0
% 1.63/1.00  res_tautology_del:                      14
% 1.63/1.00  res_num_eq_res_simplified:              0
% 1.63/1.00  res_num_sel_changes:                    0
% 1.63/1.00  res_moves_from_active_to_pass:          0
% 1.63/1.00  
% 1.63/1.00  ------ Superposition
% 1.63/1.00  
% 1.63/1.00  sup_time_total:                         0.
% 1.63/1.00  sup_time_generating:                    0.
% 1.63/1.00  sup_time_sim_full:                      0.
% 1.63/1.00  sup_time_sim_immed:                     0.
% 1.63/1.00  
% 1.63/1.00  sup_num_of_clauses:                     18
% 1.63/1.00  sup_num_in_active:                      10
% 1.63/1.00  sup_num_in_passive:                     8
% 1.63/1.00  sup_num_of_loops:                       14
% 1.63/1.00  sup_fw_superposition:                   13
% 1.63/1.00  sup_bw_superposition:                   7
% 1.63/1.00  sup_immediate_simplified:               1
% 1.63/1.00  sup_given_eliminated:                   0
% 1.63/1.00  comparisons_done:                       0
% 1.63/1.00  comparisons_avoided:                    2
% 1.63/1.00  
% 1.63/1.00  ------ Simplifications
% 1.63/1.00  
% 1.63/1.00  
% 1.63/1.00  sim_fw_subset_subsumed:                 1
% 1.63/1.00  sim_bw_subset_subsumed:                 4
% 1.63/1.00  sim_fw_subsumed:                        1
% 1.63/1.00  sim_bw_subsumed:                        0
% 1.63/1.00  sim_fw_subsumption_res:                 1
% 1.63/1.00  sim_bw_subsumption_res:                 0
% 1.63/1.00  sim_tautology_del:                      1
% 1.63/1.00  sim_eq_tautology_del:                   5
% 1.63/1.00  sim_eq_res_simp:                        0
% 1.63/1.00  sim_fw_demodulated:                     0
% 1.63/1.00  sim_bw_demodulated:                     2
% 1.63/1.00  sim_light_normalised:                   0
% 1.63/1.00  sim_joinable_taut:                      0
% 1.63/1.00  sim_joinable_simp:                      0
% 1.63/1.00  sim_ac_normalised:                      0
% 1.63/1.00  sim_smt_subsumption:                    0
% 1.63/1.00  
%------------------------------------------------------------------------------
