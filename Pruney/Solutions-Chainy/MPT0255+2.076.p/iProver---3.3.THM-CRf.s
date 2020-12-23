%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:34:28 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 382 expanded)
%              Number of clauses        :   29 (  84 expanded)
%              Number of leaves         :    9 ( 103 expanded)
%              Depth                    :   20
%              Number of atoms          :  183 (1234 expanded)
%              Number of equality atoms :   88 ( 452 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
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

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f15])).

fof(f17,plain,(
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

fof(f18,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f27,f34])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f23,f34,f34])).

fof(f10,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ),
    inference(negated_conjecture,[],[f10])).

fof(f13,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 ),
    inference(ennf_transformation,[],[f11])).

fof(f21,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
   => k2_xboole_0(k2_tarski(sK1,sK2),sK3) = k1_xboole_0 ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    k2_xboole_0(k2_tarski(sK1,sK2),sK3) = k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f13,f21])).

fof(f39,plain,(
    k2_xboole_0(k2_tarski(sK1,sK2),sK3) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f22])).

fof(f50,plain,(
    k1_xboole_0 = k3_tarski(k2_tarski(k2_tarski(sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f39,f34])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f25,f34])).

fof(f52,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k2_tarski(X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f30,f34])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f26,f34])).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k2_tarski(X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f45])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f29,f34])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(definition_unfolding,[],[f32,f34])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f9])).

fof(f49,plain,(
    ! [X0,X1] : k1_xboole_0 != k3_tarski(k2_tarski(k1_tarski(X0),X1)) ),
    inference(definition_unfolding,[],[f38,f34])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X0)
    | k3_tarski(k2_tarski(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_324,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 = k3_tarski(k2_tarski(k2_tarski(sK1,sK2),sK3)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_507,plain,
    ( k3_tarski(k2_tarski(sK3,k2_tarski(sK1,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_15])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k2_tarski(X1,X2))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_322,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k2_tarski(X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1156,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_507,c_322])).

cnf(c_2274,plain,
    ( k3_tarski(k2_tarski(sK3,X0)) = X1
    | r2_hidden(sK0(sK3,X0,X1),X0) = iProver_top
    | r2_hidden(sK0(sK3,X0,X1),X1) = iProver_top
    | r2_hidden(sK0(sK3,X0,X1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_324,c_1156])).

cnf(c_8,plain,
    ( k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_505,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_8])).

cnf(c_1155,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_505,c_322])).

cnf(c_2676,plain,
    ( k3_tarski(k2_tarski(sK3,X0)) = X1
    | r2_hidden(sK0(sK3,X0,X1),X0) = iProver_top
    | r2_hidden(sK0(sK3,X0,X1),X1) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2274,c_1155])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k2_tarski(X2,X1))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_323,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k2_tarski(X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1399,plain,
    ( r2_hidden(X0,k2_tarski(sK1,sK2)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_507,c_323])).

cnf(c_2693,plain,
    ( k3_tarski(k2_tarski(sK3,k2_tarski(sK1,sK2))) = X0
    | r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),X0),X0) = iProver_top
    | r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2676,c_1399])).

cnf(c_2718,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),X0),X0) = iProver_top
    | r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),X0),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2693,c_507])).

cnf(c_3028,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),X0),X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2718,c_1155])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k3_tarski(k2_tarski(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_326,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3030,plain,
    ( k2_tarski(sK1,sK2) = k1_xboole_0
    | k3_tarski(k2_tarski(sK3,k2_tarski(sK1,sK2))) = k2_tarski(sK1,sK2)
    | r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3028,c_326])).

cnf(c_3070,plain,
    ( k2_tarski(sK1,sK2) = k1_xboole_0
    | r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3030,c_507])).

cnf(c_0,plain,
    ( k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_14,plain,
    ( k3_tarski(k2_tarski(k1_tarski(X0),X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_662,plain,
    ( k2_tarski(X0,X1) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_14])).

cnf(c_3230,plain,
    ( r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3070,c_662])).

cnf(c_3238,plain,
    ( k2_tarski(sK1,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3028,c_3230])).

cnf(c_7996,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3238,c_662])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.30  % Computer   : n024.cluster.edu
% 0.11/0.30  % Model      : x86_64 x86_64
% 0.11/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.30  % Memory     : 8042.1875MB
% 0.11/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 16:19:51 EST 2020
% 0.15/0.31  % CPUTime    : 
% 0.15/0.31  % Running in FOF mode
% 3.16/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/0.96  
% 3.16/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.16/0.96  
% 3.16/0.96  ------  iProver source info
% 3.16/0.96  
% 3.16/0.96  git: date: 2020-06-30 10:37:57 +0100
% 3.16/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.16/0.96  git: non_committed_changes: false
% 3.16/0.96  git: last_make_outside_of_git: false
% 3.16/0.96  
% 3.16/0.96  ------ 
% 3.16/0.96  
% 3.16/0.96  ------ Input Options
% 3.16/0.96  
% 3.16/0.96  --out_options                           all
% 3.16/0.96  --tptp_safe_out                         true
% 3.16/0.96  --problem_path                          ""
% 3.16/0.96  --include_path                          ""
% 3.16/0.96  --clausifier                            res/vclausify_rel
% 3.16/0.96  --clausifier_options                    --mode clausify
% 3.16/0.96  --stdin                                 false
% 3.16/0.96  --stats_out                             all
% 3.16/0.96  
% 3.16/0.96  ------ General Options
% 3.16/0.96  
% 3.16/0.96  --fof                                   false
% 3.16/0.96  --time_out_real                         305.
% 3.16/0.96  --time_out_virtual                      -1.
% 3.16/0.96  --symbol_type_check                     false
% 3.16/0.96  --clausify_out                          false
% 3.16/0.96  --sig_cnt_out                           false
% 3.16/0.96  --trig_cnt_out                          false
% 3.16/0.96  --trig_cnt_out_tolerance                1.
% 3.16/0.96  --trig_cnt_out_sk_spl                   false
% 3.16/0.96  --abstr_cl_out                          false
% 3.16/0.96  
% 3.16/0.96  ------ Global Options
% 3.16/0.96  
% 3.16/0.96  --schedule                              default
% 3.16/0.96  --add_important_lit                     false
% 3.16/0.96  --prop_solver_per_cl                    1000
% 3.16/0.96  --min_unsat_core                        false
% 3.16/0.96  --soft_assumptions                      false
% 3.16/0.96  --soft_lemma_size                       3
% 3.16/0.96  --prop_impl_unit_size                   0
% 3.16/0.96  --prop_impl_unit                        []
% 3.16/0.96  --share_sel_clauses                     true
% 3.16/0.96  --reset_solvers                         false
% 3.16/0.96  --bc_imp_inh                            [conj_cone]
% 3.16/0.96  --conj_cone_tolerance                   3.
% 3.16/0.96  --extra_neg_conj                        none
% 3.16/0.96  --large_theory_mode                     true
% 3.16/0.96  --prolific_symb_bound                   200
% 3.16/0.96  --lt_threshold                          2000
% 3.16/0.96  --clause_weak_htbl                      true
% 3.16/0.96  --gc_record_bc_elim                     false
% 3.16/0.96  
% 3.16/0.96  ------ Preprocessing Options
% 3.16/0.96  
% 3.16/0.96  --preprocessing_flag                    true
% 3.16/0.96  --time_out_prep_mult                    0.1
% 3.16/0.96  --splitting_mode                        input
% 3.16/0.96  --splitting_grd                         true
% 3.16/0.96  --splitting_cvd                         false
% 3.16/0.96  --splitting_cvd_svl                     false
% 3.16/0.96  --splitting_nvd                         32
% 3.16/0.96  --sub_typing                            true
% 3.16/0.96  --prep_gs_sim                           true
% 3.16/0.96  --prep_unflatten                        true
% 3.16/0.96  --prep_res_sim                          true
% 3.16/0.96  --prep_upred                            true
% 3.16/0.96  --prep_sem_filter                       exhaustive
% 3.16/0.96  --prep_sem_filter_out                   false
% 3.16/0.96  --pred_elim                             true
% 3.16/0.96  --res_sim_input                         true
% 3.16/0.96  --eq_ax_congr_red                       true
% 3.16/0.96  --pure_diseq_elim                       true
% 3.16/0.96  --brand_transform                       false
% 3.16/0.96  --non_eq_to_eq                          false
% 3.16/0.96  --prep_def_merge                        true
% 3.16/0.96  --prep_def_merge_prop_impl              false
% 3.16/0.96  --prep_def_merge_mbd                    true
% 3.16/0.96  --prep_def_merge_tr_red                 false
% 3.16/0.96  --prep_def_merge_tr_cl                  false
% 3.16/0.96  --smt_preprocessing                     true
% 3.16/0.96  --smt_ac_axioms                         fast
% 3.16/0.96  --preprocessed_out                      false
% 3.16/0.96  --preprocessed_stats                    false
% 3.16/0.96  
% 3.16/0.96  ------ Abstraction refinement Options
% 3.16/0.96  
% 3.16/0.96  --abstr_ref                             []
% 3.16/0.96  --abstr_ref_prep                        false
% 3.16/0.96  --abstr_ref_until_sat                   false
% 3.16/0.96  --abstr_ref_sig_restrict                funpre
% 3.16/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.16/0.96  --abstr_ref_under                       []
% 3.16/0.96  
% 3.16/0.96  ------ SAT Options
% 3.16/0.96  
% 3.16/0.96  --sat_mode                              false
% 3.16/0.96  --sat_fm_restart_options                ""
% 3.16/0.96  --sat_gr_def                            false
% 3.16/0.96  --sat_epr_types                         true
% 3.16/0.96  --sat_non_cyclic_types                  false
% 3.16/0.96  --sat_finite_models                     false
% 3.16/0.96  --sat_fm_lemmas                         false
% 3.16/0.96  --sat_fm_prep                           false
% 3.16/0.96  --sat_fm_uc_incr                        true
% 3.16/0.96  --sat_out_model                         small
% 3.16/0.96  --sat_out_clauses                       false
% 3.16/0.96  
% 3.16/0.96  ------ QBF Options
% 3.16/0.96  
% 3.16/0.96  --qbf_mode                              false
% 3.16/0.96  --qbf_elim_univ                         false
% 3.16/0.96  --qbf_dom_inst                          none
% 3.16/0.96  --qbf_dom_pre_inst                      false
% 3.16/0.96  --qbf_sk_in                             false
% 3.16/0.96  --qbf_pred_elim                         true
% 3.16/0.96  --qbf_split                             512
% 3.16/0.96  
% 3.16/0.96  ------ BMC1 Options
% 3.16/0.96  
% 3.16/0.96  --bmc1_incremental                      false
% 3.16/0.96  --bmc1_axioms                           reachable_all
% 3.16/0.96  --bmc1_min_bound                        0
% 3.16/0.96  --bmc1_max_bound                        -1
% 3.16/0.96  --bmc1_max_bound_default                -1
% 3.16/0.96  --bmc1_symbol_reachability              true
% 3.16/0.96  --bmc1_property_lemmas                  false
% 3.16/0.96  --bmc1_k_induction                      false
% 3.16/0.96  --bmc1_non_equiv_states                 false
% 3.16/0.96  --bmc1_deadlock                         false
% 3.16/0.96  --bmc1_ucm                              false
% 3.16/0.96  --bmc1_add_unsat_core                   none
% 3.16/0.96  --bmc1_unsat_core_children              false
% 3.16/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.16/0.96  --bmc1_out_stat                         full
% 3.16/0.96  --bmc1_ground_init                      false
% 3.16/0.96  --bmc1_pre_inst_next_state              false
% 3.16/0.96  --bmc1_pre_inst_state                   false
% 3.16/0.96  --bmc1_pre_inst_reach_state             false
% 3.16/0.96  --bmc1_out_unsat_core                   false
% 3.16/0.96  --bmc1_aig_witness_out                  false
% 3.16/0.96  --bmc1_verbose                          false
% 3.16/0.96  --bmc1_dump_clauses_tptp                false
% 3.16/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.16/0.96  --bmc1_dump_file                        -
% 3.16/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.16/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.16/0.96  --bmc1_ucm_extend_mode                  1
% 3.16/0.96  --bmc1_ucm_init_mode                    2
% 3.16/0.96  --bmc1_ucm_cone_mode                    none
% 3.16/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.16/0.96  --bmc1_ucm_relax_model                  4
% 3.16/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.16/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.16/0.96  --bmc1_ucm_layered_model                none
% 3.16/0.96  --bmc1_ucm_max_lemma_size               10
% 3.16/0.96  
% 3.16/0.96  ------ AIG Options
% 3.16/0.96  
% 3.16/0.96  --aig_mode                              false
% 3.16/0.96  
% 3.16/0.96  ------ Instantiation Options
% 3.16/0.96  
% 3.16/0.96  --instantiation_flag                    true
% 3.16/0.96  --inst_sos_flag                         false
% 3.16/0.96  --inst_sos_phase                        true
% 3.16/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.16/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.16/0.96  --inst_lit_sel_side                     num_symb
% 3.16/0.96  --inst_solver_per_active                1400
% 3.16/0.96  --inst_solver_calls_frac                1.
% 3.16/0.96  --inst_passive_queue_type               priority_queues
% 3.16/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.16/0.96  --inst_passive_queues_freq              [25;2]
% 3.16/0.96  --inst_dismatching                      true
% 3.16/0.96  --inst_eager_unprocessed_to_passive     true
% 3.16/0.96  --inst_prop_sim_given                   true
% 3.16/0.96  --inst_prop_sim_new                     false
% 3.16/0.96  --inst_subs_new                         false
% 3.16/0.96  --inst_eq_res_simp                      false
% 3.16/0.96  --inst_subs_given                       false
% 3.16/0.96  --inst_orphan_elimination               true
% 3.16/0.96  --inst_learning_loop_flag               true
% 3.16/0.96  --inst_learning_start                   3000
% 3.16/0.96  --inst_learning_factor                  2
% 3.16/0.96  --inst_start_prop_sim_after_learn       3
% 3.16/0.96  --inst_sel_renew                        solver
% 3.16/0.96  --inst_lit_activity_flag                true
% 3.16/0.96  --inst_restr_to_given                   false
% 3.16/0.96  --inst_activity_threshold               500
% 3.16/0.96  --inst_out_proof                        true
% 3.16/0.96  
% 3.16/0.96  ------ Resolution Options
% 3.16/0.96  
% 3.16/0.96  --resolution_flag                       true
% 3.16/0.96  --res_lit_sel                           adaptive
% 3.16/0.96  --res_lit_sel_side                      none
% 3.16/0.96  --res_ordering                          kbo
% 3.16/0.96  --res_to_prop_solver                    active
% 3.16/0.96  --res_prop_simpl_new                    false
% 3.16/0.96  --res_prop_simpl_given                  true
% 3.16/0.96  --res_passive_queue_type                priority_queues
% 3.16/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.16/0.96  --res_passive_queues_freq               [15;5]
% 3.16/0.96  --res_forward_subs                      full
% 3.16/0.96  --res_backward_subs                     full
% 3.16/0.96  --res_forward_subs_resolution           true
% 3.16/0.96  --res_backward_subs_resolution          true
% 3.16/0.96  --res_orphan_elimination                true
% 3.16/0.96  --res_time_limit                        2.
% 3.16/0.96  --res_out_proof                         true
% 3.16/0.96  
% 3.16/0.96  ------ Superposition Options
% 3.16/0.96  
% 3.16/0.96  --superposition_flag                    true
% 3.16/0.96  --sup_passive_queue_type                priority_queues
% 3.16/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.16/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.16/0.96  --demod_completeness_check              fast
% 3.16/0.96  --demod_use_ground                      true
% 3.16/0.96  --sup_to_prop_solver                    passive
% 3.16/0.96  --sup_prop_simpl_new                    true
% 3.16/0.96  --sup_prop_simpl_given                  true
% 3.16/0.96  --sup_fun_splitting                     false
% 3.16/0.96  --sup_smt_interval                      50000
% 3.16/0.96  
% 3.16/0.96  ------ Superposition Simplification Setup
% 3.16/0.96  
% 3.16/0.96  --sup_indices_passive                   []
% 3.16/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.16/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.96  --sup_full_bw                           [BwDemod]
% 3.16/0.96  --sup_immed_triv                        [TrivRules]
% 3.16/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.16/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.96  --sup_immed_bw_main                     []
% 3.16/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.16/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/0.96  
% 3.16/0.96  ------ Combination Options
% 3.16/0.96  
% 3.16/0.96  --comb_res_mult                         3
% 3.16/0.96  --comb_sup_mult                         2
% 3.16/0.96  --comb_inst_mult                        10
% 3.16/0.96  
% 3.16/0.96  ------ Debug Options
% 3.16/0.96  
% 3.16/0.96  --dbg_backtrace                         false
% 3.16/0.96  --dbg_dump_prop_clauses                 false
% 3.16/0.96  --dbg_dump_prop_clauses_file            -
% 3.16/0.96  --dbg_out_stat                          false
% 3.16/0.96  ------ Parsing...
% 3.16/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.16/0.96  
% 3.16/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.16/0.96  
% 3.16/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.16/0.96  
% 3.16/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.16/0.96  ------ Proving...
% 3.16/0.96  ------ Problem Properties 
% 3.16/0.96  
% 3.16/0.96  
% 3.16/0.96  clauses                                 13
% 3.16/0.96  conjectures                             1
% 3.16/0.96  EPR                                     0
% 3.16/0.96  Horn                                    11
% 3.16/0.96  unary                                   6
% 3.16/0.96  binary                                  2
% 3.16/0.96  lits                                    26
% 3.16/0.96  lits eq                                 10
% 3.16/0.96  fd_pure                                 0
% 3.16/0.96  fd_pseudo                               0
% 3.16/0.96  fd_cond                                 0
% 3.16/0.96  fd_pseudo_cond                          3
% 3.16/0.96  AC symbols                              0
% 3.16/0.96  
% 3.16/0.96  ------ Schedule dynamic 5 is on 
% 3.16/0.96  
% 3.16/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.16/0.96  
% 3.16/0.96  
% 3.16/0.96  ------ 
% 3.16/0.96  Current options:
% 3.16/0.96  ------ 
% 3.16/0.96  
% 3.16/0.96  ------ Input Options
% 3.16/0.96  
% 3.16/0.96  --out_options                           all
% 3.16/0.96  --tptp_safe_out                         true
% 3.16/0.96  --problem_path                          ""
% 3.16/0.96  --include_path                          ""
% 3.16/0.96  --clausifier                            res/vclausify_rel
% 3.16/0.96  --clausifier_options                    --mode clausify
% 3.16/0.96  --stdin                                 false
% 3.16/0.96  --stats_out                             all
% 3.16/0.96  
% 3.16/0.96  ------ General Options
% 3.16/0.96  
% 3.16/0.96  --fof                                   false
% 3.16/0.96  --time_out_real                         305.
% 3.16/0.96  --time_out_virtual                      -1.
% 3.16/0.96  --symbol_type_check                     false
% 3.16/0.96  --clausify_out                          false
% 3.16/0.96  --sig_cnt_out                           false
% 3.16/0.96  --trig_cnt_out                          false
% 3.16/0.96  --trig_cnt_out_tolerance                1.
% 3.16/0.96  --trig_cnt_out_sk_spl                   false
% 3.16/0.96  --abstr_cl_out                          false
% 3.16/0.96  
% 3.16/0.96  ------ Global Options
% 3.16/0.96  
% 3.16/0.96  --schedule                              default
% 3.16/0.96  --add_important_lit                     false
% 3.16/0.96  --prop_solver_per_cl                    1000
% 3.16/0.96  --min_unsat_core                        false
% 3.16/0.96  --soft_assumptions                      false
% 3.16/0.96  --soft_lemma_size                       3
% 3.16/0.96  --prop_impl_unit_size                   0
% 3.16/0.96  --prop_impl_unit                        []
% 3.16/0.96  --share_sel_clauses                     true
% 3.16/0.96  --reset_solvers                         false
% 3.16/0.96  --bc_imp_inh                            [conj_cone]
% 3.16/0.96  --conj_cone_tolerance                   3.
% 3.16/0.96  --extra_neg_conj                        none
% 3.16/0.96  --large_theory_mode                     true
% 3.16/0.96  --prolific_symb_bound                   200
% 3.16/0.96  --lt_threshold                          2000
% 3.16/0.96  --clause_weak_htbl                      true
% 3.16/0.96  --gc_record_bc_elim                     false
% 3.16/0.96  
% 3.16/0.96  ------ Preprocessing Options
% 3.16/0.96  
% 3.16/0.96  --preprocessing_flag                    true
% 3.16/0.96  --time_out_prep_mult                    0.1
% 3.16/0.96  --splitting_mode                        input
% 3.16/0.96  --splitting_grd                         true
% 3.16/0.96  --splitting_cvd                         false
% 3.16/0.96  --splitting_cvd_svl                     false
% 3.16/0.96  --splitting_nvd                         32
% 3.16/0.96  --sub_typing                            true
% 3.16/0.96  --prep_gs_sim                           true
% 3.16/0.96  --prep_unflatten                        true
% 3.16/0.96  --prep_res_sim                          true
% 3.16/0.96  --prep_upred                            true
% 3.16/0.96  --prep_sem_filter                       exhaustive
% 3.16/0.96  --prep_sem_filter_out                   false
% 3.16/0.96  --pred_elim                             true
% 3.16/0.96  --res_sim_input                         true
% 3.16/0.96  --eq_ax_congr_red                       true
% 3.16/0.96  --pure_diseq_elim                       true
% 3.16/0.96  --brand_transform                       false
% 3.16/0.96  --non_eq_to_eq                          false
% 3.16/0.96  --prep_def_merge                        true
% 3.16/0.96  --prep_def_merge_prop_impl              false
% 3.16/0.96  --prep_def_merge_mbd                    true
% 3.16/0.96  --prep_def_merge_tr_red                 false
% 3.16/0.96  --prep_def_merge_tr_cl                  false
% 3.16/0.96  --smt_preprocessing                     true
% 3.16/0.96  --smt_ac_axioms                         fast
% 3.16/0.96  --preprocessed_out                      false
% 3.16/0.96  --preprocessed_stats                    false
% 3.16/0.96  
% 3.16/0.96  ------ Abstraction refinement Options
% 3.16/0.96  
% 3.16/0.96  --abstr_ref                             []
% 3.16/0.96  --abstr_ref_prep                        false
% 3.16/0.96  --abstr_ref_until_sat                   false
% 3.16/0.96  --abstr_ref_sig_restrict                funpre
% 3.16/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.16/0.96  --abstr_ref_under                       []
% 3.16/0.96  
% 3.16/0.96  ------ SAT Options
% 3.16/0.96  
% 3.16/0.96  --sat_mode                              false
% 3.16/0.96  --sat_fm_restart_options                ""
% 3.16/0.96  --sat_gr_def                            false
% 3.16/0.96  --sat_epr_types                         true
% 3.16/0.96  --sat_non_cyclic_types                  false
% 3.16/0.96  --sat_finite_models                     false
% 3.16/0.96  --sat_fm_lemmas                         false
% 3.16/0.96  --sat_fm_prep                           false
% 3.16/0.96  --sat_fm_uc_incr                        true
% 3.16/0.96  --sat_out_model                         small
% 3.16/0.96  --sat_out_clauses                       false
% 3.16/0.96  
% 3.16/0.96  ------ QBF Options
% 3.16/0.96  
% 3.16/0.96  --qbf_mode                              false
% 3.16/0.96  --qbf_elim_univ                         false
% 3.16/0.96  --qbf_dom_inst                          none
% 3.16/0.96  --qbf_dom_pre_inst                      false
% 3.16/0.96  --qbf_sk_in                             false
% 3.16/0.96  --qbf_pred_elim                         true
% 3.16/0.96  --qbf_split                             512
% 3.16/0.96  
% 3.16/0.96  ------ BMC1 Options
% 3.16/0.96  
% 3.16/0.96  --bmc1_incremental                      false
% 3.16/0.96  --bmc1_axioms                           reachable_all
% 3.16/0.96  --bmc1_min_bound                        0
% 3.16/0.96  --bmc1_max_bound                        -1
% 3.16/0.96  --bmc1_max_bound_default                -1
% 3.16/0.96  --bmc1_symbol_reachability              true
% 3.16/0.96  --bmc1_property_lemmas                  false
% 3.16/0.96  --bmc1_k_induction                      false
% 3.16/0.96  --bmc1_non_equiv_states                 false
% 3.16/0.96  --bmc1_deadlock                         false
% 3.16/0.96  --bmc1_ucm                              false
% 3.16/0.96  --bmc1_add_unsat_core                   none
% 3.16/0.96  --bmc1_unsat_core_children              false
% 3.16/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.16/0.96  --bmc1_out_stat                         full
% 3.16/0.96  --bmc1_ground_init                      false
% 3.16/0.96  --bmc1_pre_inst_next_state              false
% 3.16/0.96  --bmc1_pre_inst_state                   false
% 3.16/0.96  --bmc1_pre_inst_reach_state             false
% 3.16/0.96  --bmc1_out_unsat_core                   false
% 3.16/0.96  --bmc1_aig_witness_out                  false
% 3.16/0.96  --bmc1_verbose                          false
% 3.16/0.96  --bmc1_dump_clauses_tptp                false
% 3.16/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.16/0.96  --bmc1_dump_file                        -
% 3.16/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.16/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.16/0.96  --bmc1_ucm_extend_mode                  1
% 3.16/0.96  --bmc1_ucm_init_mode                    2
% 3.16/0.96  --bmc1_ucm_cone_mode                    none
% 3.16/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.16/0.96  --bmc1_ucm_relax_model                  4
% 3.16/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.16/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.16/0.96  --bmc1_ucm_layered_model                none
% 3.16/0.96  --bmc1_ucm_max_lemma_size               10
% 3.16/0.96  
% 3.16/0.96  ------ AIG Options
% 3.16/0.96  
% 3.16/0.96  --aig_mode                              false
% 3.16/0.96  
% 3.16/0.96  ------ Instantiation Options
% 3.16/0.96  
% 3.16/0.96  --instantiation_flag                    true
% 3.16/0.96  --inst_sos_flag                         false
% 3.16/0.96  --inst_sos_phase                        true
% 3.16/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.16/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.16/0.96  --inst_lit_sel_side                     none
% 3.16/0.96  --inst_solver_per_active                1400
% 3.16/0.96  --inst_solver_calls_frac                1.
% 3.16/0.96  --inst_passive_queue_type               priority_queues
% 3.16/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.16/0.96  --inst_passive_queues_freq              [25;2]
% 3.16/0.96  --inst_dismatching                      true
% 3.16/0.96  --inst_eager_unprocessed_to_passive     true
% 3.16/0.96  --inst_prop_sim_given                   true
% 3.16/0.96  --inst_prop_sim_new                     false
% 3.16/0.96  --inst_subs_new                         false
% 3.16/0.96  --inst_eq_res_simp                      false
% 3.16/0.96  --inst_subs_given                       false
% 3.16/0.96  --inst_orphan_elimination               true
% 3.16/0.96  --inst_learning_loop_flag               true
% 3.16/0.96  --inst_learning_start                   3000
% 3.16/0.96  --inst_learning_factor                  2
% 3.16/0.96  --inst_start_prop_sim_after_learn       3
% 3.16/0.96  --inst_sel_renew                        solver
% 3.16/0.96  --inst_lit_activity_flag                true
% 3.16/0.96  --inst_restr_to_given                   false
% 3.16/0.96  --inst_activity_threshold               500
% 3.16/0.96  --inst_out_proof                        true
% 3.16/0.96  
% 3.16/0.96  ------ Resolution Options
% 3.16/0.96  
% 3.16/0.96  --resolution_flag                       false
% 3.16/0.96  --res_lit_sel                           adaptive
% 3.16/0.96  --res_lit_sel_side                      none
% 3.16/0.96  --res_ordering                          kbo
% 3.16/0.96  --res_to_prop_solver                    active
% 3.16/0.96  --res_prop_simpl_new                    false
% 3.16/0.96  --res_prop_simpl_given                  true
% 3.16/0.96  --res_passive_queue_type                priority_queues
% 3.16/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.16/0.96  --res_passive_queues_freq               [15;5]
% 3.16/0.96  --res_forward_subs                      full
% 3.16/0.96  --res_backward_subs                     full
% 3.16/0.96  --res_forward_subs_resolution           true
% 3.16/0.96  --res_backward_subs_resolution          true
% 3.16/0.96  --res_orphan_elimination                true
% 3.16/0.96  --res_time_limit                        2.
% 3.16/0.96  --res_out_proof                         true
% 3.16/0.96  
% 3.16/0.96  ------ Superposition Options
% 3.16/0.96  
% 3.16/0.96  --superposition_flag                    true
% 3.16/0.96  --sup_passive_queue_type                priority_queues
% 3.16/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.16/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.16/0.96  --demod_completeness_check              fast
% 3.16/0.96  --demod_use_ground                      true
% 3.16/0.96  --sup_to_prop_solver                    passive
% 3.16/0.96  --sup_prop_simpl_new                    true
% 3.16/0.96  --sup_prop_simpl_given                  true
% 3.16/0.96  --sup_fun_splitting                     false
% 3.16/0.96  --sup_smt_interval                      50000
% 3.16/0.96  
% 3.16/0.96  ------ Superposition Simplification Setup
% 3.16/0.96  
% 3.16/0.96  --sup_indices_passive                   []
% 3.16/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.16/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.96  --sup_full_bw                           [BwDemod]
% 3.16/0.96  --sup_immed_triv                        [TrivRules]
% 3.16/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.16/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.96  --sup_immed_bw_main                     []
% 3.16/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.16/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/0.96  
% 3.16/0.96  ------ Combination Options
% 3.16/0.96  
% 3.16/0.96  --comb_res_mult                         3
% 3.16/0.96  --comb_sup_mult                         2
% 3.16/0.96  --comb_inst_mult                        10
% 3.16/0.96  
% 3.16/0.96  ------ Debug Options
% 3.16/0.96  
% 3.16/0.96  --dbg_backtrace                         false
% 3.16/0.96  --dbg_dump_prop_clauses                 false
% 3.16/0.96  --dbg_dump_prop_clauses_file            -
% 3.16/0.96  --dbg_out_stat                          false
% 3.16/0.96  
% 3.16/0.96  
% 3.16/0.96  
% 3.16/0.96  
% 3.16/0.96  ------ Proving...
% 3.16/0.96  
% 3.16/0.96  
% 3.16/0.96  % SZS status Theorem for theBenchmark.p
% 3.16/0.96  
% 3.16/0.96   Resolution empty clause
% 3.16/0.96  
% 3.16/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 3.16/0.96  
% 3.16/0.96  fof(f2,axiom,(
% 3.16/0.96    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.16/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.96  
% 3.16/0.96  fof(f14,plain,(
% 3.16/0.96    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.16/0.96    inference(nnf_transformation,[],[f2])).
% 3.16/0.96  
% 3.16/0.96  fof(f15,plain,(
% 3.16/0.96    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.16/0.96    inference(flattening,[],[f14])).
% 3.16/0.96  
% 3.16/0.96  fof(f16,plain,(
% 3.16/0.96    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.16/0.96    inference(rectify,[],[f15])).
% 3.16/0.96  
% 3.16/0.96  fof(f17,plain,(
% 3.16/0.96    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.16/0.96    introduced(choice_axiom,[])).
% 3.16/0.96  
% 3.16/0.96  fof(f18,plain,(
% 3.16/0.96    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.16/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).
% 3.16/0.96  
% 3.16/0.96  fof(f27,plain,(
% 3.16/0.96    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.16/0.96    inference(cnf_transformation,[],[f18])).
% 3.16/0.96  
% 3.16/0.96  fof(f7,axiom,(
% 3.16/0.96    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.16/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.96  
% 3.16/0.96  fof(f34,plain,(
% 3.16/0.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.16/0.96    inference(cnf_transformation,[],[f7])).
% 3.16/0.96  
% 3.16/0.96  fof(f44,plain,(
% 3.16/0.96    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.16/0.96    inference(definition_unfolding,[],[f27,f34])).
% 3.16/0.96  
% 3.16/0.96  fof(f1,axiom,(
% 3.16/0.96    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.16/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.96  
% 3.16/0.96  fof(f23,plain,(
% 3.16/0.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.16/0.96    inference(cnf_transformation,[],[f1])).
% 3.16/0.96  
% 3.16/0.96  fof(f41,plain,(
% 3.16/0.96    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0))) )),
% 3.16/0.96    inference(definition_unfolding,[],[f23,f34,f34])).
% 3.16/0.96  
% 3.16/0.96  fof(f10,conjecture,(
% 3.16/0.96    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0),
% 3.16/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.96  
% 3.16/0.96  fof(f11,negated_conjecture,(
% 3.16/0.96    ~! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0),
% 3.16/0.96    inference(negated_conjecture,[],[f10])).
% 3.16/0.96  
% 3.16/0.96  fof(f13,plain,(
% 3.16/0.96    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0),
% 3.16/0.96    inference(ennf_transformation,[],[f11])).
% 3.16/0.96  
% 3.16/0.96  fof(f21,plain,(
% 3.16/0.96    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 => k2_xboole_0(k2_tarski(sK1,sK2),sK3) = k1_xboole_0),
% 3.16/0.96    introduced(choice_axiom,[])).
% 3.16/0.96  
% 3.16/0.96  fof(f22,plain,(
% 3.16/0.96    k2_xboole_0(k2_tarski(sK1,sK2),sK3) = k1_xboole_0),
% 3.16/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f13,f21])).
% 3.16/0.96  
% 3.16/0.96  fof(f39,plain,(
% 3.16/0.96    k2_xboole_0(k2_tarski(sK1,sK2),sK3) = k1_xboole_0),
% 3.16/0.96    inference(cnf_transformation,[],[f22])).
% 3.16/0.96  
% 3.16/0.96  fof(f50,plain,(
% 3.16/0.96    k1_xboole_0 = k3_tarski(k2_tarski(k2_tarski(sK1,sK2),sK3))),
% 3.16/0.96    inference(definition_unfolding,[],[f39,f34])).
% 3.16/0.96  
% 3.16/0.96  fof(f25,plain,(
% 3.16/0.96    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 3.16/0.96    inference(cnf_transformation,[],[f18])).
% 3.16/0.96  
% 3.16/0.96  fof(f46,plain,(
% 3.16/0.96    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k2_tarski(X0,X1)) != X2) )),
% 3.16/0.96    inference(definition_unfolding,[],[f25,f34])).
% 3.16/0.96  
% 3.16/0.96  fof(f52,plain,(
% 3.16/0.96    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k2_tarski(X0,X1))) | ~r2_hidden(X4,X0)) )),
% 3.16/0.96    inference(equality_resolution,[],[f46])).
% 3.16/0.96  
% 3.16/0.96  fof(f3,axiom,(
% 3.16/0.96    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.16/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.96  
% 3.16/0.96  fof(f30,plain,(
% 3.16/0.96    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.16/0.96    inference(cnf_transformation,[],[f3])).
% 3.16/0.96  
% 3.16/0.96  fof(f48,plain,(
% 3.16/0.96    ( ! [X0] : (k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0) )),
% 3.16/0.96    inference(definition_unfolding,[],[f30,f34])).
% 3.16/0.96  
% 3.16/0.96  fof(f26,plain,(
% 3.16/0.96    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 3.16/0.96    inference(cnf_transformation,[],[f18])).
% 3.16/0.96  
% 3.16/0.96  fof(f45,plain,(
% 3.16/0.96    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k2_tarski(X0,X1)) != X2) )),
% 3.16/0.96    inference(definition_unfolding,[],[f26,f34])).
% 3.16/0.96  
% 3.16/0.96  fof(f51,plain,(
% 3.16/0.96    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k2_tarski(X0,X1))) | ~r2_hidden(X4,X1)) )),
% 3.16/0.96    inference(equality_resolution,[],[f45])).
% 3.16/0.96  
% 3.16/0.96  fof(f29,plain,(
% 3.16/0.96    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.16/0.96    inference(cnf_transformation,[],[f18])).
% 3.16/0.96  
% 3.16/0.96  fof(f42,plain,(
% 3.16/0.96    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.16/0.96    inference(definition_unfolding,[],[f29,f34])).
% 3.16/0.96  
% 3.16/0.96  fof(f5,axiom,(
% 3.16/0.96    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 3.16/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.96  
% 3.16/0.96  fof(f32,plain,(
% 3.16/0.96    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 3.16/0.96    inference(cnf_transformation,[],[f5])).
% 3.16/0.96  
% 3.16/0.96  fof(f40,plain,(
% 3.16/0.96    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))) )),
% 3.16/0.96    inference(definition_unfolding,[],[f32,f34])).
% 3.16/0.96  
% 3.16/0.96  fof(f9,axiom,(
% 3.16/0.96    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 3.16/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/0.96  
% 3.16/0.96  fof(f38,plain,(
% 3.16/0.96    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 3.16/0.96    inference(cnf_transformation,[],[f9])).
% 3.16/0.96  
% 3.16/0.96  fof(f49,plain,(
% 3.16/0.96    ( ! [X0,X1] : (k1_xboole_0 != k3_tarski(k2_tarski(k1_tarski(X0),X1))) )),
% 3.16/0.96    inference(definition_unfolding,[],[f38,f34])).
% 3.16/0.96  
% 3.16/0.96  cnf(c_4,plain,
% 3.16/0.96      ( r2_hidden(sK0(X0,X1,X2),X1)
% 3.16/0.96      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.16/0.96      | r2_hidden(sK0(X0,X1,X2),X0)
% 3.16/0.96      | k3_tarski(k2_tarski(X0,X1)) = X2 ),
% 3.16/0.96      inference(cnf_transformation,[],[f44]) ).
% 3.16/0.96  
% 3.16/0.96  cnf(c_324,plain,
% 3.16/0.96      ( k3_tarski(k2_tarski(X0,X1)) = X2
% 3.16/0.96      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
% 3.16/0.96      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 3.16/0.96      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top ),
% 3.16/0.96      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.16/0.96  
% 3.16/0.96  cnf(c_1,plain,
% 3.16/0.96      ( k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
% 3.16/0.96      inference(cnf_transformation,[],[f41]) ).
% 3.16/0.96  
% 3.16/0.96  cnf(c_15,negated_conjecture,
% 3.16/0.96      ( k1_xboole_0 = k3_tarski(k2_tarski(k2_tarski(sK1,sK2),sK3)) ),
% 3.16/0.96      inference(cnf_transformation,[],[f50]) ).
% 3.16/0.96  
% 3.16/0.96  cnf(c_507,plain,
% 3.16/0.96      ( k3_tarski(k2_tarski(sK3,k2_tarski(sK1,sK2))) = k1_xboole_0 ),
% 3.16/0.96      inference(superposition,[status(thm)],[c_1,c_15]) ).
% 3.16/0.96  
% 3.16/0.96  cnf(c_6,plain,
% 3.16/0.96      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k3_tarski(k2_tarski(X1,X2))) ),
% 3.16/0.96      inference(cnf_transformation,[],[f52]) ).
% 3.16/0.96  
% 3.16/0.96  cnf(c_322,plain,
% 3.16/0.96      ( r2_hidden(X0,X1) != iProver_top
% 3.16/0.96      | r2_hidden(X0,k3_tarski(k2_tarski(X1,X2))) = iProver_top ),
% 3.16/0.96      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.16/0.96  
% 3.16/0.96  cnf(c_1156,plain,
% 3.16/0.96      ( r2_hidden(X0,sK3) != iProver_top
% 3.16/0.96      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 3.16/0.96      inference(superposition,[status(thm)],[c_507,c_322]) ).
% 3.16/0.96  
% 3.16/0.96  cnf(c_2274,plain,
% 3.16/0.96      ( k3_tarski(k2_tarski(sK3,X0)) = X1
% 3.16/0.96      | r2_hidden(sK0(sK3,X0,X1),X0) = iProver_top
% 3.16/0.96      | r2_hidden(sK0(sK3,X0,X1),X1) = iProver_top
% 3.16/0.96      | r2_hidden(sK0(sK3,X0,X1),k1_xboole_0) = iProver_top ),
% 3.16/0.96      inference(superposition,[status(thm)],[c_324,c_1156]) ).
% 3.16/0.96  
% 3.16/0.96  cnf(c_8,plain,
% 3.16/0.96      ( k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
% 3.16/0.96      inference(cnf_transformation,[],[f48]) ).
% 3.16/0.96  
% 3.16/0.96  cnf(c_505,plain,
% 3.16/0.96      ( k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0 ),
% 3.16/0.96      inference(superposition,[status(thm)],[c_1,c_8]) ).
% 3.16/0.96  
% 3.16/0.96  cnf(c_1155,plain,
% 3.16/0.96      ( r2_hidden(X0,X1) = iProver_top
% 3.16/0.96      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.16/0.96      inference(superposition,[status(thm)],[c_505,c_322]) ).
% 3.16/0.96  
% 3.16/0.96  cnf(c_2676,plain,
% 3.16/0.96      ( k3_tarski(k2_tarski(sK3,X0)) = X1
% 3.16/0.96      | r2_hidden(sK0(sK3,X0,X1),X0) = iProver_top
% 3.16/0.96      | r2_hidden(sK0(sK3,X0,X1),X1) = iProver_top ),
% 3.16/0.96      inference(forward_subsumption_resolution,[status(thm)],[c_2274,c_1155]) ).
% 3.16/0.96  
% 3.16/0.96  cnf(c_5,plain,
% 3.16/0.96      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k3_tarski(k2_tarski(X2,X1))) ),
% 3.16/0.96      inference(cnf_transformation,[],[f51]) ).
% 3.16/0.96  
% 3.16/0.96  cnf(c_323,plain,
% 3.16/0.96      ( r2_hidden(X0,X1) != iProver_top
% 3.16/0.96      | r2_hidden(X0,k3_tarski(k2_tarski(X2,X1))) = iProver_top ),
% 3.16/0.96      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.16/0.96  
% 3.16/0.96  cnf(c_1399,plain,
% 3.16/0.96      ( r2_hidden(X0,k2_tarski(sK1,sK2)) != iProver_top
% 3.16/0.96      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 3.16/0.96      inference(superposition,[status(thm)],[c_507,c_323]) ).
% 3.16/0.96  
% 3.16/0.96  cnf(c_2693,plain,
% 3.16/0.96      ( k3_tarski(k2_tarski(sK3,k2_tarski(sK1,sK2))) = X0
% 3.16/0.96      | r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),X0),X0) = iProver_top
% 3.16/0.96      | r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),X0),k1_xboole_0) = iProver_top ),
% 3.16/0.96      inference(superposition,[status(thm)],[c_2676,c_1399]) ).
% 3.16/0.96  
% 3.16/0.96  cnf(c_2718,plain,
% 3.16/0.96      ( k1_xboole_0 = X0
% 3.16/0.96      | r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),X0),X0) = iProver_top
% 3.16/0.96      | r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),X0),k1_xboole_0) = iProver_top ),
% 3.16/0.96      inference(demodulation,[status(thm)],[c_2693,c_507]) ).
% 3.16/0.96  
% 3.16/0.96  cnf(c_3028,plain,
% 3.16/0.96      ( k1_xboole_0 = X0
% 3.16/0.96      | r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),X0),X0) = iProver_top ),
% 3.16/0.96      inference(forward_subsumption_resolution,[status(thm)],[c_2718,c_1155]) ).
% 3.16/0.96  
% 3.16/0.96  cnf(c_2,plain,
% 3.16/0.96      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 3.16/0.96      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 3.16/0.96      | k3_tarski(k2_tarski(X0,X1)) = X2 ),
% 3.16/0.96      inference(cnf_transformation,[],[f42]) ).
% 3.16/0.96  
% 3.16/0.96  cnf(c_326,plain,
% 3.16/0.96      ( k3_tarski(k2_tarski(X0,X1)) = X2
% 3.16/0.96      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
% 3.16/0.96      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top ),
% 3.16/0.96      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.16/0.96  
% 3.16/0.96  cnf(c_3030,plain,
% 3.16/0.96      ( k2_tarski(sK1,sK2) = k1_xboole_0
% 3.16/0.96      | k3_tarski(k2_tarski(sK3,k2_tarski(sK1,sK2))) = k2_tarski(sK1,sK2)
% 3.16/0.96      | r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2)) != iProver_top ),
% 3.16/0.96      inference(superposition,[status(thm)],[c_3028,c_326]) ).
% 3.16/0.96  
% 3.16/0.96  cnf(c_3070,plain,
% 3.16/0.96      ( k2_tarski(sK1,sK2) = k1_xboole_0
% 3.16/0.96      | r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2)) != iProver_top ),
% 3.16/0.96      inference(light_normalisation,[status(thm)],[c_3030,c_507]) ).
% 3.16/0.96  
% 3.16/0.96  cnf(c_0,plain,
% 3.16/0.96      ( k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) = k2_tarski(X0,X1) ),
% 3.16/0.96      inference(cnf_transformation,[],[f40]) ).
% 3.16/0.96  
% 3.16/0.96  cnf(c_14,plain,
% 3.16/0.96      ( k3_tarski(k2_tarski(k1_tarski(X0),X1)) != k1_xboole_0 ),
% 3.16/0.96      inference(cnf_transformation,[],[f49]) ).
% 3.16/0.96  
% 3.16/0.96  cnf(c_662,plain,
% 3.16/0.96      ( k2_tarski(X0,X1) != k1_xboole_0 ),
% 3.16/0.96      inference(superposition,[status(thm)],[c_0,c_14]) ).
% 3.16/0.96  
% 3.16/0.96  cnf(c_3230,plain,
% 3.16/0.96      ( r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),k2_tarski(sK1,sK2)),k2_tarski(sK1,sK2)) != iProver_top ),
% 3.16/0.96      inference(forward_subsumption_resolution,[status(thm)],[c_3070,c_662]) ).
% 3.16/0.96  
% 3.16/0.96  cnf(c_3238,plain,
% 3.16/0.96      ( k2_tarski(sK1,sK2) = k1_xboole_0 ),
% 3.16/0.96      inference(superposition,[status(thm)],[c_3028,c_3230]) ).
% 3.16/0.96  
% 3.16/0.96  cnf(c_7996,plain,
% 3.16/0.96      ( $false ),
% 3.16/0.96      inference(forward_subsumption_resolution,[status(thm)],[c_3238,c_662]) ).
% 3.16/0.96  
% 3.16/0.96  
% 3.16/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 3.16/0.96  
% 3.16/0.96  ------                               Statistics
% 3.16/0.96  
% 3.16/0.96  ------ General
% 3.16/0.96  
% 3.16/0.96  abstr_ref_over_cycles:                  0
% 3.16/0.96  abstr_ref_under_cycles:                 0
% 3.16/0.96  gc_basic_clause_elim:                   0
% 3.16/0.96  forced_gc_time:                         0
% 3.16/0.96  parsing_time:                           0.008
% 3.16/0.96  unif_index_cands_time:                  0.
% 3.16/0.96  unif_index_add_time:                    0.
% 3.16/0.96  orderings_time:                         0.
% 3.16/0.96  out_proof_time:                         0.007
% 3.16/0.96  total_time:                             0.233
% 3.16/0.96  num_of_symbols:                         42
% 3.16/0.96  num_of_terms:                           8546
% 3.16/0.96  
% 3.16/0.96  ------ Preprocessing
% 3.16/0.96  
% 3.16/0.96  num_of_splits:                          0
% 3.16/0.96  num_of_split_atoms:                     0
% 3.16/0.96  num_of_reused_defs:                     0
% 3.16/0.96  num_eq_ax_congr_red:                    21
% 3.16/0.96  num_of_sem_filtered_clauses:            1
% 3.16/0.96  num_of_subtypes:                        0
% 3.16/0.96  monotx_restored_types:                  0
% 3.16/0.96  sat_num_of_epr_types:                   0
% 3.16/0.96  sat_num_of_non_cyclic_types:            0
% 3.16/0.96  sat_guarded_non_collapsed_types:        0
% 3.16/0.96  num_pure_diseq_elim:                    0
% 3.16/0.96  simp_replaced_by:                       0
% 3.16/0.96  res_preprocessed:                       66
% 3.16/0.96  prep_upred:                             0
% 3.16/0.96  prep_unflattend:                        2
% 3.16/0.96  smt_new_axioms:                         0
% 3.16/0.96  pred_elim_cands:                        1
% 3.16/0.96  pred_elim:                              1
% 3.16/0.96  pred_elim_cl:                           3
% 3.16/0.96  pred_elim_cycles:                       3
% 3.16/0.96  merged_defs:                            0
% 3.16/0.96  merged_defs_ncl:                        0
% 3.16/0.96  bin_hyper_res:                          0
% 3.16/0.96  prep_cycles:                            4
% 3.16/0.96  pred_elim_time:                         0.
% 3.16/0.96  splitting_time:                         0.
% 3.16/0.96  sem_filter_time:                        0.
% 3.16/0.96  monotx_time:                            0.
% 3.16/0.96  subtype_inf_time:                       0.
% 3.16/0.96  
% 3.16/0.96  ------ Problem properties
% 3.16/0.96  
% 3.16/0.96  clauses:                                13
% 3.16/0.96  conjectures:                            1
% 3.16/0.96  epr:                                    0
% 3.16/0.96  horn:                                   11
% 3.16/0.96  ground:                                 1
% 3.16/0.96  unary:                                  6
% 3.16/0.96  binary:                                 2
% 3.16/0.96  lits:                                   26
% 3.16/0.96  lits_eq:                                10
% 3.16/0.96  fd_pure:                                0
% 3.16/0.96  fd_pseudo:                              0
% 3.16/0.96  fd_cond:                                0
% 3.16/0.96  fd_pseudo_cond:                         3
% 3.16/0.96  ac_symbols:                             0
% 3.16/0.96  
% 3.16/0.96  ------ Propositional Solver
% 3.16/0.96  
% 3.16/0.96  prop_solver_calls:                      29
% 3.16/0.96  prop_fast_solver_calls:                 483
% 3.16/0.96  smt_solver_calls:                       0
% 3.16/0.96  smt_fast_solver_calls:                  0
% 3.16/0.96  prop_num_of_clauses:                    2313
% 3.16/0.96  prop_preprocess_simplified:             5813
% 3.16/0.96  prop_fo_subsumed:                       4
% 3.16/0.96  prop_solver_time:                       0.
% 3.16/0.96  smt_solver_time:                        0.
% 3.16/0.96  smt_fast_solver_time:                   0.
% 3.16/0.96  prop_fast_solver_time:                  0.
% 3.16/0.96  prop_unsat_core_time:                   0.
% 3.16/0.96  
% 3.16/0.96  ------ QBF
% 3.16/0.96  
% 3.16/0.96  qbf_q_res:                              0
% 3.16/0.96  qbf_num_tautologies:                    0
% 3.16/0.96  qbf_prep_cycles:                        0
% 3.16/0.96  
% 3.16/0.96  ------ BMC1
% 3.16/0.96  
% 3.16/0.96  bmc1_current_bound:                     -1
% 3.16/0.96  bmc1_last_solved_bound:                 -1
% 3.16/0.96  bmc1_unsat_core_size:                   -1
% 3.16/0.96  bmc1_unsat_core_parents_size:           -1
% 3.16/0.96  bmc1_merge_next_fun:                    0
% 3.16/0.96  bmc1_unsat_core_clauses_time:           0.
% 3.16/0.96  
% 3.16/0.96  ------ Instantiation
% 3.16/0.96  
% 3.16/0.96  inst_num_of_clauses:                    743
% 3.16/0.96  inst_num_in_passive:                    362
% 3.16/0.96  inst_num_in_active:                     283
% 3.16/0.96  inst_num_in_unprocessed:                98
% 3.16/0.96  inst_num_of_loops:                      300
% 3.16/0.96  inst_num_of_learning_restarts:          0
% 3.16/0.96  inst_num_moves_active_passive:          15
% 3.16/0.96  inst_lit_activity:                      0
% 3.16/0.96  inst_lit_activity_moves:                0
% 3.16/0.96  inst_num_tautologies:                   0
% 3.16/0.96  inst_num_prop_implied:                  0
% 3.16/0.96  inst_num_existing_simplified:           0
% 3.16/0.96  inst_num_eq_res_simplified:             0
% 3.16/0.96  inst_num_child_elim:                    0
% 3.16/0.96  inst_num_of_dismatching_blockings:      689
% 3.16/0.96  inst_num_of_non_proper_insts:           874
% 3.16/0.96  inst_num_of_duplicates:                 0
% 3.16/0.96  inst_inst_num_from_inst_to_res:         0
% 3.16/0.96  inst_dismatching_checking_time:         0.
% 3.16/0.96  
% 3.16/0.96  ------ Resolution
% 3.16/0.96  
% 3.16/0.96  res_num_of_clauses:                     0
% 3.16/0.96  res_num_in_passive:                     0
% 3.16/0.96  res_num_in_active:                      0
% 3.16/0.96  res_num_of_loops:                       70
% 3.16/0.96  res_forward_subset_subsumed:            109
% 3.16/0.96  res_backward_subset_subsumed:           0
% 3.16/0.96  res_forward_subsumed:                   0
% 3.16/0.96  res_backward_subsumed:                  0
% 3.16/0.96  res_forward_subsumption_resolution:     0
% 3.16/0.96  res_backward_subsumption_resolution:    0
% 3.16/0.96  res_clause_to_clause_subsumption:       1744
% 3.16/0.96  res_orphan_elimination:                 0
% 3.16/0.96  res_tautology_del:                      130
% 3.16/0.96  res_num_eq_res_simplified:              0
% 3.16/0.96  res_num_sel_changes:                    0
% 3.16/0.96  res_moves_from_active_to_pass:          0
% 3.16/0.96  
% 3.16/0.96  ------ Superposition
% 3.16/0.96  
% 3.16/0.96  sup_time_total:                         0.
% 3.16/0.96  sup_time_generating:                    0.
% 3.16/0.96  sup_time_sim_full:                      0.
% 3.16/0.96  sup_time_sim_immed:                     0.
% 3.16/0.96  
% 3.16/0.96  sup_num_of_clauses:                     212
% 3.16/0.96  sup_num_in_active:                      46
% 3.16/0.96  sup_num_in_passive:                     166
% 3.16/0.96  sup_num_of_loops:                       59
% 3.16/0.96  sup_fw_superposition:                   155
% 3.16/0.96  sup_bw_superposition:                   366
% 3.16/0.96  sup_immediate_simplified:               152
% 3.16/0.96  sup_given_eliminated:                   4
% 3.16/0.96  comparisons_done:                       0
% 3.16/0.96  comparisons_avoided:                    0
% 3.16/0.96  
% 3.16/0.96  ------ Simplifications
% 3.16/0.96  
% 3.16/0.96  
% 3.16/0.96  sim_fw_subset_subsumed:                 64
% 3.16/0.96  sim_bw_subset_subsumed:                 18
% 3.16/0.96  sim_fw_subsumed:                        40
% 3.16/0.96  sim_bw_subsumed:                        1
% 3.16/0.96  sim_fw_subsumption_res:                 20
% 3.16/0.96  sim_bw_subsumption_res:                 0
% 3.16/0.96  sim_tautology_del:                      37
% 3.16/0.96  sim_eq_tautology_del:                   50
% 3.16/0.96  sim_eq_res_simp:                        15
% 3.16/0.96  sim_fw_demodulated:                     53
% 3.16/0.96  sim_bw_demodulated:                     9
% 3.16/0.96  sim_light_normalised:                   22
% 3.16/0.96  sim_joinable_taut:                      0
% 3.16/0.96  sim_joinable_simp:                      0
% 3.16/0.96  sim_ac_normalised:                      0
% 3.16/0.96  sim_smt_subsumption:                    0
% 3.16/0.96  
%------------------------------------------------------------------------------
