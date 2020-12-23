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
% DateTime   : Thu Dec  3 11:44:20 EST 2020

% Result     : Theorem 43.68s
% Output     : CNFRefutation 43.68s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 321 expanded)
%              Number of clauses        :   78 ( 133 expanded)
%              Number of leaves         :   20 (  80 expanded)
%              Depth                    :   13
%              Number of atoms          :  287 ( 724 expanded)
%              Number of equality atoms :  154 ( 279 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f53,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f37,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f34,plain,(
    ! [X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
     => r2_hidden(sK2(X1),k1_relat_1(X1)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f34])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f36,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f51,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f32])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f57,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f42,f46])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f59,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f44,f46])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f52,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f61,plain,(
    ! [X0] :
      ( k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0))) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f52,f46])).

fof(f17,conjecture,(
    k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f17])).

fof(f20,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(flattening,[],[f18])).

fof(f55,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_14,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_200221,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_200228,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK2(X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_200220,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK2(X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_201250,plain,
    ( r2_hidden(sK2(X0),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_xboole_0(k2_relat_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_200228,c_200220])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_200227,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_203379,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_xboole_0(k2_relat_1(X0)) = iProver_top
    | v1_xboole_0(k1_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_201250,c_200227])).

cnf(c_203400,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_relat_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_200221,c_203379])).

cnf(c_20,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_12,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_26,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_203548,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_relat_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_203400,c_20,c_26,c_203379])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_200226,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_203570,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_203548,c_200226])).

cnf(c_203674,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_203570])).

cnf(c_135,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_200317,plain,
    ( k3_relat_1(k1_xboole_0) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_135])).

cnf(c_203528,plain,
    ( k3_relat_1(k1_xboole_0) != k5_xboole_0(X0,X1)
    | k1_xboole_0 != k5_xboole_0(X0,X1)
    | k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_200317])).

cnf(c_203529,plain,
    ( k3_relat_1(k1_xboole_0) != k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_203528])).

cnf(c_139,plain,
    ( X0 != X1
    | X2 != X3
    | k4_xboole_0(X0,X2) = k4_xboole_0(X1,X3) ),
    theory(equality)).

cnf(c_200831,plain,
    ( k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0)) = k4_xboole_0(X0,X1)
    | k2_relat_1(k1_xboole_0) != X0
    | k1_relat_1(k1_xboole_0) != X1 ),
    inference(instantiation,[status(thm)],[c_139])).

cnf(c_200832,plain,
    ( k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_200831])).

cnf(c_200708,plain,
    ( X0 != X1
    | X0 = k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0))
    | k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0)) != X1 ),
    inference(instantiation,[status(thm)],[c_135])).

cnf(c_200802,plain,
    ( X0 != k4_xboole_0(X1,X2)
    | X0 = k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0))
    | k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0)) != k4_xboole_0(X1,X2) ),
    inference(instantiation,[status(thm)],[c_200708])).

cnf(c_200803,plain,
    ( k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0)) != k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0))
    | k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_200802])).

cnf(c_200702,plain,
    ( X0 != X1
    | X0 = k1_relat_1(k1_xboole_0)
    | k1_relat_1(k1_xboole_0) != X1 ),
    inference(instantiation,[status(thm)],[c_135])).

cnf(c_200703,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_200702])).

cnf(c_200664,plain,
    ( k1_relat_1(X0) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_200221,c_200226])).

cnf(c_200677,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_200664])).

cnf(c_140,plain,
    ( X0 != X1
    | X2 != X3
    | k5_xboole_0(X0,X2) = k5_xboole_0(X1,X3) ),
    theory(equality)).

cnf(c_200642,plain,
    ( X0 != k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0))
    | X1 != k1_relat_1(k1_xboole_0)
    | k5_xboole_0(X1,X0) = k5_xboole_0(k1_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_140])).

cnf(c_200643,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0)))
    | k1_xboole_0 != k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0))
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_200642])).

cnf(c_200328,plain,
    ( X0 != X1
    | k3_relat_1(k1_xboole_0) != X1
    | k3_relat_1(k1_xboole_0) = X0 ),
    inference(instantiation,[status(thm)],[c_135])).

cnf(c_200405,plain,
    ( X0 != k5_xboole_0(k1_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0)))
    | k3_relat_1(k1_xboole_0) = X0
    | k3_relat_1(k1_xboole_0) != k5_xboole_0(k1_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_200328])).

cnf(c_200634,plain,
    ( k5_xboole_0(X0,X1) != k5_xboole_0(k1_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0)))
    | k3_relat_1(k1_xboole_0) = k5_xboole_0(X0,X1)
    | k3_relat_1(k1_xboole_0) != k5_xboole_0(k1_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_200405])).

cnf(c_200635,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) != k5_xboole_0(k1_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0)))
    | k3_relat_1(k1_xboole_0) != k5_xboole_0(k1_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0)))
    | k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_200634])).

cnf(c_200381,plain,
    ( X0 != k3_relat_1(k1_xboole_0)
    | k3_relat_1(k1_xboole_0) = X0
    | k3_relat_1(k1_xboole_0) != k3_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_200328])).

cnf(c_200382,plain,
    ( X0 != k3_relat_1(k1_xboole_0)
    | k3_relat_1(k1_xboole_0) = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_200381])).

cnf(c_200392,plain,
    ( k5_xboole_0(k1_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0))) != k3_relat_1(k1_xboole_0)
    | k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_200382])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_44824,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(sK0(X1),X0)
    | v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_3,c_0])).

cnf(c_74519,plain,
    ( ~ r1_xboole_0(X0,X0)
    | v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_44824,c_0])).

cnf(c_9,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_170615,plain,
    ( v1_xboole_0(k4_xboole_0(X0,X0)) ),
    inference(resolution,[status(thm)],[c_74519,c_9])).

cnf(c_170617,plain,
    ( v1_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_170615])).

cnf(c_5006,plain,
    ( ~ v1_xboole_0(X0)
    | X1 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution,[status(thm)],[c_2,c_135])).

cnf(c_9015,plain,
    ( ~ v1_xboole_0(k5_xboole_0(X0,X1))
    | X2 != X0
    | X3 != X1
    | k1_xboole_0 = k5_xboole_0(X2,X3) ),
    inference(resolution,[status(thm)],[c_5006,c_140])).

cnf(c_9017,plain,
    ( ~ v1_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9015])).

cnf(c_9011,plain,
    ( ~ v1_xboole_0(k4_xboole_0(X0,X1))
    | X2 != X0
    | X3 != X1
    | k1_xboole_0 = k4_xboole_0(X2,X3) ),
    inference(resolution,[status(thm)],[c_5006,c_139])).

cnf(c_9013,plain,
    ( ~ v1_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9011])).

cnf(c_136,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_7249,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k5_xboole_0(X1,X2))
    | k5_xboole_0(X1,X2) != X0 ),
    inference(instantiation,[status(thm)],[c_136])).

cnf(c_7251,plain,
    ( v1_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0)
    | k5_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7249])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_3375,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_8])).

cnf(c_3210,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3536,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3375,c_3210])).

cnf(c_3541,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3536,c_3375])).

cnf(c_3563,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3541])).

cnf(c_3389,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3375,c_6])).

cnf(c_837,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(sK0(X1),X0)
    | v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_3,c_0])).

cnf(c_849,plain,
    ( ~ r1_xboole_0(X0,X0)
    | v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_837,c_0])).

cnf(c_850,plain,
    ( r1_xboole_0(X0,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_849])).

cnf(c_852,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_850])).

cnf(c_851,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_849])).

cnf(c_134,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_151,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_134])).

cnf(c_28,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0))) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_23,plain,
    ( k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0))) = k3_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_25,plain,
    ( k5_xboole_0(k1_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0))) = k3_relat_1(k1_xboole_0)
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f55])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_203674,c_203529,c_200832,c_200803,c_200703,c_200677,c_200643,c_200635,c_200392,c_170617,c_9017,c_9013,c_7251,c_3563,c_3541,c_3389,c_852,c_851,c_151,c_28,c_25,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:05:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 43.68/6.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 43.68/6.02  
% 43.68/6.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 43.68/6.02  
% 43.68/6.02  ------  iProver source info
% 43.68/6.02  
% 43.68/6.02  git: date: 2020-06-30 10:37:57 +0100
% 43.68/6.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 43.68/6.02  git: non_committed_changes: false
% 43.68/6.02  git: last_make_outside_of_git: false
% 43.68/6.02  
% 43.68/6.02  ------ 
% 43.68/6.02  ------ Parsing...
% 43.68/6.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 43.68/6.02  
% 43.68/6.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 43.68/6.02  
% 43.68/6.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 43.68/6.02  
% 43.68/6.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.68/6.02  ------ Proving...
% 43.68/6.02  ------ Problem Properties 
% 43.68/6.02  
% 43.68/6.02  
% 43.68/6.02  clauses                                 17
% 43.68/6.02  conjectures                             1
% 43.68/6.02  EPR                                     4
% 43.68/6.02  Horn                                    14
% 43.68/6.02  unary                                   7
% 43.68/6.02  binary                                  8
% 43.68/6.02  lits                                    29
% 43.68/6.02  lits eq                                 7
% 43.68/6.02  fd_pure                                 0
% 43.68/6.02  fd_pseudo                               0
% 43.68/6.02  fd_cond                                 1
% 43.68/6.02  fd_pseudo_cond                          0
% 43.68/6.02  AC symbols                              0
% 43.68/6.02  
% 43.68/6.02  ------ Input Options Time Limit: Unbounded
% 43.68/6.02  
% 43.68/6.02  
% 43.68/6.02  
% 43.68/6.02  
% 43.68/6.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 43.68/6.02  Current options:
% 43.68/6.02  ------ 
% 43.68/6.02  
% 43.68/6.02  
% 43.68/6.02  
% 43.68/6.02  
% 43.68/6.02  ------ Proving...
% 43.68/6.02  
% 43.68/6.02  
% 43.68/6.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.68/6.02  
% 43.68/6.02  ------ Proving...
% 43.68/6.02  
% 43.68/6.02  
% 43.68/6.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.68/6.02  
% 43.68/6.02  ------ Proving...
% 43.68/6.02  
% 43.68/6.02  
% 43.68/6.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.68/6.02  
% 43.68/6.02  ------ Proving...
% 43.68/6.02  
% 43.68/6.02  
% 43.68/6.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.68/6.02  
% 43.68/6.02  ------ Proving...
% 43.68/6.02  
% 43.68/6.02  
% 43.68/6.02  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.68/6.02  
% 43.68/6.02  ------ Proving...
% 43.68/6.02  
% 43.68/6.02  
% 43.68/6.02  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.68/6.02  
% 43.68/6.02  ------ Proving...
% 43.68/6.02  
% 43.68/6.02  
% 43.68/6.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.68/6.02  
% 43.68/6.02  ------ Proving...
% 43.68/6.02  
% 43.68/6.02  
% 43.68/6.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.68/6.02  
% 43.68/6.02  ------ Proving...
% 43.68/6.02  
% 43.68/6.02  
% 43.68/6.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.68/6.02  
% 43.68/6.02  ------ Proving...
% 43.68/6.02  
% 43.68/6.02  
% 43.68/6.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.68/6.02  
% 43.68/6.02  ------ Proving...
% 43.68/6.02  
% 43.68/6.02  
% 43.68/6.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.68/6.02  
% 43.68/6.02  ------ Proving...
% 43.68/6.02  
% 43.68/6.02  
% 43.68/6.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.68/6.02  
% 43.68/6.02  ------ Proving...
% 43.68/6.02  
% 43.68/6.02  
% 43.68/6.02  % SZS status Theorem for theBenchmark.p
% 43.68/6.02  
% 43.68/6.02  % SZS output start CNFRefutation for theBenchmark.p
% 43.68/6.02  
% 43.68/6.02  fof(f15,axiom,(
% 43.68/6.02    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 43.68/6.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.68/6.02  
% 43.68/6.02  fof(f25,plain,(
% 43.68/6.02    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 43.68/6.02    inference(ennf_transformation,[],[f15])).
% 43.68/6.02  
% 43.68/6.02  fof(f53,plain,(
% 43.68/6.02    ( ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 43.68/6.02    inference(cnf_transformation,[],[f25])).
% 43.68/6.02  
% 43.68/6.02  fof(f1,axiom,(
% 43.68/6.02    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 43.68/6.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.68/6.02  
% 43.68/6.02  fof(f28,plain,(
% 43.68/6.02    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 43.68/6.02    inference(nnf_transformation,[],[f1])).
% 43.68/6.02  
% 43.68/6.02  fof(f29,plain,(
% 43.68/6.02    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 43.68/6.02    inference(rectify,[],[f28])).
% 43.68/6.02  
% 43.68/6.02  fof(f30,plain,(
% 43.68/6.02    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 43.68/6.02    introduced(choice_axiom,[])).
% 43.68/6.02  
% 43.68/6.02  fof(f31,plain,(
% 43.68/6.02    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 43.68/6.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 43.68/6.02  
% 43.68/6.02  fof(f37,plain,(
% 43.68/6.02    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 43.68/6.02    inference(cnf_transformation,[],[f31])).
% 43.68/6.02  
% 43.68/6.02  fof(f16,axiom,(
% 43.68/6.02    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k1_relat_1(X1)) & r2_hidden(X0,k2_relat_1(X1))))),
% 43.68/6.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.68/6.02  
% 43.68/6.02  fof(f26,plain,(
% 43.68/6.02    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 43.68/6.02    inference(ennf_transformation,[],[f16])).
% 43.68/6.02  
% 43.68/6.02  fof(f27,plain,(
% 43.68/6.02    ! [X0,X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 43.68/6.02    inference(flattening,[],[f26])).
% 43.68/6.02  
% 43.68/6.02  fof(f34,plain,(
% 43.68/6.02    ! [X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(sK2(X1),k1_relat_1(X1)))),
% 43.68/6.02    introduced(choice_axiom,[])).
% 43.68/6.02  
% 43.68/6.02  fof(f35,plain,(
% 43.68/6.02    ! [X0,X1] : (r2_hidden(sK2(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 43.68/6.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f34])).
% 43.68/6.02  
% 43.68/6.02  fof(f54,plain,(
% 43.68/6.02    ( ! [X0,X1] : (r2_hidden(sK2(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 43.68/6.02    inference(cnf_transformation,[],[f35])).
% 43.68/6.02  
% 43.68/6.02  fof(f36,plain,(
% 43.68/6.02    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 43.68/6.02    inference(cnf_transformation,[],[f31])).
% 43.68/6.02  
% 43.68/6.02  fof(f13,axiom,(
% 43.68/6.02    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 43.68/6.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.68/6.02  
% 43.68/6.02  fof(f23,plain,(
% 43.68/6.02    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 43.68/6.02    inference(ennf_transformation,[],[f13])).
% 43.68/6.02  
% 43.68/6.02  fof(f51,plain,(
% 43.68/6.02    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 43.68/6.02    inference(cnf_transformation,[],[f23])).
% 43.68/6.02  
% 43.68/6.02  fof(f2,axiom,(
% 43.68/6.02    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 43.68/6.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.68/6.02  
% 43.68/6.02  fof(f21,plain,(
% 43.68/6.02    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 43.68/6.02    inference(ennf_transformation,[],[f2])).
% 43.68/6.02  
% 43.68/6.02  fof(f38,plain,(
% 43.68/6.02    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 43.68/6.02    inference(cnf_transformation,[],[f21])).
% 43.68/6.02  
% 43.68/6.02  fof(f3,axiom,(
% 43.68/6.02    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 43.68/6.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.68/6.02  
% 43.68/6.02  fof(f19,plain,(
% 43.68/6.02    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 43.68/6.02    inference(rectify,[],[f3])).
% 43.68/6.02  
% 43.68/6.02  fof(f22,plain,(
% 43.68/6.02    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 43.68/6.02    inference(ennf_transformation,[],[f19])).
% 43.68/6.02  
% 43.68/6.02  fof(f32,plain,(
% 43.68/6.02    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 43.68/6.02    introduced(choice_axiom,[])).
% 43.68/6.02  
% 43.68/6.02  fof(f33,plain,(
% 43.68/6.02    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 43.68/6.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f32])).
% 43.68/6.02  
% 43.68/6.02  fof(f41,plain,(
% 43.68/6.02    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 43.68/6.02    inference(cnf_transformation,[],[f33])).
% 43.68/6.02  
% 43.68/6.02  fof(f7,axiom,(
% 43.68/6.02    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 43.68/6.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.68/6.02  
% 43.68/6.02  fof(f45,plain,(
% 43.68/6.02    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 43.68/6.02    inference(cnf_transformation,[],[f7])).
% 43.68/6.02  
% 43.68/6.02  fof(f4,axiom,(
% 43.68/6.02    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 43.68/6.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.68/6.02  
% 43.68/6.02  fof(f42,plain,(
% 43.68/6.02    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 43.68/6.02    inference(cnf_transformation,[],[f4])).
% 43.68/6.02  
% 43.68/6.02  fof(f8,axiom,(
% 43.68/6.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 43.68/6.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.68/6.02  
% 43.68/6.02  fof(f46,plain,(
% 43.68/6.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 43.68/6.02    inference(cnf_transformation,[],[f8])).
% 43.68/6.02  
% 43.68/6.02  fof(f57,plain,(
% 43.68/6.02    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 43.68/6.02    inference(definition_unfolding,[],[f42,f46])).
% 43.68/6.02  
% 43.68/6.02  fof(f6,axiom,(
% 43.68/6.02    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 43.68/6.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.68/6.02  
% 43.68/6.02  fof(f44,plain,(
% 43.68/6.02    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 43.68/6.02    inference(cnf_transformation,[],[f6])).
% 43.68/6.02  
% 43.68/6.02  fof(f59,plain,(
% 43.68/6.02    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 43.68/6.02    inference(definition_unfolding,[],[f44,f46])).
% 43.68/6.02  
% 43.68/6.02  fof(f14,axiom,(
% 43.68/6.02    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 43.68/6.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.68/6.02  
% 43.68/6.02  fof(f24,plain,(
% 43.68/6.02    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 43.68/6.02    inference(ennf_transformation,[],[f14])).
% 43.68/6.02  
% 43.68/6.02  fof(f52,plain,(
% 43.68/6.02    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 43.68/6.02    inference(cnf_transformation,[],[f24])).
% 43.68/6.02  
% 43.68/6.02  fof(f61,plain,(
% 43.68/6.02    ( ! [X0] : (k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0))) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 43.68/6.02    inference(definition_unfolding,[],[f52,f46])).
% 43.68/6.02  
% 43.68/6.02  fof(f17,conjecture,(
% 43.68/6.02    k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 43.68/6.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.68/6.02  
% 43.68/6.02  fof(f18,negated_conjecture,(
% 43.68/6.02    ~k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 43.68/6.02    inference(negated_conjecture,[],[f17])).
% 43.68/6.02  
% 43.68/6.02  fof(f20,plain,(
% 43.68/6.02    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 43.68/6.02    inference(flattening,[],[f18])).
% 43.68/6.02  
% 43.68/6.02  fof(f55,plain,(
% 43.68/6.02    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 43.68/6.02    inference(cnf_transformation,[],[f20])).
% 43.68/6.02  
% 43.68/6.02  cnf(c_14,plain,
% 43.68/6.02      ( ~ v1_xboole_0(X0) | v1_xboole_0(k1_relat_1(X0)) ),
% 43.68/6.02      inference(cnf_transformation,[],[f53]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_200221,plain,
% 43.68/6.02      ( v1_xboole_0(X0) != iProver_top
% 43.68/6.02      | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
% 43.68/6.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_0,plain,
% 43.68/6.02      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 43.68/6.02      inference(cnf_transformation,[],[f37]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_200228,plain,
% 43.68/6.02      ( r2_hidden(sK0(X0),X0) = iProver_top
% 43.68/6.02      | v1_xboole_0(X0) = iProver_top ),
% 43.68/6.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_15,plain,
% 43.68/6.02      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 43.68/6.02      | r2_hidden(sK2(X1),k1_relat_1(X1))
% 43.68/6.02      | ~ v1_relat_1(X1) ),
% 43.68/6.02      inference(cnf_transformation,[],[f54]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_200220,plain,
% 43.68/6.02      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 43.68/6.02      | r2_hidden(sK2(X1),k1_relat_1(X1)) = iProver_top
% 43.68/6.02      | v1_relat_1(X1) != iProver_top ),
% 43.68/6.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_201250,plain,
% 43.68/6.02      ( r2_hidden(sK2(X0),k1_relat_1(X0)) = iProver_top
% 43.68/6.02      | v1_relat_1(X0) != iProver_top
% 43.68/6.02      | v1_xboole_0(k2_relat_1(X0)) = iProver_top ),
% 43.68/6.02      inference(superposition,[status(thm)],[c_200228,c_200220]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_1,plain,
% 43.68/6.02      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 43.68/6.02      inference(cnf_transformation,[],[f36]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_200227,plain,
% 43.68/6.02      ( r2_hidden(X0,X1) != iProver_top
% 43.68/6.02      | v1_xboole_0(X1) != iProver_top ),
% 43.68/6.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_203379,plain,
% 43.68/6.02      ( v1_relat_1(X0) != iProver_top
% 43.68/6.02      | v1_xboole_0(k2_relat_1(X0)) = iProver_top
% 43.68/6.02      | v1_xboole_0(k1_relat_1(X0)) != iProver_top ),
% 43.68/6.02      inference(superposition,[status(thm)],[c_201250,c_200227]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_203400,plain,
% 43.68/6.02      ( v1_relat_1(X0) != iProver_top
% 43.68/6.02      | v1_xboole_0(X0) != iProver_top
% 43.68/6.02      | v1_xboole_0(k2_relat_1(X0)) = iProver_top ),
% 43.68/6.02      inference(superposition,[status(thm)],[c_200221,c_203379]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_20,plain,
% 43.68/6.02      ( v1_xboole_0(X0) != iProver_top
% 43.68/6.02      | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
% 43.68/6.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_12,plain,
% 43.68/6.02      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 43.68/6.02      inference(cnf_transformation,[],[f51]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_26,plain,
% 43.68/6.02      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 43.68/6.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_203548,plain,
% 43.68/6.02      ( v1_xboole_0(X0) != iProver_top
% 43.68/6.02      | v1_xboole_0(k2_relat_1(X0)) = iProver_top ),
% 43.68/6.02      inference(global_propositional_subsumption,
% 43.68/6.02                [status(thm)],
% 43.68/6.02                [c_203400,c_20,c_26,c_203379]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_2,plain,
% 43.68/6.02      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 43.68/6.02      inference(cnf_transformation,[],[f38]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_200226,plain,
% 43.68/6.02      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 43.68/6.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_203570,plain,
% 43.68/6.02      ( k2_relat_1(X0) = k1_xboole_0 | v1_xboole_0(X0) != iProver_top ),
% 43.68/6.02      inference(superposition,[status(thm)],[c_203548,c_200226]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_203674,plain,
% 43.68/6.02      ( k2_relat_1(k1_xboole_0) = k1_xboole_0
% 43.68/6.02      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 43.68/6.02      inference(instantiation,[status(thm)],[c_203570]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_135,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_200317,plain,
% 43.68/6.02      ( k3_relat_1(k1_xboole_0) != X0
% 43.68/6.02      | k1_xboole_0 != X0
% 43.68/6.02      | k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
% 43.68/6.02      inference(instantiation,[status(thm)],[c_135]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_203528,plain,
% 43.68/6.02      ( k3_relat_1(k1_xboole_0) != k5_xboole_0(X0,X1)
% 43.68/6.02      | k1_xboole_0 != k5_xboole_0(X0,X1)
% 43.68/6.02      | k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
% 43.68/6.02      inference(instantiation,[status(thm)],[c_200317]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_203529,plain,
% 43.68/6.02      ( k3_relat_1(k1_xboole_0) != k5_xboole_0(k1_xboole_0,k1_xboole_0)
% 43.68/6.02      | k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0)
% 43.68/6.02      | k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
% 43.68/6.02      inference(instantiation,[status(thm)],[c_203528]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_139,plain,
% 43.68/6.02      ( X0 != X1 | X2 != X3 | k4_xboole_0(X0,X2) = k4_xboole_0(X1,X3) ),
% 43.68/6.02      theory(equality) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_200831,plain,
% 43.68/6.02      ( k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0)) = k4_xboole_0(X0,X1)
% 43.68/6.02      | k2_relat_1(k1_xboole_0) != X0
% 43.68/6.02      | k1_relat_1(k1_xboole_0) != X1 ),
% 43.68/6.02      inference(instantiation,[status(thm)],[c_139]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_200832,plain,
% 43.68/6.02      ( k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k1_xboole_0)
% 43.68/6.02      | k2_relat_1(k1_xboole_0) != k1_xboole_0
% 43.68/6.02      | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
% 43.68/6.02      inference(instantiation,[status(thm)],[c_200831]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_200708,plain,
% 43.68/6.02      ( X0 != X1
% 43.68/6.02      | X0 = k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0))
% 43.68/6.02      | k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0)) != X1 ),
% 43.68/6.02      inference(instantiation,[status(thm)],[c_135]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_200802,plain,
% 43.68/6.02      ( X0 != k4_xboole_0(X1,X2)
% 43.68/6.02      | X0 = k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0))
% 43.68/6.02      | k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0)) != k4_xboole_0(X1,X2) ),
% 43.68/6.02      inference(instantiation,[status(thm)],[c_200708]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_200803,plain,
% 43.68/6.02      ( k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0)) != k4_xboole_0(k1_xboole_0,k1_xboole_0)
% 43.68/6.02      | k1_xboole_0 = k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0))
% 43.68/6.02      | k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 43.68/6.02      inference(instantiation,[status(thm)],[c_200802]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_200702,plain,
% 43.68/6.02      ( X0 != X1
% 43.68/6.02      | X0 = k1_relat_1(k1_xboole_0)
% 43.68/6.02      | k1_relat_1(k1_xboole_0) != X1 ),
% 43.68/6.02      inference(instantiation,[status(thm)],[c_135]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_200703,plain,
% 43.68/6.02      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 43.68/6.02      | k1_xboole_0 = k1_relat_1(k1_xboole_0)
% 43.68/6.02      | k1_xboole_0 != k1_xboole_0 ),
% 43.68/6.02      inference(instantiation,[status(thm)],[c_200702]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_200664,plain,
% 43.68/6.02      ( k1_relat_1(X0) = k1_xboole_0 | v1_xboole_0(X0) != iProver_top ),
% 43.68/6.02      inference(superposition,[status(thm)],[c_200221,c_200226]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_200677,plain,
% 43.68/6.02      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
% 43.68/6.02      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 43.68/6.02      inference(instantiation,[status(thm)],[c_200664]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_140,plain,
% 43.68/6.02      ( X0 != X1 | X2 != X3 | k5_xboole_0(X0,X2) = k5_xboole_0(X1,X3) ),
% 43.68/6.02      theory(equality) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_200642,plain,
% 43.68/6.02      ( X0 != k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0))
% 43.68/6.02      | X1 != k1_relat_1(k1_xboole_0)
% 43.68/6.02      | k5_xboole_0(X1,X0) = k5_xboole_0(k1_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0))) ),
% 43.68/6.02      inference(instantiation,[status(thm)],[c_140]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_200643,plain,
% 43.68/6.02      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0)))
% 43.68/6.02      | k1_xboole_0 != k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0))
% 43.68/6.02      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 43.68/6.02      inference(instantiation,[status(thm)],[c_200642]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_200328,plain,
% 43.68/6.02      ( X0 != X1
% 43.68/6.02      | k3_relat_1(k1_xboole_0) != X1
% 43.68/6.02      | k3_relat_1(k1_xboole_0) = X0 ),
% 43.68/6.02      inference(instantiation,[status(thm)],[c_135]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_200405,plain,
% 43.68/6.02      ( X0 != k5_xboole_0(k1_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0)))
% 43.68/6.02      | k3_relat_1(k1_xboole_0) = X0
% 43.68/6.02      | k3_relat_1(k1_xboole_0) != k5_xboole_0(k1_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0))) ),
% 43.68/6.02      inference(instantiation,[status(thm)],[c_200328]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_200634,plain,
% 43.68/6.02      ( k5_xboole_0(X0,X1) != k5_xboole_0(k1_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0)))
% 43.68/6.02      | k3_relat_1(k1_xboole_0) = k5_xboole_0(X0,X1)
% 43.68/6.02      | k3_relat_1(k1_xboole_0) != k5_xboole_0(k1_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0))) ),
% 43.68/6.02      inference(instantiation,[status(thm)],[c_200405]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_200635,plain,
% 43.68/6.02      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) != k5_xboole_0(k1_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0)))
% 43.68/6.02      | k3_relat_1(k1_xboole_0) != k5_xboole_0(k1_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0)))
% 43.68/6.02      | k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 43.68/6.02      inference(instantiation,[status(thm)],[c_200634]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_200381,plain,
% 43.68/6.02      ( X0 != k3_relat_1(k1_xboole_0)
% 43.68/6.02      | k3_relat_1(k1_xboole_0) = X0
% 43.68/6.02      | k3_relat_1(k1_xboole_0) != k3_relat_1(k1_xboole_0) ),
% 43.68/6.02      inference(instantiation,[status(thm)],[c_200328]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_200382,plain,
% 43.68/6.02      ( X0 != k3_relat_1(k1_xboole_0) | k3_relat_1(k1_xboole_0) = X0 ),
% 43.68/6.02      inference(equality_resolution_simp,[status(thm)],[c_200381]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_200392,plain,
% 43.68/6.02      ( k5_xboole_0(k1_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0))) != k3_relat_1(k1_xboole_0)
% 43.68/6.02      | k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0))) ),
% 43.68/6.02      inference(instantiation,[status(thm)],[c_200382]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_3,plain,
% 43.68/6.02      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X0) | ~ r2_hidden(X2,X1) ),
% 43.68/6.02      inference(cnf_transformation,[],[f41]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_44824,plain,
% 43.68/6.02      ( ~ r1_xboole_0(X0,X1)
% 43.68/6.02      | ~ r2_hidden(sK0(X1),X0)
% 43.68/6.02      | v1_xboole_0(X1) ),
% 43.68/6.02      inference(resolution,[status(thm)],[c_3,c_0]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_74519,plain,
% 43.68/6.02      ( ~ r1_xboole_0(X0,X0) | v1_xboole_0(X0) ),
% 43.68/6.02      inference(resolution,[status(thm)],[c_44824,c_0]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_9,plain,
% 43.68/6.02      ( r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
% 43.68/6.02      inference(cnf_transformation,[],[f45]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_170615,plain,
% 43.68/6.02      ( v1_xboole_0(k4_xboole_0(X0,X0)) ),
% 43.68/6.02      inference(resolution,[status(thm)],[c_74519,c_9]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_170617,plain,
% 43.68/6.02      ( v1_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
% 43.68/6.02      inference(instantiation,[status(thm)],[c_170615]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_5006,plain,
% 43.68/6.02      ( ~ v1_xboole_0(X0) | X1 != X0 | k1_xboole_0 = X1 ),
% 43.68/6.02      inference(resolution,[status(thm)],[c_2,c_135]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_9015,plain,
% 43.68/6.02      ( ~ v1_xboole_0(k5_xboole_0(X0,X1))
% 43.68/6.02      | X2 != X0
% 43.68/6.02      | X3 != X1
% 43.68/6.02      | k1_xboole_0 = k5_xboole_0(X2,X3) ),
% 43.68/6.02      inference(resolution,[status(thm)],[c_5006,c_140]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_9017,plain,
% 43.68/6.02      ( ~ v1_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0))
% 43.68/6.02      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)
% 43.68/6.02      | k1_xboole_0 != k1_xboole_0 ),
% 43.68/6.02      inference(instantiation,[status(thm)],[c_9015]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_9011,plain,
% 43.68/6.02      ( ~ v1_xboole_0(k4_xboole_0(X0,X1))
% 43.68/6.02      | X2 != X0
% 43.68/6.02      | X3 != X1
% 43.68/6.02      | k1_xboole_0 = k4_xboole_0(X2,X3) ),
% 43.68/6.02      inference(resolution,[status(thm)],[c_5006,c_139]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_9013,plain,
% 43.68/6.02      ( ~ v1_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0))
% 43.68/6.02      | k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
% 43.68/6.02      | k1_xboole_0 != k1_xboole_0 ),
% 43.68/6.02      inference(instantiation,[status(thm)],[c_9011]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_136,plain,
% 43.68/6.02      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 43.68/6.02      theory(equality) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_7249,plain,
% 43.68/6.02      ( ~ v1_xboole_0(X0)
% 43.68/6.02      | v1_xboole_0(k5_xboole_0(X1,X2))
% 43.68/6.02      | k5_xboole_0(X1,X2) != X0 ),
% 43.68/6.02      inference(instantiation,[status(thm)],[c_136]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_7251,plain,
% 43.68/6.02      ( v1_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0))
% 43.68/6.02      | ~ v1_xboole_0(k1_xboole_0)
% 43.68/6.02      | k5_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 43.68/6.02      inference(instantiation,[status(thm)],[c_7249]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_6,plain,
% 43.68/6.02      ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
% 43.68/6.02      inference(cnf_transformation,[],[f57]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_8,plain,
% 43.68/6.02      ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 43.68/6.02      inference(cnf_transformation,[],[f59]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_3375,plain,
% 43.68/6.02      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 43.68/6.02      inference(superposition,[status(thm)],[c_6,c_8]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_3210,plain,
% 43.68/6.02      ( r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = iProver_top ),
% 43.68/6.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_3536,plain,
% 43.68/6.02      ( r1_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0) = iProver_top ),
% 43.68/6.02      inference(superposition,[status(thm)],[c_3375,c_3210]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_3541,plain,
% 43.68/6.02      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 43.68/6.02      inference(light_normalisation,[status(thm)],[c_3536,c_3375]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_3563,plain,
% 43.68/6.02      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 43.68/6.02      inference(predicate_to_equality_rev,[status(thm)],[c_3541]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_3389,plain,
% 43.68/6.02      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 43.68/6.02      inference(superposition,[status(thm)],[c_3375,c_6]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_837,plain,
% 43.68/6.02      ( ~ r1_xboole_0(X0,X1)
% 43.68/6.02      | ~ r2_hidden(sK0(X1),X0)
% 43.68/6.02      | v1_xboole_0(X1) ),
% 43.68/6.02      inference(resolution,[status(thm)],[c_3,c_0]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_849,plain,
% 43.68/6.02      ( ~ r1_xboole_0(X0,X0) | v1_xboole_0(X0) ),
% 43.68/6.02      inference(resolution,[status(thm)],[c_837,c_0]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_850,plain,
% 43.68/6.02      ( r1_xboole_0(X0,X0) != iProver_top
% 43.68/6.02      | v1_xboole_0(X0) = iProver_top ),
% 43.68/6.02      inference(predicate_to_equality,[status(thm)],[c_849]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_852,plain,
% 43.68/6.02      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
% 43.68/6.02      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 43.68/6.02      inference(instantiation,[status(thm)],[c_850]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_851,plain,
% 43.68/6.02      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 43.68/6.02      | v1_xboole_0(k1_xboole_0) ),
% 43.68/6.02      inference(instantiation,[status(thm)],[c_849]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_134,plain,( X0 = X0 ),theory(equality) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_151,plain,
% 43.68/6.02      ( k1_xboole_0 = k1_xboole_0 ),
% 43.68/6.02      inference(instantiation,[status(thm)],[c_134]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_28,plain,
% 43.68/6.02      ( v1_relat_1(k1_xboole_0) = iProver_top
% 43.68/6.02      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 43.68/6.02      inference(instantiation,[status(thm)],[c_26]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_13,plain,
% 43.68/6.02      ( ~ v1_relat_1(X0)
% 43.68/6.02      | k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0))) = k3_relat_1(X0) ),
% 43.68/6.02      inference(cnf_transformation,[],[f61]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_23,plain,
% 43.68/6.02      ( k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0))) = k3_relat_1(X0)
% 43.68/6.02      | v1_relat_1(X0) != iProver_top ),
% 43.68/6.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_25,plain,
% 43.68/6.02      ( k5_xboole_0(k1_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0))) = k3_relat_1(k1_xboole_0)
% 43.68/6.02      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 43.68/6.02      inference(instantiation,[status(thm)],[c_23]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(c_16,negated_conjecture,
% 43.68/6.02      ( k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
% 43.68/6.02      inference(cnf_transformation,[],[f55]) ).
% 43.68/6.02  
% 43.68/6.02  cnf(contradiction,plain,
% 43.68/6.02      ( $false ),
% 43.68/6.02      inference(minisat,
% 43.68/6.02                [status(thm)],
% 43.68/6.02                [c_203674,c_203529,c_200832,c_200803,c_200703,c_200677,
% 43.68/6.02                 c_200643,c_200635,c_200392,c_170617,c_9017,c_9013,
% 43.68/6.02                 c_7251,c_3563,c_3541,c_3389,c_852,c_851,c_151,c_28,c_25,
% 43.68/6.02                 c_16]) ).
% 43.68/6.02  
% 43.68/6.02  
% 43.68/6.02  % SZS output end CNFRefutation for theBenchmark.p
% 43.68/6.02  
% 43.68/6.02  ------                               Statistics
% 43.68/6.02  
% 43.68/6.02  ------ Selected
% 43.68/6.02  
% 43.68/6.02  total_time:                             5.301
% 43.68/6.02  
%------------------------------------------------------------------------------
