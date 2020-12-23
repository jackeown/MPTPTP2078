%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0472+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:23 EST 2020

% Result     : Theorem 0.44s
% Output     : CNFRefutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 112 expanded)
%              Number of clauses        :   22 (  31 expanded)
%              Number of leaves         :    8 (  26 expanded)
%              Depth                    :   12
%              Number of atoms          :  116 ( 308 expanded)
%              Number of equality atoms :   53 ( 178 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( ( k1_xboole_0 = k2_relat_1(X0)
            | k1_xboole_0 = k1_relat_1(X0) )
         => k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f13,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ( k1_xboole_0 = k2_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f14,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ( k1_xboole_0 = k2_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f15,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
        & v1_relat_1(X0) )
   => ( k1_xboole_0 != sK0
      & ( k1_xboole_0 = k2_relat_1(sK0)
        | k1_xboole_0 = k1_relat_1(sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( k1_xboole_0 != sK0
    & ( k1_xboole_0 = k2_relat_1(sK0)
      | k1_xboole_0 = k1_relat_1(sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).

fof(f23,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | k1_xboole_0 = k1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f27,plain,
    ( o_0_0_xboole_0 = k2_relat_1(sK0)
    | o_0_0_xboole_0 = k1_relat_1(sK0) ),
    inference(definition_unfolding,[],[f23,f17,f17])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f11,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f22,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f24,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f16])).

fof(f26,plain,(
    o_0_0_xboole_0 != sK0 ),
    inference(definition_unfolding,[],[f24,f17])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f21,f17])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f9,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_5,negated_conjecture,
    ( o_0_0_xboole_0 = k2_relat_1(sK0)
    | o_0_0_xboole_0 = k1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_6,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_61,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k2_relat_1(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_6])).

cnf(c_62,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK0))
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_61])).

cnf(c_207,plain,
    ( v1_xboole_0(k2_relat_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_62])).

cnf(c_4,negated_conjecture,
    ( o_0_0_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_63,plain,
    ( v1_xboole_0(k2_relat_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_62])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_239,plain,
    ( ~ v1_xboole_0(sK0)
    | o_0_0_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_240,plain,
    ( o_0_0_xboole_0 = sK0
    | v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_239])).

cnf(c_297,plain,
    ( v1_xboole_0(k2_relat_1(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_207,c_4,c_63,c_240])).

cnf(c_302,plain,
    ( k1_relat_1(sK0) = o_0_0_xboole_0
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_297])).

cnf(c_123,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_247,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_relat_1(sK0))
    | k1_relat_1(sK0) != X0 ),
    inference(instantiation,[status(thm)],[c_123])).

cnf(c_249,plain,
    ( v1_xboole_0(k1_relat_1(sK0))
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | k1_relat_1(sK0) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_247])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_71,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_relat_1(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_6])).

cnf(c_72,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK0))
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_71])).

cnf(c_0,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_17,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_302,c_249,c_239,c_72,c_17,c_0,c_4])).


%------------------------------------------------------------------------------
