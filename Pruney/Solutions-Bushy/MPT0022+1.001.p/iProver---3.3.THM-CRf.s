%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0022+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:16 EST 2020

% Result     : Theorem 0.80s
% Output     : CNFRefutation 0.80s
% Verified   : 
% Statistics : Number of formulae       :   49 (  82 expanded)
%              Number of clauses        :   26 (  31 expanded)
%              Number of leaves         :    9 (  22 expanded)
%              Depth                    :   11
%              Number of atoms          :   85 ( 141 expanded)
%              Number of equality atoms :   67 ( 115 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_xboole_0(X0,X1)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_xboole_0(X0,X1)
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 != X0
      & k1_xboole_0 = k2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 != X0
        & k1_xboole_0 = k2_xboole_0(X0,X1) )
   => ( k1_xboole_0 != sK0
      & k1_xboole_0 = k2_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( k1_xboole_0 != sK0
    & k1_xboole_0 = k2_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).

fof(f18,plain,(
    k1_xboole_0 = k2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f23,plain,(
    o_0_0_xboole_0 = k2_xboole_0(sK0,sK1) ),
    inference(definition_unfolding,[],[f18,f13])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
     => ~ v1_xboole_0(k2_xboole_0(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X1,X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X1,X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f17,f13])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0] : k2_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f16,f13])).

fof(f19,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f12])).

fof(f22,plain,(
    o_0_0_xboole_0 != sK0 ),
    inference(definition_unfolding,[],[f19,f13])).

cnf(c_5,negated_conjecture,
    ( o_0_0_xboole_0 = k2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_1,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k2_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_111,plain,
    ( v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k2_xboole_0(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_255,plain,
    ( v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_111])).

cnf(c_0,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_13,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_333,plain,
    ( v1_xboole_0(sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_255,c_13])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_110,plain,
    ( o_0_0_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_338,plain,
    ( sK1 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_333,c_110])).

cnf(c_341,plain,
    ( k2_xboole_0(sK0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_338,c_5])).

cnf(c_44,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_215,plain,
    ( k2_xboole_0(sK0,o_0_0_xboole_0) != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = k2_xboole_0(sK0,o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_216,plain,
    ( k2_xboole_0(sK0,o_0_0_xboole_0) != o_0_0_xboole_0
    | o_0_0_xboole_0 = k2_xboole_0(sK0,o_0_0_xboole_0)
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_215])).

cnf(c_139,plain,
    ( sK0 != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_202,plain,
    ( sK0 != k2_xboole_0(sK0,o_0_0_xboole_0)
    | o_0_0_xboole_0 != k2_xboole_0(sK0,o_0_0_xboole_0)
    | o_0_0_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_139])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_174,plain,
    ( k2_xboole_0(sK0,o_0_0_xboole_0) = sK0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_154,plain,
    ( X0 != X1
    | sK0 != X1
    | sK0 = X0 ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_167,plain,
    ( X0 != sK0
    | sK0 = X0
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_154])).

cnf(c_173,plain,
    ( k2_xboole_0(sK0,o_0_0_xboole_0) != sK0
    | sK0 = k2_xboole_0(sK0,o_0_0_xboole_0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_167])).

cnf(c_43,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_168,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(c_7,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | o_0_0_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4,negated_conjecture,
    ( o_0_0_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_341,c_216,c_202,c_174,c_173,c_168,c_0,c_7,c_4])).


%------------------------------------------------------------------------------
