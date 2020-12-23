%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0473+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:41 EST 2020

% Result     : Theorem 19.32s
% Output     : CNFRefutation 19.32s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 120 expanded)
%              Number of clauses        :   19 (  24 expanded)
%              Number of leaves         :    5 (  31 expanded)
%              Depth                    :   17
%              Number of atoms          :  112 ( 327 expanded)
%              Number of equality atoms :   91 ( 263 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f707,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f708,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k1_relat_1(X0)
        <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    inference(negated_conjecture,[],[f707])).

fof(f1221,plain,(
    ? [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <~> k1_xboole_0 = k2_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f708])).

fof(f1638,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k2_relat_1(X0)
        | k1_xboole_0 != k1_relat_1(X0) )
      & ( k1_xboole_0 = k2_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1221])).

fof(f1639,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k2_relat_1(X0)
        | k1_xboole_0 != k1_relat_1(X0) )
      & ( k1_xboole_0 = k2_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f1638])).

fof(f1640,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k2_relat_1(sK149)
        | k1_xboole_0 != k1_relat_1(sK149) )
      & ( k1_xboole_0 = k2_relat_1(sK149)
        | k1_xboole_0 = k1_relat_1(sK149) )
      & v1_relat_1(sK149) ) ),
    introduced(choice_axiom,[])).

fof(f1641,plain,
    ( ( k1_xboole_0 != k2_relat_1(sK149)
      | k1_xboole_0 != k1_relat_1(sK149) )
    & ( k1_xboole_0 = k2_relat_1(sK149)
      | k1_xboole_0 = k1_relat_1(sK149) )
    & v1_relat_1(sK149) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK149])],[f1639,f1640])).

fof(f2744,plain,
    ( k1_xboole_0 = k2_relat_1(sK149)
    | k1_xboole_0 = k1_relat_1(sK149) ),
    inference(cnf_transformation,[],[f1641])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1649,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f3274,plain,
    ( o_0_0_xboole_0 = k2_relat_1(sK149)
    | o_0_0_xboole_0 = k1_relat_1(sK149) ),
    inference(definition_unfolding,[],[f2744,f1649,f1649])).

fof(f706,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1219,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f706])).

fof(f1220,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1219])).

fof(f2742,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1220])).

fof(f3271,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | o_0_0_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f2742,f1649,f1649])).

fof(f2743,plain,(
    v1_relat_1(sK149) ),
    inference(cnf_transformation,[],[f1641])).

fof(f2741,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1220])).

fof(f3272,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | o_0_0_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f2741,f1649,f1649])).

fof(f2745,plain,
    ( k1_xboole_0 != k2_relat_1(sK149)
    | k1_xboole_0 != k1_relat_1(sK149) ),
    inference(cnf_transformation,[],[f1641])).

fof(f3273,plain,
    ( o_0_0_xboole_0 != k2_relat_1(sK149)
    | o_0_0_xboole_0 != k1_relat_1(sK149) ),
    inference(definition_unfolding,[],[f2745,f1649,f1649])).

fof(f703,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2737,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f703])).

fof(f3266,plain,(
    o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f2737,f1649,f1649])).

fof(f2736,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f703])).

fof(f3267,plain,(
    o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f2736,f1649,f1649])).

cnf(c_1088,negated_conjecture,
    ( o_0_0_xboole_0 = k2_relat_1(sK149)
    | o_0_0_xboole_0 = k1_relat_1(sK149) ),
    inference(cnf_transformation,[],[f3274])).

cnf(c_1085,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != o_0_0_xboole_0
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f3271])).

cnf(c_45607,plain,
    ( k2_relat_1(X0) != o_0_0_xboole_0
    | o_0_0_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1085])).

cnf(c_59643,plain,
    ( k1_relat_1(sK149) = o_0_0_xboole_0
    | sK149 = o_0_0_xboole_0
    | v1_relat_1(sK149) != iProver_top ),
    inference(superposition,[status(thm)],[c_1088,c_45607])).

cnf(c_1089,negated_conjecture,
    ( v1_relat_1(sK149) ),
    inference(cnf_transformation,[],[f2743])).

cnf(c_59650,plain,
    ( ~ v1_relat_1(sK149)
    | k1_relat_1(sK149) = o_0_0_xboole_0
    | sK149 = o_0_0_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_59643])).

cnf(c_60494,plain,
    ( sK149 = o_0_0_xboole_0
    | k1_relat_1(sK149) = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_59643,c_1089,c_59650])).

cnf(c_60495,plain,
    ( k1_relat_1(sK149) = o_0_0_xboole_0
    | sK149 = o_0_0_xboole_0 ),
    inference(renaming,[status(thm)],[c_60494])).

cnf(c_1086,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != o_0_0_xboole_0
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f3272])).

cnf(c_45606,plain,
    ( k1_relat_1(X0) != o_0_0_xboole_0
    | o_0_0_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1086])).

cnf(c_60498,plain,
    ( sK149 = o_0_0_xboole_0
    | v1_relat_1(sK149) != iProver_top ),
    inference(superposition,[status(thm)],[c_60495,c_45606])).

cnf(c_1090,plain,
    ( v1_relat_1(sK149) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1089])).

cnf(c_60519,plain,
    ( sK149 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_60498,c_1090])).

cnf(c_1087,negated_conjecture,
    ( o_0_0_xboole_0 != k2_relat_1(sK149)
    | o_0_0_xboole_0 != k1_relat_1(sK149) ),
    inference(cnf_transformation,[],[f3273])).

cnf(c_60538,plain,
    ( k2_relat_1(o_0_0_xboole_0) != o_0_0_xboole_0
    | k1_relat_1(o_0_0_xboole_0) != o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_60519,c_1087])).

cnf(c_1080,plain,
    ( k2_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3266])).

cnf(c_1081,plain,
    ( k1_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3267])).

cnf(c_60541,plain,
    ( o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_60538,c_1080,c_1081])).

cnf(c_60542,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_60541])).

%------------------------------------------------------------------------------
