%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:47 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 341 expanded)
%              Number of clauses        :   57 (  92 expanded)
%              Number of leaves         :   15 (  80 expanded)
%              Depth                    :   18
%              Number of atoms          :  240 ( 738 expanded)
%              Number of equality atoms :  102 ( 252 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f36,f49])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f50])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X1,k1_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) )
       => k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_enumset1(X0,X0,X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f45,f49,f49])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f27])).

fof(f47,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f48,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f53,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
    inference(definition_unfolding,[],[f48,f50,f50])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_892,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_894,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1402,plain,
    ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = k2_enumset1(X0,X0,X0,X0)
    | r2_hidden(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_892,c_894])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X0)) = k9_relat_1(X1,k2_enumset1(X2,X2,X2,X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_209,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X0)) = k9_relat_1(X1,k2_enumset1(X2,X2,X2,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_15])).

cnf(c_210,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK1))
    | ~ r2_hidden(X1,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)) ),
    inference(unflattening,[status(thm)],[c_209])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_214,plain,
    ( ~ r2_hidden(X1,k1_relat_1(sK1))
    | ~ r2_hidden(X0,k1_relat_1(sK1))
    | k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_210,c_16])).

cnf(c_215,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK1))
    | ~ r2_hidden(X1,k1_relat_1(sK1))
    | k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)) ),
    inference(renaming,[status(thm)],[c_214])).

cnf(c_890,plain,
    ( k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1))
    | r2_hidden(X0,k1_relat_1(sK1)) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_215])).

cnf(c_2463,plain,
    ( k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1))
    | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k1_relat_1(sK1)) = k2_enumset1(X0,X0,X0,X0)
    | r2_hidden(X1,k1_relat_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1402,c_890])).

cnf(c_2469,plain,
    ( k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1))
    | k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k1_relat_1(sK1)) = k2_enumset1(X1,X1,X1,X1)
    | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k1_relat_1(sK1)) = k2_enumset1(X0,X0,X0,X0) ),
    inference(superposition,[status(thm)],[c_1402,c_2463])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_891,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_258,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_16])).

cnf(c_259,plain,
    ( k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_258])).

cnf(c_939,plain,
    ( r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_891,c_259])).

cnf(c_2576,plain,
    ( k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK1)) = k2_enumset1(sK0,sK0,sK0,sK0)
    | r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2469,c_939])).

cnf(c_217,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) = k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_215])).

cnf(c_991,plain,
    ( r2_hidden(X0,k1_relat_1(sK1))
    | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_993,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_991])).

cnf(c_1057,plain,
    ( k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_259])).

cnf(c_552,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_996,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != X1
    | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != X0 ),
    inference(instantiation,[status(thm)],[c_552])).

cnf(c_1056,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0)
    | r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != X0
    | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_996])).

cnf(c_1148,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_1056])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1149,plain,
    ( r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1329,plain,
    ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k1_relat_1(sK1))
    | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k1_relat_1(sK1)) = k2_enumset1(X0,X0,X0,X0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1331,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK1))
    | k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK1)) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_1329])).

cnf(c_2847,plain,
    ( k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK1)) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2576,c_14,c_217,c_993,c_1057,c_1148,c_1149,c_1331])).

cnf(c_897,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
    | ~ r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_893,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1304,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X2)) = X0
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_893,c_894])).

cnf(c_1407,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_897,c_1304])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_895,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1543,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1407,c_895])).

cnf(c_11,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_246,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0),X1)
    | k7_relat_1(X0,X1) = k1_xboole_0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_16])).

cnf(c_247,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),X0)
    | k7_relat_1(sK1,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_246])).

cnf(c_400,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),X0)
    | k7_relat_1(sK1,X0) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_247])).

cnf(c_888,plain,
    ( k7_relat_1(sK1,X0) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK1),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_400])).

cnf(c_1971,plain,
    ( k7_relat_1(sK1,k4_xboole_0(X0,k1_relat_1(sK1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1543,c_888])).

cnf(c_2059,plain,
    ( k9_relat_1(sK1,k4_xboole_0(X0,k1_relat_1(sK1))) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1971,c_259])).

cnf(c_9,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2061,plain,
    ( k9_relat_1(sK1,k4_xboole_0(X0,k1_relat_1(sK1))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2059,c_9])).

cnf(c_2856,plain,
    ( k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2847,c_2061])).

cnf(c_3094,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2856,c_939])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_896,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3201,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3094,c_896])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:17:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.37/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.02  
% 2.37/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.37/1.02  
% 2.37/1.02  ------  iProver source info
% 2.37/1.02  
% 2.37/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.37/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.37/1.02  git: non_committed_changes: false
% 2.37/1.02  git: last_make_outside_of_git: false
% 2.37/1.02  
% 2.37/1.02  ------ 
% 2.37/1.02  
% 2.37/1.02  ------ Input Options
% 2.37/1.02  
% 2.37/1.02  --out_options                           all
% 2.37/1.02  --tptp_safe_out                         true
% 2.37/1.02  --problem_path                          ""
% 2.37/1.02  --include_path                          ""
% 2.37/1.02  --clausifier                            res/vclausify_rel
% 2.37/1.02  --clausifier_options                    --mode clausify
% 2.37/1.02  --stdin                                 false
% 2.37/1.02  --stats_out                             all
% 2.37/1.02  
% 2.37/1.02  ------ General Options
% 2.37/1.02  
% 2.37/1.02  --fof                                   false
% 2.37/1.02  --time_out_real                         305.
% 2.37/1.02  --time_out_virtual                      -1.
% 2.37/1.02  --symbol_type_check                     false
% 2.37/1.02  --clausify_out                          false
% 2.37/1.02  --sig_cnt_out                           false
% 2.37/1.02  --trig_cnt_out                          false
% 2.37/1.02  --trig_cnt_out_tolerance                1.
% 2.37/1.02  --trig_cnt_out_sk_spl                   false
% 2.37/1.02  --abstr_cl_out                          false
% 2.37/1.02  
% 2.37/1.02  ------ Global Options
% 2.37/1.02  
% 2.37/1.02  --schedule                              default
% 2.37/1.02  --add_important_lit                     false
% 2.37/1.02  --prop_solver_per_cl                    1000
% 2.37/1.02  --min_unsat_core                        false
% 2.37/1.02  --soft_assumptions                      false
% 2.37/1.02  --soft_lemma_size                       3
% 2.37/1.02  --prop_impl_unit_size                   0
% 2.37/1.02  --prop_impl_unit                        []
% 2.37/1.02  --share_sel_clauses                     true
% 2.37/1.02  --reset_solvers                         false
% 2.37/1.02  --bc_imp_inh                            [conj_cone]
% 2.37/1.02  --conj_cone_tolerance                   3.
% 2.37/1.02  --extra_neg_conj                        none
% 2.37/1.02  --large_theory_mode                     true
% 2.37/1.02  --prolific_symb_bound                   200
% 2.37/1.02  --lt_threshold                          2000
% 2.37/1.02  --clause_weak_htbl                      true
% 2.37/1.02  --gc_record_bc_elim                     false
% 2.37/1.02  
% 2.37/1.02  ------ Preprocessing Options
% 2.37/1.02  
% 2.37/1.02  --preprocessing_flag                    true
% 2.37/1.02  --time_out_prep_mult                    0.1
% 2.37/1.02  --splitting_mode                        input
% 2.37/1.02  --splitting_grd                         true
% 2.37/1.02  --splitting_cvd                         false
% 2.37/1.02  --splitting_cvd_svl                     false
% 2.37/1.02  --splitting_nvd                         32
% 2.37/1.02  --sub_typing                            true
% 2.37/1.02  --prep_gs_sim                           true
% 2.37/1.02  --prep_unflatten                        true
% 2.37/1.02  --prep_res_sim                          true
% 2.37/1.02  --prep_upred                            true
% 2.37/1.02  --prep_sem_filter                       exhaustive
% 2.37/1.02  --prep_sem_filter_out                   false
% 2.37/1.02  --pred_elim                             true
% 2.37/1.02  --res_sim_input                         true
% 2.37/1.02  --eq_ax_congr_red                       true
% 2.37/1.02  --pure_diseq_elim                       true
% 2.37/1.02  --brand_transform                       false
% 2.37/1.02  --non_eq_to_eq                          false
% 2.37/1.02  --prep_def_merge                        true
% 2.37/1.02  --prep_def_merge_prop_impl              false
% 2.37/1.02  --prep_def_merge_mbd                    true
% 2.37/1.02  --prep_def_merge_tr_red                 false
% 2.37/1.02  --prep_def_merge_tr_cl                  false
% 2.37/1.02  --smt_preprocessing                     true
% 2.37/1.02  --smt_ac_axioms                         fast
% 2.37/1.02  --preprocessed_out                      false
% 2.37/1.02  --preprocessed_stats                    false
% 2.37/1.02  
% 2.37/1.02  ------ Abstraction refinement Options
% 2.37/1.02  
% 2.37/1.02  --abstr_ref                             []
% 2.37/1.02  --abstr_ref_prep                        false
% 2.37/1.02  --abstr_ref_until_sat                   false
% 2.37/1.02  --abstr_ref_sig_restrict                funpre
% 2.37/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.37/1.02  --abstr_ref_under                       []
% 2.37/1.02  
% 2.37/1.02  ------ SAT Options
% 2.37/1.02  
% 2.37/1.02  --sat_mode                              false
% 2.37/1.02  --sat_fm_restart_options                ""
% 2.37/1.02  --sat_gr_def                            false
% 2.37/1.02  --sat_epr_types                         true
% 2.37/1.02  --sat_non_cyclic_types                  false
% 2.37/1.02  --sat_finite_models                     false
% 2.37/1.02  --sat_fm_lemmas                         false
% 2.37/1.02  --sat_fm_prep                           false
% 2.37/1.02  --sat_fm_uc_incr                        true
% 2.37/1.02  --sat_out_model                         small
% 2.37/1.02  --sat_out_clauses                       false
% 2.37/1.02  
% 2.37/1.02  ------ QBF Options
% 2.37/1.02  
% 2.37/1.02  --qbf_mode                              false
% 2.37/1.02  --qbf_elim_univ                         false
% 2.37/1.02  --qbf_dom_inst                          none
% 2.37/1.02  --qbf_dom_pre_inst                      false
% 2.37/1.02  --qbf_sk_in                             false
% 2.37/1.02  --qbf_pred_elim                         true
% 2.37/1.02  --qbf_split                             512
% 2.37/1.02  
% 2.37/1.02  ------ BMC1 Options
% 2.37/1.02  
% 2.37/1.02  --bmc1_incremental                      false
% 2.37/1.02  --bmc1_axioms                           reachable_all
% 2.37/1.02  --bmc1_min_bound                        0
% 2.37/1.02  --bmc1_max_bound                        -1
% 2.37/1.02  --bmc1_max_bound_default                -1
% 2.37/1.02  --bmc1_symbol_reachability              true
% 2.37/1.02  --bmc1_property_lemmas                  false
% 2.37/1.02  --bmc1_k_induction                      false
% 2.37/1.02  --bmc1_non_equiv_states                 false
% 2.37/1.02  --bmc1_deadlock                         false
% 2.37/1.02  --bmc1_ucm                              false
% 2.37/1.02  --bmc1_add_unsat_core                   none
% 2.37/1.02  --bmc1_unsat_core_children              false
% 2.37/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.37/1.02  --bmc1_out_stat                         full
% 2.37/1.02  --bmc1_ground_init                      false
% 2.37/1.02  --bmc1_pre_inst_next_state              false
% 2.37/1.02  --bmc1_pre_inst_state                   false
% 2.37/1.02  --bmc1_pre_inst_reach_state             false
% 2.37/1.02  --bmc1_out_unsat_core                   false
% 2.37/1.02  --bmc1_aig_witness_out                  false
% 2.37/1.02  --bmc1_verbose                          false
% 2.37/1.02  --bmc1_dump_clauses_tptp                false
% 2.37/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.37/1.02  --bmc1_dump_file                        -
% 2.37/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.37/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.37/1.02  --bmc1_ucm_extend_mode                  1
% 2.37/1.02  --bmc1_ucm_init_mode                    2
% 2.37/1.02  --bmc1_ucm_cone_mode                    none
% 2.37/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.37/1.02  --bmc1_ucm_relax_model                  4
% 2.37/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.37/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.37/1.02  --bmc1_ucm_layered_model                none
% 2.37/1.02  --bmc1_ucm_max_lemma_size               10
% 2.37/1.02  
% 2.37/1.02  ------ AIG Options
% 2.37/1.02  
% 2.37/1.02  --aig_mode                              false
% 2.37/1.02  
% 2.37/1.02  ------ Instantiation Options
% 2.37/1.02  
% 2.37/1.02  --instantiation_flag                    true
% 2.37/1.02  --inst_sos_flag                         false
% 2.37/1.02  --inst_sos_phase                        true
% 2.37/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.37/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.37/1.02  --inst_lit_sel_side                     num_symb
% 2.37/1.02  --inst_solver_per_active                1400
% 2.37/1.02  --inst_solver_calls_frac                1.
% 2.37/1.02  --inst_passive_queue_type               priority_queues
% 2.37/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.37/1.02  --inst_passive_queues_freq              [25;2]
% 2.37/1.02  --inst_dismatching                      true
% 2.37/1.02  --inst_eager_unprocessed_to_passive     true
% 2.37/1.02  --inst_prop_sim_given                   true
% 2.37/1.02  --inst_prop_sim_new                     false
% 2.37/1.02  --inst_subs_new                         false
% 2.37/1.02  --inst_eq_res_simp                      false
% 2.37/1.02  --inst_subs_given                       false
% 2.37/1.02  --inst_orphan_elimination               true
% 2.37/1.02  --inst_learning_loop_flag               true
% 2.37/1.02  --inst_learning_start                   3000
% 2.37/1.02  --inst_learning_factor                  2
% 2.37/1.02  --inst_start_prop_sim_after_learn       3
% 2.37/1.02  --inst_sel_renew                        solver
% 2.37/1.02  --inst_lit_activity_flag                true
% 2.37/1.02  --inst_restr_to_given                   false
% 2.37/1.02  --inst_activity_threshold               500
% 2.37/1.02  --inst_out_proof                        true
% 2.37/1.02  
% 2.37/1.02  ------ Resolution Options
% 2.37/1.02  
% 2.37/1.02  --resolution_flag                       true
% 2.37/1.02  --res_lit_sel                           adaptive
% 2.37/1.02  --res_lit_sel_side                      none
% 2.37/1.02  --res_ordering                          kbo
% 2.37/1.02  --res_to_prop_solver                    active
% 2.37/1.02  --res_prop_simpl_new                    false
% 2.37/1.02  --res_prop_simpl_given                  true
% 2.37/1.02  --res_passive_queue_type                priority_queues
% 2.37/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.37/1.02  --res_passive_queues_freq               [15;5]
% 2.37/1.02  --res_forward_subs                      full
% 2.37/1.02  --res_backward_subs                     full
% 2.37/1.02  --res_forward_subs_resolution           true
% 2.37/1.02  --res_backward_subs_resolution          true
% 2.37/1.02  --res_orphan_elimination                true
% 2.37/1.02  --res_time_limit                        2.
% 2.37/1.02  --res_out_proof                         true
% 2.37/1.02  
% 2.37/1.02  ------ Superposition Options
% 2.37/1.02  
% 2.37/1.02  --superposition_flag                    true
% 2.37/1.02  --sup_passive_queue_type                priority_queues
% 2.37/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.37/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.37/1.02  --demod_completeness_check              fast
% 2.37/1.02  --demod_use_ground                      true
% 2.37/1.02  --sup_to_prop_solver                    passive
% 2.37/1.02  --sup_prop_simpl_new                    true
% 2.37/1.02  --sup_prop_simpl_given                  true
% 2.37/1.02  --sup_fun_splitting                     false
% 2.37/1.02  --sup_smt_interval                      50000
% 2.37/1.02  
% 2.37/1.02  ------ Superposition Simplification Setup
% 2.37/1.02  
% 2.37/1.02  --sup_indices_passive                   []
% 2.37/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.37/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.37/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.37/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.37/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.37/1.02  --sup_full_bw                           [BwDemod]
% 2.37/1.02  --sup_immed_triv                        [TrivRules]
% 2.37/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.37/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.37/1.02  --sup_immed_bw_main                     []
% 2.37/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.37/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.37/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.37/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.37/1.02  
% 2.37/1.02  ------ Combination Options
% 2.37/1.02  
% 2.37/1.02  --comb_res_mult                         3
% 2.37/1.02  --comb_sup_mult                         2
% 2.37/1.02  --comb_inst_mult                        10
% 2.37/1.02  
% 2.37/1.02  ------ Debug Options
% 2.37/1.02  
% 2.37/1.02  --dbg_backtrace                         false
% 2.37/1.02  --dbg_dump_prop_clauses                 false
% 2.37/1.02  --dbg_dump_prop_clauses_file            -
% 2.37/1.02  --dbg_out_stat                          false
% 2.37/1.02  ------ Parsing...
% 2.37/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.37/1.02  
% 2.37/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.37/1.02  
% 2.37/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.37/1.02  
% 2.37/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.37/1.02  ------ Proving...
% 2.37/1.02  ------ Problem Properties 
% 2.37/1.02  
% 2.37/1.02  
% 2.37/1.02  clauses                                 14
% 2.37/1.02  conjectures                             1
% 2.37/1.02  EPR                                     3
% 2.37/1.02  Horn                                    13
% 2.37/1.02  unary                                   6
% 2.37/1.02  binary                                  6
% 2.37/1.02  lits                                    24
% 2.37/1.02  lits eq                                 9
% 2.37/1.02  fd_pure                                 0
% 2.37/1.02  fd_pseudo                               0
% 2.37/1.02  fd_cond                                 0
% 2.37/1.02  fd_pseudo_cond                          1
% 2.37/1.02  AC symbols                              0
% 2.37/1.02  
% 2.37/1.02  ------ Schedule dynamic 5 is on 
% 2.37/1.02  
% 2.37/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.37/1.02  
% 2.37/1.02  
% 2.37/1.02  ------ 
% 2.37/1.02  Current options:
% 2.37/1.02  ------ 
% 2.37/1.02  
% 2.37/1.02  ------ Input Options
% 2.37/1.02  
% 2.37/1.02  --out_options                           all
% 2.37/1.02  --tptp_safe_out                         true
% 2.37/1.02  --problem_path                          ""
% 2.37/1.02  --include_path                          ""
% 2.37/1.02  --clausifier                            res/vclausify_rel
% 2.37/1.02  --clausifier_options                    --mode clausify
% 2.37/1.02  --stdin                                 false
% 2.37/1.02  --stats_out                             all
% 2.37/1.02  
% 2.37/1.02  ------ General Options
% 2.37/1.02  
% 2.37/1.02  --fof                                   false
% 2.37/1.02  --time_out_real                         305.
% 2.37/1.02  --time_out_virtual                      -1.
% 2.37/1.02  --symbol_type_check                     false
% 2.37/1.02  --clausify_out                          false
% 2.37/1.02  --sig_cnt_out                           false
% 2.37/1.02  --trig_cnt_out                          false
% 2.37/1.02  --trig_cnt_out_tolerance                1.
% 2.37/1.02  --trig_cnt_out_sk_spl                   false
% 2.37/1.02  --abstr_cl_out                          false
% 2.37/1.02  
% 2.37/1.02  ------ Global Options
% 2.37/1.02  
% 2.37/1.02  --schedule                              default
% 2.37/1.02  --add_important_lit                     false
% 2.37/1.02  --prop_solver_per_cl                    1000
% 2.37/1.02  --min_unsat_core                        false
% 2.37/1.02  --soft_assumptions                      false
% 2.37/1.02  --soft_lemma_size                       3
% 2.37/1.02  --prop_impl_unit_size                   0
% 2.37/1.02  --prop_impl_unit                        []
% 2.37/1.02  --share_sel_clauses                     true
% 2.37/1.02  --reset_solvers                         false
% 2.37/1.02  --bc_imp_inh                            [conj_cone]
% 2.37/1.02  --conj_cone_tolerance                   3.
% 2.37/1.02  --extra_neg_conj                        none
% 2.37/1.02  --large_theory_mode                     true
% 2.37/1.02  --prolific_symb_bound                   200
% 2.37/1.02  --lt_threshold                          2000
% 2.37/1.02  --clause_weak_htbl                      true
% 2.37/1.02  --gc_record_bc_elim                     false
% 2.37/1.02  
% 2.37/1.02  ------ Preprocessing Options
% 2.37/1.02  
% 2.37/1.02  --preprocessing_flag                    true
% 2.37/1.02  --time_out_prep_mult                    0.1
% 2.37/1.02  --splitting_mode                        input
% 2.37/1.02  --splitting_grd                         true
% 2.37/1.02  --splitting_cvd                         false
% 2.37/1.02  --splitting_cvd_svl                     false
% 2.37/1.02  --splitting_nvd                         32
% 2.37/1.02  --sub_typing                            true
% 2.37/1.02  --prep_gs_sim                           true
% 2.37/1.02  --prep_unflatten                        true
% 2.37/1.02  --prep_res_sim                          true
% 2.37/1.02  --prep_upred                            true
% 2.37/1.02  --prep_sem_filter                       exhaustive
% 2.37/1.02  --prep_sem_filter_out                   false
% 2.37/1.02  --pred_elim                             true
% 2.37/1.02  --res_sim_input                         true
% 2.37/1.02  --eq_ax_congr_red                       true
% 2.37/1.02  --pure_diseq_elim                       true
% 2.37/1.02  --brand_transform                       false
% 2.37/1.02  --non_eq_to_eq                          false
% 2.37/1.02  --prep_def_merge                        true
% 2.37/1.02  --prep_def_merge_prop_impl              false
% 2.37/1.02  --prep_def_merge_mbd                    true
% 2.37/1.02  --prep_def_merge_tr_red                 false
% 2.37/1.02  --prep_def_merge_tr_cl                  false
% 2.37/1.02  --smt_preprocessing                     true
% 2.37/1.02  --smt_ac_axioms                         fast
% 2.37/1.02  --preprocessed_out                      false
% 2.37/1.02  --preprocessed_stats                    false
% 2.37/1.02  
% 2.37/1.02  ------ Abstraction refinement Options
% 2.37/1.02  
% 2.37/1.02  --abstr_ref                             []
% 2.37/1.02  --abstr_ref_prep                        false
% 2.37/1.02  --abstr_ref_until_sat                   false
% 2.37/1.02  --abstr_ref_sig_restrict                funpre
% 2.37/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.37/1.02  --abstr_ref_under                       []
% 2.37/1.02  
% 2.37/1.02  ------ SAT Options
% 2.37/1.02  
% 2.37/1.02  --sat_mode                              false
% 2.37/1.02  --sat_fm_restart_options                ""
% 2.37/1.02  --sat_gr_def                            false
% 2.37/1.02  --sat_epr_types                         true
% 2.37/1.02  --sat_non_cyclic_types                  false
% 2.37/1.02  --sat_finite_models                     false
% 2.37/1.02  --sat_fm_lemmas                         false
% 2.37/1.02  --sat_fm_prep                           false
% 2.37/1.02  --sat_fm_uc_incr                        true
% 2.37/1.02  --sat_out_model                         small
% 2.37/1.02  --sat_out_clauses                       false
% 2.37/1.02  
% 2.37/1.02  ------ QBF Options
% 2.37/1.02  
% 2.37/1.02  --qbf_mode                              false
% 2.37/1.02  --qbf_elim_univ                         false
% 2.37/1.02  --qbf_dom_inst                          none
% 2.37/1.02  --qbf_dom_pre_inst                      false
% 2.37/1.02  --qbf_sk_in                             false
% 2.37/1.02  --qbf_pred_elim                         true
% 2.37/1.02  --qbf_split                             512
% 2.37/1.02  
% 2.37/1.02  ------ BMC1 Options
% 2.37/1.02  
% 2.37/1.02  --bmc1_incremental                      false
% 2.37/1.02  --bmc1_axioms                           reachable_all
% 2.37/1.02  --bmc1_min_bound                        0
% 2.37/1.02  --bmc1_max_bound                        -1
% 2.37/1.02  --bmc1_max_bound_default                -1
% 2.37/1.02  --bmc1_symbol_reachability              true
% 2.37/1.02  --bmc1_property_lemmas                  false
% 2.37/1.02  --bmc1_k_induction                      false
% 2.37/1.02  --bmc1_non_equiv_states                 false
% 2.37/1.02  --bmc1_deadlock                         false
% 2.37/1.02  --bmc1_ucm                              false
% 2.37/1.02  --bmc1_add_unsat_core                   none
% 2.37/1.02  --bmc1_unsat_core_children              false
% 2.37/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.37/1.02  --bmc1_out_stat                         full
% 2.37/1.02  --bmc1_ground_init                      false
% 2.37/1.02  --bmc1_pre_inst_next_state              false
% 2.37/1.02  --bmc1_pre_inst_state                   false
% 2.37/1.02  --bmc1_pre_inst_reach_state             false
% 2.37/1.02  --bmc1_out_unsat_core                   false
% 2.37/1.02  --bmc1_aig_witness_out                  false
% 2.37/1.02  --bmc1_verbose                          false
% 2.37/1.02  --bmc1_dump_clauses_tptp                false
% 2.37/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.37/1.02  --bmc1_dump_file                        -
% 2.37/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.37/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.37/1.02  --bmc1_ucm_extend_mode                  1
% 2.37/1.02  --bmc1_ucm_init_mode                    2
% 2.37/1.02  --bmc1_ucm_cone_mode                    none
% 2.37/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.37/1.02  --bmc1_ucm_relax_model                  4
% 2.37/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.37/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.37/1.02  --bmc1_ucm_layered_model                none
% 2.37/1.02  --bmc1_ucm_max_lemma_size               10
% 2.37/1.02  
% 2.37/1.02  ------ AIG Options
% 2.37/1.02  
% 2.37/1.02  --aig_mode                              false
% 2.37/1.02  
% 2.37/1.02  ------ Instantiation Options
% 2.37/1.02  
% 2.37/1.02  --instantiation_flag                    true
% 2.37/1.02  --inst_sos_flag                         false
% 2.37/1.02  --inst_sos_phase                        true
% 2.37/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.37/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.37/1.02  --inst_lit_sel_side                     none
% 2.37/1.02  --inst_solver_per_active                1400
% 2.37/1.02  --inst_solver_calls_frac                1.
% 2.37/1.02  --inst_passive_queue_type               priority_queues
% 2.37/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.37/1.02  --inst_passive_queues_freq              [25;2]
% 2.37/1.02  --inst_dismatching                      true
% 2.37/1.02  --inst_eager_unprocessed_to_passive     true
% 2.37/1.02  --inst_prop_sim_given                   true
% 2.37/1.02  --inst_prop_sim_new                     false
% 2.37/1.02  --inst_subs_new                         false
% 2.37/1.02  --inst_eq_res_simp                      false
% 2.37/1.02  --inst_subs_given                       false
% 2.37/1.02  --inst_orphan_elimination               true
% 2.37/1.02  --inst_learning_loop_flag               true
% 2.37/1.02  --inst_learning_start                   3000
% 2.37/1.02  --inst_learning_factor                  2
% 2.37/1.02  --inst_start_prop_sim_after_learn       3
% 2.37/1.02  --inst_sel_renew                        solver
% 2.37/1.02  --inst_lit_activity_flag                true
% 2.37/1.02  --inst_restr_to_given                   false
% 2.37/1.02  --inst_activity_threshold               500
% 2.37/1.02  --inst_out_proof                        true
% 2.37/1.02  
% 2.37/1.02  ------ Resolution Options
% 2.37/1.02  
% 2.37/1.02  --resolution_flag                       false
% 2.37/1.02  --res_lit_sel                           adaptive
% 2.37/1.02  --res_lit_sel_side                      none
% 2.37/1.02  --res_ordering                          kbo
% 2.37/1.02  --res_to_prop_solver                    active
% 2.37/1.02  --res_prop_simpl_new                    false
% 2.37/1.02  --res_prop_simpl_given                  true
% 2.37/1.02  --res_passive_queue_type                priority_queues
% 2.37/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.37/1.02  --res_passive_queues_freq               [15;5]
% 2.37/1.02  --res_forward_subs                      full
% 2.37/1.02  --res_backward_subs                     full
% 2.37/1.02  --res_forward_subs_resolution           true
% 2.37/1.02  --res_backward_subs_resolution          true
% 2.37/1.02  --res_orphan_elimination                true
% 2.37/1.02  --res_time_limit                        2.
% 2.37/1.02  --res_out_proof                         true
% 2.37/1.02  
% 2.37/1.02  ------ Superposition Options
% 2.37/1.02  
% 2.37/1.02  --superposition_flag                    true
% 2.37/1.02  --sup_passive_queue_type                priority_queues
% 2.37/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.37/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.37/1.02  --demod_completeness_check              fast
% 2.37/1.02  --demod_use_ground                      true
% 2.37/1.02  --sup_to_prop_solver                    passive
% 2.37/1.02  --sup_prop_simpl_new                    true
% 2.37/1.02  --sup_prop_simpl_given                  true
% 2.37/1.02  --sup_fun_splitting                     false
% 2.37/1.02  --sup_smt_interval                      50000
% 2.37/1.02  
% 2.37/1.02  ------ Superposition Simplification Setup
% 2.37/1.02  
% 2.37/1.02  --sup_indices_passive                   []
% 2.37/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.37/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.37/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.37/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.37/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.37/1.02  --sup_full_bw                           [BwDemod]
% 2.37/1.02  --sup_immed_triv                        [TrivRules]
% 2.37/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.37/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.37/1.02  --sup_immed_bw_main                     []
% 2.37/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.37/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.37/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.37/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.37/1.02  
% 2.37/1.02  ------ Combination Options
% 2.37/1.02  
% 2.37/1.02  --comb_res_mult                         3
% 2.37/1.02  --comb_sup_mult                         2
% 2.37/1.02  --comb_inst_mult                        10
% 2.37/1.02  
% 2.37/1.02  ------ Debug Options
% 2.37/1.02  
% 2.37/1.02  --dbg_backtrace                         false
% 2.37/1.02  --dbg_dump_prop_clauses                 false
% 2.37/1.02  --dbg_dump_prop_clauses_file            -
% 2.37/1.02  --dbg_out_stat                          false
% 2.37/1.02  
% 2.37/1.02  
% 2.37/1.02  
% 2.37/1.02  
% 2.37/1.02  ------ Proving...
% 2.37/1.02  
% 2.37/1.02  
% 2.37/1.02  % SZS status Theorem for theBenchmark.p
% 2.37/1.02  
% 2.37/1.02   Resolution empty clause
% 2.37/1.02  
% 2.37/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.37/1.02  
% 2.37/1.02  fof(f8,axiom,(
% 2.37/1.02    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 2.37/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/1.02  
% 2.37/1.02  fof(f16,plain,(
% 2.37/1.02    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 2.37/1.02    inference(ennf_transformation,[],[f8])).
% 2.37/1.02  
% 2.37/1.02  fof(f39,plain,(
% 2.37/1.02    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.37/1.02    inference(cnf_transformation,[],[f16])).
% 2.37/1.02  
% 2.37/1.02  fof(f5,axiom,(
% 2.37/1.02    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.37/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/1.02  
% 2.37/1.02  fof(f36,plain,(
% 2.37/1.02    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.37/1.02    inference(cnf_transformation,[],[f5])).
% 2.37/1.02  
% 2.37/1.02  fof(f6,axiom,(
% 2.37/1.02    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.37/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/1.02  
% 2.37/1.02  fof(f37,plain,(
% 2.37/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.37/1.02    inference(cnf_transformation,[],[f6])).
% 2.37/1.02  
% 2.37/1.02  fof(f7,axiom,(
% 2.37/1.02    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.37/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/1.02  
% 2.37/1.02  fof(f38,plain,(
% 2.37/1.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.37/1.02    inference(cnf_transformation,[],[f7])).
% 2.37/1.02  
% 2.37/1.02  fof(f49,plain,(
% 2.37/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.37/1.02    inference(definition_unfolding,[],[f37,f38])).
% 2.37/1.02  
% 2.37/1.02  fof(f50,plain,(
% 2.37/1.02    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.37/1.02    inference(definition_unfolding,[],[f36,f49])).
% 2.37/1.02  
% 2.37/1.02  fof(f51,plain,(
% 2.37/1.02    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 2.37/1.02    inference(definition_unfolding,[],[f39,f50])).
% 2.37/1.02  
% 2.37/1.02  fof(f3,axiom,(
% 2.37/1.02    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.37/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/1.02  
% 2.37/1.02  fof(f25,plain,(
% 2.37/1.02    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 2.37/1.02    inference(nnf_transformation,[],[f3])).
% 2.37/1.02  
% 2.37/1.02  fof(f33,plain,(
% 2.37/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.37/1.02    inference(cnf_transformation,[],[f25])).
% 2.37/1.02  
% 2.37/1.02  fof(f12,axiom,(
% 2.37/1.02    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X1,k1_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) => k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))))),
% 2.37/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/1.02  
% 2.37/1.02  fof(f19,plain,(
% 2.37/1.02    ! [X0,X1,X2] : ((k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | (~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.37/1.02    inference(ennf_transformation,[],[f12])).
% 2.37/1.02  
% 2.37/1.02  fof(f20,plain,(
% 2.37/1.02    ! [X0,X1,X2] : (k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.37/1.02    inference(flattening,[],[f19])).
% 2.37/1.02  
% 2.37/1.02  fof(f45,plain,(
% 2.37/1.02    ( ! [X2,X0,X1] : (k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.37/1.02    inference(cnf_transformation,[],[f20])).
% 2.37/1.02  
% 2.37/1.02  fof(f52,plain,(
% 2.37/1.02    ( ! [X2,X0,X1] : (k2_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_enumset1(X0,X0,X0,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.37/1.02    inference(definition_unfolding,[],[f45,f49,f49])).
% 2.37/1.02  
% 2.37/1.02  fof(f13,conjecture,(
% 2.37/1.02    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 2.37/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/1.02  
% 2.37/1.02  fof(f14,negated_conjecture,(
% 2.37/1.02    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 2.37/1.02    inference(negated_conjecture,[],[f13])).
% 2.37/1.02  
% 2.37/1.02  fof(f21,plain,(
% 2.37/1.02    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 2.37/1.02    inference(ennf_transformation,[],[f14])).
% 2.37/1.02  
% 2.37/1.02  fof(f22,plain,(
% 2.37/1.02    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.37/1.02    inference(flattening,[],[f21])).
% 2.37/1.02  
% 2.37/1.02  fof(f27,plain,(
% 2.37/1.02    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 2.37/1.02    introduced(choice_axiom,[])).
% 2.37/1.02  
% 2.37/1.02  fof(f28,plain,(
% 2.37/1.02    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 2.37/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f27])).
% 2.37/1.02  
% 2.37/1.02  fof(f47,plain,(
% 2.37/1.02    v1_funct_1(sK1)),
% 2.37/1.02    inference(cnf_transformation,[],[f28])).
% 2.37/1.02  
% 2.37/1.02  fof(f46,plain,(
% 2.37/1.02    v1_relat_1(sK1)),
% 2.37/1.02    inference(cnf_transformation,[],[f28])).
% 2.37/1.02  
% 2.37/1.02  fof(f48,plain,(
% 2.37/1.02    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))),
% 2.37/1.02    inference(cnf_transformation,[],[f28])).
% 2.37/1.02  
% 2.37/1.02  fof(f53,plain,(
% 2.37/1.02    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))),
% 2.37/1.02    inference(definition_unfolding,[],[f48,f50,f50])).
% 2.37/1.02  
% 2.37/1.02  fof(f9,axiom,(
% 2.37/1.02    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.37/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/1.02  
% 2.37/1.02  fof(f17,plain,(
% 2.37/1.02    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.37/1.02    inference(ennf_transformation,[],[f9])).
% 2.37/1.02  
% 2.37/1.02  fof(f40,plain,(
% 2.37/1.02    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.37/1.02    inference(cnf_transformation,[],[f17])).
% 2.37/1.02  
% 2.37/1.02  fof(f1,axiom,(
% 2.37/1.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.37/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/1.02  
% 2.37/1.02  fof(f23,plain,(
% 2.37/1.02    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.37/1.02    inference(nnf_transformation,[],[f1])).
% 2.37/1.02  
% 2.37/1.02  fof(f24,plain,(
% 2.37/1.02    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.37/1.02    inference(flattening,[],[f23])).
% 2.37/1.02  
% 2.37/1.02  fof(f30,plain,(
% 2.37/1.02    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.37/1.02    inference(cnf_transformation,[],[f24])).
% 2.37/1.02  
% 2.37/1.02  fof(f54,plain,(
% 2.37/1.02    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.37/1.02    inference(equality_resolution,[],[f30])).
% 2.37/1.02  
% 2.37/1.02  fof(f4,axiom,(
% 2.37/1.02    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 2.37/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/1.02  
% 2.37/1.02  fof(f15,plain,(
% 2.37/1.02    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.37/1.02    inference(ennf_transformation,[],[f4])).
% 2.37/1.02  
% 2.37/1.02  fof(f35,plain,(
% 2.37/1.02    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.37/1.02    inference(cnf_transformation,[],[f15])).
% 2.37/1.02  
% 2.37/1.02  fof(f34,plain,(
% 2.37/1.02    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 2.37/1.02    inference(cnf_transformation,[],[f25])).
% 2.37/1.02  
% 2.37/1.02  fof(f11,axiom,(
% 2.37/1.02    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 2.37/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/1.02  
% 2.37/1.02  fof(f18,plain,(
% 2.37/1.02    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.37/1.02    inference(ennf_transformation,[],[f11])).
% 2.37/1.02  
% 2.37/1.02  fof(f26,plain,(
% 2.37/1.02    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.37/1.02    inference(nnf_transformation,[],[f18])).
% 2.37/1.02  
% 2.37/1.02  fof(f44,plain,(
% 2.37/1.02    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.37/1.02    inference(cnf_transformation,[],[f26])).
% 2.37/1.02  
% 2.37/1.02  fof(f10,axiom,(
% 2.37/1.02    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.37/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/1.02  
% 2.37/1.02  fof(f42,plain,(
% 2.37/1.02    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.37/1.02    inference(cnf_transformation,[],[f10])).
% 2.37/1.02  
% 2.37/1.02  fof(f2,axiom,(
% 2.37/1.02    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.37/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/1.02  
% 2.37/1.02  fof(f32,plain,(
% 2.37/1.02    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.37/1.02    inference(cnf_transformation,[],[f2])).
% 2.37/1.02  
% 2.37/1.02  cnf(c_7,plain,
% 2.37/1.02      ( r2_hidden(X0,X1) | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
% 2.37/1.02      inference(cnf_transformation,[],[f51]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_892,plain,
% 2.37/1.02      ( r2_hidden(X0,X1) = iProver_top
% 2.37/1.02      | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = iProver_top ),
% 2.37/1.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_5,plain,
% 2.37/1.02      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 2.37/1.02      inference(cnf_transformation,[],[f33]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_894,plain,
% 2.37/1.02      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 2.37/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_1402,plain,
% 2.37/1.02      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = k2_enumset1(X0,X0,X0,X0)
% 2.37/1.02      | r2_hidden(X0,X1) = iProver_top ),
% 2.37/1.02      inference(superposition,[status(thm)],[c_892,c_894]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_13,plain,
% 2.37/1.02      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.37/1.02      | ~ r2_hidden(X2,k1_relat_1(X1))
% 2.37/1.02      | ~ v1_funct_1(X1)
% 2.37/1.02      | ~ v1_relat_1(X1)
% 2.37/1.02      | k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X0)) = k9_relat_1(X1,k2_enumset1(X2,X2,X2,X0)) ),
% 2.37/1.02      inference(cnf_transformation,[],[f52]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_15,negated_conjecture,
% 2.37/1.02      ( v1_funct_1(sK1) ),
% 2.37/1.02      inference(cnf_transformation,[],[f47]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_209,plain,
% 2.37/1.02      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.37/1.02      | ~ r2_hidden(X2,k1_relat_1(X1))
% 2.37/1.02      | ~ v1_relat_1(X1)
% 2.37/1.02      | k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X0)) = k9_relat_1(X1,k2_enumset1(X2,X2,X2,X0))
% 2.37/1.02      | sK1 != X1 ),
% 2.37/1.02      inference(resolution_lifted,[status(thm)],[c_13,c_15]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_210,plain,
% 2.37/1.02      ( ~ r2_hidden(X0,k1_relat_1(sK1))
% 2.37/1.02      | ~ r2_hidden(X1,k1_relat_1(sK1))
% 2.37/1.02      | ~ v1_relat_1(sK1)
% 2.37/1.02      | k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)) ),
% 2.37/1.02      inference(unflattening,[status(thm)],[c_209]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_16,negated_conjecture,
% 2.37/1.02      ( v1_relat_1(sK1) ),
% 2.37/1.02      inference(cnf_transformation,[],[f46]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_214,plain,
% 2.37/1.02      ( ~ r2_hidden(X1,k1_relat_1(sK1))
% 2.37/1.02      | ~ r2_hidden(X0,k1_relat_1(sK1))
% 2.37/1.02      | k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)) ),
% 2.37/1.02      inference(global_propositional_subsumption,[status(thm)],[c_210,c_16]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_215,plain,
% 2.37/1.02      ( ~ r2_hidden(X0,k1_relat_1(sK1))
% 2.37/1.02      | ~ r2_hidden(X1,k1_relat_1(sK1))
% 2.37/1.02      | k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)) ),
% 2.37/1.02      inference(renaming,[status(thm)],[c_214]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_890,plain,
% 2.37/1.02      ( k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1))
% 2.37/1.02      | r2_hidden(X0,k1_relat_1(sK1)) != iProver_top
% 2.37/1.02      | r2_hidden(X1,k1_relat_1(sK1)) != iProver_top ),
% 2.37/1.02      inference(predicate_to_equality,[status(thm)],[c_215]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_2463,plain,
% 2.37/1.02      ( k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1))
% 2.37/1.02      | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k1_relat_1(sK1)) = k2_enumset1(X0,X0,X0,X0)
% 2.37/1.02      | r2_hidden(X1,k1_relat_1(sK1)) != iProver_top ),
% 2.37/1.02      inference(superposition,[status(thm)],[c_1402,c_890]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_2469,plain,
% 2.37/1.02      ( k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1))
% 2.37/1.02      | k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k1_relat_1(sK1)) = k2_enumset1(X1,X1,X1,X1)
% 2.37/1.02      | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k1_relat_1(sK1)) = k2_enumset1(X0,X0,X0,X0) ),
% 2.37/1.02      inference(superposition,[status(thm)],[c_1402,c_2463]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_14,negated_conjecture,
% 2.37/1.02      ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
% 2.37/1.02      inference(cnf_transformation,[],[f53]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_891,plain,
% 2.37/1.02      ( r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) != iProver_top ),
% 2.37/1.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_8,plain,
% 2.37/1.02      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.37/1.02      inference(cnf_transformation,[],[f40]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_258,plain,
% 2.37/1.02      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) | sK1 != X0 ),
% 2.37/1.02      inference(resolution_lifted,[status(thm)],[c_8,c_16]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_259,plain,
% 2.37/1.02      ( k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
% 2.37/1.02      inference(unflattening,[status(thm)],[c_258]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_939,plain,
% 2.37/1.02      ( r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) != iProver_top ),
% 2.37/1.02      inference(demodulation,[status(thm)],[c_891,c_259]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_2576,plain,
% 2.37/1.02      ( k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK1)) = k2_enumset1(sK0,sK0,sK0,sK0)
% 2.37/1.02      | r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != iProver_top ),
% 2.37/1.02      inference(superposition,[status(thm)],[c_2469,c_939]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_217,plain,
% 2.37/1.02      ( ~ r2_hidden(sK0,k1_relat_1(sK1))
% 2.37/1.02      | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) = k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
% 2.37/1.02      inference(instantiation,[status(thm)],[c_215]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_991,plain,
% 2.37/1.02      ( r2_hidden(X0,k1_relat_1(sK1))
% 2.37/1.02      | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k1_relat_1(sK1)) ),
% 2.37/1.02      inference(instantiation,[status(thm)],[c_7]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_993,plain,
% 2.37/1.02      ( r2_hidden(sK0,k1_relat_1(sK1))
% 2.37/1.02      | r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK1)) ),
% 2.37/1.02      inference(instantiation,[status(thm)],[c_991]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_1057,plain,
% 2.37/1.02      ( k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
% 2.37/1.02      inference(instantiation,[status(thm)],[c_259]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_552,plain,
% 2.37/1.02      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.37/1.02      theory(equality) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_996,plain,
% 2.37/1.02      ( ~ r1_tarski(X0,X1)
% 2.37/1.02      | r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
% 2.37/1.02      | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != X1
% 2.37/1.02      | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != X0 ),
% 2.37/1.02      inference(instantiation,[status(thm)],[c_552]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_1056,plain,
% 2.37/1.02      ( ~ r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0)
% 2.37/1.02      | r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
% 2.37/1.02      | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != X0
% 2.37/1.02      | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
% 2.37/1.02      inference(instantiation,[status(thm)],[c_996]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_1148,plain,
% 2.37/1.02      ( ~ r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
% 2.37/1.02      | r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
% 2.37/1.02      | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
% 2.37/1.02      | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
% 2.37/1.02      inference(instantiation,[status(thm)],[c_1056]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f54]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_1149,plain,
% 2.37/1.02      ( r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
% 2.37/1.02      inference(instantiation,[status(thm)],[c_1]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_1329,plain,
% 2.37/1.02      ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k1_relat_1(sK1))
% 2.37/1.02      | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k1_relat_1(sK1)) = k2_enumset1(X0,X0,X0,X0) ),
% 2.37/1.02      inference(instantiation,[status(thm)],[c_5]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_1331,plain,
% 2.37/1.02      ( ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK1))
% 2.37/1.02      | k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK1)) = k2_enumset1(sK0,sK0,sK0,sK0) ),
% 2.37/1.02      inference(instantiation,[status(thm)],[c_1329]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_2847,plain,
% 2.37/1.02      ( k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK1)) = k2_enumset1(sK0,sK0,sK0,sK0) ),
% 2.37/1.02      inference(global_propositional_subsumption,
% 2.37/1.02                [status(thm)],
% 2.37/1.02                [c_2576,c_14,c_217,c_993,c_1057,c_1148,c_1149,c_1331]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_897,plain,
% 2.37/1.02      ( r1_tarski(X0,X0) = iProver_top ),
% 2.37/1.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_6,plain,
% 2.37/1.02      ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) | ~ r1_tarski(X0,X2) ),
% 2.37/1.02      inference(cnf_transformation,[],[f35]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_893,plain,
% 2.37/1.02      ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top
% 2.37/1.02      | r1_tarski(X0,X2) != iProver_top ),
% 2.37/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_1304,plain,
% 2.37/1.02      ( k4_xboole_0(X0,k4_xboole_0(X1,X2)) = X0
% 2.37/1.02      | r1_tarski(X0,X2) != iProver_top ),
% 2.37/1.02      inference(superposition,[status(thm)],[c_893,c_894]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_1407,plain,
% 2.37/1.02      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 2.37/1.02      inference(superposition,[status(thm)],[c_897,c_1304]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_4,plain,
% 2.37/1.02      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 2.37/1.02      inference(cnf_transformation,[],[f34]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_895,plain,
% 2.37/1.02      ( k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1) = iProver_top ),
% 2.37/1.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_1543,plain,
% 2.37/1.02      ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
% 2.37/1.02      inference(superposition,[status(thm)],[c_1407,c_895]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_11,plain,
% 2.37/1.02      ( ~ r1_xboole_0(k1_relat_1(X0),X1)
% 2.37/1.02      | ~ v1_relat_1(X0)
% 2.37/1.02      | k7_relat_1(X0,X1) = k1_xboole_0 ),
% 2.37/1.02      inference(cnf_transformation,[],[f44]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_246,plain,
% 2.37/1.02      ( ~ r1_xboole_0(k1_relat_1(X0),X1)
% 2.37/1.02      | k7_relat_1(X0,X1) = k1_xboole_0
% 2.37/1.02      | sK1 != X0 ),
% 2.37/1.02      inference(resolution_lifted,[status(thm)],[c_11,c_16]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_247,plain,
% 2.37/1.02      ( ~ r1_xboole_0(k1_relat_1(sK1),X0) | k7_relat_1(sK1,X0) = k1_xboole_0 ),
% 2.37/1.02      inference(unflattening,[status(thm)],[c_246]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_400,plain,
% 2.37/1.02      ( ~ r1_xboole_0(k1_relat_1(sK1),X0) | k7_relat_1(sK1,X0) = k1_xboole_0 ),
% 2.37/1.02      inference(prop_impl,[status(thm)],[c_247]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_888,plain,
% 2.37/1.02      ( k7_relat_1(sK1,X0) = k1_xboole_0
% 2.37/1.02      | r1_xboole_0(k1_relat_1(sK1),X0) != iProver_top ),
% 2.37/1.02      inference(predicate_to_equality,[status(thm)],[c_400]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_1971,plain,
% 2.37/1.02      ( k7_relat_1(sK1,k4_xboole_0(X0,k1_relat_1(sK1))) = k1_xboole_0 ),
% 2.37/1.02      inference(superposition,[status(thm)],[c_1543,c_888]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_2059,plain,
% 2.37/1.02      ( k9_relat_1(sK1,k4_xboole_0(X0,k1_relat_1(sK1))) = k2_relat_1(k1_xboole_0) ),
% 2.37/1.02      inference(superposition,[status(thm)],[c_1971,c_259]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_9,plain,
% 2.37/1.02      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.37/1.02      inference(cnf_transformation,[],[f42]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_2061,plain,
% 2.37/1.02      ( k9_relat_1(sK1,k4_xboole_0(X0,k1_relat_1(sK1))) = k1_xboole_0 ),
% 2.37/1.02      inference(light_normalisation,[status(thm)],[c_2059,c_9]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_2856,plain,
% 2.37/1.02      ( k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
% 2.37/1.02      inference(superposition,[status(thm)],[c_2847,c_2061]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_3094,plain,
% 2.37/1.02      ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) != iProver_top ),
% 2.37/1.02      inference(demodulation,[status(thm)],[c_2856,c_939]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_3,plain,
% 2.37/1.02      ( r1_tarski(k1_xboole_0,X0) ),
% 2.37/1.02      inference(cnf_transformation,[],[f32]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_896,plain,
% 2.37/1.02      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.37/1.02      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.37/1.02  
% 2.37/1.02  cnf(c_3201,plain,
% 2.37/1.02      ( $false ),
% 2.37/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_3094,c_896]) ).
% 2.37/1.02  
% 2.37/1.02  
% 2.37/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.37/1.02  
% 2.37/1.02  ------                               Statistics
% 2.37/1.02  
% 2.37/1.02  ------ General
% 2.37/1.02  
% 2.37/1.02  abstr_ref_over_cycles:                  0
% 2.37/1.02  abstr_ref_under_cycles:                 0
% 2.37/1.02  gc_basic_clause_elim:                   0
% 2.37/1.02  forced_gc_time:                         0
% 2.37/1.02  parsing_time:                           0.018
% 2.37/1.02  unif_index_cands_time:                  0.
% 2.37/1.02  unif_index_add_time:                    0.
% 2.37/1.02  orderings_time:                         0.
% 2.37/1.02  out_proof_time:                         0.009
% 2.37/1.02  total_time:                             0.156
% 2.37/1.02  num_of_symbols:                         46
% 2.37/1.02  num_of_terms:                           2595
% 2.37/1.02  
% 2.37/1.02  ------ Preprocessing
% 2.37/1.02  
% 2.37/1.02  num_of_splits:                          0
% 2.37/1.02  num_of_split_atoms:                     0
% 2.37/1.02  num_of_reused_defs:                     0
% 2.37/1.02  num_eq_ax_congr_red:                    10
% 2.37/1.02  num_of_sem_filtered_clauses:            1
% 2.37/1.02  num_of_subtypes:                        0
% 2.37/1.02  monotx_restored_types:                  0
% 2.37/1.02  sat_num_of_epr_types:                   0
% 2.37/1.02  sat_num_of_non_cyclic_types:            0
% 2.37/1.02  sat_guarded_non_collapsed_types:        0
% 2.37/1.02  num_pure_diseq_elim:                    0
% 2.37/1.02  simp_replaced_by:                       0
% 2.37/1.02  res_preprocessed:                       81
% 2.37/1.02  prep_upred:                             0
% 2.37/1.02  prep_unflattend:                        26
% 2.37/1.02  smt_new_axioms:                         0
% 2.37/1.02  pred_elim_cands:                        3
% 2.37/1.02  pred_elim:                              2
% 2.37/1.02  pred_elim_cl:                           2
% 2.37/1.02  pred_elim_cycles:                       4
% 2.37/1.02  merged_defs:                            14
% 2.37/1.02  merged_defs_ncl:                        0
% 2.37/1.02  bin_hyper_res:                          14
% 2.37/1.02  prep_cycles:                            4
% 2.37/1.02  pred_elim_time:                         0.005
% 2.37/1.02  splitting_time:                         0.
% 2.37/1.02  sem_filter_time:                        0.
% 2.37/1.02  monotx_time:                            0.
% 2.37/1.02  subtype_inf_time:                       0.
% 2.37/1.02  
% 2.37/1.02  ------ Problem properties
% 2.37/1.02  
% 2.37/1.02  clauses:                                14
% 2.37/1.02  conjectures:                            1
% 2.37/1.02  epr:                                    3
% 2.37/1.02  horn:                                   13
% 2.37/1.02  ground:                                 3
% 2.37/1.02  unary:                                  6
% 2.37/1.02  binary:                                 6
% 2.37/1.02  lits:                                   24
% 2.37/1.02  lits_eq:                                9
% 2.37/1.02  fd_pure:                                0
% 2.37/1.02  fd_pseudo:                              0
% 2.37/1.02  fd_cond:                                0
% 2.37/1.02  fd_pseudo_cond:                         1
% 2.37/1.02  ac_symbols:                             0
% 2.37/1.02  
% 2.37/1.02  ------ Propositional Solver
% 2.37/1.02  
% 2.37/1.02  prop_solver_calls:                      28
% 2.37/1.02  prop_fast_solver_calls:                 449
% 2.37/1.02  smt_solver_calls:                       0
% 2.37/1.02  smt_fast_solver_calls:                  0
% 2.37/1.02  prop_num_of_clauses:                    1068
% 2.37/1.02  prop_preprocess_simplified:             3384
% 2.37/1.02  prop_fo_subsumed:                       2
% 2.37/1.02  prop_solver_time:                       0.
% 2.37/1.02  smt_solver_time:                        0.
% 2.37/1.02  smt_fast_solver_time:                   0.
% 2.37/1.02  prop_fast_solver_time:                  0.
% 2.37/1.02  prop_unsat_core_time:                   0.
% 2.37/1.02  
% 2.37/1.02  ------ QBF
% 2.37/1.02  
% 2.37/1.02  qbf_q_res:                              0
% 2.37/1.02  qbf_num_tautologies:                    0
% 2.37/1.02  qbf_prep_cycles:                        0
% 2.37/1.02  
% 2.37/1.02  ------ BMC1
% 2.37/1.02  
% 2.37/1.02  bmc1_current_bound:                     -1
% 2.37/1.02  bmc1_last_solved_bound:                 -1
% 2.37/1.02  bmc1_unsat_core_size:                   -1
% 2.37/1.02  bmc1_unsat_core_parents_size:           -1
% 2.37/1.02  bmc1_merge_next_fun:                    0
% 2.37/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.37/1.02  
% 2.37/1.02  ------ Instantiation
% 2.37/1.02  
% 2.37/1.02  inst_num_of_clauses:                    326
% 2.37/1.02  inst_num_in_passive:                    30
% 2.37/1.02  inst_num_in_active:                     202
% 2.37/1.02  inst_num_in_unprocessed:                94
% 2.37/1.02  inst_num_of_loops:                      210
% 2.37/1.02  inst_num_of_learning_restarts:          0
% 2.37/1.02  inst_num_moves_active_passive:          5
% 2.37/1.02  inst_lit_activity:                      0
% 2.37/1.02  inst_lit_activity_moves:                0
% 2.37/1.02  inst_num_tautologies:                   0
% 2.37/1.02  inst_num_prop_implied:                  0
% 2.37/1.02  inst_num_existing_simplified:           0
% 2.37/1.02  inst_num_eq_res_simplified:             0
% 2.37/1.02  inst_num_child_elim:                    0
% 2.37/1.02  inst_num_of_dismatching_blockings:      87
% 2.37/1.02  inst_num_of_non_proper_insts:           395
% 2.37/1.02  inst_num_of_duplicates:                 0
% 2.37/1.02  inst_inst_num_from_inst_to_res:         0
% 2.37/1.02  inst_dismatching_checking_time:         0.
% 2.37/1.02  
% 2.37/1.02  ------ Resolution
% 2.37/1.02  
% 2.37/1.02  res_num_of_clauses:                     0
% 2.37/1.02  res_num_in_passive:                     0
% 2.37/1.02  res_num_in_active:                      0
% 2.37/1.02  res_num_of_loops:                       85
% 2.37/1.02  res_forward_subset_subsumed:            75
% 2.37/1.02  res_backward_subset_subsumed:           0
% 2.37/1.02  res_forward_subsumed:                   0
% 2.37/1.02  res_backward_subsumed:                  0
% 2.37/1.02  res_forward_subsumption_resolution:     0
% 2.37/1.02  res_backward_subsumption_resolution:    0
% 2.37/1.02  res_clause_to_clause_subsumption:       227
% 2.37/1.02  res_orphan_elimination:                 0
% 2.37/1.02  res_tautology_del:                      64
% 2.37/1.02  res_num_eq_res_simplified:              0
% 2.37/1.02  res_num_sel_changes:                    0
% 2.37/1.02  res_moves_from_active_to_pass:          0
% 2.37/1.02  
% 2.37/1.02  ------ Superposition
% 2.37/1.02  
% 2.37/1.02  sup_time_total:                         0.
% 2.37/1.02  sup_time_generating:                    0.
% 2.37/1.02  sup_time_sim_full:                      0.
% 2.37/1.02  sup_time_sim_immed:                     0.
% 2.37/1.02  
% 2.37/1.02  sup_num_of_clauses:                     67
% 2.37/1.02  sup_num_in_active:                      38
% 2.37/1.02  sup_num_in_passive:                     29
% 2.37/1.02  sup_num_of_loops:                       40
% 2.37/1.02  sup_fw_superposition:                   32
% 2.37/1.02  sup_bw_superposition:                   66
% 2.37/1.02  sup_immediate_simplified:               9
% 2.37/1.02  sup_given_eliminated:                   1
% 2.37/1.02  comparisons_done:                       0
% 2.37/1.02  comparisons_avoided:                    24
% 2.37/1.02  
% 2.37/1.02  ------ Simplifications
% 2.37/1.02  
% 2.37/1.02  
% 2.37/1.02  sim_fw_subset_subsumed:                 1
% 2.37/1.02  sim_bw_subset_subsumed:                 1
% 2.37/1.02  sim_fw_subsumed:                        6
% 2.37/1.02  sim_bw_subsumed:                        2
% 2.37/1.02  sim_fw_subsumption_res:                 1
% 2.37/1.02  sim_bw_subsumption_res:                 0
% 2.37/1.02  sim_tautology_del:                      0
% 2.37/1.02  sim_eq_tautology_del:                   2
% 2.37/1.02  sim_eq_res_simp:                        1
% 2.37/1.02  sim_fw_demodulated:                     1
% 2.37/1.02  sim_bw_demodulated:                     1
% 2.37/1.02  sim_light_normalised:                   2
% 2.37/1.02  sim_joinable_taut:                      0
% 2.37/1.02  sim_joinable_simp:                      0
% 2.37/1.02  sim_ac_normalised:                      0
% 2.37/1.02  sim_smt_subsumption:                    0
% 2.37/1.02  
%------------------------------------------------------------------------------
