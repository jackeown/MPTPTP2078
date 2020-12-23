%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:48 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 351 expanded)
%              Number of clauses        :   48 (  97 expanded)
%              Number of leaves         :   13 (  83 expanded)
%              Depth                    :   20
%              Number of atoms          :  229 ( 825 expanded)
%              Number of equality atoms :  105 ( 321 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f22])).

fof(f38,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f29,f30])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f40])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X1,k1_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) )
       => k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_enumset1(X0,X0,X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f36,f40,f40])).

fof(f37,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f39,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f28,f40])).

fof(f44,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
    inference(definition_unfolding,[],[f39,f41,f41])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f24])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_11,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_380,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | r1_xboole_0(k2_enumset1(X0,X0,X0,X2),X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_385,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X2,X1) = iProver_top
    | r1_xboole_0(k2_enumset1(X0,X0,X0,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_383,plain,
    ( k7_relat_1(X0,X1) = k1_xboole_0
    | r1_xboole_0(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_977,plain,
    ( k7_relat_1(X0,k2_enumset1(X1,X1,X1,X2)) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
    | r2_hidden(X2,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_385,c_383])).

cnf(c_1380,plain,
    ( k7_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_977])).

cnf(c_1382,plain,
    ( k7_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1380])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X0)) = k9_relat_1(X1,k2_enumset1(X2,X2,X2,X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_382,plain,
    ( k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X2)) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X2))
    | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2165,plain,
    ( k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X2)) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X2))
    | k7_relat_1(X0,k2_enumset1(X2,X2,X2,X2)) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1382,c_382])).

cnf(c_2351,plain,
    ( k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X2)) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X2))
    | k7_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k1_xboole_0
    | k7_relat_1(X0,k2_enumset1(X2,X2,X2,X2)) = k1_xboole_0
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1382,c_2165])).

cnf(c_2571,plain,
    ( k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1))
    | k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0
    | k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X1)) = k1_xboole_0
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_380,c_2351])).

cnf(c_12,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2572,plain,
    ( ~ v1_relat_1(sK1)
    | k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1))
    | k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0
    | k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X1)) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2571])).

cnf(c_2681,plain,
    ( k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X1)) = k1_xboole_0
    | k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0
    | k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2571,c_12,c_2572])).

cnf(c_2682,plain,
    ( k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1))
    | k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0
    | k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X1)) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2681])).

cnf(c_379,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_384,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_669,plain,
    ( k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(superposition,[status(thm)],[c_379,c_384])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_381,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1002,plain,
    ( r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_669,c_381])).

cnf(c_2692,plain,
    ( k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0
    | r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2682,c_1002])).

cnf(c_507,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK1))
    | ~ r2_hidden(X1,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k2_enumset1(k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X0)) = k9_relat_1(sK1,k2_enumset1(X1,X1,X1,X0)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_509,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) = k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_507])).

cnf(c_482,plain,
    ( ~ v1_relat_1(sK1)
    | k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_564,plain,
    ( ~ v1_relat_1(sK1)
    | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_482])).

cnf(c_598,plain,
    ( r2_hidden(X0,k1_relat_1(sK1))
    | r2_hidden(X1,k1_relat_1(sK1))
    | r1_xboole_0(k2_enumset1(X0,X0,X0,X1),k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_600,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_598])).

cnf(c_163,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_502,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != X1
    | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != X0 ),
    inference(instantiation,[status(thm)],[c_163])).

cnf(c_563,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0)
    | r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != X0
    | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_502])).

cnf(c_744,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_563])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_862,plain,
    ( r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1125,plain,
    ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X1),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1127,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1125])).

cnf(c_2753,plain,
    ( k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2692,c_12,c_11,c_10,c_509,c_564,c_600,c_744,c_862,c_1127])).

cnf(c_2756,plain,
    ( k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2753,c_669])).

cnf(c_7,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2757,plain,
    ( k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2756,c_7])).

cnf(c_3078,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2757,c_1002])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_386,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3778,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3078,c_386])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:31:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.97/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.00  
% 2.97/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.97/1.00  
% 2.97/1.00  ------  iProver source info
% 2.97/1.00  
% 2.97/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.97/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.97/1.00  git: non_committed_changes: false
% 2.97/1.00  git: last_make_outside_of_git: false
% 2.97/1.00  
% 2.97/1.00  ------ 
% 2.97/1.00  ------ Parsing...
% 2.97/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.97/1.00  
% 2.97/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 2.97/1.00  
% 2.97/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.97/1.00  
% 2.97/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.97/1.00  ------ Proving...
% 2.97/1.00  ------ Problem Properties 
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  clauses                                 12
% 2.97/1.00  conjectures                             3
% 2.97/1.00  EPR                                     5
% 2.97/1.00  Horn                                    11
% 2.97/1.00  unary                                   7
% 2.97/1.00  binary                                  1
% 2.97/1.00  lits                                    23
% 2.97/1.00  lits eq                                 6
% 2.97/1.00  fd_pure                                 0
% 2.97/1.00  fd_pseudo                               0
% 2.97/1.00  fd_cond                                 0
% 2.97/1.00  fd_pseudo_cond                          1
% 2.97/1.00  AC symbols                              0
% 2.97/1.00  
% 2.97/1.00  ------ Input Options Time Limit: Unbounded
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  ------ 
% 2.97/1.00  Current options:
% 2.97/1.00  ------ 
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  ------ Proving...
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  % SZS status Theorem for theBenchmark.p
% 2.97/1.00  
% 2.97/1.00   Resolution empty clause
% 2.97/1.00  
% 2.97/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.97/1.00  
% 2.97/1.00  fof(f11,conjecture,(
% 2.97/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f12,negated_conjecture,(
% 2.97/1.00    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 2.97/1.00    inference(negated_conjecture,[],[f11])).
% 2.97/1.00  
% 2.97/1.00  fof(f18,plain,(
% 2.97/1.00    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 2.97/1.00    inference(ennf_transformation,[],[f12])).
% 2.97/1.00  
% 2.97/1.00  fof(f19,plain,(
% 2.97/1.00    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.97/1.00    inference(flattening,[],[f18])).
% 2.97/1.00  
% 2.97/1.00  fof(f22,plain,(
% 2.97/1.00    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 2.97/1.00    introduced(choice_axiom,[])).
% 2.97/1.00  
% 2.97/1.00  fof(f23,plain,(
% 2.97/1.00    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 2.97/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f22])).
% 2.97/1.00  
% 2.97/1.00  fof(f38,plain,(
% 2.97/1.00    v1_funct_1(sK1)),
% 2.97/1.00    inference(cnf_transformation,[],[f23])).
% 2.97/1.00  
% 2.97/1.00  fof(f6,axiom,(
% 2.97/1.00    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f13,plain,(
% 2.97/1.00    ! [X0,X1,X2] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 2.97/1.00    inference(ennf_transformation,[],[f6])).
% 2.97/1.00  
% 2.97/1.00  fof(f31,plain,(
% 2.97/1.00    ( ! [X2,X0,X1] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f13])).
% 2.97/1.00  
% 2.97/1.00  fof(f4,axiom,(
% 2.97/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f29,plain,(
% 2.97/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f4])).
% 2.97/1.00  
% 2.97/1.00  fof(f5,axiom,(
% 2.97/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f30,plain,(
% 2.97/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f5])).
% 2.97/1.00  
% 2.97/1.00  fof(f40,plain,(
% 2.97/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.97/1.00    inference(definition_unfolding,[],[f29,f30])).
% 2.97/1.00  
% 2.97/1.00  fof(f42,plain,(
% 2.97/1.00    ( ! [X2,X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 2.97/1.00    inference(definition_unfolding,[],[f31,f40])).
% 2.97/1.00  
% 2.97/1.00  fof(f8,axiom,(
% 2.97/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f15,plain,(
% 2.97/1.00    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.97/1.00    inference(ennf_transformation,[],[f8])).
% 2.97/1.00  
% 2.97/1.00  fof(f33,plain,(
% 2.97/1.00    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f15])).
% 2.97/1.00  
% 2.97/1.00  fof(f10,axiom,(
% 2.97/1.00    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X1,k1_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) => k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f16,plain,(
% 2.97/1.00    ! [X0,X1,X2] : ((k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | (~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.97/1.00    inference(ennf_transformation,[],[f10])).
% 2.97/1.00  
% 2.97/1.00  fof(f17,plain,(
% 2.97/1.00    ! [X0,X1,X2] : (k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.97/1.00    inference(flattening,[],[f16])).
% 2.97/1.00  
% 2.97/1.00  fof(f36,plain,(
% 2.97/1.00    ( ! [X2,X0,X1] : (k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f17])).
% 2.97/1.00  
% 2.97/1.00  fof(f43,plain,(
% 2.97/1.00    ( ! [X2,X0,X1] : (k2_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_enumset1(X0,X0,X0,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.97/1.00    inference(definition_unfolding,[],[f36,f40,f40])).
% 2.97/1.00  
% 2.97/1.00  fof(f37,plain,(
% 2.97/1.00    v1_relat_1(sK1)),
% 2.97/1.00    inference(cnf_transformation,[],[f23])).
% 2.97/1.00  
% 2.97/1.00  fof(f7,axiom,(
% 2.97/1.00    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f14,plain,(
% 2.97/1.00    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.97/1.00    inference(ennf_transformation,[],[f7])).
% 2.97/1.00  
% 2.97/1.00  fof(f32,plain,(
% 2.97/1.00    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f14])).
% 2.97/1.00  
% 2.97/1.00  fof(f39,plain,(
% 2.97/1.00    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))),
% 2.97/1.00    inference(cnf_transformation,[],[f23])).
% 2.97/1.00  
% 2.97/1.00  fof(f3,axiom,(
% 2.97/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f28,plain,(
% 2.97/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f3])).
% 2.97/1.00  
% 2.97/1.00  fof(f41,plain,(
% 2.97/1.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.97/1.00    inference(definition_unfolding,[],[f28,f40])).
% 2.97/1.00  
% 2.97/1.00  fof(f44,plain,(
% 2.97/1.00    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))),
% 2.97/1.00    inference(definition_unfolding,[],[f39,f41,f41])).
% 2.97/1.00  
% 2.97/1.00  fof(f1,axiom,(
% 2.97/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f20,plain,(
% 2.97/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.97/1.00    inference(nnf_transformation,[],[f1])).
% 2.97/1.00  
% 2.97/1.00  fof(f21,plain,(
% 2.97/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.97/1.00    inference(flattening,[],[f20])).
% 2.97/1.00  
% 2.97/1.00  fof(f24,plain,(
% 2.97/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.97/1.00    inference(cnf_transformation,[],[f21])).
% 2.97/1.00  
% 2.97/1.00  fof(f46,plain,(
% 2.97/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.97/1.00    inference(equality_resolution,[],[f24])).
% 2.97/1.00  
% 2.97/1.00  fof(f9,axiom,(
% 2.97/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f35,plain,(
% 2.97/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.97/1.00    inference(cnf_transformation,[],[f9])).
% 2.97/1.00  
% 2.97/1.00  fof(f2,axiom,(
% 2.97/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.97/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.00  
% 2.97/1.00  fof(f27,plain,(
% 2.97/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.97/1.00    inference(cnf_transformation,[],[f2])).
% 2.97/1.00  
% 2.97/1.00  cnf(c_11,negated_conjecture,
% 2.97/1.00      ( v1_funct_1(sK1) ),
% 2.97/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_380,plain,
% 2.97/1.00      ( v1_funct_1(sK1) = iProver_top ),
% 2.97/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_4,plain,
% 2.97/1.00      ( r2_hidden(X0,X1)
% 2.97/1.00      | r2_hidden(X2,X1)
% 2.97/1.00      | r1_xboole_0(k2_enumset1(X0,X0,X0,X2),X1) ),
% 2.97/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.97/1.00  
% 2.97/1.00  cnf(c_385,plain,
% 2.97/1.00      ( r2_hidden(X0,X1) = iProver_top
% 2.97/1.00      | r2_hidden(X2,X1) = iProver_top
% 2.97/1.00      | r1_xboole_0(k2_enumset1(X0,X0,X0,X2),X1) = iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_6,plain,
% 2.97/1.01      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 2.97/1.01      | ~ v1_relat_1(X1)
% 2.97/1.01      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 2.97/1.01      inference(cnf_transformation,[],[f33]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_383,plain,
% 2.97/1.01      ( k7_relat_1(X0,X1) = k1_xboole_0
% 2.97/1.01      | r1_xboole_0(X1,k1_relat_1(X0)) != iProver_top
% 2.97/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_977,plain,
% 2.97/1.01      ( k7_relat_1(X0,k2_enumset1(X1,X1,X1,X2)) = k1_xboole_0
% 2.97/1.01      | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
% 2.97/1.01      | r2_hidden(X2,k1_relat_1(X0)) = iProver_top
% 2.97/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.97/1.01      inference(superposition,[status(thm)],[c_385,c_383]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_1380,plain,
% 2.97/1.01      ( k7_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k1_xboole_0
% 2.97/1.01      | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
% 2.97/1.01      | v1_relat_1(X0) != iProver_top
% 2.97/1.01      | iProver_top != iProver_top ),
% 2.97/1.01      inference(equality_factoring,[status(thm)],[c_977]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_1382,plain,
% 2.97/1.01      ( k7_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k1_xboole_0
% 2.97/1.01      | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
% 2.97/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.97/1.01      inference(equality_resolution_simp,[status(thm)],[c_1380]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_9,plain,
% 2.97/1.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.97/1.01      | ~ r2_hidden(X2,k1_relat_1(X1))
% 2.97/1.01      | ~ v1_funct_1(X1)
% 2.97/1.01      | ~ v1_relat_1(X1)
% 2.97/1.01      | k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X0)) = k9_relat_1(X1,k2_enumset1(X2,X2,X2,X0)) ),
% 2.97/1.01      inference(cnf_transformation,[],[f43]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_382,plain,
% 2.97/1.01      ( k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X2)) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X2))
% 2.97/1.01      | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
% 2.97/1.01      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 2.97/1.01      | v1_funct_1(X0) != iProver_top
% 2.97/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2165,plain,
% 2.97/1.01      ( k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X2)) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X2))
% 2.97/1.01      | k7_relat_1(X0,k2_enumset1(X2,X2,X2,X2)) = k1_xboole_0
% 2.97/1.01      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 2.97/1.01      | v1_funct_1(X0) != iProver_top
% 2.97/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.97/1.01      inference(superposition,[status(thm)],[c_1382,c_382]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2351,plain,
% 2.97/1.01      ( k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X2)) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X2))
% 2.97/1.01      | k7_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k1_xboole_0
% 2.97/1.01      | k7_relat_1(X0,k2_enumset1(X2,X2,X2,X2)) = k1_xboole_0
% 2.97/1.01      | v1_funct_1(X0) != iProver_top
% 2.97/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.97/1.01      inference(superposition,[status(thm)],[c_1382,c_2165]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2571,plain,
% 2.97/1.01      ( k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1))
% 2.97/1.01      | k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0
% 2.97/1.01      | k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X1)) = k1_xboole_0
% 2.97/1.01      | v1_relat_1(sK1) != iProver_top ),
% 2.97/1.01      inference(superposition,[status(thm)],[c_380,c_2351]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_12,negated_conjecture,
% 2.97/1.01      ( v1_relat_1(sK1) ),
% 2.97/1.01      inference(cnf_transformation,[],[f37]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2572,plain,
% 2.97/1.01      ( ~ v1_relat_1(sK1)
% 2.97/1.01      | k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1))
% 2.97/1.01      | k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0
% 2.97/1.01      | k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X1)) = k1_xboole_0 ),
% 2.97/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_2571]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2681,plain,
% 2.97/1.01      ( k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X1)) = k1_xboole_0
% 2.97/1.01      | k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0
% 2.97/1.01      | k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)) ),
% 2.97/1.01      inference(global_propositional_subsumption,
% 2.97/1.01                [status(thm)],
% 2.97/1.01                [c_2571,c_12,c_2572]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2682,plain,
% 2.97/1.01      ( k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1))
% 2.97/1.01      | k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0
% 2.97/1.01      | k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X1)) = k1_xboole_0 ),
% 2.97/1.01      inference(renaming,[status(thm)],[c_2681]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_379,plain,
% 2.97/1.01      ( v1_relat_1(sK1) = iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_5,plain,
% 2.97/1.01      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.97/1.01      inference(cnf_transformation,[],[f32]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_384,plain,
% 2.97/1.01      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 2.97/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_669,plain,
% 2.97/1.01      ( k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
% 2.97/1.01      inference(superposition,[status(thm)],[c_379,c_384]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_10,negated_conjecture,
% 2.97/1.01      ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
% 2.97/1.01      inference(cnf_transformation,[],[f44]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_381,plain,
% 2.97/1.01      ( r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) != iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_1002,plain,
% 2.97/1.01      ( r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) != iProver_top ),
% 2.97/1.01      inference(demodulation,[status(thm)],[c_669,c_381]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2692,plain,
% 2.97/1.01      ( k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0
% 2.97/1.01      | r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != iProver_top ),
% 2.97/1.01      inference(superposition,[status(thm)],[c_2682,c_1002]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_507,plain,
% 2.97/1.01      ( ~ r2_hidden(X0,k1_relat_1(sK1))
% 2.97/1.01      | ~ r2_hidden(X1,k1_relat_1(sK1))
% 2.97/1.01      | ~ v1_funct_1(sK1)
% 2.97/1.01      | ~ v1_relat_1(sK1)
% 2.97/1.01      | k2_enumset1(k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X0)) = k9_relat_1(sK1,k2_enumset1(X1,X1,X1,X0)) ),
% 2.97/1.01      inference(instantiation,[status(thm)],[c_9]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_509,plain,
% 2.97/1.01      ( ~ r2_hidden(sK0,k1_relat_1(sK1))
% 2.97/1.01      | ~ v1_funct_1(sK1)
% 2.97/1.01      | ~ v1_relat_1(sK1)
% 2.97/1.01      | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) = k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
% 2.97/1.01      inference(instantiation,[status(thm)],[c_507]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_482,plain,
% 2.97/1.01      ( ~ v1_relat_1(sK1)
% 2.97/1.01      | k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
% 2.97/1.01      inference(instantiation,[status(thm)],[c_5]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_564,plain,
% 2.97/1.01      ( ~ v1_relat_1(sK1)
% 2.97/1.01      | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
% 2.97/1.01      inference(instantiation,[status(thm)],[c_482]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_598,plain,
% 2.97/1.01      ( r2_hidden(X0,k1_relat_1(sK1))
% 2.97/1.01      | r2_hidden(X1,k1_relat_1(sK1))
% 2.97/1.01      | r1_xboole_0(k2_enumset1(X0,X0,X0,X1),k1_relat_1(sK1)) ),
% 2.97/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_600,plain,
% 2.97/1.01      ( r2_hidden(sK0,k1_relat_1(sK1))
% 2.97/1.01      | r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK1)) ),
% 2.97/1.01      inference(instantiation,[status(thm)],[c_598]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_163,plain,
% 2.97/1.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.97/1.01      theory(equality) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_502,plain,
% 2.97/1.01      ( ~ r1_tarski(X0,X1)
% 2.97/1.01      | r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
% 2.97/1.01      | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != X1
% 2.97/1.01      | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != X0 ),
% 2.97/1.01      inference(instantiation,[status(thm)],[c_163]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_563,plain,
% 2.97/1.01      ( ~ r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0)
% 2.97/1.01      | r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
% 2.97/1.01      | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != X0
% 2.97/1.01      | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
% 2.97/1.01      inference(instantiation,[status(thm)],[c_502]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_744,plain,
% 2.97/1.01      ( ~ r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
% 2.97/1.01      | r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
% 2.97/1.01      | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
% 2.97/1.01      | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
% 2.97/1.01      inference(instantiation,[status(thm)],[c_563]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f46]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_862,plain,
% 2.97/1.01      ( r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
% 2.97/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_1125,plain,
% 2.97/1.01      ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X1),k1_relat_1(sK1))
% 2.97/1.01      | ~ v1_relat_1(sK1)
% 2.97/1.01      | k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)) = k1_xboole_0 ),
% 2.97/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_1127,plain,
% 2.97/1.01      ( ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_relat_1(sK1))
% 2.97/1.01      | ~ v1_relat_1(sK1)
% 2.97/1.01      | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
% 2.97/1.01      inference(instantiation,[status(thm)],[c_1125]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2753,plain,
% 2.97/1.01      ( k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
% 2.97/1.01      inference(global_propositional_subsumption,
% 2.97/1.01                [status(thm)],
% 2.97/1.01                [c_2692,c_12,c_11,c_10,c_509,c_564,c_600,c_744,c_862,c_1127]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2756,plain,
% 2.97/1.01      ( k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k2_relat_1(k1_xboole_0) ),
% 2.97/1.01      inference(superposition,[status(thm)],[c_2753,c_669]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_7,plain,
% 2.97/1.01      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.97/1.01      inference(cnf_transformation,[],[f35]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2757,plain,
% 2.97/1.01      ( k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
% 2.97/1.01      inference(light_normalisation,[status(thm)],[c_2756,c_7]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_3078,plain,
% 2.97/1.01      ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) != iProver_top ),
% 2.97/1.01      inference(demodulation,[status(thm)],[c_2757,c_1002]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_3,plain,
% 2.97/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 2.97/1.01      inference(cnf_transformation,[],[f27]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_386,plain,
% 2.97/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_3778,plain,
% 2.97/1.01      ( $false ),
% 2.97/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_3078,c_386]) ).
% 2.97/1.01  
% 2.97/1.01  
% 2.97/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.97/1.01  
% 2.97/1.01  ------                               Statistics
% 2.97/1.01  
% 2.97/1.01  ------ Selected
% 2.97/1.01  
% 2.97/1.01  total_time:                             0.152
% 2.97/1.01  
%------------------------------------------------------------------------------
