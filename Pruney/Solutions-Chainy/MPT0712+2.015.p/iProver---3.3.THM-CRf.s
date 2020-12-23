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

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 365 expanded)
%              Number of clauses        :   36 (  91 expanded)
%              Number of leaves         :   12 (  86 expanded)
%              Depth                    :   20
%              Number of atoms          :  235 ( 853 expanded)
%              Number of equality atoms :  118 ( 298 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f30,f51])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f33,f52])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

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

fof(f19,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f25])).

fof(f48,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X1,k1_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) )
       => k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_enumset1(X0,X0,X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f47,f51,f51])).

fof(f49,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f50,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f64,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
    inference(definition_unfolding,[],[f50,f52,f52])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f21])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f65,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f28])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ~ ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3 ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(flattening,[],[f23])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
      | k1_xboole_0 != X3 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))
      | k1_xboole_0 != X3 ) ),
    inference(definition_unfolding,[],[f35,f32])).

fof(f74,plain,(
    ! [X2,X0,X1] : r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f61])).

cnf(c_3,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_14,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_203,plain,
    ( r2_hidden(X0,X1)
    | ~ v1_relat_1(X2)
    | k2_enumset1(X0,X0,X0,X0) != X3
    | k7_relat_1(X2,X3) = k1_xboole_0
    | k1_relat_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_14])).

cnf(c_204,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_203])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_247,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | k7_relat_1(X1,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_204,c_20])).

cnf(c_248,plain,
    ( r2_hidden(X0,k1_relat_1(sK1))
    | k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_247])).

cnf(c_610,plain,
    ( k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_248])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X0)) = k9_relat_1(X1,k2_enumset1(X2,X2,X2,X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_222,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X0)) = k9_relat_1(X1,k2_enumset1(X2,X2,X2,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_19])).

cnf(c_223,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK1))
    | ~ r2_hidden(X1,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)) ),
    inference(unflattening,[status(thm)],[c_222])).

cnf(c_227,plain,
    ( ~ r2_hidden(X1,k1_relat_1(sK1))
    | ~ r2_hidden(X0,k1_relat_1(sK1))
    | k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_223,c_20])).

cnf(c_228,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK1))
    | ~ r2_hidden(X1,k1_relat_1(sK1))
    | k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)) ),
    inference(renaming,[status(thm)],[c_227])).

cnf(c_611,plain,
    ( k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1))
    | r2_hidden(X0,k1_relat_1(sK1)) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_228])).

cnf(c_727,plain,
    ( k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1))
    | k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_610,c_611])).

cnf(c_812,plain,
    ( k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1))
    | k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X1)) = k1_xboole_0
    | k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_610,c_727])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_612,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_259,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_260,plain,
    ( k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_259])).

cnf(c_656,plain,
    ( r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_612,c_260])).

cnf(c_823,plain,
    ( k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0
    | r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_812,c_656])).

cnf(c_865,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_823])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1154,plain,
    ( r1_tarski(k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)),k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1160,plain,
    ( r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_1154])).

cnf(c_1605,plain,
    ( k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_823,c_865,c_1160])).

cnf(c_1608,plain,
    ( k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1605,c_260])).

cnf(c_15,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1609,plain,
    ( k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1608,c_15])).

cnf(c_1611,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1609,c_656])).

cnf(c_11,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_614,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1683,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1611,c_614])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n023.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:53:21 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.90/1.05  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.05  
% 1.90/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.90/1.05  
% 1.90/1.05  ------  iProver source info
% 1.90/1.05  
% 1.90/1.05  git: date: 2020-06-30 10:37:57 +0100
% 1.90/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.90/1.05  git: non_committed_changes: false
% 1.90/1.05  git: last_make_outside_of_git: false
% 1.90/1.05  
% 1.90/1.05  ------ 
% 1.90/1.05  
% 1.90/1.05  ------ Input Options
% 1.90/1.05  
% 1.90/1.05  --out_options                           all
% 1.90/1.05  --tptp_safe_out                         true
% 1.90/1.05  --problem_path                          ""
% 1.90/1.05  --include_path                          ""
% 1.90/1.05  --clausifier                            res/vclausify_rel
% 1.90/1.05  --clausifier_options                    --mode clausify
% 1.90/1.05  --stdin                                 false
% 1.90/1.05  --stats_out                             all
% 1.90/1.05  
% 1.90/1.05  ------ General Options
% 1.90/1.05  
% 1.90/1.05  --fof                                   false
% 1.90/1.05  --time_out_real                         305.
% 1.90/1.05  --time_out_virtual                      -1.
% 1.90/1.05  --symbol_type_check                     false
% 1.90/1.05  --clausify_out                          false
% 1.90/1.05  --sig_cnt_out                           false
% 1.90/1.05  --trig_cnt_out                          false
% 1.90/1.05  --trig_cnt_out_tolerance                1.
% 1.90/1.05  --trig_cnt_out_sk_spl                   false
% 1.90/1.05  --abstr_cl_out                          false
% 1.90/1.05  
% 1.90/1.05  ------ Global Options
% 1.90/1.05  
% 1.90/1.05  --schedule                              default
% 1.90/1.05  --add_important_lit                     false
% 1.90/1.05  --prop_solver_per_cl                    1000
% 1.90/1.05  --min_unsat_core                        false
% 1.90/1.05  --soft_assumptions                      false
% 1.90/1.05  --soft_lemma_size                       3
% 1.90/1.05  --prop_impl_unit_size                   0
% 1.90/1.05  --prop_impl_unit                        []
% 1.90/1.05  --share_sel_clauses                     true
% 1.90/1.05  --reset_solvers                         false
% 1.90/1.05  --bc_imp_inh                            [conj_cone]
% 1.90/1.05  --conj_cone_tolerance                   3.
% 1.90/1.05  --extra_neg_conj                        none
% 1.90/1.05  --large_theory_mode                     true
% 1.90/1.05  --prolific_symb_bound                   200
% 1.90/1.05  --lt_threshold                          2000
% 1.90/1.05  --clause_weak_htbl                      true
% 1.90/1.05  --gc_record_bc_elim                     false
% 1.90/1.05  
% 1.90/1.05  ------ Preprocessing Options
% 1.90/1.05  
% 1.90/1.05  --preprocessing_flag                    true
% 1.90/1.05  --time_out_prep_mult                    0.1
% 1.90/1.05  --splitting_mode                        input
% 1.90/1.05  --splitting_grd                         true
% 1.90/1.05  --splitting_cvd                         false
% 1.90/1.05  --splitting_cvd_svl                     false
% 1.90/1.05  --splitting_nvd                         32
% 1.90/1.05  --sub_typing                            true
% 1.90/1.05  --prep_gs_sim                           true
% 1.90/1.05  --prep_unflatten                        true
% 1.90/1.05  --prep_res_sim                          true
% 1.90/1.05  --prep_upred                            true
% 1.90/1.05  --prep_sem_filter                       exhaustive
% 1.90/1.05  --prep_sem_filter_out                   false
% 1.90/1.05  --pred_elim                             true
% 1.90/1.05  --res_sim_input                         true
% 1.90/1.05  --eq_ax_congr_red                       true
% 1.90/1.05  --pure_diseq_elim                       true
% 1.90/1.05  --brand_transform                       false
% 1.90/1.05  --non_eq_to_eq                          false
% 1.90/1.05  --prep_def_merge                        true
% 1.90/1.05  --prep_def_merge_prop_impl              false
% 1.90/1.05  --prep_def_merge_mbd                    true
% 1.90/1.05  --prep_def_merge_tr_red                 false
% 1.90/1.05  --prep_def_merge_tr_cl                  false
% 1.90/1.05  --smt_preprocessing                     true
% 1.90/1.05  --smt_ac_axioms                         fast
% 1.90/1.05  --preprocessed_out                      false
% 1.90/1.05  --preprocessed_stats                    false
% 1.90/1.05  
% 1.90/1.05  ------ Abstraction refinement Options
% 1.90/1.05  
% 1.90/1.05  --abstr_ref                             []
% 1.90/1.05  --abstr_ref_prep                        false
% 1.90/1.05  --abstr_ref_until_sat                   false
% 1.90/1.05  --abstr_ref_sig_restrict                funpre
% 1.90/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 1.90/1.05  --abstr_ref_under                       []
% 1.90/1.05  
% 1.90/1.05  ------ SAT Options
% 1.90/1.05  
% 1.90/1.05  --sat_mode                              false
% 1.90/1.05  --sat_fm_restart_options                ""
% 1.90/1.05  --sat_gr_def                            false
% 1.90/1.05  --sat_epr_types                         true
% 1.90/1.05  --sat_non_cyclic_types                  false
% 1.90/1.05  --sat_finite_models                     false
% 1.90/1.05  --sat_fm_lemmas                         false
% 1.90/1.05  --sat_fm_prep                           false
% 1.90/1.05  --sat_fm_uc_incr                        true
% 1.90/1.05  --sat_out_model                         small
% 1.90/1.05  --sat_out_clauses                       false
% 1.90/1.05  
% 1.90/1.05  ------ QBF Options
% 1.90/1.05  
% 1.90/1.05  --qbf_mode                              false
% 1.90/1.05  --qbf_elim_univ                         false
% 1.90/1.05  --qbf_dom_inst                          none
% 1.90/1.05  --qbf_dom_pre_inst                      false
% 1.90/1.05  --qbf_sk_in                             false
% 1.90/1.05  --qbf_pred_elim                         true
% 1.90/1.05  --qbf_split                             512
% 1.90/1.05  
% 1.90/1.05  ------ BMC1 Options
% 1.90/1.05  
% 1.90/1.05  --bmc1_incremental                      false
% 1.90/1.05  --bmc1_axioms                           reachable_all
% 1.90/1.05  --bmc1_min_bound                        0
% 1.90/1.05  --bmc1_max_bound                        -1
% 1.90/1.05  --bmc1_max_bound_default                -1
% 1.90/1.05  --bmc1_symbol_reachability              true
% 1.90/1.05  --bmc1_property_lemmas                  false
% 1.90/1.05  --bmc1_k_induction                      false
% 1.90/1.05  --bmc1_non_equiv_states                 false
% 1.90/1.05  --bmc1_deadlock                         false
% 1.90/1.05  --bmc1_ucm                              false
% 1.90/1.05  --bmc1_add_unsat_core                   none
% 1.90/1.05  --bmc1_unsat_core_children              false
% 1.90/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 1.90/1.05  --bmc1_out_stat                         full
% 1.90/1.05  --bmc1_ground_init                      false
% 1.90/1.05  --bmc1_pre_inst_next_state              false
% 1.90/1.05  --bmc1_pre_inst_state                   false
% 1.90/1.05  --bmc1_pre_inst_reach_state             false
% 1.90/1.05  --bmc1_out_unsat_core                   false
% 1.90/1.05  --bmc1_aig_witness_out                  false
% 1.90/1.05  --bmc1_verbose                          false
% 1.90/1.05  --bmc1_dump_clauses_tptp                false
% 1.90/1.05  --bmc1_dump_unsat_core_tptp             false
% 1.90/1.05  --bmc1_dump_file                        -
% 1.90/1.05  --bmc1_ucm_expand_uc_limit              128
% 1.90/1.05  --bmc1_ucm_n_expand_iterations          6
% 1.90/1.05  --bmc1_ucm_extend_mode                  1
% 1.90/1.05  --bmc1_ucm_init_mode                    2
% 1.90/1.05  --bmc1_ucm_cone_mode                    none
% 1.90/1.05  --bmc1_ucm_reduced_relation_type        0
% 1.90/1.05  --bmc1_ucm_relax_model                  4
% 1.90/1.05  --bmc1_ucm_full_tr_after_sat            true
% 1.90/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 1.90/1.05  --bmc1_ucm_layered_model                none
% 1.90/1.05  --bmc1_ucm_max_lemma_size               10
% 1.90/1.05  
% 1.90/1.05  ------ AIG Options
% 1.90/1.05  
% 1.90/1.05  --aig_mode                              false
% 1.90/1.05  
% 1.90/1.05  ------ Instantiation Options
% 1.90/1.05  
% 1.90/1.05  --instantiation_flag                    true
% 1.90/1.05  --inst_sos_flag                         false
% 1.90/1.05  --inst_sos_phase                        true
% 1.90/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.90/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.90/1.05  --inst_lit_sel_side                     num_symb
% 1.90/1.05  --inst_solver_per_active                1400
% 1.90/1.05  --inst_solver_calls_frac                1.
% 1.90/1.05  --inst_passive_queue_type               priority_queues
% 1.90/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.90/1.05  --inst_passive_queues_freq              [25;2]
% 1.90/1.05  --inst_dismatching                      true
% 1.90/1.05  --inst_eager_unprocessed_to_passive     true
% 1.90/1.05  --inst_prop_sim_given                   true
% 1.90/1.05  --inst_prop_sim_new                     false
% 1.90/1.05  --inst_subs_new                         false
% 1.90/1.05  --inst_eq_res_simp                      false
% 1.90/1.05  --inst_subs_given                       false
% 1.90/1.05  --inst_orphan_elimination               true
% 1.90/1.05  --inst_learning_loop_flag               true
% 1.90/1.05  --inst_learning_start                   3000
% 1.90/1.05  --inst_learning_factor                  2
% 1.90/1.05  --inst_start_prop_sim_after_learn       3
% 1.90/1.05  --inst_sel_renew                        solver
% 1.90/1.05  --inst_lit_activity_flag                true
% 1.90/1.05  --inst_restr_to_given                   false
% 1.90/1.05  --inst_activity_threshold               500
% 1.90/1.05  --inst_out_proof                        true
% 1.90/1.05  
% 1.90/1.05  ------ Resolution Options
% 1.90/1.05  
% 1.90/1.05  --resolution_flag                       true
% 1.90/1.05  --res_lit_sel                           adaptive
% 1.90/1.05  --res_lit_sel_side                      none
% 1.90/1.05  --res_ordering                          kbo
% 1.90/1.05  --res_to_prop_solver                    active
% 1.90/1.05  --res_prop_simpl_new                    false
% 1.90/1.05  --res_prop_simpl_given                  true
% 1.90/1.05  --res_passive_queue_type                priority_queues
% 1.90/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.90/1.05  --res_passive_queues_freq               [15;5]
% 1.90/1.05  --res_forward_subs                      full
% 1.90/1.05  --res_backward_subs                     full
% 1.90/1.05  --res_forward_subs_resolution           true
% 1.90/1.05  --res_backward_subs_resolution          true
% 1.90/1.05  --res_orphan_elimination                true
% 1.90/1.05  --res_time_limit                        2.
% 1.90/1.05  --res_out_proof                         true
% 1.90/1.05  
% 1.90/1.05  ------ Superposition Options
% 1.90/1.05  
% 1.90/1.05  --superposition_flag                    true
% 1.90/1.05  --sup_passive_queue_type                priority_queues
% 1.90/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.90/1.05  --sup_passive_queues_freq               [8;1;4]
% 1.90/1.05  --demod_completeness_check              fast
% 1.90/1.05  --demod_use_ground                      true
% 1.90/1.05  --sup_to_prop_solver                    passive
% 1.90/1.05  --sup_prop_simpl_new                    true
% 1.90/1.05  --sup_prop_simpl_given                  true
% 1.90/1.05  --sup_fun_splitting                     false
% 1.90/1.05  --sup_smt_interval                      50000
% 1.90/1.05  
% 1.90/1.05  ------ Superposition Simplification Setup
% 1.90/1.05  
% 1.90/1.05  --sup_indices_passive                   []
% 1.90/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.90/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.90/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.90/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 1.90/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.90/1.05  --sup_full_bw                           [BwDemod]
% 1.90/1.05  --sup_immed_triv                        [TrivRules]
% 1.90/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.90/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.90/1.05  --sup_immed_bw_main                     []
% 1.90/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.90/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 1.90/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.90/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.90/1.05  
% 1.90/1.05  ------ Combination Options
% 1.90/1.05  
% 1.90/1.05  --comb_res_mult                         3
% 1.90/1.05  --comb_sup_mult                         2
% 1.90/1.05  --comb_inst_mult                        10
% 1.90/1.05  
% 1.90/1.05  ------ Debug Options
% 1.90/1.05  
% 1.90/1.05  --dbg_backtrace                         false
% 1.90/1.05  --dbg_dump_prop_clauses                 false
% 1.90/1.05  --dbg_dump_prop_clauses_file            -
% 1.90/1.05  --dbg_out_stat                          false
% 1.90/1.05  ------ Parsing...
% 1.90/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.90/1.05  
% 1.90/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.90/1.05  
% 1.90/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.90/1.05  
% 1.90/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.90/1.05  ------ Proving...
% 1.90/1.05  ------ Problem Properties 
% 1.90/1.05  
% 1.90/1.05  
% 1.90/1.05  clauses                                 17
% 1.90/1.05  conjectures                             1
% 1.90/1.05  EPR                                     2
% 1.90/1.05  Horn                                    15
% 1.90/1.05  unary                                   13
% 1.90/1.05  binary                                  1
% 1.90/1.05  lits                                    30
% 1.90/1.05  lits eq                                 14
% 1.90/1.05  fd_pure                                 0
% 1.90/1.05  fd_pseudo                               0
% 1.90/1.05  fd_cond                                 0
% 1.90/1.05  fd_pseudo_cond                          2
% 1.90/1.05  AC symbols                              0
% 1.90/1.05  
% 1.90/1.05  ------ Schedule dynamic 5 is on 
% 1.90/1.05  
% 1.90/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.90/1.05  
% 1.90/1.05  
% 1.90/1.05  ------ 
% 1.90/1.05  Current options:
% 1.90/1.05  ------ 
% 1.90/1.05  
% 1.90/1.05  ------ Input Options
% 1.90/1.05  
% 1.90/1.05  --out_options                           all
% 1.90/1.05  --tptp_safe_out                         true
% 1.90/1.05  --problem_path                          ""
% 1.90/1.05  --include_path                          ""
% 1.90/1.05  --clausifier                            res/vclausify_rel
% 1.90/1.05  --clausifier_options                    --mode clausify
% 1.90/1.05  --stdin                                 false
% 1.90/1.05  --stats_out                             all
% 1.90/1.05  
% 1.90/1.05  ------ General Options
% 1.90/1.05  
% 1.90/1.05  --fof                                   false
% 1.90/1.05  --time_out_real                         305.
% 1.90/1.05  --time_out_virtual                      -1.
% 1.90/1.05  --symbol_type_check                     false
% 1.90/1.05  --clausify_out                          false
% 1.90/1.05  --sig_cnt_out                           false
% 1.90/1.05  --trig_cnt_out                          false
% 1.90/1.05  --trig_cnt_out_tolerance                1.
% 1.90/1.05  --trig_cnt_out_sk_spl                   false
% 1.90/1.05  --abstr_cl_out                          false
% 1.90/1.05  
% 1.90/1.05  ------ Global Options
% 1.90/1.05  
% 1.90/1.05  --schedule                              default
% 1.90/1.05  --add_important_lit                     false
% 1.90/1.05  --prop_solver_per_cl                    1000
% 1.90/1.05  --min_unsat_core                        false
% 1.90/1.05  --soft_assumptions                      false
% 1.90/1.05  --soft_lemma_size                       3
% 1.90/1.05  --prop_impl_unit_size                   0
% 1.90/1.05  --prop_impl_unit                        []
% 1.90/1.05  --share_sel_clauses                     true
% 1.90/1.05  --reset_solvers                         false
% 1.90/1.05  --bc_imp_inh                            [conj_cone]
% 1.90/1.05  --conj_cone_tolerance                   3.
% 1.90/1.05  --extra_neg_conj                        none
% 1.90/1.05  --large_theory_mode                     true
% 1.90/1.05  --prolific_symb_bound                   200
% 1.90/1.05  --lt_threshold                          2000
% 1.90/1.05  --clause_weak_htbl                      true
% 1.90/1.05  --gc_record_bc_elim                     false
% 1.90/1.05  
% 1.90/1.05  ------ Preprocessing Options
% 1.90/1.05  
% 1.90/1.05  --preprocessing_flag                    true
% 1.90/1.05  --time_out_prep_mult                    0.1
% 1.90/1.05  --splitting_mode                        input
% 1.90/1.05  --splitting_grd                         true
% 1.90/1.05  --splitting_cvd                         false
% 1.90/1.05  --splitting_cvd_svl                     false
% 1.90/1.05  --splitting_nvd                         32
% 1.90/1.05  --sub_typing                            true
% 1.90/1.05  --prep_gs_sim                           true
% 1.90/1.05  --prep_unflatten                        true
% 1.90/1.05  --prep_res_sim                          true
% 1.90/1.05  --prep_upred                            true
% 1.90/1.05  --prep_sem_filter                       exhaustive
% 1.90/1.05  --prep_sem_filter_out                   false
% 1.90/1.05  --pred_elim                             true
% 1.90/1.05  --res_sim_input                         true
% 1.90/1.05  --eq_ax_congr_red                       true
% 1.90/1.05  --pure_diseq_elim                       true
% 1.90/1.05  --brand_transform                       false
% 1.90/1.05  --non_eq_to_eq                          false
% 1.90/1.05  --prep_def_merge                        true
% 1.90/1.05  --prep_def_merge_prop_impl              false
% 1.90/1.05  --prep_def_merge_mbd                    true
% 1.90/1.05  --prep_def_merge_tr_red                 false
% 1.90/1.05  --prep_def_merge_tr_cl                  false
% 1.90/1.05  --smt_preprocessing                     true
% 1.90/1.05  --smt_ac_axioms                         fast
% 1.90/1.05  --preprocessed_out                      false
% 1.90/1.05  --preprocessed_stats                    false
% 1.90/1.05  
% 1.90/1.05  ------ Abstraction refinement Options
% 1.90/1.05  
% 1.90/1.05  --abstr_ref                             []
% 1.90/1.05  --abstr_ref_prep                        false
% 1.90/1.05  --abstr_ref_until_sat                   false
% 1.90/1.05  --abstr_ref_sig_restrict                funpre
% 1.90/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 1.90/1.05  --abstr_ref_under                       []
% 1.90/1.05  
% 1.90/1.05  ------ SAT Options
% 1.90/1.05  
% 1.90/1.05  --sat_mode                              false
% 1.90/1.05  --sat_fm_restart_options                ""
% 1.90/1.05  --sat_gr_def                            false
% 1.90/1.05  --sat_epr_types                         true
% 1.90/1.05  --sat_non_cyclic_types                  false
% 1.90/1.05  --sat_finite_models                     false
% 1.90/1.05  --sat_fm_lemmas                         false
% 1.90/1.05  --sat_fm_prep                           false
% 1.90/1.05  --sat_fm_uc_incr                        true
% 1.90/1.05  --sat_out_model                         small
% 1.90/1.05  --sat_out_clauses                       false
% 1.90/1.05  
% 1.90/1.05  ------ QBF Options
% 1.90/1.05  
% 1.90/1.05  --qbf_mode                              false
% 1.90/1.05  --qbf_elim_univ                         false
% 1.90/1.05  --qbf_dom_inst                          none
% 1.90/1.05  --qbf_dom_pre_inst                      false
% 1.90/1.05  --qbf_sk_in                             false
% 1.90/1.05  --qbf_pred_elim                         true
% 1.90/1.05  --qbf_split                             512
% 1.90/1.05  
% 1.90/1.05  ------ BMC1 Options
% 1.90/1.05  
% 1.90/1.05  --bmc1_incremental                      false
% 1.90/1.05  --bmc1_axioms                           reachable_all
% 1.90/1.05  --bmc1_min_bound                        0
% 1.90/1.05  --bmc1_max_bound                        -1
% 1.90/1.05  --bmc1_max_bound_default                -1
% 1.90/1.05  --bmc1_symbol_reachability              true
% 1.90/1.05  --bmc1_property_lemmas                  false
% 1.90/1.05  --bmc1_k_induction                      false
% 1.90/1.05  --bmc1_non_equiv_states                 false
% 1.90/1.05  --bmc1_deadlock                         false
% 1.90/1.05  --bmc1_ucm                              false
% 1.90/1.05  --bmc1_add_unsat_core                   none
% 1.90/1.05  --bmc1_unsat_core_children              false
% 1.90/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 1.90/1.05  --bmc1_out_stat                         full
% 1.90/1.05  --bmc1_ground_init                      false
% 1.90/1.05  --bmc1_pre_inst_next_state              false
% 1.90/1.05  --bmc1_pre_inst_state                   false
% 1.90/1.05  --bmc1_pre_inst_reach_state             false
% 1.90/1.05  --bmc1_out_unsat_core                   false
% 1.90/1.05  --bmc1_aig_witness_out                  false
% 1.90/1.05  --bmc1_verbose                          false
% 1.90/1.05  --bmc1_dump_clauses_tptp                false
% 1.90/1.05  --bmc1_dump_unsat_core_tptp             false
% 1.90/1.05  --bmc1_dump_file                        -
% 1.90/1.05  --bmc1_ucm_expand_uc_limit              128
% 1.90/1.05  --bmc1_ucm_n_expand_iterations          6
% 1.90/1.05  --bmc1_ucm_extend_mode                  1
% 1.90/1.05  --bmc1_ucm_init_mode                    2
% 1.90/1.05  --bmc1_ucm_cone_mode                    none
% 1.90/1.05  --bmc1_ucm_reduced_relation_type        0
% 1.90/1.05  --bmc1_ucm_relax_model                  4
% 1.90/1.05  --bmc1_ucm_full_tr_after_sat            true
% 1.90/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 1.90/1.05  --bmc1_ucm_layered_model                none
% 1.90/1.05  --bmc1_ucm_max_lemma_size               10
% 1.90/1.05  
% 1.90/1.05  ------ AIG Options
% 1.90/1.05  
% 1.90/1.05  --aig_mode                              false
% 1.90/1.05  
% 1.90/1.05  ------ Instantiation Options
% 1.90/1.05  
% 1.90/1.05  --instantiation_flag                    true
% 1.90/1.05  --inst_sos_flag                         false
% 1.90/1.05  --inst_sos_phase                        true
% 1.90/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.90/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.90/1.05  --inst_lit_sel_side                     none
% 1.90/1.05  --inst_solver_per_active                1400
% 1.90/1.05  --inst_solver_calls_frac                1.
% 1.90/1.05  --inst_passive_queue_type               priority_queues
% 1.90/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.90/1.05  --inst_passive_queues_freq              [25;2]
% 1.90/1.05  --inst_dismatching                      true
% 1.90/1.05  --inst_eager_unprocessed_to_passive     true
% 1.90/1.05  --inst_prop_sim_given                   true
% 1.90/1.05  --inst_prop_sim_new                     false
% 1.90/1.05  --inst_subs_new                         false
% 1.90/1.05  --inst_eq_res_simp                      false
% 1.90/1.05  --inst_subs_given                       false
% 1.90/1.05  --inst_orphan_elimination               true
% 1.90/1.05  --inst_learning_loop_flag               true
% 1.90/1.05  --inst_learning_start                   3000
% 1.90/1.05  --inst_learning_factor                  2
% 1.90/1.05  --inst_start_prop_sim_after_learn       3
% 1.90/1.05  --inst_sel_renew                        solver
% 1.90/1.05  --inst_lit_activity_flag                true
% 1.90/1.05  --inst_restr_to_given                   false
% 1.90/1.05  --inst_activity_threshold               500
% 1.90/1.05  --inst_out_proof                        true
% 1.90/1.05  
% 1.90/1.05  ------ Resolution Options
% 1.90/1.05  
% 1.90/1.05  --resolution_flag                       false
% 1.90/1.05  --res_lit_sel                           adaptive
% 1.90/1.05  --res_lit_sel_side                      none
% 1.90/1.05  --res_ordering                          kbo
% 1.90/1.05  --res_to_prop_solver                    active
% 1.90/1.05  --res_prop_simpl_new                    false
% 1.90/1.05  --res_prop_simpl_given                  true
% 1.90/1.05  --res_passive_queue_type                priority_queues
% 1.90/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.90/1.05  --res_passive_queues_freq               [15;5]
% 1.90/1.05  --res_forward_subs                      full
% 1.90/1.05  --res_backward_subs                     full
% 1.90/1.05  --res_forward_subs_resolution           true
% 1.90/1.05  --res_backward_subs_resolution          true
% 1.90/1.05  --res_orphan_elimination                true
% 1.90/1.05  --res_time_limit                        2.
% 1.90/1.05  --res_out_proof                         true
% 1.90/1.05  
% 1.90/1.05  ------ Superposition Options
% 1.90/1.05  
% 1.90/1.05  --superposition_flag                    true
% 1.90/1.05  --sup_passive_queue_type                priority_queues
% 1.90/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.90/1.05  --sup_passive_queues_freq               [8;1;4]
% 1.90/1.05  --demod_completeness_check              fast
% 1.90/1.05  --demod_use_ground                      true
% 1.90/1.05  --sup_to_prop_solver                    passive
% 1.90/1.05  --sup_prop_simpl_new                    true
% 1.90/1.05  --sup_prop_simpl_given                  true
% 1.90/1.05  --sup_fun_splitting                     false
% 1.90/1.05  --sup_smt_interval                      50000
% 1.90/1.05  
% 1.90/1.05  ------ Superposition Simplification Setup
% 1.90/1.05  
% 1.90/1.05  --sup_indices_passive                   []
% 1.90/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.90/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.90/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.90/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 1.90/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.90/1.05  --sup_full_bw                           [BwDemod]
% 1.90/1.05  --sup_immed_triv                        [TrivRules]
% 1.90/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.90/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.90/1.05  --sup_immed_bw_main                     []
% 1.90/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.90/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 1.90/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.90/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.90/1.05  
% 1.90/1.05  ------ Combination Options
% 1.90/1.05  
% 1.90/1.05  --comb_res_mult                         3
% 1.90/1.05  --comb_sup_mult                         2
% 1.90/1.05  --comb_inst_mult                        10
% 1.90/1.05  
% 1.90/1.05  ------ Debug Options
% 1.90/1.05  
% 1.90/1.05  --dbg_backtrace                         false
% 1.90/1.05  --dbg_dump_prop_clauses                 false
% 1.90/1.05  --dbg_dump_prop_clauses_file            -
% 1.90/1.05  --dbg_out_stat                          false
% 1.90/1.05  
% 1.90/1.05  
% 1.90/1.05  
% 1.90/1.05  
% 1.90/1.05  ------ Proving...
% 1.90/1.05  
% 1.90/1.05  
% 1.90/1.05  % SZS status Theorem for theBenchmark.p
% 1.90/1.05  
% 1.90/1.05   Resolution empty clause
% 1.90/1.05  
% 1.90/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 1.90/1.05  
% 1.90/1.05  fof(f5,axiom,(
% 1.90/1.05    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.90/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/1.05  
% 1.90/1.05  fof(f13,plain,(
% 1.90/1.05    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.90/1.05    inference(ennf_transformation,[],[f5])).
% 1.90/1.05  
% 1.90/1.05  fof(f33,plain,(
% 1.90/1.05    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.90/1.05    inference(cnf_transformation,[],[f13])).
% 1.90/1.05  
% 1.90/1.05  fof(f2,axiom,(
% 1.90/1.05    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.90/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/1.05  
% 1.90/1.05  fof(f30,plain,(
% 1.90/1.05    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.90/1.05    inference(cnf_transformation,[],[f2])).
% 1.90/1.05  
% 1.90/1.05  fof(f3,axiom,(
% 1.90/1.05    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.90/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/1.05  
% 1.90/1.05  fof(f31,plain,(
% 1.90/1.05    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.90/1.05    inference(cnf_transformation,[],[f3])).
% 1.90/1.05  
% 1.90/1.05  fof(f4,axiom,(
% 1.90/1.05    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.90/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/1.05  
% 1.90/1.05  fof(f32,plain,(
% 1.90/1.05    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.90/1.05    inference(cnf_transformation,[],[f4])).
% 1.90/1.05  
% 1.90/1.05  fof(f51,plain,(
% 1.90/1.05    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.90/1.05    inference(definition_unfolding,[],[f31,f32])).
% 1.90/1.05  
% 1.90/1.05  fof(f52,plain,(
% 1.90/1.05    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.90/1.05    inference(definition_unfolding,[],[f30,f51])).
% 1.90/1.05  
% 1.90/1.05  fof(f53,plain,(
% 1.90/1.05    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.90/1.05    inference(definition_unfolding,[],[f33,f52])).
% 1.90/1.05  
% 1.90/1.05  fof(f8,axiom,(
% 1.90/1.05    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 1.90/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/1.05  
% 1.90/1.05  fof(f16,plain,(
% 1.90/1.05    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.90/1.05    inference(ennf_transformation,[],[f8])).
% 1.90/1.05  
% 1.90/1.05  fof(f44,plain,(
% 1.90/1.05    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.90/1.05    inference(cnf_transformation,[],[f16])).
% 1.90/1.05  
% 1.90/1.05  fof(f11,conjecture,(
% 1.90/1.05    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 1.90/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/1.05  
% 1.90/1.05  fof(f12,negated_conjecture,(
% 1.90/1.05    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 1.90/1.05    inference(negated_conjecture,[],[f11])).
% 1.90/1.05  
% 1.90/1.05  fof(f19,plain,(
% 1.90/1.05    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.90/1.05    inference(ennf_transformation,[],[f12])).
% 1.90/1.05  
% 1.90/1.05  fof(f20,plain,(
% 1.90/1.05    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.90/1.05    inference(flattening,[],[f19])).
% 1.90/1.05  
% 1.90/1.05  fof(f25,plain,(
% 1.90/1.05    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.90/1.05    introduced(choice_axiom,[])).
% 1.90/1.05  
% 1.90/1.05  fof(f26,plain,(
% 1.90/1.05    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.90/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f25])).
% 1.90/1.05  
% 1.90/1.05  fof(f48,plain,(
% 1.90/1.05    v1_relat_1(sK1)),
% 1.90/1.05    inference(cnf_transformation,[],[f26])).
% 1.90/1.05  
% 1.90/1.05  fof(f10,axiom,(
% 1.90/1.05    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X1,k1_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) => k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))))),
% 1.90/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/1.05  
% 1.90/1.05  fof(f17,plain,(
% 1.90/1.05    ! [X0,X1,X2] : ((k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | (~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.90/1.05    inference(ennf_transformation,[],[f10])).
% 1.90/1.05  
% 1.90/1.05  fof(f18,plain,(
% 1.90/1.05    ! [X0,X1,X2] : (k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.90/1.05    inference(flattening,[],[f17])).
% 1.90/1.05  
% 1.90/1.05  fof(f47,plain,(
% 1.90/1.05    ( ! [X2,X0,X1] : (k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.90/1.05    inference(cnf_transformation,[],[f18])).
% 1.90/1.05  
% 1.90/1.05  fof(f63,plain,(
% 1.90/1.05    ( ! [X2,X0,X1] : (k2_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_enumset1(X0,X0,X0,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.90/1.05    inference(definition_unfolding,[],[f47,f51,f51])).
% 1.90/1.05  
% 1.90/1.05  fof(f49,plain,(
% 1.90/1.05    v1_funct_1(sK1)),
% 1.90/1.05    inference(cnf_transformation,[],[f26])).
% 1.90/1.05  
% 1.90/1.05  fof(f50,plain,(
% 1.90/1.05    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))),
% 1.90/1.05    inference(cnf_transformation,[],[f26])).
% 1.90/1.05  
% 1.90/1.05  fof(f64,plain,(
% 1.90/1.05    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))),
% 1.90/1.05    inference(definition_unfolding,[],[f50,f52,f52])).
% 1.90/1.05  
% 1.90/1.05  fof(f7,axiom,(
% 1.90/1.05    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.90/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/1.05  
% 1.90/1.05  fof(f15,plain,(
% 1.90/1.05    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.90/1.05    inference(ennf_transformation,[],[f7])).
% 1.90/1.05  
% 1.90/1.05  fof(f43,plain,(
% 1.90/1.05    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.90/1.05    inference(cnf_transformation,[],[f15])).
% 1.90/1.05  
% 1.90/1.05  fof(f1,axiom,(
% 1.90/1.05    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.90/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/1.05  
% 1.90/1.05  fof(f21,plain,(
% 1.90/1.05    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.90/1.05    inference(nnf_transformation,[],[f1])).
% 1.90/1.05  
% 1.90/1.05  fof(f22,plain,(
% 1.90/1.05    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.90/1.05    inference(flattening,[],[f21])).
% 1.90/1.05  
% 1.90/1.05  fof(f28,plain,(
% 1.90/1.05    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.90/1.05    inference(cnf_transformation,[],[f22])).
% 1.90/1.05  
% 1.90/1.05  fof(f65,plain,(
% 1.90/1.05    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.90/1.05    inference(equality_resolution,[],[f28])).
% 1.90/1.05  
% 1.90/1.05  fof(f9,axiom,(
% 1.90/1.05    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.90/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/1.05  
% 1.90/1.05  fof(f46,plain,(
% 1.90/1.05    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.90/1.05    inference(cnf_transformation,[],[f9])).
% 1.90/1.05  
% 1.90/1.05  fof(f6,axiom,(
% 1.90/1.05    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 1.90/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/1.05  
% 1.90/1.05  fof(f14,plain,(
% 1.90/1.05    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 1.90/1.05    inference(ennf_transformation,[],[f6])).
% 1.90/1.05  
% 1.90/1.05  fof(f23,plain,(
% 1.90/1.05    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & ((k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3) | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 1.90/1.05    inference(nnf_transformation,[],[f14])).
% 1.90/1.05  
% 1.90/1.05  fof(f24,plain,(
% 1.90/1.05    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 1.90/1.05    inference(flattening,[],[f23])).
% 1.90/1.05  
% 1.90/1.05  fof(f35,plain,(
% 1.90/1.05    ( ! [X2,X0,X3,X1] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) | k1_xboole_0 != X3) )),
% 1.90/1.05    inference(cnf_transformation,[],[f24])).
% 1.90/1.05  
% 1.90/1.05  fof(f61,plain,(
% 1.90/1.05    ( ! [X2,X0,X3,X1] : (r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) | k1_xboole_0 != X3) )),
% 1.90/1.05    inference(definition_unfolding,[],[f35,f32])).
% 1.90/1.05  
% 1.90/1.05  fof(f74,plain,(
% 1.90/1.05    ( ! [X2,X0,X1] : (r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X1,X2))) )),
% 1.90/1.05    inference(equality_resolution,[],[f61])).
% 1.90/1.05  
% 1.90/1.05  cnf(c_3,plain,
% 1.90/1.05      ( r2_hidden(X0,X1) | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
% 1.90/1.05      inference(cnf_transformation,[],[f53]) ).
% 1.90/1.05  
% 1.90/1.05  cnf(c_14,plain,
% 1.90/1.05      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 1.90/1.05      | ~ v1_relat_1(X1)
% 1.90/1.05      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 1.90/1.05      inference(cnf_transformation,[],[f44]) ).
% 1.90/1.05  
% 1.90/1.05  cnf(c_203,plain,
% 1.90/1.05      ( r2_hidden(X0,X1)
% 1.90/1.05      | ~ v1_relat_1(X2)
% 1.90/1.05      | k2_enumset1(X0,X0,X0,X0) != X3
% 1.90/1.05      | k7_relat_1(X2,X3) = k1_xboole_0
% 1.90/1.05      | k1_relat_1(X2) != X1 ),
% 1.90/1.05      inference(resolution_lifted,[status(thm)],[c_3,c_14]) ).
% 1.90/1.05  
% 1.90/1.05  cnf(c_204,plain,
% 1.90/1.05      ( r2_hidden(X0,k1_relat_1(X1))
% 1.90/1.05      | ~ v1_relat_1(X1)
% 1.90/1.05      | k7_relat_1(X1,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0 ),
% 1.90/1.05      inference(unflattening,[status(thm)],[c_203]) ).
% 1.90/1.05  
% 1.90/1.05  cnf(c_20,negated_conjecture,
% 1.90/1.05      ( v1_relat_1(sK1) ),
% 1.90/1.05      inference(cnf_transformation,[],[f48]) ).
% 1.90/1.05  
% 1.90/1.05  cnf(c_247,plain,
% 1.90/1.05      ( r2_hidden(X0,k1_relat_1(X1))
% 1.90/1.05      | k7_relat_1(X1,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0
% 1.90/1.05      | sK1 != X1 ),
% 1.90/1.05      inference(resolution_lifted,[status(thm)],[c_204,c_20]) ).
% 1.90/1.05  
% 1.90/1.05  cnf(c_248,plain,
% 1.90/1.05      ( r2_hidden(X0,k1_relat_1(sK1))
% 1.90/1.05      | k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0 ),
% 1.90/1.05      inference(unflattening,[status(thm)],[c_247]) ).
% 1.90/1.05  
% 1.90/1.05  cnf(c_610,plain,
% 1.90/1.05      ( k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0
% 1.90/1.05      | r2_hidden(X0,k1_relat_1(sK1)) = iProver_top ),
% 1.90/1.05      inference(predicate_to_equality,[status(thm)],[c_248]) ).
% 1.90/1.05  
% 1.90/1.05  cnf(c_17,plain,
% 1.90/1.05      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 1.90/1.05      | ~ r2_hidden(X2,k1_relat_1(X1))
% 1.90/1.05      | ~ v1_funct_1(X1)
% 1.90/1.05      | ~ v1_relat_1(X1)
% 1.90/1.05      | k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X0)) = k9_relat_1(X1,k2_enumset1(X2,X2,X2,X0)) ),
% 1.90/1.05      inference(cnf_transformation,[],[f63]) ).
% 1.90/1.05  
% 1.90/1.05  cnf(c_19,negated_conjecture,
% 1.90/1.05      ( v1_funct_1(sK1) ),
% 1.90/1.05      inference(cnf_transformation,[],[f49]) ).
% 1.90/1.05  
% 1.90/1.05  cnf(c_222,plain,
% 1.90/1.05      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 1.90/1.05      | ~ r2_hidden(X2,k1_relat_1(X1))
% 1.90/1.05      | ~ v1_relat_1(X1)
% 1.90/1.05      | k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X0)) = k9_relat_1(X1,k2_enumset1(X2,X2,X2,X0))
% 1.90/1.05      | sK1 != X1 ),
% 1.90/1.05      inference(resolution_lifted,[status(thm)],[c_17,c_19]) ).
% 1.90/1.05  
% 1.90/1.05  cnf(c_223,plain,
% 1.90/1.05      ( ~ r2_hidden(X0,k1_relat_1(sK1))
% 1.90/1.05      | ~ r2_hidden(X1,k1_relat_1(sK1))
% 1.90/1.05      | ~ v1_relat_1(sK1)
% 1.90/1.05      | k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)) ),
% 1.90/1.05      inference(unflattening,[status(thm)],[c_222]) ).
% 1.90/1.05  
% 1.90/1.05  cnf(c_227,plain,
% 1.90/1.05      ( ~ r2_hidden(X1,k1_relat_1(sK1))
% 1.90/1.05      | ~ r2_hidden(X0,k1_relat_1(sK1))
% 1.90/1.05      | k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)) ),
% 1.90/1.05      inference(global_propositional_subsumption,[status(thm)],[c_223,c_20]) ).
% 1.90/1.05  
% 1.90/1.05  cnf(c_228,plain,
% 1.90/1.05      ( ~ r2_hidden(X0,k1_relat_1(sK1))
% 1.90/1.05      | ~ r2_hidden(X1,k1_relat_1(sK1))
% 1.90/1.05      | k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)) ),
% 1.90/1.05      inference(renaming,[status(thm)],[c_227]) ).
% 1.90/1.05  
% 1.90/1.05  cnf(c_611,plain,
% 1.90/1.05      ( k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1))
% 1.90/1.05      | r2_hidden(X0,k1_relat_1(sK1)) != iProver_top
% 1.90/1.05      | r2_hidden(X1,k1_relat_1(sK1)) != iProver_top ),
% 1.90/1.05      inference(predicate_to_equality,[status(thm)],[c_228]) ).
% 1.90/1.05  
% 1.90/1.05  cnf(c_727,plain,
% 1.90/1.05      ( k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1))
% 1.90/1.05      | k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0
% 1.90/1.05      | r2_hidden(X1,k1_relat_1(sK1)) != iProver_top ),
% 1.90/1.05      inference(superposition,[status(thm)],[c_610,c_611]) ).
% 1.90/1.05  
% 1.90/1.05  cnf(c_812,plain,
% 1.90/1.05      ( k2_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1))
% 1.90/1.05      | k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X1)) = k1_xboole_0
% 1.90/1.05      | k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0 ),
% 1.90/1.05      inference(superposition,[status(thm)],[c_610,c_727]) ).
% 1.90/1.05  
% 1.90/1.05  cnf(c_18,negated_conjecture,
% 1.90/1.05      ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
% 1.90/1.05      inference(cnf_transformation,[],[f64]) ).
% 1.90/1.05  
% 1.90/1.05  cnf(c_612,plain,
% 1.90/1.05      ( r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) != iProver_top ),
% 1.90/1.05      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.90/1.05  
% 1.90/1.05  cnf(c_13,plain,
% 1.90/1.05      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 1.90/1.05      inference(cnf_transformation,[],[f43]) ).
% 1.90/1.05  
% 1.90/1.05  cnf(c_259,plain,
% 1.90/1.05      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) | sK1 != X0 ),
% 1.90/1.05      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 1.90/1.05  
% 1.90/1.05  cnf(c_260,plain,
% 1.90/1.05      ( k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
% 1.90/1.05      inference(unflattening,[status(thm)],[c_259]) ).
% 1.90/1.05  
% 1.90/1.05  cnf(c_656,plain,
% 1.90/1.05      ( r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) != iProver_top ),
% 1.90/1.05      inference(demodulation,[status(thm)],[c_612,c_260]) ).
% 1.90/1.05  
% 1.90/1.05  cnf(c_823,plain,
% 1.90/1.05      ( k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0
% 1.90/1.05      | r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != iProver_top ),
% 1.90/1.05      inference(superposition,[status(thm)],[c_812,c_656]) ).
% 1.90/1.05  
% 1.90/1.05  cnf(c_865,plain,
% 1.90/1.05      ( ~ r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
% 1.90/1.05      | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
% 1.90/1.05      inference(predicate_to_equality_rev,[status(thm)],[c_823]) ).
% 1.90/1.05  
% 1.90/1.05  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f65]) ).
% 1.90/1.05  
% 1.90/1.05  cnf(c_1154,plain,
% 1.90/1.05      ( r1_tarski(k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1)),k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X1))) ),
% 1.90/1.05      inference(instantiation,[status(thm)],[c_1]) ).
% 1.90/1.05  
% 1.90/1.05  cnf(c_1160,plain,
% 1.90/1.05      ( r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
% 1.90/1.05      inference(instantiation,[status(thm)],[c_1154]) ).
% 1.90/1.05  
% 1.90/1.05  cnf(c_1605,plain,
% 1.90/1.05      ( k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
% 1.90/1.05      inference(global_propositional_subsumption,
% 1.90/1.05                [status(thm)],
% 1.90/1.05                [c_823,c_865,c_1160]) ).
% 1.90/1.05  
% 1.90/1.05  cnf(c_1608,plain,
% 1.90/1.05      ( k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k2_relat_1(k1_xboole_0) ),
% 1.90/1.05      inference(superposition,[status(thm)],[c_1605,c_260]) ).
% 1.90/1.05  
% 1.90/1.05  cnf(c_15,plain,
% 1.90/1.05      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 1.90/1.05      inference(cnf_transformation,[],[f46]) ).
% 1.90/1.05  
% 1.90/1.05  cnf(c_1609,plain,
% 1.90/1.05      ( k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
% 1.90/1.05      inference(light_normalisation,[status(thm)],[c_1608,c_15]) ).
% 1.90/1.05  
% 1.90/1.05  cnf(c_1611,plain,
% 1.90/1.05      ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) != iProver_top ),
% 1.90/1.05      inference(demodulation,[status(thm)],[c_1609,c_656]) ).
% 1.90/1.05  
% 1.90/1.05  cnf(c_11,plain,
% 1.90/1.05      ( r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X1,X2)) ),
% 1.90/1.05      inference(cnf_transformation,[],[f74]) ).
% 1.90/1.05  
% 1.90/1.05  cnf(c_614,plain,
% 1.90/1.05      ( r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
% 1.90/1.05      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.90/1.05  
% 1.90/1.05  cnf(c_1683,plain,
% 1.90/1.05      ( $false ),
% 1.90/1.05      inference(forward_subsumption_resolution,[status(thm)],[c_1611,c_614]) ).
% 1.90/1.05  
% 1.90/1.05  
% 1.90/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 1.90/1.05  
% 1.90/1.05  ------                               Statistics
% 1.90/1.05  
% 1.90/1.05  ------ General
% 1.90/1.05  
% 1.90/1.05  abstr_ref_over_cycles:                  0
% 1.90/1.05  abstr_ref_under_cycles:                 0
% 1.90/1.05  gc_basic_clause_elim:                   0
% 1.90/1.05  forced_gc_time:                         0
% 1.90/1.05  parsing_time:                           0.013
% 1.90/1.05  unif_index_cands_time:                  0.
% 1.90/1.05  unif_index_add_time:                    0.
% 1.90/1.05  orderings_time:                         0.
% 1.90/1.05  out_proof_time:                         0.011
% 1.90/1.05  total_time:                             0.145
% 1.90/1.05  num_of_symbols:                         45
% 1.90/1.05  num_of_terms:                           1798
% 1.90/1.05  
% 1.90/1.05  ------ Preprocessing
% 1.90/1.05  
% 1.90/1.05  num_of_splits:                          0
% 1.90/1.05  num_of_split_atoms:                     0
% 1.90/1.05  num_of_reused_defs:                     0
% 1.90/1.05  num_eq_ax_congr_red:                    4
% 1.90/1.05  num_of_sem_filtered_clauses:            1
% 1.90/1.05  num_of_subtypes:                        0
% 1.90/1.05  monotx_restored_types:                  0
% 1.90/1.05  sat_num_of_epr_types:                   0
% 1.90/1.05  sat_num_of_non_cyclic_types:            0
% 1.90/1.05  sat_guarded_non_collapsed_types:        0
% 1.90/1.05  num_pure_diseq_elim:                    0
% 1.90/1.05  simp_replaced_by:                       0
% 1.90/1.05  res_preprocessed:                       92
% 1.90/1.05  prep_upred:                             0
% 1.90/1.05  prep_unflattend:                        5
% 1.90/1.05  smt_new_axioms:                         0
% 1.90/1.05  pred_elim_cands:                        2
% 1.90/1.05  pred_elim:                              3
% 1.90/1.05  pred_elim_cl:                           3
% 1.90/1.05  pred_elim_cycles:                       5
% 1.90/1.05  merged_defs:                            0
% 1.90/1.05  merged_defs_ncl:                        0
% 1.90/1.05  bin_hyper_res:                          0
% 1.90/1.05  prep_cycles:                            4
% 1.90/1.05  pred_elim_time:                         0.003
% 1.90/1.05  splitting_time:                         0.
% 1.90/1.05  sem_filter_time:                        0.
% 1.90/1.05  monotx_time:                            0.001
% 1.90/1.05  subtype_inf_time:                       0.
% 1.90/1.05  
% 1.90/1.05  ------ Problem properties
% 1.90/1.05  
% 1.90/1.05  clauses:                                17
% 1.90/1.05  conjectures:                            1
% 1.90/1.05  epr:                                    2
% 1.90/1.05  horn:                                   15
% 1.90/1.05  ground:                                 3
% 1.90/1.05  unary:                                  13
% 1.90/1.05  binary:                                 1
% 1.90/1.05  lits:                                   30
% 1.90/1.05  lits_eq:                                14
% 1.90/1.05  fd_pure:                                0
% 1.90/1.05  fd_pseudo:                              0
% 1.90/1.05  fd_cond:                                0
% 1.90/1.05  fd_pseudo_cond:                         2
% 1.90/1.05  ac_symbols:                             0
% 1.90/1.05  
% 1.90/1.05  ------ Propositional Solver
% 1.90/1.05  
% 1.90/1.05  prop_solver_calls:                      26
% 1.90/1.05  prop_fast_solver_calls:                 426
% 1.90/1.05  smt_solver_calls:                       0
% 1.90/1.05  smt_fast_solver_calls:                  0
% 1.90/1.05  prop_num_of_clauses:                    478
% 1.90/1.05  prop_preprocess_simplified:             2793
% 1.90/1.05  prop_fo_subsumed:                       2
% 1.90/1.05  prop_solver_time:                       0.
% 1.90/1.05  smt_solver_time:                        0.
% 1.90/1.05  smt_fast_solver_time:                   0.
% 1.90/1.05  prop_fast_solver_time:                  0.
% 1.90/1.05  prop_unsat_core_time:                   0.
% 1.90/1.05  
% 1.90/1.05  ------ QBF
% 1.90/1.05  
% 1.90/1.05  qbf_q_res:                              0
% 1.90/1.05  qbf_num_tautologies:                    0
% 1.90/1.05  qbf_prep_cycles:                        0
% 1.90/1.05  
% 1.90/1.05  ------ BMC1
% 1.90/1.05  
% 1.90/1.05  bmc1_current_bound:                     -1
% 1.90/1.05  bmc1_last_solved_bound:                 -1
% 1.90/1.05  bmc1_unsat_core_size:                   -1
% 1.90/1.05  bmc1_unsat_core_parents_size:           -1
% 1.90/1.05  bmc1_merge_next_fun:                    0
% 1.90/1.05  bmc1_unsat_core_clauses_time:           0.
% 1.90/1.05  
% 1.90/1.05  ------ Instantiation
% 1.90/1.05  
% 1.90/1.05  inst_num_of_clauses:                    153
% 1.90/1.05  inst_num_in_passive:                    40
% 1.90/1.05  inst_num_in_active:                     82
% 1.90/1.05  inst_num_in_unprocessed:                31
% 1.90/1.05  inst_num_of_loops:                      90
% 1.90/1.05  inst_num_of_learning_restarts:          0
% 1.90/1.05  inst_num_moves_active_passive:          5
% 1.90/1.05  inst_lit_activity:                      0
% 1.90/1.05  inst_lit_activity_moves:                0
% 1.90/1.05  inst_num_tautologies:                   0
% 1.90/1.05  inst_num_prop_implied:                  0
% 1.90/1.05  inst_num_existing_simplified:           0
% 1.90/1.05  inst_num_eq_res_simplified:             0
% 1.90/1.06  inst_num_child_elim:                    0
% 1.90/1.06  inst_num_of_dismatching_blockings:      44
% 1.90/1.06  inst_num_of_non_proper_insts:           142
% 1.90/1.06  inst_num_of_duplicates:                 0
% 1.90/1.06  inst_inst_num_from_inst_to_res:         0
% 1.90/1.06  inst_dismatching_checking_time:         0.
% 1.90/1.06  
% 1.90/1.06  ------ Resolution
% 1.90/1.06  
% 1.90/1.06  res_num_of_clauses:                     0
% 1.90/1.06  res_num_in_passive:                     0
% 1.90/1.06  res_num_in_active:                      0
% 1.90/1.06  res_num_of_loops:                       96
% 1.90/1.06  res_forward_subset_subsumed:            22
% 1.90/1.06  res_backward_subset_subsumed:           0
% 1.90/1.06  res_forward_subsumed:                   0
% 1.90/1.06  res_backward_subsumed:                  0
% 1.90/1.06  res_forward_subsumption_resolution:     0
% 1.90/1.06  res_backward_subsumption_resolution:    0
% 1.90/1.06  res_clause_to_clause_subsumption:       265
% 1.90/1.06  res_orphan_elimination:                 0
% 1.90/1.06  res_tautology_del:                      4
% 1.90/1.06  res_num_eq_res_simplified:              0
% 1.90/1.06  res_num_sel_changes:                    0
% 1.90/1.06  res_moves_from_active_to_pass:          0
% 1.90/1.06  
% 1.90/1.06  ------ Superposition
% 1.90/1.06  
% 1.90/1.06  sup_time_total:                         0.
% 1.90/1.06  sup_time_generating:                    0.
% 1.90/1.06  sup_time_sim_full:                      0.
% 1.90/1.06  sup_time_sim_immed:                     0.
% 1.90/1.06  
% 1.90/1.06  sup_num_of_clauses:                     52
% 1.90/1.06  sup_num_in_active:                      13
% 1.90/1.06  sup_num_in_passive:                     39
% 1.90/1.06  sup_num_of_loops:                       16
% 1.90/1.06  sup_fw_superposition:                   20
% 1.90/1.06  sup_bw_superposition:                   33
% 1.90/1.06  sup_immediate_simplified:               6
% 1.90/1.06  sup_given_eliminated:                   0
% 1.90/1.06  comparisons_done:                       0
% 1.90/1.06  comparisons_avoided:                    33
% 1.90/1.06  
% 1.90/1.06  ------ Simplifications
% 1.90/1.06  
% 1.90/1.06  
% 1.90/1.06  sim_fw_subset_subsumed:                 2
% 1.90/1.06  sim_bw_subset_subsumed:                 1
% 1.90/1.06  sim_fw_subsumed:                        1
% 1.90/1.06  sim_bw_subsumed:                        4
% 1.90/1.06  sim_fw_subsumption_res:                 1
% 1.90/1.06  sim_bw_subsumption_res:                 0
% 1.90/1.06  sim_tautology_del:                      0
% 1.90/1.06  sim_eq_tautology_del:                   0
% 1.90/1.06  sim_eq_res_simp:                        3
% 1.90/1.06  sim_fw_demodulated:                     1
% 1.90/1.06  sim_bw_demodulated:                     3
% 1.90/1.06  sim_light_normalised:                   3
% 1.90/1.06  sim_joinable_taut:                      0
% 1.90/1.06  sim_joinable_simp:                      0
% 1.90/1.06  sim_ac_normalised:                      0
% 1.90/1.06  sim_smt_subsumption:                    0
% 1.90/1.06  
%------------------------------------------------------------------------------
