%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:39 EST 2020

% Result     : Theorem 7.73s
% Output     : CNFRefutation 7.73s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 129 expanded)
%              Number of clauses        :   34 (  39 expanded)
%              Number of leaves         :    9 (  26 expanded)
%              Depth                    :   19
%              Number of atoms          :  194 ( 485 expanded)
%              Number of equality atoms :   59 ( 118 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v2_funct_1(X1)
            & r1_tarski(X0,k1_relat_1(X1)) )
         => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f38,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f39,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f43,plain,
    ( ? [X0,X1] :
        ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
        & v2_funct_1(X1)
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0
      & v2_funct_1(sK1)
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0
    & v2_funct_1(sK1)
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f43])).

fof(f71,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f66,f52])).

fof(f70,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f74,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f49,f52])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f72,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f73,plain,(
    k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_25,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_32727,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_18,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_32728,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_10,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_32729,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_20,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_setfam_1(k2_tarski(X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_344,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k2_tarski(X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_26])).

cnf(c_345,plain,
    ( ~ v1_relat_1(sK1)
    | k1_setfam_1(k2_tarski(X0,k9_relat_1(sK1,k1_relat_1(sK1)))) = k9_relat_1(sK1,k10_relat_1(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_344])).

cnf(c_27,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_349,plain,
    ( k1_setfam_1(k2_tarski(X0,k9_relat_1(sK1,k1_relat_1(sK1)))) = k9_relat_1(sK1,k10_relat_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_345,c_27])).

cnf(c_4,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_32730,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_32891,plain,
    ( r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_349,c_32730])).

cnf(c_21,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k1_relat_1(X2))
    | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_24,negated_conjecture,
    ( v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_278,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k1_relat_1(X2))
    | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_24])).

cnf(c_279,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k1_relat_1(sK1))
    | ~ r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(unflattening,[status(thm)],[c_278])).

cnf(c_281,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k1_relat_1(sK1))
    | ~ r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_279,c_27,c_26])).

cnf(c_32723,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k1_relat_1(sK1)) != iProver_top
    | r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_281])).

cnf(c_32964,plain,
    ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) = iProver_top
    | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),k1_relat_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_32891,c_32723])).

cnf(c_33045,plain,
    ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_32729,c_32964])).

cnf(c_28,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_33144,plain,
    ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_33045,c_28])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_32732,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_33153,plain,
    ( k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0
    | r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_33144,c_32732])).

cnf(c_33193,plain,
    ( k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK1)) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_32728,c_33153])).

cnf(c_33214,plain,
    ( r1_tarski(X0,k1_relat_1(sK1)) != iProver_top
    | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_33193,c_28])).

cnf(c_33215,plain,
    ( k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_33214])).

cnf(c_33225,plain,
    ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) = sK0 ),
    inference(superposition,[status(thm)],[c_32727,c_33215])).

cnf(c_23,negated_conjecture,
    ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 ),
    inference(cnf_transformation,[],[f73])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_33225,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:43:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.73/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.73/1.49  
% 7.73/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.73/1.49  
% 7.73/1.49  ------  iProver source info
% 7.73/1.49  
% 7.73/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.73/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.73/1.49  git: non_committed_changes: false
% 7.73/1.49  git: last_make_outside_of_git: false
% 7.73/1.49  
% 7.73/1.49  ------ 
% 7.73/1.49  ------ Parsing...
% 7.73/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.49  ------ Proving...
% 7.73/1.49  ------ Problem Properties 
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  clauses                                 27
% 7.73/1.49  conjectures                             3
% 7.73/1.49  EPR                                     5
% 7.73/1.49  Horn                                    27
% 7.73/1.49  unary                                   13
% 7.73/1.49  binary                                  8
% 7.73/1.49  lits                                    47
% 7.73/1.49  lits eq                                 15
% 7.73/1.49  fd_pure                                 0
% 7.73/1.49  fd_pseudo                               0
% 7.73/1.49  fd_cond                                 0
% 7.73/1.49  fd_pseudo_cond                          1
% 7.73/1.49  AC symbols                              0
% 7.73/1.49  
% 7.73/1.49  ------ Input Options Time Limit: Unbounded
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 7.73/1.49  Current options:
% 7.73/1.49  ------ 
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ Proving...
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.49  
% 7.73/1.49  ------ Proving...
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.49  
% 7.73/1.49  ------ Proving...
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.73/1.49  
% 7.73/1.49  ------ Proving...
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.49  
% 7.73/1.49  ------ Proving...
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.73/1.49  
% 7.73/1.49  ------ Proving...
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.49  
% 7.73/1.49  ------ Proving...
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.49  
% 7.73/1.49  ------ Proving...
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.49  
% 7.73/1.49  ------ Proving...
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.49  
% 7.73/1.49  ------ Proving...
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.73/1.49  
% 7.73/1.49  ------ Proving...
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.49  
% 7.73/1.49  ------ Proving...
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.73/1.49  
% 7.73/1.49  ------ Proving...
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.49  
% 7.73/1.49  ------ Proving...
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.49  
% 7.73/1.49  ------ Proving...
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.49  
% 7.73/1.49  ------ Proving...
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.49  
% 7.73/1.49  ------ Proving...
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.49  
% 7.73/1.49  ------ Proving...
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.49  
% 7.73/1.49  ------ Proving...
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.49  
% 7.73/1.49  ------ Proving...
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  % SZS status Theorem for theBenchmark.p
% 7.73/1.49  
% 7.73/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.73/1.49  
% 7.73/1.49  fof(f20,conjecture,(
% 7.73/1.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f21,negated_conjecture,(
% 7.73/1.49    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 7.73/1.49    inference(negated_conjecture,[],[f20])).
% 7.73/1.49  
% 7.73/1.49  fof(f38,plain,(
% 7.73/1.49    ? [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & (v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 7.73/1.49    inference(ennf_transformation,[],[f21])).
% 7.73/1.49  
% 7.73/1.49  fof(f39,plain,(
% 7.73/1.49    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 7.73/1.49    inference(flattening,[],[f38])).
% 7.73/1.49  
% 7.73/1.49  fof(f43,plain,(
% 7.73/1.49    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 7.73/1.49    introduced(choice_axiom,[])).
% 7.73/1.49  
% 7.73/1.49  fof(f44,plain,(
% 7.73/1.49    k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 7.73/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f43])).
% 7.73/1.49  
% 7.73/1.49  fof(f71,plain,(
% 7.73/1.49    r1_tarski(sK0,k1_relat_1(sK1))),
% 7.73/1.49    inference(cnf_transformation,[],[f44])).
% 7.73/1.49  
% 7.73/1.49  fof(f15,axiom,(
% 7.73/1.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f30,plain,(
% 7.73/1.49    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 7.73/1.49    inference(ennf_transformation,[],[f15])).
% 7.73/1.49  
% 7.73/1.49  fof(f31,plain,(
% 7.73/1.49    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.73/1.49    inference(flattening,[],[f30])).
% 7.73/1.49  
% 7.73/1.49  fof(f64,plain,(
% 7.73/1.49    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f31])).
% 7.73/1.49  
% 7.73/1.49  fof(f9,axiom,(
% 7.73/1.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f25,plain,(
% 7.73/1.49    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.73/1.49    inference(ennf_transformation,[],[f9])).
% 7.73/1.49  
% 7.73/1.49  fof(f56,plain,(
% 7.73/1.49    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f25])).
% 7.73/1.49  
% 7.73/1.49  fof(f17,axiom,(
% 7.73/1.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f34,plain,(
% 7.73/1.49    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.73/1.49    inference(ennf_transformation,[],[f17])).
% 7.73/1.49  
% 7.73/1.49  fof(f35,plain,(
% 7.73/1.49    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.73/1.49    inference(flattening,[],[f34])).
% 7.73/1.49  
% 7.73/1.49  fof(f66,plain,(
% 7.73/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f35])).
% 7.73/1.49  
% 7.73/1.49  fof(f6,axiom,(
% 7.73/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f52,plain,(
% 7.73/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.73/1.49    inference(cnf_transformation,[],[f6])).
% 7.73/1.49  
% 7.73/1.49  fof(f75,plain,(
% 7.73/1.49    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.73/1.49    inference(definition_unfolding,[],[f66,f52])).
% 7.73/1.49  
% 7.73/1.49  fof(f70,plain,(
% 7.73/1.49    v1_funct_1(sK1)),
% 7.73/1.49    inference(cnf_transformation,[],[f44])).
% 7.73/1.49  
% 7.73/1.49  fof(f69,plain,(
% 7.73/1.49    v1_relat_1(sK1)),
% 7.73/1.49    inference(cnf_transformation,[],[f44])).
% 7.73/1.49  
% 7.73/1.49  fof(f3,axiom,(
% 7.73/1.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f49,plain,(
% 7.73/1.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f3])).
% 7.73/1.49  
% 7.73/1.49  fof(f74,plain,(
% 7.73/1.49    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 7.73/1.49    inference(definition_unfolding,[],[f49,f52])).
% 7.73/1.49  
% 7.73/1.49  fof(f18,axiom,(
% 7.73/1.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f36,plain,(
% 7.73/1.49    ! [X0,X1,X2] : ((r1_tarski(X0,X1) | (~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 7.73/1.49    inference(ennf_transformation,[],[f18])).
% 7.73/1.49  
% 7.73/1.49  fof(f37,plain,(
% 7.73/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.73/1.49    inference(flattening,[],[f36])).
% 7.73/1.49  
% 7.73/1.49  fof(f67,plain,(
% 7.73/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f37])).
% 7.73/1.49  
% 7.73/1.49  fof(f72,plain,(
% 7.73/1.49    v2_funct_1(sK1)),
% 7.73/1.49    inference(cnf_transformation,[],[f44])).
% 7.73/1.49  
% 7.73/1.49  fof(f1,axiom,(
% 7.73/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f40,plain,(
% 7.73/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.73/1.49    inference(nnf_transformation,[],[f1])).
% 7.73/1.49  
% 7.73/1.49  fof(f41,plain,(
% 7.73/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.73/1.49    inference(flattening,[],[f40])).
% 7.73/1.49  
% 7.73/1.49  fof(f47,plain,(
% 7.73/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f41])).
% 7.73/1.49  
% 7.73/1.49  fof(f73,plain,(
% 7.73/1.49    k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0),
% 7.73/1.49    inference(cnf_transformation,[],[f44])).
% 7.73/1.49  
% 7.73/1.49  cnf(c_25,negated_conjecture,
% 7.73/1.49      ( r1_tarski(sK0,k1_relat_1(sK1)) ),
% 7.73/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_32727,plain,
% 7.73/1.49      ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_18,plain,
% 7.73/1.49      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
% 7.73/1.49      | ~ r1_tarski(X0,k1_relat_1(X1))
% 7.73/1.49      | ~ v1_relat_1(X1) ),
% 7.73/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_32728,plain,
% 7.73/1.49      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
% 7.73/1.49      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 7.73/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_10,plain,
% 7.73/1.49      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 7.73/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_32729,plain,
% 7.73/1.49      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
% 7.73/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_20,plain,
% 7.73/1.49      ( ~ v1_funct_1(X0)
% 7.73/1.49      | ~ v1_relat_1(X0)
% 7.73/1.49      | k1_setfam_1(k2_tarski(X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
% 7.73/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_26,negated_conjecture,
% 7.73/1.49      ( v1_funct_1(sK1) ),
% 7.73/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_344,plain,
% 7.73/1.49      ( ~ v1_relat_1(X0)
% 7.73/1.49      | k1_setfam_1(k2_tarski(X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1))
% 7.73/1.49      | sK1 != X0 ),
% 7.73/1.49      inference(resolution_lifted,[status(thm)],[c_20,c_26]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_345,plain,
% 7.73/1.49      ( ~ v1_relat_1(sK1)
% 7.73/1.49      | k1_setfam_1(k2_tarski(X0,k9_relat_1(sK1,k1_relat_1(sK1)))) = k9_relat_1(sK1,k10_relat_1(sK1,X0)) ),
% 7.73/1.49      inference(unflattening,[status(thm)],[c_344]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_27,negated_conjecture,
% 7.73/1.49      ( v1_relat_1(sK1) ),
% 7.73/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_349,plain,
% 7.73/1.49      ( k1_setfam_1(k2_tarski(X0,k9_relat_1(sK1,k1_relat_1(sK1)))) = k9_relat_1(sK1,k10_relat_1(sK1,X0)) ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_345,c_27]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_4,plain,
% 7.73/1.49      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
% 7.73/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_32730,plain,
% 7.73/1.49      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_32891,plain,
% 7.73/1.49      ( r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) = iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_349,c_32730]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_21,plain,
% 7.73/1.49      ( r1_tarski(X0,X1)
% 7.73/1.49      | ~ r1_tarski(X0,k1_relat_1(X2))
% 7.73/1.49      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 7.73/1.49      | ~ v2_funct_1(X2)
% 7.73/1.49      | ~ v1_funct_1(X2)
% 7.73/1.49      | ~ v1_relat_1(X2) ),
% 7.73/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_24,negated_conjecture,
% 7.73/1.49      ( v2_funct_1(sK1) ),
% 7.73/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_278,plain,
% 7.73/1.49      ( r1_tarski(X0,X1)
% 7.73/1.49      | ~ r1_tarski(X0,k1_relat_1(X2))
% 7.73/1.49      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 7.73/1.49      | ~ v1_funct_1(X2)
% 7.73/1.49      | ~ v1_relat_1(X2)
% 7.73/1.49      | sK1 != X2 ),
% 7.73/1.49      inference(resolution_lifted,[status(thm)],[c_21,c_24]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_279,plain,
% 7.73/1.49      ( r1_tarski(X0,X1)
% 7.73/1.49      | ~ r1_tarski(X0,k1_relat_1(sK1))
% 7.73/1.49      | ~ r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
% 7.73/1.49      | ~ v1_funct_1(sK1)
% 7.73/1.49      | ~ v1_relat_1(sK1) ),
% 7.73/1.49      inference(unflattening,[status(thm)],[c_278]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_281,plain,
% 7.73/1.49      ( r1_tarski(X0,X1)
% 7.73/1.49      | ~ r1_tarski(X0,k1_relat_1(sK1))
% 7.73/1.49      | ~ r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_279,c_27,c_26]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_32723,plain,
% 7.73/1.49      ( r1_tarski(X0,X1) = iProver_top
% 7.73/1.49      | r1_tarski(X0,k1_relat_1(sK1)) != iProver_top
% 7.73/1.49      | r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_281]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_32964,plain,
% 7.73/1.49      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) = iProver_top
% 7.73/1.49      | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),k1_relat_1(sK1)) != iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_32891,c_32723]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_33045,plain,
% 7.73/1.49      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) = iProver_top
% 7.73/1.49      | v1_relat_1(sK1) != iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_32729,c_32964]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_28,plain,
% 7.73/1.49      ( v1_relat_1(sK1) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_33144,plain,
% 7.73/1.49      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) = iProver_top ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_33045,c_28]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_0,plain,
% 7.73/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.73/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_32732,plain,
% 7.73/1.49      ( X0 = X1
% 7.73/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.73/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_33153,plain,
% 7.73/1.49      ( k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0
% 7.73/1.49      | r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) != iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_33144,c_32732]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_33193,plain,
% 7.73/1.49      ( k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0
% 7.73/1.49      | r1_tarski(X0,k1_relat_1(sK1)) != iProver_top
% 7.73/1.49      | v1_relat_1(sK1) != iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_32728,c_33153]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_33214,plain,
% 7.73/1.49      ( r1_tarski(X0,k1_relat_1(sK1)) != iProver_top
% 7.73/1.49      | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0 ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_33193,c_28]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_33215,plain,
% 7.73/1.49      ( k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0
% 7.73/1.49      | r1_tarski(X0,k1_relat_1(sK1)) != iProver_top ),
% 7.73/1.49      inference(renaming,[status(thm)],[c_33214]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_33225,plain,
% 7.73/1.49      ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) = sK0 ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_32727,c_33215]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_23,negated_conjecture,
% 7.73/1.49      ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 ),
% 7.73/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(contradiction,plain,
% 7.73/1.49      ( $false ),
% 7.73/1.49      inference(minisat,[status(thm)],[c_33225,c_23]) ).
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.73/1.49  
% 7.73/1.49  ------                               Statistics
% 7.73/1.49  
% 7.73/1.49  ------ Selected
% 7.73/1.49  
% 7.73/1.49  total_time:                             0.74
% 7.73/1.49  
%------------------------------------------------------------------------------
