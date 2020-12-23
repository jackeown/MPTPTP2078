%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0706+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:56 EST 2020

% Result     : Theorem 0.79s
% Output     : CNFRefutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 127 expanded)
%              Number of clauses        :   33 (  42 expanded)
%              Number of leaves         :    6 (  25 expanded)
%              Depth                    :   14
%              Number of atoms          :  167 ( 583 expanded)
%              Number of equality atoms :   60 ( 186 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f9])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f14])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X1,k2_relat_1(X2))
          & r1_tarski(X0,k2_relat_1(X2))
          & k10_relat_1(X2,X0) = k10_relat_1(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X1,k2_relat_1(X2))
            & r1_tarski(X0,k2_relat_1(X2))
            & k10_relat_1(X2,X0) = k10_relat_1(X2,X1) )
         => X0 = X1 ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & r1_tarski(X1,k2_relat_1(X2))
      & r1_tarski(X0,k2_relat_1(X2))
      & k10_relat_1(X2,X0) = k10_relat_1(X2,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & r1_tarski(X1,k2_relat_1(X2))
      & r1_tarski(X0,k2_relat_1(X2))
      & k10_relat_1(X2,X0) = k10_relat_1(X2,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X1
        & r1_tarski(X1,k2_relat_1(X2))
        & r1_tarski(X0,k2_relat_1(X2))
        & k10_relat_1(X2,X0) = k10_relat_1(X2,X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( sK0 != sK1
      & r1_tarski(sK1,k2_relat_1(sK2))
      & r1_tarski(sK0,k2_relat_1(sK2))
      & k10_relat_1(sK2,sK0) = k10_relat_1(sK2,sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( sK0 != sK1
    & r1_tarski(sK1,k2_relat_1(sK2))
    & r1_tarski(sK0,k2_relat_1(sK2))
    & k10_relat_1(sK2,sK0) = k10_relat_1(sK2,sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f11])).

fof(f19,plain,(
    k10_relat_1(sK2,sK0) = k10_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k2_relat_1(X2))
      | ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k2_relat_1(X2))
      | ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f5])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k2_relat_1(X2))
      | ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f18,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f17,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f15,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f22,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f21,plain,(
    r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f20,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_238,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_7,negated_conjecture,
    ( k10_relat_1(sK2,sK0) = k10_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k2_relat_1(X2))
    | ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_8,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_84,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k2_relat_1(X2))
    | ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
    | ~ v1_relat_1(X2)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_8])).

cnf(c_85,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k2_relat_1(sK2))
    | ~ r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))
    | ~ v1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_84])).

cnf(c_9,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_87,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))
    | ~ r1_tarski(X0,k2_relat_1(sK2))
    | r1_tarski(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_85,c_9])).

cnf(c_88,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k2_relat_1(sK2))
    | ~ r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) ),
    inference(renaming,[status(thm)],[c_87])).

cnf(c_235,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k2_relat_1(sK2)) != iProver_top
    | r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_88])).

cnf(c_427,plain,
    ( r1_tarski(X0,k2_relat_1(sK2)) != iProver_top
    | r1_tarski(X0,sK1) = iProver_top
    | r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_235])).

cnf(c_631,plain,
    ( r1_tarski(sK0,k2_relat_1(sK2)) != iProver_top
    | r1_tarski(sK0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_238,c_427])).

cnf(c_589,plain,
    ( r1_tarski(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_592,plain,
    ( r1_tarski(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_589])).

cnf(c_144,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_298,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0))
    | k10_relat_1(sK2,sK1) != X0
    | k10_relat_1(sK2,sK0) != X1 ),
    inference(instantiation,[status(thm)],[c_144])).

cnf(c_392,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK1),X0)
    | r1_tarski(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0))
    | k10_relat_1(sK2,sK1) != k10_relat_1(sK2,sK1)
    | k10_relat_1(sK2,sK0) != X0 ),
    inference(instantiation,[status(thm)],[c_298])).

cnf(c_588,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK1))
    | r1_tarski(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0))
    | k10_relat_1(sK2,sK1) != k10_relat_1(sK2,sK1)
    | k10_relat_1(sK2,sK0) != k10_relat_1(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_392])).

cnf(c_590,plain,
    ( k10_relat_1(sK2,sK1) != k10_relat_1(sK2,sK1)
    | k10_relat_1(sK2,sK0) != k10_relat_1(sK2,sK1)
    | r1_tarski(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK1)) != iProver_top
    | r1_tarski(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_588])).

cnf(c_142,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_393,plain,
    ( k10_relat_1(sK2,sK1) = k10_relat_1(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_142])).

cnf(c_280,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0))
    | ~ r1_tarski(sK1,k2_relat_1(sK2))
    | r1_tarski(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_88])).

cnf(c_281,plain,
    ( r1_tarski(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)) != iProver_top
    | r1_tarski(sK1,k2_relat_1(sK2)) != iProver_top
    | r1_tarski(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_280])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f15])).

cnf(c_273,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ r1_tarski(sK0,sK1)
    | sK0 = sK1 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_274,plain,
    ( sK0 = sK1
    | r1_tarski(sK1,sK0) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_273])).

cnf(c_4,negated_conjecture,
    ( sK0 != sK1 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_5,negated_conjecture,
    ( r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_13,plain,
    ( r1_tarski(sK1,k2_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6,negated_conjecture,
    ( r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_12,plain,
    ( r1_tarski(sK0,k2_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_631,c_592,c_590,c_393,c_281,c_274,c_4,c_13,c_12,c_7])).


%------------------------------------------------------------------------------
