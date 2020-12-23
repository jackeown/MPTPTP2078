%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0525+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:44 EST 2020

% Result     : Theorem 34.63s
% Output     : CNFRefutation 34.63s
% Verified   : 
% Statistics : Number of formulae       :   31 (  64 expanded)
%              Number of clauses        :   15 (  18 expanded)
%              Number of leaves         :    4 (  13 expanded)
%              Depth                    :   11
%              Number of atoms          :   66 ( 169 expanded)
%              Number of equality atoms :   31 (  64 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f701,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f702,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(k2_relat_1(X1),X0)
         => k8_relat_1(X0,X1) = X1 ) ) ),
    inference(negated_conjecture,[],[f701])).

fof(f1276,plain,(
    ? [X0,X1] :
      ( k8_relat_1(X0,X1) != X1
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f702])).

fof(f1277,plain,(
    ? [X0,X1] :
      ( k8_relat_1(X0,X1) != X1
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f1276])).

fof(f1790,plain,
    ( ? [X0,X1] :
        ( k8_relat_1(X0,X1) != X1
        & r1_tarski(k2_relat_1(X1),X0)
        & v1_relat_1(X1) )
   => ( k8_relat_1(sK151,sK152) != sK152
      & r1_tarski(k2_relat_1(sK152),sK151)
      & v1_relat_1(sK152) ) ),
    introduced(choice_axiom,[])).

fof(f1791,plain,
    ( k8_relat_1(sK151,sK152) != sK152
    & r1_tarski(k2_relat_1(sK152),sK151)
    & v1_relat_1(sK152) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK151,sK152])],[f1277,f1790])).

fof(f2917,plain,(
    v1_relat_1(sK152) ),
    inference(cnf_transformation,[],[f1791])).

fof(f699,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1274,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f699])).

fof(f2915,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1274])).

fof(f2918,plain,(
    r1_tarski(k2_relat_1(sK152),sK151) ),
    inference(cnf_transformation,[],[f1791])).

fof(f755,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1342,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f755])).

fof(f1343,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1342])).

fof(f2989,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1343])).

fof(f2919,plain,(
    k8_relat_1(sK151,sK152) != sK152 ),
    inference(cnf_transformation,[],[f1791])).

cnf(c_1097,negated_conjecture,
    ( v1_relat_1(sK152) ),
    inference(cnf_transformation,[],[f2917])).

cnf(c_49112,plain,
    ( v1_relat_1(sK152) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1097])).

cnf(c_1093,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f2915])).

cnf(c_49115,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1093])).

cnf(c_125883,plain,
    ( k5_relat_1(sK152,k6_relat_1(X0)) = k8_relat_1(X0,sK152) ),
    inference(superposition,[status(thm)],[c_49112,c_49115])).

cnf(c_1096,negated_conjecture,
    ( r1_tarski(k2_relat_1(sK152),sK151) ),
    inference(cnf_transformation,[],[f2918])).

cnf(c_49113,plain,
    ( r1_tarski(k2_relat_1(sK152),sK151) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1096])).

cnf(c_1167,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f2989])).

cnf(c_49062,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1167])).

cnf(c_61408,plain,
    ( k5_relat_1(sK152,k6_relat_1(sK151)) = sK152
    | v1_relat_1(sK152) != iProver_top ),
    inference(superposition,[status(thm)],[c_49113,c_49062])).

cnf(c_59454,plain,
    ( ~ r1_tarski(k2_relat_1(sK152),sK151)
    | ~ v1_relat_1(sK152)
    | k5_relat_1(sK152,k6_relat_1(sK151)) = sK152 ),
    inference(instantiation,[status(thm)],[c_1167])).

cnf(c_62285,plain,
    ( k5_relat_1(sK152,k6_relat_1(sK151)) = sK152 ),
    inference(global_propositional_subsumption,[status(thm)],[c_61408,c_1097,c_1096,c_59454])).

cnf(c_127238,plain,
    ( k8_relat_1(sK151,sK152) = sK152 ),
    inference(superposition,[status(thm)],[c_125883,c_62285])).

cnf(c_1095,negated_conjecture,
    ( k8_relat_1(sK151,sK152) != sK152 ),
    inference(cnf_transformation,[],[f2919])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_127238,c_1095])).

%------------------------------------------------------------------------------
