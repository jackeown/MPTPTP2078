%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0531+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:44 EST 2020

% Result     : Theorem 23.17s
% Output     : CNFRefutation 23.17s
% Verified   : 
% Statistics : Number of formulae       :   35 (  55 expanded)
%              Number of clauses        :   16 (  17 expanded)
%              Number of leaves         :    5 (  11 expanded)
%              Depth                    :   12
%              Number of atoms          :   75 ( 140 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f658,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1230,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f658])).

fof(f2880,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1230])).

fof(f707,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f708,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f707])).

fof(f1291,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f708])).

fof(f1292,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f1291])).

fof(f1805,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k8_relat_1(sK151,sK153),k8_relat_1(sK152,sK153))
      & r1_tarski(sK151,sK152)
      & v1_relat_1(sK153) ) ),
    introduced(choice_axiom,[])).

fof(f1806,plain,
    ( ~ r1_tarski(k8_relat_1(sK151,sK153),k8_relat_1(sK152,sK153))
    & r1_tarski(sK151,sK152)
    & v1_relat_1(sK153) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK151,sK152,sK153])],[f1292,f1805])).

fof(f2938,plain,(
    v1_relat_1(sK153) ),
    inference(cnf_transformation,[],[f1806])).

fof(f2939,plain,(
    r1_tarski(sK151,sK152) ),
    inference(cnf_transformation,[],[f1806])).

fof(f706,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1289,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f706])).

fof(f1290,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1289])).

fof(f2937,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1290])).

fof(f693,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1273,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f693])).

fof(f2924,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1273])).

fof(f2940,plain,(
    ~ r1_tarski(k8_relat_1(sK151,sK153),k8_relat_1(sK152,sK153)) ),
    inference(cnf_transformation,[],[f1806])).

cnf(c_1043,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k8_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f2880])).

cnf(c_88642,plain,
    ( v1_relat_1(k8_relat_1(sK152,sK153))
    | ~ v1_relat_1(sK153) ),
    inference(instantiation,[status(thm)],[c_1043])).

cnf(c_1103,negated_conjecture,
    ( v1_relat_1(sK153) ),
    inference(cnf_transformation,[],[f2938])).

cnf(c_49360,plain,
    ( v1_relat_1(sK153) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1103])).

cnf(c_1102,negated_conjecture,
    ( r1_tarski(sK151,sK152) ),
    inference(cnf_transformation,[],[f2939])).

cnf(c_49361,plain,
    ( r1_tarski(sK151,sK152) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1102])).

cnf(c_1100,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f2937])).

cnf(c_49363,plain,
    ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1100])).

cnf(c_57984,plain,
    ( k8_relat_1(sK151,k8_relat_1(sK152,X0)) = k8_relat_1(sK151,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_49361,c_49363])).

cnf(c_58062,plain,
    ( k8_relat_1(sK151,k8_relat_1(sK152,sK153)) = k8_relat_1(sK151,sK153) ),
    inference(superposition,[status(thm)],[c_49360,c_57984])).

cnf(c_1087,plain,
    ( r1_tarski(k8_relat_1(X0,X1),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f2924])).

cnf(c_49376,plain,
    ( r1_tarski(k8_relat_1(X0,X1),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1087])).

cnf(c_68069,plain,
    ( r1_tarski(k8_relat_1(sK151,sK153),k8_relat_1(sK152,sK153)) = iProver_top
    | v1_relat_1(k8_relat_1(sK152,sK153)) != iProver_top ),
    inference(superposition,[status(thm)],[c_58062,c_49376])).

cnf(c_68150,plain,
    ( r1_tarski(k8_relat_1(sK151,sK153),k8_relat_1(sK152,sK153))
    | ~ v1_relat_1(k8_relat_1(sK152,sK153)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_68069])).

cnf(c_1101,negated_conjecture,
    ( ~ r1_tarski(k8_relat_1(sK151,sK153),k8_relat_1(sK152,sK153)) ),
    inference(cnf_transformation,[],[f2940])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_88642,c_68150,c_1101,c_1103])).

%------------------------------------------------------------------------------
