%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0506+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:43 EST 2020

% Result     : Theorem 27.68s
% Output     : CNFRefutation 27.68s
% Verified   : 
% Statistics : Number of formulae       :   37 (  57 expanded)
%              Number of clauses        :   18 (  19 expanded)
%              Number of leaves         :    5 (  11 expanded)
%              Depth                    :   11
%              Number of atoms          :   77 ( 142 expanded)
%              Number of equality atoms :   21 (  21 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f678,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f679,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f678])).

fof(f1225,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f679])).

fof(f1226,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f1225])).

fof(f1732,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k7_relat_1(sK151,sK149),k7_relat_1(sK151,sK150))
      & r1_tarski(sK149,sK150)
      & v1_relat_1(sK151) ) ),
    introduced(choice_axiom,[])).

fof(f1733,plain,
    ( ~ r1_tarski(k7_relat_1(sK151,sK149),k7_relat_1(sK151,sK150))
    & r1_tarski(sK149,sK150)
    & v1_relat_1(sK151) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK149,sK150,sK151])],[f1226,f1732])).

fof(f2827,plain,(
    v1_relat_1(sK151) ),
    inference(cnf_transformation,[],[f1733])).

fof(f2828,plain,(
    r1_tarski(sK149,sK150) ),
    inference(cnf_transformation,[],[f1733])).

fof(f677,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1223,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f677])).

fof(f1224,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1223])).

fof(f2826,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1224])).

fof(f738,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1298,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f738])).

fof(f2907,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1298])).

fof(f656,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1199,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f656])).

fof(f2800,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1199])).

fof(f2829,plain,(
    ~ r1_tarski(k7_relat_1(sK151,sK149),k7_relat_1(sK151,sK150)) ),
    inference(cnf_transformation,[],[f1733])).

cnf(c_1065,negated_conjecture,
    ( v1_relat_1(sK151) ),
    inference(cnf_transformation,[],[f2827])).

cnf(c_47985,plain,
    ( v1_relat_1(sK151) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1065])).

cnf(c_1064,negated_conjecture,
    ( r1_tarski(sK149,sK150) ),
    inference(cnf_transformation,[],[f2828])).

cnf(c_47986,plain,
    ( r1_tarski(sK149,sK150) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1064])).

cnf(c_1062,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f2826])).

cnf(c_47988,plain,
    ( k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,X2)
    | r1_tarski(X2,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1062])).

cnf(c_94061,plain,
    ( k7_relat_1(k7_relat_1(X0,sK150),sK149) = k7_relat_1(X0,sK149)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_47986,c_47988])).

cnf(c_94914,plain,
    ( k7_relat_1(k7_relat_1(sK151,sK150),sK149) = k7_relat_1(sK151,sK149) ),
    inference(superposition,[status(thm)],[c_47985,c_94061])).

cnf(c_1143,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f2907])).

cnf(c_47928,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1143])).

cnf(c_94930,plain,
    ( r1_tarski(k7_relat_1(sK151,sK149),k7_relat_1(sK151,sK150)) = iProver_top
    | v1_relat_1(k7_relat_1(sK151,sK150)) != iProver_top ),
    inference(superposition,[status(thm)],[c_94914,c_47928])).

cnf(c_1036,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2800])).

cnf(c_87228,plain,
    ( v1_relat_1(k7_relat_1(sK151,sK150))
    | ~ v1_relat_1(sK151) ),
    inference(instantiation,[status(thm)],[c_1036])).

cnf(c_87229,plain,
    ( v1_relat_1(k7_relat_1(sK151,sK150)) = iProver_top
    | v1_relat_1(sK151) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_87228])).

cnf(c_1063,negated_conjecture,
    ( ~ r1_tarski(k7_relat_1(sK151,sK149),k7_relat_1(sK151,sK150)) ),
    inference(cnf_transformation,[],[f2829])).

cnf(c_1158,plain,
    ( r1_tarski(k7_relat_1(sK151,sK149),k7_relat_1(sK151,sK150)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1063])).

cnf(c_1156,plain,
    ( v1_relat_1(sK151) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1065])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_94930,c_87229,c_1158,c_1156])).

%------------------------------------------------------------------------------
