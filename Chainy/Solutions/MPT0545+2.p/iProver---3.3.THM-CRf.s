%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0545+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:44 EST 2020

% Result     : Theorem 23.75s
% Output     : CNFRefutation 23.75s
% Verified   : 
% Statistics : Number of formulae       :   28 (  40 expanded)
%              Number of clauses        :   15 (  16 expanded)
%              Number of leaves         :    6 (  10 expanded)
%              Depth                    :    8
%              Number of atoms          :   57 (  83 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f724,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f725,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) ) ),
    inference(negated_conjecture,[],[f724])).

fof(f1325,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f725])).

fof(f1847,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k9_relat_1(sK156,sK155),k9_relat_1(sK156,k1_relat_1(sK156)))
      & v1_relat_1(sK156) ) ),
    introduced(choice_axiom,[])).

fof(f1848,plain,
    ( ~ r1_tarski(k9_relat_1(sK156,sK155),k9_relat_1(sK156,k1_relat_1(sK156)))
    & v1_relat_1(sK156) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK155,sK156])],[f1325,f1847])).

fof(f3004,plain,(
    v1_relat_1(sK156) ),
    inference(cnf_transformation,[],[f1848])).

fof(f723,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1324,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f723])).

fof(f3003,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1324])).

fof(f721,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1322,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f721])).

fof(f3001,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1322])).

fof(f3005,plain,(
    ~ r1_tarski(k9_relat_1(sK156,sK155),k9_relat_1(sK156,k1_relat_1(sK156))) ),
    inference(cnf_transformation,[],[f1848])).

cnf(c_32654,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_56618,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(sK156,sK155),k9_relat_1(sK156,k1_relat_1(sK156)))
    | k9_relat_1(sK156,k1_relat_1(sK156)) != X1
    | k9_relat_1(sK156,sK155) != X0 ),
    inference(instantiation,[status(thm)],[c_32654])).

cnf(c_65786,plain,
    ( ~ r1_tarski(k9_relat_1(sK156,sK155),X0)
    | r1_tarski(k9_relat_1(sK156,sK155),k9_relat_1(sK156,k1_relat_1(sK156)))
    | k9_relat_1(sK156,k1_relat_1(sK156)) != X0
    | k9_relat_1(sK156,sK155) != k9_relat_1(sK156,sK155) ),
    inference(instantiation,[status(thm)],[c_56618])).

cnf(c_88290,plain,
    ( r1_tarski(k9_relat_1(sK156,sK155),k9_relat_1(sK156,k1_relat_1(sK156)))
    | ~ r1_tarski(k9_relat_1(sK156,sK155),k2_relat_1(sK156))
    | k9_relat_1(sK156,k1_relat_1(sK156)) != k2_relat_1(sK156)
    | k9_relat_1(sK156,sK155) != k9_relat_1(sK156,sK155) ),
    inference(instantiation,[status(thm)],[c_65786])).

cnf(c_1126,negated_conjecture,
    ( v1_relat_1(sK156) ),
    inference(cnf_transformation,[],[f3004])).

cnf(c_51064,plain,
    ( v1_relat_1(sK156) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1126])).

cnf(c_1124,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f3003])).

cnf(c_51066,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1124])).

cnf(c_75515,plain,
    ( k9_relat_1(sK156,k1_relat_1(sK156)) = k2_relat_1(sK156) ),
    inference(superposition,[status(thm)],[c_51064,c_51066])).

cnf(c_32646,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_65787,plain,
    ( k9_relat_1(sK156,sK155) = k9_relat_1(sK156,sK155) ),
    inference(instantiation,[status(thm)],[c_32646])).

cnf(c_1122,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f3001])).

cnf(c_65150,plain,
    ( r1_tarski(k9_relat_1(sK156,sK155),k2_relat_1(sK156))
    | ~ v1_relat_1(sK156) ),
    inference(instantiation,[status(thm)],[c_1122])).

cnf(c_1125,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK156,sK155),k9_relat_1(sK156,k1_relat_1(sK156))) ),
    inference(cnf_transformation,[],[f3005])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_88290,c_75515,c_65787,c_65150,c_1125,c_1126])).

%------------------------------------------------------------------------------
