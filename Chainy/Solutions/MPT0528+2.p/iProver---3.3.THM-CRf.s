%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0528+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:44 EST 2020

% Result     : Theorem 54.99s
% Output     : CNFRefutation 54.99s
% Verified   : 
% Statistics : Number of formulae       :   31 (  36 expanded)
%              Number of clauses        :   14 (  14 expanded)
%              Number of leaves         :    7 (   9 expanded)
%              Depth                    :    6
%              Number of atoms          :   66 (  78 expanded)
%              Number of equality atoms :   25 (  31 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f692,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1269,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f692])).

fof(f2914,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1269])).

fof(f701,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1279,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f701])).

fof(f1280,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1279])).

fof(f2923,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1280])).

fof(f658,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1227,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f658])).

fof(f2871,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1227])).

fof(f704,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f705,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f704])).

fof(f1283,plain,(
    ? [X0,X1] :
      ( k8_relat_1(X0,X1) != k8_relat_1(X0,k8_relat_1(X0,X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f705])).

fof(f1796,plain,
    ( ? [X0,X1] :
        ( k8_relat_1(X0,X1) != k8_relat_1(X0,k8_relat_1(X0,X1))
        & v1_relat_1(X1) )
   => ( k8_relat_1(sK151,sK152) != k8_relat_1(sK151,k8_relat_1(sK151,sK152))
      & v1_relat_1(sK152) ) ),
    introduced(choice_axiom,[])).

fof(f1797,plain,
    ( k8_relat_1(sK151,sK152) != k8_relat_1(sK151,k8_relat_1(sK151,sK152))
    & v1_relat_1(sK152) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK151,sK152])],[f1283,f1796])).

fof(f2927,plain,(
    k8_relat_1(sK151,sK152) != k8_relat_1(sK151,k8_relat_1(sK151,sK152)) ),
    inference(cnf_transformation,[],[f1797])).

fof(f2926,plain,(
    v1_relat_1(sK152) ),
    inference(cnf_transformation,[],[f1797])).

cnf(c_1086,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f2914])).

cnf(c_190409,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(sK151,sK152)),sK151)
    | ~ v1_relat_1(sK152) ),
    inference(instantiation,[status(thm)],[c_1086])).

cnf(c_1095,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k8_relat_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f2923])).

cnf(c_99851,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1(sK151,sK152)),sK151)
    | ~ v1_relat_1(k8_relat_1(sK151,sK152))
    | k8_relat_1(sK151,k8_relat_1(sK151,sK152)) = k8_relat_1(sK151,sK152) ),
    inference(instantiation,[status(thm)],[c_1095])).

cnf(c_32142,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_75148,plain,
    ( k8_relat_1(sK151,sK152) = k8_relat_1(sK151,sK152) ),
    inference(instantiation,[status(thm)],[c_32142])).

cnf(c_32143,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_59880,plain,
    ( k8_relat_1(sK151,k8_relat_1(sK151,sK152)) != X0
    | k8_relat_1(sK151,sK152) != X0
    | k8_relat_1(sK151,sK152) = k8_relat_1(sK151,k8_relat_1(sK151,sK152)) ),
    inference(instantiation,[status(thm)],[c_32143])).

cnf(c_75147,plain,
    ( k8_relat_1(sK151,k8_relat_1(sK151,sK152)) != k8_relat_1(sK151,sK152)
    | k8_relat_1(sK151,sK152) = k8_relat_1(sK151,k8_relat_1(sK151,sK152))
    | k8_relat_1(sK151,sK152) != k8_relat_1(sK151,sK152) ),
    inference(instantiation,[status(thm)],[c_59880])).

cnf(c_1043,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k8_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f2871])).

cnf(c_73969,plain,
    ( v1_relat_1(k8_relat_1(sK151,sK152))
    | ~ v1_relat_1(sK152) ),
    inference(instantiation,[status(thm)],[c_1043])).

cnf(c_1098,negated_conjecture,
    ( k8_relat_1(sK151,sK152) != k8_relat_1(sK151,k8_relat_1(sK151,sK152)) ),
    inference(cnf_transformation,[],[f2927])).

cnf(c_1099,negated_conjecture,
    ( v1_relat_1(sK152) ),
    inference(cnf_transformation,[],[f2926])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_190409,c_99851,c_75148,c_75147,c_73969,c_1098,c_1099])).

%------------------------------------------------------------------------------
