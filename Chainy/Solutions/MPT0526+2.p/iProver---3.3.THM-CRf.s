%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0526+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:44 EST 2020

% Result     : Theorem 19.37s
% Output     : CNFRefutation 19.37s
% Verified   : 
% Statistics : Number of formulae       :   28 (  39 expanded)
%              Number of clauses        :    9 (   9 expanded)
%              Number of leaves         :    5 (   9 expanded)
%              Depth                    :    8
%              Number of atoms          :   75 ( 115 expanded)
%              Number of equality atoms :   14 (  20 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f792,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f1386,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f792])).

fof(f1387,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f1386])).

fof(f1388,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK11(X0,X1),X1)
        & r2_hidden(sK11(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1389,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK11(X0,X1),X1)
          & r2_hidden(sK11(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f1387,f1388])).

fof(f1820,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK11(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f1389])).

fof(f1819,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK11(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f1389])).

fof(f701,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1277,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f701])).

fof(f1278,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1277])).

fof(f2919,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1278])).

fof(f702,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f703,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    inference(negated_conjecture,[],[f702])).

fof(f1279,plain,(
    ? [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) != X0
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f703])).

fof(f1792,plain,
    ( ? [X0] :
        ( k8_relat_1(k2_relat_1(X0),X0) != X0
        & v1_relat_1(X0) )
   => ( k8_relat_1(k2_relat_1(sK151),sK151) != sK151
      & v1_relat_1(sK151) ) ),
    introduced(choice_axiom,[])).

fof(f1793,plain,
    ( k8_relat_1(k2_relat_1(sK151),sK151) != sK151
    & v1_relat_1(sK151) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK151])],[f1279,f1792])).

fof(f2921,plain,(
    k8_relat_1(k2_relat_1(sK151),sK151) != sK151 ),
    inference(cnf_transformation,[],[f1793])).

fof(f2920,plain,(
    v1_relat_1(sK151) ),
    inference(cnf_transformation,[],[f1793])).

cnf(c_10,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK11(X0,X1),X1) ),
    inference(cnf_transformation,[],[f1820])).

cnf(c_54286,plain,
    ( r1_tarski(k2_relat_1(sK151),k2_relat_1(sK151))
    | ~ r2_hidden(sK11(k2_relat_1(sK151),k2_relat_1(sK151)),k2_relat_1(sK151)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK11(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1819])).

cnf(c_54288,plain,
    ( r1_tarski(k2_relat_1(sK151),k2_relat_1(sK151))
    | r2_hidden(sK11(k2_relat_1(sK151),k2_relat_1(sK151)),k2_relat_1(sK151)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1095,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k8_relat_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f2919])).

cnf(c_50778,plain,
    ( ~ r1_tarski(k2_relat_1(sK151),k2_relat_1(sK151))
    | ~ v1_relat_1(sK151)
    | k8_relat_1(k2_relat_1(sK151),sK151) = sK151 ),
    inference(instantiation,[status(thm)],[c_1095])).

cnf(c_1096,negated_conjecture,
    ( k8_relat_1(k2_relat_1(sK151),sK151) != sK151 ),
    inference(cnf_transformation,[],[f2921])).

cnf(c_1097,negated_conjecture,
    ( v1_relat_1(sK151) ),
    inference(cnf_transformation,[],[f2920])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_54286,c_54288,c_50778,c_1096,c_1097])).

%------------------------------------------------------------------------------
