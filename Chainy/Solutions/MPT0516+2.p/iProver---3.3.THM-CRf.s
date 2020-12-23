%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0516+2 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 22.90s
% Output     : CNFRefutation 22.90s
% Verified   : 
% Statistics : Number of formulae       :   29 (  40 expanded)
%              Number of clauses        :    9 (   9 expanded)
%              Number of leaves         :    5 (   9 expanded)
%              Depth                    :    8
%              Number of atoms          :   88 ( 128 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f691,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(X0,k2_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1256,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(X0,k2_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f691])).

fof(f1768,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
          | ~ r2_hidden(X0,k2_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k2_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f1256])).

fof(f1769,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
          | ~ r2_hidden(X0,k2_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k2_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1768])).

fof(f2885,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1769])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f782,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f1364,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f782])).

fof(f1365,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f1364])).

fof(f1366,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK11(X0,X1),X1)
        & r2_hidden(sK11(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1367,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK11(X0,X1),X1)
          & r2_hidden(sK11(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f1365,f1366])).

fof(f1797,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK11(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f1367])).

fof(f1798,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK11(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f1367])).

fof(f692,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f693,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    inference(negated_conjecture,[],[f692])).

fof(f1257,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f693])).

fof(f1770,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k8_relat_1(sK151,sK152)),sK151)
      & v1_relat_1(sK152) ) ),
    introduced(choice_axiom,[])).

fof(f1771,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1(sK151,sK152)),sK151)
    & v1_relat_1(sK152) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK151,sK152])],[f1257,f1770])).

fof(f2889,plain,(
    ~ r1_tarski(k2_relat_1(k8_relat_1(sK151,sK152)),sK151) ),
    inference(cnf_transformation,[],[f1771])).

fof(f2888,plain,(
    v1_relat_1(sK152) ),
    inference(cnf_transformation,[],[f1771])).

cnf(c_1085,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f2885])).

cnf(c_66990,plain,
    ( ~ r2_hidden(sK11(k2_relat_1(k8_relat_1(sK151,sK152)),sK151),k2_relat_1(k8_relat_1(sK151,sK152)))
    | r2_hidden(sK11(k2_relat_1(k8_relat_1(sK151,sK152)),sK151),sK151)
    | ~ v1_relat_1(sK152) ),
    inference(instantiation,[status(thm)],[c_1085])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK11(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1797])).

cnf(c_57376,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(sK151,sK152)),sK151)
    | r2_hidden(sK11(k2_relat_1(k8_relat_1(sK151,sK152)),sK151),k2_relat_1(k8_relat_1(sK151,sK152))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK11(X0,X1),X1) ),
    inference(cnf_transformation,[],[f1798])).

cnf(c_57368,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(sK151,sK152)),sK151)
    | ~ r2_hidden(sK11(k2_relat_1(k8_relat_1(sK151,sK152)),sK151),sK151) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1086,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1(sK151,sK152)),sK151) ),
    inference(cnf_transformation,[],[f2889])).

cnf(c_1087,negated_conjecture,
    ( v1_relat_1(sK152) ),
    inference(cnf_transformation,[],[f2888])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_66990,c_57376,c_57368,c_1086,c_1087])).

%------------------------------------------------------------------------------
