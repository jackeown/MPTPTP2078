%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0518+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:43 EST 2020

% Result     : Theorem 18.71s
% Output     : CNFRefutation 18.71s
% Verified   : 
% Statistics : Number of formulae       :   29 (  40 expanded)
%              Number of clauses        :    9 (   9 expanded)
%              Number of leaves         :    5 (   9 expanded)
%              Depth                    :    8
%              Number of atoms          :   88 ( 128 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f691,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(X0,k2_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1258,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(X0,k2_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f691])).

fof(f1772,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
          | ~ r2_hidden(X0,k2_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k2_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f1258])).

fof(f1773,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
          | ~ r2_hidden(X0,k2_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k2_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1772])).

fof(f2890,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k2_relat_1(X2))
      | ~ r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1773])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f784,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f1368,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f784])).

fof(f1369,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f1368])).

fof(f1370,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK11(X0,X1),X1)
        & r2_hidden(sK11(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1371,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK11(X0,X1),X1)
          & r2_hidden(sK11(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f1369,f1370])).

fof(f1801,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK11(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f1371])).

fof(f1802,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK11(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f1371])).

fof(f694,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f695,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1)) ) ),
    inference(negated_conjecture,[],[f694])).

fof(f1261,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f695])).

fof(f1774,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k8_relat_1(sK151,sK152)),k2_relat_1(sK152))
      & v1_relat_1(sK152) ) ),
    introduced(choice_axiom,[])).

fof(f1775,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1(sK151,sK152)),k2_relat_1(sK152))
    & v1_relat_1(sK152) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK151,sK152])],[f1261,f1774])).

fof(f2895,plain,(
    ~ r1_tarski(k2_relat_1(k8_relat_1(sK151,sK152)),k2_relat_1(sK152)) ),
    inference(cnf_transformation,[],[f1775])).

fof(f2894,plain,(
    v1_relat_1(sK152) ),
    inference(cnf_transformation,[],[f1775])).

cnf(c_1084,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(X0,k2_relat_1(k8_relat_1(X2,X1)))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f2890])).

cnf(c_66836,plain,
    ( ~ r2_hidden(sK11(k2_relat_1(k8_relat_1(sK151,sK152)),k2_relat_1(sK152)),k2_relat_1(k8_relat_1(sK151,sK152)))
    | r2_hidden(sK11(k2_relat_1(k8_relat_1(sK151,sK152)),k2_relat_1(sK152)),k2_relat_1(sK152))
    | ~ v1_relat_1(sK152) ),
    inference(instantiation,[status(thm)],[c_1084])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK11(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1801])).

cnf(c_57468,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(sK151,sK152)),k2_relat_1(sK152))
    | r2_hidden(sK11(k2_relat_1(k8_relat_1(sK151,sK152)),k2_relat_1(sK152)),k2_relat_1(k8_relat_1(sK151,sK152))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK11(X0,X1),X1) ),
    inference(cnf_transformation,[],[f1802])).

cnf(c_57460,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(sK151,sK152)),k2_relat_1(sK152))
    | ~ r2_hidden(sK11(k2_relat_1(k8_relat_1(sK151,sK152)),k2_relat_1(sK152)),k2_relat_1(sK152)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1088,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1(sK151,sK152)),k2_relat_1(sK152)) ),
    inference(cnf_transformation,[],[f2895])).

cnf(c_1089,negated_conjecture,
    ( v1_relat_1(sK152) ),
    inference(cnf_transformation,[],[f2894])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_66836,c_57468,c_57460,c_1088,c_1089])).

%------------------------------------------------------------------------------
