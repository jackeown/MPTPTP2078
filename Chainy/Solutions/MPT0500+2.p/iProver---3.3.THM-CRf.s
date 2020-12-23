%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0500+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:42 EST 2020

% Result     : Theorem 19.15s
% Output     : CNFRefutation 19.15s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f762,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f1318,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f762])).

fof(f1319,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f1318])).

fof(f1320,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK11(X0,X1),X1)
        & r2_hidden(sK11(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1321,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK11(X0,X1),X1)
          & r2_hidden(sK11(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f1319,f1320])).

fof(f1745,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK11(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f1321])).

fof(f1744,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK11(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f1321])).

fof(f741,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1294,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f741])).

fof(f1295,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1294])).

fof(f2895,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1295])).

fof(f742,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f743,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(negated_conjecture,[],[f742])).

fof(f1296,plain,(
    ? [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) != X0
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f743])).

fof(f1733,plain,
    ( ? [X0] :
        ( k7_relat_1(X0,k1_relat_1(X0)) != X0
        & v1_relat_1(X0) )
   => ( k7_relat_1(sK154,k1_relat_1(sK154)) != sK154
      & v1_relat_1(sK154) ) ),
    introduced(choice_axiom,[])).

fof(f1734,plain,
    ( k7_relat_1(sK154,k1_relat_1(sK154)) != sK154
    & v1_relat_1(sK154) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK154])],[f1296,f1733])).

fof(f2897,plain,(
    k7_relat_1(sK154,k1_relat_1(sK154)) != sK154 ),
    inference(cnf_transformation,[],[f1734])).

fof(f2896,plain,(
    v1_relat_1(sK154) ),
    inference(cnf_transformation,[],[f1734])).

cnf(c_10,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK11(X0,X1),X1) ),
    inference(cnf_transformation,[],[f1745])).

cnf(c_52797,plain,
    ( r1_tarski(k1_relat_1(sK154),k1_relat_1(sK154))
    | ~ r2_hidden(sK11(k1_relat_1(sK154),k1_relat_1(sK154)),k1_relat_1(sK154)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK11(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1744])).

cnf(c_52799,plain,
    ( r1_tarski(k1_relat_1(sK154),k1_relat_1(sK154))
    | r2_hidden(sK11(k1_relat_1(sK154),k1_relat_1(sK154)),k1_relat_1(sK154)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1146,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f2895])).

cnf(c_49324,plain,
    ( ~ r1_tarski(k1_relat_1(sK154),k1_relat_1(sK154))
    | ~ v1_relat_1(sK154)
    | k7_relat_1(sK154,k1_relat_1(sK154)) = sK154 ),
    inference(instantiation,[status(thm)],[c_1146])).

cnf(c_1147,negated_conjecture,
    ( k7_relat_1(sK154,k1_relat_1(sK154)) != sK154 ),
    inference(cnf_transformation,[],[f2897])).

cnf(c_1148,negated_conjecture,
    ( v1_relat_1(sK154) ),
    inference(cnf_transformation,[],[f2896])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_52797,c_52799,c_49324,c_1147,c_1148])).

%------------------------------------------------------------------------------
