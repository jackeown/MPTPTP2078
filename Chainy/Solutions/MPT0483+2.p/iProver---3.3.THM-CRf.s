%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0483+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:41 EST 2020

% Result     : Theorem 27.53s
% Output     : CNFRefutation 27.53s
% Verified   : 
% Statistics : Number of formulae       :   28 (  39 expanded)
%              Number of clauses        :    9 (   9 expanded)
%              Number of leaves         :    5 (   9 expanded)
%              Depth                    :    8
%              Number of atoms          :   75 ( 115 expanded)
%              Number of equality atoms :   14 (  20 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f742,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f1274,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f742])).

fof(f1275,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f1274])).

fof(f1276,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK11(X0,X1),X1)
        & r2_hidden(sK11(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1277,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK11(X0,X1),X1)
          & r2_hidden(sK11(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f1275,f1276])).

fof(f1693,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK11(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f1277])).

fof(f1692,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK11(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f1277])).

fof(f721,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1250,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f721])).

fof(f1251,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1250])).

fof(f2814,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1251])).

fof(f722,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f723,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(negated_conjecture,[],[f722])).

fof(f1252,plain,(
    ? [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) != X0
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f723])).

fof(f1681,plain,
    ( ? [X0] :
        ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) != X0
        & v1_relat_1(X0) )
   => ( k5_relat_1(k6_relat_1(k1_relat_1(sK152)),sK152) != sK152
      & v1_relat_1(sK152) ) ),
    introduced(choice_axiom,[])).

fof(f1682,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(sK152)),sK152) != sK152
    & v1_relat_1(sK152) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK152])],[f1252,f1681])).

fof(f2816,plain,(
    k5_relat_1(k6_relat_1(k1_relat_1(sK152)),sK152) != sK152 ),
    inference(cnf_transformation,[],[f1682])).

fof(f2815,plain,(
    v1_relat_1(sK152) ),
    inference(cnf_transformation,[],[f1682])).

cnf(c_10,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK11(X0,X1),X1) ),
    inference(cnf_transformation,[],[f1693])).

cnf(c_51664,plain,
    ( r1_tarski(k1_relat_1(sK152),k1_relat_1(sK152))
    | ~ r2_hidden(sK11(k1_relat_1(sK152),k1_relat_1(sK152)),k1_relat_1(sK152)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK11(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1692])).

cnf(c_51666,plain,
    ( r1_tarski(k1_relat_1(sK152),k1_relat_1(sK152))
    | r2_hidden(sK11(k1_relat_1(sK152),k1_relat_1(sK152)),k1_relat_1(sK152)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1117,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f2814])).

cnf(c_48249,plain,
    ( ~ r1_tarski(k1_relat_1(sK152),k1_relat_1(sK152))
    | ~ v1_relat_1(sK152)
    | k5_relat_1(k6_relat_1(k1_relat_1(sK152)),sK152) = sK152 ),
    inference(instantiation,[status(thm)],[c_1117])).

cnf(c_1118,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k1_relat_1(sK152)),sK152) != sK152 ),
    inference(cnf_transformation,[],[f2816])).

cnf(c_1119,negated_conjecture,
    ( v1_relat_1(sK152) ),
    inference(cnf_transformation,[],[f2815])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_51664,c_51666,c_48249,c_1118,c_1119])).

%------------------------------------------------------------------------------
