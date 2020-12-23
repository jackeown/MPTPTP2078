%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0288+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:33 EST 2020

% Result     : Theorem 14.75s
% Output     : CNFRefutation 14.75s
% Verified   : 
% Statistics : Number of formulae       :   35 (  44 expanded)
%              Number of clauses        :   12 (  12 expanded)
%              Number of leaves         :    7 (  11 expanded)
%              Depth                    :    9
%              Number of atoms          :   92 ( 117 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f383,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f560,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f383])).

fof(f1251,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f560])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f397,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f574,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f397])).

fof(f575,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f574])).

fof(f576,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f577,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f575,f576])).

fof(f726,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f577])).

fof(f385,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f561,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f385])).

fof(f714,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(sK35(X0,X1),X1)
        & r2_hidden(sK35(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f715,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ( ~ r1_tarski(sK35(X0,X1),X1)
        & r2_hidden(sK35(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK35])],[f561,f714])).

fof(f1253,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | r2_hidden(sK35(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f715])).

fof(f1254,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ~ r1_tarski(sK35(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f715])).

fof(f386,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f387,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f386])).

fof(f562,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k3_tarski(X0),k3_tarski(X1))
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f387])).

fof(f716,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k3_tarski(X0),k3_tarski(X1))
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k3_tarski(sK36),k3_tarski(sK37))
      & r1_tarski(sK36,sK37) ) ),
    introduced(choice_axiom,[])).

fof(f717,plain,
    ( ~ r1_tarski(k3_tarski(sK36),k3_tarski(sK37))
    & r1_tarski(sK36,sK37) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK36,sK37])],[f562,f716])).

fof(f1256,plain,(
    ~ r1_tarski(k3_tarski(sK36),k3_tarski(sK37)) ),
    inference(cnf_transformation,[],[f717])).

fof(f1255,plain,(
    r1_tarski(sK36,sK37) ),
    inference(cnf_transformation,[],[f717])).

cnf(c_521,plain,
    ( r1_tarski(X0,k3_tarski(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f1251])).

cnf(c_46864,plain,
    ( r1_tarski(sK35(sK36,k3_tarski(sK37)),k3_tarski(sK37))
    | ~ r2_hidden(sK35(sK36,k3_tarski(sK37)),sK37) ),
    inference(instantiation,[status(thm)],[c_521])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f726])).

cnf(c_22062,plain,
    ( ~ r1_tarski(sK36,X0)
    | r2_hidden(sK35(sK36,k3_tarski(sK37)),X0)
    | ~ r2_hidden(sK35(sK36,k3_tarski(sK37)),sK36) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_37395,plain,
    ( ~ r1_tarski(sK36,sK37)
    | r2_hidden(sK35(sK36,k3_tarski(sK37)),sK37)
    | ~ r2_hidden(sK35(sK36,k3_tarski(sK37)),sK36) ),
    inference(instantiation,[status(thm)],[c_22062])).

cnf(c_524,plain,
    ( r1_tarski(k3_tarski(X0),X1)
    | r2_hidden(sK35(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1253])).

cnf(c_18381,plain,
    ( r1_tarski(k3_tarski(sK36),k3_tarski(sK37))
    | r2_hidden(sK35(sK36,k3_tarski(sK37)),sK36) ),
    inference(instantiation,[status(thm)],[c_524])).

cnf(c_523,plain,
    ( ~ r1_tarski(sK35(X0,X1),X1)
    | r1_tarski(k3_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f1254])).

cnf(c_18378,plain,
    ( ~ r1_tarski(sK35(sK36,k3_tarski(sK37)),k3_tarski(sK37))
    | r1_tarski(k3_tarski(sK36),k3_tarski(sK37)) ),
    inference(instantiation,[status(thm)],[c_523])).

cnf(c_525,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(sK36),k3_tarski(sK37)) ),
    inference(cnf_transformation,[],[f1256])).

cnf(c_526,negated_conjecture,
    ( r1_tarski(sK36,sK37) ),
    inference(cnf_transformation,[],[f1255])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_46864,c_37395,c_18381,c_18378,c_525,c_526])).

%------------------------------------------------------------------------------
