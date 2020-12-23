%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0290+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:33 EST 2020

% Result     : Theorem 15.81s
% Output     : CNFRefutation 15.81s
% Verified   : 
% Statistics : Number of formulae       :   50 (  72 expanded)
%              Number of clauses        :   15 (  16 expanded)
%              Number of leaves         :    9 (  18 expanded)
%              Depth                    :   10
%              Number of atoms          :  166 ( 267 expanded)
%              Number of equality atoms :   15 (  32 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f383,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f562,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f383])).

fof(f1254,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f562])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f586,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f587,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f586])).

fof(f588,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f587])).

fof(f589,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
          | ~ r2_hidden(sK7(X0,X1,X2),X0)
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK7(X0,X1,X2),X1)
            & r2_hidden(sK7(X0,X1,X2),X0) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f590,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
            | ~ r2_hidden(sK7(X0,X1,X2),X0)
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK7(X0,X1,X2),X1)
              & r2_hidden(sK7(X0,X1,X2),X0) )
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f588,f589])).

fof(f738,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f590])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f876,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f1288,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f738,f876])).

fof(f1626,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f1288])).

fof(f739,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f590])).

fof(f1287,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f739,f876])).

fof(f1625,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f1287])).

fof(f75,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f434,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f75])).

fof(f435,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f434])).

fof(f838,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f435])).

fof(f1335,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f838,f876])).

fof(f385,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f563,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f385])).

fof(f717,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(sK35(X0,X1),X1)
        & r2_hidden(sK35(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f718,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ( ~ r1_tarski(sK35(X0,X1),X1)
        & r2_hidden(sK35(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK35])],[f563,f717])).

fof(f1256,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | r2_hidden(sK35(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f718])).

fof(f1257,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ~ r1_tarski(sK35(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f718])).

fof(f388,conjecture,(
    ! [X0,X1] : r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f389,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) ),
    inference(negated_conjecture,[],[f388])).

fof(f565,plain,(
    ? [X0,X1] : ~ r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) ),
    inference(ennf_transformation,[],[f389])).

fof(f719,plain,
    ( ? [X0,X1] : ~ r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1)))
   => ~ r1_tarski(k3_tarski(k3_xboole_0(sK36,sK37)),k3_xboole_0(k3_tarski(sK36),k3_tarski(sK37))) ),
    introduced(choice_axiom,[])).

fof(f720,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0(sK36,sK37)),k3_xboole_0(k3_tarski(sK36),k3_tarski(sK37))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK36,sK37])],[f565,f719])).

fof(f1260,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0(sK36,sK37)),k3_xboole_0(k3_tarski(sK36),k3_tarski(sK37))) ),
    inference(cnf_transformation,[],[f720])).

fof(f1619,plain,(
    ~ r1_tarski(k3_tarski(k4_xboole_0(sK36,k4_xboole_0(sK36,sK37))),k4_xboole_0(k3_tarski(sK36),k4_xboole_0(k3_tarski(sK36),k3_tarski(sK37)))) ),
    inference(definition_unfolding,[],[f1260,f876,f876])).

cnf(c_521,plain,
    ( r1_tarski(X0,k3_tarski(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f1254])).

cnf(c_28661,plain,
    ( r1_tarski(sK35(k4_xboole_0(sK36,k4_xboole_0(sK36,sK37)),k4_xboole_0(k3_tarski(sK36),k4_xboole_0(k3_tarski(sK36),k3_tarski(sK37)))),k3_tarski(sK36))
    | ~ r2_hidden(sK35(k4_xboole_0(sK36,k4_xboole_0(sK36,sK37)),k4_xboole_0(k3_tarski(sK36),k4_xboole_0(k3_tarski(sK36),k3_tarski(sK37)))),sK36) ),
    inference(instantiation,[status(thm)],[c_521])).

cnf(c_28535,plain,
    ( r1_tarski(sK35(k4_xboole_0(sK36,k4_xboole_0(sK36,sK37)),k4_xboole_0(k3_tarski(sK36),k4_xboole_0(k3_tarski(sK36),k3_tarski(sK37)))),k3_tarski(sK37))
    | ~ r2_hidden(sK35(k4_xboole_0(sK36,k4_xboole_0(sK36,sK37)),k4_xboole_0(k3_tarski(sK36),k4_xboole_0(k3_tarski(sK36),k3_tarski(sK37)))),sK37) ),
    inference(instantiation,[status(thm)],[c_521])).

cnf(c_24,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f1626])).

cnf(c_19335,plain,
    ( ~ r2_hidden(sK35(k4_xboole_0(sK36,k4_xboole_0(sK36,sK37)),k4_xboole_0(k3_tarski(sK36),k4_xboole_0(k3_tarski(sK36),k3_tarski(sK37)))),k4_xboole_0(sK36,k4_xboole_0(sK36,sK37)))
    | r2_hidden(sK35(k4_xboole_0(sK36,k4_xboole_0(sK36,sK37)),k4_xboole_0(k3_tarski(sK36),k4_xboole_0(k3_tarski(sK36),k3_tarski(sK37)))),sK36) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_23,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f1625])).

cnf(c_19332,plain,
    ( ~ r2_hidden(sK35(k4_xboole_0(sK36,k4_xboole_0(sK36,sK37)),k4_xboole_0(k3_tarski(sK36),k4_xboole_0(k3_tarski(sK36),k3_tarski(sK37)))),k4_xboole_0(sK36,k4_xboole_0(sK36,sK37)))
    | r2_hidden(sK35(k4_xboole_0(sK36,k4_xboole_0(sK36,sK37)),k4_xboole_0(k3_tarski(sK36),k4_xboole_0(k3_tarski(sK36),k3_tarski(sK37)))),sK37) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_117,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f1335])).

cnf(c_19237,plain,
    ( r1_tarski(sK35(k4_xboole_0(sK36,k4_xboole_0(sK36,sK37)),k4_xboole_0(k3_tarski(sK36),k4_xboole_0(k3_tarski(sK36),k3_tarski(sK37)))),k4_xboole_0(k3_tarski(sK36),k4_xboole_0(k3_tarski(sK36),k3_tarski(sK37))))
    | ~ r1_tarski(sK35(k4_xboole_0(sK36,k4_xboole_0(sK36,sK37)),k4_xboole_0(k3_tarski(sK36),k4_xboole_0(k3_tarski(sK36),k3_tarski(sK37)))),k3_tarski(sK37))
    | ~ r1_tarski(sK35(k4_xboole_0(sK36,k4_xboole_0(sK36,sK37)),k4_xboole_0(k3_tarski(sK36),k4_xboole_0(k3_tarski(sK36),k3_tarski(sK37)))),k3_tarski(sK36)) ),
    inference(instantiation,[status(thm)],[c_117])).

cnf(c_524,plain,
    ( r1_tarski(k3_tarski(X0),X1)
    | r2_hidden(sK35(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1256])).

cnf(c_15011,plain,
    ( r1_tarski(k3_tarski(k4_xboole_0(sK36,k4_xboole_0(sK36,sK37))),k4_xboole_0(k3_tarski(sK36),k4_xboole_0(k3_tarski(sK36),k3_tarski(sK37))))
    | r2_hidden(sK35(k4_xboole_0(sK36,k4_xboole_0(sK36,sK37)),k4_xboole_0(k3_tarski(sK36),k4_xboole_0(k3_tarski(sK36),k3_tarski(sK37)))),k4_xboole_0(sK36,k4_xboole_0(sK36,sK37))) ),
    inference(instantiation,[status(thm)],[c_524])).

cnf(c_523,plain,
    ( ~ r1_tarski(sK35(X0,X1),X1)
    | r1_tarski(k3_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f1257])).

cnf(c_15008,plain,
    ( ~ r1_tarski(sK35(k4_xboole_0(sK36,k4_xboole_0(sK36,sK37)),k4_xboole_0(k3_tarski(sK36),k4_xboole_0(k3_tarski(sK36),k3_tarski(sK37)))),k4_xboole_0(k3_tarski(sK36),k4_xboole_0(k3_tarski(sK36),k3_tarski(sK37))))
    | r1_tarski(k3_tarski(k4_xboole_0(sK36,k4_xboole_0(sK36,sK37))),k4_xboole_0(k3_tarski(sK36),k4_xboole_0(k3_tarski(sK36),k3_tarski(sK37)))) ),
    inference(instantiation,[status(thm)],[c_523])).

cnf(c_527,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k4_xboole_0(sK36,k4_xboole_0(sK36,sK37))),k4_xboole_0(k3_tarski(sK36),k4_xboole_0(k3_tarski(sK36),k3_tarski(sK37)))) ),
    inference(cnf_transformation,[],[f1619])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_28661,c_28535,c_19335,c_19332,c_19237,c_15011,c_15008,c_527])).

%------------------------------------------------------------------------------
