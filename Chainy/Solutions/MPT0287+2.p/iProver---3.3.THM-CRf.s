%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0287+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:33 EST 2020

% Result     : Theorem 19.62s
% Output     : CNFRefutation 19.62s
% Verified   : 
% Statistics : Number of formulae       :   42 (  66 expanded)
%              Number of clauses        :   15 (  15 expanded)
%              Number of leaves         :    8 (  18 expanded)
%              Depth                    :    9
%              Number of atoms          :  163 ( 303 expanded)
%              Number of equality atoms :    9 (  16 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f396,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f572,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f396])).

fof(f573,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f572])).

fof(f574,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f575,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f573,f574])).

fof(f722,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f575])).

fof(f385,conjecture,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f386,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ! [X2] :
            ( r2_hidden(X2,X0)
           => r1_tarski(X2,X1) )
       => r1_tarski(k3_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f385])).

fof(f560,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k3_tarski(X0),X1)
      & ! [X2] :
          ( r1_tarski(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f386])).

fof(f712,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k3_tarski(X0),X1)
        & ! [X2] :
            ( r1_tarski(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
   => ( ~ r1_tarski(k3_tarski(sK35),sK36)
      & ! [X2] :
          ( r1_tarski(X2,sK36)
          | ~ r2_hidden(X2,sK35) ) ) ),
    introduced(choice_axiom,[])).

fof(f713,plain,
    ( ~ r1_tarski(k3_tarski(sK35),sK36)
    & ! [X2] :
        ( r1_tarski(X2,sK36)
        | ~ r2_hidden(X2,sK35) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK35,sK36])],[f560,f712])).

fof(f1249,plain,(
    ! [X2] :
      ( r1_tarski(X2,sK36)
      | ~ r2_hidden(X2,sK35) ) ),
    inference(cnf_transformation,[],[f713])).

fof(f286,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f668,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f286])).

fof(f669,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f668])).

fof(f672,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK32(X0,X5),X0)
        & r2_hidden(X5,sK32(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f671,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK31(X0,X1),X0)
        & r2_hidden(X2,sK31(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f670,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK30(X0,X1),X3) )
          | ~ r2_hidden(sK30(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK30(X0,X1),X4) )
          | r2_hidden(sK30(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f673,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK30(X0,X1),X3) )
            | ~ r2_hidden(sK30(X0,X1),X1) )
          & ( ( r2_hidden(sK31(X0,X1),X0)
              & r2_hidden(sK30(X0,X1),sK31(X0,X1)) )
            | r2_hidden(sK30(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK32(X0,X5),X0)
                & r2_hidden(X5,sK32(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK30,sK31,sK32])],[f669,f672,f671,f670])).

fof(f1095,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK32(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f673])).

fof(f1668,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,sK32(X0,X5))
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f1095])).

fof(f1096,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK32(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f673])).

fof(f1667,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK32(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f1096])).

fof(f723,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f575])).

fof(f724,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f575])).

fof(f1250,plain,(
    ~ r1_tarski(k3_tarski(sK35),sK36) ),
    inference(cnf_transformation,[],[f713])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f722])).

cnf(c_29437,plain,
    ( ~ r1_tarski(sK32(sK35,sK5(k3_tarski(sK35),sK36)),X0)
    | r2_hidden(sK5(k3_tarski(sK35),sK36),X0)
    | ~ r2_hidden(sK5(k3_tarski(sK35),sK36),sK32(sK35,sK5(k3_tarski(sK35),sK36))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_77275,plain,
    ( ~ r1_tarski(sK32(sK35,sK5(k3_tarski(sK35),sK36)),sK36)
    | ~ r2_hidden(sK5(k3_tarski(sK35),sK36),sK32(sK35,sK5(k3_tarski(sK35),sK36)))
    | r2_hidden(sK5(k3_tarski(sK35),sK36),sK36) ),
    inference(instantiation,[status(thm)],[c_29437])).

cnf(c_524,negated_conjecture,
    ( r1_tarski(X0,sK36)
    | ~ r2_hidden(X0,sK35) ),
    inference(cnf_transformation,[],[f1249])).

cnf(c_29647,plain,
    ( r1_tarski(sK32(sK35,sK5(k3_tarski(sK35),sK36)),sK36)
    | ~ r2_hidden(sK32(sK35,sK5(k3_tarski(sK35),sK36)),sK35) ),
    inference(instantiation,[status(thm)],[c_524])).

cnf(c_374,plain,
    ( r2_hidden(X0,sK32(X1,X0))
    | ~ r2_hidden(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f1668])).

cnf(c_21691,plain,
    ( r2_hidden(sK5(k3_tarski(sK35),sK36),sK32(sK35,sK5(k3_tarski(sK35),sK36)))
    | ~ r2_hidden(sK5(k3_tarski(sK35),sK36),k3_tarski(sK35)) ),
    inference(instantiation,[status(thm)],[c_374])).

cnf(c_373,plain,
    ( ~ r2_hidden(X0,k3_tarski(X1))
    | r2_hidden(sK32(X1,X0),X1) ),
    inference(cnf_transformation,[],[f1667])).

cnf(c_21692,plain,
    ( r2_hidden(sK32(sK35,sK5(k3_tarski(sK35),sK36)),sK35)
    | ~ r2_hidden(sK5(k3_tarski(sK35),sK36),k3_tarski(sK35)) ),
    inference(instantiation,[status(thm)],[c_373])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK5(X0,X1),X0) ),
    inference(cnf_transformation,[],[f723])).

cnf(c_18365,plain,
    ( r1_tarski(k3_tarski(sK35),sK36)
    | r2_hidden(sK5(k3_tarski(sK35),sK36),k3_tarski(sK35)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK5(X0,X1),X1) ),
    inference(cnf_transformation,[],[f724])).

cnf(c_18357,plain,
    ( r1_tarski(k3_tarski(sK35),sK36)
    | ~ r2_hidden(sK5(k3_tarski(sK35),sK36),sK36) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_523,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(sK35),sK36) ),
    inference(cnf_transformation,[],[f1250])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_77275,c_29647,c_21691,c_21692,c_18365,c_18357,c_523])).

%------------------------------------------------------------------------------
