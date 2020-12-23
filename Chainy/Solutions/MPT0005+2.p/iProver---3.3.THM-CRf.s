%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0005+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:10 EST 2020

% Result     : Theorem 1.22s
% Output     : CNFRefutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :   33 (  48 expanded)
%              Number of clauses        :   10 (  10 expanded)
%              Number of leaves         :    6 (  12 expanded)
%              Depth                    :    9
%              Number of atoms          :  174 ( 282 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f28,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f76,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK8(X0,X1),X1)
          & r2_hidden(sK8(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f42,f76])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f49])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f50])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & ~ r2_hidden(sK1(X0,X1,X2),X0) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( r2_hidden(sK1(X0,X1,X2),X1)
          | r2_hidden(sK1(X0,X1,X2),X0)
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & ~ r2_hidden(sK1(X0,X1,X2),X0) )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( r2_hidden(sK1(X0,X1,X2),X1)
            | r2_hidden(sK1(X0,X1,X2),X0)
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f51,f52])).

fof(f89,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f152,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f89])).

fof(f30,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( ~ r2_hidden(X2,X0)
            & r2_hidden(X2,X1) )
        & ~ ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) )
        & r2_hidden(X2,k2_xboole_0(X0,X1))
        & r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
          & ~ ( ~ r2_hidden(X2,X1)
              & r2_hidden(X2,X0) )
          & r2_hidden(X2,k2_xboole_0(X0,X1))
          & r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f30])).

fof(f44,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X2,X0)
        | ~ r2_hidden(X2,X1) )
      & ( r2_hidden(X2,X1)
        | ~ r2_hidden(X2,X0) )
      & r2_hidden(X2,k2_xboole_0(X0,X1))
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f80,plain,
    ( ? [X0,X1,X2] :
        ( ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
        & ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
        & r2_hidden(X2,k2_xboole_0(X0,X1))
        & r1_xboole_0(X0,X1) )
   => ( ( r2_hidden(sK12,sK10)
        | ~ r2_hidden(sK12,sK11) )
      & ( r2_hidden(sK12,sK11)
        | ~ r2_hidden(sK12,sK10) )
      & r2_hidden(sK12,k2_xboole_0(sK10,sK11))
      & r1_xboole_0(sK10,sK11) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,
    ( ( r2_hidden(sK12,sK10)
      | ~ r2_hidden(sK12,sK11) )
    & ( r2_hidden(sK12,sK11)
      | ~ r2_hidden(sK12,sK10) )
    & r2_hidden(sK12,k2_xboole_0(sK10,sK11))
    & r1_xboole_0(sK10,sK11) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f44,f80])).

fof(f136,plain,
    ( r2_hidden(sK12,sK10)
    | ~ r2_hidden(sK12,sK11) ),
    inference(cnf_transformation,[],[f81])).

fof(f135,plain,
    ( r2_hidden(sK12,sK11)
    | ~ r2_hidden(sK12,sK10) ),
    inference(cnf_transformation,[],[f81])).

fof(f134,plain,(
    r2_hidden(sK12,k2_xboole_0(sK10,sK11)) ),
    inference(cnf_transformation,[],[f81])).

fof(f133,plain,(
    r1_xboole_0(sK10,sK11) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_44,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_2683,plain,
    ( ~ r1_xboole_0(sK10,X0)
    | ~ r2_hidden(sK12,X0)
    | ~ r2_hidden(sK12,sK10) ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_3294,plain,
    ( ~ r1_xboole_0(sK10,sK11)
    | ~ r2_hidden(sK12,sK11)
    | ~ r2_hidden(sK12,sK10) ),
    inference(instantiation,[status(thm)],[c_2683])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f152])).

cnf(c_2512,plain,
    ( ~ r2_hidden(sK12,k2_xboole_0(sK10,sK11))
    | r2_hidden(sK12,sK11)
    | r2_hidden(sK12,sK10) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_49,negated_conjecture,
    ( ~ r2_hidden(sK12,sK11)
    | r2_hidden(sK12,sK10) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_50,negated_conjecture,
    ( r2_hidden(sK12,sK11)
    | ~ r2_hidden(sK12,sK10) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_51,negated_conjecture,
    ( r2_hidden(sK12,k2_xboole_0(sK10,sK11)) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_52,negated_conjecture,
    ( r1_xboole_0(sK10,sK11) ),
    inference(cnf_transformation,[],[f133])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3294,c_2512,c_49,c_50,c_51,c_52])).

%------------------------------------------------------------------------------
