%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0011+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:11 EST 2020

% Result     : Theorem 10.95s
% Output     : CNFRefutation 10.95s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 630 expanded)
%              Number of clauses        :   30 ( 136 expanded)
%              Number of leaves         :    7 ( 137 expanded)
%              Depth                    :   17
%              Number of atoms          :  233 (4106 expanded)
%              Number of equality atoms :   35 ( 570 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f87,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f88,plain,(
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
    inference(flattening,[],[f87])).

fof(f89,plain,(
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
    inference(rectify,[],[f88])).

fof(f90,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & ~ r2_hidden(sK2(X0,X1,X2),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( r2_hidden(sK2(X0,X1,X2),X1)
          | r2_hidden(sK2(X0,X1,X2),X0)
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f91,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & ~ r2_hidden(sK2(X0,X1,X2),X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( r2_hidden(sK2(X0,X1,X2),X1)
            | r2_hidden(sK2(X0,X1,X2),X0)
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f89,f90])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f44,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(negated_conjecture,[],[f44])).

fof(f75,plain,(
    ? [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) != k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(ennf_transformation,[],[f45])).

fof(f124,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) != k2_xboole_0(k2_xboole_0(X0,X1),X2)
   => k2_xboole_0(k2_xboole_0(sK13,sK14),sK15) != k2_xboole_0(sK13,k2_xboole_0(sK14,sK15)) ),
    introduced(choice_axiom,[])).

fof(f125,plain,(
    k2_xboole_0(k2_xboole_0(sK13,sK14),sK15) != k2_xboole_0(sK13,k2_xboole_0(sK14,sK15)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14,sK15])],[f75,f124])).

fof(f199,plain,(
    k2_xboole_0(k2_xboole_0(sK13,sK14),sK15) != k2_xboole_0(sK13,k2_xboole_0(sK14,sK15)) ),
    inference(cnf_transformation,[],[f125])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f57])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f83])).

fof(f85,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f84,f85])).

fof(f134,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f122,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f122])).

fof(f190,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f123])).

fof(f231,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f190])).

fof(f137,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f91])).

fof(f223,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f137])).

fof(f138,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f91])).

fof(f222,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f138])).

fof(f139,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f91])).

fof(f221,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f139])).

cnf(c_12,plain,
    ( r2_hidden(sK2(X0,X1,X2),X1)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | r2_hidden(sK2(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f140])).

cnf(c_71,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(sK13,sK14),sK15) != k2_xboole_0(sK13,k2_xboole_0(sK14,sK15)) ),
    inference(cnf_transformation,[],[f199])).

cnf(c_20545,plain,
    ( r2_hidden(sK2(k2_xboole_0(sK13,sK14),sK15,k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))),k2_xboole_0(sK13,k2_xboole_0(sK14,sK15)))
    | r2_hidden(sK2(k2_xboole_0(sK13,sK14),sK15,k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))),k2_xboole_0(sK13,sK14))
    | r2_hidden(sK2(k2_xboole_0(sK13,sK14),sK15,k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))),sK15) ),
    inference(resolution,[status(thm)],[c_12,c_71])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_21345,plain,
    ( ~ r1_tarski(k2_xboole_0(sK13,k2_xboole_0(sK14,sK15)),X0)
    | r2_hidden(sK2(k2_xboole_0(sK13,sK14),sK15,k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))),X0)
    | r2_hidden(sK2(k2_xboole_0(sK13,sK14),sK15,k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))),k2_xboole_0(sK13,sK14))
    | r2_hidden(sK2(k2_xboole_0(sK13,sK14),sK15,k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))),sK15) ),
    inference(resolution,[status(thm)],[c_20545,c_9])).

cnf(c_21704,plain,
    ( ~ r1_tarski(k2_xboole_0(sK13,k2_xboole_0(sK14,sK15)),k2_xboole_0(sK13,sK14))
    | r2_hidden(sK2(k2_xboole_0(sK13,sK14),sK15,k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))),k2_xboole_0(sK13,sK14))
    | r2_hidden(sK2(k2_xboole_0(sK13,sK14),sK15,k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))),sK15) ),
    inference(factoring,[status(thm)],[c_21345])).

cnf(c_11,plain,
    ( ~ r2_hidden(sK2(X0,X1,X2),X2)
    | ~ r2_hidden(sK2(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f141])).

cnf(c_22200,plain,
    ( ~ r1_tarski(k2_xboole_0(sK13,k2_xboole_0(sK14,sK15)),k2_xboole_0(sK13,sK14))
    | ~ r2_hidden(sK2(k2_xboole_0(sK13,sK14),sK15,k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))),k2_xboole_0(sK13,k2_xboole_0(sK14,sK15)))
    | r2_hidden(sK2(k2_xboole_0(sK13,sK14),sK15,k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))),sK15)
    | k2_xboole_0(k2_xboole_0(sK13,sK14),sK15) = k2_xboole_0(sK13,k2_xboole_0(sK14,sK15)) ),
    inference(resolution,[status(thm)],[c_21704,c_11])).

cnf(c_10,plain,
    ( ~ r2_hidden(sK2(X0,X1,X2),X1)
    | ~ r2_hidden(sK2(X0,X1,X2),X2)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f142])).

cnf(c_3541,plain,
    ( ~ r2_hidden(sK2(k2_xboole_0(sK13,sK14),sK15,k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))),k2_xboole_0(sK13,k2_xboole_0(sK14,sK15)))
    | ~ r2_hidden(sK2(k2_xboole_0(sK13,sK14),sK15,k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))),sK15)
    | k2_xboole_0(k2_xboole_0(sK13,sK14),sK15) = k2_xboole_0(sK13,k2_xboole_0(sK14,sK15)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_64,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f231])).

cnf(c_22960,plain,
    ( r1_tarski(k2_xboole_0(sK13,sK14),k2_xboole_0(sK13,sK14)) ),
    inference(instantiation,[status(thm)],[c_64])).

cnf(c_21646,plain,
    ( ~ r1_tarski(k2_xboole_0(sK13,k2_xboole_0(sK14,sK15)),X0)
    | ~ r1_tarski(k2_xboole_0(sK13,sK14),X1)
    | r2_hidden(sK2(k2_xboole_0(sK13,sK14),sK15,k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))),X0)
    | r2_hidden(sK2(k2_xboole_0(sK13,sK14),sK15,k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))),X1)
    | r2_hidden(sK2(k2_xboole_0(sK13,sK14),sK15,k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))),sK15) ),
    inference(resolution,[status(thm)],[c_21345,c_9])).

cnf(c_25000,plain,
    ( ~ r1_tarski(k2_xboole_0(sK13,k2_xboole_0(sK14,sK15)),sK15)
    | ~ r1_tarski(k2_xboole_0(sK13,sK14),X0)
    | r2_hidden(sK2(k2_xboole_0(sK13,sK14),sK15,k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))),X0)
    | r2_hidden(sK2(k2_xboole_0(sK13,sK14),sK15,k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))),sK15) ),
    inference(factoring,[status(thm)],[c_21646])).

cnf(c_3960,plain,
    ( ~ r1_tarski(k2_xboole_0(sK13,sK14),X0)
    | r2_hidden(sK2(k2_xboole_0(sK13,sK14),sK15,k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))),X0)
    | ~ r2_hidden(sK2(k2_xboole_0(sK13,sK14),sK15,k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))),k2_xboole_0(sK13,sK14)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_15,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f223])).

cnf(c_21350,plain,
    ( r2_hidden(sK2(k2_xboole_0(sK13,sK14),sK15,k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))),k2_xboole_0(sK14,sK15))
    | r2_hidden(sK2(k2_xboole_0(sK13,sK14),sK15,k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))),k2_xboole_0(sK13,sK14))
    | r2_hidden(sK2(k2_xboole_0(sK13,sK14),sK15,k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))),sK15)
    | r2_hidden(sK2(k2_xboole_0(sK13,sK14),sK15,k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))),sK13) ),
    inference(resolution,[status(thm)],[c_20545,c_15])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f222])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f221])).

cnf(c_21787,plain,
    ( r2_hidden(sK2(k2_xboole_0(sK13,sK14),sK15,k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))),k2_xboole_0(sK14,sK15))
    | r2_hidden(sK2(k2_xboole_0(sK13,sK14),sK15,k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))),k2_xboole_0(sK13,sK14)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_21350,c_14,c_13])).

cnf(c_21962,plain,
    ( r2_hidden(sK2(k2_xboole_0(sK13,sK14),sK15,k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))),k2_xboole_0(sK13,sK14))
    | r2_hidden(sK2(k2_xboole_0(sK13,sK14),sK15,k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))),sK15)
    | r2_hidden(sK2(k2_xboole_0(sK13,sK14),sK15,k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))),sK14) ),
    inference(resolution,[status(thm)],[c_21787,c_15])).

cnf(c_29480,plain,
    ( r2_hidden(sK2(k2_xboole_0(sK13,sK14),sK15,k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))),k2_xboole_0(sK13,sK14))
    | r2_hidden(sK2(k2_xboole_0(sK13,sK14),sK15,k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))),sK15) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_21962,c_13])).

cnf(c_31924,plain,
    ( ~ r1_tarski(k2_xboole_0(sK13,sK14),X0)
    | r2_hidden(sK2(k2_xboole_0(sK13,sK14),sK15,k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))),X0)
    | r2_hidden(sK2(k2_xboole_0(sK13,sK14),sK15,k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))),sK15) ),
    inference(global_propositional_subsumption,[status(thm)],[c_25000,c_3960,c_29480])).

cnf(c_32326,plain,
    ( ~ r1_tarski(k2_xboole_0(sK13,sK14),k2_xboole_0(sK13,sK14))
    | ~ r2_hidden(sK2(k2_xboole_0(sK13,sK14),sK15,k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))),k2_xboole_0(sK13,k2_xboole_0(sK14,sK15)))
    | r2_hidden(sK2(k2_xboole_0(sK13,sK14),sK15,k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))),sK15)
    | k2_xboole_0(k2_xboole_0(sK13,sK14),sK15) = k2_xboole_0(sK13,k2_xboole_0(sK14,sK15)) ),
    inference(resolution,[status(thm)],[c_31924,c_11])).

cnf(c_34108,plain,
    ( ~ r2_hidden(sK2(k2_xboole_0(sK13,sK14),sK15,k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))),k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22200,c_71,c_3541,c_22960,c_32326])).

cnf(c_34789,plain,
    ( ~ r2_hidden(sK2(k2_xboole_0(sK13,sK14),sK15,k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))),k2_xboole_0(sK14,sK15)) ),
    inference(resolution,[status(thm)],[c_34108,c_13])).

cnf(c_41201,plain,
    ( ~ r2_hidden(sK2(k2_xboole_0(sK13,sK14),sK15,k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))),sK14) ),
    inference(resolution,[status(thm)],[c_34789,c_14])).

cnf(c_34791,plain,
    ( ~ r2_hidden(sK2(k2_xboole_0(sK13,sK14),sK15,k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))),sK13) ),
    inference(resolution,[status(thm)],[c_34108,c_14])).

cnf(c_3972,plain,
    ( ~ r2_hidden(sK2(k2_xboole_0(sK13,sK14),sK15,k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))),k2_xboole_0(sK13,sK14))
    | r2_hidden(sK2(k2_xboole_0(sK13,sK14),sK15,k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))),sK14)
    | r2_hidden(sK2(k2_xboole_0(sK13,sK14),sK15,k2_xboole_0(sK13,k2_xboole_0(sK14,sK15))),sK13) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_41201,c_34791,c_34789,c_21787,c_3972])).

%------------------------------------------------------------------------------
