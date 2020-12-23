%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:24 EST 2020

% Result     : Theorem 15.48s
% Output     : CNFRefutation 15.48s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 110 expanded)
%              Number of clauses        :   34 (  35 expanded)
%              Number of leaves         :   13 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :  273 ( 428 expanded)
%              Number of equality atoms :   24 (  24 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f21])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f3,axiom,(
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

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f23])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( r2_hidden(X3,X1)
           => r1_xboole_0(X3,X2) )
        & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))) )
     => r1_tarski(X2,k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( ! [X3] :
              ( r2_hidden(X3,X1)
             => r1_xboole_0(X3,X2) )
          & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))) )
       => r1_tarski(X2,k3_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X2,k3_tarski(X0))
      & ! [X3] :
          ( r1_xboole_0(X3,X2)
          | ~ r2_hidden(X3,X1) )
      & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X2,k3_tarski(X0))
      & ! [X3] :
          ( r1_xboole_0(X3,X2)
          | ~ r2_hidden(X3,X1) )
      & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))) ) ),
    inference(flattening,[],[f12])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X2,k3_tarski(X0))
        & ! [X3] :
            ( r1_xboole_0(X3,X2)
            | ~ r2_hidden(X3,X1) )
        & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))) )
   => ( ~ r1_tarski(sK6,k3_tarski(sK4))
      & ! [X3] :
          ( r1_xboole_0(X3,sK6)
          | ~ r2_hidden(X3,sK5) )
      & r1_tarski(sK6,k3_tarski(k2_xboole_0(sK4,sK5))) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ r1_tarski(sK6,k3_tarski(sK4))
    & ! [X3] :
        ( r1_xboole_0(X3,sK6)
        | ~ r2_hidden(X3,sK5) )
    & r1_tarski(sK6,k3_tarski(k2_xboole_0(sK4,sK5))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f13,f27])).

fof(f44,plain,(
    r1_tarski(sK6,k3_tarski(k2_xboole_0(sK4,sK5))) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_xboole_0(X2,X1) )
     => r1_xboole_0(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_xboole_0(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_xboole_0(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_xboole_0(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ( ~ r1_xboole_0(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f25])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ~ r1_xboole_0(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f45,plain,(
    ! [X3] :
      ( r1_xboole_0(X3,sK6)
      | ~ r2_hidden(X3,sK5) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f46,plain,(
    ~ r1_tarski(sK6,k3_tarski(sK4)) ),
    inference(cnf_transformation,[],[f28])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_912,plain,
    ( ~ r2_hidden(sK0(sK6,k3_tarski(sK4)),X0)
    | r2_hidden(sK0(sK6,k3_tarski(sK4)),X1)
    | ~ r1_tarski(X0,X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_4563,plain,
    ( ~ r2_hidden(sK0(sK6,k3_tarski(sK4)),X0)
    | r2_hidden(sK0(sK6,k3_tarski(sK4)),k2_xboole_0(k3_tarski(sK4),X1))
    | ~ r1_tarski(X0,k2_xboole_0(k3_tarski(sK4),X1)) ),
    inference(instantiation,[status(thm)],[c_912])).

cnf(c_58896,plain,
    ( ~ r2_hidden(sK0(sK6,k3_tarski(sK4)),X0)
    | r2_hidden(sK0(sK6,k3_tarski(sK4)),k2_xboole_0(k3_tarski(sK4),k3_tarski(sK5)))
    | ~ r1_tarski(X0,k2_xboole_0(k3_tarski(sK4),k3_tarski(sK5))) ),
    inference(instantiation,[status(thm)],[c_4563])).

cnf(c_58902,plain,
    ( r2_hidden(sK0(sK6,k3_tarski(sK4)),k2_xboole_0(k3_tarski(sK4),k3_tarski(sK5)))
    | ~ r2_hidden(sK0(sK6,k3_tarski(sK4)),sK6)
    | ~ r1_tarski(sK6,k2_xboole_0(k3_tarski(sK4),k3_tarski(sK5))) ),
    inference(instantiation,[status(thm)],[c_58896])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_924,plain,
    ( r2_hidden(sK0(sK6,k3_tarski(sK4)),X0)
    | r2_hidden(sK0(sK6,k3_tarski(sK4)),X1)
    | ~ r2_hidden(sK0(sK6,k3_tarski(sK4)),k2_xboole_0(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2010,plain,
    ( r2_hidden(sK0(sK6,k3_tarski(sK4)),X0)
    | ~ r2_hidden(sK0(sK6,k3_tarski(sK4)),k2_xboole_0(k3_tarski(sK4),X0))
    | r2_hidden(sK0(sK6,k3_tarski(sK4)),k3_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_924])).

cnf(c_25642,plain,
    ( ~ r2_hidden(sK0(sK6,k3_tarski(sK4)),k2_xboole_0(k3_tarski(sK4),k3_tarski(sK5)))
    | r2_hidden(sK0(sK6,k3_tarski(sK4)),k3_tarski(sK5))
    | r2_hidden(sK0(sK6,k3_tarski(sK4)),k3_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_2010])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_5192,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(sK0(X2,k3_tarski(sK4)),X1)
    | ~ r2_hidden(sK0(X2,k3_tarski(sK4)),X0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_19841,plain,
    ( ~ r1_xboole_0(k3_tarski(sK5),X0)
    | ~ r2_hidden(sK0(X1,k3_tarski(sK4)),X0)
    | ~ r2_hidden(sK0(X1,k3_tarski(sK4)),k3_tarski(sK5)) ),
    inference(instantiation,[status(thm)],[c_5192])).

cnf(c_19858,plain,
    ( ~ r1_xboole_0(k3_tarski(sK5),sK6)
    | ~ r2_hidden(sK0(sK6,k3_tarski(sK4)),k3_tarski(sK5))
    | ~ r2_hidden(sK0(sK6,k3_tarski(sK4)),sK6) ),
    inference(instantiation,[status(thm)],[c_19841])).

cnf(c_268,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_12,plain,
    ( k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2328,plain,
    ( r1_tarski(X0,k2_xboole_0(k3_tarski(X1),k3_tarski(X2)))
    | ~ r1_tarski(X3,k3_tarski(k2_xboole_0(X1,X2)))
    | X0 != X3 ),
    inference(resolution,[status(thm)],[c_268,c_12])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(sK6,k3_tarski(k2_xboole_0(sK4,sK5))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_13778,plain,
    ( r1_tarski(X0,k2_xboole_0(k3_tarski(sK4),k3_tarski(sK5)))
    | X0 != sK6 ),
    inference(resolution,[status(thm)],[c_2328,c_17])).

cnf(c_13780,plain,
    ( r1_tarski(sK6,k2_xboole_0(k3_tarski(sK4),k3_tarski(sK5)))
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_13778])).

cnf(c_13,plain,
    ( ~ r1_xboole_0(sK3(X0,X1),X1)
    | r1_xboole_0(k3_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_16,negated_conjecture,
    ( r1_xboole_0(X0,sK6)
    | ~ r2_hidden(X0,sK5) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1026,plain,
    ( r1_xboole_0(k3_tarski(X0),sK6)
    | ~ r2_hidden(sK3(X0,sK6),sK5) ),
    inference(resolution,[status(thm)],[c_13,c_16])).

cnf(c_14,plain,
    ( r1_xboole_0(k3_tarski(X0),X1)
    | r2_hidden(sK3(X0,X1),X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1036,plain,
    ( r1_xboole_0(k3_tarski(sK5),sK6) ),
    inference(resolution,[status(thm)],[c_1026,c_14])).

cnf(c_266,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_279,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_266])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_15,negated_conjecture,
    ( ~ r1_tarski(sK6,k3_tarski(sK4)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_227,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | k3_tarski(sK4) != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_15])).

cnf(c_228,plain,
    ( ~ r2_hidden(sK0(sK6,k3_tarski(sK4)),k3_tarski(sK4)) ),
    inference(unflattening,[status(thm)],[c_227])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_220,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | k3_tarski(sK4) != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_15])).

cnf(c_221,plain,
    ( r2_hidden(sK0(sK6,k3_tarski(sK4)),sK6) ),
    inference(unflattening,[status(thm)],[c_220])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_58902,c_25642,c_19858,c_13780,c_1036,c_279,c_228,c_221])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:29:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.48/2.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.48/2.49  
% 15.48/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.48/2.49  
% 15.48/2.49  ------  iProver source info
% 15.48/2.49  
% 15.48/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.48/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.48/2.49  git: non_committed_changes: false
% 15.48/2.49  git: last_make_outside_of_git: false
% 15.48/2.49  
% 15.48/2.49  ------ 
% 15.48/2.49  ------ Parsing...
% 15.48/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.48/2.49  
% 15.48/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 15.48/2.49  
% 15.48/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.48/2.49  
% 15.48/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.48/2.49  ------ Proving...
% 15.48/2.49  ------ Problem Properties 
% 15.48/2.49  
% 15.48/2.49  
% 15.48/2.49  clauses                                 18
% 15.48/2.49  conjectures                             3
% 15.48/2.49  EPR                                     3
% 15.48/2.49  Horn                                    12
% 15.48/2.49  unary                                   3
% 15.48/2.49  binary                                  9
% 15.48/2.49  lits                                    40
% 15.48/2.49  lits eq                                 4
% 15.48/2.49  fd_pure                                 0
% 15.48/2.49  fd_pseudo                               0
% 15.48/2.49  fd_cond                                 0
% 15.48/2.49  fd_pseudo_cond                          3
% 15.48/2.49  AC symbols                              0
% 15.48/2.49  
% 15.48/2.49  ------ Input Options Time Limit: Unbounded
% 15.48/2.49  
% 15.48/2.49  
% 15.48/2.49  ------ 
% 15.48/2.49  Current options:
% 15.48/2.49  ------ 
% 15.48/2.49  
% 15.48/2.49  
% 15.48/2.49  
% 15.48/2.49  
% 15.48/2.49  ------ Proving...
% 15.48/2.49  
% 15.48/2.49  
% 15.48/2.49  % SZS status Theorem for theBenchmark.p
% 15.48/2.49  
% 15.48/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.48/2.49  
% 15.48/2.49  fof(f1,axiom,(
% 15.48/2.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 15.48/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.48/2.49  
% 15.48/2.49  fof(f9,plain,(
% 15.48/2.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 15.48/2.49    inference(ennf_transformation,[],[f1])).
% 15.48/2.49  
% 15.48/2.49  fof(f14,plain,(
% 15.48/2.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 15.48/2.49    inference(nnf_transformation,[],[f9])).
% 15.48/2.49  
% 15.48/2.49  fof(f15,plain,(
% 15.48/2.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.48/2.49    inference(rectify,[],[f14])).
% 15.48/2.49  
% 15.48/2.49  fof(f16,plain,(
% 15.48/2.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 15.48/2.49    introduced(choice_axiom,[])).
% 15.48/2.49  
% 15.48/2.49  fof(f17,plain,(
% 15.48/2.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.48/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 15.48/2.49  
% 15.48/2.49  fof(f29,plain,(
% 15.48/2.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 15.48/2.49    inference(cnf_transformation,[],[f17])).
% 15.48/2.49  
% 15.48/2.49  fof(f2,axiom,(
% 15.48/2.49    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 15.48/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.48/2.49  
% 15.48/2.49  fof(f18,plain,(
% 15.48/2.49    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 15.48/2.49    inference(nnf_transformation,[],[f2])).
% 15.48/2.49  
% 15.48/2.49  fof(f19,plain,(
% 15.48/2.49    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 15.48/2.49    inference(flattening,[],[f18])).
% 15.48/2.49  
% 15.48/2.49  fof(f20,plain,(
% 15.48/2.49    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 15.48/2.49    inference(rectify,[],[f19])).
% 15.48/2.49  
% 15.48/2.49  fof(f21,plain,(
% 15.48/2.49    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 15.48/2.49    introduced(choice_axiom,[])).
% 15.48/2.49  
% 15.48/2.49  fof(f22,plain,(
% 15.48/2.49    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 15.48/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f21])).
% 15.48/2.49  
% 15.48/2.49  fof(f32,plain,(
% 15.48/2.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 15.48/2.49    inference(cnf_transformation,[],[f22])).
% 15.48/2.49  
% 15.48/2.49  fof(f49,plain,(
% 15.48/2.49    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 15.48/2.49    inference(equality_resolution,[],[f32])).
% 15.48/2.49  
% 15.48/2.49  fof(f3,axiom,(
% 15.48/2.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 15.48/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.48/2.49  
% 15.48/2.49  fof(f8,plain,(
% 15.48/2.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 15.48/2.49    inference(rectify,[],[f3])).
% 15.48/2.49  
% 15.48/2.49  fof(f10,plain,(
% 15.48/2.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 15.48/2.49    inference(ennf_transformation,[],[f8])).
% 15.48/2.49  
% 15.48/2.49  fof(f23,plain,(
% 15.48/2.49    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 15.48/2.49    introduced(choice_axiom,[])).
% 15.48/2.49  
% 15.48/2.49  fof(f24,plain,(
% 15.48/2.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 15.48/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f23])).
% 15.48/2.49  
% 15.48/2.49  fof(f40,plain,(
% 15.48/2.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 15.48/2.49    inference(cnf_transformation,[],[f24])).
% 15.48/2.49  
% 15.48/2.49  fof(f4,axiom,(
% 15.48/2.49    ! [X0,X1] : k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1))),
% 15.48/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.48/2.49  
% 15.48/2.49  fof(f41,plain,(
% 15.48/2.49    ( ! [X0,X1] : (k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1))) )),
% 15.48/2.49    inference(cnf_transformation,[],[f4])).
% 15.48/2.49  
% 15.48/2.49  fof(f6,conjecture,(
% 15.48/2.49    ! [X0,X1,X2] : ((! [X3] : (r2_hidden(X3,X1) => r1_xboole_0(X3,X2)) & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1)))) => r1_tarski(X2,k3_tarski(X0)))),
% 15.48/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.48/2.49  
% 15.48/2.49  fof(f7,negated_conjecture,(
% 15.48/2.49    ~! [X0,X1,X2] : ((! [X3] : (r2_hidden(X3,X1) => r1_xboole_0(X3,X2)) & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1)))) => r1_tarski(X2,k3_tarski(X0)))),
% 15.48/2.49    inference(negated_conjecture,[],[f6])).
% 15.48/2.49  
% 15.48/2.49  fof(f12,plain,(
% 15.48/2.49    ? [X0,X1,X2] : (~r1_tarski(X2,k3_tarski(X0)) & (! [X3] : (r1_xboole_0(X3,X2) | ~r2_hidden(X3,X1)) & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1)))))),
% 15.48/2.49    inference(ennf_transformation,[],[f7])).
% 15.48/2.49  
% 15.48/2.49  fof(f13,plain,(
% 15.48/2.49    ? [X0,X1,X2] : (~r1_tarski(X2,k3_tarski(X0)) & ! [X3] : (r1_xboole_0(X3,X2) | ~r2_hidden(X3,X1)) & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))))),
% 15.48/2.49    inference(flattening,[],[f12])).
% 15.48/2.49  
% 15.48/2.49  fof(f27,plain,(
% 15.48/2.49    ? [X0,X1,X2] : (~r1_tarski(X2,k3_tarski(X0)) & ! [X3] : (r1_xboole_0(X3,X2) | ~r2_hidden(X3,X1)) & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1)))) => (~r1_tarski(sK6,k3_tarski(sK4)) & ! [X3] : (r1_xboole_0(X3,sK6) | ~r2_hidden(X3,sK5)) & r1_tarski(sK6,k3_tarski(k2_xboole_0(sK4,sK5))))),
% 15.48/2.49    introduced(choice_axiom,[])).
% 15.48/2.49  
% 15.48/2.49  fof(f28,plain,(
% 15.48/2.49    ~r1_tarski(sK6,k3_tarski(sK4)) & ! [X3] : (r1_xboole_0(X3,sK6) | ~r2_hidden(X3,sK5)) & r1_tarski(sK6,k3_tarski(k2_xboole_0(sK4,sK5)))),
% 15.48/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f13,f27])).
% 15.48/2.49  
% 15.48/2.49  fof(f44,plain,(
% 15.48/2.49    r1_tarski(sK6,k3_tarski(k2_xboole_0(sK4,sK5)))),
% 15.48/2.49    inference(cnf_transformation,[],[f28])).
% 15.48/2.49  
% 15.48/2.49  fof(f5,axiom,(
% 15.48/2.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_xboole_0(X2,X1)) => r1_xboole_0(k3_tarski(X0),X1))),
% 15.48/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.48/2.49  
% 15.48/2.49  fof(f11,plain,(
% 15.48/2.49    ! [X0,X1] : (r1_xboole_0(k3_tarski(X0),X1) | ? [X2] : (~r1_xboole_0(X2,X1) & r2_hidden(X2,X0)))),
% 15.48/2.49    inference(ennf_transformation,[],[f5])).
% 15.48/2.49  
% 15.48/2.49  fof(f25,plain,(
% 15.48/2.49    ! [X1,X0] : (? [X2] : (~r1_xboole_0(X2,X1) & r2_hidden(X2,X0)) => (~r1_xboole_0(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 15.48/2.49    introduced(choice_axiom,[])).
% 15.48/2.49  
% 15.48/2.49  fof(f26,plain,(
% 15.48/2.49    ! [X0,X1] : (r1_xboole_0(k3_tarski(X0),X1) | (~r1_xboole_0(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 15.48/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f25])).
% 15.48/2.49  
% 15.48/2.49  fof(f43,plain,(
% 15.48/2.49    ( ! [X0,X1] : (r1_xboole_0(k3_tarski(X0),X1) | ~r1_xboole_0(sK3(X0,X1),X1)) )),
% 15.48/2.49    inference(cnf_transformation,[],[f26])).
% 15.48/2.49  
% 15.48/2.49  fof(f45,plain,(
% 15.48/2.49    ( ! [X3] : (r1_xboole_0(X3,sK6) | ~r2_hidden(X3,sK5)) )),
% 15.48/2.49    inference(cnf_transformation,[],[f28])).
% 15.48/2.49  
% 15.48/2.49  fof(f42,plain,(
% 15.48/2.49    ( ! [X0,X1] : (r1_xboole_0(k3_tarski(X0),X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 15.48/2.49    inference(cnf_transformation,[],[f26])).
% 15.48/2.49  
% 15.48/2.49  fof(f31,plain,(
% 15.48/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 15.48/2.49    inference(cnf_transformation,[],[f17])).
% 15.48/2.49  
% 15.48/2.49  fof(f46,plain,(
% 15.48/2.49    ~r1_tarski(sK6,k3_tarski(sK4))),
% 15.48/2.49    inference(cnf_transformation,[],[f28])).
% 15.48/2.49  
% 15.48/2.49  fof(f30,plain,(
% 15.48/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 15.48/2.49    inference(cnf_transformation,[],[f17])).
% 15.48/2.49  
% 15.48/2.49  cnf(c_2,plain,
% 15.48/2.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 15.48/2.49      inference(cnf_transformation,[],[f29]) ).
% 15.48/2.49  
% 15.48/2.49  cnf(c_912,plain,
% 15.48/2.49      ( ~ r2_hidden(sK0(sK6,k3_tarski(sK4)),X0)
% 15.48/2.49      | r2_hidden(sK0(sK6,k3_tarski(sK4)),X1)
% 15.48/2.49      | ~ r1_tarski(X0,X1) ),
% 15.48/2.49      inference(instantiation,[status(thm)],[c_2]) ).
% 15.48/2.49  
% 15.48/2.49  cnf(c_4563,plain,
% 15.48/2.49      ( ~ r2_hidden(sK0(sK6,k3_tarski(sK4)),X0)
% 15.48/2.49      | r2_hidden(sK0(sK6,k3_tarski(sK4)),k2_xboole_0(k3_tarski(sK4),X1))
% 15.48/2.49      | ~ r1_tarski(X0,k2_xboole_0(k3_tarski(sK4),X1)) ),
% 15.48/2.49      inference(instantiation,[status(thm)],[c_912]) ).
% 15.48/2.49  
% 15.48/2.49  cnf(c_58896,plain,
% 15.48/2.49      ( ~ r2_hidden(sK0(sK6,k3_tarski(sK4)),X0)
% 15.48/2.49      | r2_hidden(sK0(sK6,k3_tarski(sK4)),k2_xboole_0(k3_tarski(sK4),k3_tarski(sK5)))
% 15.48/2.49      | ~ r1_tarski(X0,k2_xboole_0(k3_tarski(sK4),k3_tarski(sK5))) ),
% 15.48/2.49      inference(instantiation,[status(thm)],[c_4563]) ).
% 15.48/2.49  
% 15.48/2.49  cnf(c_58902,plain,
% 15.48/2.49      ( r2_hidden(sK0(sK6,k3_tarski(sK4)),k2_xboole_0(k3_tarski(sK4),k3_tarski(sK5)))
% 15.48/2.49      | ~ r2_hidden(sK0(sK6,k3_tarski(sK4)),sK6)
% 15.48/2.49      | ~ r1_tarski(sK6,k2_xboole_0(k3_tarski(sK4),k3_tarski(sK5))) ),
% 15.48/2.49      inference(instantiation,[status(thm)],[c_58896]) ).
% 15.48/2.49  
% 15.48/2.49  cnf(c_8,plain,
% 15.48/2.49      ( r2_hidden(X0,X1)
% 15.48/2.49      | r2_hidden(X0,X2)
% 15.48/2.49      | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 15.48/2.49      inference(cnf_transformation,[],[f49]) ).
% 15.48/2.49  
% 15.48/2.49  cnf(c_924,plain,
% 15.48/2.49      ( r2_hidden(sK0(sK6,k3_tarski(sK4)),X0)
% 15.48/2.49      | r2_hidden(sK0(sK6,k3_tarski(sK4)),X1)
% 15.48/2.49      | ~ r2_hidden(sK0(sK6,k3_tarski(sK4)),k2_xboole_0(X1,X0)) ),
% 15.48/2.49      inference(instantiation,[status(thm)],[c_8]) ).
% 15.48/2.49  
% 15.48/2.49  cnf(c_2010,plain,
% 15.48/2.49      ( r2_hidden(sK0(sK6,k3_tarski(sK4)),X0)
% 15.48/2.49      | ~ r2_hidden(sK0(sK6,k3_tarski(sK4)),k2_xboole_0(k3_tarski(sK4),X0))
% 15.48/2.49      | r2_hidden(sK0(sK6,k3_tarski(sK4)),k3_tarski(sK4)) ),
% 15.48/2.49      inference(instantiation,[status(thm)],[c_924]) ).
% 15.48/2.49  
% 15.48/2.49  cnf(c_25642,plain,
% 15.48/2.49      ( ~ r2_hidden(sK0(sK6,k3_tarski(sK4)),k2_xboole_0(k3_tarski(sK4),k3_tarski(sK5)))
% 15.48/2.49      | r2_hidden(sK0(sK6,k3_tarski(sK4)),k3_tarski(sK5))
% 15.48/2.49      | r2_hidden(sK0(sK6,k3_tarski(sK4)),k3_tarski(sK4)) ),
% 15.48/2.49      inference(instantiation,[status(thm)],[c_2010]) ).
% 15.48/2.49  
% 15.48/2.49  cnf(c_9,plain,
% 15.48/2.49      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 15.48/2.49      inference(cnf_transformation,[],[f40]) ).
% 15.48/2.49  
% 15.48/2.49  cnf(c_5192,plain,
% 15.48/2.49      ( ~ r1_xboole_0(X0,X1)
% 15.48/2.49      | ~ r2_hidden(sK0(X2,k3_tarski(sK4)),X1)
% 15.48/2.49      | ~ r2_hidden(sK0(X2,k3_tarski(sK4)),X0) ),
% 15.48/2.49      inference(instantiation,[status(thm)],[c_9]) ).
% 15.48/2.49  
% 15.48/2.49  cnf(c_19841,plain,
% 15.48/2.49      ( ~ r1_xboole_0(k3_tarski(sK5),X0)
% 15.48/2.49      | ~ r2_hidden(sK0(X1,k3_tarski(sK4)),X0)
% 15.48/2.49      | ~ r2_hidden(sK0(X1,k3_tarski(sK4)),k3_tarski(sK5)) ),
% 15.48/2.49      inference(instantiation,[status(thm)],[c_5192]) ).
% 15.48/2.49  
% 15.48/2.49  cnf(c_19858,plain,
% 15.48/2.49      ( ~ r1_xboole_0(k3_tarski(sK5),sK6)
% 15.48/2.49      | ~ r2_hidden(sK0(sK6,k3_tarski(sK4)),k3_tarski(sK5))
% 15.48/2.49      | ~ r2_hidden(sK0(sK6,k3_tarski(sK4)),sK6) ),
% 15.48/2.49      inference(instantiation,[status(thm)],[c_19841]) ).
% 15.48/2.49  
% 15.48/2.49  cnf(c_268,plain,
% 15.48/2.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.48/2.49      theory(equality) ).
% 15.48/2.49  
% 15.48/2.49  cnf(c_12,plain,
% 15.48/2.49      ( k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1)) ),
% 15.48/2.49      inference(cnf_transformation,[],[f41]) ).
% 15.48/2.49  
% 15.48/2.49  cnf(c_2328,plain,
% 15.48/2.49      ( r1_tarski(X0,k2_xboole_0(k3_tarski(X1),k3_tarski(X2)))
% 15.48/2.49      | ~ r1_tarski(X3,k3_tarski(k2_xboole_0(X1,X2)))
% 15.48/2.49      | X0 != X3 ),
% 15.48/2.49      inference(resolution,[status(thm)],[c_268,c_12]) ).
% 15.48/2.49  
% 15.48/2.49  cnf(c_17,negated_conjecture,
% 15.48/2.49      ( r1_tarski(sK6,k3_tarski(k2_xboole_0(sK4,sK5))) ),
% 15.48/2.49      inference(cnf_transformation,[],[f44]) ).
% 15.48/2.49  
% 15.48/2.49  cnf(c_13778,plain,
% 15.48/2.49      ( r1_tarski(X0,k2_xboole_0(k3_tarski(sK4),k3_tarski(sK5)))
% 15.48/2.49      | X0 != sK6 ),
% 15.48/2.49      inference(resolution,[status(thm)],[c_2328,c_17]) ).
% 15.48/2.49  
% 15.48/2.49  cnf(c_13780,plain,
% 15.48/2.49      ( r1_tarski(sK6,k2_xboole_0(k3_tarski(sK4),k3_tarski(sK5)))
% 15.48/2.49      | sK6 != sK6 ),
% 15.48/2.49      inference(instantiation,[status(thm)],[c_13778]) ).
% 15.48/2.49  
% 15.48/2.49  cnf(c_13,plain,
% 15.48/2.49      ( ~ r1_xboole_0(sK3(X0,X1),X1) | r1_xboole_0(k3_tarski(X0),X1) ),
% 15.48/2.49      inference(cnf_transformation,[],[f43]) ).
% 15.48/2.49  
% 15.48/2.49  cnf(c_16,negated_conjecture,
% 15.48/2.49      ( r1_xboole_0(X0,sK6) | ~ r2_hidden(X0,sK5) ),
% 15.48/2.49      inference(cnf_transformation,[],[f45]) ).
% 15.48/2.49  
% 15.48/2.49  cnf(c_1026,plain,
% 15.48/2.49      ( r1_xboole_0(k3_tarski(X0),sK6) | ~ r2_hidden(sK3(X0,sK6),sK5) ),
% 15.48/2.49      inference(resolution,[status(thm)],[c_13,c_16]) ).
% 15.48/2.49  
% 15.48/2.49  cnf(c_14,plain,
% 15.48/2.49      ( r1_xboole_0(k3_tarski(X0),X1) | r2_hidden(sK3(X0,X1),X0) ),
% 15.48/2.49      inference(cnf_transformation,[],[f42]) ).
% 15.48/2.49  
% 15.48/2.49  cnf(c_1036,plain,
% 15.48/2.49      ( r1_xboole_0(k3_tarski(sK5),sK6) ),
% 15.48/2.49      inference(resolution,[status(thm)],[c_1026,c_14]) ).
% 15.48/2.49  
% 15.48/2.49  cnf(c_266,plain,( X0 = X0 ),theory(equality) ).
% 15.48/2.49  
% 15.48/2.49  cnf(c_279,plain,
% 15.48/2.49      ( sK6 = sK6 ),
% 15.48/2.49      inference(instantiation,[status(thm)],[c_266]) ).
% 15.48/2.49  
% 15.48/2.49  cnf(c_0,plain,
% 15.48/2.49      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 15.48/2.49      inference(cnf_transformation,[],[f31]) ).
% 15.48/2.49  
% 15.48/2.49  cnf(c_15,negated_conjecture,
% 15.48/2.49      ( ~ r1_tarski(sK6,k3_tarski(sK4)) ),
% 15.48/2.49      inference(cnf_transformation,[],[f46]) ).
% 15.48/2.49  
% 15.48/2.49  cnf(c_227,plain,
% 15.48/2.49      ( ~ r2_hidden(sK0(X0,X1),X1) | k3_tarski(sK4) != X1 | sK6 != X0 ),
% 15.48/2.49      inference(resolution_lifted,[status(thm)],[c_0,c_15]) ).
% 15.48/2.49  
% 15.48/2.49  cnf(c_228,plain,
% 15.48/2.49      ( ~ r2_hidden(sK0(sK6,k3_tarski(sK4)),k3_tarski(sK4)) ),
% 15.48/2.49      inference(unflattening,[status(thm)],[c_227]) ).
% 15.48/2.49  
% 15.48/2.49  cnf(c_1,plain,
% 15.48/2.49      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 15.48/2.49      inference(cnf_transformation,[],[f30]) ).
% 15.48/2.49  
% 15.48/2.49  cnf(c_220,plain,
% 15.48/2.49      ( r2_hidden(sK0(X0,X1),X0) | k3_tarski(sK4) != X1 | sK6 != X0 ),
% 15.48/2.49      inference(resolution_lifted,[status(thm)],[c_1,c_15]) ).
% 15.48/2.49  
% 15.48/2.49  cnf(c_221,plain,
% 15.48/2.49      ( r2_hidden(sK0(sK6,k3_tarski(sK4)),sK6) ),
% 15.48/2.49      inference(unflattening,[status(thm)],[c_220]) ).
% 15.48/2.49  
% 15.48/2.49  cnf(contradiction,plain,
% 15.48/2.49      ( $false ),
% 15.48/2.49      inference(minisat,
% 15.48/2.49                [status(thm)],
% 15.48/2.49                [c_58902,c_25642,c_19858,c_13780,c_1036,c_279,c_228,
% 15.48/2.49                 c_221]) ).
% 15.48/2.49  
% 15.48/2.49  
% 15.48/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.48/2.49  
% 15.48/2.49  ------                               Statistics
% 15.48/2.49  
% 15.48/2.49  ------ Selected
% 15.48/2.49  
% 15.48/2.49  total_time:                             1.652
% 15.48/2.49  
%------------------------------------------------------------------------------
