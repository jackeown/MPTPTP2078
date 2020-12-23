%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0289+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:56 EST 2020

% Result     : Theorem 14.91s
% Output     : CNFRefutation 14.91s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 182 expanded)
%              Number of clauses        :   33 (  41 expanded)
%              Number of leaves         :    8 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :  272 (1287 expanded)
%              Number of equality atoms :   39 ( 154 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f24,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK4(X0,X5),X0)
        & r2_hidden(X5,sK4(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK3(X0,X1),X0)
        & r2_hidden(X2,sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
              | ~ r2_hidden(sK2(X0,X1),X3) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK2(X0,X1),X4) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK2(X0,X1),X3) )
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( ( r2_hidden(sK3(X0,X1),X0)
              & r2_hidden(sK2(X0,X1),sK3(X0,X1)) )
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK4(X0,X5),X0)
                & r2_hidden(X5,sK4(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f21,f24,f23,f22])).

fof(f39,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f49,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f39])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f18,plain,(
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

fof(f19,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f18])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f46,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f33])).

fof(f37,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK4(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f51,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,sK4(X0,X5))
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f38,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK4(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f50,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK4(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,conjecture,(
    ! [X0,X1] : k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f6])).

fof(f10,plain,(
    ? [X0,X1] : k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) != k3_tarski(k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,
    ( ? [X0,X1] : k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) != k3_tarski(k2_xboole_0(X0,X1))
   => k2_xboole_0(k3_tarski(sK5),k3_tarski(sK6)) != k3_tarski(k2_xboole_0(sK5,sK6)) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    k2_xboole_0(k3_tarski(sK5),k3_tarski(sK6)) != k3_tarski(k2_xboole_0(sK5,sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f10,f26])).

fof(f45,plain,(
    k2_xboole_0(k3_tarski(sK5),k3_tarski(sK6)) != k3_tarski(k2_xboole_0(sK5,sK6)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2870,plain,
    ( ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),sK4(k2_xboole_0(sK5,sK6),sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))))
    | r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(X0))
    | ~ r2_hidden(sK4(k2_xboole_0(sK5,sK6),sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),X0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_47012,plain,
    ( ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),sK4(k2_xboole_0(sK5,sK6),sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))))
    | r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK6))
    | ~ r2_hidden(sK4(k2_xboole_0(sK5,sK6),sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),sK6) ),
    inference(instantiation,[status(thm)],[c_2870])).

cnf(c_1028,plain,
    ( ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),sK4(sK6,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))))
    | r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(X0))
    | ~ r2_hidden(sK4(sK6,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),X0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_43132,plain,
    ( ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),sK4(sK6,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))))
    | r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(k2_xboole_0(X0,sK6)))
    | ~ r2_hidden(sK4(sK6,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),k2_xboole_0(X0,sK6)) ),
    inference(instantiation,[status(thm)],[c_1028])).

cnf(c_43134,plain,
    ( ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),sK4(sK6,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))))
    | r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(k2_xboole_0(sK5,sK6)))
    | ~ r2_hidden(sK4(sK6,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),k2_xboole_0(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_43132])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1480,plain,
    ( r2_hidden(sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),k2_xboole_0(sK5,X0))
    | ~ r2_hidden(sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),sK5) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_16266,plain,
    ( r2_hidden(sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),k2_xboole_0(sK5,sK6))
    | ~ r2_hidden(sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),sK5) ),
    inference(instantiation,[status(thm)],[c_1480])).

cnf(c_1344,plain,
    ( ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))))
    | r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(X0))
    | ~ r2_hidden(sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),X0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_8922,plain,
    ( ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))))
    | r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(k2_xboole_0(sK5,sK6)))
    | ~ r2_hidden(sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),k2_xboole_0(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_1344])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2930,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(sK5,sK6),sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),k2_xboole_0(sK5,sK6))
    | r2_hidden(sK4(k2_xboole_0(sK5,sK6),sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),sK6)
    | r2_hidden(sK4(k2_xboole_0(sK5,sK6),sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),sK5) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2872,plain,
    ( ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),sK4(k2_xboole_0(sK5,sK6),sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))))
    | r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK5))
    | ~ r2_hidden(sK4(k2_xboole_0(sK5,sK6),sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),sK5) ),
    inference(instantiation,[status(thm)],[c_2870])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1067,plain,
    ( r2_hidden(sK4(sK6,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),k2_xboole_0(X0,sK6))
    | ~ r2_hidden(sK4(sK6,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),sK6) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1069,plain,
    ( r2_hidden(sK4(sK6,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),k2_xboole_0(sK5,sK6))
    | ~ r2_hidden(sK4(sK6,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),sK6) ),
    inference(instantiation,[status(thm)],[c_1067])).

cnf(c_14,plain,
    ( r2_hidden(X0,sK4(X1,X0))
    | ~ r2_hidden(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_877,plain,
    ( r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),sK4(sK6,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))))
    | ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK6)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k3_tarski(X1))
    | r2_hidden(sK4(X1,X0),X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_878,plain,
    ( ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK6))
    | r2_hidden(sK4(sK6,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),sK6) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_824,plain,
    ( r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),sK4(k2_xboole_0(sK5,sK6),sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))))
    | ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(k2_xboole_0(sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_825,plain,
    ( ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(k2_xboole_0(sK5,sK6)))
    | r2_hidden(sK4(k2_xboole_0(sK5,sK6),sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),k2_xboole_0(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | ~ r2_hidden(sK1(X0,X1,X2),X2)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_821,plain,
    ( ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(k2_xboole_0(sK5,sK6)))
    | ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK6))
    | k2_xboole_0(k3_tarski(sK5),k3_tarski(sK6)) = k3_tarski(k2_xboole_0(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_734,plain,
    ( r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))))
    | ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK5)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_735,plain,
    ( ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK5))
    | r2_hidden(sK4(sK5,sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6)))),sK5) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_4,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X2)
    | ~ r2_hidden(sK1(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_731,plain,
    ( ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(k2_xboole_0(sK5,sK6)))
    | ~ r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK5))
    | k2_xboole_0(k3_tarski(sK5),k3_tarski(sK6)) = k3_tarski(k2_xboole_0(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | r2_hidden(sK1(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_700,plain,
    ( r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(k2_xboole_0(sK5,sK6)))
    | r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK6))
    | r2_hidden(sK1(k3_tarski(sK5),k3_tarski(sK6),k3_tarski(k2_xboole_0(sK5,sK6))),k3_tarski(sK5))
    | k2_xboole_0(k3_tarski(sK5),k3_tarski(sK6)) = k3_tarski(k2_xboole_0(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_17,negated_conjecture,
    ( k2_xboole_0(k3_tarski(sK5),k3_tarski(sK6)) != k3_tarski(k2_xboole_0(sK5,sK6)) ),
    inference(cnf_transformation,[],[f45])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_47012,c_43134,c_16266,c_8922,c_2930,c_2872,c_1069,c_877,c_878,c_824,c_825,c_821,c_734,c_735,c_731,c_700,c_17])).


%------------------------------------------------------------------------------
