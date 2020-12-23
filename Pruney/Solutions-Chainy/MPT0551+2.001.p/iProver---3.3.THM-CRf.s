%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:46:35 EST 2020

% Result     : Theorem 23.79s
% Output     : CNFRefutation 23.79s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 464 expanded)
%              Number of clauses        :   47 (  95 expanded)
%              Number of leaves         :    8 ( 132 expanded)
%              Depth                    :   18
%              Number of atoms          :  350 (3158 expanded)
%              Number of equality atoms :   40 ( 398 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   15 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X5,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X8,X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f14])).

fof(f18,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK3(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,X3),X0) )
     => ( r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X2),X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X4,X3),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X3),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(X4,sK1(X0,X1,X2)),X0) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(X5,sK1(X0,X1,X2)),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(X4,sK1(X0,X1,X2)),X0) )
                | ~ r2_hidden(sK1(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK2(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK1(X0,X1,X2)),X0) )
                | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ( r2_hidden(sK3(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(sK3(X0,X1,X6),X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f15,f18,f17,f16])).

fof(f34,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f11,plain,(
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
    inference(rectify,[],[f10])).

fof(f12,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & ~ r2_hidden(sK0(X0,X1,X2),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( r2_hidden(sK0(X0,X1,X2),X1)
          | r2_hidden(sK0(X0,X1,X2),X0)
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & ~ r2_hidden(sK0(X0,X1,X2),X0) )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( r2_hidden(sK0(X0,X1,X2),X1)
            | r2_hidden(sK0(X0,X1,X2),X0)
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f12])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f45,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k2_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) != k9_relat_1(X2,k2_xboole_0(X0,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) != k9_relat_1(X2,k2_xboole_0(X0,X1))
        & v1_relat_1(X2) )
   => ( k2_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6)) != k9_relat_1(sK7,k2_xboole_0(sK5,sK6))
      & v1_relat_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( k2_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6)) != k9_relat_1(sK7,k2_xboole_0(sK5,sK6))
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f8,f24])).

fof(f43,plain,(
    k2_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6)) != k9_relat_1(sK7,k2_xboole_0(sK5,sK6)) ),
    inference(cnf_transformation,[],[f25])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f42,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f25])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f46,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f32,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f49,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f44,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f28])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_79288,plain,
    ( ~ r2_hidden(sK3(sK7,sK6,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),X0)
    | r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,X0))
    | ~ r2_hidden(k4_tarski(sK3(sK7,sK6,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK7)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_80129,plain,
    ( ~ r2_hidden(sK3(sK7,sK6,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),k2_xboole_0(X0,X1))
    | r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,k2_xboole_0(X0,X1)))
    | ~ r2_hidden(k4_tarski(sK3(sK7,sK6,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK7)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_79288])).

cnf(c_80170,plain,
    ( ~ r2_hidden(sK3(sK7,sK6,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),k2_xboole_0(sK5,sK6))
    | r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))
    | ~ r2_hidden(k4_tarski(sK3(sK7,sK6,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK7)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_80129])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_73791,plain,
    ( ~ r2_hidden(sK3(sK7,sK5,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),X0)
    | r2_hidden(sK3(sK7,sK5,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),k2_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_73909,plain,
    ( r2_hidden(sK3(sK7,sK5,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),k2_xboole_0(sK5,X0))
    | ~ r2_hidden(sK3(sK7,sK5,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK5) ),
    inference(instantiation,[status(thm)],[c_73791])).

cnf(c_78478,plain,
    ( r2_hidden(sK3(sK7,sK5,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),k2_xboole_0(sK5,sK6))
    | ~ r2_hidden(sK3(sK7,sK5,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK5) ),
    inference(instantiation,[status(thm)],[c_73909])).

cnf(c_73422,plain,
    ( ~ r2_hidden(sK3(sK7,sK5,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),X0)
    | r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,X0))
    | ~ r2_hidden(k4_tarski(sK3(sK7,sK5,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK7)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_73765,plain,
    ( ~ r2_hidden(sK3(sK7,sK5,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),k2_xboole_0(X0,X1))
    | r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,k2_xboole_0(X0,X1)))
    | ~ r2_hidden(k4_tarski(sK3(sK7,sK5,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK7)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_73422])).

cnf(c_73972,plain,
    ( ~ r2_hidden(sK3(sK7,sK5,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),k2_xboole_0(sK5,X0))
    | r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,k2_xboole_0(sK5,X0)))
    | ~ r2_hidden(k4_tarski(sK3(sK7,sK5,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK7)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_73765])).

cnf(c_78460,plain,
    ( ~ r2_hidden(sK3(sK7,sK5,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),k2_xboole_0(sK5,sK6))
    | r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))
    | ~ r2_hidden(k4_tarski(sK3(sK7,sK5,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK7)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_73972])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_61468,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(arAF0_sK3_0_1_2(X1,X2),X2)
    | ~ v1_relat_1(X1)
    | ~ iProver_ARSWP_42 ),
    inference(arg_filter_abstr,[status(unp)],[c_10])).

cnf(c_16,negated_conjecture,
    ( k2_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6)) != k9_relat_1(sK7,k2_xboole_0(sK5,sK6)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_62127,plain,
    ( r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))
    | r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK6))
    | r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK5)) ),
    inference(resolution,[status(thm)],[c_16,c_2])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_18769,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,k2_xboole_0(X2,X3)))
    | r2_hidden(sK3(X1,k2_xboole_0(X2,X3),X0),X3)
    | r2_hidden(sK3(X1,k2_xboole_0(X2,X3),X0),X2)
    | ~ v1_relat_1(X1) ),
    inference(resolution,[status(thm)],[c_10,c_5])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK3(X1,X2,X0),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_18984,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(X0,k9_relat_1(X1,X3))
    | ~ r2_hidden(sK3(X1,X2,X0),X3)
    | ~ v1_relat_1(X1) ),
    inference(resolution,[status(thm)],[c_9,c_11])).

cnf(c_22434,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ r2_hidden(X0,k9_relat_1(X1,k2_xboole_0(X3,X2)))
    | r2_hidden(sK3(X1,k2_xboole_0(X3,X2),X0),X3)
    | ~ v1_relat_1(X1) ),
    inference(resolution,[status(thm)],[c_18769,c_18984])).

cnf(c_27776,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(X0,k9_relat_1(X1,X3))
    | ~ r2_hidden(X0,k9_relat_1(X1,k2_xboole_0(X3,X2)))
    | ~ v1_relat_1(X1) ),
    inference(resolution,[status(thm)],[c_22434,c_18984])).

cnf(c_18547,plain,
    ( r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))
    | r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK6))
    | r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK5)) ),
    inference(resolution,[status(thm)],[c_16,c_2])).

cnf(c_29034,plain,
    ( r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK6))
    | r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK5))
    | ~ v1_relat_1(sK7) ),
    inference(resolution,[status(thm)],[c_27776,c_18547])).

cnf(c_62130,plain,
    ( r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK6))
    | r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_62127,c_17,c_29034])).

cnf(c_62725,plain,
    ( r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK5))
    | r2_hidden(arAF0_sK3_0_1_2(sK7,sK6),sK6)
    | ~ v1_relat_1(sK7)
    | ~ iProver_ARSWP_42 ),
    inference(resolution,[status(thm)],[c_61468,c_62130])).

cnf(c_62973,plain,
    ( r2_hidden(arAF0_sK3_0_1_2(sK7,sK6),sK6)
    | r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK5))
    | ~ iProver_ARSWP_42 ),
    inference(global_propositional_subsumption,[status(thm)],[c_62725,c_17])).

cnf(c_62974,plain,
    ( r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK5))
    | r2_hidden(arAF0_sK3_0_1_2(sK7,sK6),sK6)
    | ~ iProver_ARSWP_42 ),
    inference(renaming,[status(thm)],[c_62973])).

cnf(c_63979,plain,
    ( ~ r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))
    | r2_hidden(arAF0_sK3_0_1_2(sK7,sK6),sK6)
    | ~ iProver_ARSWP_42
    | k2_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6)) = k9_relat_1(sK7,k2_xboole_0(sK5,sK6)) ),
    inference(resolution,[status(thm)],[c_1,c_62974])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_775,plain,
    ( ~ r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))
    | ~ r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK6))
    | k2_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6)) = k9_relat_1(sK7,k2_xboole_0(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_18105,plain,
    ( ~ r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))
    | ~ r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK5))
    | k2_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6)) = k9_relat_1(sK7,k2_xboole_0(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_64501,plain,
    ( ~ r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_63979,c_17,c_16,c_775,c_18105,c_29034])).

cnf(c_19226,plain,
    ( ~ r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(X0,X1))
    | r2_hidden(k4_tarski(sK3(X0,X1,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),X0)
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_29196,plain,
    ( ~ r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK5))
    | r2_hidden(k4_tarski(sK3(sK7,sK5,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK7)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_19226])).

cnf(c_29091,plain,
    ( r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK5))
    | r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_29034,c_17])).

cnf(c_29092,plain,
    ( r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK6))
    | r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK5)) ),
    inference(renaming,[status(thm)],[c_29091])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_18432,plain,
    ( ~ r2_hidden(sK3(sK7,X0,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),X1)
    | r2_hidden(sK3(sK7,X0,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),k2_xboole_0(sK5,X1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_27386,plain,
    ( r2_hidden(sK3(sK7,sK6,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),k2_xboole_0(sK5,sK6))
    | ~ r2_hidden(sK3(sK7,sK6,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK6) ),
    inference(instantiation,[status(thm)],[c_18432])).

cnf(c_18826,plain,
    ( ~ r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK6))
    | r2_hidden(k4_tarski(sK3(sK7,sK6,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK7)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_18276,plain,
    ( r2_hidden(sK3(sK7,sK5,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK5)
    | ~ r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK5))
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_18190,plain,
    ( r2_hidden(sK3(sK7,sK6,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK6)
    | ~ r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK6))
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_80170,c_78478,c_78460,c_64501,c_29196,c_29092,c_27386,c_18826,c_18276,c_18190,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:55:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 23.79/3.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.79/3.50  
% 23.79/3.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.79/3.50  
% 23.79/3.50  ------  iProver source info
% 23.79/3.50  
% 23.79/3.50  git: date: 2020-06-30 10:37:57 +0100
% 23.79/3.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.79/3.50  git: non_committed_changes: false
% 23.79/3.50  git: last_make_outside_of_git: false
% 23.79/3.50  
% 23.79/3.50  ------ 
% 23.79/3.50  ------ Parsing...
% 23.79/3.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.79/3.50  
% 23.79/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 23.79/3.50  
% 23.79/3.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.79/3.50  
% 23.79/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.79/3.50  ------ Proving...
% 23.79/3.50  ------ Problem Properties 
% 23.79/3.50  
% 23.79/3.50  
% 23.79/3.50  clauses                                 17
% 23.79/3.50  conjectures                             2
% 23.79/3.50  EPR                                     1
% 23.79/3.50  Horn                                    13
% 23.79/3.50  unary                                   2
% 23.79/3.50  binary                                  2
% 23.79/3.50  lits                                    51
% 23.79/3.50  lits eq                                 7
% 23.79/3.50  fd_pure                                 0
% 23.79/3.50  fd_pseudo                               0
% 23.79/3.50  fd_cond                                 0
% 23.79/3.50  fd_pseudo_cond                          6
% 23.79/3.50  AC symbols                              0
% 23.79/3.50  
% 23.79/3.50  ------ Input Options Time Limit: Unbounded
% 23.79/3.50  
% 23.79/3.50  
% 23.79/3.50  
% 23.79/3.50  
% 23.79/3.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 23.79/3.50  Current options:
% 23.79/3.50  ------ 
% 23.79/3.50  
% 23.79/3.50  
% 23.79/3.50  
% 23.79/3.50  
% 23.79/3.50  ------ Proving...
% 23.79/3.50  
% 23.79/3.50  
% 23.79/3.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.79/3.50  
% 23.79/3.50  ------ Proving...
% 23.79/3.50  
% 23.79/3.50  
% 23.79/3.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.79/3.50  
% 23.79/3.50  ------ Proving...
% 23.79/3.50  
% 23.79/3.50  
% 23.79/3.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.79/3.50  
% 23.79/3.50  ------ Proving...
% 23.79/3.50  
% 23.79/3.50  
% 23.79/3.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.79/3.50  
% 23.79/3.50  ------ Proving...
% 23.79/3.50  
% 23.79/3.50  
% 23.79/3.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.79/3.50  
% 23.79/3.50  ------ Proving...
% 23.79/3.50  
% 23.79/3.50  
% 23.79/3.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.79/3.50  
% 23.79/3.50  ------ Proving...
% 23.79/3.50  
% 23.79/3.50  
% 23.79/3.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.79/3.50  
% 23.79/3.50  ------ Proving...
% 23.79/3.50  
% 23.79/3.50  
% 23.79/3.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.79/3.50  
% 23.79/3.50  ------ Proving...
% 23.79/3.50  
% 23.79/3.50  
% 23.79/3.50  % SZS status Theorem for theBenchmark.p
% 23.79/3.50  
% 23.79/3.50  % SZS output start CNFRefutation for theBenchmark.p
% 23.79/3.51  
% 23.79/3.51  fof(f2,axiom,(
% 23.79/3.51    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))))),
% 23.79/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.79/3.51  
% 23.79/3.51  fof(f6,plain,(
% 23.79/3.51    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))) | ~v1_relat_1(X0))),
% 23.79/3.51    inference(ennf_transformation,[],[f2])).
% 23.79/3.51  
% 23.79/3.51  fof(f14,plain,(
% 23.79/3.51    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 23.79/3.51    inference(nnf_transformation,[],[f6])).
% 23.79/3.51  
% 23.79/3.51  fof(f15,plain,(
% 23.79/3.51    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 23.79/3.51    inference(rectify,[],[f14])).
% 23.79/3.51  
% 23.79/3.51  fof(f18,plain,(
% 23.79/3.51    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) => (r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X6),X6),X0)))),
% 23.79/3.51    introduced(choice_axiom,[])).
% 23.79/3.51  
% 23.79/3.51  fof(f17,plain,(
% 23.79/3.51    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) => (r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X3),X0)))) )),
% 23.79/3.51    introduced(choice_axiom,[])).
% 23.79/3.51  
% 23.79/3.51  fof(f16,plain,(
% 23.79/3.51    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK1(X0,X1,X2)),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,sK1(X0,X1,X2)),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 23.79/3.51    introduced(choice_axiom,[])).
% 23.79/3.51  
% 23.79/3.51  fof(f19,plain,(
% 23.79/3.51    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK1(X0,X1,X2)),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK1(X0,X1,X2)),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & ((r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X6),X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 23.79/3.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f15,f18,f17,f16])).
% 23.79/3.51  
% 23.79/3.51  fof(f34,plain,(
% 23.79/3.51    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0) | k9_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 23.79/3.51    inference(cnf_transformation,[],[f19])).
% 23.79/3.51  
% 23.79/3.51  fof(f47,plain,(
% 23.79/3.51    ( ! [X6,X0,X7,X1] : (r2_hidden(X6,k9_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0) | ~v1_relat_1(X0)) )),
% 23.79/3.51    inference(equality_resolution,[],[f34])).
% 23.79/3.51  
% 23.79/3.51  fof(f1,axiom,(
% 23.79/3.51    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 23.79/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.79/3.51  
% 23.79/3.51  fof(f9,plain,(
% 23.79/3.51    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 23.79/3.51    inference(nnf_transformation,[],[f1])).
% 23.79/3.51  
% 23.79/3.51  fof(f10,plain,(
% 23.79/3.51    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 23.79/3.51    inference(flattening,[],[f9])).
% 23.79/3.51  
% 23.79/3.51  fof(f11,plain,(
% 23.79/3.51    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 23.79/3.51    inference(rectify,[],[f10])).
% 23.79/3.51  
% 23.79/3.51  fof(f12,plain,(
% 23.79/3.51    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 23.79/3.51    introduced(choice_axiom,[])).
% 23.79/3.51  
% 23.79/3.51  fof(f13,plain,(
% 23.79/3.51    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 23.79/3.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f12])).
% 23.79/3.51  
% 23.79/3.51  fof(f27,plain,(
% 23.79/3.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 23.79/3.51    inference(cnf_transformation,[],[f13])).
% 23.79/3.51  
% 23.79/3.51  fof(f45,plain,(
% 23.79/3.51    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 23.79/3.51    inference(equality_resolution,[],[f27])).
% 23.79/3.51  
% 23.79/3.51  fof(f30,plain,(
% 23.79/3.51    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 23.79/3.51    inference(cnf_transformation,[],[f13])).
% 23.79/3.51  
% 23.79/3.51  fof(f33,plain,(
% 23.79/3.51    ( ! [X6,X2,X0,X1] : (r2_hidden(sK3(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 23.79/3.51    inference(cnf_transformation,[],[f19])).
% 23.79/3.51  
% 23.79/3.51  fof(f48,plain,(
% 23.79/3.51    ( ! [X6,X0,X1] : (r2_hidden(sK3(X0,X1,X6),X1) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 23.79/3.51    inference(equality_resolution,[],[f33])).
% 23.79/3.51  
% 23.79/3.51  fof(f4,conjecture,(
% 23.79/3.51    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k2_xboole_0(X0,X1)))),
% 23.79/3.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.79/3.51  
% 23.79/3.51  fof(f5,negated_conjecture,(
% 23.79/3.51    ~! [X0,X1,X2] : (v1_relat_1(X2) => k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k2_xboole_0(X0,X1)))),
% 23.79/3.51    inference(negated_conjecture,[],[f4])).
% 23.79/3.51  
% 23.79/3.51  fof(f8,plain,(
% 23.79/3.51    ? [X0,X1,X2] : (k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) != k9_relat_1(X2,k2_xboole_0(X0,X1)) & v1_relat_1(X2))),
% 23.79/3.51    inference(ennf_transformation,[],[f5])).
% 23.79/3.51  
% 23.79/3.51  fof(f24,plain,(
% 23.79/3.51    ? [X0,X1,X2] : (k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) != k9_relat_1(X2,k2_xboole_0(X0,X1)) & v1_relat_1(X2)) => (k2_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6)) != k9_relat_1(sK7,k2_xboole_0(sK5,sK6)) & v1_relat_1(sK7))),
% 23.79/3.51    introduced(choice_axiom,[])).
% 23.79/3.51  
% 23.79/3.51  fof(f25,plain,(
% 23.79/3.51    k2_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6)) != k9_relat_1(sK7,k2_xboole_0(sK5,sK6)) & v1_relat_1(sK7)),
% 23.79/3.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f8,f24])).
% 23.79/3.51  
% 23.79/3.51  fof(f43,plain,(
% 23.79/3.51    k2_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6)) != k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),
% 23.79/3.51    inference(cnf_transformation,[],[f25])).
% 23.79/3.51  
% 23.79/3.51  fof(f29,plain,(
% 23.79/3.51    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 23.79/3.51    inference(cnf_transformation,[],[f13])).
% 23.79/3.51  
% 23.79/3.51  fof(f42,plain,(
% 23.79/3.51    v1_relat_1(sK7)),
% 23.79/3.51    inference(cnf_transformation,[],[f25])).
% 23.79/3.51  
% 23.79/3.51  fof(f26,plain,(
% 23.79/3.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 23.79/3.51    inference(cnf_transformation,[],[f13])).
% 23.79/3.51  
% 23.79/3.51  fof(f46,plain,(
% 23.79/3.51    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 23.79/3.51    inference(equality_resolution,[],[f26])).
% 23.79/3.51  
% 23.79/3.51  fof(f32,plain,(
% 23.79/3.51    ( ! [X6,X2,X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1,X6),X6),X0) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 23.79/3.51    inference(cnf_transformation,[],[f19])).
% 23.79/3.51  
% 23.79/3.51  fof(f49,plain,(
% 23.79/3.51    ( ! [X6,X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1,X6),X6),X0) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 23.79/3.51    inference(equality_resolution,[],[f32])).
% 23.79/3.51  
% 23.79/3.51  fof(f31,plain,(
% 23.79/3.51    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 23.79/3.51    inference(cnf_transformation,[],[f13])).
% 23.79/3.51  
% 23.79/3.51  fof(f28,plain,(
% 23.79/3.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 23.79/3.51    inference(cnf_transformation,[],[f13])).
% 23.79/3.51  
% 23.79/3.51  fof(f44,plain,(
% 23.79/3.51    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 23.79/3.51    inference(equality_resolution,[],[f28])).
% 23.79/3.51  
% 23.79/3.51  cnf(c_9,plain,
% 23.79/3.51      ( ~ r2_hidden(X0,X1)
% 23.79/3.51      | r2_hidden(X2,k9_relat_1(X3,X1))
% 23.79/3.51      | ~ r2_hidden(k4_tarski(X0,X2),X3)
% 23.79/3.51      | ~ v1_relat_1(X3) ),
% 23.79/3.51      inference(cnf_transformation,[],[f47]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_79288,plain,
% 23.79/3.51      ( ~ r2_hidden(sK3(sK7,sK6,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),X0)
% 23.79/3.51      | r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,X0))
% 23.79/3.51      | ~ r2_hidden(k4_tarski(sK3(sK7,sK6,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK7)
% 23.79/3.51      | ~ v1_relat_1(sK7) ),
% 23.79/3.51      inference(instantiation,[status(thm)],[c_9]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_80129,plain,
% 23.79/3.51      ( ~ r2_hidden(sK3(sK7,sK6,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),k2_xboole_0(X0,X1))
% 23.79/3.51      | r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,k2_xboole_0(X0,X1)))
% 23.79/3.51      | ~ r2_hidden(k4_tarski(sK3(sK7,sK6,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK7)
% 23.79/3.51      | ~ v1_relat_1(sK7) ),
% 23.79/3.51      inference(instantiation,[status(thm)],[c_79288]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_80170,plain,
% 23.79/3.51      ( ~ r2_hidden(sK3(sK7,sK6,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),k2_xboole_0(sK5,sK6))
% 23.79/3.51      | r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))
% 23.79/3.51      | ~ r2_hidden(k4_tarski(sK3(sK7,sK6,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK7)
% 23.79/3.51      | ~ v1_relat_1(sK7) ),
% 23.79/3.51      inference(instantiation,[status(thm)],[c_80129]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_4,plain,
% 23.79/3.51      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
% 23.79/3.51      inference(cnf_transformation,[],[f45]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_73791,plain,
% 23.79/3.51      ( ~ r2_hidden(sK3(sK7,sK5,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),X0)
% 23.79/3.51      | r2_hidden(sK3(sK7,sK5,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),k2_xboole_0(X0,X1)) ),
% 23.79/3.51      inference(instantiation,[status(thm)],[c_4]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_73909,plain,
% 23.79/3.51      ( r2_hidden(sK3(sK7,sK5,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),k2_xboole_0(sK5,X0))
% 23.79/3.51      | ~ r2_hidden(sK3(sK7,sK5,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK5) ),
% 23.79/3.51      inference(instantiation,[status(thm)],[c_73791]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_78478,plain,
% 23.79/3.51      ( r2_hidden(sK3(sK7,sK5,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),k2_xboole_0(sK5,sK6))
% 23.79/3.51      | ~ r2_hidden(sK3(sK7,sK5,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK5) ),
% 23.79/3.51      inference(instantiation,[status(thm)],[c_73909]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_73422,plain,
% 23.79/3.51      ( ~ r2_hidden(sK3(sK7,sK5,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),X0)
% 23.79/3.51      | r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,X0))
% 23.79/3.51      | ~ r2_hidden(k4_tarski(sK3(sK7,sK5,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK7)
% 23.79/3.51      | ~ v1_relat_1(sK7) ),
% 23.79/3.51      inference(instantiation,[status(thm)],[c_9]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_73765,plain,
% 23.79/3.51      ( ~ r2_hidden(sK3(sK7,sK5,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),k2_xboole_0(X0,X1))
% 23.79/3.51      | r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,k2_xboole_0(X0,X1)))
% 23.79/3.51      | ~ r2_hidden(k4_tarski(sK3(sK7,sK5,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK7)
% 23.79/3.51      | ~ v1_relat_1(sK7) ),
% 23.79/3.51      inference(instantiation,[status(thm)],[c_73422]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_73972,plain,
% 23.79/3.51      ( ~ r2_hidden(sK3(sK7,sK5,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),k2_xboole_0(sK5,X0))
% 23.79/3.51      | r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,k2_xboole_0(sK5,X0)))
% 23.79/3.51      | ~ r2_hidden(k4_tarski(sK3(sK7,sK5,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK7)
% 23.79/3.51      | ~ v1_relat_1(sK7) ),
% 23.79/3.51      inference(instantiation,[status(thm)],[c_73765]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_78460,plain,
% 23.79/3.51      ( ~ r2_hidden(sK3(sK7,sK5,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),k2_xboole_0(sK5,sK6))
% 23.79/3.51      | r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))
% 23.79/3.51      | ~ r2_hidden(k4_tarski(sK3(sK7,sK5,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK7)
% 23.79/3.51      | ~ v1_relat_1(sK7) ),
% 23.79/3.51      inference(instantiation,[status(thm)],[c_73972]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_1,plain,
% 23.79/3.51      ( ~ r2_hidden(sK0(X0,X1,X2),X2)
% 23.79/3.51      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 23.79/3.51      | k2_xboole_0(X0,X1) = X2 ),
% 23.79/3.51      inference(cnf_transformation,[],[f30]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_10,plain,
% 23.79/3.51      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 23.79/3.51      | r2_hidden(sK3(X1,X2,X0),X2)
% 23.79/3.51      | ~ v1_relat_1(X1) ),
% 23.79/3.51      inference(cnf_transformation,[],[f48]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_61468,plain,
% 23.79/3.51      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 23.79/3.51      | r2_hidden(arAF0_sK3_0_1_2(X1,X2),X2)
% 23.79/3.51      | ~ v1_relat_1(X1)
% 23.79/3.51      | ~ iProver_ARSWP_42 ),
% 23.79/3.51      inference(arg_filter_abstr,[status(unp)],[c_10]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_16,negated_conjecture,
% 23.79/3.51      ( k2_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6)) != k9_relat_1(sK7,k2_xboole_0(sK5,sK6)) ),
% 23.79/3.51      inference(cnf_transformation,[],[f43]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_2,plain,
% 23.79/3.51      ( r2_hidden(sK0(X0,X1,X2),X1)
% 23.79/3.51      | r2_hidden(sK0(X0,X1,X2),X2)
% 23.79/3.51      | r2_hidden(sK0(X0,X1,X2),X0)
% 23.79/3.51      | k2_xboole_0(X0,X1) = X2 ),
% 23.79/3.51      inference(cnf_transformation,[],[f29]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_62127,plain,
% 23.79/3.51      ( r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))
% 23.79/3.51      | r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK6))
% 23.79/3.51      | r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK5)) ),
% 23.79/3.51      inference(resolution,[status(thm)],[c_16,c_2]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_17,negated_conjecture,
% 23.79/3.51      ( v1_relat_1(sK7) ),
% 23.79/3.51      inference(cnf_transformation,[],[f42]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_5,plain,
% 23.79/3.51      ( r2_hidden(X0,X1)
% 23.79/3.51      | r2_hidden(X0,X2)
% 23.79/3.51      | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 23.79/3.51      inference(cnf_transformation,[],[f46]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_18769,plain,
% 23.79/3.51      ( ~ r2_hidden(X0,k9_relat_1(X1,k2_xboole_0(X2,X3)))
% 23.79/3.51      | r2_hidden(sK3(X1,k2_xboole_0(X2,X3),X0),X3)
% 23.79/3.51      | r2_hidden(sK3(X1,k2_xboole_0(X2,X3),X0),X2)
% 23.79/3.51      | ~ v1_relat_1(X1) ),
% 23.79/3.51      inference(resolution,[status(thm)],[c_10,c_5]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_11,plain,
% 23.79/3.51      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 23.79/3.51      | r2_hidden(k4_tarski(sK3(X1,X2,X0),X0),X1)
% 23.79/3.51      | ~ v1_relat_1(X1) ),
% 23.79/3.51      inference(cnf_transformation,[],[f49]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_18984,plain,
% 23.79/3.51      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 23.79/3.51      | r2_hidden(X0,k9_relat_1(X1,X3))
% 23.79/3.51      | ~ r2_hidden(sK3(X1,X2,X0),X3)
% 23.79/3.51      | ~ v1_relat_1(X1) ),
% 23.79/3.51      inference(resolution,[status(thm)],[c_9,c_11]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_22434,plain,
% 23.79/3.51      ( r2_hidden(X0,k9_relat_1(X1,X2))
% 23.79/3.51      | ~ r2_hidden(X0,k9_relat_1(X1,k2_xboole_0(X3,X2)))
% 23.79/3.51      | r2_hidden(sK3(X1,k2_xboole_0(X3,X2),X0),X3)
% 23.79/3.51      | ~ v1_relat_1(X1) ),
% 23.79/3.51      inference(resolution,[status(thm)],[c_18769,c_18984]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_27776,plain,
% 23.79/3.51      ( r2_hidden(X0,k9_relat_1(X1,X2))
% 23.79/3.51      | r2_hidden(X0,k9_relat_1(X1,X3))
% 23.79/3.51      | ~ r2_hidden(X0,k9_relat_1(X1,k2_xboole_0(X3,X2)))
% 23.79/3.51      | ~ v1_relat_1(X1) ),
% 23.79/3.51      inference(resolution,[status(thm)],[c_22434,c_18984]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_18547,plain,
% 23.79/3.51      ( r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))
% 23.79/3.51      | r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK6))
% 23.79/3.51      | r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK5)) ),
% 23.79/3.51      inference(resolution,[status(thm)],[c_16,c_2]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_29034,plain,
% 23.79/3.51      ( r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK6))
% 23.79/3.51      | r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK5))
% 23.79/3.51      | ~ v1_relat_1(sK7) ),
% 23.79/3.51      inference(resolution,[status(thm)],[c_27776,c_18547]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_62130,plain,
% 23.79/3.51      ( r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK6))
% 23.79/3.51      | r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK5)) ),
% 23.79/3.51      inference(global_propositional_subsumption,
% 23.79/3.51                [status(thm)],
% 23.79/3.51                [c_62127,c_17,c_29034]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_62725,plain,
% 23.79/3.51      ( r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK5))
% 23.79/3.51      | r2_hidden(arAF0_sK3_0_1_2(sK7,sK6),sK6)
% 23.79/3.51      | ~ v1_relat_1(sK7)
% 23.79/3.51      | ~ iProver_ARSWP_42 ),
% 23.79/3.51      inference(resolution,[status(thm)],[c_61468,c_62130]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_62973,plain,
% 23.79/3.51      ( r2_hidden(arAF0_sK3_0_1_2(sK7,sK6),sK6)
% 23.79/3.51      | r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK5))
% 23.79/3.51      | ~ iProver_ARSWP_42 ),
% 23.79/3.51      inference(global_propositional_subsumption,
% 23.79/3.51                [status(thm)],
% 23.79/3.51                [c_62725,c_17]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_62974,plain,
% 23.79/3.51      ( r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK5))
% 23.79/3.51      | r2_hidden(arAF0_sK3_0_1_2(sK7,sK6),sK6)
% 23.79/3.51      | ~ iProver_ARSWP_42 ),
% 23.79/3.51      inference(renaming,[status(thm)],[c_62973]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_63979,plain,
% 23.79/3.51      ( ~ r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))
% 23.79/3.51      | r2_hidden(arAF0_sK3_0_1_2(sK7,sK6),sK6)
% 23.79/3.51      | ~ iProver_ARSWP_42
% 23.79/3.51      | k2_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6)) = k9_relat_1(sK7,k2_xboole_0(sK5,sK6)) ),
% 23.79/3.51      inference(resolution,[status(thm)],[c_1,c_62974]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_0,plain,
% 23.79/3.51      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 23.79/3.51      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 23.79/3.51      | k2_xboole_0(X0,X1) = X2 ),
% 23.79/3.51      inference(cnf_transformation,[],[f31]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_775,plain,
% 23.79/3.51      ( ~ r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))
% 23.79/3.51      | ~ r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK6))
% 23.79/3.51      | k2_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6)) = k9_relat_1(sK7,k2_xboole_0(sK5,sK6)) ),
% 23.79/3.51      inference(instantiation,[status(thm)],[c_0]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_18105,plain,
% 23.79/3.51      ( ~ r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))
% 23.79/3.51      | ~ r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK5))
% 23.79/3.51      | k2_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6)) = k9_relat_1(sK7,k2_xboole_0(sK5,sK6)) ),
% 23.79/3.51      inference(instantiation,[status(thm)],[c_1]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_64501,plain,
% 23.79/3.51      ( ~ r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))) ),
% 23.79/3.51      inference(global_propositional_subsumption,
% 23.79/3.51                [status(thm)],
% 23.79/3.51                [c_63979,c_17,c_16,c_775,c_18105,c_29034]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_19226,plain,
% 23.79/3.51      ( ~ r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(X0,X1))
% 23.79/3.51      | r2_hidden(k4_tarski(sK3(X0,X1,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),X0)
% 23.79/3.51      | ~ v1_relat_1(X0) ),
% 23.79/3.51      inference(instantiation,[status(thm)],[c_11]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_29196,plain,
% 23.79/3.51      ( ~ r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK5))
% 23.79/3.51      | r2_hidden(k4_tarski(sK3(sK7,sK5,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK7)
% 23.79/3.51      | ~ v1_relat_1(sK7) ),
% 23.79/3.51      inference(instantiation,[status(thm)],[c_19226]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_29091,plain,
% 23.79/3.51      ( r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK5))
% 23.79/3.51      | r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK6)) ),
% 23.79/3.51      inference(global_propositional_subsumption,
% 23.79/3.51                [status(thm)],
% 23.79/3.51                [c_29034,c_17]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_29092,plain,
% 23.79/3.51      ( r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK6))
% 23.79/3.51      | r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK5)) ),
% 23.79/3.51      inference(renaming,[status(thm)],[c_29091]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_3,plain,
% 23.79/3.51      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 23.79/3.51      inference(cnf_transformation,[],[f44]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_18432,plain,
% 23.79/3.51      ( ~ r2_hidden(sK3(sK7,X0,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),X1)
% 23.79/3.51      | r2_hidden(sK3(sK7,X0,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),k2_xboole_0(sK5,X1)) ),
% 23.79/3.51      inference(instantiation,[status(thm)],[c_3]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_27386,plain,
% 23.79/3.51      ( r2_hidden(sK3(sK7,sK6,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),k2_xboole_0(sK5,sK6))
% 23.79/3.51      | ~ r2_hidden(sK3(sK7,sK6,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK6) ),
% 23.79/3.51      inference(instantiation,[status(thm)],[c_18432]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_18826,plain,
% 23.79/3.51      ( ~ r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK6))
% 23.79/3.51      | r2_hidden(k4_tarski(sK3(sK7,sK6,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK7)
% 23.79/3.51      | ~ v1_relat_1(sK7) ),
% 23.79/3.51      inference(instantiation,[status(thm)],[c_11]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_18276,plain,
% 23.79/3.51      ( r2_hidden(sK3(sK7,sK5,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK5)
% 23.79/3.51      | ~ r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK5))
% 23.79/3.51      | ~ v1_relat_1(sK7) ),
% 23.79/3.51      inference(instantiation,[status(thm)],[c_10]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(c_18190,plain,
% 23.79/3.51      ( r2_hidden(sK3(sK7,sK6,sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6)))),sK6)
% 23.79/3.51      | ~ r2_hidden(sK0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6),k9_relat_1(sK7,k2_xboole_0(sK5,sK6))),k9_relat_1(sK7,sK6))
% 23.79/3.51      | ~ v1_relat_1(sK7) ),
% 23.79/3.51      inference(instantiation,[status(thm)],[c_10]) ).
% 23.79/3.51  
% 23.79/3.51  cnf(contradiction,plain,
% 23.79/3.51      ( $false ),
% 23.79/3.51      inference(minisat,
% 23.79/3.51                [status(thm)],
% 23.79/3.51                [c_80170,c_78478,c_78460,c_64501,c_29196,c_29092,c_27386,
% 23.79/3.51                 c_18826,c_18276,c_18190,c_17]) ).
% 23.79/3.51  
% 23.79/3.51  
% 23.79/3.51  % SZS output end CNFRefutation for theBenchmark.p
% 23.79/3.51  
% 23.79/3.51  ------                               Statistics
% 23.79/3.51  
% 23.79/3.51  ------ Selected
% 23.79/3.51  
% 23.79/3.51  total_time:                             2.954
% 23.79/3.51  
%------------------------------------------------------------------------------
