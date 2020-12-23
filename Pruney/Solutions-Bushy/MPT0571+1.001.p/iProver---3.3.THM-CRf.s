%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0571+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:38 EST 2020

% Result     : Theorem 55.19s
% Output     : CNFRefutation 55.19s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 301 expanded)
%              Number of clauses        :   66 (  91 expanded)
%              Number of leaves         :    8 (  74 expanded)
%              Depth                    :   13
%              Number of atoms          :  396 (1666 expanded)
%              Number of equality atoms :   96 ( 288 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   15 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X3,X5),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X6,X8),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f7])).

fof(f11,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK2(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X3,X5),X0) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X3,sK1(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X3,X5),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK0(X0,X1,X2),X5),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK0(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK1(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0) )
                | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK2(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f11,f10,f9])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),X4),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) != k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( k10_relat_1(X2,k2_xboole_0(X0,X1)) != k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & v1_relat_1(X2) )
   => ( k10_relat_1(sK6,k2_xboole_0(sK4,sK5)) != k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( k10_relat_1(sK6,k2_xboole_0(sK4,sK5)) != k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f6,f18])).

fof(f32,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
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

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & ~ r2_hidden(sK3(X0,X1,X2),X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( r2_hidden(sK3(X0,X1,X2),X1)
          | r2_hidden(sK3(X0,X1,X2),X0)
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & ~ r2_hidden(sK3(X0,X1,X2),X0) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( r2_hidden(sK3(X0,X1,X2),X1)
            | r2_hidden(sK3(X0,X1,X2),X0)
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f28])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f22,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f22])).

fof(f21,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f21])).

fof(f20,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f20])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f39,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f33,plain,(
    k10_relat_1(sK6,k2_xboole_0(sK4,sK5)) != k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(X2,X1,X3),X3)
    | ~ r2_hidden(k4_tarski(sK0(X2,X1,X3),X0),X2)
    | ~ v1_relat_1(X2)
    | k10_relat_1(X2,X1) = X3 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_178,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(X2,X1,X3),X3)
    | ~ r2_hidden(k4_tarski(sK0(X2,X1,X3),X0),X2)
    | k10_relat_1(X2,X1) = X3
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_13])).

cnf(c_179,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(sK6,X1,X2),X2)
    | ~ r2_hidden(k4_tarski(sK0(sK6,X1,X2),X0),sK6)
    | k10_relat_1(sK6,X1) = X2 ),
    inference(unflattening,[status(thm)],[c_178])).

cnf(c_605,plain,
    ( ~ r2_hidden(X0,k2_xboole_0(sK4,sK5))
    | ~ r2_hidden(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)))
    | ~ r2_hidden(k4_tarski(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),X0),sK6)
    | k10_relat_1(sK6,k2_xboole_0(sK4,sK5)) = k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_179])).

cnf(c_108780,plain,
    ( ~ r2_hidden(sK2(sK6,sK4,sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)))),k2_xboole_0(sK4,sK5))
    | ~ r2_hidden(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)))
    | ~ r2_hidden(k4_tarski(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),sK2(sK6,sK4,sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))))),sK6)
    | k10_relat_1(sK6,k2_xboole_0(sK4,sK5)) = k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_605])).

cnf(c_108781,plain,
    ( k10_relat_1(sK6,k2_xboole_0(sK4,sK5)) = k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))
    | r2_hidden(sK2(sK6,sK4,sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)))),k2_xboole_0(sK4,sK5)) != iProver_top
    | r2_hidden(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))) != iProver_top
    | r2_hidden(k4_tarski(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),sK2(sK6,sK4,sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))))),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_108780])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_653,plain,
    ( r2_hidden(X0,k2_xboole_0(X1,k10_relat_1(sK6,X2)))
    | ~ r2_hidden(X0,k10_relat_1(sK6,X2)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_858,plain,
    ( r2_hidden(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k2_xboole_0(X0,k10_relat_1(sK6,sK5)))
    | ~ r2_hidden(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k10_relat_1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_653])).

cnf(c_47922,plain,
    ( r2_hidden(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)))
    | ~ r2_hidden(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k10_relat_1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_858])).

cnf(c_47923,plain,
    ( r2_hidden(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))) = iProver_top
    | r2_hidden(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k10_relat_1(sK6,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47922])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_658,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,k10_relat_1(sK6,X2))) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1675,plain,
    ( r2_hidden(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,X0)))
    | ~ r2_hidden(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k10_relat_1(sK6,sK4)) ),
    inference(instantiation,[status(thm)],[c_658])).

cnf(c_41590,plain,
    ( r2_hidden(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)))
    | ~ r2_hidden(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k10_relat_1(sK6,sK4)) ),
    inference(instantiation,[status(thm)],[c_1675])).

cnf(c_41591,plain,
    ( r2_hidden(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))) = iProver_top
    | r2_hidden(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k10_relat_1(sK6,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41590])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_196,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | sK6 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_13])).

cnf(c_197,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK6,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),sK6) ),
    inference(unflattening,[status(thm)],[c_196])).

cnf(c_3222,plain,
    ( r2_hidden(X0,k10_relat_1(sK6,sK4))
    | ~ r2_hidden(sK1(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),sK4)
    | ~ r2_hidden(k4_tarski(X0,sK1(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)))),sK6) ),
    inference(instantiation,[status(thm)],[c_197])).

cnf(c_38576,plain,
    ( ~ r2_hidden(sK1(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),sK4)
    | r2_hidden(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k10_relat_1(sK6,sK4))
    | ~ r2_hidden(k4_tarski(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),sK1(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)))),sK6) ),
    inference(instantiation,[status(thm)],[c_3222])).

cnf(c_38577,plain,
    ( r2_hidden(sK1(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),sK4) != iProver_top
    | r2_hidden(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k10_relat_1(sK6,sK4)) = iProver_top
    | r2_hidden(k4_tarski(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),sK1(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)))),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38576])).

cnf(c_645,plain,
    ( r2_hidden(X0,k2_xboole_0(sK4,sK5))
    | ~ r2_hidden(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_38542,plain,
    ( r2_hidden(sK2(sK6,sK4,sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)))),k2_xboole_0(sK4,sK5))
    | ~ r2_hidden(sK2(sK6,sK4,sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)))),sK4) ),
    inference(instantiation,[status(thm)],[c_645])).

cnf(c_38543,plain,
    ( r2_hidden(sK2(sK6,sK4,sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)))),k2_xboole_0(sK4,sK5)) = iProver_top
    | r2_hidden(sK2(sK6,sK4,sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)))),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38542])).

cnf(c_1017,plain,
    ( r2_hidden(X0,k10_relat_1(sK6,sK5))
    | ~ r2_hidden(sK1(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),sK5)
    | ~ r2_hidden(k4_tarski(X0,sK1(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)))),sK6) ),
    inference(instantiation,[status(thm)],[c_197])).

cnf(c_28246,plain,
    ( ~ r2_hidden(sK1(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),sK5)
    | r2_hidden(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k10_relat_1(sK6,sK5))
    | ~ r2_hidden(k4_tarski(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),sK1(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)))),sK6) ),
    inference(instantiation,[status(thm)],[c_1017])).

cnf(c_28247,plain,
    ( r2_hidden(sK1(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),sK5) != iProver_top
    | r2_hidden(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k10_relat_1(sK6,sK5)) = iProver_top
    | r2_hidden(k4_tarski(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),sK1(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)))),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28246])).

cnf(c_9987,plain,
    ( ~ r2_hidden(sK2(sK6,sK5,sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)))),k2_xboole_0(sK4,sK5))
    | ~ r2_hidden(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)))
    | ~ r2_hidden(k4_tarski(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),sK2(sK6,sK5,sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))))),sK6)
    | k10_relat_1(sK6,k2_xboole_0(sK4,sK5)) = k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_605])).

cnf(c_9988,plain,
    ( k10_relat_1(sK6,k2_xboole_0(sK4,sK5)) = k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))
    | r2_hidden(sK2(sK6,sK5,sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)))),k2_xboole_0(sK4,sK5)) != iProver_top
    | r2_hidden(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))) != iProver_top
    | r2_hidden(k4_tarski(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),sK2(sK6,sK5,sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))))),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9987])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_223,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),X2)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_13])).

cnf(c_224,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK6,X1))
    | r2_hidden(sK2(sK6,X1,X0),X1) ),
    inference(unflattening,[status(thm)],[c_223])).

cnf(c_1706,plain,
    ( r2_hidden(sK2(sK6,sK4,sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)))),sK4)
    | ~ r2_hidden(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k10_relat_1(sK6,sK4)) ),
    inference(instantiation,[status(thm)],[c_224])).

cnf(c_1710,plain,
    ( r2_hidden(sK2(sK6,sK4,sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)))),sK4) = iProver_top
    | r2_hidden(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k10_relat_1(sK6,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1706])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X0,sK2(X1,X2,X0)),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_211,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X0,sK2(X1,X2,X0)),X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_13])).

cnf(c_212,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK6,X1))
    | r2_hidden(k4_tarski(X0,sK2(sK6,X1,X0)),sK6) ),
    inference(unflattening,[status(thm)],[c_211])).

cnf(c_1707,plain,
    ( ~ r2_hidden(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k10_relat_1(sK6,sK4))
    | r2_hidden(k4_tarski(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),sK2(sK6,sK4,sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))))),sK6) ),
    inference(instantiation,[status(thm)],[c_212])).

cnf(c_1708,plain,
    ( r2_hidden(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k10_relat_1(sK6,sK4)) != iProver_top
    | r2_hidden(k4_tarski(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),sK2(sK6,sK4,sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))))),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1707])).

cnf(c_640,plain,
    ( r2_hidden(X0,k2_xboole_0(sK4,sK5))
    | ~ r2_hidden(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_904,plain,
    ( r2_hidden(sK2(sK6,sK5,sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)))),k2_xboole_0(sK4,sK5))
    | ~ r2_hidden(sK2(sK6,sK5,sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)))),sK5) ),
    inference(instantiation,[status(thm)],[c_640])).

cnf(c_905,plain,
    ( r2_hidden(sK2(sK6,sK5,sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)))),k2_xboole_0(sK4,sK5)) = iProver_top
    | r2_hidden(sK2(sK6,sK5,sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)))),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_904])).

cnf(c_730,plain,
    ( r2_hidden(sK2(sK6,sK5,sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)))),sK5)
    | ~ r2_hidden(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k10_relat_1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_224])).

cnf(c_734,plain,
    ( r2_hidden(sK2(sK6,sK5,sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)))),sK5) = iProver_top
    | r2_hidden(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k10_relat_1(sK6,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_730])).

cnf(c_731,plain,
    ( ~ r2_hidden(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k10_relat_1(sK6,sK5))
    | r2_hidden(k4_tarski(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),sK2(sK6,sK5,sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))))),sK6) ),
    inference(instantiation,[status(thm)],[c_212])).

cnf(c_732,plain,
    ( r2_hidden(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k10_relat_1(sK6,sK5)) != iProver_top
    | r2_hidden(k4_tarski(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),sK2(sK6,sK5,sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))))),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_731])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_697,plain,
    ( ~ r2_hidden(sK1(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k2_xboole_0(sK4,sK5))
    | r2_hidden(sK1(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),sK5)
    | r2_hidden(sK1(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),sK4) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_698,plain,
    ( r2_hidden(sK1(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k2_xboole_0(sK4,sK5)) != iProver_top
    | r2_hidden(sK1(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),sK5) = iProver_top
    | r2_hidden(sK1(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_697])).

cnf(c_577,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k2_xboole_0(X1,k10_relat_1(sK6,X2)))
    | r2_hidden(X0,k10_relat_1(sK6,X2)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_650,plain,
    ( ~ r2_hidden(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)))
    | r2_hidden(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k10_relat_1(sK6,sK5))
    | r2_hidden(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k10_relat_1(sK6,sK4)) ),
    inference(instantiation,[status(thm)],[c_577])).

cnf(c_651,plain,
    ( r2_hidden(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))) != iProver_top
    | r2_hidden(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k10_relat_1(sK6,sK5)) = iProver_top
    | r2_hidden(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k10_relat_1(sK6,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_650])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_148,plain,
    ( r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
    | k10_relat_1(X0,X1) = X2
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_13])).

cnf(c_149,plain,
    ( r2_hidden(sK0(sK6,X0,X1),X1)
    | r2_hidden(k4_tarski(sK0(sK6,X0,X1),sK1(sK6,X0,X1)),sK6)
    | k10_relat_1(sK6,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_148])).

cnf(c_602,plain,
    ( r2_hidden(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)))
    | r2_hidden(k4_tarski(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),sK1(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)))),sK6)
    | k10_relat_1(sK6,k2_xboole_0(sK4,sK5)) = k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_149])).

cnf(c_603,plain,
    ( k10_relat_1(sK6,k2_xboole_0(sK4,sK5)) = k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))
    | r2_hidden(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))) = iProver_top
    | r2_hidden(k4_tarski(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),sK1(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)))),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_602])).

cnf(c_1,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_163,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k10_relat_1(X0,X1) = X2
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_13])).

cnf(c_164,plain,
    ( r2_hidden(sK1(sK6,X0,X1),X0)
    | r2_hidden(sK0(sK6,X0,X1),X1)
    | k10_relat_1(sK6,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_163])).

cnf(c_599,plain,
    ( r2_hidden(sK1(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k2_xboole_0(sK4,sK5))
    | r2_hidden(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)))
    | k10_relat_1(sK6,k2_xboole_0(sK4,sK5)) = k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_164])).

cnf(c_600,plain,
    ( k10_relat_1(sK6,k2_xboole_0(sK4,sK5)) = k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))
    | r2_hidden(sK1(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k2_xboole_0(sK4,sK5)) = iProver_top
    | r2_hidden(sK0(sK6,k2_xboole_0(sK4,sK5),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))),k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_599])).

cnf(c_12,negated_conjecture,
    ( k10_relat_1(sK6,k2_xboole_0(sK4,sK5)) != k2_xboole_0(k10_relat_1(sK6,sK4),k10_relat_1(sK6,sK5)) ),
    inference(cnf_transformation,[],[f33])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_108781,c_47923,c_41591,c_38577,c_38543,c_28247,c_9988,c_1710,c_1708,c_905,c_734,c_732,c_698,c_651,c_603,c_600,c_12])).


%------------------------------------------------------------------------------
