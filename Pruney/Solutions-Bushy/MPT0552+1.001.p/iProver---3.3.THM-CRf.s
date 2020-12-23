%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0552+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:34 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 152 expanded)
%              Number of clauses        :   33 (  40 expanded)
%              Number of leaves         :   10 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  298 ( 771 expanded)
%              Number of equality atoms :   36 (  80 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f11,plain,(
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
    inference(rectify,[],[f10])).

fof(f14,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK2(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,X3),X0) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
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
              | ~ r2_hidden(k4_tarski(X4,sK0(X0,X1,X2)),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(X5,sK0(X0,X1,X2)),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(X4,sK0(X0,X1,X2)),X0) )
                | ~ r2_hidden(sK0(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK1(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK0(X0,X1,X2)),X0) )
                | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ( r2_hidden(sK2(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f14,f13,f12])).

fof(f27,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK7,k3_xboole_0(sK5,sK6)),k3_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6)))
      & v1_relat_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ~ r1_tarski(k9_relat_1(sK7,k3_xboole_0(sK5,sK6)),k3_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6)))
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f9,f23])).

fof(f39,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f21])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f44,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f8,f16])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f40,plain,(
    ~ r1_tarski(k9_relat_1(sK7,k3_xboole_0(sK5,sK6)),k3_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6))) ),
    inference(cnf_transformation,[],[f24])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f46,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f45,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f26,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f25,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_247,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | sK7 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_15])).

cnf(c_248,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(sK7,X1))
    | ~ r2_hidden(k4_tarski(X0,X2),sK7) ),
    inference(unflattening,[status(thm)],[c_247])).

cnf(c_964,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,sK5))
    | ~ r2_hidden(sK2(sK7,k3_xboole_0(sK5,sK6),sK3(k9_relat_1(sK7,k3_xboole_0(sK5,sK6)),k3_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6)))),sK5)
    | ~ r2_hidden(k4_tarski(sK2(sK7,k3_xboole_0(sK5,sK6),sK3(k9_relat_1(sK7,k3_xboole_0(sK5,sK6)),k3_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6)))),X0),sK7) ),
    inference(instantiation,[status(thm)],[c_248])).

cnf(c_1542,plain,
    ( ~ r2_hidden(sK2(sK7,k3_xboole_0(sK5,sK6),sK3(k9_relat_1(sK7,k3_xboole_0(sK5,sK6)),k3_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6)))),sK5)
    | r2_hidden(sK3(k9_relat_1(sK7,k3_xboole_0(sK5,sK6)),k3_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6))),k9_relat_1(sK7,sK5))
    | ~ r2_hidden(k4_tarski(sK2(sK7,k3_xboole_0(sK5,sK6),sK3(k9_relat_1(sK7,k3_xboole_0(sK5,sK6)),k3_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6)))),sK3(k9_relat_1(sK7,k3_xboole_0(sK5,sK6)),k3_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6)))),sK7) ),
    inference(instantiation,[status(thm)],[c_964])).

cnf(c_949,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,sK6))
    | ~ r2_hidden(sK2(sK7,k3_xboole_0(sK5,sK6),sK3(k9_relat_1(sK7,k3_xboole_0(sK5,sK6)),k3_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6)))),sK6)
    | ~ r2_hidden(k4_tarski(sK2(sK7,k3_xboole_0(sK5,sK6),sK3(k9_relat_1(sK7,k3_xboole_0(sK5,sK6)),k3_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6)))),X0),sK7) ),
    inference(instantiation,[status(thm)],[c_248])).

cnf(c_1521,plain,
    ( ~ r2_hidden(sK2(sK7,k3_xboole_0(sK5,sK6),sK3(k9_relat_1(sK7,k3_xboole_0(sK5,sK6)),k3_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6)))),sK6)
    | r2_hidden(sK3(k9_relat_1(sK7,k3_xboole_0(sK5,sK6)),k3_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6))),k9_relat_1(sK7,sK6))
    | ~ r2_hidden(k4_tarski(sK2(sK7,k3_xboole_0(sK5,sK6),sK3(k9_relat_1(sK7,k3_xboole_0(sK5,sK6)),k3_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6)))),sK3(k9_relat_1(sK7,k3_xboole_0(sK5,sK6)),k3_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6)))),sK7) ),
    inference(instantiation,[status(thm)],[c_949])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_656,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK3(X0,X1),X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK7,k3_xboole_0(sK5,sK6)),k3_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_188,plain,
    ( ~ r2_hidden(sK3(X0,X1),X1)
    | k3_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6)) != X1
    | k9_relat_1(sK7,k3_xboole_0(sK5,sK6)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_14])).

cnf(c_189,plain,
    ( ~ r2_hidden(sK3(k9_relat_1(sK7,k3_xboole_0(sK5,sK6)),k3_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6))),k3_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6))) ),
    inference(unflattening,[status(thm)],[c_188])).

cnf(c_652,plain,
    ( r2_hidden(sK3(k9_relat_1(sK7,k3_xboole_0(sK5,sK6)),k3_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6))),k3_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_189])).

cnf(c_1436,plain,
    ( r2_hidden(sK3(k9_relat_1(sK7,k3_xboole_0(sK5,sK6)),k3_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6))),k9_relat_1(sK7,sK6)) != iProver_top
    | r2_hidden(sK3(k9_relat_1(sK7,k3_xboole_0(sK5,sK6)),k3_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6))),k9_relat_1(sK7,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_656,c_652])).

cnf(c_1441,plain,
    ( ~ r2_hidden(sK3(k9_relat_1(sK7,k3_xboole_0(sK5,sK6)),k3_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6))),k9_relat_1(sK7,sK6))
    | ~ r2_hidden(sK3(k9_relat_1(sK7,k3_xboole_0(sK5,sK6)),k3_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6))),k9_relat_1(sK7,sK5)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1436])).

cnf(c_13,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_829,plain,
    ( ~ r2_hidden(sK2(sK7,k3_xboole_0(sK5,sK6),sK3(k9_relat_1(sK7,k3_xboole_0(sK5,sK6)),k3_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6)))),k3_xboole_0(sK5,sK6))
    | r2_hidden(sK2(sK7,k3_xboole_0(sK5,sK6),sK3(k9_relat_1(sK7,k3_xboole_0(sK5,sK6)),k3_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6)))),sK5) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_12,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_826,plain,
    ( ~ r2_hidden(sK2(sK7,k3_xboole_0(sK5,sK6),sK3(k9_relat_1(sK7,k3_xboole_0(sK5,sK6)),k3_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6)))),k3_xboole_0(sK5,sK6))
    | r2_hidden(sK2(sK7,k3_xboole_0(sK5,sK6),sK3(k9_relat_1(sK7,k3_xboole_0(sK5,sK6)),k3_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6)))),sK6) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_274,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),X2)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_15])).

cnf(c_275,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
    | r2_hidden(sK2(sK7,X1,X0),X1) ),
    inference(unflattening,[status(thm)],[c_274])).

cnf(c_764,plain,
    ( r2_hidden(sK2(sK7,k3_xboole_0(sK5,sK6),sK3(k9_relat_1(sK7,k3_xboole_0(sK5,sK6)),k3_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6)))),k3_xboole_0(sK5,sK6))
    | ~ r2_hidden(sK3(k9_relat_1(sK7,k3_xboole_0(sK5,sK6)),k3_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6))),k9_relat_1(sK7,k3_xboole_0(sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_275])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK2(X1,X2,X0),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_262,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK2(X1,X2,X0),X0),X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_15])).

cnf(c_263,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
    | r2_hidden(k4_tarski(sK2(sK7,X1,X0),X0),sK7) ),
    inference(unflattening,[status(thm)],[c_262])).

cnf(c_761,plain,
    ( ~ r2_hidden(sK3(k9_relat_1(sK7,k3_xboole_0(sK5,sK6)),k3_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6))),k9_relat_1(sK7,k3_xboole_0(sK5,sK6)))
    | r2_hidden(k4_tarski(sK2(sK7,k3_xboole_0(sK5,sK6),sK3(k9_relat_1(sK7,k3_xboole_0(sK5,sK6)),k3_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6)))),sK3(k9_relat_1(sK7,k3_xboole_0(sK5,sK6)),k3_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6)))),sK7) ),
    inference(instantiation,[status(thm)],[c_263])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK3(X0,X1),X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_181,plain,
    ( r2_hidden(sK3(X0,X1),X0)
    | k3_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6)) != X1
    | k9_relat_1(sK7,k3_xboole_0(sK5,sK6)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_14])).

cnf(c_182,plain,
    ( r2_hidden(sK3(k9_relat_1(sK7,k3_xboole_0(sK5,sK6)),k3_xboole_0(k9_relat_1(sK7,sK5),k9_relat_1(sK7,sK6))),k9_relat_1(sK7,k3_xboole_0(sK5,sK6))) ),
    inference(unflattening,[status(thm)],[c_181])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1542,c_1521,c_1441,c_829,c_826,c_764,c_761,c_182])).


%------------------------------------------------------------------------------
