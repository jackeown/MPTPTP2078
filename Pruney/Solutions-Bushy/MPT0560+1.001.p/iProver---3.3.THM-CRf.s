%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0560+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:35 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 132 expanded)
%              Number of clauses        :   29 (  29 expanded)
%              Number of leaves         :   11 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :  359 ( 866 expanded)
%              Number of equality atoms :   45 ( 111 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal clause size      :   16 (   3 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
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

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f22,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK4(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK4(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,X3),X0) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1,X2),X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
              | ~ r2_hidden(k4_tarski(X4,sK2(X0,X1,X2)),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(X5,sK2(X0,X1,X2)),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(X4,sK2(X0,X1,X2)),X0) )
                | ~ r2_hidden(sK2(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK3(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X0) )
                | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ( r2_hidden(sK4(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(sK4(X0,X1,X6),X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f19,f22,f21,f20])).

fof(f35,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f47,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
            & r2_hidden(sK0(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK0(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
                    & r2_hidden(sK0(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).

fof(f29,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f44,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(k4_tarski(X4,sK2(X0,X1,X2)),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f28,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k9_relat_1(X0,X1) != k9_relat_1(k7_relat_1(X0,X2),X1)
          & r1_tarski(X1,X2) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( k9_relat_1(X0,X1) != k9_relat_1(k7_relat_1(X0,X2),X1)
          & r1_tarski(X1,X2) )
     => ( k9_relat_1(X0,sK6) != k9_relat_1(k7_relat_1(X0,sK7),sK6)
        & r1_tarski(sK6,sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k9_relat_1(X0,X1) != k9_relat_1(k7_relat_1(X0,X2),X1)
            & r1_tarski(X1,X2) )
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k9_relat_1(sK5,X1) != k9_relat_1(k7_relat_1(sK5,X2),X1)
          & r1_tarski(X1,X2) )
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( k9_relat_1(sK5,sK6) != k9_relat_1(k7_relat_1(sK5,sK7),sK6)
    & r1_tarski(sK6,sK7)
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f12,f25,f24])).

fof(f42,plain,(
    r1_tarski(sK6,sK7) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f49,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f34,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f48,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X0)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f43,plain,(
    k9_relat_1(sK5,sK6) != k9_relat_1(k7_relat_1(sK5,sK7),sK6) ),
    inference(cnf_transformation,[],[f26])).

fof(f41,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_874,plain,
    ( r2_hidden(X0,k9_relat_1(X1,sK6))
    | ~ r2_hidden(sK3(sK5,sK6,k9_relat_1(k7_relat_1(sK5,sK7),sK6)),sK6)
    | ~ r2_hidden(k4_tarski(sK3(sK5,sK6,k9_relat_1(k7_relat_1(sK5,sK7),sK6)),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2763,plain,
    ( ~ r2_hidden(sK3(sK5,sK6,k9_relat_1(k7_relat_1(sK5,sK7),sK6)),sK6)
    | r2_hidden(sK2(sK5,sK6,k9_relat_1(k7_relat_1(sK5,sK7),sK6)),k9_relat_1(k7_relat_1(sK5,sK7),sK6))
    | ~ r2_hidden(k4_tarski(sK3(sK5,sK6,k9_relat_1(k7_relat_1(sK5,sK7),sK6)),sK2(sK5,sK6,k9_relat_1(k7_relat_1(sK5,sK7),sK6))),k7_relat_1(sK5,sK7))
    | ~ v1_relat_1(k7_relat_1(sK5,sK7)) ),
    inference(instantiation,[status(thm)],[c_874])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | r2_hidden(k4_tarski(X0,X2),k7_relat_1(X3,X1))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k7_relat_1(X3,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1124,plain,
    ( ~ r2_hidden(sK3(sK5,sK6,k9_relat_1(k7_relat_1(sK5,sK7),sK6)),sK7)
    | ~ r2_hidden(k4_tarski(sK3(sK5,sK6,k9_relat_1(k7_relat_1(sK5,sK7),sK6)),X0),X1)
    | r2_hidden(k4_tarski(sK3(sK5,sK6,k9_relat_1(k7_relat_1(sK5,sK7),sK6)),X0),k7_relat_1(X1,sK7))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(k7_relat_1(X1,sK7)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2024,plain,
    ( ~ r2_hidden(sK3(sK5,sK6,k9_relat_1(k7_relat_1(sK5,sK7),sK6)),sK7)
    | r2_hidden(k4_tarski(sK3(sK5,sK6,k9_relat_1(k7_relat_1(sK5,sK7),sK6)),sK2(sK5,sK6,k9_relat_1(k7_relat_1(sK5,sK7),sK6))),k7_relat_1(sK5,sK7))
    | ~ r2_hidden(k4_tarski(sK3(sK5,sK6,k9_relat_1(k7_relat_1(sK5,sK7),sK6)),sK2(sK5,sK6,k9_relat_1(k7_relat_1(sK5,sK7),sK6))),sK5)
    | ~ v1_relat_1(k7_relat_1(sK5,sK7))
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1124])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK2(X2,X1,X3),X3)
    | ~ r2_hidden(k4_tarski(X0,sK2(X2,X1,X3)),X2)
    | ~ v1_relat_1(X2)
    | k9_relat_1(X2,X1) = X3 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_729,plain,
    ( ~ r2_hidden(X0,sK6)
    | ~ r2_hidden(sK2(sK5,sK6,k9_relat_1(k7_relat_1(sK5,sK7),sK6)),k9_relat_1(k7_relat_1(sK5,sK7),sK6))
    | ~ r2_hidden(k4_tarski(X0,sK2(sK5,sK6,k9_relat_1(k7_relat_1(sK5,sK7),sK6))),sK5)
    | ~ v1_relat_1(sK5)
    | k9_relat_1(sK5,sK6) = k9_relat_1(k7_relat_1(sK5,sK7),sK6) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1181,plain,
    ( ~ r2_hidden(sK4(k7_relat_1(sK5,sK7),sK6,sK2(sK5,sK6,k9_relat_1(k7_relat_1(sK5,sK7),sK6))),sK6)
    | ~ r2_hidden(sK2(sK5,sK6,k9_relat_1(k7_relat_1(sK5,sK7),sK6)),k9_relat_1(k7_relat_1(sK5,sK7),sK6))
    | ~ r2_hidden(k4_tarski(sK4(k7_relat_1(sK5,sK7),sK6,sK2(sK5,sK6,k9_relat_1(k7_relat_1(sK5,sK7),sK6))),sK2(sK5,sK6,k9_relat_1(k7_relat_1(sK5,sK7),sK6))),sK5)
    | ~ v1_relat_1(sK5)
    | k9_relat_1(sK5,sK6) = k9_relat_1(k7_relat_1(sK5,sK7),sK6) ),
    inference(instantiation,[status(thm)],[c_729])).

cnf(c_4,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X0,X1),k7_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k7_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1159,plain,
    ( ~ r2_hidden(k4_tarski(sK4(k7_relat_1(sK5,sK7),sK6,sK2(sK5,sK6,k9_relat_1(k7_relat_1(sK5,sK7),sK6))),sK2(sK5,sK6,k9_relat_1(k7_relat_1(sK5,sK7),sK6))),k7_relat_1(sK5,sK7))
    | r2_hidden(k4_tarski(sK4(k7_relat_1(sK5,sK7),sK6,sK2(sK5,sK6,k9_relat_1(k7_relat_1(sK5,sK7),sK6))),sK2(sK5,sK6,k9_relat_1(k7_relat_1(sK5,sK7),sK6))),sK5)
    | ~ v1_relat_1(k7_relat_1(sK5,sK7))
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(sK6,sK7) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_181,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | sK7 != X2
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_15])).

cnf(c_182,plain,
    ( r2_hidden(X0,sK7)
    | ~ r2_hidden(X0,sK6) ),
    inference(unflattening,[status(thm)],[c_181])).

cnf(c_889,plain,
    ( r2_hidden(sK3(sK5,sK6,k9_relat_1(k7_relat_1(sK5,sK7),sK6)),sK7)
    | ~ r2_hidden(sK3(sK5,sK6,k9_relat_1(k7_relat_1(sK5,sK7),sK6)),sK6) ),
    inference(instantiation,[status(thm)],[c_182])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_807,plain,
    ( v1_relat_1(k7_relat_1(sK5,sK7))
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK4(X1,X2,X0),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_760,plain,
    ( ~ r2_hidden(sK2(sK5,sK6,k9_relat_1(k7_relat_1(sK5,sK7),sK6)),k9_relat_1(k7_relat_1(sK5,sK7),sK6))
    | r2_hidden(k4_tarski(sK4(k7_relat_1(sK5,sK7),sK6,sK2(sK5,sK6,k9_relat_1(k7_relat_1(sK5,sK7),sK6))),sK2(sK5,sK6,k9_relat_1(k7_relat_1(sK5,sK7),sK6))),k7_relat_1(sK5,sK7))
    | ~ v1_relat_1(k7_relat_1(sK5,sK7)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK4(X1,X2,X0),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_761,plain,
    ( r2_hidden(sK4(k7_relat_1(sK5,sK7),sK6,sK2(sK5,sK6,k9_relat_1(k7_relat_1(sK5,sK7),sK6))),sK6)
    | ~ r2_hidden(sK2(sK5,sK6,k9_relat_1(k7_relat_1(sK5,sK7),sK6)),k9_relat_1(k7_relat_1(sK5,sK7),sK6))
    | ~ v1_relat_1(k7_relat_1(sK5,sK7)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_8,plain,
    ( r2_hidden(sK2(X0,X1,X2),X2)
    | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_734,plain,
    ( r2_hidden(sK2(sK5,sK6,k9_relat_1(k7_relat_1(sK5,sK7),sK6)),k9_relat_1(k7_relat_1(sK5,sK7),sK6))
    | r2_hidden(k4_tarski(sK3(sK5,sK6,k9_relat_1(k7_relat_1(sK5,sK7),sK6)),sK2(sK5,sK6,k9_relat_1(k7_relat_1(sK5,sK7),sK6))),sK5)
    | ~ v1_relat_1(sK5)
    | k9_relat_1(sK5,sK6) = k9_relat_1(k7_relat_1(sK5,sK7),sK6) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( r2_hidden(sK3(X0,X1,X2),X1)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_726,plain,
    ( r2_hidden(sK3(sK5,sK6,k9_relat_1(k7_relat_1(sK5,sK7),sK6)),sK6)
    | r2_hidden(sK2(sK5,sK6,k9_relat_1(k7_relat_1(sK5,sK7),sK6)),k9_relat_1(k7_relat_1(sK5,sK7),sK6))
    | ~ v1_relat_1(sK5)
    | k9_relat_1(sK5,sK6) = k9_relat_1(k7_relat_1(sK5,sK7),sK6) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_14,negated_conjecture,
    ( k9_relat_1(sK5,sK6) != k9_relat_1(k7_relat_1(sK5,sK7),sK6) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f41])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2763,c_2024,c_1181,c_1159,c_889,c_807,c_760,c_761,c_734,c_726,c_14,c_16])).


%------------------------------------------------------------------------------
