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
% DateTime   : Thu Dec  3 11:46:02 EST 2020

% Result     : Theorem 3.69s
% Output     : CNFRefutation 3.69s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 671 expanded)
%              Number of clauses        :   86 ( 222 expanded)
%              Number of leaves         :   18 ( 182 expanded)
%              Depth                    :   23
%              Number of atoms          :  481 (2683 expanded)
%              Number of equality atoms :  197 ( 738 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   15 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f12,plain,(
    ? [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) != k2_relat_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,
    ( ? [X0] :
        ( k9_relat_1(X0,k1_relat_1(X0)) != k2_relat_1(X0)
        & v1_relat_1(X0) )
   => ( k9_relat_1(sK8,k1_relat_1(sK8)) != k2_relat_1(sK8)
      & v1_relat_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( k9_relat_1(sK8,k1_relat_1(sK8)) != k2_relat_1(sK8)
    & v1_relat_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f12,f29])).

fof(f48,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X0] :
      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f19])).

fof(f23,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f20,f23,f22,f21])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f38,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f53,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f38])).

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

fof(f8,plain,(
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

fof(f13,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f14,plain,(
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
    inference(rectify,[],[f13])).

fof(f17,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK2(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,X3),X0) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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

fof(f18,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f17,f16,f15])).

fof(f31,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f52,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f46,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X3,X2),X0) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r2_hidden(k4_tarski(X3,X2),X0)
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
          | ~ r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1) )
        & ( r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
          | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ( ( ~ r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
                  | ~ r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1) )
                & ( r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
                  | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f26,f27])).

fof(f42,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f55,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f33,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f49,plain,(
    k9_relat_1(sK8,k1_relat_1(sK8)) != k2_relat_1(sK8) ),
    inference(cnf_transformation,[],[f30])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(k4_tarski(X4,sK0(X0,X1,X2)),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK0(X0,X1,X2)),X0)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_460,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_462,plain,
    ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_739,plain,
    ( k2_relat_1(k4_relat_1(sK8)) = k1_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_460,c_462])).

cnf(c_7,plain,
    ( r2_hidden(sK3(X0,X1),X1)
    | r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_470,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(sK3(X0,X1),X1) = iProver_top
    | r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_8,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_469,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1245,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(sK3(X0,X1),X1) = iProver_top
    | r2_hidden(sK3(X0,X1),k2_relat_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_470,c_469])).

cnf(c_2844,plain,
    ( k2_relat_1(k4_relat_1(sK8)) = X0
    | r2_hidden(sK3(k4_relat_1(sK8),X0),X0) = iProver_top
    | r2_hidden(sK3(k4_relat_1(sK8),X0),k1_relat_1(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_739,c_1245])).

cnf(c_2882,plain,
    ( k1_relat_1(sK8) = X0
    | r2_hidden(sK3(k4_relat_1(sK8),X0),X0) = iProver_top
    | r2_hidden(sK3(k4_relat_1(sK8),X0),k1_relat_1(sK8)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2844,c_739])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK2(X1,X2,X0),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_472,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK2(X1,X2,X0),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1905,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(X0,k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_472,c_469])).

cnf(c_3421,plain,
    ( k9_relat_1(X0,X1) = k1_relat_1(sK8)
    | r2_hidden(sK3(k4_relat_1(sK8),k9_relat_1(X0,X1)),k1_relat_1(sK8)) = iProver_top
    | r2_hidden(sK3(k4_relat_1(sK8),k9_relat_1(X0,X1)),k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2882,c_1905])).

cnf(c_3943,plain,
    ( k9_relat_1(k4_relat_1(sK8),X0) = k1_relat_1(sK8)
    | r2_hidden(sK3(k4_relat_1(sK8),k9_relat_1(k4_relat_1(sK8),X0)),k1_relat_1(sK8)) = iProver_top
    | v1_relat_1(k4_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_739,c_3421])).

cnf(c_19,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_26,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_28,plain,
    ( v1_relat_1(k4_relat_1(sK8)) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_3998,plain,
    ( r2_hidden(sK3(k4_relat_1(sK8),k9_relat_1(k4_relat_1(sK8),X0)),k1_relat_1(sK8)) = iProver_top
    | k9_relat_1(k4_relat_1(sK8),X0) = k1_relat_1(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3943,c_19,c_28])).

cnf(c_3999,plain,
    ( k9_relat_1(k4_relat_1(sK8),X0) = k1_relat_1(sK8)
    | r2_hidden(sK3(k4_relat_1(sK8),k9_relat_1(k4_relat_1(sK8),X0)),k1_relat_1(sK8)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3998])).

cnf(c_463,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_738,plain,
    ( k2_relat_1(k4_relat_1(k4_relat_1(X0))) = k1_relat_1(k4_relat_1(X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_463,c_462])).

cnf(c_1383,plain,
    ( k2_relat_1(k4_relat_1(k4_relat_1(sK8))) = k1_relat_1(k4_relat_1(sK8)) ),
    inference(superposition,[status(thm)],[c_460,c_738])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_461,plain,
    ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_676,plain,
    ( k1_relat_1(k4_relat_1(sK8)) = k2_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_460,c_461])).

cnf(c_1385,plain,
    ( k2_relat_1(k4_relat_1(k4_relat_1(sK8))) = k2_relat_1(sK8) ),
    inference(light_normalisation,[status(thm)],[c_1383,c_676])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK5(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_468,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(sK5(X1,X0),X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_12,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | r2_hidden(k4_tarski(X1,X0),k4_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k4_relat_1(X2)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_465,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),k4_relat_1(X2)) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k4_relat_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_554,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),k4_relat_1(X2)) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_465,c_463])).

cnf(c_4365,plain,
    ( r2_hidden(X0,k2_relat_1(k4_relat_1(X1))) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_554,c_469])).

cnf(c_4434,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK5(X1,X0),k2_relat_1(k4_relat_1(X1))) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_468,c_4365])).

cnf(c_5385,plain,
    ( r2_hidden(X0,k2_relat_1(k4_relat_1(sK8))) != iProver_top
    | r2_hidden(sK5(k4_relat_1(sK8),X0),k2_relat_1(sK8)) = iProver_top
    | v1_relat_1(k4_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1385,c_4434])).

cnf(c_5421,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(sK5(k4_relat_1(sK8),X0),k2_relat_1(sK8)) = iProver_top
    | v1_relat_1(k4_relat_1(sK8)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5385,c_739])).

cnf(c_6165,plain,
    ( r2_hidden(sK5(k4_relat_1(sK8),X0),k2_relat_1(sK8)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5421,c_19,c_28])).

cnf(c_6166,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(sK5(k4_relat_1(sK8),X0),k2_relat_1(sK8)) = iProver_top ),
    inference(renaming,[status(thm)],[c_6165])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_474,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k9_relat_1(X3,X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X3) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1933,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) = iProver_top
    | r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK5(X1,X0),X2) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_468,c_474])).

cnf(c_12105,plain,
    ( r2_hidden(X0,k9_relat_1(k4_relat_1(sK8),k2_relat_1(sK8))) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(X0,k2_relat_1(k4_relat_1(sK8))) != iProver_top
    | v1_relat_1(k4_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6166,c_1933])).

cnf(c_12166,plain,
    ( r2_hidden(X0,k9_relat_1(k4_relat_1(sK8),k2_relat_1(sK8))) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | v1_relat_1(k4_relat_1(sK8)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12105,c_739])).

cnf(c_12421,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(X0,k9_relat_1(k4_relat_1(sK8),k2_relat_1(sK8))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12166,c_19,c_28])).

cnf(c_12422,plain,
    ( r2_hidden(X0,k9_relat_1(k4_relat_1(sK8),k2_relat_1(sK8))) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_12421])).

cnf(c_6,plain,
    ( ~ r2_hidden(sK3(X0,X1),X1)
    | ~ r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_471,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(sK3(X0,X1),X1) != iProver_top
    | r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1735,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(sK3(X0,X1),X1) != iProver_top
    | r2_hidden(sK3(X0,X1),k2_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_468,c_471])).

cnf(c_4650,plain,
    ( k2_relat_1(k4_relat_1(sK8)) = X0
    | r2_hidden(sK3(k4_relat_1(sK8),X0),X0) != iProver_top
    | r2_hidden(sK3(k4_relat_1(sK8),X0),k1_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_739,c_1735])).

cnf(c_4686,plain,
    ( k1_relat_1(sK8) = X0
    | r2_hidden(sK3(k4_relat_1(sK8),X0),X0) != iProver_top
    | r2_hidden(sK3(k4_relat_1(sK8),X0),k1_relat_1(sK8)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4650,c_739])).

cnf(c_4816,plain,
    ( k9_relat_1(k4_relat_1(sK8),X0) = k1_relat_1(sK8)
    | r2_hidden(sK3(k4_relat_1(sK8),k9_relat_1(k4_relat_1(sK8),X0)),k9_relat_1(k4_relat_1(sK8),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3999,c_4686])).

cnf(c_12438,plain,
    ( k9_relat_1(k4_relat_1(sK8),k2_relat_1(sK8)) = k1_relat_1(sK8)
    | r2_hidden(sK3(k4_relat_1(sK8),k9_relat_1(k4_relat_1(sK8),k2_relat_1(sK8))),k1_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12422,c_4816])).

cnf(c_17,negated_conjecture,
    ( k9_relat_1(sK8,k1_relat_1(sK8)) != k2_relat_1(sK8) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_27,plain,
    ( v1_relat_1(k4_relat_1(sK8))
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_183,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_189,plain,
    ( k1_relat_1(sK8) = k1_relat_1(sK8)
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_183])).

cnf(c_176,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_191,plain,
    ( sK8 = sK8 ),
    inference(instantiation,[status(thm)],[c_176])).

cnf(c_731,plain,
    ( ~ r2_hidden(sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8)),k2_relat_1(sK8))
    | r2_hidden(k4_tarski(sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))),sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))),sK8) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(X2,X1,X3),X3)
    | ~ r2_hidden(k4_tarski(X0,sK0(X2,X1,X3)),X2)
    | ~ v1_relat_1(X2)
    | k9_relat_1(X2,X1) = X3 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_900,plain,
    ( ~ r2_hidden(sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8)),k2_relat_1(sK8))
    | ~ r2_hidden(sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))),k1_relat_1(sK8))
    | ~ r2_hidden(k4_tarski(sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))),sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))),sK8)
    | ~ v1_relat_1(sK8)
    | k9_relat_1(sK8,k1_relat_1(sK8)) = k2_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_911,plain,
    ( r2_hidden(k4_tarski(sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8)),sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8)))),k4_relat_1(sK8))
    | ~ r2_hidden(k4_tarski(sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))),sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))),sK8)
    | ~ v1_relat_1(k4_relat_1(sK8))
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1219,plain,
    ( ~ r2_hidden(sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8)),X0)
    | r2_hidden(sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))),k9_relat_1(k4_relat_1(sK8),X0))
    | ~ r2_hidden(k4_tarski(sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8)),sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8)))),k4_relat_1(sK8))
    | ~ v1_relat_1(k4_relat_1(sK8)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1714,plain,
    ( ~ r2_hidden(sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8)),k2_relat_1(sK8))
    | r2_hidden(sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))),k9_relat_1(k4_relat_1(sK8),k2_relat_1(sK8)))
    | ~ r2_hidden(k4_tarski(sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8)),sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8)))),k4_relat_1(sK8))
    | ~ v1_relat_1(k4_relat_1(sK8)) ),
    inference(instantiation,[status(thm)],[c_1219])).

cnf(c_2516,plain,
    ( sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))) = sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))) ),
    inference(instantiation,[status(thm)],[c_176])).

cnf(c_1,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_4241,plain,
    ( r2_hidden(sK1(sK8,k1_relat_1(sK8),k2_relat_1(sK8)),k1_relat_1(sK8))
    | r2_hidden(sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8)),k2_relat_1(sK8))
    | ~ v1_relat_1(sK8) ),
    inference(resolution,[status(thm)],[c_1,c_17])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK0(X0,X1,X2)),X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_718,plain,
    ( r2_hidden(sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8)),k2_relat_1(sK8))
    | r2_hidden(k4_tarski(sK1(sK8,k1_relat_1(sK8),k2_relat_1(sK8)),sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))),sK8)
    | ~ v1_relat_1(sK8)
    | k9_relat_1(sK8,k1_relat_1(sK8)) = k2_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_799,plain,
    ( r2_hidden(sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8)),k2_relat_1(sK8))
    | ~ r2_hidden(k4_tarski(sK1(sK8,k1_relat_1(sK8),k2_relat_1(sK8)),sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))),sK8) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_4747,plain,
    ( r2_hidden(sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8)),k2_relat_1(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4241,c_18,c_17,c_718,c_799])).

cnf(c_177,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1040,plain,
    ( X0 != X1
    | k1_relat_1(sK8) != X1
    | k1_relat_1(sK8) = X0 ),
    inference(instantiation,[status(thm)],[c_177])).

cnf(c_1517,plain,
    ( X0 != k1_relat_1(X1)
    | k1_relat_1(sK8) = X0
    | k1_relat_1(sK8) != k1_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_1040])).

cnf(c_7339,plain,
    ( k9_relat_1(k4_relat_1(sK8),k2_relat_1(sK8)) != k1_relat_1(X0)
    | k1_relat_1(sK8) = k9_relat_1(k4_relat_1(sK8),k2_relat_1(sK8))
    | k1_relat_1(sK8) != k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1517])).

cnf(c_7341,plain,
    ( k9_relat_1(k4_relat_1(sK8),k2_relat_1(sK8)) != k1_relat_1(sK8)
    | k1_relat_1(sK8) = k9_relat_1(k4_relat_1(sK8),k2_relat_1(sK8))
    | k1_relat_1(sK8) != k1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_7339])).

cnf(c_179,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2134,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))),k9_relat_1(k4_relat_1(sK8),k2_relat_1(sK8)))
    | X0 != sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8)))
    | X1 != k9_relat_1(k4_relat_1(sK8),k2_relat_1(sK8)) ),
    inference(instantiation,[status(thm)],[c_179])).

cnf(c_2515,plain,
    ( r2_hidden(sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))),X0)
    | ~ r2_hidden(sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))),k9_relat_1(k4_relat_1(sK8),k2_relat_1(sK8)))
    | X0 != k9_relat_1(k4_relat_1(sK8),k2_relat_1(sK8))
    | sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))) != sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))) ),
    inference(instantiation,[status(thm)],[c_2134])).

cnf(c_7340,plain,
    ( ~ r2_hidden(sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))),k9_relat_1(k4_relat_1(sK8),k2_relat_1(sK8)))
    | r2_hidden(sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))),k1_relat_1(sK8))
    | sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))) != sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8)))
    | k1_relat_1(sK8) != k9_relat_1(k4_relat_1(sK8),k2_relat_1(sK8)) ),
    inference(instantiation,[status(thm)],[c_2515])).

cnf(c_13357,plain,
    ( r2_hidden(sK3(k4_relat_1(sK8),k9_relat_1(k4_relat_1(sK8),k2_relat_1(sK8))),k1_relat_1(sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12438,c_18,c_17,c_27,c_189,c_191,c_718,c_731,c_799,c_900,c_911,c_1714,c_2516,c_7341,c_7340])).

cnf(c_13364,plain,
    ( k9_relat_1(k4_relat_1(sK8),k2_relat_1(sK8)) = k1_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_3999,c_13357])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13364,c_7340,c_7341,c_4747,c_2516,c_1714,c_911,c_900,c_731,c_191,c_189,c_27,c_17,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:16:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.69/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.69/0.97  
% 3.69/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.69/0.97  
% 3.69/0.97  ------  iProver source info
% 3.69/0.97  
% 3.69/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.69/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.69/0.97  git: non_committed_changes: false
% 3.69/0.97  git: last_make_outside_of_git: false
% 3.69/0.97  
% 3.69/0.97  ------ 
% 3.69/0.97  ------ Parsing...
% 3.69/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.69/0.97  
% 3.69/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.69/0.97  
% 3.69/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.69/0.97  
% 3.69/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.69/0.97  ------ Proving...
% 3.69/0.97  ------ Problem Properties 
% 3.69/0.97  
% 3.69/0.97  
% 3.69/0.97  clauses                                 19
% 3.69/0.97  conjectures                             2
% 3.69/0.97  EPR                                     1
% 3.69/0.97  Horn                                    15
% 3.69/0.97  unary                                   2
% 3.69/0.97  binary                                  5
% 3.69/0.97  lits                                    59
% 3.69/0.97  lits eq                                 10
% 3.69/0.97  fd_pure                                 0
% 3.69/0.97  fd_pseudo                               0
% 3.69/0.97  fd_cond                                 0
% 3.69/0.97  fd_pseudo_cond                          7
% 3.69/0.97  AC symbols                              0
% 3.69/0.97  
% 3.69/0.97  ------ Input Options Time Limit: Unbounded
% 3.69/0.97  
% 3.69/0.97  
% 3.69/0.97  ------ 
% 3.69/0.97  Current options:
% 3.69/0.97  ------ 
% 3.69/0.97  
% 3.69/0.97  
% 3.69/0.97  
% 3.69/0.97  
% 3.69/0.97  ------ Proving...
% 3.69/0.97  
% 3.69/0.97  
% 3.69/0.97  % SZS status Theorem for theBenchmark.p
% 3.69/0.97  
% 3.69/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.69/0.97  
% 3.69/0.97  fof(f6,conjecture,(
% 3.69/0.97    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 3.69/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.97  
% 3.69/0.97  fof(f7,negated_conjecture,(
% 3.69/0.97    ~! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 3.69/0.97    inference(negated_conjecture,[],[f6])).
% 3.69/0.97  
% 3.69/0.97  fof(f12,plain,(
% 3.69/0.97    ? [X0] : (k9_relat_1(X0,k1_relat_1(X0)) != k2_relat_1(X0) & v1_relat_1(X0))),
% 3.69/0.97    inference(ennf_transformation,[],[f7])).
% 3.69/0.97  
% 3.69/0.97  fof(f29,plain,(
% 3.69/0.97    ? [X0] : (k9_relat_1(X0,k1_relat_1(X0)) != k2_relat_1(X0) & v1_relat_1(X0)) => (k9_relat_1(sK8,k1_relat_1(sK8)) != k2_relat_1(sK8) & v1_relat_1(sK8))),
% 3.69/0.97    introduced(choice_axiom,[])).
% 3.69/0.97  
% 3.69/0.97  fof(f30,plain,(
% 3.69/0.97    k9_relat_1(sK8,k1_relat_1(sK8)) != k2_relat_1(sK8) & v1_relat_1(sK8)),
% 3.69/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f12,f29])).
% 3.69/0.97  
% 3.69/0.97  fof(f48,plain,(
% 3.69/0.97    v1_relat_1(sK8)),
% 3.69/0.97    inference(cnf_transformation,[],[f30])).
% 3.69/0.97  
% 3.69/0.97  fof(f5,axiom,(
% 3.69/0.97    ! [X0] : (v1_relat_1(X0) => (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 3.69/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.97  
% 3.69/0.97  fof(f11,plain,(
% 3.69/0.97    ! [X0] : ((k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.69/0.97    inference(ennf_transformation,[],[f5])).
% 3.69/0.97  
% 3.69/0.97  fof(f47,plain,(
% 3.69/0.97    ( ! [X0] : (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.69/0.97    inference(cnf_transformation,[],[f11])).
% 3.69/0.97  
% 3.69/0.97  fof(f2,axiom,(
% 3.69/0.97    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 3.69/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.97  
% 3.69/0.97  fof(f19,plain,(
% 3.69/0.97    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 3.69/0.97    inference(nnf_transformation,[],[f2])).
% 3.69/0.97  
% 3.69/0.97  fof(f20,plain,(
% 3.69/0.97    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.69/0.97    inference(rectify,[],[f19])).
% 3.69/0.97  
% 3.69/0.97  fof(f23,plain,(
% 3.69/0.97    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0))),
% 3.69/0.97    introduced(choice_axiom,[])).
% 3.69/0.97  
% 3.69/0.97  fof(f22,plain,(
% 3.69/0.97    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK4(X0,X1),X2),X0))) )),
% 3.69/0.97    introduced(choice_axiom,[])).
% 3.69/0.97  
% 3.69/0.97  fof(f21,plain,(
% 3.69/0.97    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 3.69/0.97    introduced(choice_axiom,[])).
% 3.69/0.97  
% 3.69/0.97  fof(f24,plain,(
% 3.69/0.97    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.69/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f20,f23,f22,f21])).
% 3.69/0.97  
% 3.69/0.97  fof(f39,plain,(
% 3.69/0.97    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)) )),
% 3.69/0.97    inference(cnf_transformation,[],[f24])).
% 3.69/0.97  
% 3.69/0.97  fof(f38,plain,(
% 3.69/0.97    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 3.69/0.97    inference(cnf_transformation,[],[f24])).
% 3.69/0.97  
% 3.69/0.97  fof(f53,plain,(
% 3.69/0.97    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 3.69/0.97    inference(equality_resolution,[],[f38])).
% 3.69/0.97  
% 3.69/0.97  fof(f1,axiom,(
% 3.69/0.97    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))))),
% 3.69/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.97  
% 3.69/0.97  fof(f8,plain,(
% 3.69/0.97    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))) | ~v1_relat_1(X0))),
% 3.69/0.97    inference(ennf_transformation,[],[f1])).
% 3.69/0.97  
% 3.69/0.97  fof(f13,plain,(
% 3.69/0.97    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.69/0.97    inference(nnf_transformation,[],[f8])).
% 3.69/0.97  
% 3.69/0.97  fof(f14,plain,(
% 3.69/0.97    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.69/0.97    inference(rectify,[],[f13])).
% 3.69/0.97  
% 3.69/0.97  fof(f17,plain,(
% 3.69/0.97    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) => (r2_hidden(sK2(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0)))),
% 3.69/0.97    introduced(choice_axiom,[])).
% 3.69/0.97  
% 3.69/0.97  fof(f16,plain,(
% 3.69/0.97    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X3),X0)))) )),
% 3.69/0.97    introduced(choice_axiom,[])).
% 3.69/0.97  
% 3.69/0.97  fof(f15,plain,(
% 3.69/0.97    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK0(X0,X1,X2)),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,sK0(X0,X1,X2)),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.69/0.97    introduced(choice_axiom,[])).
% 3.69/0.97  
% 3.69/0.97  fof(f18,plain,(
% 3.69/0.97    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK0(X0,X1,X2)),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK0(X0,X1,X2)),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & ((r2_hidden(sK2(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.69/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f17,f16,f15])).
% 3.69/0.97  
% 3.69/0.97  fof(f31,plain,(
% 3.69/0.97    ( ! [X6,X2,X0,X1] : (r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 3.69/0.97    inference(cnf_transformation,[],[f18])).
% 3.69/0.97  
% 3.69/0.97  fof(f52,plain,(
% 3.69/0.97    ( ! [X6,X0,X1] : (r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.69/0.97    inference(equality_resolution,[],[f31])).
% 3.69/0.97  
% 3.69/0.97  fof(f4,axiom,(
% 3.69/0.97    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 3.69/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.97  
% 3.69/0.97  fof(f10,plain,(
% 3.69/0.97    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.69/0.97    inference(ennf_transformation,[],[f4])).
% 3.69/0.97  
% 3.69/0.97  fof(f45,plain,(
% 3.69/0.97    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.69/0.97    inference(cnf_transformation,[],[f10])).
% 3.69/0.97  
% 3.69/0.97  fof(f46,plain,(
% 3.69/0.97    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.69/0.97    inference(cnf_transformation,[],[f11])).
% 3.69/0.97  
% 3.69/0.97  fof(f37,plain,(
% 3.69/0.97    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 3.69/0.97    inference(cnf_transformation,[],[f24])).
% 3.69/0.97  
% 3.69/0.97  fof(f54,plain,(
% 3.69/0.97    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 3.69/0.97    inference(equality_resolution,[],[f37])).
% 3.69/0.97  
% 3.69/0.97  fof(f3,axiom,(
% 3.69/0.97    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (k4_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0)))))),
% 3.69/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.97  
% 3.69/0.97  fof(f9,plain,(
% 3.69/0.97    ! [X0] : (! [X1] : ((k4_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.69/0.97    inference(ennf_transformation,[],[f3])).
% 3.69/0.97  
% 3.69/0.97  fof(f25,plain,(
% 3.69/0.97    ! [X0] : (! [X1] : (((k4_relat_1(X0) = X1 | ? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X3,X2),X0)) & (r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1))) | k4_relat_1(X0) != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.69/0.97    inference(nnf_transformation,[],[f9])).
% 3.69/0.97  
% 3.69/0.97  fof(f26,plain,(
% 3.69/0.97    ! [X0] : (! [X1] : (((k4_relat_1(X0) = X1 | ? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0)) & (r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k4_relat_1(X0) != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.69/0.97    inference(rectify,[],[f25])).
% 3.69/0.97  
% 3.69/0.97  fof(f27,plain,(
% 3.69/0.97    ! [X1,X0] : (? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1))) => ((~r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) | ~r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1)) & (r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1))))),
% 3.69/0.97    introduced(choice_axiom,[])).
% 3.69/0.97  
% 3.69/0.97  fof(f28,plain,(
% 3.69/0.97    ! [X0] : (! [X1] : (((k4_relat_1(X0) = X1 | ((~r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) | ~r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1)) & (r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0)) & (r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k4_relat_1(X0) != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.69/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f26,f27])).
% 3.69/0.97  
% 3.69/0.97  fof(f42,plain,(
% 3.69/0.97    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0) | k4_relat_1(X0) != X1 | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.69/0.97    inference(cnf_transformation,[],[f28])).
% 3.69/0.97  
% 3.69/0.97  fof(f55,plain,(
% 3.69/0.97    ( ! [X4,X0,X5] : (r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X4),X0) | ~v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.69/0.97    inference(equality_resolution,[],[f42])).
% 3.69/0.97  
% 3.69/0.97  fof(f33,plain,(
% 3.69/0.97    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0) | k9_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 3.69/0.97    inference(cnf_transformation,[],[f18])).
% 3.69/0.97  
% 3.69/0.97  fof(f50,plain,(
% 3.69/0.97    ( ! [X6,X0,X7,X1] : (r2_hidden(X6,k9_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0) | ~v1_relat_1(X0)) )),
% 3.69/0.97    inference(equality_resolution,[],[f33])).
% 3.69/0.97  
% 3.69/0.97  fof(f40,plain,(
% 3.69/0.97    ( ! [X0,X3,X1] : (k2_relat_1(X0) = X1 | ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 3.69/0.97    inference(cnf_transformation,[],[f24])).
% 3.69/0.97  
% 3.69/0.97  fof(f49,plain,(
% 3.69/0.97    k9_relat_1(sK8,k1_relat_1(sK8)) != k2_relat_1(sK8)),
% 3.69/0.97    inference(cnf_transformation,[],[f30])).
% 3.69/0.97  
% 3.69/0.97  fof(f36,plain,(
% 3.69/0.97    ( ! [X4,X2,X0,X1] : (k9_relat_1(X0,X1) = X2 | ~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK0(X0,X1,X2)),X0) | ~r2_hidden(sK0(X0,X1,X2),X2) | ~v1_relat_1(X0)) )),
% 3.69/0.97    inference(cnf_transformation,[],[f18])).
% 3.69/0.97  
% 3.69/0.97  fof(f35,plain,(
% 3.69/0.97    ( ! [X2,X0,X1] : (k9_relat_1(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2) | ~v1_relat_1(X0)) )),
% 3.69/0.97    inference(cnf_transformation,[],[f18])).
% 3.69/0.97  
% 3.69/0.97  fof(f34,plain,(
% 3.69/0.97    ( ! [X2,X0,X1] : (k9_relat_1(X0,X1) = X2 | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK0(X0,X1,X2)),X0) | r2_hidden(sK0(X0,X1,X2),X2) | ~v1_relat_1(X0)) )),
% 3.69/0.97    inference(cnf_transformation,[],[f18])).
% 3.69/0.97  
% 3.69/0.97  cnf(c_18,negated_conjecture,
% 3.69/0.97      ( v1_relat_1(sK8) ),
% 3.69/0.97      inference(cnf_transformation,[],[f48]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_460,plain,
% 3.69/0.97      ( v1_relat_1(sK8) = iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_15,plain,
% 3.69/0.97      ( ~ v1_relat_1(X0) | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
% 3.69/0.97      inference(cnf_transformation,[],[f47]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_462,plain,
% 3.69/0.97      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
% 3.69/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_739,plain,
% 3.69/0.97      ( k2_relat_1(k4_relat_1(sK8)) = k1_relat_1(sK8) ),
% 3.69/0.97      inference(superposition,[status(thm)],[c_460,c_462]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_7,plain,
% 3.69/0.97      ( r2_hidden(sK3(X0,X1),X1)
% 3.69/0.97      | r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
% 3.69/0.97      | k2_relat_1(X0) = X1 ),
% 3.69/0.97      inference(cnf_transformation,[],[f39]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_470,plain,
% 3.69/0.97      ( k2_relat_1(X0) = X1
% 3.69/0.97      | r2_hidden(sK3(X0,X1),X1) = iProver_top
% 3.69/0.97      | r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) = iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_8,plain,
% 3.69/0.97      ( r2_hidden(X0,k2_relat_1(X1)) | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
% 3.69/0.97      inference(cnf_transformation,[],[f53]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_469,plain,
% 3.69/0.97      ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
% 3.69/0.97      | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1245,plain,
% 3.69/0.97      ( k2_relat_1(X0) = X1
% 3.69/0.97      | r2_hidden(sK3(X0,X1),X1) = iProver_top
% 3.69/0.97      | r2_hidden(sK3(X0,X1),k2_relat_1(X0)) = iProver_top ),
% 3.69/0.97      inference(superposition,[status(thm)],[c_470,c_469]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_2844,plain,
% 3.69/0.97      ( k2_relat_1(k4_relat_1(sK8)) = X0
% 3.69/0.97      | r2_hidden(sK3(k4_relat_1(sK8),X0),X0) = iProver_top
% 3.69/0.97      | r2_hidden(sK3(k4_relat_1(sK8),X0),k1_relat_1(sK8)) = iProver_top ),
% 3.69/0.97      inference(superposition,[status(thm)],[c_739,c_1245]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_2882,plain,
% 3.69/0.97      ( k1_relat_1(sK8) = X0
% 3.69/0.97      | r2_hidden(sK3(k4_relat_1(sK8),X0),X0) = iProver_top
% 3.69/0.97      | r2_hidden(sK3(k4_relat_1(sK8),X0),k1_relat_1(sK8)) = iProver_top ),
% 3.69/0.97      inference(demodulation,[status(thm)],[c_2844,c_739]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_5,plain,
% 3.69/0.97      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.69/0.97      | r2_hidden(k4_tarski(sK2(X1,X2,X0),X0),X1)
% 3.69/0.97      | ~ v1_relat_1(X1) ),
% 3.69/0.97      inference(cnf_transformation,[],[f52]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_472,plain,
% 3.69/0.97      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.69/0.97      | r2_hidden(k4_tarski(sK2(X1,X2,X0),X0),X1) = iProver_top
% 3.69/0.97      | v1_relat_1(X1) != iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1905,plain,
% 3.69/0.97      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.69/0.97      | r2_hidden(X0,k2_relat_1(X1)) = iProver_top
% 3.69/0.97      | v1_relat_1(X1) != iProver_top ),
% 3.69/0.97      inference(superposition,[status(thm)],[c_472,c_469]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_3421,plain,
% 3.69/0.97      ( k9_relat_1(X0,X1) = k1_relat_1(sK8)
% 3.69/0.97      | r2_hidden(sK3(k4_relat_1(sK8),k9_relat_1(X0,X1)),k1_relat_1(sK8)) = iProver_top
% 3.69/0.97      | r2_hidden(sK3(k4_relat_1(sK8),k9_relat_1(X0,X1)),k2_relat_1(X0)) = iProver_top
% 3.69/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.69/0.97      inference(superposition,[status(thm)],[c_2882,c_1905]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_3943,plain,
% 3.69/0.97      ( k9_relat_1(k4_relat_1(sK8),X0) = k1_relat_1(sK8)
% 3.69/0.97      | r2_hidden(sK3(k4_relat_1(sK8),k9_relat_1(k4_relat_1(sK8),X0)),k1_relat_1(sK8)) = iProver_top
% 3.69/0.97      | v1_relat_1(k4_relat_1(sK8)) != iProver_top ),
% 3.69/0.97      inference(superposition,[status(thm)],[c_739,c_3421]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_19,plain,
% 3.69/0.97      ( v1_relat_1(sK8) = iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_14,plain,
% 3.69/0.97      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 3.69/0.97      inference(cnf_transformation,[],[f45]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_26,plain,
% 3.69/0.97      ( v1_relat_1(X0) != iProver_top
% 3.69/0.97      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_28,plain,
% 3.69/0.97      ( v1_relat_1(k4_relat_1(sK8)) = iProver_top
% 3.69/0.97      | v1_relat_1(sK8) != iProver_top ),
% 3.69/0.97      inference(instantiation,[status(thm)],[c_26]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_3998,plain,
% 3.69/0.97      ( r2_hidden(sK3(k4_relat_1(sK8),k9_relat_1(k4_relat_1(sK8),X0)),k1_relat_1(sK8)) = iProver_top
% 3.69/0.97      | k9_relat_1(k4_relat_1(sK8),X0) = k1_relat_1(sK8) ),
% 3.69/0.97      inference(global_propositional_subsumption,
% 3.69/0.97                [status(thm)],
% 3.69/0.97                [c_3943,c_19,c_28]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_3999,plain,
% 3.69/0.97      ( k9_relat_1(k4_relat_1(sK8),X0) = k1_relat_1(sK8)
% 3.69/0.97      | r2_hidden(sK3(k4_relat_1(sK8),k9_relat_1(k4_relat_1(sK8),X0)),k1_relat_1(sK8)) = iProver_top ),
% 3.69/0.97      inference(renaming,[status(thm)],[c_3998]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_463,plain,
% 3.69/0.97      ( v1_relat_1(X0) != iProver_top
% 3.69/0.97      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_738,plain,
% 3.69/0.97      ( k2_relat_1(k4_relat_1(k4_relat_1(X0))) = k1_relat_1(k4_relat_1(X0))
% 3.69/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.69/0.97      inference(superposition,[status(thm)],[c_463,c_462]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1383,plain,
% 3.69/0.97      ( k2_relat_1(k4_relat_1(k4_relat_1(sK8))) = k1_relat_1(k4_relat_1(sK8)) ),
% 3.69/0.97      inference(superposition,[status(thm)],[c_460,c_738]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_16,plain,
% 3.69/0.97      ( ~ v1_relat_1(X0) | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
% 3.69/0.97      inference(cnf_transformation,[],[f46]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_461,plain,
% 3.69/0.97      ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
% 3.69/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_676,plain,
% 3.69/0.97      ( k1_relat_1(k4_relat_1(sK8)) = k2_relat_1(sK8) ),
% 3.69/0.97      inference(superposition,[status(thm)],[c_460,c_461]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1385,plain,
% 3.69/0.97      ( k2_relat_1(k4_relat_1(k4_relat_1(sK8))) = k2_relat_1(sK8) ),
% 3.69/0.97      inference(light_normalisation,[status(thm)],[c_1383,c_676]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_9,plain,
% 3.69/0.97      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.69/0.97      | r2_hidden(k4_tarski(sK5(X1,X0),X0),X1) ),
% 3.69/0.97      inference(cnf_transformation,[],[f54]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_468,plain,
% 3.69/0.97      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 3.69/0.97      | r2_hidden(k4_tarski(sK5(X1,X0),X0),X1) = iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_12,plain,
% 3.69/0.97      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.69/0.97      | r2_hidden(k4_tarski(X1,X0),k4_relat_1(X2))
% 3.69/0.97      | ~ v1_relat_1(X2)
% 3.69/0.97      | ~ v1_relat_1(k4_relat_1(X2)) ),
% 3.69/0.97      inference(cnf_transformation,[],[f55]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_465,plain,
% 3.69/0.97      ( r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
% 3.69/0.97      | r2_hidden(k4_tarski(X1,X0),k4_relat_1(X2)) = iProver_top
% 3.69/0.97      | v1_relat_1(X2) != iProver_top
% 3.69/0.97      | v1_relat_1(k4_relat_1(X2)) != iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_554,plain,
% 3.69/0.97      ( r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
% 3.69/0.97      | r2_hidden(k4_tarski(X1,X0),k4_relat_1(X2)) = iProver_top
% 3.69/0.97      | v1_relat_1(X2) != iProver_top ),
% 3.69/0.97      inference(forward_subsumption_resolution,
% 3.69/0.97                [status(thm)],
% 3.69/0.97                [c_465,c_463]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_4365,plain,
% 3.69/0.97      ( r2_hidden(X0,k2_relat_1(k4_relat_1(X1))) = iProver_top
% 3.69/0.97      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top
% 3.69/0.97      | v1_relat_1(X1) != iProver_top ),
% 3.69/0.97      inference(superposition,[status(thm)],[c_554,c_469]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_4434,plain,
% 3.69/0.97      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 3.69/0.97      | r2_hidden(sK5(X1,X0),k2_relat_1(k4_relat_1(X1))) = iProver_top
% 3.69/0.97      | v1_relat_1(X1) != iProver_top ),
% 3.69/0.97      inference(superposition,[status(thm)],[c_468,c_4365]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_5385,plain,
% 3.69/0.97      ( r2_hidden(X0,k2_relat_1(k4_relat_1(sK8))) != iProver_top
% 3.69/0.97      | r2_hidden(sK5(k4_relat_1(sK8),X0),k2_relat_1(sK8)) = iProver_top
% 3.69/0.97      | v1_relat_1(k4_relat_1(sK8)) != iProver_top ),
% 3.69/0.97      inference(superposition,[status(thm)],[c_1385,c_4434]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_5421,plain,
% 3.69/0.97      ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 3.69/0.97      | r2_hidden(sK5(k4_relat_1(sK8),X0),k2_relat_1(sK8)) = iProver_top
% 3.69/0.97      | v1_relat_1(k4_relat_1(sK8)) != iProver_top ),
% 3.69/0.97      inference(light_normalisation,[status(thm)],[c_5385,c_739]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_6165,plain,
% 3.69/0.97      ( r2_hidden(sK5(k4_relat_1(sK8),X0),k2_relat_1(sK8)) = iProver_top
% 3.69/0.97      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top ),
% 3.69/0.97      inference(global_propositional_subsumption,
% 3.69/0.97                [status(thm)],
% 3.69/0.97                [c_5421,c_19,c_28]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_6166,plain,
% 3.69/0.97      ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 3.69/0.97      | r2_hidden(sK5(k4_relat_1(sK8),X0),k2_relat_1(sK8)) = iProver_top ),
% 3.69/0.97      inference(renaming,[status(thm)],[c_6165]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_3,plain,
% 3.69/0.97      ( ~ r2_hidden(X0,X1)
% 3.69/0.97      | r2_hidden(X2,k9_relat_1(X3,X1))
% 3.69/0.97      | ~ r2_hidden(k4_tarski(X0,X2),X3)
% 3.69/0.97      | ~ v1_relat_1(X3) ),
% 3.69/0.97      inference(cnf_transformation,[],[f50]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_474,plain,
% 3.69/0.97      ( r2_hidden(X0,X1) != iProver_top
% 3.69/0.97      | r2_hidden(X2,k9_relat_1(X3,X1)) = iProver_top
% 3.69/0.97      | r2_hidden(k4_tarski(X0,X2),X3) != iProver_top
% 3.69/0.97      | v1_relat_1(X3) != iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1933,plain,
% 3.69/0.97      ( r2_hidden(X0,k9_relat_1(X1,X2)) = iProver_top
% 3.69/0.97      | r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 3.69/0.97      | r2_hidden(sK5(X1,X0),X2) != iProver_top
% 3.69/0.97      | v1_relat_1(X1) != iProver_top ),
% 3.69/0.97      inference(superposition,[status(thm)],[c_468,c_474]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_12105,plain,
% 3.69/0.97      ( r2_hidden(X0,k9_relat_1(k4_relat_1(sK8),k2_relat_1(sK8))) = iProver_top
% 3.69/0.97      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 3.69/0.97      | r2_hidden(X0,k2_relat_1(k4_relat_1(sK8))) != iProver_top
% 3.69/0.97      | v1_relat_1(k4_relat_1(sK8)) != iProver_top ),
% 3.69/0.97      inference(superposition,[status(thm)],[c_6166,c_1933]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_12166,plain,
% 3.69/0.97      ( r2_hidden(X0,k9_relat_1(k4_relat_1(sK8),k2_relat_1(sK8))) = iProver_top
% 3.69/0.97      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 3.69/0.97      | v1_relat_1(k4_relat_1(sK8)) != iProver_top ),
% 3.69/0.97      inference(light_normalisation,[status(thm)],[c_12105,c_739]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_12421,plain,
% 3.69/0.97      ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 3.69/0.97      | r2_hidden(X0,k9_relat_1(k4_relat_1(sK8),k2_relat_1(sK8))) = iProver_top ),
% 3.69/0.97      inference(global_propositional_subsumption,
% 3.69/0.97                [status(thm)],
% 3.69/0.97                [c_12166,c_19,c_28]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_12422,plain,
% 3.69/0.97      ( r2_hidden(X0,k9_relat_1(k4_relat_1(sK8),k2_relat_1(sK8))) = iProver_top
% 3.69/0.97      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top ),
% 3.69/0.97      inference(renaming,[status(thm)],[c_12421]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_6,plain,
% 3.69/0.97      ( ~ r2_hidden(sK3(X0,X1),X1)
% 3.69/0.97      | ~ r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0)
% 3.69/0.97      | k2_relat_1(X0) = X1 ),
% 3.69/0.97      inference(cnf_transformation,[],[f40]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_471,plain,
% 3.69/0.97      ( k2_relat_1(X0) = X1
% 3.69/0.97      | r2_hidden(sK3(X0,X1),X1) != iProver_top
% 3.69/0.97      | r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0) != iProver_top ),
% 3.69/0.97      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1735,plain,
% 3.69/0.97      ( k2_relat_1(X0) = X1
% 3.69/0.97      | r2_hidden(sK3(X0,X1),X1) != iProver_top
% 3.69/0.97      | r2_hidden(sK3(X0,X1),k2_relat_1(X0)) != iProver_top ),
% 3.69/0.97      inference(superposition,[status(thm)],[c_468,c_471]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_4650,plain,
% 3.69/0.97      ( k2_relat_1(k4_relat_1(sK8)) = X0
% 3.69/0.97      | r2_hidden(sK3(k4_relat_1(sK8),X0),X0) != iProver_top
% 3.69/0.97      | r2_hidden(sK3(k4_relat_1(sK8),X0),k1_relat_1(sK8)) != iProver_top ),
% 3.69/0.97      inference(superposition,[status(thm)],[c_739,c_1735]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_4686,plain,
% 3.69/0.97      ( k1_relat_1(sK8) = X0
% 3.69/0.97      | r2_hidden(sK3(k4_relat_1(sK8),X0),X0) != iProver_top
% 3.69/0.97      | r2_hidden(sK3(k4_relat_1(sK8),X0),k1_relat_1(sK8)) != iProver_top ),
% 3.69/0.97      inference(demodulation,[status(thm)],[c_4650,c_739]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_4816,plain,
% 3.69/0.97      ( k9_relat_1(k4_relat_1(sK8),X0) = k1_relat_1(sK8)
% 3.69/0.97      | r2_hidden(sK3(k4_relat_1(sK8),k9_relat_1(k4_relat_1(sK8),X0)),k9_relat_1(k4_relat_1(sK8),X0)) != iProver_top ),
% 3.69/0.97      inference(superposition,[status(thm)],[c_3999,c_4686]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_12438,plain,
% 3.69/0.97      ( k9_relat_1(k4_relat_1(sK8),k2_relat_1(sK8)) = k1_relat_1(sK8)
% 3.69/0.97      | r2_hidden(sK3(k4_relat_1(sK8),k9_relat_1(k4_relat_1(sK8),k2_relat_1(sK8))),k1_relat_1(sK8)) != iProver_top ),
% 3.69/0.97      inference(superposition,[status(thm)],[c_12422,c_4816]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_17,negated_conjecture,
% 3.69/0.97      ( k9_relat_1(sK8,k1_relat_1(sK8)) != k2_relat_1(sK8) ),
% 3.69/0.97      inference(cnf_transformation,[],[f49]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_27,plain,
% 3.69/0.97      ( v1_relat_1(k4_relat_1(sK8)) | ~ v1_relat_1(sK8) ),
% 3.69/0.97      inference(instantiation,[status(thm)],[c_14]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_183,plain,
% 3.69/0.97      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 3.69/0.97      theory(equality) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_189,plain,
% 3.69/0.97      ( k1_relat_1(sK8) = k1_relat_1(sK8) | sK8 != sK8 ),
% 3.69/0.97      inference(instantiation,[status(thm)],[c_183]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_176,plain,( X0 = X0 ),theory(equality) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_191,plain,
% 3.69/0.97      ( sK8 = sK8 ),
% 3.69/0.97      inference(instantiation,[status(thm)],[c_176]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_731,plain,
% 3.69/0.97      ( ~ r2_hidden(sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8)),k2_relat_1(sK8))
% 3.69/0.97      | r2_hidden(k4_tarski(sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))),sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))),sK8) ),
% 3.69/0.97      inference(instantiation,[status(thm)],[c_9]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_0,plain,
% 3.69/0.97      ( ~ r2_hidden(X0,X1)
% 3.69/0.97      | ~ r2_hidden(sK0(X2,X1,X3),X3)
% 3.69/0.97      | ~ r2_hidden(k4_tarski(X0,sK0(X2,X1,X3)),X2)
% 3.69/0.97      | ~ v1_relat_1(X2)
% 3.69/0.97      | k9_relat_1(X2,X1) = X3 ),
% 3.69/0.97      inference(cnf_transformation,[],[f36]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_900,plain,
% 3.69/0.97      ( ~ r2_hidden(sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8)),k2_relat_1(sK8))
% 3.69/0.97      | ~ r2_hidden(sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))),k1_relat_1(sK8))
% 3.69/0.97      | ~ r2_hidden(k4_tarski(sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))),sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))),sK8)
% 3.69/0.97      | ~ v1_relat_1(sK8)
% 3.69/0.97      | k9_relat_1(sK8,k1_relat_1(sK8)) = k2_relat_1(sK8) ),
% 3.69/0.97      inference(instantiation,[status(thm)],[c_0]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_911,plain,
% 3.69/0.97      ( r2_hidden(k4_tarski(sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8)),sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8)))),k4_relat_1(sK8))
% 3.69/0.97      | ~ r2_hidden(k4_tarski(sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))),sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))),sK8)
% 3.69/0.97      | ~ v1_relat_1(k4_relat_1(sK8))
% 3.69/0.97      | ~ v1_relat_1(sK8) ),
% 3.69/0.97      inference(instantiation,[status(thm)],[c_12]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1219,plain,
% 3.69/0.97      ( ~ r2_hidden(sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8)),X0)
% 3.69/0.97      | r2_hidden(sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))),k9_relat_1(k4_relat_1(sK8),X0))
% 3.69/0.97      | ~ r2_hidden(k4_tarski(sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8)),sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8)))),k4_relat_1(sK8))
% 3.69/0.97      | ~ v1_relat_1(k4_relat_1(sK8)) ),
% 3.69/0.97      inference(instantiation,[status(thm)],[c_3]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1714,plain,
% 3.69/0.97      ( ~ r2_hidden(sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8)),k2_relat_1(sK8))
% 3.69/0.97      | r2_hidden(sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))),k9_relat_1(k4_relat_1(sK8),k2_relat_1(sK8)))
% 3.69/0.97      | ~ r2_hidden(k4_tarski(sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8)),sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8)))),k4_relat_1(sK8))
% 3.69/0.97      | ~ v1_relat_1(k4_relat_1(sK8)) ),
% 3.69/0.97      inference(instantiation,[status(thm)],[c_1219]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_2516,plain,
% 3.69/0.97      ( sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))) = sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))) ),
% 3.69/0.97      inference(instantiation,[status(thm)],[c_176]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_1,plain,
% 3.69/0.97      ( r2_hidden(sK1(X0,X1,X2),X1)
% 3.69/0.97      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.69/0.97      | ~ v1_relat_1(X0)
% 3.69/0.97      | k9_relat_1(X0,X1) = X2 ),
% 3.69/0.97      inference(cnf_transformation,[],[f35]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_4241,plain,
% 3.69/0.97      ( r2_hidden(sK1(sK8,k1_relat_1(sK8),k2_relat_1(sK8)),k1_relat_1(sK8))
% 3.69/0.97      | r2_hidden(sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8)),k2_relat_1(sK8))
% 3.69/0.97      | ~ v1_relat_1(sK8) ),
% 3.69/0.97      inference(resolution,[status(thm)],[c_1,c_17]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_2,plain,
% 3.69/0.97      ( r2_hidden(sK0(X0,X1,X2),X2)
% 3.69/0.97      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK0(X0,X1,X2)),X0)
% 3.69/0.97      | ~ v1_relat_1(X0)
% 3.69/0.97      | k9_relat_1(X0,X1) = X2 ),
% 3.69/0.97      inference(cnf_transformation,[],[f34]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_718,plain,
% 3.69/0.97      ( r2_hidden(sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8)),k2_relat_1(sK8))
% 3.69/0.97      | r2_hidden(k4_tarski(sK1(sK8,k1_relat_1(sK8),k2_relat_1(sK8)),sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))),sK8)
% 3.69/0.97      | ~ v1_relat_1(sK8)
% 3.69/0.97      | k9_relat_1(sK8,k1_relat_1(sK8)) = k2_relat_1(sK8) ),
% 3.69/0.97      inference(instantiation,[status(thm)],[c_2]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_799,plain,
% 3.69/0.97      ( r2_hidden(sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8)),k2_relat_1(sK8))
% 3.69/0.97      | ~ r2_hidden(k4_tarski(sK1(sK8,k1_relat_1(sK8),k2_relat_1(sK8)),sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))),sK8) ),
% 3.69/0.97      inference(instantiation,[status(thm)],[c_8]) ).
% 3.69/0.97  
% 3.69/0.97  cnf(c_4747,plain,
% 3.69/0.97      ( r2_hidden(sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8)),k2_relat_1(sK8)) ),
% 3.69/0.97      inference(global_propositional_subsumption,
% 3.69/0.98                [status(thm)],
% 3.69/0.98                [c_4241,c_18,c_17,c_718,c_799]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_177,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_1040,plain,
% 3.69/0.98      ( X0 != X1 | k1_relat_1(sK8) != X1 | k1_relat_1(sK8) = X0 ),
% 3.69/0.98      inference(instantiation,[status(thm)],[c_177]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_1517,plain,
% 3.69/0.98      ( X0 != k1_relat_1(X1)
% 3.69/0.98      | k1_relat_1(sK8) = X0
% 3.69/0.98      | k1_relat_1(sK8) != k1_relat_1(X1) ),
% 3.69/0.98      inference(instantiation,[status(thm)],[c_1040]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_7339,plain,
% 3.69/0.98      ( k9_relat_1(k4_relat_1(sK8),k2_relat_1(sK8)) != k1_relat_1(X0)
% 3.69/0.98      | k1_relat_1(sK8) = k9_relat_1(k4_relat_1(sK8),k2_relat_1(sK8))
% 3.69/0.98      | k1_relat_1(sK8) != k1_relat_1(X0) ),
% 3.69/0.98      inference(instantiation,[status(thm)],[c_1517]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_7341,plain,
% 3.69/0.98      ( k9_relat_1(k4_relat_1(sK8),k2_relat_1(sK8)) != k1_relat_1(sK8)
% 3.69/0.98      | k1_relat_1(sK8) = k9_relat_1(k4_relat_1(sK8),k2_relat_1(sK8))
% 3.69/0.98      | k1_relat_1(sK8) != k1_relat_1(sK8) ),
% 3.69/0.98      inference(instantiation,[status(thm)],[c_7339]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_179,plain,
% 3.69/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.69/0.98      theory(equality) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_2134,plain,
% 3.69/0.98      ( r2_hidden(X0,X1)
% 3.69/0.98      | ~ r2_hidden(sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))),k9_relat_1(k4_relat_1(sK8),k2_relat_1(sK8)))
% 3.69/0.98      | X0 != sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8)))
% 3.69/0.98      | X1 != k9_relat_1(k4_relat_1(sK8),k2_relat_1(sK8)) ),
% 3.69/0.98      inference(instantiation,[status(thm)],[c_179]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_2515,plain,
% 3.69/0.98      ( r2_hidden(sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))),X0)
% 3.69/0.98      | ~ r2_hidden(sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))),k9_relat_1(k4_relat_1(sK8),k2_relat_1(sK8)))
% 3.69/0.98      | X0 != k9_relat_1(k4_relat_1(sK8),k2_relat_1(sK8))
% 3.69/0.98      | sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))) != sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))) ),
% 3.69/0.98      inference(instantiation,[status(thm)],[c_2134]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_7340,plain,
% 3.69/0.98      ( ~ r2_hidden(sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))),k9_relat_1(k4_relat_1(sK8),k2_relat_1(sK8)))
% 3.69/0.98      | r2_hidden(sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))),k1_relat_1(sK8))
% 3.69/0.98      | sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8))) != sK5(sK8,sK0(sK8,k1_relat_1(sK8),k2_relat_1(sK8)))
% 3.69/0.98      | k1_relat_1(sK8) != k9_relat_1(k4_relat_1(sK8),k2_relat_1(sK8)) ),
% 3.69/0.98      inference(instantiation,[status(thm)],[c_2515]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_13357,plain,
% 3.69/0.98      ( r2_hidden(sK3(k4_relat_1(sK8),k9_relat_1(k4_relat_1(sK8),k2_relat_1(sK8))),k1_relat_1(sK8)) != iProver_top ),
% 3.69/0.98      inference(global_propositional_subsumption,
% 3.69/0.98                [status(thm)],
% 3.69/0.98                [c_12438,c_18,c_17,c_27,c_189,c_191,c_718,c_731,c_799,
% 3.69/0.98                 c_900,c_911,c_1714,c_2516,c_7341,c_7340]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(c_13364,plain,
% 3.69/0.98      ( k9_relat_1(k4_relat_1(sK8),k2_relat_1(sK8)) = k1_relat_1(sK8) ),
% 3.69/0.98      inference(superposition,[status(thm)],[c_3999,c_13357]) ).
% 3.69/0.98  
% 3.69/0.98  cnf(contradiction,plain,
% 3.69/0.98      ( $false ),
% 3.69/0.98      inference(minisat,
% 3.69/0.98                [status(thm)],
% 3.69/0.98                [c_13364,c_7340,c_7341,c_4747,c_2516,c_1714,c_911,c_900,
% 3.69/0.98                 c_731,c_191,c_189,c_27,c_17,c_18]) ).
% 3.69/0.98  
% 3.69/0.98  
% 3.69/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.69/0.98  
% 3.69/0.98  ------                               Statistics
% 3.69/0.98  
% 3.69/0.98  ------ Selected
% 3.69/0.98  
% 3.69/0.98  total_time:                             0.431
% 3.69/0.98  
%------------------------------------------------------------------------------
