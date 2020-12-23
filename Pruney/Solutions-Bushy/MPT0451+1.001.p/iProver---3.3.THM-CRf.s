%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0451+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:20 EST 2020

% Result     : Theorem 3.41s
% Output     : CNFRefutation 3.41s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 166 expanded)
%              Number of clauses        :   34 (  42 expanded)
%              Number of leaves         :   13 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :  296 ( 826 expanded)
%              Number of equality atoms :   75 ( 173 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f10])).

fof(f14,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK1(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK0(X0,X1),X3),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK0(X0,X1),X4),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK0(X0,X1),X3),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f14,f13,f12])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( k1_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(sK0(X0,X1),X3),X0)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f20,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
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

fof(f21,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f17,f20,f19,f18])).

fof(f33,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f45,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f23,f24])).

fof(f36,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X4),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f48,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X5,X4),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f37,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f47,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f32,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
      | r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
          & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f9,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k4_relat_1(X0))
        | k1_relat_1(k4_relat_1(X0)) != k2_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,
    ( ? [X0] :
        ( ( k1_relat_1(X0) != k2_relat_1(k4_relat_1(X0))
          | k1_relat_1(k4_relat_1(X0)) != k2_relat_1(X0) )
        & v1_relat_1(X0) )
   => ( ( k1_relat_1(sK8) != k2_relat_1(k4_relat_1(sK8))
        | k1_relat_1(k4_relat_1(sK8)) != k2_relat_1(sK8) )
      & v1_relat_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ( k1_relat_1(sK8) != k2_relat_1(k4_relat_1(sK8))
      | k1_relat_1(k4_relat_1(sK8)) != k2_relat_1(sK8) )
    & v1_relat_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f9,f26])).

fof(f42,plain,
    ( k1_relat_1(sK8) != k2_relat_1(k4_relat_1(sK8))
    | k1_relat_1(k4_relat_1(sK8)) != k2_relat_1(sK8) ),
    inference(cnf_transformation,[],[f27])).

fof(f41,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_0,plain,
    ( ~ r2_hidden(k4_tarski(sK0(X0,X1),X2),X0)
    | ~ r2_hidden(sK0(X0,X1),X1)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_579,plain,
    ( ~ r2_hidden(k4_tarski(sK0(sK8,k2_relat_1(k4_relat_1(sK8))),X0),sK8)
    | ~ r2_hidden(sK0(sK8,k2_relat_1(k4_relat_1(sK8))),k2_relat_1(k4_relat_1(sK8)))
    | k1_relat_1(sK8) = k2_relat_1(k4_relat_1(sK8)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_7223,plain,
    ( ~ r2_hidden(k4_tarski(sK0(sK8,k2_relat_1(k4_relat_1(sK8))),sK5(k4_relat_1(sK8),sK0(sK8,k2_relat_1(k4_relat_1(sK8))))),sK8)
    | ~ r2_hidden(sK0(sK8,k2_relat_1(k4_relat_1(sK8))),k2_relat_1(k4_relat_1(sK8)))
    | k1_relat_1(sK8) = k2_relat_1(k4_relat_1(sK8)) ),
    inference(instantiation,[status(thm)],[c_579])).

cnf(c_6,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3239,plain,
    ( ~ r2_hidden(k4_tarski(sK1(sK8,k2_relat_1(k4_relat_1(sK8))),sK0(sK8,k2_relat_1(k4_relat_1(sK8)))),k4_relat_1(sK8))
    | r2_hidden(sK0(sK8,k2_relat_1(k4_relat_1(sK8))),k2_relat_1(k4_relat_1(sK8))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_556,plain,
    ( ~ r2_hidden(k4_tarski(sK0(k4_relat_1(sK8),k2_relat_1(sK8)),X0),k4_relat_1(sK8))
    | ~ r2_hidden(sK0(k4_relat_1(sK8),k2_relat_1(sK8)),k2_relat_1(sK8))
    | k1_relat_1(k4_relat_1(sK8)) = k2_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2931,plain,
    ( ~ r2_hidden(k4_tarski(sK0(k4_relat_1(sK8),k2_relat_1(sK8)),sK5(sK8,sK0(k4_relat_1(sK8),k2_relat_1(sK8)))),k4_relat_1(sK8))
    | ~ r2_hidden(sK0(k4_relat_1(sK8),k2_relat_1(sK8)),k2_relat_1(sK8))
    | k1_relat_1(k4_relat_1(sK8)) = k2_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_556])).

cnf(c_2932,plain,
    ( k1_relat_1(k4_relat_1(sK8)) = k2_relat_1(sK8)
    | r2_hidden(k4_tarski(sK0(k4_relat_1(sK8),k2_relat_1(sK8)),sK5(sK8,sK0(k4_relat_1(sK8),k2_relat_1(sK8)))),k4_relat_1(sK8)) != iProver_top
    | r2_hidden(sK0(k4_relat_1(sK8),k2_relat_1(sK8)),k2_relat_1(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2931])).

cnf(c_1873,plain,
    ( ~ r2_hidden(k4_tarski(sK1(k4_relat_1(sK8),k2_relat_1(sK8)),sK0(k4_relat_1(sK8),k2_relat_1(sK8))),sK8)
    | r2_hidden(sK0(k4_relat_1(sK8),k2_relat_1(sK8)),k2_relat_1(sK8)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1874,plain,
    ( r2_hidden(k4_tarski(sK1(k4_relat_1(sK8),k2_relat_1(sK8)),sK0(k4_relat_1(sK8),k2_relat_1(sK8))),sK8) != iProver_top
    | r2_hidden(sK0(k4_relat_1(sK8),k2_relat_1(sK8)),k2_relat_1(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1873])).

cnf(c_11,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X1,X0),k4_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k4_relat_1(X2)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1501,plain,
    ( ~ r2_hidden(k4_tarski(sK5(k4_relat_1(sK8),sK0(sK8,k2_relat_1(k4_relat_1(sK8)))),sK0(sK8,k2_relat_1(k4_relat_1(sK8)))),k4_relat_1(sK8))
    | r2_hidden(k4_tarski(sK0(sK8,k2_relat_1(k4_relat_1(sK8))),sK5(k4_relat_1(sK8),sK0(sK8,k2_relat_1(k4_relat_1(sK8))))),sK8)
    | ~ v1_relat_1(k4_relat_1(sK8))
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | r2_hidden(k4_tarski(X1,X0),k4_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k4_relat_1(X2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_996,plain,
    ( r2_hidden(k4_tarski(sK1(sK8,k2_relat_1(k4_relat_1(sK8))),sK0(sK8,k2_relat_1(k4_relat_1(sK8)))),k4_relat_1(sK8))
    | ~ r2_hidden(k4_tarski(sK0(sK8,k2_relat_1(k4_relat_1(sK8))),sK1(sK8,k2_relat_1(k4_relat_1(sK8)))),sK8)
    | ~ v1_relat_1(k4_relat_1(sK8))
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_699,plain,
    ( ~ r2_hidden(k4_tarski(sK5(sK8,sK0(k4_relat_1(sK8),k2_relat_1(sK8))),sK0(k4_relat_1(sK8),k2_relat_1(sK8))),sK8)
    | r2_hidden(k4_tarski(sK0(k4_relat_1(sK8),k2_relat_1(sK8)),sK5(sK8,sK0(k4_relat_1(sK8),k2_relat_1(sK8)))),k4_relat_1(sK8))
    | ~ v1_relat_1(k4_relat_1(sK8))
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_700,plain,
    ( r2_hidden(k4_tarski(sK5(sK8,sK0(k4_relat_1(sK8),k2_relat_1(sK8))),sK0(k4_relat_1(sK8),k2_relat_1(sK8))),sK8) != iProver_top
    | r2_hidden(k4_tarski(sK0(k4_relat_1(sK8),k2_relat_1(sK8)),sK5(sK8,sK0(k4_relat_1(sK8),k2_relat_1(sK8)))),k4_relat_1(sK8)) = iProver_top
    | v1_relat_1(k4_relat_1(sK8)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_699])).

cnf(c_623,plain,
    ( r2_hidden(k4_tarski(sK1(k4_relat_1(sK8),k2_relat_1(sK8)),sK0(k4_relat_1(sK8),k2_relat_1(sK8))),sK8)
    | ~ r2_hidden(k4_tarski(sK0(k4_relat_1(sK8),k2_relat_1(sK8)),sK1(k4_relat_1(sK8),k2_relat_1(sK8))),k4_relat_1(sK8))
    | ~ v1_relat_1(k4_relat_1(sK8))
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_624,plain,
    ( r2_hidden(k4_tarski(sK1(k4_relat_1(sK8),k2_relat_1(sK8)),sK0(k4_relat_1(sK8),k2_relat_1(sK8))),sK8) = iProver_top
    | r2_hidden(k4_tarski(sK0(k4_relat_1(sK8),k2_relat_1(sK8)),sK1(k4_relat_1(sK8),k2_relat_1(sK8))),k4_relat_1(sK8)) != iProver_top
    | v1_relat_1(k4_relat_1(sK8)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_623])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK5(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_588,plain,
    ( r2_hidden(k4_tarski(sK5(k4_relat_1(sK8),sK0(sK8,k2_relat_1(k4_relat_1(sK8)))),sK0(sK8,k2_relat_1(k4_relat_1(sK8)))),k4_relat_1(sK8))
    | ~ r2_hidden(sK0(sK8,k2_relat_1(k4_relat_1(sK8))),k2_relat_1(k4_relat_1(sK8))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1,plain,
    ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
    | r2_hidden(sK0(X0,X1),X1)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_578,plain,
    ( r2_hidden(k4_tarski(sK0(sK8,k2_relat_1(k4_relat_1(sK8))),sK1(sK8,k2_relat_1(k4_relat_1(sK8)))),sK8)
    | r2_hidden(sK0(sK8,k2_relat_1(k4_relat_1(sK8))),k2_relat_1(k4_relat_1(sK8)))
    | k1_relat_1(sK8) = k2_relat_1(k4_relat_1(sK8)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_570,plain,
    ( r2_hidden(k4_tarski(sK5(sK8,sK0(k4_relat_1(sK8),k2_relat_1(sK8))),sK0(k4_relat_1(sK8),k2_relat_1(sK8))),sK8)
    | ~ r2_hidden(sK0(k4_relat_1(sK8),k2_relat_1(sK8)),k2_relat_1(sK8)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_571,plain,
    ( r2_hidden(k4_tarski(sK5(sK8,sK0(k4_relat_1(sK8),k2_relat_1(sK8))),sK0(k4_relat_1(sK8),k2_relat_1(sK8))),sK8) = iProver_top
    | r2_hidden(sK0(k4_relat_1(sK8),k2_relat_1(sK8)),k2_relat_1(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_570])).

cnf(c_561,plain,
    ( r2_hidden(k4_tarski(sK0(k4_relat_1(sK8),k2_relat_1(sK8)),sK1(k4_relat_1(sK8),k2_relat_1(sK8))),k4_relat_1(sK8))
    | r2_hidden(sK0(k4_relat_1(sK8),k2_relat_1(sK8)),k2_relat_1(sK8))
    | k1_relat_1(k4_relat_1(sK8)) = k2_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_562,plain,
    ( k1_relat_1(k4_relat_1(sK8)) = k2_relat_1(sK8)
    | r2_hidden(k4_tarski(sK0(k4_relat_1(sK8),k2_relat_1(sK8)),sK1(k4_relat_1(sK8),k2_relat_1(sK8))),k4_relat_1(sK8)) = iProver_top
    | r2_hidden(sK0(k4_relat_1(sK8),k2_relat_1(sK8)),k2_relat_1(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_561])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_16,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_18,plain,
    ( v1_relat_1(k4_relat_1(sK8)) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_17,plain,
    ( v1_relat_1(k4_relat_1(sK8))
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_13,negated_conjecture,
    ( k1_relat_1(k4_relat_1(sK8)) != k2_relat_1(sK8)
    | k1_relat_1(sK8) != k2_relat_1(k4_relat_1(sK8)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_15,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7223,c_3239,c_2932,c_1874,c_1501,c_996,c_700,c_624,c_588,c_578,c_571,c_562,c_18,c_17,c_13,c_15,c_14])).


%------------------------------------------------------------------------------
