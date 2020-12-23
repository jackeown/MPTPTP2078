%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0476+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:23 EST 2020

% Result     : Theorem 3.08s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 187 expanded)
%              Number of clauses        :   44 (  64 expanded)
%              Number of leaves         :   16 (  47 expanded)
%              Depth                    :   16
%              Number of atoms          :  345 (1030 expanded)
%              Number of equality atoms :  148 ( 367 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   15 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f18,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f15,f18,f17,f16])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f10])).

fof(f12,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( X2 != X3
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( ( X2 = X3
              & r2_hidden(X2,X0) )
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( sK0(X0,X1) != sK1(X0,X1)
          | ~ r2_hidden(sK0(X0,X1),X0)
          | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
        & ( ( sK0(X0,X1) = sK1(X0,X1)
            & r2_hidden(sK0(X0,X1),X0) )
          | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( ( sK0(X0,X1) != sK1(X0,X1)
              | ~ r2_hidden(sK0(X0,X1),X0)
              | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
            & ( ( sK0(X0,X1) = sK1(X0,X1)
                & r2_hidden(sK0(X0,X1),X0) )
              | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).

fof(f28,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f47,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f29,plain,(
    ! [X4,X0,X5,X1] :
      ( X4 = X5
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f46,plain,(
    ! [X4,X0,X5] :
      ( X4 = X5
      | ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f30,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | X4 != X5
      | ~ r2_hidden(X4,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f44,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X5),X1)
      | ~ r2_hidden(X5,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f30])).

fof(f45,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0))
      | ~ r2_hidden(X5,X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f24,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f21,f24,f23,f22])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( k1_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,conjecture,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( k2_relat_1(k6_relat_1(X0)) = X0
        & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f8,plain,(
    ? [X0] :
      ( k2_relat_1(k6_relat_1(X0)) != X0
      | k1_relat_1(k6_relat_1(X0)) != X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,
    ( ? [X0] :
        ( k2_relat_1(k6_relat_1(X0)) != X0
        | k1_relat_1(k6_relat_1(X0)) != X0 )
   => ( k2_relat_1(k6_relat_1(sK8)) != sK8
      | k1_relat_1(k6_relat_1(sK8)) != sK8 ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( k2_relat_1(k6_relat_1(sK8)) != sK8
    | k1_relat_1(k6_relat_1(sK8)) != sK8 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f8,f26])).

fof(f43,plain,
    ( k2_relat_1(k6_relat_1(sK8)) != sK8
    | k1_relat_1(k6_relat_1(sK8)) != sK8 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_398,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1642,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK6(k6_relat_1(sK8),sK8),sK8)
    | X0 != sK6(k6_relat_1(sK8),sK8)
    | X1 != sK8 ),
    inference(instantiation,[status(thm)],[c_398])).

cnf(c_3531,plain,
    ( ~ r2_hidden(sK6(k6_relat_1(sK8),sK8),sK8)
    | r2_hidden(sK5(k6_relat_1(sK8),sK8),X0)
    | X0 != sK8
    | sK5(k6_relat_1(sK8),sK8) != sK6(k6_relat_1(sK8),sK8) ),
    inference(instantiation,[status(thm)],[c_1642])).

cnf(c_3533,plain,
    ( ~ r2_hidden(sK6(k6_relat_1(sK8),sK8),sK8)
    | r2_hidden(sK5(k6_relat_1(sK8),sK8),sK8)
    | sK5(k6_relat_1(sK8),sK8) != sK6(k6_relat_1(sK8),sK8)
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_3531])).

cnf(c_7,plain,
    ( r2_hidden(sK2(X0,X1),X1)
    | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_640,plain,
    ( k1_relat_1(X0) = X1
    | r2_hidden(sK2(X0,X1),X1) = iProver_top
    | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_14,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k6_relat_1(X1))
    | ~ v1_relat_1(k6_relat_1(X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_227,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k6_relat_1(X1))
    | k6_relat_1(X1) != k6_relat_1(X3) ),
    inference(resolution_lifted,[status(thm)],[c_14,c_5])).

cnf(c_630,plain,
    ( k6_relat_1(X0) != k6_relat_1(X1)
    | r2_hidden(X2,X0) = iProver_top
    | r2_hidden(k4_tarski(X2,X3),k6_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_227])).

cnf(c_1736,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k6_relat_1(X1)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_630])).

cnf(c_2775,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X1
    | r2_hidden(sK2(k6_relat_1(X0),X1),X1) = iProver_top
    | r2_hidden(sK2(k6_relat_1(X0),X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_640,c_1736])).

cnf(c_2800,plain,
    ( k1_relat_1(k6_relat_1(sK8)) = sK8
    | r2_hidden(sK2(k6_relat_1(sK8),sK8),sK8) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2775])).

cnf(c_4,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k6_relat_1(X2))
    | ~ v1_relat_1(k6_relat_1(X2))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_255,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k6_relat_1(X2))
    | X1 = X0
    | k6_relat_1(X2) != k6_relat_1(X3) ),
    inference(resolution_lifted,[status(thm)],[c_14,c_4])).

cnf(c_1417,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK5(k6_relat_1(sK8),sK8)),k6_relat_1(X1))
    | sK5(k6_relat_1(sK8),sK8) = X0
    | k6_relat_1(X1) != k6_relat_1(X2) ),
    inference(instantiation,[status(thm)],[c_255])).

cnf(c_2460,plain,
    ( ~ r2_hidden(k4_tarski(sK6(k6_relat_1(sK8),sK8),sK5(k6_relat_1(sK8),sK8)),k6_relat_1(sK8))
    | sK5(k6_relat_1(sK8),sK8) = sK6(k6_relat_1(sK8),sK8)
    | k6_relat_1(sK8) != k6_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1417])).

cnf(c_2461,plain,
    ( sK5(k6_relat_1(sK8),sK8) = sK6(k6_relat_1(sK8),sK8)
    | k6_relat_1(sK8) != k6_relat_1(X0)
    | r2_hidden(k4_tarski(sK6(k6_relat_1(sK8),sK8),sK5(k6_relat_1(sK8),sK8)),k6_relat_1(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2460])).

cnf(c_2463,plain,
    ( sK5(k6_relat_1(sK8),sK8) = sK6(k6_relat_1(sK8),sK8)
    | k6_relat_1(sK8) != k6_relat_1(sK8)
    | r2_hidden(k4_tarski(sK6(k6_relat_1(sK8),sK8),sK5(k6_relat_1(sK8),sK8)),k6_relat_1(sK8)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2461])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(X0,X0),k6_relat_1(X1))
    | ~ v1_relat_1(k6_relat_1(X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_241,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(X0,X0),k6_relat_1(X1))
    | k6_relat_1(X1) != k6_relat_1(X2) ),
    inference(resolution_lifted,[status(thm)],[c_14,c_3])).

cnf(c_629,plain,
    ( k6_relat_1(X0) != k6_relat_1(X1)
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(k4_tarski(X2,X2),k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_241])).

cnf(c_938,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(k4_tarski(X0,X0),k6_relat_1(X1)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_629])).

cnf(c_10,plain,
    ( ~ r2_hidden(sK5(X0,X1),X1)
    | ~ r2_hidden(k4_tarski(X2,sK5(X0,X1)),X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_637,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(sK5(X0,X1),X1) != iProver_top
    | r2_hidden(k4_tarski(X2,sK5(X0,X1)),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1221,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X1
    | r2_hidden(sK5(k6_relat_1(X0),X1),X1) != iProver_top
    | r2_hidden(sK5(k6_relat_1(X0),X1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_938,c_637])).

cnf(c_1249,plain,
    ( ~ r2_hidden(sK5(k6_relat_1(X0),X1),X1)
    | ~ r2_hidden(sK5(k6_relat_1(X0),X1),X0)
    | k2_relat_1(k6_relat_1(X0)) = X1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1221])).

cnf(c_1251,plain,
    ( ~ r2_hidden(sK5(k6_relat_1(sK8),sK8),sK8)
    | k2_relat_1(k6_relat_1(sK8)) = sK8 ),
    inference(instantiation,[status(thm)],[c_1249])).

cnf(c_1250,plain,
    ( k2_relat_1(k6_relat_1(sK8)) = sK8
    | r2_hidden(sK5(k6_relat_1(sK8),sK8),sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1221])).

cnf(c_6,plain,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | ~ r2_hidden(k4_tarski(sK2(X0,X1),X2),X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_641,plain,
    ( k1_relat_1(X0) = X1
    | r2_hidden(sK2(X0,X1),X1) != iProver_top
    | r2_hidden(k4_tarski(sK2(X0,X1),X2),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1219,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X1
    | r2_hidden(sK2(k6_relat_1(X0),X1),X1) != iProver_top
    | r2_hidden(sK2(k6_relat_1(X0),X1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_938,c_641])).

cnf(c_1244,plain,
    ( k1_relat_1(k6_relat_1(sK8)) = sK8
    | r2_hidden(sK2(k6_relat_1(sK8),sK8),sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1219])).

cnf(c_866,plain,
    ( r2_hidden(sK6(k6_relat_1(sK8),sK8),sK8)
    | ~ r2_hidden(k4_tarski(sK6(k6_relat_1(sK8),sK8),sK5(k6_relat_1(sK8),sK8)),k6_relat_1(sK8))
    | k6_relat_1(sK8) != k6_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_227])).

cnf(c_868,plain,
    ( r2_hidden(sK6(k6_relat_1(sK8),sK8),sK8)
    | ~ r2_hidden(k4_tarski(sK6(k6_relat_1(sK8),sK8),sK5(k6_relat_1(sK8),sK8)),k6_relat_1(sK8))
    | k6_relat_1(sK8) != k6_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_866])).

cnf(c_11,plain,
    ( r2_hidden(sK5(X0,X1),X1)
    | r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_784,plain,
    ( r2_hidden(sK5(k6_relat_1(sK8),sK8),sK8)
    | r2_hidden(k4_tarski(sK6(k6_relat_1(sK8),sK8),sK5(k6_relat_1(sK8),sK8)),k6_relat_1(sK8))
    | k2_relat_1(k6_relat_1(sK8)) = sK8 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_785,plain,
    ( k2_relat_1(k6_relat_1(sK8)) = sK8
    | r2_hidden(sK5(k6_relat_1(sK8),sK8),sK8) = iProver_top
    | r2_hidden(k4_tarski(sK6(k6_relat_1(sK8),sK8),sK5(k6_relat_1(sK8),sK8)),k6_relat_1(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_784])).

cnf(c_393,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_410,plain,
    ( sK8 = sK8 ),
    inference(instantiation,[status(thm)],[c_393])).

cnf(c_395,plain,
    ( X0 != X1
    | k6_relat_1(X0) = k6_relat_1(X1) ),
    theory(equality)).

cnf(c_402,plain,
    ( k6_relat_1(sK8) = k6_relat_1(sK8)
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_395])).

cnf(c_15,negated_conjecture,
    ( k2_relat_1(k6_relat_1(sK8)) != sK8
    | k1_relat_1(k6_relat_1(sK8)) != sK8 ),
    inference(cnf_transformation,[],[f43])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3533,c_2800,c_2463,c_1251,c_1250,c_1244,c_868,c_785,c_784,c_410,c_402,c_15])).


%------------------------------------------------------------------------------
