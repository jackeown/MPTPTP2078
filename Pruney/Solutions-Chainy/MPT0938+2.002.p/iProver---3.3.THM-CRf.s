%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:39 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 394 expanded)
%              Number of clauses        :   83 ( 140 expanded)
%              Number of leaves         :   12 (  74 expanded)
%              Depth                    :   19
%              Number of atoms          :  460 (1841 expanded)
%              Number of equality atoms :  152 ( 356 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   17 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) )
           => r2_hidden(k4_tarski(X1,X3),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f20,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ? [X1,X2,X3] :
              ( ~ r2_hidden(k4_tarski(X1,X3),X0)
              & r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X1,X2,X3] :
              ( r2_hidden(k4_tarski(X1,X3),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(k4_tarski(X1,X2),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f21,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ? [X1,X2,X3] :
              ( ~ r2_hidden(k4_tarski(X1,X3),X0)
              & r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X4,X5,X6] :
              ( r2_hidden(k4_tarski(X4,X6),X0)
              | ~ r2_hidden(k4_tarski(X5,X6),X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r2_hidden(k4_tarski(X1,X3),X0)
          & r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(k4_tarski(X1,X2),X0) )
     => ( ~ r2_hidden(k4_tarski(sK1(X0),sK3(X0)),X0)
        & r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
        & r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK1(X0),sK3(X0)),X0)
            & r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
            & r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) ) )
        & ( ! [X4,X5,X6] :
              ( r2_hidden(k4_tarski(X4,X6),X0)
              | ~ r2_hidden(k4_tarski(X5,X6),X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f21,f22])).

fof(f37,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK4(X0,X1),sK5(X0,X1))
          | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) )
        & ( r1_tarski(sK4(X0,X1),sK5(X0,X1))
          | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) )
        & r2_hidden(sK5(X0,X1),X0)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK4(X0,X1),sK5(X0,X1))
              | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) )
            & ( r1_tarski(sK4(X0,X1),sK5(X0,X1))
              | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) )
            & r2_hidden(sK5(X0,X1),X0)
            & r2_hidden(sK4(X0,X1),X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f26,f27])).

fof(f41,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_tarski(X4,X5)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f54,plain,(
    ! [X4,X0,X5] :
      ( r1_tarski(X4,X5)
      | ~ r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f55,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f38,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f16])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f42,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f53,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f39,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | ~ r2_hidden(k4_tarski(sK1(X0),sK3(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,conjecture,(
    ! [X0] : v8_relat_2(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] : v8_relat_2(k1_wellord2(X0)) ),
    inference(negated_conjecture,[],[f6])).

fof(f15,plain,(
    ? [X0] : ~ v8_relat_2(k1_wellord2(X0)) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,
    ( ? [X0] : ~ v8_relat_2(k1_wellord2(X0))
   => ~ v8_relat_2(k1_wellord2(sK6)) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ~ v8_relat_2(k1_wellord2(sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f15,f29])).

fof(f48,plain,(
    ~ v8_relat_2(k1_wellord2(sK6)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_7,plain,
    ( r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
    | v8_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_16,plain,
    ( v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_387,plain,
    ( r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
    | v8_relat_2(X0)
    | k1_wellord2(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_16])).

cnf(c_388,plain,
    ( r2_hidden(k4_tarski(sK1(k1_wellord2(X0)),sK2(k1_wellord2(X0))),k1_wellord2(X0))
    | v8_relat_2(k1_wellord2(X0)) ),
    inference(unflattening,[status(thm)],[c_387])).

cnf(c_1673,plain,
    ( r2_hidden(k4_tarski(sK1(k1_wellord2(X0)),sK2(k1_wellord2(X0))),k1_wellord2(X0)) = iProver_top
    | v8_relat_2(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_388])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1))
    | r1_tarski(X2,X0)
    | ~ v1_relat_1(k1_wellord2(X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_433,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1))
    | r1_tarski(X2,X0)
    | k1_wellord2(X1) != k1_wellord2(X3) ),
    inference(resolution_lifted,[status(thm)],[c_16,c_14])).

cnf(c_1669,plain,
    ( k1_wellord2(X0) != k1_wellord2(X1)
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X3,X0) != iProver_top
    | r2_hidden(k4_tarski(X3,X2),k1_wellord2(X0)) != iProver_top
    | r1_tarski(X3,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_433])).

cnf(c_4,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_311,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | k1_wellord2(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_16])).

cnf(c_312,plain,
    ( r2_hidden(X0,k3_relat_1(k1_wellord2(X1)))
    | ~ r2_hidden(k4_tarski(X0,X2),k1_wellord2(X1)) ),
    inference(unflattening,[status(thm)],[c_311])).

cnf(c_1679,plain,
    ( r2_hidden(X0,k3_relat_1(k1_wellord2(X1))) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k1_wellord2(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_312])).

cnf(c_15,plain,
    ( ~ v1_relat_1(k1_wellord2(X0))
    | k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_103,plain,
    ( k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_16])).

cnf(c_1701,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k1_wellord2(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1679,c_103])).

cnf(c_3,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_323,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | k1_wellord2(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_16])).

cnf(c_324,plain,
    ( r2_hidden(X0,k3_relat_1(k1_wellord2(X1)))
    | ~ r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1)) ),
    inference(unflattening,[status(thm)],[c_323])).

cnf(c_1678,plain,
    ( r2_hidden(X0,k3_relat_1(k1_wellord2(X1))) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_324])).

cnf(c_1696,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1678,c_103])).

cnf(c_1749,plain,
    ( k1_wellord2(X0) != k1_wellord2(X1)
    | r2_hidden(k4_tarski(X2,X3),k1_wellord2(X1)) != iProver_top
    | r1_tarski(X2,X3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1669,c_1701,c_1696])).

cnf(c_1995,plain,
    ( r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1749])).

cnf(c_3771,plain,
    ( r1_tarski(sK1(k1_wellord2(X0)),sK2(k1_wellord2(X0))) = iProver_top
    | v8_relat_2(k1_wellord2(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1673,c_1995])).

cnf(c_6,plain,
    ( r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
    | v8_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_397,plain,
    ( r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
    | v8_relat_2(X0)
    | k1_wellord2(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_16])).

cnf(c_398,plain,
    ( r2_hidden(k4_tarski(sK2(k1_wellord2(X0)),sK3(k1_wellord2(X0))),k1_wellord2(X0))
    | v8_relat_2(k1_wellord2(X0)) ),
    inference(unflattening,[status(thm)],[c_397])).

cnf(c_1672,plain,
    ( r2_hidden(k4_tarski(sK2(k1_wellord2(X0)),sK3(k1_wellord2(X0))),k1_wellord2(X0)) = iProver_top
    | v8_relat_2(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_398])).

cnf(c_3002,plain,
    ( r1_tarski(sK2(k1_wellord2(X0)),sK3(k1_wellord2(X0))) = iProver_top
    | v8_relat_2(k1_wellord2(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1672,c_1995])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1682,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_1681,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2134,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1682,c_1681])).

cnf(c_2253,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | r1_tarski(X3,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2134,c_1681])).

cnf(c_3702,plain,
    ( r2_hidden(sK0(X0,X1),sK3(k1_wellord2(X2))) = iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,sK2(k1_wellord2(X2))) != iProver_top
    | v8_relat_2(k1_wellord2(X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3002,c_2253])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1683,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5164,plain,
    ( r1_tarski(X0,sK2(k1_wellord2(X1))) != iProver_top
    | r1_tarski(X0,sK3(k1_wellord2(X1))) = iProver_top
    | v8_relat_2(k1_wellord2(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3702,c_1683])).

cnf(c_5211,plain,
    ( r1_tarski(sK1(k1_wellord2(X0)),sK3(k1_wellord2(X0))) = iProver_top
    | v8_relat_2(k1_wellord2(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3771,c_5164])).

cnf(c_5217,plain,
    ( r1_tarski(sK1(k1_wellord2(sK6)),sK3(k1_wellord2(sK6))) = iProver_top
    | v8_relat_2(k1_wellord2(sK6)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5211])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1))
    | ~ r1_tarski(X2,X0)
    | ~ v1_relat_1(k1_wellord2(X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_453,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1))
    | ~ r1_tarski(X2,X0)
    | k1_wellord2(X1) != k1_wellord2(X3) ),
    inference(resolution_lifted,[status(thm)],[c_16,c_13])).

cnf(c_1668,plain,
    ( k1_wellord2(X0) != k1_wellord2(X1)
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X3,X0) != iProver_top
    | r2_hidden(k4_tarski(X3,X2),k1_wellord2(X0)) = iProver_top
    | r1_tarski(X3,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_453])).

cnf(c_2126,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1)) = iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1668])).

cnf(c_5,plain,
    ( ~ r2_hidden(k4_tarski(sK1(X0),sK3(X0)),X0)
    | v8_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_407,plain,
    ( ~ r2_hidden(k4_tarski(sK1(X0),sK3(X0)),X0)
    | v8_relat_2(X0)
    | k1_wellord2(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_16])).

cnf(c_408,plain,
    ( ~ r2_hidden(k4_tarski(sK1(k1_wellord2(X0)),sK3(k1_wellord2(X0))),k1_wellord2(X0))
    | v8_relat_2(k1_wellord2(X0)) ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_1671,plain,
    ( r2_hidden(k4_tarski(sK1(k1_wellord2(X0)),sK3(k1_wellord2(X0))),k1_wellord2(X0)) != iProver_top
    | v8_relat_2(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_408])).

cnf(c_2464,plain,
    ( r2_hidden(sK3(k1_wellord2(X0)),X0) != iProver_top
    | r2_hidden(sK1(k1_wellord2(X0)),X0) != iProver_top
    | r1_tarski(sK1(k1_wellord2(X0)),sK3(k1_wellord2(X0))) != iProver_top
    | v8_relat_2(k1_wellord2(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2126,c_1671])).

cnf(c_2488,plain,
    ( r2_hidden(sK3(k1_wellord2(sK6)),sK6) != iProver_top
    | r2_hidden(sK1(k1_wellord2(sK6)),sK6) != iProver_top
    | r1_tarski(sK1(k1_wellord2(sK6)),sK3(k1_wellord2(sK6))) != iProver_top
    | v8_relat_2(k1_wellord2(sK6)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2464])).

cnf(c_2133,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1682,c_1683])).

cnf(c_2144,plain,
    ( r1_tarski(sK6,sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2133])).

cnf(c_1363,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2032,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_relat_1(k1_wellord2(X2)),X3)
    | X3 != X1
    | k3_relat_1(k1_wellord2(X2)) != X0 ),
    inference(instantiation,[status(thm)],[c_1363])).

cnf(c_2033,plain,
    ( X0 != X1
    | k3_relat_1(k1_wellord2(X2)) != X3
    | r1_tarski(X3,X1) != iProver_top
    | r1_tarski(k3_relat_1(k1_wellord2(X2)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2032])).

cnf(c_2035,plain,
    ( k3_relat_1(k1_wellord2(sK6)) != sK6
    | sK6 != sK6
    | r1_tarski(k3_relat_1(k1_wellord2(sK6)),sK6) = iProver_top
    | r1_tarski(sK6,sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2033])).

cnf(c_1889,plain,
    ( r2_hidden(sK3(k1_wellord2(X0)),X1)
    | ~ r2_hidden(sK3(k1_wellord2(X0)),k3_relat_1(k1_wellord2(X0)))
    | ~ r1_tarski(k3_relat_1(k1_wellord2(X0)),X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1895,plain,
    ( r2_hidden(sK3(k1_wellord2(X0)),X1) = iProver_top
    | r2_hidden(sK3(k1_wellord2(X0)),k3_relat_1(k1_wellord2(X0))) != iProver_top
    | r1_tarski(k3_relat_1(k1_wellord2(X0)),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1889])).

cnf(c_1897,plain,
    ( r2_hidden(sK3(k1_wellord2(sK6)),k3_relat_1(k1_wellord2(sK6))) != iProver_top
    | r2_hidden(sK3(k1_wellord2(sK6)),sK6) = iProver_top
    | r1_tarski(k3_relat_1(k1_wellord2(sK6)),sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1895])).

cnf(c_1856,plain,
    ( r2_hidden(sK1(k1_wellord2(X0)),X1)
    | ~ r2_hidden(sK1(k1_wellord2(X0)),k3_relat_1(k1_wellord2(X0)))
    | ~ r1_tarski(k3_relat_1(k1_wellord2(X0)),X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1862,plain,
    ( r2_hidden(sK1(k1_wellord2(X0)),X1) = iProver_top
    | r2_hidden(sK1(k1_wellord2(X0)),k3_relat_1(k1_wellord2(X0))) != iProver_top
    | r1_tarski(k3_relat_1(k1_wellord2(X0)),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1856])).

cnf(c_1864,plain,
    ( r2_hidden(sK1(k1_wellord2(sK6)),k3_relat_1(k1_wellord2(sK6))) != iProver_top
    | r2_hidden(sK1(k1_wellord2(sK6)),sK6) = iProver_top
    | r1_tarski(k3_relat_1(k1_wellord2(sK6)),sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1862])).

cnf(c_1805,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k1_wellord2(X0)),sK3(k1_wellord2(X0))),k1_wellord2(X0))
    | r2_hidden(sK3(k1_wellord2(X0)),k3_relat_1(k1_wellord2(X0))) ),
    inference(instantiation,[status(thm)],[c_324])).

cnf(c_1806,plain,
    ( r2_hidden(k4_tarski(sK2(k1_wellord2(X0)),sK3(k1_wellord2(X0))),k1_wellord2(X0)) != iProver_top
    | r2_hidden(sK3(k1_wellord2(X0)),k3_relat_1(k1_wellord2(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1805])).

cnf(c_1808,plain,
    ( r2_hidden(k4_tarski(sK2(k1_wellord2(sK6)),sK3(k1_wellord2(sK6))),k1_wellord2(sK6)) != iProver_top
    | r2_hidden(sK3(k1_wellord2(sK6)),k3_relat_1(k1_wellord2(sK6))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1806])).

cnf(c_1790,plain,
    ( ~ r2_hidden(k4_tarski(sK1(k1_wellord2(X0)),sK2(k1_wellord2(X0))),k1_wellord2(X0))
    | r2_hidden(sK1(k1_wellord2(X0)),k3_relat_1(k1_wellord2(X0))) ),
    inference(instantiation,[status(thm)],[c_312])).

cnf(c_1791,plain,
    ( r2_hidden(k4_tarski(sK1(k1_wellord2(X0)),sK2(k1_wellord2(X0))),k1_wellord2(X0)) != iProver_top
    | r2_hidden(sK1(k1_wellord2(X0)),k3_relat_1(k1_wellord2(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1790])).

cnf(c_1793,plain,
    ( r2_hidden(k4_tarski(sK1(k1_wellord2(sK6)),sK2(k1_wellord2(sK6))),k1_wellord2(sK6)) != iProver_top
    | r2_hidden(sK1(k1_wellord2(sK6)),k3_relat_1(k1_wellord2(sK6))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1791])).

cnf(c_1361,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1386,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_1361])).

cnf(c_17,negated_conjecture,
    ( ~ v8_relat_2(k1_wellord2(sK6)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_271,plain,
    ( r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
    | ~ v1_relat_1(X0)
    | k1_wellord2(sK6) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_17])).

cnf(c_272,plain,
    ( r2_hidden(k4_tarski(sK2(k1_wellord2(sK6)),sK3(k1_wellord2(sK6))),k1_wellord2(sK6))
    | ~ v1_relat_1(k1_wellord2(sK6)) ),
    inference(unflattening,[status(thm)],[c_271])).

cnf(c_273,plain,
    ( r2_hidden(k4_tarski(sK2(k1_wellord2(sK6)),sK3(k1_wellord2(sK6))),k1_wellord2(sK6)) = iProver_top
    | v1_relat_1(k1_wellord2(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_272])).

cnf(c_260,plain,
    ( r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
    | ~ v1_relat_1(X0)
    | k1_wellord2(sK6) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_17])).

cnf(c_261,plain,
    ( r2_hidden(k4_tarski(sK1(k1_wellord2(sK6)),sK2(k1_wellord2(sK6))),k1_wellord2(sK6))
    | ~ v1_relat_1(k1_wellord2(sK6)) ),
    inference(unflattening,[status(thm)],[c_260])).

cnf(c_262,plain,
    ( r2_hidden(k4_tarski(sK1(k1_wellord2(sK6)),sK2(k1_wellord2(sK6))),k1_wellord2(sK6)) = iProver_top
    | v1_relat_1(k1_wellord2(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_261])).

cnf(c_23,plain,
    ( ~ v1_relat_1(k1_wellord2(sK6))
    | k3_relat_1(k1_wellord2(sK6)) = sK6 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_19,plain,
    ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_21,plain,
    ( v1_relat_1(k1_wellord2(sK6)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_20,plain,
    ( v1_relat_1(k1_wellord2(sK6)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_18,plain,
    ( v8_relat_2(k1_wellord2(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5217,c_2488,c_2144,c_2035,c_1897,c_1864,c_1808,c_1793,c_1386,c_273,c_262,c_23,c_21,c_20,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.01/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:06:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.34/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.00  
% 2.34/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.34/1.00  
% 2.34/1.00  ------  iProver source info
% 2.34/1.00  
% 2.34/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.34/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.34/1.00  git: non_committed_changes: false
% 2.34/1.00  git: last_make_outside_of_git: false
% 2.34/1.00  
% 2.34/1.00  ------ 
% 2.34/1.00  
% 2.34/1.00  ------ Input Options
% 2.34/1.00  
% 2.34/1.00  --out_options                           all
% 2.34/1.00  --tptp_safe_out                         true
% 2.34/1.00  --problem_path                          ""
% 2.34/1.00  --include_path                          ""
% 2.34/1.00  --clausifier                            res/vclausify_rel
% 2.34/1.00  --clausifier_options                    --mode clausify
% 2.34/1.00  --stdin                                 false
% 2.34/1.00  --stats_out                             all
% 2.34/1.00  
% 2.34/1.00  ------ General Options
% 2.34/1.00  
% 2.34/1.00  --fof                                   false
% 2.34/1.00  --time_out_real                         305.
% 2.34/1.00  --time_out_virtual                      -1.
% 2.34/1.00  --symbol_type_check                     false
% 2.34/1.00  --clausify_out                          false
% 2.34/1.00  --sig_cnt_out                           false
% 2.34/1.00  --trig_cnt_out                          false
% 2.34/1.00  --trig_cnt_out_tolerance                1.
% 2.34/1.00  --trig_cnt_out_sk_spl                   false
% 2.34/1.00  --abstr_cl_out                          false
% 2.34/1.00  
% 2.34/1.00  ------ Global Options
% 2.34/1.00  
% 2.34/1.00  --schedule                              default
% 2.34/1.00  --add_important_lit                     false
% 2.34/1.00  --prop_solver_per_cl                    1000
% 2.34/1.00  --min_unsat_core                        false
% 2.34/1.00  --soft_assumptions                      false
% 2.34/1.00  --soft_lemma_size                       3
% 2.34/1.00  --prop_impl_unit_size                   0
% 2.34/1.00  --prop_impl_unit                        []
% 2.34/1.00  --share_sel_clauses                     true
% 2.34/1.00  --reset_solvers                         false
% 2.34/1.00  --bc_imp_inh                            [conj_cone]
% 2.34/1.00  --conj_cone_tolerance                   3.
% 2.34/1.00  --extra_neg_conj                        none
% 2.34/1.00  --large_theory_mode                     true
% 2.34/1.00  --prolific_symb_bound                   200
% 2.34/1.00  --lt_threshold                          2000
% 2.34/1.00  --clause_weak_htbl                      true
% 2.34/1.00  --gc_record_bc_elim                     false
% 2.34/1.00  
% 2.34/1.00  ------ Preprocessing Options
% 2.34/1.00  
% 2.34/1.00  --preprocessing_flag                    true
% 2.34/1.00  --time_out_prep_mult                    0.1
% 2.34/1.00  --splitting_mode                        input
% 2.34/1.00  --splitting_grd                         true
% 2.34/1.00  --splitting_cvd                         false
% 2.34/1.00  --splitting_cvd_svl                     false
% 2.34/1.00  --splitting_nvd                         32
% 2.34/1.00  --sub_typing                            true
% 2.34/1.00  --prep_gs_sim                           true
% 2.34/1.00  --prep_unflatten                        true
% 2.34/1.00  --prep_res_sim                          true
% 2.34/1.00  --prep_upred                            true
% 2.34/1.00  --prep_sem_filter                       exhaustive
% 2.34/1.00  --prep_sem_filter_out                   false
% 2.34/1.00  --pred_elim                             true
% 2.34/1.00  --res_sim_input                         true
% 2.34/1.00  --eq_ax_congr_red                       true
% 2.34/1.00  --pure_diseq_elim                       true
% 2.34/1.00  --brand_transform                       false
% 2.34/1.00  --non_eq_to_eq                          false
% 2.34/1.00  --prep_def_merge                        true
% 2.34/1.00  --prep_def_merge_prop_impl              false
% 2.34/1.00  --prep_def_merge_mbd                    true
% 2.34/1.00  --prep_def_merge_tr_red                 false
% 2.34/1.00  --prep_def_merge_tr_cl                  false
% 2.34/1.00  --smt_preprocessing                     true
% 2.34/1.00  --smt_ac_axioms                         fast
% 2.34/1.00  --preprocessed_out                      false
% 2.34/1.00  --preprocessed_stats                    false
% 2.34/1.00  
% 2.34/1.00  ------ Abstraction refinement Options
% 2.34/1.00  
% 2.34/1.00  --abstr_ref                             []
% 2.34/1.00  --abstr_ref_prep                        false
% 2.34/1.00  --abstr_ref_until_sat                   false
% 2.34/1.00  --abstr_ref_sig_restrict                funpre
% 2.34/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.34/1.00  --abstr_ref_under                       []
% 2.34/1.00  
% 2.34/1.00  ------ SAT Options
% 2.34/1.00  
% 2.34/1.00  --sat_mode                              false
% 2.34/1.00  --sat_fm_restart_options                ""
% 2.34/1.00  --sat_gr_def                            false
% 2.34/1.00  --sat_epr_types                         true
% 2.34/1.00  --sat_non_cyclic_types                  false
% 2.34/1.00  --sat_finite_models                     false
% 2.34/1.00  --sat_fm_lemmas                         false
% 2.34/1.00  --sat_fm_prep                           false
% 2.34/1.00  --sat_fm_uc_incr                        true
% 2.34/1.00  --sat_out_model                         small
% 2.34/1.00  --sat_out_clauses                       false
% 2.34/1.00  
% 2.34/1.00  ------ QBF Options
% 2.34/1.00  
% 2.34/1.00  --qbf_mode                              false
% 2.34/1.00  --qbf_elim_univ                         false
% 2.34/1.00  --qbf_dom_inst                          none
% 2.34/1.00  --qbf_dom_pre_inst                      false
% 2.34/1.00  --qbf_sk_in                             false
% 2.34/1.00  --qbf_pred_elim                         true
% 2.34/1.00  --qbf_split                             512
% 2.34/1.00  
% 2.34/1.00  ------ BMC1 Options
% 2.34/1.00  
% 2.34/1.00  --bmc1_incremental                      false
% 2.34/1.00  --bmc1_axioms                           reachable_all
% 2.34/1.00  --bmc1_min_bound                        0
% 2.34/1.00  --bmc1_max_bound                        -1
% 2.34/1.00  --bmc1_max_bound_default                -1
% 2.34/1.00  --bmc1_symbol_reachability              true
% 2.34/1.00  --bmc1_property_lemmas                  false
% 2.34/1.00  --bmc1_k_induction                      false
% 2.34/1.00  --bmc1_non_equiv_states                 false
% 2.34/1.00  --bmc1_deadlock                         false
% 2.34/1.00  --bmc1_ucm                              false
% 2.34/1.00  --bmc1_add_unsat_core                   none
% 2.34/1.00  --bmc1_unsat_core_children              false
% 2.34/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.34/1.00  --bmc1_out_stat                         full
% 2.34/1.00  --bmc1_ground_init                      false
% 2.34/1.00  --bmc1_pre_inst_next_state              false
% 2.34/1.00  --bmc1_pre_inst_state                   false
% 2.34/1.00  --bmc1_pre_inst_reach_state             false
% 2.34/1.00  --bmc1_out_unsat_core                   false
% 2.34/1.00  --bmc1_aig_witness_out                  false
% 2.34/1.00  --bmc1_verbose                          false
% 2.34/1.00  --bmc1_dump_clauses_tptp                false
% 2.34/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.34/1.00  --bmc1_dump_file                        -
% 2.34/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.34/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.34/1.00  --bmc1_ucm_extend_mode                  1
% 2.34/1.00  --bmc1_ucm_init_mode                    2
% 2.34/1.00  --bmc1_ucm_cone_mode                    none
% 2.34/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.34/1.00  --bmc1_ucm_relax_model                  4
% 2.34/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.34/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.34/1.00  --bmc1_ucm_layered_model                none
% 2.34/1.00  --bmc1_ucm_max_lemma_size               10
% 2.34/1.00  
% 2.34/1.00  ------ AIG Options
% 2.34/1.00  
% 2.34/1.00  --aig_mode                              false
% 2.34/1.00  
% 2.34/1.00  ------ Instantiation Options
% 2.34/1.00  
% 2.34/1.00  --instantiation_flag                    true
% 2.34/1.00  --inst_sos_flag                         false
% 2.34/1.00  --inst_sos_phase                        true
% 2.34/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.34/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.34/1.00  --inst_lit_sel_side                     num_symb
% 2.34/1.00  --inst_solver_per_active                1400
% 2.34/1.00  --inst_solver_calls_frac                1.
% 2.34/1.00  --inst_passive_queue_type               priority_queues
% 2.34/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.34/1.00  --inst_passive_queues_freq              [25;2]
% 2.34/1.00  --inst_dismatching                      true
% 2.34/1.00  --inst_eager_unprocessed_to_passive     true
% 2.34/1.00  --inst_prop_sim_given                   true
% 2.34/1.00  --inst_prop_sim_new                     false
% 2.34/1.00  --inst_subs_new                         false
% 2.34/1.00  --inst_eq_res_simp                      false
% 2.34/1.00  --inst_subs_given                       false
% 2.34/1.00  --inst_orphan_elimination               true
% 2.34/1.00  --inst_learning_loop_flag               true
% 2.34/1.00  --inst_learning_start                   3000
% 2.34/1.00  --inst_learning_factor                  2
% 2.34/1.00  --inst_start_prop_sim_after_learn       3
% 2.34/1.00  --inst_sel_renew                        solver
% 2.34/1.00  --inst_lit_activity_flag                true
% 2.34/1.00  --inst_restr_to_given                   false
% 2.34/1.00  --inst_activity_threshold               500
% 2.34/1.00  --inst_out_proof                        true
% 2.34/1.00  
% 2.34/1.00  ------ Resolution Options
% 2.34/1.00  
% 2.34/1.00  --resolution_flag                       true
% 2.34/1.00  --res_lit_sel                           adaptive
% 2.34/1.00  --res_lit_sel_side                      none
% 2.34/1.00  --res_ordering                          kbo
% 2.34/1.00  --res_to_prop_solver                    active
% 2.34/1.00  --res_prop_simpl_new                    false
% 2.34/1.00  --res_prop_simpl_given                  true
% 2.34/1.00  --res_passive_queue_type                priority_queues
% 2.34/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.34/1.00  --res_passive_queues_freq               [15;5]
% 2.34/1.00  --res_forward_subs                      full
% 2.34/1.00  --res_backward_subs                     full
% 2.34/1.00  --res_forward_subs_resolution           true
% 2.34/1.00  --res_backward_subs_resolution          true
% 2.34/1.00  --res_orphan_elimination                true
% 2.34/1.00  --res_time_limit                        2.
% 2.34/1.00  --res_out_proof                         true
% 2.34/1.00  
% 2.34/1.00  ------ Superposition Options
% 2.34/1.00  
% 2.34/1.00  --superposition_flag                    true
% 2.34/1.00  --sup_passive_queue_type                priority_queues
% 2.34/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.34/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.34/1.00  --demod_completeness_check              fast
% 2.34/1.00  --demod_use_ground                      true
% 2.34/1.00  --sup_to_prop_solver                    passive
% 2.34/1.00  --sup_prop_simpl_new                    true
% 2.34/1.00  --sup_prop_simpl_given                  true
% 2.34/1.00  --sup_fun_splitting                     false
% 2.34/1.00  --sup_smt_interval                      50000
% 2.34/1.00  
% 2.34/1.00  ------ Superposition Simplification Setup
% 2.34/1.00  
% 2.34/1.00  --sup_indices_passive                   []
% 2.34/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.34/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.00  --sup_full_bw                           [BwDemod]
% 2.34/1.00  --sup_immed_triv                        [TrivRules]
% 2.34/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.34/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.00  --sup_immed_bw_main                     []
% 2.34/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.34/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/1.00  
% 2.34/1.00  ------ Combination Options
% 2.34/1.00  
% 2.34/1.00  --comb_res_mult                         3
% 2.34/1.00  --comb_sup_mult                         2
% 2.34/1.00  --comb_inst_mult                        10
% 2.34/1.00  
% 2.34/1.00  ------ Debug Options
% 2.34/1.00  
% 2.34/1.00  --dbg_backtrace                         false
% 2.34/1.00  --dbg_dump_prop_clauses                 false
% 2.34/1.00  --dbg_dump_prop_clauses_file            -
% 2.34/1.00  --dbg_out_stat                          false
% 2.34/1.00  ------ Parsing...
% 2.34/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.34/1.00  
% 2.34/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.34/1.00  
% 2.34/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.34/1.00  
% 2.34/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.34/1.00  ------ Proving...
% 2.34/1.00  ------ Problem Properties 
% 2.34/1.00  
% 2.34/1.00  
% 2.34/1.00  clauses                                 17
% 2.34/1.00  conjectures                             1
% 2.34/1.00  EPR                                     1
% 2.34/1.00  Horn                                    11
% 2.34/1.00  unary                                   2
% 2.34/1.00  binary                                  9
% 2.34/1.00  lits                                    43
% 2.34/1.00  lits eq                                 7
% 2.34/1.00  fd_pure                                 0
% 2.34/1.00  fd_pseudo                               0
% 2.34/1.00  fd_cond                                 0
% 2.34/1.00  fd_pseudo_cond                          0
% 2.34/1.00  AC symbols                              0
% 2.34/1.00  
% 2.34/1.00  ------ Schedule dynamic 5 is on 
% 2.34/1.00  
% 2.34/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.34/1.00  
% 2.34/1.00  
% 2.34/1.00  ------ 
% 2.34/1.00  Current options:
% 2.34/1.00  ------ 
% 2.34/1.00  
% 2.34/1.00  ------ Input Options
% 2.34/1.00  
% 2.34/1.00  --out_options                           all
% 2.34/1.00  --tptp_safe_out                         true
% 2.34/1.00  --problem_path                          ""
% 2.34/1.00  --include_path                          ""
% 2.34/1.00  --clausifier                            res/vclausify_rel
% 2.34/1.00  --clausifier_options                    --mode clausify
% 2.34/1.00  --stdin                                 false
% 2.34/1.00  --stats_out                             all
% 2.34/1.00  
% 2.34/1.00  ------ General Options
% 2.34/1.00  
% 2.34/1.00  --fof                                   false
% 2.34/1.00  --time_out_real                         305.
% 2.34/1.00  --time_out_virtual                      -1.
% 2.34/1.00  --symbol_type_check                     false
% 2.34/1.00  --clausify_out                          false
% 2.34/1.00  --sig_cnt_out                           false
% 2.34/1.00  --trig_cnt_out                          false
% 2.34/1.00  --trig_cnt_out_tolerance                1.
% 2.34/1.00  --trig_cnt_out_sk_spl                   false
% 2.34/1.00  --abstr_cl_out                          false
% 2.34/1.00  
% 2.34/1.00  ------ Global Options
% 2.34/1.00  
% 2.34/1.00  --schedule                              default
% 2.34/1.00  --add_important_lit                     false
% 2.34/1.00  --prop_solver_per_cl                    1000
% 2.34/1.00  --min_unsat_core                        false
% 2.34/1.00  --soft_assumptions                      false
% 2.34/1.00  --soft_lemma_size                       3
% 2.34/1.00  --prop_impl_unit_size                   0
% 2.34/1.00  --prop_impl_unit                        []
% 2.34/1.00  --share_sel_clauses                     true
% 2.34/1.00  --reset_solvers                         false
% 2.34/1.00  --bc_imp_inh                            [conj_cone]
% 2.34/1.00  --conj_cone_tolerance                   3.
% 2.34/1.00  --extra_neg_conj                        none
% 2.34/1.00  --large_theory_mode                     true
% 2.34/1.00  --prolific_symb_bound                   200
% 2.34/1.00  --lt_threshold                          2000
% 2.34/1.00  --clause_weak_htbl                      true
% 2.34/1.00  --gc_record_bc_elim                     false
% 2.34/1.00  
% 2.34/1.00  ------ Preprocessing Options
% 2.34/1.00  
% 2.34/1.00  --preprocessing_flag                    true
% 2.34/1.00  --time_out_prep_mult                    0.1
% 2.34/1.00  --splitting_mode                        input
% 2.34/1.00  --splitting_grd                         true
% 2.34/1.00  --splitting_cvd                         false
% 2.34/1.00  --splitting_cvd_svl                     false
% 2.34/1.00  --splitting_nvd                         32
% 2.34/1.00  --sub_typing                            true
% 2.34/1.00  --prep_gs_sim                           true
% 2.34/1.00  --prep_unflatten                        true
% 2.34/1.00  --prep_res_sim                          true
% 2.34/1.00  --prep_upred                            true
% 2.34/1.00  --prep_sem_filter                       exhaustive
% 2.34/1.00  --prep_sem_filter_out                   false
% 2.34/1.00  --pred_elim                             true
% 2.34/1.00  --res_sim_input                         true
% 2.34/1.00  --eq_ax_congr_red                       true
% 2.34/1.00  --pure_diseq_elim                       true
% 2.34/1.00  --brand_transform                       false
% 2.34/1.00  --non_eq_to_eq                          false
% 2.34/1.00  --prep_def_merge                        true
% 2.34/1.00  --prep_def_merge_prop_impl              false
% 2.34/1.00  --prep_def_merge_mbd                    true
% 2.34/1.00  --prep_def_merge_tr_red                 false
% 2.34/1.00  --prep_def_merge_tr_cl                  false
% 2.34/1.00  --smt_preprocessing                     true
% 2.34/1.00  --smt_ac_axioms                         fast
% 2.34/1.00  --preprocessed_out                      false
% 2.34/1.00  --preprocessed_stats                    false
% 2.34/1.00  
% 2.34/1.00  ------ Abstraction refinement Options
% 2.34/1.00  
% 2.34/1.00  --abstr_ref                             []
% 2.34/1.00  --abstr_ref_prep                        false
% 2.34/1.00  --abstr_ref_until_sat                   false
% 2.34/1.00  --abstr_ref_sig_restrict                funpre
% 2.34/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.34/1.00  --abstr_ref_under                       []
% 2.34/1.00  
% 2.34/1.00  ------ SAT Options
% 2.34/1.00  
% 2.34/1.00  --sat_mode                              false
% 2.34/1.00  --sat_fm_restart_options                ""
% 2.34/1.00  --sat_gr_def                            false
% 2.34/1.00  --sat_epr_types                         true
% 2.34/1.00  --sat_non_cyclic_types                  false
% 2.34/1.00  --sat_finite_models                     false
% 2.34/1.00  --sat_fm_lemmas                         false
% 2.34/1.00  --sat_fm_prep                           false
% 2.34/1.00  --sat_fm_uc_incr                        true
% 2.34/1.00  --sat_out_model                         small
% 2.34/1.00  --sat_out_clauses                       false
% 2.34/1.00  
% 2.34/1.00  ------ QBF Options
% 2.34/1.00  
% 2.34/1.00  --qbf_mode                              false
% 2.34/1.00  --qbf_elim_univ                         false
% 2.34/1.00  --qbf_dom_inst                          none
% 2.34/1.00  --qbf_dom_pre_inst                      false
% 2.34/1.00  --qbf_sk_in                             false
% 2.34/1.00  --qbf_pred_elim                         true
% 2.34/1.00  --qbf_split                             512
% 2.34/1.00  
% 2.34/1.00  ------ BMC1 Options
% 2.34/1.00  
% 2.34/1.00  --bmc1_incremental                      false
% 2.34/1.00  --bmc1_axioms                           reachable_all
% 2.34/1.00  --bmc1_min_bound                        0
% 2.34/1.00  --bmc1_max_bound                        -1
% 2.34/1.00  --bmc1_max_bound_default                -1
% 2.34/1.00  --bmc1_symbol_reachability              true
% 2.34/1.00  --bmc1_property_lemmas                  false
% 2.34/1.00  --bmc1_k_induction                      false
% 2.34/1.00  --bmc1_non_equiv_states                 false
% 2.34/1.00  --bmc1_deadlock                         false
% 2.34/1.00  --bmc1_ucm                              false
% 2.34/1.00  --bmc1_add_unsat_core                   none
% 2.34/1.00  --bmc1_unsat_core_children              false
% 2.34/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.34/1.00  --bmc1_out_stat                         full
% 2.34/1.00  --bmc1_ground_init                      false
% 2.34/1.00  --bmc1_pre_inst_next_state              false
% 2.34/1.00  --bmc1_pre_inst_state                   false
% 2.34/1.00  --bmc1_pre_inst_reach_state             false
% 2.34/1.00  --bmc1_out_unsat_core                   false
% 2.34/1.00  --bmc1_aig_witness_out                  false
% 2.34/1.00  --bmc1_verbose                          false
% 2.34/1.00  --bmc1_dump_clauses_tptp                false
% 2.34/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.34/1.00  --bmc1_dump_file                        -
% 2.34/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.34/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.34/1.00  --bmc1_ucm_extend_mode                  1
% 2.34/1.00  --bmc1_ucm_init_mode                    2
% 2.34/1.00  --bmc1_ucm_cone_mode                    none
% 2.34/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.34/1.00  --bmc1_ucm_relax_model                  4
% 2.34/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.34/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.34/1.00  --bmc1_ucm_layered_model                none
% 2.34/1.00  --bmc1_ucm_max_lemma_size               10
% 2.34/1.00  
% 2.34/1.00  ------ AIG Options
% 2.34/1.00  
% 2.34/1.00  --aig_mode                              false
% 2.34/1.00  
% 2.34/1.00  ------ Instantiation Options
% 2.34/1.00  
% 2.34/1.00  --instantiation_flag                    true
% 2.34/1.00  --inst_sos_flag                         false
% 2.34/1.00  --inst_sos_phase                        true
% 2.34/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.34/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.34/1.00  --inst_lit_sel_side                     none
% 2.34/1.00  --inst_solver_per_active                1400
% 2.34/1.00  --inst_solver_calls_frac                1.
% 2.34/1.00  --inst_passive_queue_type               priority_queues
% 2.34/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.34/1.00  --inst_passive_queues_freq              [25;2]
% 2.34/1.00  --inst_dismatching                      true
% 2.34/1.00  --inst_eager_unprocessed_to_passive     true
% 2.34/1.00  --inst_prop_sim_given                   true
% 2.34/1.00  --inst_prop_sim_new                     false
% 2.34/1.00  --inst_subs_new                         false
% 2.34/1.00  --inst_eq_res_simp                      false
% 2.34/1.00  --inst_subs_given                       false
% 2.34/1.00  --inst_orphan_elimination               true
% 2.34/1.00  --inst_learning_loop_flag               true
% 2.34/1.00  --inst_learning_start                   3000
% 2.34/1.00  --inst_learning_factor                  2
% 2.34/1.00  --inst_start_prop_sim_after_learn       3
% 2.34/1.00  --inst_sel_renew                        solver
% 2.34/1.00  --inst_lit_activity_flag                true
% 2.34/1.00  --inst_restr_to_given                   false
% 2.34/1.00  --inst_activity_threshold               500
% 2.34/1.00  --inst_out_proof                        true
% 2.34/1.00  
% 2.34/1.00  ------ Resolution Options
% 2.34/1.00  
% 2.34/1.00  --resolution_flag                       false
% 2.34/1.00  --res_lit_sel                           adaptive
% 2.34/1.00  --res_lit_sel_side                      none
% 2.34/1.00  --res_ordering                          kbo
% 2.34/1.00  --res_to_prop_solver                    active
% 2.34/1.00  --res_prop_simpl_new                    false
% 2.34/1.00  --res_prop_simpl_given                  true
% 2.34/1.00  --res_passive_queue_type                priority_queues
% 2.34/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.34/1.00  --res_passive_queues_freq               [15;5]
% 2.34/1.00  --res_forward_subs                      full
% 2.34/1.00  --res_backward_subs                     full
% 2.34/1.00  --res_forward_subs_resolution           true
% 2.34/1.00  --res_backward_subs_resolution          true
% 2.34/1.00  --res_orphan_elimination                true
% 2.34/1.00  --res_time_limit                        2.
% 2.34/1.00  --res_out_proof                         true
% 2.34/1.00  
% 2.34/1.00  ------ Superposition Options
% 2.34/1.00  
% 2.34/1.00  --superposition_flag                    true
% 2.34/1.00  --sup_passive_queue_type                priority_queues
% 2.34/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.34/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.34/1.00  --demod_completeness_check              fast
% 2.34/1.00  --demod_use_ground                      true
% 2.34/1.00  --sup_to_prop_solver                    passive
% 2.34/1.00  --sup_prop_simpl_new                    true
% 2.34/1.00  --sup_prop_simpl_given                  true
% 2.34/1.00  --sup_fun_splitting                     false
% 2.34/1.00  --sup_smt_interval                      50000
% 2.34/1.00  
% 2.34/1.00  ------ Superposition Simplification Setup
% 2.34/1.00  
% 2.34/1.00  --sup_indices_passive                   []
% 2.34/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.34/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.00  --sup_full_bw                           [BwDemod]
% 2.34/1.00  --sup_immed_triv                        [TrivRules]
% 2.34/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.34/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.00  --sup_immed_bw_main                     []
% 2.34/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.34/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/1.00  
% 2.34/1.00  ------ Combination Options
% 2.34/1.00  
% 2.34/1.00  --comb_res_mult                         3
% 2.34/1.00  --comb_sup_mult                         2
% 2.34/1.00  --comb_inst_mult                        10
% 2.34/1.00  
% 2.34/1.00  ------ Debug Options
% 2.34/1.00  
% 2.34/1.00  --dbg_backtrace                         false
% 2.34/1.00  --dbg_dump_prop_clauses                 false
% 2.34/1.00  --dbg_dump_prop_clauses_file            -
% 2.34/1.00  --dbg_out_stat                          false
% 2.34/1.00  
% 2.34/1.00  
% 2.34/1.00  
% 2.34/1.00  
% 2.34/1.00  ------ Proving...
% 2.34/1.00  
% 2.34/1.00  
% 2.34/1.00  % SZS status Theorem for theBenchmark.p
% 2.34/1.00  
% 2.34/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.34/1.00  
% 2.34/1.00  fof(f3,axiom,(
% 2.34/1.00    ! [X0] : (v1_relat_1(X0) => (v8_relat_2(X0) <=> ! [X1,X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => r2_hidden(k4_tarski(X1,X3),X0))))),
% 2.34/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/1.00  
% 2.34/1.00  fof(f11,plain,(
% 2.34/1.00    ! [X0] : ((v8_relat_2(X0) <=> ! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | (~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)))) | ~v1_relat_1(X0))),
% 2.34/1.00    inference(ennf_transformation,[],[f3])).
% 2.34/1.00  
% 2.34/1.00  fof(f12,plain,(
% 2.34/1.00    ! [X0] : ((v8_relat_2(X0) <=> ! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0))) | ~v1_relat_1(X0))),
% 2.34/1.00    inference(flattening,[],[f11])).
% 2.34/1.00  
% 2.34/1.00  fof(f20,plain,(
% 2.34/1.00    ! [X0] : (((v8_relat_2(X0) | ? [X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 2.34/1.00    inference(nnf_transformation,[],[f12])).
% 2.34/1.00  
% 2.34/1.00  fof(f21,plain,(
% 2.34/1.00    ! [X0] : (((v8_relat_2(X0) | ? [X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X4,X5,X6] : (r2_hidden(k4_tarski(X4,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 2.34/1.00    inference(rectify,[],[f20])).
% 2.34/1.00  
% 2.34/1.00  fof(f22,plain,(
% 2.34/1.00    ! [X0] : (? [X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => (~r2_hidden(k4_tarski(sK1(X0),sK3(X0)),X0) & r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) & r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)))),
% 2.34/1.00    introduced(choice_axiom,[])).
% 2.34/1.00  
% 2.34/1.00  fof(f23,plain,(
% 2.34/1.00    ! [X0] : (((v8_relat_2(X0) | (~r2_hidden(k4_tarski(sK1(X0),sK3(X0)),X0) & r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) & r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0))) & (! [X4,X5,X6] : (r2_hidden(k4_tarski(X4,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 2.34/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f21,f22])).
% 2.34/1.00  
% 2.34/1.00  fof(f37,plain,(
% 2.34/1.00    ( ! [X0] : (v8_relat_2(X0) | r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) | ~v1_relat_1(X0)) )),
% 2.34/1.00    inference(cnf_transformation,[],[f23])).
% 2.34/1.00  
% 2.34/1.00  fof(f5,axiom,(
% 2.34/1.00    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 2.34/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/1.00  
% 2.34/1.00  fof(f47,plain,(
% 2.34/1.00    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 2.34/1.00    inference(cnf_transformation,[],[f5])).
% 2.34/1.00  
% 2.34/1.00  fof(f4,axiom,(
% 2.34/1.00    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 2.34/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/1.00  
% 2.34/1.00  fof(f13,plain,(
% 2.34/1.00    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 2.34/1.00    inference(ennf_transformation,[],[f4])).
% 2.34/1.00  
% 2.34/1.00  fof(f14,plain,(
% 2.34/1.00    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 2.34/1.00    inference(flattening,[],[f13])).
% 2.34/1.00  
% 2.34/1.00  fof(f24,plain,(
% 2.34/1.00    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 2.34/1.00    inference(nnf_transformation,[],[f14])).
% 2.34/1.00  
% 2.34/1.00  fof(f25,plain,(
% 2.34/1.00    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 2.34/1.00    inference(flattening,[],[f24])).
% 2.34/1.00  
% 2.34/1.00  fof(f26,plain,(
% 2.34/1.00    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 2.34/1.00    inference(rectify,[],[f25])).
% 2.34/1.00  
% 2.34/1.00  fof(f27,plain,(
% 2.34/1.00    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK4(X0,X1),sK5(X0,X1)) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)) & (r1_tarski(sK4(X0,X1),sK5(X0,X1)) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)) & r2_hidden(sK5(X0,X1),X0) & r2_hidden(sK4(X0,X1),X0)))),
% 2.34/1.00    introduced(choice_axiom,[])).
% 2.34/1.00  
% 2.34/1.00  fof(f28,plain,(
% 2.34/1.00    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK4(X0,X1),sK5(X0,X1)) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)) & (r1_tarski(sK4(X0,X1),sK5(X0,X1)) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)) & r2_hidden(sK5(X0,X1),X0) & r2_hidden(sK4(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 2.34/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f26,f27])).
% 2.34/1.00  
% 2.34/1.00  fof(f41,plain,(
% 2.34/1.00    ( ! [X4,X0,X5,X1] : (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 2.34/1.00    inference(cnf_transformation,[],[f28])).
% 2.34/1.00  
% 2.34/1.00  fof(f54,plain,(
% 2.34/1.00    ( ! [X4,X0,X5] : (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0)) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | ~v1_relat_1(k1_wellord2(X0))) )),
% 2.34/1.00    inference(equality_resolution,[],[f41])).
% 2.34/1.00  
% 2.34/1.00  fof(f2,axiom,(
% 2.34/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 2.34/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/1.00  
% 2.34/1.00  fof(f9,plain,(
% 2.34/1.00    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 2.34/1.00    inference(ennf_transformation,[],[f2])).
% 2.34/1.00  
% 2.34/1.00  fof(f10,plain,(
% 2.34/1.00    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 2.34/1.00    inference(flattening,[],[f9])).
% 2.34/1.00  
% 2.34/1.00  fof(f34,plain,(
% 2.34/1.00    ( ! [X2,X0,X1] : (r2_hidden(X0,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 2.34/1.00    inference(cnf_transformation,[],[f10])).
% 2.34/1.00  
% 2.34/1.00  fof(f40,plain,(
% 2.34/1.00    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 2.34/1.00    inference(cnf_transformation,[],[f28])).
% 2.34/1.00  
% 2.34/1.00  fof(f55,plain,(
% 2.34/1.00    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 2.34/1.00    inference(equality_resolution,[],[f40])).
% 2.34/1.00  
% 2.34/1.00  fof(f35,plain,(
% 2.34/1.00    ( ! [X2,X0,X1] : (r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 2.34/1.00    inference(cnf_transformation,[],[f10])).
% 2.34/1.00  
% 2.34/1.00  fof(f38,plain,(
% 2.34/1.00    ( ! [X0] : (v8_relat_2(X0) | r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) | ~v1_relat_1(X0)) )),
% 2.34/1.00    inference(cnf_transformation,[],[f23])).
% 2.34/1.00  
% 2.34/1.00  fof(f1,axiom,(
% 2.34/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.34/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/1.00  
% 2.34/1.00  fof(f8,plain,(
% 2.34/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.34/1.00    inference(ennf_transformation,[],[f1])).
% 2.34/1.00  
% 2.34/1.00  fof(f16,plain,(
% 2.34/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.34/1.00    inference(nnf_transformation,[],[f8])).
% 2.34/1.00  
% 2.34/1.00  fof(f17,plain,(
% 2.34/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.34/1.00    inference(rectify,[],[f16])).
% 2.34/1.00  
% 2.34/1.00  fof(f18,plain,(
% 2.34/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.34/1.00    introduced(choice_axiom,[])).
% 2.34/1.00  
% 2.34/1.00  fof(f19,plain,(
% 2.34/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.34/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).
% 2.34/1.00  
% 2.34/1.00  fof(f32,plain,(
% 2.34/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.34/1.00    inference(cnf_transformation,[],[f19])).
% 2.34/1.00  
% 2.34/1.00  fof(f31,plain,(
% 2.34/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.34/1.00    inference(cnf_transformation,[],[f19])).
% 2.34/1.00  
% 2.34/1.00  fof(f33,plain,(
% 2.34/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.34/1.00    inference(cnf_transformation,[],[f19])).
% 2.34/1.00  
% 2.34/1.00  fof(f42,plain,(
% 2.34/1.00    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 2.34/1.00    inference(cnf_transformation,[],[f28])).
% 2.34/1.00  
% 2.34/1.00  fof(f53,plain,(
% 2.34/1.00    ( ! [X4,X0,X5] : (r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0)) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | ~v1_relat_1(k1_wellord2(X0))) )),
% 2.34/1.00    inference(equality_resolution,[],[f42])).
% 2.34/1.00  
% 2.34/1.00  fof(f39,plain,(
% 2.34/1.00    ( ! [X0] : (v8_relat_2(X0) | ~r2_hidden(k4_tarski(sK1(X0),sK3(X0)),X0) | ~v1_relat_1(X0)) )),
% 2.34/1.00    inference(cnf_transformation,[],[f23])).
% 2.34/1.00  
% 2.34/1.00  fof(f6,conjecture,(
% 2.34/1.00    ! [X0] : v8_relat_2(k1_wellord2(X0))),
% 2.34/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/1.00  
% 2.34/1.00  fof(f7,negated_conjecture,(
% 2.34/1.00    ~! [X0] : v8_relat_2(k1_wellord2(X0))),
% 2.34/1.00    inference(negated_conjecture,[],[f6])).
% 2.34/1.00  
% 2.34/1.00  fof(f15,plain,(
% 2.34/1.00    ? [X0] : ~v8_relat_2(k1_wellord2(X0))),
% 2.34/1.00    inference(ennf_transformation,[],[f7])).
% 2.34/1.00  
% 2.34/1.00  fof(f29,plain,(
% 2.34/1.00    ? [X0] : ~v8_relat_2(k1_wellord2(X0)) => ~v8_relat_2(k1_wellord2(sK6))),
% 2.34/1.00    introduced(choice_axiom,[])).
% 2.34/1.00  
% 2.34/1.00  fof(f30,plain,(
% 2.34/1.00    ~v8_relat_2(k1_wellord2(sK6))),
% 2.34/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f15,f29])).
% 2.34/1.00  
% 2.34/1.00  fof(f48,plain,(
% 2.34/1.00    ~v8_relat_2(k1_wellord2(sK6))),
% 2.34/1.00    inference(cnf_transformation,[],[f30])).
% 2.34/1.00  
% 2.34/1.00  cnf(c_7,plain,
% 2.34/1.00      ( r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
% 2.34/1.00      | v8_relat_2(X0)
% 2.34/1.00      | ~ v1_relat_1(X0) ),
% 2.34/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_16,plain,
% 2.34/1.00      ( v1_relat_1(k1_wellord2(X0)) ),
% 2.34/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_387,plain,
% 2.34/1.00      ( r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
% 2.34/1.00      | v8_relat_2(X0)
% 2.34/1.00      | k1_wellord2(X1) != X0 ),
% 2.34/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_16]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_388,plain,
% 2.34/1.00      ( r2_hidden(k4_tarski(sK1(k1_wellord2(X0)),sK2(k1_wellord2(X0))),k1_wellord2(X0))
% 2.34/1.00      | v8_relat_2(k1_wellord2(X0)) ),
% 2.34/1.00      inference(unflattening,[status(thm)],[c_387]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1673,plain,
% 2.34/1.00      ( r2_hidden(k4_tarski(sK1(k1_wellord2(X0)),sK2(k1_wellord2(X0))),k1_wellord2(X0)) = iProver_top
% 2.34/1.00      | v8_relat_2(k1_wellord2(X0)) = iProver_top ),
% 2.34/1.00      inference(predicate_to_equality,[status(thm)],[c_388]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_14,plain,
% 2.34/1.00      ( ~ r2_hidden(X0,X1)
% 2.34/1.00      | ~ r2_hidden(X2,X1)
% 2.34/1.00      | ~ r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1))
% 2.34/1.00      | r1_tarski(X2,X0)
% 2.34/1.00      | ~ v1_relat_1(k1_wellord2(X1)) ),
% 2.34/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_433,plain,
% 2.34/1.00      ( ~ r2_hidden(X0,X1)
% 2.34/1.00      | ~ r2_hidden(X2,X1)
% 2.34/1.00      | ~ r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1))
% 2.34/1.00      | r1_tarski(X2,X0)
% 2.34/1.00      | k1_wellord2(X1) != k1_wellord2(X3) ),
% 2.34/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_14]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1669,plain,
% 2.34/1.00      ( k1_wellord2(X0) != k1_wellord2(X1)
% 2.34/1.00      | r2_hidden(X2,X0) != iProver_top
% 2.34/1.00      | r2_hidden(X3,X0) != iProver_top
% 2.34/1.00      | r2_hidden(k4_tarski(X3,X2),k1_wellord2(X0)) != iProver_top
% 2.34/1.00      | r1_tarski(X3,X2) = iProver_top ),
% 2.34/1.00      inference(predicate_to_equality,[status(thm)],[c_433]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_4,plain,
% 2.34/1.00      ( r2_hidden(X0,k3_relat_1(X1))
% 2.34/1.00      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 2.34/1.00      | ~ v1_relat_1(X1) ),
% 2.34/1.00      inference(cnf_transformation,[],[f34]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_311,plain,
% 2.34/1.00      ( r2_hidden(X0,k3_relat_1(X1))
% 2.34/1.00      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 2.34/1.00      | k1_wellord2(X3) != X1 ),
% 2.34/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_16]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_312,plain,
% 2.34/1.00      ( r2_hidden(X0,k3_relat_1(k1_wellord2(X1)))
% 2.34/1.00      | ~ r2_hidden(k4_tarski(X0,X2),k1_wellord2(X1)) ),
% 2.34/1.00      inference(unflattening,[status(thm)],[c_311]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1679,plain,
% 2.34/1.00      ( r2_hidden(X0,k3_relat_1(k1_wellord2(X1))) = iProver_top
% 2.34/1.00      | r2_hidden(k4_tarski(X0,X2),k1_wellord2(X1)) != iProver_top ),
% 2.34/1.00      inference(predicate_to_equality,[status(thm)],[c_312]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_15,plain,
% 2.34/1.00      ( ~ v1_relat_1(k1_wellord2(X0))
% 2.34/1.00      | k3_relat_1(k1_wellord2(X0)) = X0 ),
% 2.34/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_103,plain,
% 2.34/1.00      ( k3_relat_1(k1_wellord2(X0)) = X0 ),
% 2.34/1.00      inference(global_propositional_subsumption,
% 2.34/1.00                [status(thm)],
% 2.34/1.00                [c_15,c_16]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1701,plain,
% 2.34/1.00      ( r2_hidden(X0,X1) = iProver_top
% 2.34/1.00      | r2_hidden(k4_tarski(X0,X2),k1_wellord2(X1)) != iProver_top ),
% 2.34/1.00      inference(demodulation,[status(thm)],[c_1679,c_103]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_3,plain,
% 2.34/1.00      ( r2_hidden(X0,k3_relat_1(X1))
% 2.34/1.00      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 2.34/1.00      | ~ v1_relat_1(X1) ),
% 2.34/1.00      inference(cnf_transformation,[],[f35]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_323,plain,
% 2.34/1.00      ( r2_hidden(X0,k3_relat_1(X1))
% 2.34/1.00      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 2.34/1.00      | k1_wellord2(X3) != X1 ),
% 2.34/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_16]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_324,plain,
% 2.34/1.00      ( r2_hidden(X0,k3_relat_1(k1_wellord2(X1)))
% 2.34/1.00      | ~ r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1)) ),
% 2.34/1.00      inference(unflattening,[status(thm)],[c_323]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1678,plain,
% 2.34/1.00      ( r2_hidden(X0,k3_relat_1(k1_wellord2(X1))) = iProver_top
% 2.34/1.00      | r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1)) != iProver_top ),
% 2.34/1.00      inference(predicate_to_equality,[status(thm)],[c_324]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1696,plain,
% 2.34/1.00      ( r2_hidden(X0,X1) = iProver_top
% 2.34/1.00      | r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1)) != iProver_top ),
% 2.34/1.00      inference(demodulation,[status(thm)],[c_1678,c_103]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1749,plain,
% 2.34/1.00      ( k1_wellord2(X0) != k1_wellord2(X1)
% 2.34/1.00      | r2_hidden(k4_tarski(X2,X3),k1_wellord2(X1)) != iProver_top
% 2.34/1.00      | r1_tarski(X2,X3) = iProver_top ),
% 2.34/1.00      inference(forward_subsumption_resolution,
% 2.34/1.00                [status(thm)],
% 2.34/1.00                [c_1669,c_1701,c_1696]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1995,plain,
% 2.34/1.00      ( r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2)) != iProver_top
% 2.34/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.34/1.00      inference(equality_resolution,[status(thm)],[c_1749]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_3771,plain,
% 2.34/1.00      ( r1_tarski(sK1(k1_wellord2(X0)),sK2(k1_wellord2(X0))) = iProver_top
% 2.34/1.00      | v8_relat_2(k1_wellord2(X0)) = iProver_top ),
% 2.34/1.00      inference(superposition,[status(thm)],[c_1673,c_1995]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_6,plain,
% 2.34/1.00      ( r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
% 2.34/1.00      | v8_relat_2(X0)
% 2.34/1.00      | ~ v1_relat_1(X0) ),
% 2.34/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_397,plain,
% 2.34/1.00      ( r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
% 2.34/1.00      | v8_relat_2(X0)
% 2.34/1.00      | k1_wellord2(X1) != X0 ),
% 2.34/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_16]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_398,plain,
% 2.34/1.00      ( r2_hidden(k4_tarski(sK2(k1_wellord2(X0)),sK3(k1_wellord2(X0))),k1_wellord2(X0))
% 2.34/1.00      | v8_relat_2(k1_wellord2(X0)) ),
% 2.34/1.00      inference(unflattening,[status(thm)],[c_397]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1672,plain,
% 2.34/1.00      ( r2_hidden(k4_tarski(sK2(k1_wellord2(X0)),sK3(k1_wellord2(X0))),k1_wellord2(X0)) = iProver_top
% 2.34/1.00      | v8_relat_2(k1_wellord2(X0)) = iProver_top ),
% 2.34/1.00      inference(predicate_to_equality,[status(thm)],[c_398]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_3002,plain,
% 2.34/1.00      ( r1_tarski(sK2(k1_wellord2(X0)),sK3(k1_wellord2(X0))) = iProver_top
% 2.34/1.00      | v8_relat_2(k1_wellord2(X0)) = iProver_top ),
% 2.34/1.00      inference(superposition,[status(thm)],[c_1672,c_1995]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1,plain,
% 2.34/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.34/1.00      inference(cnf_transformation,[],[f32]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1682,plain,
% 2.34/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.34/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.34/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_2,plain,
% 2.34/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.34/1.00      inference(cnf_transformation,[],[f31]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1681,plain,
% 2.34/1.00      ( r2_hidden(X0,X1) != iProver_top
% 2.34/1.00      | r2_hidden(X0,X2) = iProver_top
% 2.34/1.00      | r1_tarski(X1,X2) != iProver_top ),
% 2.34/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_2134,plain,
% 2.34/1.00      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 2.34/1.00      | r1_tarski(X0,X2) != iProver_top
% 2.34/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.34/1.00      inference(superposition,[status(thm)],[c_1682,c_1681]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_2253,plain,
% 2.34/1.00      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 2.34/1.00      | r1_tarski(X0,X3) != iProver_top
% 2.34/1.00      | r1_tarski(X3,X2) != iProver_top
% 2.34/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.34/1.00      inference(superposition,[status(thm)],[c_2134,c_1681]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_3702,plain,
% 2.34/1.00      ( r2_hidden(sK0(X0,X1),sK3(k1_wellord2(X2))) = iProver_top
% 2.34/1.00      | r1_tarski(X0,X1) = iProver_top
% 2.34/1.00      | r1_tarski(X0,sK2(k1_wellord2(X2))) != iProver_top
% 2.34/1.00      | v8_relat_2(k1_wellord2(X2)) = iProver_top ),
% 2.34/1.00      inference(superposition,[status(thm)],[c_3002,c_2253]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_0,plain,
% 2.34/1.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.34/1.00      inference(cnf_transformation,[],[f33]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1683,plain,
% 2.34/1.00      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 2.34/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.34/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_5164,plain,
% 2.34/1.00      ( r1_tarski(X0,sK2(k1_wellord2(X1))) != iProver_top
% 2.34/1.00      | r1_tarski(X0,sK3(k1_wellord2(X1))) = iProver_top
% 2.34/1.00      | v8_relat_2(k1_wellord2(X1)) = iProver_top ),
% 2.34/1.00      inference(superposition,[status(thm)],[c_3702,c_1683]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_5211,plain,
% 2.34/1.00      ( r1_tarski(sK1(k1_wellord2(X0)),sK3(k1_wellord2(X0))) = iProver_top
% 2.34/1.00      | v8_relat_2(k1_wellord2(X0)) = iProver_top ),
% 2.34/1.00      inference(superposition,[status(thm)],[c_3771,c_5164]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_5217,plain,
% 2.34/1.00      ( r1_tarski(sK1(k1_wellord2(sK6)),sK3(k1_wellord2(sK6))) = iProver_top
% 2.34/1.00      | v8_relat_2(k1_wellord2(sK6)) = iProver_top ),
% 2.34/1.00      inference(instantiation,[status(thm)],[c_5211]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_13,plain,
% 2.34/1.00      ( ~ r2_hidden(X0,X1)
% 2.34/1.00      | ~ r2_hidden(X2,X1)
% 2.34/1.00      | r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1))
% 2.34/1.00      | ~ r1_tarski(X2,X0)
% 2.34/1.00      | ~ v1_relat_1(k1_wellord2(X1)) ),
% 2.34/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_453,plain,
% 2.34/1.00      ( ~ r2_hidden(X0,X1)
% 2.34/1.00      | ~ r2_hidden(X2,X1)
% 2.34/1.00      | r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1))
% 2.34/1.00      | ~ r1_tarski(X2,X0)
% 2.34/1.00      | k1_wellord2(X1) != k1_wellord2(X3) ),
% 2.34/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_13]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1668,plain,
% 2.34/1.00      ( k1_wellord2(X0) != k1_wellord2(X1)
% 2.34/1.00      | r2_hidden(X2,X0) != iProver_top
% 2.34/1.00      | r2_hidden(X3,X0) != iProver_top
% 2.34/1.00      | r2_hidden(k4_tarski(X3,X2),k1_wellord2(X0)) = iProver_top
% 2.34/1.00      | r1_tarski(X3,X2) != iProver_top ),
% 2.34/1.00      inference(predicate_to_equality,[status(thm)],[c_453]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_2126,plain,
% 2.34/1.00      ( r2_hidden(X0,X1) != iProver_top
% 2.34/1.00      | r2_hidden(X2,X1) != iProver_top
% 2.34/1.00      | r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1)) = iProver_top
% 2.34/1.00      | r1_tarski(X2,X0) != iProver_top ),
% 2.34/1.00      inference(equality_resolution,[status(thm)],[c_1668]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_5,plain,
% 2.34/1.00      ( ~ r2_hidden(k4_tarski(sK1(X0),sK3(X0)),X0)
% 2.34/1.00      | v8_relat_2(X0)
% 2.34/1.00      | ~ v1_relat_1(X0) ),
% 2.34/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_407,plain,
% 2.34/1.00      ( ~ r2_hidden(k4_tarski(sK1(X0),sK3(X0)),X0)
% 2.34/1.00      | v8_relat_2(X0)
% 2.34/1.00      | k1_wellord2(X1) != X0 ),
% 2.34/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_16]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_408,plain,
% 2.34/1.00      ( ~ r2_hidden(k4_tarski(sK1(k1_wellord2(X0)),sK3(k1_wellord2(X0))),k1_wellord2(X0))
% 2.34/1.00      | v8_relat_2(k1_wellord2(X0)) ),
% 2.34/1.00      inference(unflattening,[status(thm)],[c_407]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1671,plain,
% 2.34/1.00      ( r2_hidden(k4_tarski(sK1(k1_wellord2(X0)),sK3(k1_wellord2(X0))),k1_wellord2(X0)) != iProver_top
% 2.34/1.00      | v8_relat_2(k1_wellord2(X0)) = iProver_top ),
% 2.34/1.00      inference(predicate_to_equality,[status(thm)],[c_408]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_2464,plain,
% 2.34/1.00      ( r2_hidden(sK3(k1_wellord2(X0)),X0) != iProver_top
% 2.34/1.00      | r2_hidden(sK1(k1_wellord2(X0)),X0) != iProver_top
% 2.34/1.00      | r1_tarski(sK1(k1_wellord2(X0)),sK3(k1_wellord2(X0))) != iProver_top
% 2.34/1.00      | v8_relat_2(k1_wellord2(X0)) = iProver_top ),
% 2.34/1.00      inference(superposition,[status(thm)],[c_2126,c_1671]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_2488,plain,
% 2.34/1.00      ( r2_hidden(sK3(k1_wellord2(sK6)),sK6) != iProver_top
% 2.34/1.00      | r2_hidden(sK1(k1_wellord2(sK6)),sK6) != iProver_top
% 2.34/1.00      | r1_tarski(sK1(k1_wellord2(sK6)),sK3(k1_wellord2(sK6))) != iProver_top
% 2.34/1.00      | v8_relat_2(k1_wellord2(sK6)) = iProver_top ),
% 2.34/1.00      inference(instantiation,[status(thm)],[c_2464]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_2133,plain,
% 2.34/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 2.34/1.00      inference(superposition,[status(thm)],[c_1682,c_1683]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_2144,plain,
% 2.34/1.00      ( r1_tarski(sK6,sK6) = iProver_top ),
% 2.34/1.00      inference(instantiation,[status(thm)],[c_2133]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1363,plain,
% 2.34/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.34/1.00      theory(equality) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_2032,plain,
% 2.34/1.00      ( ~ r1_tarski(X0,X1)
% 2.34/1.00      | r1_tarski(k3_relat_1(k1_wellord2(X2)),X3)
% 2.34/1.00      | X3 != X1
% 2.34/1.00      | k3_relat_1(k1_wellord2(X2)) != X0 ),
% 2.34/1.00      inference(instantiation,[status(thm)],[c_1363]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_2033,plain,
% 2.34/1.00      ( X0 != X1
% 2.34/1.00      | k3_relat_1(k1_wellord2(X2)) != X3
% 2.34/1.00      | r1_tarski(X3,X1) != iProver_top
% 2.34/1.00      | r1_tarski(k3_relat_1(k1_wellord2(X2)),X0) = iProver_top ),
% 2.34/1.00      inference(predicate_to_equality,[status(thm)],[c_2032]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_2035,plain,
% 2.34/1.00      ( k3_relat_1(k1_wellord2(sK6)) != sK6
% 2.34/1.00      | sK6 != sK6
% 2.34/1.00      | r1_tarski(k3_relat_1(k1_wellord2(sK6)),sK6) = iProver_top
% 2.34/1.00      | r1_tarski(sK6,sK6) != iProver_top ),
% 2.34/1.00      inference(instantiation,[status(thm)],[c_2033]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1889,plain,
% 2.34/1.00      ( r2_hidden(sK3(k1_wellord2(X0)),X1)
% 2.34/1.00      | ~ r2_hidden(sK3(k1_wellord2(X0)),k3_relat_1(k1_wellord2(X0)))
% 2.34/1.00      | ~ r1_tarski(k3_relat_1(k1_wellord2(X0)),X1) ),
% 2.34/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1895,plain,
% 2.34/1.00      ( r2_hidden(sK3(k1_wellord2(X0)),X1) = iProver_top
% 2.34/1.00      | r2_hidden(sK3(k1_wellord2(X0)),k3_relat_1(k1_wellord2(X0))) != iProver_top
% 2.34/1.00      | r1_tarski(k3_relat_1(k1_wellord2(X0)),X1) != iProver_top ),
% 2.34/1.00      inference(predicate_to_equality,[status(thm)],[c_1889]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1897,plain,
% 2.34/1.00      ( r2_hidden(sK3(k1_wellord2(sK6)),k3_relat_1(k1_wellord2(sK6))) != iProver_top
% 2.34/1.00      | r2_hidden(sK3(k1_wellord2(sK6)),sK6) = iProver_top
% 2.34/1.00      | r1_tarski(k3_relat_1(k1_wellord2(sK6)),sK6) != iProver_top ),
% 2.34/1.00      inference(instantiation,[status(thm)],[c_1895]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1856,plain,
% 2.34/1.00      ( r2_hidden(sK1(k1_wellord2(X0)),X1)
% 2.34/1.00      | ~ r2_hidden(sK1(k1_wellord2(X0)),k3_relat_1(k1_wellord2(X0)))
% 2.34/1.00      | ~ r1_tarski(k3_relat_1(k1_wellord2(X0)),X1) ),
% 2.34/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1862,plain,
% 2.34/1.00      ( r2_hidden(sK1(k1_wellord2(X0)),X1) = iProver_top
% 2.34/1.00      | r2_hidden(sK1(k1_wellord2(X0)),k3_relat_1(k1_wellord2(X0))) != iProver_top
% 2.34/1.00      | r1_tarski(k3_relat_1(k1_wellord2(X0)),X1) != iProver_top ),
% 2.34/1.00      inference(predicate_to_equality,[status(thm)],[c_1856]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1864,plain,
% 2.34/1.00      ( r2_hidden(sK1(k1_wellord2(sK6)),k3_relat_1(k1_wellord2(sK6))) != iProver_top
% 2.34/1.00      | r2_hidden(sK1(k1_wellord2(sK6)),sK6) = iProver_top
% 2.34/1.00      | r1_tarski(k3_relat_1(k1_wellord2(sK6)),sK6) != iProver_top ),
% 2.34/1.00      inference(instantiation,[status(thm)],[c_1862]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1805,plain,
% 2.34/1.00      ( ~ r2_hidden(k4_tarski(sK2(k1_wellord2(X0)),sK3(k1_wellord2(X0))),k1_wellord2(X0))
% 2.34/1.00      | r2_hidden(sK3(k1_wellord2(X0)),k3_relat_1(k1_wellord2(X0))) ),
% 2.34/1.00      inference(instantiation,[status(thm)],[c_324]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1806,plain,
% 2.34/1.00      ( r2_hidden(k4_tarski(sK2(k1_wellord2(X0)),sK3(k1_wellord2(X0))),k1_wellord2(X0)) != iProver_top
% 2.34/1.00      | r2_hidden(sK3(k1_wellord2(X0)),k3_relat_1(k1_wellord2(X0))) = iProver_top ),
% 2.34/1.00      inference(predicate_to_equality,[status(thm)],[c_1805]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1808,plain,
% 2.34/1.00      ( r2_hidden(k4_tarski(sK2(k1_wellord2(sK6)),sK3(k1_wellord2(sK6))),k1_wellord2(sK6)) != iProver_top
% 2.34/1.00      | r2_hidden(sK3(k1_wellord2(sK6)),k3_relat_1(k1_wellord2(sK6))) = iProver_top ),
% 2.34/1.00      inference(instantiation,[status(thm)],[c_1806]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1790,plain,
% 2.34/1.00      ( ~ r2_hidden(k4_tarski(sK1(k1_wellord2(X0)),sK2(k1_wellord2(X0))),k1_wellord2(X0))
% 2.34/1.00      | r2_hidden(sK1(k1_wellord2(X0)),k3_relat_1(k1_wellord2(X0))) ),
% 2.34/1.00      inference(instantiation,[status(thm)],[c_312]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1791,plain,
% 2.34/1.00      ( r2_hidden(k4_tarski(sK1(k1_wellord2(X0)),sK2(k1_wellord2(X0))),k1_wellord2(X0)) != iProver_top
% 2.34/1.00      | r2_hidden(sK1(k1_wellord2(X0)),k3_relat_1(k1_wellord2(X0))) = iProver_top ),
% 2.34/1.00      inference(predicate_to_equality,[status(thm)],[c_1790]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1793,plain,
% 2.34/1.00      ( r2_hidden(k4_tarski(sK1(k1_wellord2(sK6)),sK2(k1_wellord2(sK6))),k1_wellord2(sK6)) != iProver_top
% 2.34/1.00      | r2_hidden(sK1(k1_wellord2(sK6)),k3_relat_1(k1_wellord2(sK6))) = iProver_top ),
% 2.34/1.00      inference(instantiation,[status(thm)],[c_1791]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1361,plain,( X0 = X0 ),theory(equality) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1386,plain,
% 2.34/1.00      ( sK6 = sK6 ),
% 2.34/1.00      inference(instantiation,[status(thm)],[c_1361]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_17,negated_conjecture,
% 2.34/1.00      ( ~ v8_relat_2(k1_wellord2(sK6)) ),
% 2.34/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_271,plain,
% 2.34/1.00      ( r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
% 2.34/1.00      | ~ v1_relat_1(X0)
% 2.34/1.00      | k1_wellord2(sK6) != X0 ),
% 2.34/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_17]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_272,plain,
% 2.34/1.00      ( r2_hidden(k4_tarski(sK2(k1_wellord2(sK6)),sK3(k1_wellord2(sK6))),k1_wellord2(sK6))
% 2.34/1.00      | ~ v1_relat_1(k1_wellord2(sK6)) ),
% 2.34/1.00      inference(unflattening,[status(thm)],[c_271]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_273,plain,
% 2.34/1.00      ( r2_hidden(k4_tarski(sK2(k1_wellord2(sK6)),sK3(k1_wellord2(sK6))),k1_wellord2(sK6)) = iProver_top
% 2.34/1.00      | v1_relat_1(k1_wellord2(sK6)) != iProver_top ),
% 2.34/1.00      inference(predicate_to_equality,[status(thm)],[c_272]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_260,plain,
% 2.34/1.00      ( r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
% 2.34/1.00      | ~ v1_relat_1(X0)
% 2.34/1.00      | k1_wellord2(sK6) != X0 ),
% 2.34/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_17]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_261,plain,
% 2.34/1.00      ( r2_hidden(k4_tarski(sK1(k1_wellord2(sK6)),sK2(k1_wellord2(sK6))),k1_wellord2(sK6))
% 2.34/1.00      | ~ v1_relat_1(k1_wellord2(sK6)) ),
% 2.34/1.00      inference(unflattening,[status(thm)],[c_260]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_262,plain,
% 2.34/1.00      ( r2_hidden(k4_tarski(sK1(k1_wellord2(sK6)),sK2(k1_wellord2(sK6))),k1_wellord2(sK6)) = iProver_top
% 2.34/1.00      | v1_relat_1(k1_wellord2(sK6)) != iProver_top ),
% 2.34/1.00      inference(predicate_to_equality,[status(thm)],[c_261]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_23,plain,
% 2.34/1.00      ( ~ v1_relat_1(k1_wellord2(sK6))
% 2.34/1.00      | k3_relat_1(k1_wellord2(sK6)) = sK6 ),
% 2.34/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_19,plain,
% 2.34/1.00      ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
% 2.34/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_21,plain,
% 2.34/1.00      ( v1_relat_1(k1_wellord2(sK6)) = iProver_top ),
% 2.34/1.00      inference(instantiation,[status(thm)],[c_19]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_20,plain,
% 2.34/1.00      ( v1_relat_1(k1_wellord2(sK6)) ),
% 2.34/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_18,plain,
% 2.34/1.00      ( v8_relat_2(k1_wellord2(sK6)) != iProver_top ),
% 2.34/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(contradiction,plain,
% 2.34/1.00      ( $false ),
% 2.34/1.00      inference(minisat,
% 2.34/1.00                [status(thm)],
% 2.34/1.00                [c_5217,c_2488,c_2144,c_2035,c_1897,c_1864,c_1808,c_1793,
% 2.34/1.00                 c_1386,c_273,c_262,c_23,c_21,c_20,c_18]) ).
% 2.34/1.00  
% 2.34/1.00  
% 2.34/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.34/1.00  
% 2.34/1.00  ------                               Statistics
% 2.34/1.00  
% 2.34/1.00  ------ General
% 2.34/1.00  
% 2.34/1.00  abstr_ref_over_cycles:                  0
% 2.34/1.00  abstr_ref_under_cycles:                 0
% 2.34/1.00  gc_basic_clause_elim:                   0
% 2.34/1.00  forced_gc_time:                         0
% 2.34/1.00  parsing_time:                           0.008
% 2.34/1.00  unif_index_cands_time:                  0.
% 2.34/1.00  unif_index_add_time:                    0.
% 2.34/1.00  orderings_time:                         0.
% 2.34/1.00  out_proof_time:                         0.007
% 2.34/1.00  total_time:                             0.191
% 2.34/1.00  num_of_symbols:                         45
% 2.34/1.00  num_of_terms:                           6981
% 2.34/1.00  
% 2.34/1.00  ------ Preprocessing
% 2.34/1.00  
% 2.34/1.00  num_of_splits:                          0
% 2.34/1.00  num_of_split_atoms:                     0
% 2.34/1.00  num_of_reused_defs:                     0
% 2.34/1.00  num_eq_ax_congr_red:                    11
% 2.34/1.00  num_of_sem_filtered_clauses:            1
% 2.34/1.00  num_of_subtypes:                        0
% 2.34/1.00  monotx_restored_types:                  0
% 2.34/1.00  sat_num_of_epr_types:                   0
% 2.34/1.00  sat_num_of_non_cyclic_types:            0
% 2.34/1.00  sat_guarded_non_collapsed_types:        0
% 2.34/1.00  num_pure_diseq_elim:                    0
% 2.34/1.00  simp_replaced_by:                       0
% 2.34/1.00  res_preprocessed:                       96
% 2.34/1.00  prep_upred:                             0
% 2.34/1.00  prep_unflattend:                        56
% 2.34/1.00  smt_new_axioms:                         0
% 2.34/1.00  pred_elim_cands:                        3
% 2.34/1.00  pred_elim:                              1
% 2.34/1.00  pred_elim_cl:                           1
% 2.34/1.00  pred_elim_cycles:                       6
% 2.34/1.00  merged_defs:                            0
% 2.34/1.00  merged_defs_ncl:                        0
% 2.34/1.00  bin_hyper_res:                          0
% 2.34/1.00  prep_cycles:                            4
% 2.34/1.00  pred_elim_time:                         0.018
% 2.34/1.00  splitting_time:                         0.
% 2.34/1.00  sem_filter_time:                        0.
% 2.34/1.00  monotx_time:                            0.013
% 2.34/1.00  subtype_inf_time:                       0.
% 2.34/1.00  
% 2.34/1.00  ------ Problem properties
% 2.34/1.00  
% 2.34/1.00  clauses:                                17
% 2.34/1.00  conjectures:                            1
% 2.34/1.00  epr:                                    1
% 2.34/1.00  horn:                                   11
% 2.34/1.00  ground:                                 1
% 2.34/1.00  unary:                                  2
% 2.34/1.00  binary:                                 9
% 2.34/1.00  lits:                                   43
% 2.34/1.00  lits_eq:                                7
% 2.34/1.00  fd_pure:                                0
% 2.34/1.00  fd_pseudo:                              0
% 2.34/1.00  fd_cond:                                0
% 2.34/1.00  fd_pseudo_cond:                         0
% 2.34/1.00  ac_symbols:                             0
% 2.34/1.00  
% 2.34/1.00  ------ Propositional Solver
% 2.34/1.00  
% 2.34/1.00  prop_solver_calls:                      26
% 2.34/1.00  prop_fast_solver_calls:                 863
% 2.34/1.00  smt_solver_calls:                       0
% 2.34/1.00  smt_fast_solver_calls:                  0
% 2.34/1.00  prop_num_of_clauses:                    1681
% 2.34/1.00  prop_preprocess_simplified:             5748
% 2.34/1.00  prop_fo_subsumed:                       4
% 2.34/1.00  prop_solver_time:                       0.
% 2.34/1.00  smt_solver_time:                        0.
% 2.34/1.00  smt_fast_solver_time:                   0.
% 2.34/1.00  prop_fast_solver_time:                  0.
% 2.34/1.00  prop_unsat_core_time:                   0.
% 2.34/1.00  
% 2.34/1.00  ------ QBF
% 2.34/1.00  
% 2.34/1.00  qbf_q_res:                              0
% 2.34/1.00  qbf_num_tautologies:                    0
% 2.34/1.00  qbf_prep_cycles:                        0
% 2.34/1.00  
% 2.34/1.00  ------ BMC1
% 2.34/1.00  
% 2.34/1.00  bmc1_current_bound:                     -1
% 2.34/1.00  bmc1_last_solved_bound:                 -1
% 2.34/1.00  bmc1_unsat_core_size:                   -1
% 2.34/1.00  bmc1_unsat_core_parents_size:           -1
% 2.34/1.00  bmc1_merge_next_fun:                    0
% 2.34/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.34/1.00  
% 2.34/1.00  ------ Instantiation
% 2.34/1.00  
% 2.34/1.00  inst_num_of_clauses:                    492
% 2.34/1.00  inst_num_in_passive:                    80
% 2.34/1.00  inst_num_in_active:                     186
% 2.34/1.00  inst_num_in_unprocessed:                226
% 2.34/1.00  inst_num_of_loops:                      220
% 2.34/1.00  inst_num_of_learning_restarts:          0
% 2.34/1.00  inst_num_moves_active_passive:          33
% 2.34/1.00  inst_lit_activity:                      0
% 2.34/1.00  inst_lit_activity_moves:                0
% 2.34/1.00  inst_num_tautologies:                   0
% 2.34/1.00  inst_num_prop_implied:                  0
% 2.34/1.00  inst_num_existing_simplified:           0
% 2.34/1.00  inst_num_eq_res_simplified:             0
% 2.34/1.00  inst_num_child_elim:                    0
% 2.34/1.00  inst_num_of_dismatching_blockings:      101
% 2.34/1.00  inst_num_of_non_proper_insts:           418
% 2.34/1.00  inst_num_of_duplicates:                 0
% 2.34/1.00  inst_inst_num_from_inst_to_res:         0
% 2.34/1.00  inst_dismatching_checking_time:         0.
% 2.34/1.00  
% 2.34/1.00  ------ Resolution
% 2.34/1.00  
% 2.34/1.00  res_num_of_clauses:                     0
% 2.34/1.00  res_num_in_passive:                     0
% 2.34/1.00  res_num_in_active:                      0
% 2.34/1.00  res_num_of_loops:                       100
% 2.34/1.00  res_forward_subset_subsumed:            16
% 2.34/1.00  res_backward_subset_subsumed:           0
% 2.34/1.00  res_forward_subsumed:                   0
% 2.34/1.00  res_backward_subsumed:                  0
% 2.34/1.00  res_forward_subsumption_resolution:     0
% 2.34/1.00  res_backward_subsumption_resolution:    0
% 2.34/1.00  res_clause_to_clause_subsumption:       648
% 2.34/1.00  res_orphan_elimination:                 0
% 2.34/1.00  res_tautology_del:                      18
% 2.34/1.00  res_num_eq_res_simplified:              0
% 2.34/1.00  res_num_sel_changes:                    0
% 2.34/1.00  res_moves_from_active_to_pass:          0
% 2.34/1.00  
% 2.34/1.00  ------ Superposition
% 2.34/1.00  
% 2.34/1.00  sup_time_total:                         0.
% 2.34/1.00  sup_time_generating:                    0.
% 2.34/1.00  sup_time_sim_full:                      0.
% 2.34/1.00  sup_time_sim_immed:                     0.
% 2.34/1.00  
% 2.34/1.00  sup_num_of_clauses:                     66
% 2.34/1.00  sup_num_in_active:                      44
% 2.34/1.00  sup_num_in_passive:                     22
% 2.34/1.00  sup_num_of_loops:                       43
% 2.34/1.00  sup_fw_superposition:                   25
% 2.34/1.00  sup_bw_superposition:                   54
% 2.34/1.00  sup_immediate_simplified:               5
% 2.34/1.00  sup_given_eliminated:                   0
% 2.34/1.00  comparisons_done:                       0
% 2.34/1.00  comparisons_avoided:                    0
% 2.34/1.00  
% 2.34/1.00  ------ Simplifications
% 2.34/1.00  
% 2.34/1.00  
% 2.34/1.00  sim_fw_subset_subsumed:                 2
% 2.34/1.00  sim_bw_subset_subsumed:                 0
% 2.34/1.00  sim_fw_subsumed:                        3
% 2.34/1.00  sim_bw_subsumed:                        0
% 2.34/1.00  sim_fw_subsumption_res:                 3
% 2.34/1.00  sim_bw_subsumption_res:                 0
% 2.34/1.00  sim_tautology_del:                      11
% 2.34/1.00  sim_eq_tautology_del:                   4
% 2.34/1.00  sim_eq_res_simp:                        0
% 2.34/1.00  sim_fw_demodulated:                     2
% 2.34/1.00  sim_bw_demodulated:                     0
% 2.34/1.00  sim_light_normalised:                   4
% 2.34/1.00  sim_joinable_taut:                      0
% 2.34/1.00  sim_joinable_simp:                      0
% 2.34/1.00  sim_ac_normalised:                      0
% 2.34/1.00  sim_smt_subsumption:                    0
% 2.34/1.00  
%------------------------------------------------------------------------------
