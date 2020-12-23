%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0938+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:28 EST 2020

% Result     : Theorem 1.48s
% Output     : CNFRefutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 226 expanded)
%              Number of clauses        :   60 (  82 expanded)
%              Number of leaves         :    9 (  41 expanded)
%              Depth                    :   19
%              Number of atoms          :  430 (1388 expanded)
%              Number of equality atoms :  119 ( 198 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   17 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r8_relat_2(X0,X1)
        <=> ! [X2,X3,X4] :
              ( ( r2_hidden(k4_tarski(X3,X4),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X4,X1)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) )
             => r2_hidden(k4_tarski(X2,X4),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r8_relat_2(X0,X1)
        <=> ! [X2,X3,X4] :
              ( r2_hidden(k4_tarski(X2,X4),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r8_relat_2(X0,X1)
        <=> ! [X2,X3,X4] :
              ( r2_hidden(k4_tarski(X2,X4),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r8_relat_2(X0,X1)
            | ? [X2,X3,X4] :
                ( ~ r2_hidden(k4_tarski(X2,X4),X0)
                & r2_hidden(k4_tarski(X3,X4),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X4,X1)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X2,X3,X4] :
                ( r2_hidden(k4_tarski(X2,X4),X0)
                | ~ r2_hidden(k4_tarski(X3,X4),X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X0)
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1) )
            | ~ r8_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r8_relat_2(X0,X1)
            | ? [X2,X3,X4] :
                ( ~ r2_hidden(k4_tarski(X2,X4),X0)
                & r2_hidden(k4_tarski(X3,X4),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X4,X1)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X5,X6,X7] :
                ( r2_hidden(k4_tarski(X5,X7),X0)
                | ~ r2_hidden(k4_tarski(X6,X7),X0)
                | ~ r2_hidden(k4_tarski(X5,X6),X0)
                | ~ r2_hidden(X7,X1)
                | ~ r2_hidden(X6,X1)
                | ~ r2_hidden(X5,X1) )
            | ~ r8_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2,X3,X4] :
          ( ~ r2_hidden(k4_tarski(X2,X4),X0)
          & r2_hidden(k4_tarski(X3,X4),X0)
          & r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(X4,X1)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK4(X0,X1)),X0)
        & r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
        & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
        & r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r8_relat_2(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK4(X0,X1)),X0)
              & r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
              & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
              & r2_hidden(sK4(X0,X1),X1)
              & r2_hidden(sK3(X0,X1),X1)
              & r2_hidden(sK2(X0,X1),X1) ) )
          & ( ! [X5,X6,X7] :
                ( r2_hidden(k4_tarski(X5,X7),X0)
                | ~ r2_hidden(k4_tarski(X6,X7),X0)
                | ~ r2_hidden(k4_tarski(X5,X6),X0)
                | ~ r2_hidden(X7,X1)
                | ~ r2_hidden(X6,X1)
                | ~ r2_hidden(X5,X1) )
            | ~ r8_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f23,f24])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r8_relat_2(X0,X1)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
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

fof(f9,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK0(X0,X1),sK1(X0,X1))
          | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
        & ( r1_tarski(sK0(X0,X1),sK1(X0,X1))
          | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
        & r2_hidden(sK1(X0,X1),X0)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK0(X0,X1),sK1(X0,X1))
              | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
            & ( r1_tarski(sK0(X0,X1),sK1(X0,X1))
              | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
            & r2_hidden(sK1(X0,X1),X0)
            & r2_hidden(sK0(X0,X1),X0) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).

fof(f31,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_tarski(X4,X5)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f52,plain,(
    ! [X4,X0,X5] :
      ( r1_tarski(X4,X5)
      | ~ r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r8_relat_2(X0,X1)
      | r2_hidden(sK4(X0,X1),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r8_relat_2(X0,X1)
      | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r8_relat_2(X0,X1)
      | r2_hidden(sK3(X0,X1),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f32,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f51,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r8_relat_2(X0,X1)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK4(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v8_relat_2(X0)
      <=> r8_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> r8_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ~ r8_relat_2(X0,k3_relat_1(X0)) )
        & ( r8_relat_2(X0,k3_relat_1(X0))
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | ~ r8_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,conjecture,(
    ! [X0] : v8_relat_2(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] : v8_relat_2(k1_wellord2(X0)) ),
    inference(negated_conjecture,[],[f6])).

fof(f15,plain,(
    ? [X0] : ~ v8_relat_2(k1_wellord2(X0)) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,
    ( ? [X0] : ~ v8_relat_2(k1_wellord2(X0))
   => ~ v8_relat_2(k1_wellord2(sK5)) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ~ v8_relat_2(k1_wellord2(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f15,f26])).

fof(f46,plain,(
    ~ v8_relat_2(k1_wellord2(sK5)) ),
    inference(cnf_transformation,[],[f27])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f53,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r8_relat_2(X0,X1)
      | r2_hidden(sK2(X0,X1),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_11,plain,
    ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
    | r8_relat_2(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_16,plain,
    ( v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_265,plain,
    ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
    | r8_relat_2(X0,X1)
    | k1_wellord2(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_16])).

cnf(c_266,plain,
    ( r2_hidden(k4_tarski(sK2(k1_wellord2(X0),X1),sK3(k1_wellord2(X0),X1)),k1_wellord2(X0))
    | r8_relat_2(k1_wellord2(X0),X1) ),
    inference(unflattening,[status(thm)],[c_265])).

cnf(c_1473,plain,
    ( r2_hidden(k4_tarski(sK2(k1_wellord2(X0),X1),sK3(k1_wellord2(X0),X1)),k1_wellord2(X0)) = iProver_top
    | r8_relat_2(k1_wellord2(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_266])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1))
    | r1_tarski(X2,X0)
    | ~ v1_relat_1(k1_wellord2(X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_355,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1))
    | r1_tarski(X2,X0)
    | k1_wellord2(X1) != k1_wellord2(X3) ),
    inference(resolution_lifted,[status(thm)],[c_16,c_7])).

cnf(c_1466,plain,
    ( k1_wellord2(X0) != k1_wellord2(X1)
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X3,X0) != iProver_top
    | r2_hidden(k4_tarski(X3,X2),k1_wellord2(X0)) != iProver_top
    | r1_tarski(X3,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_355])).

cnf(c_1787,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1)) != iProver_top
    | r1_tarski(X2,X0) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1466])).

cnf(c_2884,plain,
    ( r2_hidden(sK3(k1_wellord2(X0),X1),X0) != iProver_top
    | r2_hidden(sK2(k1_wellord2(X0),X1),X0) != iProver_top
    | r1_tarski(sK2(k1_wellord2(X0),X1),sK3(k1_wellord2(X0),X1)) = iProver_top
    | r8_relat_2(k1_wellord2(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1473,c_1787])).

cnf(c_12,plain,
    ( r2_hidden(sK4(X0,X1),X1)
    | r8_relat_2(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_253,plain,
    ( r2_hidden(sK4(X0,X1),X1)
    | r8_relat_2(X0,X1)
    | k1_wellord2(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_16])).

cnf(c_254,plain,
    ( r2_hidden(sK4(k1_wellord2(X0),X1),X1)
    | r8_relat_2(k1_wellord2(X0),X1) ),
    inference(unflattening,[status(thm)],[c_253])).

cnf(c_1474,plain,
    ( r2_hidden(sK4(k1_wellord2(X0),X1),X1) = iProver_top
    | r8_relat_2(k1_wellord2(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_254])).

cnf(c_10,plain,
    ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
    | r8_relat_2(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_277,plain,
    ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
    | r8_relat_2(X0,X1)
    | k1_wellord2(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_16])).

cnf(c_278,plain,
    ( r2_hidden(k4_tarski(sK3(k1_wellord2(X0),X1),sK4(k1_wellord2(X0),X1)),k1_wellord2(X0))
    | r8_relat_2(k1_wellord2(X0),X1) ),
    inference(unflattening,[status(thm)],[c_277])).

cnf(c_1472,plain,
    ( r2_hidden(k4_tarski(sK3(k1_wellord2(X0),X1),sK4(k1_wellord2(X0),X1)),k1_wellord2(X0)) = iProver_top
    | r8_relat_2(k1_wellord2(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_278])).

cnf(c_2299,plain,
    ( r2_hidden(sK3(k1_wellord2(X0),X1),X0) != iProver_top
    | r2_hidden(sK4(k1_wellord2(X0),X1),X0) != iProver_top
    | r1_tarski(sK3(k1_wellord2(X0),X1),sK4(k1_wellord2(X0),X1)) = iProver_top
    | r8_relat_2(k1_wellord2(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1472,c_1787])).

cnf(c_17,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1478,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2937,plain,
    ( r2_hidden(sK3(k1_wellord2(X0),X1),X0) != iProver_top
    | r2_hidden(sK4(k1_wellord2(X0),X1),X0) != iProver_top
    | r1_tarski(X2,sK3(k1_wellord2(X0),X1)) != iProver_top
    | r1_tarski(X2,sK4(k1_wellord2(X0),X1)) = iProver_top
    | r8_relat_2(k1_wellord2(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2299,c_1478])).

cnf(c_3041,plain,
    ( r2_hidden(sK3(k1_wellord2(X0),X0),X0) != iProver_top
    | r1_tarski(X1,sK3(k1_wellord2(X0),X0)) != iProver_top
    | r1_tarski(X1,sK4(k1_wellord2(X0),X0)) = iProver_top
    | r8_relat_2(k1_wellord2(X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1474,c_2937])).

cnf(c_13,plain,
    ( r2_hidden(sK3(X0,X1),X1)
    | r8_relat_2(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_241,plain,
    ( r2_hidden(sK3(X0,X1),X1)
    | r8_relat_2(X0,X1)
    | k1_wellord2(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_16])).

cnf(c_242,plain,
    ( r2_hidden(sK3(k1_wellord2(X0),X1),X1)
    | r8_relat_2(k1_wellord2(X0),X1) ),
    inference(unflattening,[status(thm)],[c_241])).

cnf(c_1475,plain,
    ( r2_hidden(sK3(k1_wellord2(X0),X1),X1) = iProver_top
    | r8_relat_2(k1_wellord2(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_242])).

cnf(c_3486,plain,
    ( r1_tarski(X0,sK3(k1_wellord2(X1),X1)) != iProver_top
    | r1_tarski(X0,sK4(k1_wellord2(X1),X1)) = iProver_top
    | r8_relat_2(k1_wellord2(X1),X1) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3041,c_1475])).

cnf(c_3490,plain,
    ( r2_hidden(sK3(k1_wellord2(X0),X0),X0) != iProver_top
    | r2_hidden(sK2(k1_wellord2(X0),X0),X0) != iProver_top
    | r1_tarski(sK2(k1_wellord2(X0),X0),sK4(k1_wellord2(X0),X0)) = iProver_top
    | r8_relat_2(k1_wellord2(X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2884,c_3486])).

cnf(c_3492,plain,
    ( r2_hidden(sK3(k1_wellord2(sK5),sK5),sK5) != iProver_top
    | r2_hidden(sK2(k1_wellord2(sK5),sK5),sK5) != iProver_top
    | r1_tarski(sK2(k1_wellord2(sK5),sK5),sK4(k1_wellord2(sK5),sK5)) = iProver_top
    | r8_relat_2(k1_wellord2(sK5),sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3490])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1))
    | ~ r1_tarski(X2,X0)
    | ~ v1_relat_1(k1_wellord2(X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_375,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1))
    | ~ r1_tarski(X2,X0)
    | k1_wellord2(X1) != k1_wellord2(X3) ),
    inference(resolution_lifted,[status(thm)],[c_16,c_6])).

cnf(c_1465,plain,
    ( k1_wellord2(X0) != k1_wellord2(X1)
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X3,X0) != iProver_top
    | r2_hidden(k4_tarski(X3,X2),k1_wellord2(X0)) = iProver_top
    | r1_tarski(X3,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_375])).

cnf(c_1687,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1)) = iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1465])).

cnf(c_9,plain,
    ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK4(X0,X1)),X0)
    | r8_relat_2(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_289,plain,
    ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK4(X0,X1)),X0)
    | r8_relat_2(X0,X1)
    | k1_wellord2(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_16])).

cnf(c_290,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k1_wellord2(X0),X1),sK4(k1_wellord2(X0),X1)),k1_wellord2(X0))
    | r8_relat_2(k1_wellord2(X0),X1) ),
    inference(unflattening,[status(thm)],[c_289])).

cnf(c_1471,plain,
    ( r2_hidden(k4_tarski(sK2(k1_wellord2(X0),X1),sK4(k1_wellord2(X0),X1)),k1_wellord2(X0)) != iProver_top
    | r8_relat_2(k1_wellord2(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_290])).

cnf(c_1696,plain,
    ( r2_hidden(sK4(k1_wellord2(X0),X1),X0) != iProver_top
    | r2_hidden(sK2(k1_wellord2(X0),X1),X0) != iProver_top
    | r1_tarski(sK2(k1_wellord2(X0),X1),sK4(k1_wellord2(X0),X1)) != iProver_top
    | r8_relat_2(k1_wellord2(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1687,c_1471])).

cnf(c_1698,plain,
    ( r2_hidden(sK4(k1_wellord2(sK5),sK5),sK5) != iProver_top
    | r2_hidden(sK2(k1_wellord2(sK5),sK5),sK5) != iProver_top
    | r1_tarski(sK2(k1_wellord2(sK5),sK5),sK4(k1_wellord2(sK5),sK5)) != iProver_top
    | r8_relat_2(k1_wellord2(sK5),sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1696])).

cnf(c_0,plain,
    ( ~ r8_relat_2(X0,k3_relat_1(X0))
    | ~ v1_relat_1(X0)
    | v8_relat_2(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_18,negated_conjecture,
    ( ~ v8_relat_2(k1_wellord2(sK5)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_216,plain,
    ( ~ r8_relat_2(X0,k3_relat_1(X0))
    | ~ v1_relat_1(X0)
    | k1_wellord2(sK5) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_18])).

cnf(c_217,plain,
    ( ~ r8_relat_2(k1_wellord2(sK5),k3_relat_1(k1_wellord2(sK5)))
    | ~ v1_relat_1(k1_wellord2(sK5)) ),
    inference(unflattening,[status(thm)],[c_216])).

cnf(c_22,plain,
    ( v1_relat_1(k1_wellord2(sK5)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_219,plain,
    ( ~ r8_relat_2(k1_wellord2(sK5),k3_relat_1(k1_wellord2(sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_217,c_22])).

cnf(c_1477,plain,
    ( r8_relat_2(k1_wellord2(sK5),k3_relat_1(k1_wellord2(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_219])).

cnf(c_8,plain,
    ( ~ v1_relat_1(k1_wellord2(X0))
    | k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_119,plain,
    ( k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8,c_16])).

cnf(c_1481,plain,
    ( r8_relat_2(k1_wellord2(sK5),sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1477,c_119])).

cnf(c_255,plain,
    ( r2_hidden(sK4(k1_wellord2(X0),X1),X1) = iProver_top
    | r8_relat_2(k1_wellord2(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_254])).

cnf(c_257,plain,
    ( r2_hidden(sK4(k1_wellord2(sK5),sK5),sK5) = iProver_top
    | r8_relat_2(k1_wellord2(sK5),sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_255])).

cnf(c_243,plain,
    ( r2_hidden(sK3(k1_wellord2(X0),X1),X1) = iProver_top
    | r8_relat_2(k1_wellord2(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_242])).

cnf(c_245,plain,
    ( r2_hidden(sK3(k1_wellord2(sK5),sK5),sK5) = iProver_top
    | r8_relat_2(k1_wellord2(sK5),sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_243])).

cnf(c_14,plain,
    ( r2_hidden(sK2(X0,X1),X1)
    | r8_relat_2(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_229,plain,
    ( r2_hidden(sK2(X0,X1),X1)
    | r8_relat_2(X0,X1)
    | k1_wellord2(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_16])).

cnf(c_230,plain,
    ( r2_hidden(sK2(k1_wellord2(X0),X1),X1)
    | r8_relat_2(k1_wellord2(X0),X1) ),
    inference(unflattening,[status(thm)],[c_229])).

cnf(c_231,plain,
    ( r2_hidden(sK2(k1_wellord2(X0),X1),X1) = iProver_top
    | r8_relat_2(k1_wellord2(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_230])).

cnf(c_233,plain,
    ( r2_hidden(sK2(k1_wellord2(sK5),sK5),sK5) = iProver_top
    | r8_relat_2(k1_wellord2(sK5),sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_231])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3492,c_1698,c_1481,c_257,c_245,c_233])).


%------------------------------------------------------------------------------
