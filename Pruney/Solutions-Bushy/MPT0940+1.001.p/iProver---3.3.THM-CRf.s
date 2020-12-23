%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0940+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:28 EST 2020

% Result     : Theorem 1.04s
% Output     : CNFRefutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 161 expanded)
%              Number of clauses        :   47 (  59 expanded)
%              Number of leaves         :    9 (  29 expanded)
%              Depth                    :   15
%              Number of atoms          :  364 ( 900 expanded)
%              Number of equality atoms :  107 ( 206 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   17 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X3,X2),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) )
             => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( X2 = X3
              | ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( X2 = X3
              | ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r4_relat_2(X0,X1)
            | ? [X2,X3] :
                ( X2 != X3
                & r2_hidden(k4_tarski(X3,X2),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X2,X3] :
                ( X2 = X3
                | ~ r2_hidden(k4_tarski(X3,X2),X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X0)
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1) )
            | ~ r4_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r4_relat_2(X0,X1)
            | ? [X2,X3] :
                ( X2 != X3
                & r2_hidden(k4_tarski(X3,X2),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X4,X5] :
                ( X4 = X5
                | ~ r2_hidden(k4_tarski(X5,X4),X0)
                | ~ r2_hidden(k4_tarski(X4,X5),X0)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r4_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X2 != X3
          & r2_hidden(k4_tarski(X3,X2),X0)
          & r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( sK2(X0,X1) != sK3(X0,X1)
        & r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
        & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
        & r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r4_relat_2(X0,X1)
            | ( sK2(X0,X1) != sK3(X0,X1)
              & r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
              & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
              & r2_hidden(sK3(X0,X1),X1)
              & r2_hidden(sK2(X0,X1),X1) ) )
          & ( ! [X4,X5] :
                ( X4 = X5
                | ~ r2_hidden(k4_tarski(X5,X4),X0)
                | ~ r2_hidden(k4_tarski(X4,X5),X0)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r4_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f23,f24])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r4_relat_2(X0,X1)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

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

fof(f34,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_tarski(X4,X5)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f55,plain,(
    ! [X4,X0,X5] :
      ( r1_tarski(X4,X5)
      | ~ r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r4_relat_2(X0,X1)
      | r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f14])).

fof(f30,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v4_relat_2(X0)
      <=> r4_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> r4_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ~ r4_relat_2(X0,k3_relat_1(X0)) )
        & ( r4_relat_2(X0,k3_relat_1(X0))
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | ~ r4_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,conjecture,(
    ! [X0] : v4_relat_2(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] : v4_relat_2(k1_wellord2(X0)) ),
    inference(negated_conjecture,[],[f6])).

fof(f13,plain,(
    ? [X0] : ~ v4_relat_2(k1_wellord2(X0)) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,
    ( ? [X0] : ~ v4_relat_2(k1_wellord2(X0))
   => ~ v4_relat_2(k1_wellord2(sK4)) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ~ v4_relat_2(k1_wellord2(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f26])).

fof(f47,plain,(
    ~ v4_relat_2(k1_wellord2(sK4)) ),
    inference(cnf_transformation,[],[f27])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f56,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r4_relat_2(X0,X1)
      | sK2(X0,X1) != sK3(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r4_relat_2(X0,X1)
      | r2_hidden(sK3(X0,X1),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r4_relat_2(X0,X1)
      | r2_hidden(sK2(X0,X1),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_14,plain,
    ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
    | r4_relat_2(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_18,plain,
    ( v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_262,plain,
    ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
    | r4_relat_2(X0,X1)
    | k1_wellord2(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_18])).

cnf(c_263,plain,
    ( r2_hidden(k4_tarski(sK2(k1_wellord2(X0),X1),sK3(k1_wellord2(X0),X1)),k1_wellord2(X0))
    | r4_relat_2(k1_wellord2(X0),X1) ),
    inference(unflattening,[status(thm)],[c_262])).

cnf(c_1324,plain,
    ( r2_hidden(k4_tarski(sK2(k1_wellord2(X0),X1),sK3(k1_wellord2(X0),X1)),k1_wellord2(X0)) = iProver_top
    | r4_relat_2(k1_wellord2(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_263])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1))
    | r1_tarski(X2,X0)
    | ~ v1_relat_1(k1_wellord2(X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_352,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1))
    | r1_tarski(X2,X0)
    | k1_wellord2(X1) != k1_wellord2(X3) ),
    inference(resolution_lifted,[status(thm)],[c_18,c_10])).

cnf(c_1317,plain,
    ( k1_wellord2(X0) != k1_wellord2(X1)
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X3,X0) != iProver_top
    | r2_hidden(k4_tarski(X3,X2),k1_wellord2(X0)) != iProver_top
    | r1_tarski(X3,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_352])).

cnf(c_1730,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1)) != iProver_top
    | r1_tarski(X2,X0) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1317])).

cnf(c_2296,plain,
    ( r2_hidden(sK3(k1_wellord2(X0),X1),X0) != iProver_top
    | r2_hidden(sK2(k1_wellord2(X0),X1),X0) != iProver_top
    | r4_relat_2(k1_wellord2(X0),X1) = iProver_top
    | r1_tarski(sK2(k1_wellord2(X0),X1),sK3(k1_wellord2(X0),X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1324,c_1730])).

cnf(c_2336,plain,
    ( r2_hidden(sK3(k1_wellord2(sK4),sK4),sK4) != iProver_top
    | r2_hidden(sK2(k1_wellord2(sK4),sK4),sK4) != iProver_top
    | r4_relat_2(k1_wellord2(sK4),sK4) = iProver_top
    | r1_tarski(sK2(k1_wellord2(sK4),sK4),sK3(k1_wellord2(sK4),sK4)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2296])).

cnf(c_13,plain,
    ( r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
    | r4_relat_2(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_274,plain,
    ( r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
    | r4_relat_2(X0,X1)
    | k1_wellord2(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_18])).

cnf(c_275,plain,
    ( r2_hidden(k4_tarski(sK3(k1_wellord2(X0),X1),sK2(k1_wellord2(X0),X1)),k1_wellord2(X0))
    | r4_relat_2(k1_wellord2(X0),X1) ),
    inference(unflattening,[status(thm)],[c_274])).

cnf(c_1323,plain,
    ( r2_hidden(k4_tarski(sK3(k1_wellord2(X0),X1),sK2(k1_wellord2(X0),X1)),k1_wellord2(X0)) = iProver_top
    | r4_relat_2(k1_wellord2(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_275])).

cnf(c_2073,plain,
    ( r2_hidden(sK3(k1_wellord2(X0),X1),X0) != iProver_top
    | r2_hidden(sK2(k1_wellord2(X0),X1),X0) != iProver_top
    | r4_relat_2(k1_wellord2(X0),X1) = iProver_top
    | r1_tarski(sK3(k1_wellord2(X0),X1),sK2(k1_wellord2(X0),X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1323,c_1730])).

cnf(c_2083,plain,
    ( r2_hidden(sK3(k1_wellord2(sK4),sK4),sK4) != iProver_top
    | r2_hidden(sK2(k1_wellord2(sK4),sK4),sK4) != iProver_top
    | r4_relat_2(k1_wellord2(sK4),sK4) = iProver_top
    | r1_tarski(sK3(k1_wellord2(sK4),sK4),sK2(k1_wellord2(sK4),sK4)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2073])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1431,plain,
    ( ~ r1_tarski(sK3(k1_wellord2(X0),X1),sK2(k1_wellord2(X0),X1))
    | ~ r1_tarski(sK2(k1_wellord2(X0),X1),sK3(k1_wellord2(X0),X1))
    | sK3(k1_wellord2(X0),X1) = sK2(k1_wellord2(X0),X1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1432,plain,
    ( sK3(k1_wellord2(X0),X1) = sK2(k1_wellord2(X0),X1)
    | r1_tarski(sK3(k1_wellord2(X0),X1),sK2(k1_wellord2(X0),X1)) != iProver_top
    | r1_tarski(sK2(k1_wellord2(X0),X1),sK3(k1_wellord2(X0),X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1431])).

cnf(c_1434,plain,
    ( sK3(k1_wellord2(sK4),sK4) = sK2(k1_wellord2(sK4),sK4)
    | r1_tarski(sK3(k1_wellord2(sK4),sK4),sK2(k1_wellord2(sK4),sK4)) != iProver_top
    | r1_tarski(sK2(k1_wellord2(sK4),sK4),sK3(k1_wellord2(sK4),sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1432])).

cnf(c_3,plain,
    ( ~ r4_relat_2(X0,k3_relat_1(X0))
    | ~ v1_relat_1(X0)
    | v4_relat_2(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_19,negated_conjecture,
    ( ~ v4_relat_2(k1_wellord2(sK4)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_225,plain,
    ( ~ r4_relat_2(X0,k3_relat_1(X0))
    | ~ v1_relat_1(X0)
    | k1_wellord2(sK4) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_19])).

cnf(c_226,plain,
    ( ~ r4_relat_2(k1_wellord2(sK4),k3_relat_1(k1_wellord2(sK4)))
    | ~ v1_relat_1(k1_wellord2(sK4)) ),
    inference(unflattening,[status(thm)],[c_225])).

cnf(c_22,plain,
    ( v1_relat_1(k1_wellord2(sK4)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_228,plain,
    ( ~ r4_relat_2(k1_wellord2(sK4),k3_relat_1(k1_wellord2(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_226,c_22])).

cnf(c_1327,plain,
    ( r4_relat_2(k1_wellord2(sK4),k3_relat_1(k1_wellord2(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_228])).

cnf(c_11,plain,
    ( ~ v1_relat_1(k1_wellord2(X0))
    | k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_125,plain,
    ( k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_18])).

cnf(c_1334,plain,
    ( r4_relat_2(k1_wellord2(sK4),sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1327,c_125])).

cnf(c_12,plain,
    ( r4_relat_2(X0,X1)
    | ~ v1_relat_1(X0)
    | sK3(X0,X1) != sK2(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_286,plain,
    ( r4_relat_2(X0,X1)
    | sK3(X0,X1) != sK2(X0,X1)
    | k1_wellord2(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_18])).

cnf(c_287,plain,
    ( r4_relat_2(k1_wellord2(X0),X1)
    | sK3(k1_wellord2(X0),X1) != sK2(k1_wellord2(X0),X1) ),
    inference(unflattening,[status(thm)],[c_286])).

cnf(c_288,plain,
    ( sK3(k1_wellord2(X0),X1) != sK2(k1_wellord2(X0),X1)
    | r4_relat_2(k1_wellord2(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_287])).

cnf(c_290,plain,
    ( sK3(k1_wellord2(sK4),sK4) != sK2(k1_wellord2(sK4),sK4)
    | r4_relat_2(k1_wellord2(sK4),sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_288])).

cnf(c_15,plain,
    ( r2_hidden(sK3(X0,X1),X1)
    | r4_relat_2(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_250,plain,
    ( r2_hidden(sK3(X0,X1),X1)
    | r4_relat_2(X0,X1)
    | k1_wellord2(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_18])).

cnf(c_251,plain,
    ( r2_hidden(sK3(k1_wellord2(X0),X1),X1)
    | r4_relat_2(k1_wellord2(X0),X1) ),
    inference(unflattening,[status(thm)],[c_250])).

cnf(c_252,plain,
    ( r2_hidden(sK3(k1_wellord2(X0),X1),X1) = iProver_top
    | r4_relat_2(k1_wellord2(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_251])).

cnf(c_254,plain,
    ( r2_hidden(sK3(k1_wellord2(sK4),sK4),sK4) = iProver_top
    | r4_relat_2(k1_wellord2(sK4),sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_252])).

cnf(c_16,plain,
    ( r2_hidden(sK2(X0,X1),X1)
    | r4_relat_2(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_238,plain,
    ( r2_hidden(sK2(X0,X1),X1)
    | r4_relat_2(X0,X1)
    | k1_wellord2(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_18])).

cnf(c_239,plain,
    ( r2_hidden(sK2(k1_wellord2(X0),X1),X1)
    | r4_relat_2(k1_wellord2(X0),X1) ),
    inference(unflattening,[status(thm)],[c_238])).

cnf(c_240,plain,
    ( r2_hidden(sK2(k1_wellord2(X0),X1),X1) = iProver_top
    | r4_relat_2(k1_wellord2(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_239])).

cnf(c_242,plain,
    ( r2_hidden(sK2(k1_wellord2(sK4),sK4),sK4) = iProver_top
    | r4_relat_2(k1_wellord2(sK4),sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_240])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2336,c_2083,c_1434,c_1334,c_290,c_254,c_242])).


%------------------------------------------------------------------------------
