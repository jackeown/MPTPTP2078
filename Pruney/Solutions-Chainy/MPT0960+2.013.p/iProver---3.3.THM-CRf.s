%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:50 EST 2020

% Result     : Theorem 15.62s
% Output     : CNFRefutation 15.62s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 229 expanded)
%              Number of clauses        :   64 (  75 expanded)
%              Number of leaves         :   20 (  59 expanded)
%              Depth                    :   15
%              Number of atoms          :  472 (1153 expanded)
%              Number of equality atoms :  143 ( 277 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   17 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK7(X0,X1),sK8(X0,X1))
          | ~ r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1) )
        & ( r1_tarski(sK7(X0,X1),sK8(X0,X1))
          | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1) )
        & r2_hidden(sK8(X0,X1),X0)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK7(X0,X1),sK8(X0,X1))
              | ~ r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1) )
            & ( r1_tarski(sK7(X0,X1),sK8(X0,X1))
              | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1) )
            & r2_hidden(sK8(X0,X1),X0)
            & r2_hidden(sK7(X0,X1),X0) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f38,f39])).

fof(f62,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f79,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f34,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f31,f34,f33,f32])).

fof(f54,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f73,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f53,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f74,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f28,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f25,f28,f27,f26])).

fof(f50,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f71,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( k1_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f49,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f72,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f81,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f60])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f57,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,conjecture,(
    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(negated_conjecture,[],[f9])).

fof(f17,plain,(
    ? [X0] : ~ r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(ennf_transformation,[],[f10])).

fof(f41,plain,
    ( ? [X0] : ~ r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))
   => ~ r1_tarski(k1_wellord2(sK9),k2_zfmisc_1(sK9,sK9)) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ~ r1_tarski(k1_wellord2(sK9),k2_zfmisc_1(sK9,sK9)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f17,f41])).

fof(f68,plain,(
    ~ r1_tarski(k1_wellord2(sK9),k2_zfmisc_1(sK9,sK9)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_24,plain,
    ( v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1))
    | ~ r1_tarski(X2,X0)
    | ~ v1_relat_1(k1_wellord2(X1)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_976,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1))
    | ~ r1_tarski(X2,X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_24,c_21])).

cnf(c_12,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_18166,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r2_hidden(X0,k2_relat_1(k1_wellord2(X1)))
    | ~ r1_tarski(X2,X0) ),
    inference(resolution,[status(thm)],[c_976,c_12])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_68225,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_relat_1(k1_wellord2(X1))) ),
    inference(resolution,[status(thm)],[c_18166,c_5])).

cnf(c_10,plain,
    ( ~ r2_hidden(sK4(X0,X1),X1)
    | ~ r2_hidden(k4_tarski(X2,sK4(X0,X1)),X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK6(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_6729,plain,
    ( ~ r2_hidden(sK4(X0,X1),X1)
    | ~ r2_hidden(sK4(X0,X1),k2_relat_1(X0))
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_10,c_13])).

cnf(c_69246,plain,
    ( ~ r2_hidden(sK4(k1_wellord2(X0),X1),X0)
    | ~ r2_hidden(sK4(k1_wellord2(X0),X1),X1)
    | k2_relat_1(k1_wellord2(X0)) = X1 ),
    inference(resolution,[status(thm)],[c_68225,c_6729])).

cnf(c_69248,plain,
    ( ~ r2_hidden(sK4(k1_wellord2(sK9),sK9),sK9)
    | k2_relat_1(k1_wellord2(sK9)) = sK9 ),
    inference(instantiation,[status(thm)],[c_69246])).

cnf(c_8,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_18152,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r2_hidden(X2,k1_relat_1(k1_wellord2(X1)))
    | ~ r1_tarski(X2,X0) ),
    inference(resolution,[status(thm)],[c_976,c_8])).

cnf(c_67613,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k1_relat_1(k1_wellord2(X1))) ),
    inference(resolution,[status(thm)],[c_18152,c_5])).

cnf(c_6,plain,
    ( ~ r2_hidden(k4_tarski(sK1(X0,X1),X2),X0)
    | ~ r2_hidden(sK1(X0,X1),X1)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_6622,plain,
    ( ~ r2_hidden(sK1(X0,X1),X1)
    | ~ r2_hidden(sK1(X0,X1),k1_relat_1(X0))
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_6,c_9])).

cnf(c_69107,plain,
    ( ~ r2_hidden(sK1(k1_wellord2(X0),X1),X0)
    | ~ r2_hidden(sK1(k1_wellord2(X0),X1),X1)
    | k1_relat_1(k1_wellord2(X0)) = X1 ),
    inference(resolution,[status(thm)],[c_67613,c_6622])).

cnf(c_69109,plain,
    ( ~ r2_hidden(sK1(k1_wellord2(sK9),sK9),sK9)
    | k1_relat_1(k1_wellord2(sK9)) = sK9 ),
    inference(instantiation,[status(thm)],[c_69107])).

cnf(c_23,plain,
    ( ~ v1_relat_1(k1_wellord2(X0))
    | k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_194,plain,
    ( k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_23,c_24])).

cnf(c_7,plain,
    ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
    | r2_hidden(sK1(X0,X1),X1)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_758,plain,
    ( k1_relat_1(X0) = X1
    | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_16,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_749,plain,
    ( r2_hidden(X0,k3_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2944,plain,
    ( k1_relat_1(X0) = X1
    | r2_hidden(sK1(X0,X1),X1) = iProver_top
    | r2_hidden(sK1(X0,X1),k3_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_758,c_749])).

cnf(c_30121,plain,
    ( k1_relat_1(k1_wellord2(X0)) = X1
    | r2_hidden(sK1(k1_wellord2(X0),X1),X1) = iProver_top
    | r2_hidden(sK1(k1_wellord2(X0),X1),X0) = iProver_top
    | v1_relat_1(k1_wellord2(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_194,c_2944])).

cnf(c_30250,plain,
    ( r2_hidden(sK1(k1_wellord2(X0),X1),X1)
    | r2_hidden(sK1(k1_wellord2(X0),X1),X0)
    | ~ v1_relat_1(k1_wellord2(X0))
    | k1_relat_1(k1_wellord2(X0)) = X1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_30121])).

cnf(c_30252,plain,
    ( r2_hidden(sK1(k1_wellord2(sK9),sK9),sK9)
    | ~ v1_relat_1(k1_wellord2(sK9))
    | k1_relat_1(k1_wellord2(sK9)) = sK9 ),
    inference(instantiation,[status(thm)],[c_30250])).

cnf(c_11,plain,
    ( r2_hidden(sK4(X0,X1),X1)
    | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_754,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(sK4(X0,X1),X1) = iProver_top
    | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_15,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_750,plain,
    ( r2_hidden(X0,k3_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2714,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(sK4(X0,X1),X1) = iProver_top
    | r2_hidden(sK4(X0,X1),k3_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_754,c_750])).

cnf(c_29957,plain,
    ( k2_relat_1(k1_wellord2(X0)) = X1
    | r2_hidden(sK4(k1_wellord2(X0),X1),X1) = iProver_top
    | r2_hidden(sK4(k1_wellord2(X0),X1),X0) = iProver_top
    | v1_relat_1(k1_wellord2(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_194,c_2714])).

cnf(c_30086,plain,
    ( r2_hidden(sK4(k1_wellord2(X0),X1),X1)
    | r2_hidden(sK4(k1_wellord2(X0),X1),X0)
    | ~ v1_relat_1(k1_wellord2(X0))
    | k2_relat_1(k1_wellord2(X0)) = X1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_29957])).

cnf(c_30088,plain,
    ( r2_hidden(sK4(k1_wellord2(sK9),sK9),sK9)
    | ~ v1_relat_1(k1_wellord2(sK9))
    | k2_relat_1(k1_wellord2(sK9)) = sK9 ),
    inference(instantiation,[status(thm)],[c_30086])).

cnf(c_358,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1328,plain,
    ( X0 != X1
    | k2_zfmisc_1(sK9,sK9) != X1
    | k2_zfmisc_1(sK9,sK9) = X0 ),
    inference(instantiation,[status(thm)],[c_358])).

cnf(c_2338,plain,
    ( X0 != k2_zfmisc_1(sK9,sK9)
    | k2_zfmisc_1(sK9,sK9) = X0
    | k2_zfmisc_1(sK9,sK9) != k2_zfmisc_1(sK9,sK9) ),
    inference(instantiation,[status(thm)],[c_1328])).

cnf(c_5699,plain,
    ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK9,sK9)
    | k2_zfmisc_1(sK9,sK9) = k2_zfmisc_1(X0,X1)
    | k2_zfmisc_1(sK9,sK9) != k2_zfmisc_1(sK9,sK9) ),
    inference(instantiation,[status(thm)],[c_2338])).

cnf(c_18414,plain,
    ( k2_zfmisc_1(k1_relat_1(k1_wellord2(sK9)),k2_relat_1(k1_wellord2(sK9))) != k2_zfmisc_1(sK9,sK9)
    | k2_zfmisc_1(sK9,sK9) = k2_zfmisc_1(k1_relat_1(k1_wellord2(sK9)),k2_relat_1(k1_wellord2(sK9)))
    | k2_zfmisc_1(sK9,sK9) != k2_zfmisc_1(sK9,sK9) ),
    inference(instantiation,[status(thm)],[c_5699])).

cnf(c_362,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_12882,plain,
    ( k2_zfmisc_1(k1_relat_1(k1_wellord2(sK9)),k2_relat_1(k1_wellord2(sK9))) = k2_zfmisc_1(X0,X1)
    | k2_relat_1(k1_wellord2(sK9)) != X1
    | k1_relat_1(k1_wellord2(sK9)) != X0 ),
    inference(instantiation,[status(thm)],[c_362])).

cnf(c_12884,plain,
    ( k2_zfmisc_1(k1_relat_1(k1_wellord2(sK9)),k2_relat_1(k1_wellord2(sK9))) = k2_zfmisc_1(sK9,sK9)
    | k2_relat_1(k1_wellord2(sK9)) != sK9
    | k1_relat_1(k1_wellord2(sK9)) != sK9 ),
    inference(instantiation,[status(thm)],[c_12882])).

cnf(c_359,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_998,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_wellord2(sK9),k2_zfmisc_1(sK9,sK9))
    | k2_zfmisc_1(sK9,sK9) != X1
    | k1_wellord2(sK9) != X0 ),
    inference(instantiation,[status(thm)],[c_359])).

cnf(c_1098,plain,
    ( ~ r1_tarski(k1_wellord2(X0),X1)
    | r1_tarski(k1_wellord2(sK9),k2_zfmisc_1(sK9,sK9))
    | k2_zfmisc_1(sK9,sK9) != X1
    | k1_wellord2(sK9) != k1_wellord2(X0) ),
    inference(instantiation,[status(thm)],[c_998])).

cnf(c_1329,plain,
    ( ~ r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X1,X2))
    | r1_tarski(k1_wellord2(sK9),k2_zfmisc_1(sK9,sK9))
    | k2_zfmisc_1(sK9,sK9) != k2_zfmisc_1(X1,X2)
    | k1_wellord2(sK9) != k1_wellord2(X0) ),
    inference(instantiation,[status(thm)],[c_1098])).

cnf(c_2648,plain,
    ( ~ r1_tarski(k1_wellord2(X0),k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0))))
    | r1_tarski(k1_wellord2(sK9),k2_zfmisc_1(sK9,sK9))
    | k2_zfmisc_1(sK9,sK9) != k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0)))
    | k1_wellord2(sK9) != k1_wellord2(X0) ),
    inference(instantiation,[status(thm)],[c_1329])).

cnf(c_2650,plain,
    ( ~ r1_tarski(k1_wellord2(sK9),k2_zfmisc_1(k1_relat_1(k1_wellord2(sK9)),k2_relat_1(k1_wellord2(sK9))))
    | r1_tarski(k1_wellord2(sK9),k2_zfmisc_1(sK9,sK9))
    | k2_zfmisc_1(sK9,sK9) != k2_zfmisc_1(k1_relat_1(k1_wellord2(sK9)),k2_relat_1(k1_wellord2(sK9)))
    | k1_wellord2(sK9) != k1_wellord2(sK9) ),
    inference(instantiation,[status(thm)],[c_2648])).

cnf(c_14,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_961,plain,
    ( r1_tarski(k1_wellord2(X0),k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0))))
    | ~ v1_relat_1(k1_wellord2(X0)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_963,plain,
    ( r1_tarski(k1_wellord2(sK9),k2_zfmisc_1(k1_relat_1(k1_wellord2(sK9)),k2_relat_1(k1_wellord2(sK9))))
    | ~ v1_relat_1(k1_wellord2(sK9)) ),
    inference(instantiation,[status(thm)],[c_961])).

cnf(c_365,plain,
    ( X0 != X1
    | k1_wellord2(X0) = k1_wellord2(X1) ),
    theory(equality)).

cnf(c_374,plain,
    ( k1_wellord2(sK9) = k1_wellord2(sK9)
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_365])).

cnf(c_371,plain,
    ( k2_zfmisc_1(sK9,sK9) = k2_zfmisc_1(sK9,sK9)
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_362])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_87,plain,
    ( ~ r1_tarski(sK9,sK9)
    | sK9 = sK9 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_83,plain,
    ( r1_tarski(sK9,sK9) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_28,plain,
    ( v1_relat_1(k1_wellord2(sK9)) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_25,negated_conjecture,
    ( ~ r1_tarski(k1_wellord2(sK9),k2_zfmisc_1(sK9,sK9)) ),
    inference(cnf_transformation,[],[f68])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_69248,c_69109,c_30252,c_30088,c_18414,c_12884,c_2650,c_963,c_374,c_371,c_87,c_83,c_28,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:44:54 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 15.62/2.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.62/2.49  
% 15.62/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.62/2.49  
% 15.62/2.49  ------  iProver source info
% 15.62/2.49  
% 15.62/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.62/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.62/2.49  git: non_committed_changes: false
% 15.62/2.49  git: last_make_outside_of_git: false
% 15.62/2.49  
% 15.62/2.49  ------ 
% 15.62/2.49  ------ Parsing...
% 15.62/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.62/2.49  
% 15.62/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 15.62/2.49  
% 15.62/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.62/2.49  
% 15.62/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.62/2.49  ------ Proving...
% 15.62/2.49  ------ Problem Properties 
% 15.62/2.49  
% 15.62/2.49  
% 15.62/2.49  clauses                                 25
% 15.62/2.49  conjectures                             1
% 15.62/2.49  EPR                                     3
% 15.62/2.49  Horn                                    19
% 15.62/2.49  unary                                   4
% 15.62/2.49  binary                                  7
% 15.62/2.49  lits                                    66
% 15.62/2.49  lits eq                                 10
% 15.62/2.49  fd_pure                                 0
% 15.62/2.49  fd_pseudo                               0
% 15.62/2.49  fd_cond                                 0
% 15.62/2.49  fd_pseudo_cond                          5
% 15.62/2.49  AC symbols                              0
% 15.62/2.49  
% 15.62/2.49  ------ Input Options Time Limit: Unbounded
% 15.62/2.49  
% 15.62/2.49  
% 15.62/2.49  ------ 
% 15.62/2.49  Current options:
% 15.62/2.49  ------ 
% 15.62/2.49  
% 15.62/2.49  
% 15.62/2.49  
% 15.62/2.49  
% 15.62/2.49  ------ Proving...
% 15.62/2.49  
% 15.62/2.49  
% 15.62/2.49  % SZS status Theorem for theBenchmark.p
% 15.62/2.49  
% 15.62/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.62/2.49  
% 15.62/2.49  fof(f8,axiom,(
% 15.62/2.49    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 15.62/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.62/2.49  
% 15.62/2.49  fof(f67,plain,(
% 15.62/2.49    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 15.62/2.49    inference(cnf_transformation,[],[f8])).
% 15.62/2.49  
% 15.62/2.49  fof(f7,axiom,(
% 15.62/2.49    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 15.62/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.62/2.49  
% 15.62/2.49  fof(f15,plain,(
% 15.62/2.49    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 15.62/2.49    inference(ennf_transformation,[],[f7])).
% 15.62/2.49  
% 15.62/2.49  fof(f16,plain,(
% 15.62/2.49    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 15.62/2.49    inference(flattening,[],[f15])).
% 15.62/2.49  
% 15.62/2.49  fof(f36,plain,(
% 15.62/2.49    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 15.62/2.49    inference(nnf_transformation,[],[f16])).
% 15.62/2.49  
% 15.62/2.49  fof(f37,plain,(
% 15.62/2.49    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 15.62/2.49    inference(flattening,[],[f36])).
% 15.62/2.49  
% 15.62/2.49  fof(f38,plain,(
% 15.62/2.49    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 15.62/2.49    inference(rectify,[],[f37])).
% 15.62/2.49  
% 15.62/2.49  fof(f39,plain,(
% 15.62/2.49    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK7(X0,X1),sK8(X0,X1)) | ~r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1)) & (r1_tarski(sK7(X0,X1),sK8(X0,X1)) | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1)) & r2_hidden(sK8(X0,X1),X0) & r2_hidden(sK7(X0,X1),X0)))),
% 15.62/2.49    introduced(choice_axiom,[])).
% 15.62/2.49  
% 15.62/2.49  fof(f40,plain,(
% 15.62/2.49    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK7(X0,X1),sK8(X0,X1)) | ~r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1)) & (r1_tarski(sK7(X0,X1),sK8(X0,X1)) | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1)) & r2_hidden(sK8(X0,X1),X0) & r2_hidden(sK7(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 15.62/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f38,f39])).
% 15.62/2.49  
% 15.62/2.49  fof(f62,plain,(
% 15.62/2.49    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 15.62/2.49    inference(cnf_transformation,[],[f40])).
% 15.62/2.49  
% 15.62/2.49  fof(f79,plain,(
% 15.62/2.49    ( ! [X4,X0,X5] : (r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0)) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | ~v1_relat_1(k1_wellord2(X0))) )),
% 15.62/2.49    inference(equality_resolution,[],[f62])).
% 15.62/2.49  
% 15.62/2.49  fof(f4,axiom,(
% 15.62/2.49    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 15.62/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.62/2.49  
% 15.62/2.49  fof(f30,plain,(
% 15.62/2.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 15.62/2.49    inference(nnf_transformation,[],[f4])).
% 15.62/2.49  
% 15.62/2.49  fof(f31,plain,(
% 15.62/2.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 15.62/2.49    inference(rectify,[],[f30])).
% 15.62/2.49  
% 15.62/2.49  fof(f34,plain,(
% 15.62/2.49    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0))),
% 15.62/2.49    introduced(choice_axiom,[])).
% 15.62/2.49  
% 15.62/2.49  fof(f33,plain,(
% 15.62/2.49    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK5(X0,X1),X2),X0))) )),
% 15.62/2.49    introduced(choice_axiom,[])).
% 15.62/2.49  
% 15.62/2.49  fof(f32,plain,(
% 15.62/2.49    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 15.62/2.49    introduced(choice_axiom,[])).
% 15.62/2.49  
% 15.62/2.49  fof(f35,plain,(
% 15.62/2.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 15.62/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f31,f34,f33,f32])).
% 15.62/2.49  
% 15.62/2.49  fof(f54,plain,(
% 15.62/2.49    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 15.62/2.49    inference(cnf_transformation,[],[f35])).
% 15.62/2.49  
% 15.62/2.49  fof(f73,plain,(
% 15.62/2.49    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 15.62/2.49    inference(equality_resolution,[],[f54])).
% 15.62/2.49  
% 15.62/2.49  fof(f2,axiom,(
% 15.62/2.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.62/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.62/2.49  
% 15.62/2.49  fof(f22,plain,(
% 15.62/2.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.62/2.49    inference(nnf_transformation,[],[f2])).
% 15.62/2.49  
% 15.62/2.49  fof(f23,plain,(
% 15.62/2.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.62/2.49    inference(flattening,[],[f22])).
% 15.62/2.49  
% 15.62/2.49  fof(f46,plain,(
% 15.62/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 15.62/2.49    inference(cnf_transformation,[],[f23])).
% 15.62/2.49  
% 15.62/2.49  fof(f70,plain,(
% 15.62/2.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 15.62/2.49    inference(equality_resolution,[],[f46])).
% 15.62/2.49  
% 15.62/2.49  fof(f56,plain,(
% 15.62/2.49    ( ! [X0,X3,X1] : (k2_relat_1(X0) = X1 | ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) )),
% 15.62/2.49    inference(cnf_transformation,[],[f35])).
% 15.62/2.49  
% 15.62/2.49  fof(f53,plain,(
% 15.62/2.49    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 15.62/2.49    inference(cnf_transformation,[],[f35])).
% 15.62/2.49  
% 15.62/2.49  fof(f74,plain,(
% 15.62/2.49    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 15.62/2.49    inference(equality_resolution,[],[f53])).
% 15.62/2.49  
% 15.62/2.49  fof(f3,axiom,(
% 15.62/2.49    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 15.62/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.62/2.49  
% 15.62/2.49  fof(f24,plain,(
% 15.62/2.49    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 15.62/2.49    inference(nnf_transformation,[],[f3])).
% 15.62/2.49  
% 15.62/2.49  fof(f25,plain,(
% 15.62/2.49    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 15.62/2.49    inference(rectify,[],[f24])).
% 15.62/2.49  
% 15.62/2.49  fof(f28,plain,(
% 15.62/2.49    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0))),
% 15.62/2.49    introduced(choice_axiom,[])).
% 15.62/2.49  
% 15.62/2.49  fof(f27,plain,(
% 15.62/2.49    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0))) )),
% 15.62/2.49    introduced(choice_axiom,[])).
% 15.62/2.49  
% 15.62/2.49  fof(f26,plain,(
% 15.62/2.49    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 15.62/2.49    introduced(choice_axiom,[])).
% 15.62/2.49  
% 15.62/2.49  fof(f29,plain,(
% 15.62/2.49    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 15.62/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f25,f28,f27,f26])).
% 15.62/2.49  
% 15.62/2.49  fof(f50,plain,(
% 15.62/2.49    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 15.62/2.49    inference(cnf_transformation,[],[f29])).
% 15.62/2.49  
% 15.62/2.49  fof(f71,plain,(
% 15.62/2.49    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 15.62/2.49    inference(equality_resolution,[],[f50])).
% 15.62/2.49  
% 15.62/2.49  fof(f52,plain,(
% 15.62/2.49    ( ! [X0,X3,X1] : (k1_relat_1(X0) = X1 | ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 15.62/2.49    inference(cnf_transformation,[],[f29])).
% 15.62/2.49  
% 15.62/2.49  fof(f49,plain,(
% 15.62/2.49    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 15.62/2.49    inference(cnf_transformation,[],[f29])).
% 15.62/2.49  
% 15.62/2.49  fof(f72,plain,(
% 15.62/2.49    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 15.62/2.49    inference(equality_resolution,[],[f49])).
% 15.62/2.49  
% 15.62/2.49  fof(f60,plain,(
% 15.62/2.49    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 15.62/2.49    inference(cnf_transformation,[],[f40])).
% 15.62/2.49  
% 15.62/2.49  fof(f81,plain,(
% 15.62/2.49    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 15.62/2.49    inference(equality_resolution,[],[f60])).
% 15.62/2.49  
% 15.62/2.49  fof(f51,plain,(
% 15.62/2.49    ( ! [X0,X1] : (k1_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)) )),
% 15.62/2.49    inference(cnf_transformation,[],[f29])).
% 15.62/2.49  
% 15.62/2.49  fof(f6,axiom,(
% 15.62/2.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 15.62/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.62/2.49  
% 15.62/2.49  fof(f13,plain,(
% 15.62/2.49    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 15.62/2.49    inference(ennf_transformation,[],[f6])).
% 15.62/2.49  
% 15.62/2.49  fof(f14,plain,(
% 15.62/2.49    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 15.62/2.49    inference(flattening,[],[f13])).
% 15.62/2.49  
% 15.62/2.49  fof(f58,plain,(
% 15.62/2.49    ( ! [X2,X0,X1] : (r2_hidden(X0,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 15.62/2.49    inference(cnf_transformation,[],[f14])).
% 15.62/2.49  
% 15.62/2.49  fof(f55,plain,(
% 15.62/2.49    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)) )),
% 15.62/2.49    inference(cnf_transformation,[],[f35])).
% 15.62/2.49  
% 15.62/2.49  fof(f59,plain,(
% 15.62/2.49    ( ! [X2,X0,X1] : (r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 15.62/2.49    inference(cnf_transformation,[],[f14])).
% 15.62/2.49  
% 15.62/2.49  fof(f5,axiom,(
% 15.62/2.49    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 15.62/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.62/2.49  
% 15.62/2.49  fof(f12,plain,(
% 15.62/2.49    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 15.62/2.49    inference(ennf_transformation,[],[f5])).
% 15.62/2.49  
% 15.62/2.49  fof(f57,plain,(
% 15.62/2.49    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 15.62/2.49    inference(cnf_transformation,[],[f12])).
% 15.62/2.49  
% 15.62/2.49  fof(f48,plain,(
% 15.62/2.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 15.62/2.49    inference(cnf_transformation,[],[f23])).
% 15.62/2.49  
% 15.62/2.49  fof(f9,conjecture,(
% 15.62/2.49    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 15.62/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.62/2.49  
% 15.62/2.49  fof(f10,negated_conjecture,(
% 15.62/2.49    ~! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 15.62/2.49    inference(negated_conjecture,[],[f9])).
% 15.62/2.49  
% 15.62/2.49  fof(f17,plain,(
% 15.62/2.49    ? [X0] : ~r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 15.62/2.49    inference(ennf_transformation,[],[f10])).
% 15.62/2.49  
% 15.62/2.49  fof(f41,plain,(
% 15.62/2.49    ? [X0] : ~r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) => ~r1_tarski(k1_wellord2(sK9),k2_zfmisc_1(sK9,sK9))),
% 15.62/2.49    introduced(choice_axiom,[])).
% 15.62/2.49  
% 15.62/2.49  fof(f42,plain,(
% 15.62/2.49    ~r1_tarski(k1_wellord2(sK9),k2_zfmisc_1(sK9,sK9))),
% 15.62/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f17,f41])).
% 15.62/2.49  
% 15.62/2.49  fof(f68,plain,(
% 15.62/2.49    ~r1_tarski(k1_wellord2(sK9),k2_zfmisc_1(sK9,sK9))),
% 15.62/2.49    inference(cnf_transformation,[],[f42])).
% 15.62/2.49  
% 15.62/2.49  cnf(c_24,plain,
% 15.62/2.49      ( v1_relat_1(k1_wellord2(X0)) ),
% 15.62/2.49      inference(cnf_transformation,[],[f67]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_21,plain,
% 15.62/2.49      ( ~ r2_hidden(X0,X1)
% 15.62/2.49      | ~ r2_hidden(X2,X1)
% 15.62/2.49      | r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1))
% 15.62/2.49      | ~ r1_tarski(X2,X0)
% 15.62/2.49      | ~ v1_relat_1(k1_wellord2(X1)) ),
% 15.62/2.49      inference(cnf_transformation,[],[f79]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_976,plain,
% 15.62/2.49      ( ~ r2_hidden(X0,X1)
% 15.62/2.49      | ~ r2_hidden(X2,X1)
% 15.62/2.49      | r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1))
% 15.62/2.49      | ~ r1_tarski(X2,X0) ),
% 15.62/2.49      inference(backward_subsumption_resolution,
% 15.62/2.49                [status(thm)],
% 15.62/2.49                [c_24,c_21]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_12,plain,
% 15.62/2.49      ( r2_hidden(X0,k2_relat_1(X1)) | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
% 15.62/2.49      inference(cnf_transformation,[],[f73]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_18166,plain,
% 15.62/2.49      ( ~ r2_hidden(X0,X1)
% 15.62/2.49      | ~ r2_hidden(X2,X1)
% 15.62/2.49      | r2_hidden(X0,k2_relat_1(k1_wellord2(X1)))
% 15.62/2.49      | ~ r1_tarski(X2,X0) ),
% 15.62/2.49      inference(resolution,[status(thm)],[c_976,c_12]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_5,plain,
% 15.62/2.49      ( r1_tarski(X0,X0) ),
% 15.62/2.49      inference(cnf_transformation,[],[f70]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_68225,plain,
% 15.62/2.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_relat_1(k1_wellord2(X1))) ),
% 15.62/2.49      inference(resolution,[status(thm)],[c_18166,c_5]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_10,plain,
% 15.62/2.49      ( ~ r2_hidden(sK4(X0,X1),X1)
% 15.62/2.49      | ~ r2_hidden(k4_tarski(X2,sK4(X0,X1)),X0)
% 15.62/2.49      | k2_relat_1(X0) = X1 ),
% 15.62/2.49      inference(cnf_transformation,[],[f56]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_13,plain,
% 15.62/2.49      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 15.62/2.49      | r2_hidden(k4_tarski(sK6(X1,X0),X0),X1) ),
% 15.62/2.49      inference(cnf_transformation,[],[f74]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_6729,plain,
% 15.62/2.49      ( ~ r2_hidden(sK4(X0,X1),X1)
% 15.62/2.49      | ~ r2_hidden(sK4(X0,X1),k2_relat_1(X0))
% 15.62/2.49      | k2_relat_1(X0) = X1 ),
% 15.62/2.49      inference(resolution,[status(thm)],[c_10,c_13]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_69246,plain,
% 15.62/2.49      ( ~ r2_hidden(sK4(k1_wellord2(X0),X1),X0)
% 15.62/2.49      | ~ r2_hidden(sK4(k1_wellord2(X0),X1),X1)
% 15.62/2.49      | k2_relat_1(k1_wellord2(X0)) = X1 ),
% 15.62/2.49      inference(resolution,[status(thm)],[c_68225,c_6729]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_69248,plain,
% 15.62/2.49      ( ~ r2_hidden(sK4(k1_wellord2(sK9),sK9),sK9)
% 15.62/2.49      | k2_relat_1(k1_wellord2(sK9)) = sK9 ),
% 15.62/2.49      inference(instantiation,[status(thm)],[c_69246]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_8,plain,
% 15.62/2.49      ( r2_hidden(X0,k1_relat_1(X1)) | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
% 15.62/2.49      inference(cnf_transformation,[],[f71]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_18152,plain,
% 15.62/2.49      ( ~ r2_hidden(X0,X1)
% 15.62/2.49      | ~ r2_hidden(X2,X1)
% 15.62/2.49      | r2_hidden(X2,k1_relat_1(k1_wellord2(X1)))
% 15.62/2.49      | ~ r1_tarski(X2,X0) ),
% 15.62/2.49      inference(resolution,[status(thm)],[c_976,c_8]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_67613,plain,
% 15.62/2.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k1_relat_1(k1_wellord2(X1))) ),
% 15.62/2.49      inference(resolution,[status(thm)],[c_18152,c_5]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_6,plain,
% 15.62/2.49      ( ~ r2_hidden(k4_tarski(sK1(X0,X1),X2),X0)
% 15.62/2.49      | ~ r2_hidden(sK1(X0,X1),X1)
% 15.62/2.49      | k1_relat_1(X0) = X1 ),
% 15.62/2.49      inference(cnf_transformation,[],[f52]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_9,plain,
% 15.62/2.49      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 15.62/2.49      | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) ),
% 15.62/2.49      inference(cnf_transformation,[],[f72]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_6622,plain,
% 15.62/2.49      ( ~ r2_hidden(sK1(X0,X1),X1)
% 15.62/2.49      | ~ r2_hidden(sK1(X0,X1),k1_relat_1(X0))
% 15.62/2.49      | k1_relat_1(X0) = X1 ),
% 15.62/2.49      inference(resolution,[status(thm)],[c_6,c_9]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_69107,plain,
% 15.62/2.49      ( ~ r2_hidden(sK1(k1_wellord2(X0),X1),X0)
% 15.62/2.49      | ~ r2_hidden(sK1(k1_wellord2(X0),X1),X1)
% 15.62/2.49      | k1_relat_1(k1_wellord2(X0)) = X1 ),
% 15.62/2.49      inference(resolution,[status(thm)],[c_67613,c_6622]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_69109,plain,
% 15.62/2.49      ( ~ r2_hidden(sK1(k1_wellord2(sK9),sK9),sK9)
% 15.62/2.49      | k1_relat_1(k1_wellord2(sK9)) = sK9 ),
% 15.62/2.49      inference(instantiation,[status(thm)],[c_69107]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_23,plain,
% 15.62/2.49      ( ~ v1_relat_1(k1_wellord2(X0))
% 15.62/2.49      | k3_relat_1(k1_wellord2(X0)) = X0 ),
% 15.62/2.49      inference(cnf_transformation,[],[f81]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_194,plain,
% 15.62/2.49      ( k3_relat_1(k1_wellord2(X0)) = X0 ),
% 15.62/2.49      inference(global_propositional_subsumption,
% 15.62/2.49                [status(thm)],
% 15.62/2.49                [c_23,c_24]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_7,plain,
% 15.62/2.49      ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
% 15.62/2.49      | r2_hidden(sK1(X0,X1),X1)
% 15.62/2.49      | k1_relat_1(X0) = X1 ),
% 15.62/2.49      inference(cnf_transformation,[],[f51]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_758,plain,
% 15.62/2.49      ( k1_relat_1(X0) = X1
% 15.62/2.49      | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) = iProver_top
% 15.62/2.49      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 15.62/2.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_16,plain,
% 15.62/2.49      ( r2_hidden(X0,k3_relat_1(X1))
% 15.62/2.49      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 15.62/2.49      | ~ v1_relat_1(X1) ),
% 15.62/2.49      inference(cnf_transformation,[],[f58]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_749,plain,
% 15.62/2.49      ( r2_hidden(X0,k3_relat_1(X1)) = iProver_top
% 15.62/2.49      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top
% 15.62/2.49      | v1_relat_1(X1) != iProver_top ),
% 15.62/2.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_2944,plain,
% 15.62/2.49      ( k1_relat_1(X0) = X1
% 15.62/2.49      | r2_hidden(sK1(X0,X1),X1) = iProver_top
% 15.62/2.49      | r2_hidden(sK1(X0,X1),k3_relat_1(X0)) = iProver_top
% 15.62/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.62/2.49      inference(superposition,[status(thm)],[c_758,c_749]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_30121,plain,
% 15.62/2.49      ( k1_relat_1(k1_wellord2(X0)) = X1
% 15.62/2.49      | r2_hidden(sK1(k1_wellord2(X0),X1),X1) = iProver_top
% 15.62/2.49      | r2_hidden(sK1(k1_wellord2(X0),X1),X0) = iProver_top
% 15.62/2.49      | v1_relat_1(k1_wellord2(X0)) != iProver_top ),
% 15.62/2.49      inference(superposition,[status(thm)],[c_194,c_2944]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_30250,plain,
% 15.62/2.49      ( r2_hidden(sK1(k1_wellord2(X0),X1),X1)
% 15.62/2.49      | r2_hidden(sK1(k1_wellord2(X0),X1),X0)
% 15.62/2.49      | ~ v1_relat_1(k1_wellord2(X0))
% 15.62/2.49      | k1_relat_1(k1_wellord2(X0)) = X1 ),
% 15.62/2.49      inference(predicate_to_equality_rev,[status(thm)],[c_30121]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_30252,plain,
% 15.62/2.49      ( r2_hidden(sK1(k1_wellord2(sK9),sK9),sK9)
% 15.62/2.49      | ~ v1_relat_1(k1_wellord2(sK9))
% 15.62/2.49      | k1_relat_1(k1_wellord2(sK9)) = sK9 ),
% 15.62/2.49      inference(instantiation,[status(thm)],[c_30250]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_11,plain,
% 15.62/2.49      ( r2_hidden(sK4(X0,X1),X1)
% 15.62/2.49      | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
% 15.62/2.49      | k2_relat_1(X0) = X1 ),
% 15.62/2.49      inference(cnf_transformation,[],[f55]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_754,plain,
% 15.62/2.49      ( k2_relat_1(X0) = X1
% 15.62/2.49      | r2_hidden(sK4(X0,X1),X1) = iProver_top
% 15.62/2.49      | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) = iProver_top ),
% 15.62/2.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_15,plain,
% 15.62/2.49      ( r2_hidden(X0,k3_relat_1(X1))
% 15.62/2.49      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 15.62/2.49      | ~ v1_relat_1(X1) ),
% 15.62/2.49      inference(cnf_transformation,[],[f59]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_750,plain,
% 15.62/2.49      ( r2_hidden(X0,k3_relat_1(X1)) = iProver_top
% 15.62/2.49      | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
% 15.62/2.49      | v1_relat_1(X1) != iProver_top ),
% 15.62/2.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_2714,plain,
% 15.62/2.49      ( k2_relat_1(X0) = X1
% 15.62/2.49      | r2_hidden(sK4(X0,X1),X1) = iProver_top
% 15.62/2.49      | r2_hidden(sK4(X0,X1),k3_relat_1(X0)) = iProver_top
% 15.62/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.62/2.49      inference(superposition,[status(thm)],[c_754,c_750]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_29957,plain,
% 15.62/2.49      ( k2_relat_1(k1_wellord2(X0)) = X1
% 15.62/2.49      | r2_hidden(sK4(k1_wellord2(X0),X1),X1) = iProver_top
% 15.62/2.49      | r2_hidden(sK4(k1_wellord2(X0),X1),X0) = iProver_top
% 15.62/2.49      | v1_relat_1(k1_wellord2(X0)) != iProver_top ),
% 15.62/2.49      inference(superposition,[status(thm)],[c_194,c_2714]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_30086,plain,
% 15.62/2.49      ( r2_hidden(sK4(k1_wellord2(X0),X1),X1)
% 15.62/2.49      | r2_hidden(sK4(k1_wellord2(X0),X1),X0)
% 15.62/2.49      | ~ v1_relat_1(k1_wellord2(X0))
% 15.62/2.49      | k2_relat_1(k1_wellord2(X0)) = X1 ),
% 15.62/2.49      inference(predicate_to_equality_rev,[status(thm)],[c_29957]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_30088,plain,
% 15.62/2.49      ( r2_hidden(sK4(k1_wellord2(sK9),sK9),sK9)
% 15.62/2.49      | ~ v1_relat_1(k1_wellord2(sK9))
% 15.62/2.49      | k2_relat_1(k1_wellord2(sK9)) = sK9 ),
% 15.62/2.49      inference(instantiation,[status(thm)],[c_30086]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_358,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_1328,plain,
% 15.62/2.49      ( X0 != X1
% 15.62/2.49      | k2_zfmisc_1(sK9,sK9) != X1
% 15.62/2.49      | k2_zfmisc_1(sK9,sK9) = X0 ),
% 15.62/2.49      inference(instantiation,[status(thm)],[c_358]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_2338,plain,
% 15.62/2.49      ( X0 != k2_zfmisc_1(sK9,sK9)
% 15.62/2.49      | k2_zfmisc_1(sK9,sK9) = X0
% 15.62/2.49      | k2_zfmisc_1(sK9,sK9) != k2_zfmisc_1(sK9,sK9) ),
% 15.62/2.49      inference(instantiation,[status(thm)],[c_1328]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_5699,plain,
% 15.62/2.49      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK9,sK9)
% 15.62/2.49      | k2_zfmisc_1(sK9,sK9) = k2_zfmisc_1(X0,X1)
% 15.62/2.49      | k2_zfmisc_1(sK9,sK9) != k2_zfmisc_1(sK9,sK9) ),
% 15.62/2.49      inference(instantiation,[status(thm)],[c_2338]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_18414,plain,
% 15.62/2.49      ( k2_zfmisc_1(k1_relat_1(k1_wellord2(sK9)),k2_relat_1(k1_wellord2(sK9))) != k2_zfmisc_1(sK9,sK9)
% 15.62/2.49      | k2_zfmisc_1(sK9,sK9) = k2_zfmisc_1(k1_relat_1(k1_wellord2(sK9)),k2_relat_1(k1_wellord2(sK9)))
% 15.62/2.49      | k2_zfmisc_1(sK9,sK9) != k2_zfmisc_1(sK9,sK9) ),
% 15.62/2.49      inference(instantiation,[status(thm)],[c_5699]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_362,plain,
% 15.62/2.49      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 15.62/2.49      theory(equality) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_12882,plain,
% 15.62/2.49      ( k2_zfmisc_1(k1_relat_1(k1_wellord2(sK9)),k2_relat_1(k1_wellord2(sK9))) = k2_zfmisc_1(X0,X1)
% 15.62/2.49      | k2_relat_1(k1_wellord2(sK9)) != X1
% 15.62/2.49      | k1_relat_1(k1_wellord2(sK9)) != X0 ),
% 15.62/2.49      inference(instantiation,[status(thm)],[c_362]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_12884,plain,
% 15.62/2.49      ( k2_zfmisc_1(k1_relat_1(k1_wellord2(sK9)),k2_relat_1(k1_wellord2(sK9))) = k2_zfmisc_1(sK9,sK9)
% 15.62/2.49      | k2_relat_1(k1_wellord2(sK9)) != sK9
% 15.62/2.49      | k1_relat_1(k1_wellord2(sK9)) != sK9 ),
% 15.62/2.49      inference(instantiation,[status(thm)],[c_12882]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_359,plain,
% 15.62/2.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.62/2.49      theory(equality) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_998,plain,
% 15.62/2.49      ( ~ r1_tarski(X0,X1)
% 15.62/2.49      | r1_tarski(k1_wellord2(sK9),k2_zfmisc_1(sK9,sK9))
% 15.62/2.49      | k2_zfmisc_1(sK9,sK9) != X1
% 15.62/2.49      | k1_wellord2(sK9) != X0 ),
% 15.62/2.49      inference(instantiation,[status(thm)],[c_359]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_1098,plain,
% 15.62/2.49      ( ~ r1_tarski(k1_wellord2(X0),X1)
% 15.62/2.49      | r1_tarski(k1_wellord2(sK9),k2_zfmisc_1(sK9,sK9))
% 15.62/2.49      | k2_zfmisc_1(sK9,sK9) != X1
% 15.62/2.49      | k1_wellord2(sK9) != k1_wellord2(X0) ),
% 15.62/2.49      inference(instantiation,[status(thm)],[c_998]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_1329,plain,
% 15.62/2.49      ( ~ r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X1,X2))
% 15.62/2.49      | r1_tarski(k1_wellord2(sK9),k2_zfmisc_1(sK9,sK9))
% 15.62/2.49      | k2_zfmisc_1(sK9,sK9) != k2_zfmisc_1(X1,X2)
% 15.62/2.49      | k1_wellord2(sK9) != k1_wellord2(X0) ),
% 15.62/2.49      inference(instantiation,[status(thm)],[c_1098]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_2648,plain,
% 15.62/2.49      ( ~ r1_tarski(k1_wellord2(X0),k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0))))
% 15.62/2.49      | r1_tarski(k1_wellord2(sK9),k2_zfmisc_1(sK9,sK9))
% 15.62/2.49      | k2_zfmisc_1(sK9,sK9) != k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0)))
% 15.62/2.49      | k1_wellord2(sK9) != k1_wellord2(X0) ),
% 15.62/2.49      inference(instantiation,[status(thm)],[c_1329]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_2650,plain,
% 15.62/2.49      ( ~ r1_tarski(k1_wellord2(sK9),k2_zfmisc_1(k1_relat_1(k1_wellord2(sK9)),k2_relat_1(k1_wellord2(sK9))))
% 15.62/2.49      | r1_tarski(k1_wellord2(sK9),k2_zfmisc_1(sK9,sK9))
% 15.62/2.49      | k2_zfmisc_1(sK9,sK9) != k2_zfmisc_1(k1_relat_1(k1_wellord2(sK9)),k2_relat_1(k1_wellord2(sK9)))
% 15.62/2.49      | k1_wellord2(sK9) != k1_wellord2(sK9) ),
% 15.62/2.49      inference(instantiation,[status(thm)],[c_2648]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_14,plain,
% 15.62/2.49      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
% 15.62/2.49      | ~ v1_relat_1(X0) ),
% 15.62/2.49      inference(cnf_transformation,[],[f57]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_961,plain,
% 15.62/2.49      ( r1_tarski(k1_wellord2(X0),k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0))))
% 15.62/2.49      | ~ v1_relat_1(k1_wellord2(X0)) ),
% 15.62/2.49      inference(instantiation,[status(thm)],[c_14]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_963,plain,
% 15.62/2.49      ( r1_tarski(k1_wellord2(sK9),k2_zfmisc_1(k1_relat_1(k1_wellord2(sK9)),k2_relat_1(k1_wellord2(sK9))))
% 15.62/2.49      | ~ v1_relat_1(k1_wellord2(sK9)) ),
% 15.62/2.49      inference(instantiation,[status(thm)],[c_961]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_365,plain,
% 15.62/2.49      ( X0 != X1 | k1_wellord2(X0) = k1_wellord2(X1) ),
% 15.62/2.49      theory(equality) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_374,plain,
% 15.62/2.49      ( k1_wellord2(sK9) = k1_wellord2(sK9) | sK9 != sK9 ),
% 15.62/2.49      inference(instantiation,[status(thm)],[c_365]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_371,plain,
% 15.62/2.49      ( k2_zfmisc_1(sK9,sK9) = k2_zfmisc_1(sK9,sK9) | sK9 != sK9 ),
% 15.62/2.49      inference(instantiation,[status(thm)],[c_362]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_3,plain,
% 15.62/2.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 15.62/2.49      inference(cnf_transformation,[],[f48]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_87,plain,
% 15.62/2.49      ( ~ r1_tarski(sK9,sK9) | sK9 = sK9 ),
% 15.62/2.49      inference(instantiation,[status(thm)],[c_3]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_83,plain,
% 15.62/2.49      ( r1_tarski(sK9,sK9) ),
% 15.62/2.49      inference(instantiation,[status(thm)],[c_5]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_28,plain,
% 15.62/2.49      ( v1_relat_1(k1_wellord2(sK9)) ),
% 15.62/2.49      inference(instantiation,[status(thm)],[c_24]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(c_25,negated_conjecture,
% 15.62/2.49      ( ~ r1_tarski(k1_wellord2(sK9),k2_zfmisc_1(sK9,sK9)) ),
% 15.62/2.49      inference(cnf_transformation,[],[f68]) ).
% 15.62/2.49  
% 15.62/2.49  cnf(contradiction,plain,
% 15.62/2.49      ( $false ),
% 15.62/2.49      inference(minisat,
% 15.62/2.49                [status(thm)],
% 15.62/2.49                [c_69248,c_69109,c_30252,c_30088,c_18414,c_12884,c_2650,
% 15.62/2.49                 c_963,c_374,c_371,c_87,c_83,c_28,c_25]) ).
% 15.62/2.49  
% 15.62/2.49  
% 15.62/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.62/2.49  
% 15.62/2.49  ------                               Statistics
% 15.62/2.49  
% 15.62/2.49  ------ Selected
% 15.62/2.49  
% 15.62/2.49  total_time:                             1.909
% 15.62/2.49  
%------------------------------------------------------------------------------
