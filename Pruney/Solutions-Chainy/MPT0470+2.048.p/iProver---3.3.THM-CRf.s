%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:44:03 EST 2020

% Result     : Theorem 10.42s
% Output     : CNFRefutation 10.42s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 766 expanded)
%              Number of clauses        :  109 ( 329 expanded)
%              Number of leaves         :   24 ( 153 expanded)
%              Depth                    :   26
%              Number of atoms          :  465 (1975 expanded)
%              Number of equality atoms :  220 ( 684 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f51,plain,(
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
    inference(rectify,[],[f50])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r2_hidden(k4_tarski(X3,X2),X0)
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
          | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) )
        & ( r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
          | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ( ( ~ r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
                  | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) )
                & ( r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
                  | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f51,f52])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k4_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
      | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).

fof(f58,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f69,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f74,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f18,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f39,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f56,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK8,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK8) )
      & v1_relat_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK8,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK8) )
    & v1_relat_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f39,f56])).

fof(f83,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f57])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f77,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f17,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f59,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f46])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f44])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f6,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f48])).

fof(f67,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f61,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f84,plain,
    ( k1_xboole_0 != k5_relat_1(sK8,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK8) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1053,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_13,plain,
    ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
    | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k4_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1043,plain,
    ( k4_relat_1(X0) = X1
    | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) = iProver_top
    | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1054,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3087,plain,
    ( k4_relat_1(X0) = X1
    | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1043,c_1054])).

cnf(c_11,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_61,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_37179,plain,
    ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) = iProver_top
    | k4_relat_1(X0) = X1
    | v1_relat_1(X1) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3087,c_61])).

cnf(c_37180,plain,
    ( k4_relat_1(X0) = X1
    | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_37179])).

cnf(c_37187,plain,
    ( k4_relat_1(X0) = X1
    | v1_relat_1(X1) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_37180,c_1054])).

cnf(c_1045,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_37335,plain,
    ( k4_relat_1(X0) = X1
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_37187,c_1045])).

cnf(c_37339,plain,
    ( k4_relat_1(k1_xboole_0) = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1053,c_37335])).

cnf(c_38545,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1053,c_37339])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1040,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1039,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_26,negated_conjecture,
    ( v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1034,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1274,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1053,c_1045])).

cnf(c_21,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1036,plain,
    ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3218,plain,
    ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k1_xboole_0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1274,c_1036])).

cnf(c_6947,plain,
    ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(X0))) = k4_relat_1(k5_relat_1(k4_relat_1(X0),k1_xboole_0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1040,c_3218])).

cnf(c_11353,plain,
    ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK8))) = k4_relat_1(k5_relat_1(k4_relat_1(sK8),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1034,c_6947])).

cnf(c_19,plain,
    ( ~ v1_relat_1(X0)
    | k4_relat_1(k4_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1037,plain,
    ( k4_relat_1(k4_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1347,plain,
    ( k4_relat_1(k4_relat_1(sK8)) = sK8 ),
    inference(superposition,[status(thm)],[c_1034,c_1037])).

cnf(c_11383,plain,
    ( k4_relat_1(k5_relat_1(k4_relat_1(sK8),k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),sK8) ),
    inference(light_normalisation,[status(thm)],[c_11353,c_1347])).

cnf(c_12194,plain,
    ( v1_relat_1(k5_relat_1(k4_relat_1(sK8),k1_xboole_0)) != iProver_top
    | v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11383,c_1040])).

cnf(c_14683,plain,
    ( v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK8)) = iProver_top
    | v1_relat_1(k4_relat_1(sK8)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1039,c_12194])).

cnf(c_63,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_61])).

cnf(c_86,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_18919,plain,
    ( v1_relat_1(k4_relat_1(sK8)) != iProver_top
    | v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14683,c_63,c_86])).

cnf(c_18920,plain,
    ( v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK8)) = iProver_top
    | v1_relat_1(k4_relat_1(sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_18919])).

cnf(c_18978,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK8))) = k5_relat_1(k4_relat_1(k1_xboole_0),sK8)
    | v1_relat_1(k4_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18920,c_1037])).

cnf(c_20614,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK8))) = k5_relat_1(k4_relat_1(k1_xboole_0),sK8)
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1040,c_18978])).

cnf(c_27,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_20698,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK8))) = k5_relat_1(k4_relat_1(k1_xboole_0),sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20614,c_27])).

cnf(c_38616,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK8))) = k5_relat_1(k1_xboole_0,sK8) ),
    inference(demodulation,[status(thm)],[c_38545,c_20698])).

cnf(c_2101,plain,
    ( k5_relat_1(k4_relat_1(sK8),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,sK8))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1034,c_1036])).

cnf(c_3217,plain,
    ( k5_relat_1(k4_relat_1(sK8),k4_relat_1(k1_xboole_0)) = k4_relat_1(k5_relat_1(k1_xboole_0,sK8)) ),
    inference(superposition,[status(thm)],[c_1274,c_2101])).

cnf(c_38626,plain,
    ( k5_relat_1(k4_relat_1(sK8),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,sK8)) ),
    inference(demodulation,[status(thm)],[c_38545,c_3217])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_20,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_283,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k3_xboole_0(X2,X3) = X2
    | k2_relat_1(X1) != X3
    | k2_relat_1(k5_relat_1(X0,X1)) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_284,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k3_xboole_0(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_283])).

cnf(c_1033,plain,
    ( k3_xboole_0(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_284])).

cnf(c_1410,plain,
    ( k3_xboole_0(k2_relat_1(k5_relat_1(k4_relat_1(X0),X1)),k2_relat_1(X1)) = k2_relat_1(k5_relat_1(k4_relat_1(X0),X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1040,c_1033])).

cnf(c_6204,plain,
    ( k3_xboole_0(k2_relat_1(k5_relat_1(k4_relat_1(sK8),X0)),k2_relat_1(X0)) = k2_relat_1(k5_relat_1(k4_relat_1(sK8),X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1034,c_1410])).

cnf(c_7082,plain,
    ( k3_xboole_0(k2_relat_1(k5_relat_1(k4_relat_1(sK8),k1_xboole_0)),k2_relat_1(k1_xboole_0)) = k2_relat_1(k5_relat_1(k4_relat_1(sK8),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1274,c_6204])).

cnf(c_23,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_7107,plain,
    ( k3_xboole_0(k2_relat_1(k5_relat_1(k4_relat_1(sK8),k1_xboole_0)),k1_xboole_0) = k2_relat_1(k5_relat_1(k4_relat_1(sK8),k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_7082,c_23])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1055,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1048,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2183,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | v1_xboole_0(k3_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1055,c_1048])).

cnf(c_7840,plain,
    ( r1_xboole_0(k2_relat_1(k5_relat_1(k4_relat_1(sK8),k1_xboole_0)),k1_xboole_0) != iProver_top
    | v1_xboole_0(k2_relat_1(k5_relat_1(k4_relat_1(sK8),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7107,c_2183])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1050,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1280,plain,
    ( k3_xboole_0(k2_relat_1(k5_relat_1(sK8,X0)),k2_relat_1(X0)) = k2_relat_1(k5_relat_1(sK8,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1034,c_1033])).

cnf(c_3227,plain,
    ( k3_xboole_0(k2_relat_1(k5_relat_1(sK8,k1_xboole_0)),k2_relat_1(k1_xboole_0)) = k2_relat_1(k5_relat_1(sK8,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1274,c_1280])).

cnf(c_3237,plain,
    ( k3_xboole_0(k2_relat_1(k5_relat_1(sK8,k1_xboole_0)),k1_xboole_0) = k2_relat_1(k5_relat_1(sK8,k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_3227,c_23])).

cnf(c_3260,plain,
    ( r1_xboole_0(k2_relat_1(k5_relat_1(sK8,k1_xboole_0)),k1_xboole_0) != iProver_top
    | r2_hidden(X0,k2_relat_1(k5_relat_1(sK8,k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3237,c_1048])).

cnf(c_1841,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1050,c_1054])).

cnf(c_6,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1049,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2185,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(k3_xboole_0(X0,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1049,c_1048])).

cnf(c_6378,plain,
    ( r1_xboole_0(k2_relat_1(k5_relat_1(sK8,k1_xboole_0)),X0) = iProver_top
    | r1_xboole_0(k2_relat_1(k5_relat_1(sK8,k1_xboole_0)),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3237,c_2185])).

cnf(c_11337,plain,
    ( r1_xboole_0(k2_relat_1(k5_relat_1(sK8,k1_xboole_0)),X0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1841,c_6378])).

cnf(c_11346,plain,
    ( r1_xboole_0(k2_relat_1(k5_relat_1(sK8,k1_xboole_0)),k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11337])).

cnf(c_11684,plain,
    ( r2_hidden(X0,k2_relat_1(k5_relat_1(sK8,k1_xboole_0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3260,c_86,c_11346])).

cnf(c_11692,plain,
    ( r1_xboole_0(X0,k2_relat_1(k5_relat_1(sK8,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1050,c_11684])).

cnf(c_9,plain,
    ( r2_hidden(sK3(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1046,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK3(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_11694,plain,
    ( k2_relat_1(k5_relat_1(sK8,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1046,c_11684])).

cnf(c_12981,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11692,c_11694])).

cnf(c_14978,plain,
    ( v1_xboole_0(k2_relat_1(k5_relat_1(k4_relat_1(sK8),k1_xboole_0))) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7840,c_12981])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1038,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k2_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_14982,plain,
    ( v1_relat_1(k5_relat_1(k4_relat_1(sK8),k1_xboole_0)) != iProver_top
    | v1_xboole_0(k5_relat_1(k4_relat_1(sK8),k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_14978,c_1038])).

cnf(c_15798,plain,
    ( v1_relat_1(k4_relat_1(sK8)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top
    | v1_xboole_0(k5_relat_1(k4_relat_1(sK8),k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1039,c_14982])).

cnf(c_22138,plain,
    ( v1_relat_1(k4_relat_1(sK8)) != iProver_top
    | v1_xboole_0(k5_relat_1(k4_relat_1(sK8),k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15798,c_63,c_86])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1052,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_22145,plain,
    ( k5_relat_1(k4_relat_1(sK8),k1_xboole_0) = k1_xboole_0
    | v1_relat_1(k4_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_22138,c_1052])).

cnf(c_23570,plain,
    ( k5_relat_1(k4_relat_1(sK8),k1_xboole_0) = k1_xboole_0
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1040,c_22145])).

cnf(c_23601,plain,
    ( k5_relat_1(k4_relat_1(sK8),k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_23570,c_27])).

cnf(c_38629,plain,
    ( k4_relat_1(k5_relat_1(k1_xboole_0,sK8)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_38626,c_23601])).

cnf(c_38660,plain,
    ( k5_relat_1(k1_xboole_0,sK8) = k4_relat_1(k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_38616,c_38629])).

cnf(c_38662,plain,
    ( k5_relat_1(k1_xboole_0,sK8) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_38660,c_38545])).

cnf(c_5181,plain,
    ( r1_xboole_0(k2_relat_1(k5_relat_1(sK8,k1_xboole_0)),k1_xboole_0) != iProver_top
    | v1_xboole_0(k2_relat_1(k5_relat_1(sK8,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3237,c_2183])).

cnf(c_8065,plain,
    ( v1_xboole_0(k2_relat_1(k5_relat_1(sK8,k1_xboole_0))) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1841,c_5181])).

cnf(c_1356,plain,
    ( v1_relat_1(k5_relat_1(sK8,k1_xboole_0))
    | ~ v1_relat_1(sK8)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1357,plain,
    ( v1_relat_1(k5_relat_1(sK8,k1_xboole_0)) = iProver_top
    | v1_relat_1(sK8) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1356])).

cnf(c_1318,plain,
    ( ~ v1_relat_1(k5_relat_1(sK8,k1_xboole_0))
    | v1_xboole_0(k5_relat_1(sK8,k1_xboole_0))
    | ~ v1_xboole_0(k2_relat_1(k5_relat_1(sK8,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1319,plain,
    ( v1_relat_1(k5_relat_1(sK8,k1_xboole_0)) != iProver_top
    | v1_xboole_0(k5_relat_1(sK8,k1_xboole_0)) = iProver_top
    | v1_xboole_0(k2_relat_1(k5_relat_1(sK8,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1318])).

cnf(c_629,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1269,plain,
    ( k5_relat_1(k1_xboole_0,sK8) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK8) ),
    inference(instantiation,[status(thm)],[c_629])).

cnf(c_1270,plain,
    ( k5_relat_1(k1_xboole_0,sK8) != k1_xboole_0
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK8)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1269])).

cnf(c_1237,plain,
    ( ~ v1_xboole_0(k5_relat_1(sK8,k1_xboole_0))
    | k1_xboole_0 = k5_relat_1(sK8,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1238,plain,
    ( k1_xboole_0 = k5_relat_1(sK8,k1_xboole_0)
    | v1_xboole_0(k5_relat_1(sK8,k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1237])).

cnf(c_84,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK8,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK8) ),
    inference(cnf_transformation,[],[f84])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_38662,c_8065,c_1357,c_1319,c_1270,c_1238,c_86,c_2,c_84,c_63,c_25,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:38:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 10.42/1.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.42/1.99  
% 10.42/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 10.42/1.99  
% 10.42/1.99  ------  iProver source info
% 10.42/1.99  
% 10.42/1.99  git: date: 2020-06-30 10:37:57 +0100
% 10.42/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 10.42/1.99  git: non_committed_changes: false
% 10.42/1.99  git: last_make_outside_of_git: false
% 10.42/1.99  
% 10.42/1.99  ------ 
% 10.42/1.99  
% 10.42/1.99  ------ Input Options
% 10.42/1.99  
% 10.42/1.99  --out_options                           all
% 10.42/1.99  --tptp_safe_out                         true
% 10.42/1.99  --problem_path                          ""
% 10.42/1.99  --include_path                          ""
% 10.42/1.99  --clausifier                            res/vclausify_rel
% 10.42/1.99  --clausifier_options                    --mode clausify
% 10.42/1.99  --stdin                                 false
% 10.42/1.99  --stats_out                             all
% 10.42/1.99  
% 10.42/1.99  ------ General Options
% 10.42/1.99  
% 10.42/1.99  --fof                                   false
% 10.42/1.99  --time_out_real                         305.
% 10.42/1.99  --time_out_virtual                      -1.
% 10.42/1.99  --symbol_type_check                     false
% 10.42/1.99  --clausify_out                          false
% 10.42/1.99  --sig_cnt_out                           false
% 10.42/1.99  --trig_cnt_out                          false
% 10.42/1.99  --trig_cnt_out_tolerance                1.
% 10.42/1.99  --trig_cnt_out_sk_spl                   false
% 10.42/1.99  --abstr_cl_out                          false
% 10.42/1.99  
% 10.42/1.99  ------ Global Options
% 10.42/1.99  
% 10.42/1.99  --schedule                              default
% 10.42/1.99  --add_important_lit                     false
% 10.42/1.99  --prop_solver_per_cl                    1000
% 10.42/1.99  --min_unsat_core                        false
% 10.42/1.99  --soft_assumptions                      false
% 10.42/1.99  --soft_lemma_size                       3
% 10.42/1.99  --prop_impl_unit_size                   0
% 10.42/1.99  --prop_impl_unit                        []
% 10.42/1.99  --share_sel_clauses                     true
% 10.42/1.99  --reset_solvers                         false
% 10.42/1.99  --bc_imp_inh                            [conj_cone]
% 10.42/1.99  --conj_cone_tolerance                   3.
% 10.42/1.99  --extra_neg_conj                        none
% 10.42/1.99  --large_theory_mode                     true
% 10.42/1.99  --prolific_symb_bound                   200
% 10.42/1.99  --lt_threshold                          2000
% 10.42/1.99  --clause_weak_htbl                      true
% 10.42/1.99  --gc_record_bc_elim                     false
% 10.42/1.99  
% 10.42/1.99  ------ Preprocessing Options
% 10.42/1.99  
% 10.42/1.99  --preprocessing_flag                    true
% 10.42/1.99  --time_out_prep_mult                    0.1
% 10.42/1.99  --splitting_mode                        input
% 10.42/1.99  --splitting_grd                         true
% 10.42/1.99  --splitting_cvd                         false
% 10.42/1.99  --splitting_cvd_svl                     false
% 10.42/1.99  --splitting_nvd                         32
% 10.42/1.99  --sub_typing                            true
% 10.42/1.99  --prep_gs_sim                           true
% 10.42/1.99  --prep_unflatten                        true
% 10.42/1.99  --prep_res_sim                          true
% 10.42/1.99  --prep_upred                            true
% 10.42/1.99  --prep_sem_filter                       exhaustive
% 10.42/1.99  --prep_sem_filter_out                   false
% 10.42/1.99  --pred_elim                             true
% 10.42/1.99  --res_sim_input                         true
% 10.42/1.99  --eq_ax_congr_red                       true
% 10.42/1.99  --pure_diseq_elim                       true
% 10.42/1.99  --brand_transform                       false
% 10.42/1.99  --non_eq_to_eq                          false
% 10.42/1.99  --prep_def_merge                        true
% 10.42/1.99  --prep_def_merge_prop_impl              false
% 10.42/1.99  --prep_def_merge_mbd                    true
% 10.42/1.99  --prep_def_merge_tr_red                 false
% 10.42/1.99  --prep_def_merge_tr_cl                  false
% 10.42/1.99  --smt_preprocessing                     true
% 10.42/1.99  --smt_ac_axioms                         fast
% 10.42/1.99  --preprocessed_out                      false
% 10.42/1.99  --preprocessed_stats                    false
% 10.42/1.99  
% 10.42/1.99  ------ Abstraction refinement Options
% 10.42/1.99  
% 10.42/1.99  --abstr_ref                             []
% 10.42/1.99  --abstr_ref_prep                        false
% 10.42/1.99  --abstr_ref_until_sat                   false
% 10.42/1.99  --abstr_ref_sig_restrict                funpre
% 10.42/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 10.42/1.99  --abstr_ref_under                       []
% 10.42/1.99  
% 10.42/1.99  ------ SAT Options
% 10.42/1.99  
% 10.42/1.99  --sat_mode                              false
% 10.42/1.99  --sat_fm_restart_options                ""
% 10.42/1.99  --sat_gr_def                            false
% 10.42/1.99  --sat_epr_types                         true
% 10.42/1.99  --sat_non_cyclic_types                  false
% 10.42/1.99  --sat_finite_models                     false
% 10.42/1.99  --sat_fm_lemmas                         false
% 10.42/1.99  --sat_fm_prep                           false
% 10.42/1.99  --sat_fm_uc_incr                        true
% 10.42/1.99  --sat_out_model                         small
% 10.42/1.99  --sat_out_clauses                       false
% 10.42/1.99  
% 10.42/1.99  ------ QBF Options
% 10.42/1.99  
% 10.42/1.99  --qbf_mode                              false
% 10.42/1.99  --qbf_elim_univ                         false
% 10.42/1.99  --qbf_dom_inst                          none
% 10.42/1.99  --qbf_dom_pre_inst                      false
% 10.42/1.99  --qbf_sk_in                             false
% 10.42/1.99  --qbf_pred_elim                         true
% 10.42/1.99  --qbf_split                             512
% 10.42/1.99  
% 10.42/1.99  ------ BMC1 Options
% 10.42/1.99  
% 10.42/1.99  --bmc1_incremental                      false
% 10.42/1.99  --bmc1_axioms                           reachable_all
% 10.42/1.99  --bmc1_min_bound                        0
% 10.42/1.99  --bmc1_max_bound                        -1
% 10.42/1.99  --bmc1_max_bound_default                -1
% 10.42/1.99  --bmc1_symbol_reachability              true
% 10.42/1.99  --bmc1_property_lemmas                  false
% 10.42/1.99  --bmc1_k_induction                      false
% 10.42/1.99  --bmc1_non_equiv_states                 false
% 10.42/1.99  --bmc1_deadlock                         false
% 10.42/1.99  --bmc1_ucm                              false
% 10.42/1.99  --bmc1_add_unsat_core                   none
% 10.42/1.99  --bmc1_unsat_core_children              false
% 10.42/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 10.42/1.99  --bmc1_out_stat                         full
% 10.42/1.99  --bmc1_ground_init                      false
% 10.42/1.99  --bmc1_pre_inst_next_state              false
% 10.42/1.99  --bmc1_pre_inst_state                   false
% 10.42/1.99  --bmc1_pre_inst_reach_state             false
% 10.42/1.99  --bmc1_out_unsat_core                   false
% 10.42/1.99  --bmc1_aig_witness_out                  false
% 10.42/1.99  --bmc1_verbose                          false
% 10.42/1.99  --bmc1_dump_clauses_tptp                false
% 10.42/1.99  --bmc1_dump_unsat_core_tptp             false
% 10.42/1.99  --bmc1_dump_file                        -
% 10.42/1.99  --bmc1_ucm_expand_uc_limit              128
% 10.42/1.99  --bmc1_ucm_n_expand_iterations          6
% 10.42/1.99  --bmc1_ucm_extend_mode                  1
% 10.42/1.99  --bmc1_ucm_init_mode                    2
% 10.42/1.99  --bmc1_ucm_cone_mode                    none
% 10.42/1.99  --bmc1_ucm_reduced_relation_type        0
% 10.42/1.99  --bmc1_ucm_relax_model                  4
% 10.42/1.99  --bmc1_ucm_full_tr_after_sat            true
% 10.42/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 10.42/1.99  --bmc1_ucm_layered_model                none
% 10.42/1.99  --bmc1_ucm_max_lemma_size               10
% 10.42/1.99  
% 10.42/1.99  ------ AIG Options
% 10.42/1.99  
% 10.42/1.99  --aig_mode                              false
% 10.42/1.99  
% 10.42/1.99  ------ Instantiation Options
% 10.42/1.99  
% 10.42/1.99  --instantiation_flag                    true
% 10.42/1.99  --inst_sos_flag                         false
% 10.42/1.99  --inst_sos_phase                        true
% 10.42/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 10.42/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 10.42/1.99  --inst_lit_sel_side                     num_symb
% 10.42/1.99  --inst_solver_per_active                1400
% 10.42/1.99  --inst_solver_calls_frac                1.
% 10.42/1.99  --inst_passive_queue_type               priority_queues
% 10.42/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 10.42/1.99  --inst_passive_queues_freq              [25;2]
% 10.42/1.99  --inst_dismatching                      true
% 10.42/1.99  --inst_eager_unprocessed_to_passive     true
% 10.42/1.99  --inst_prop_sim_given                   true
% 10.42/1.99  --inst_prop_sim_new                     false
% 10.42/1.99  --inst_subs_new                         false
% 10.42/1.99  --inst_eq_res_simp                      false
% 10.42/1.99  --inst_subs_given                       false
% 10.42/1.99  --inst_orphan_elimination               true
% 10.42/1.99  --inst_learning_loop_flag               true
% 10.42/1.99  --inst_learning_start                   3000
% 10.42/1.99  --inst_learning_factor                  2
% 10.42/1.99  --inst_start_prop_sim_after_learn       3
% 10.42/1.99  --inst_sel_renew                        solver
% 10.42/1.99  --inst_lit_activity_flag                true
% 10.42/1.99  --inst_restr_to_given                   false
% 10.42/1.99  --inst_activity_threshold               500
% 10.42/1.99  --inst_out_proof                        true
% 10.42/1.99  
% 10.42/1.99  ------ Resolution Options
% 10.42/1.99  
% 10.42/1.99  --resolution_flag                       true
% 10.42/1.99  --res_lit_sel                           adaptive
% 10.42/1.99  --res_lit_sel_side                      none
% 10.42/1.99  --res_ordering                          kbo
% 10.42/1.99  --res_to_prop_solver                    active
% 10.42/1.99  --res_prop_simpl_new                    false
% 10.42/1.99  --res_prop_simpl_given                  true
% 10.42/1.99  --res_passive_queue_type                priority_queues
% 10.42/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 10.42/1.99  --res_passive_queues_freq               [15;5]
% 10.42/1.99  --res_forward_subs                      full
% 10.42/1.99  --res_backward_subs                     full
% 10.42/1.99  --res_forward_subs_resolution           true
% 10.42/1.99  --res_backward_subs_resolution          true
% 10.42/1.99  --res_orphan_elimination                true
% 10.42/1.99  --res_time_limit                        2.
% 10.42/1.99  --res_out_proof                         true
% 10.42/1.99  
% 10.42/1.99  ------ Superposition Options
% 10.42/1.99  
% 10.42/1.99  --superposition_flag                    true
% 10.42/1.99  --sup_passive_queue_type                priority_queues
% 10.42/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 10.42/1.99  --sup_passive_queues_freq               [8;1;4]
% 10.42/1.99  --demod_completeness_check              fast
% 10.42/1.99  --demod_use_ground                      true
% 10.42/1.99  --sup_to_prop_solver                    passive
% 10.42/1.99  --sup_prop_simpl_new                    true
% 10.42/1.99  --sup_prop_simpl_given                  true
% 10.42/1.99  --sup_fun_splitting                     false
% 10.42/1.99  --sup_smt_interval                      50000
% 10.42/1.99  
% 10.42/1.99  ------ Superposition Simplification Setup
% 10.42/1.99  
% 10.42/1.99  --sup_indices_passive                   []
% 10.42/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 10.42/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 10.42/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 10.42/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 10.42/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 10.42/1.99  --sup_full_bw                           [BwDemod]
% 10.42/1.99  --sup_immed_triv                        [TrivRules]
% 10.42/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 10.42/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 10.42/1.99  --sup_immed_bw_main                     []
% 10.42/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 10.42/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 10.42/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 10.42/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 10.42/1.99  
% 10.42/1.99  ------ Combination Options
% 10.42/1.99  
% 10.42/1.99  --comb_res_mult                         3
% 10.42/1.99  --comb_sup_mult                         2
% 10.42/1.99  --comb_inst_mult                        10
% 10.42/1.99  
% 10.42/1.99  ------ Debug Options
% 10.42/1.99  
% 10.42/1.99  --dbg_backtrace                         false
% 10.42/1.99  --dbg_dump_prop_clauses                 false
% 10.42/1.99  --dbg_dump_prop_clauses_file            -
% 10.42/1.99  --dbg_out_stat                          false
% 10.42/1.99  ------ Parsing...
% 10.42/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 10.42/1.99  
% 10.42/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 10.42/1.99  
% 10.42/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 10.42/1.99  
% 10.42/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 10.42/1.99  ------ Proving...
% 10.42/1.99  ------ Problem Properties 
% 10.42/1.99  
% 10.42/1.99  
% 10.42/1.99  clauses                                 26
% 10.42/1.99  conjectures                             2
% 10.42/1.99  EPR                                     6
% 10.42/1.99  Horn                                    19
% 10.42/1.99  unary                                   4
% 10.42/1.99  binary                                  12
% 10.42/1.99  lits                                    64
% 10.42/1.99  lits eq                                 12
% 10.42/1.99  fd_pure                                 0
% 10.42/1.99  fd_pseudo                               0
% 10.42/1.99  fd_cond                                 3
% 10.42/1.99  fd_pseudo_cond                          2
% 10.42/1.99  AC symbols                              0
% 10.42/1.99  
% 10.42/1.99  ------ Schedule dynamic 5 is on 
% 10.42/1.99  
% 10.42/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 10.42/1.99  
% 10.42/1.99  
% 10.42/1.99  ------ 
% 10.42/1.99  Current options:
% 10.42/1.99  ------ 
% 10.42/1.99  
% 10.42/1.99  ------ Input Options
% 10.42/1.99  
% 10.42/1.99  --out_options                           all
% 10.42/1.99  --tptp_safe_out                         true
% 10.42/1.99  --problem_path                          ""
% 10.42/1.99  --include_path                          ""
% 10.42/1.99  --clausifier                            res/vclausify_rel
% 10.42/1.99  --clausifier_options                    --mode clausify
% 10.42/1.99  --stdin                                 false
% 10.42/1.99  --stats_out                             all
% 10.42/1.99  
% 10.42/1.99  ------ General Options
% 10.42/1.99  
% 10.42/1.99  --fof                                   false
% 10.42/1.99  --time_out_real                         305.
% 10.42/1.99  --time_out_virtual                      -1.
% 10.42/1.99  --symbol_type_check                     false
% 10.42/1.99  --clausify_out                          false
% 10.42/1.99  --sig_cnt_out                           false
% 10.42/1.99  --trig_cnt_out                          false
% 10.42/1.99  --trig_cnt_out_tolerance                1.
% 10.42/1.99  --trig_cnt_out_sk_spl                   false
% 10.42/1.99  --abstr_cl_out                          false
% 10.42/1.99  
% 10.42/1.99  ------ Global Options
% 10.42/1.99  
% 10.42/1.99  --schedule                              default
% 10.42/1.99  --add_important_lit                     false
% 10.42/1.99  --prop_solver_per_cl                    1000
% 10.42/1.99  --min_unsat_core                        false
% 10.42/1.99  --soft_assumptions                      false
% 10.42/1.99  --soft_lemma_size                       3
% 10.42/1.99  --prop_impl_unit_size                   0
% 10.42/1.99  --prop_impl_unit                        []
% 10.42/1.99  --share_sel_clauses                     true
% 10.42/1.99  --reset_solvers                         false
% 10.42/1.99  --bc_imp_inh                            [conj_cone]
% 10.42/1.99  --conj_cone_tolerance                   3.
% 10.42/1.99  --extra_neg_conj                        none
% 10.42/1.99  --large_theory_mode                     true
% 10.42/1.99  --prolific_symb_bound                   200
% 10.42/1.99  --lt_threshold                          2000
% 10.42/1.99  --clause_weak_htbl                      true
% 10.42/1.99  --gc_record_bc_elim                     false
% 10.42/1.99  
% 10.42/1.99  ------ Preprocessing Options
% 10.42/1.99  
% 10.42/1.99  --preprocessing_flag                    true
% 10.42/1.99  --time_out_prep_mult                    0.1
% 10.42/1.99  --splitting_mode                        input
% 10.42/1.99  --splitting_grd                         true
% 10.42/1.99  --splitting_cvd                         false
% 10.42/1.99  --splitting_cvd_svl                     false
% 10.42/1.99  --splitting_nvd                         32
% 10.42/1.99  --sub_typing                            true
% 10.42/1.99  --prep_gs_sim                           true
% 10.42/1.99  --prep_unflatten                        true
% 10.42/1.99  --prep_res_sim                          true
% 10.42/1.99  --prep_upred                            true
% 10.42/1.99  --prep_sem_filter                       exhaustive
% 10.42/1.99  --prep_sem_filter_out                   false
% 10.42/1.99  --pred_elim                             true
% 10.42/1.99  --res_sim_input                         true
% 10.42/1.99  --eq_ax_congr_red                       true
% 10.42/1.99  --pure_diseq_elim                       true
% 10.42/1.99  --brand_transform                       false
% 10.42/1.99  --non_eq_to_eq                          false
% 10.42/1.99  --prep_def_merge                        true
% 10.42/1.99  --prep_def_merge_prop_impl              false
% 10.42/1.99  --prep_def_merge_mbd                    true
% 10.42/1.99  --prep_def_merge_tr_red                 false
% 10.42/1.99  --prep_def_merge_tr_cl                  false
% 10.42/1.99  --smt_preprocessing                     true
% 10.42/1.99  --smt_ac_axioms                         fast
% 10.42/1.99  --preprocessed_out                      false
% 10.42/1.99  --preprocessed_stats                    false
% 10.42/1.99  
% 10.42/1.99  ------ Abstraction refinement Options
% 10.42/1.99  
% 10.42/1.99  --abstr_ref                             []
% 10.42/1.99  --abstr_ref_prep                        false
% 10.42/1.99  --abstr_ref_until_sat                   false
% 10.42/1.99  --abstr_ref_sig_restrict                funpre
% 10.42/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 10.42/1.99  --abstr_ref_under                       []
% 10.42/1.99  
% 10.42/1.99  ------ SAT Options
% 10.42/1.99  
% 10.42/1.99  --sat_mode                              false
% 10.42/1.99  --sat_fm_restart_options                ""
% 10.42/1.99  --sat_gr_def                            false
% 10.42/1.99  --sat_epr_types                         true
% 10.42/1.99  --sat_non_cyclic_types                  false
% 10.42/1.99  --sat_finite_models                     false
% 10.42/1.99  --sat_fm_lemmas                         false
% 10.42/1.99  --sat_fm_prep                           false
% 10.42/1.99  --sat_fm_uc_incr                        true
% 10.42/1.99  --sat_out_model                         small
% 10.42/1.99  --sat_out_clauses                       false
% 10.42/1.99  
% 10.42/1.99  ------ QBF Options
% 10.42/1.99  
% 10.42/1.99  --qbf_mode                              false
% 10.42/1.99  --qbf_elim_univ                         false
% 10.42/1.99  --qbf_dom_inst                          none
% 10.42/1.99  --qbf_dom_pre_inst                      false
% 10.42/1.99  --qbf_sk_in                             false
% 10.42/1.99  --qbf_pred_elim                         true
% 10.42/1.99  --qbf_split                             512
% 10.42/1.99  
% 10.42/1.99  ------ BMC1 Options
% 10.42/1.99  
% 10.42/1.99  --bmc1_incremental                      false
% 10.42/1.99  --bmc1_axioms                           reachable_all
% 10.42/1.99  --bmc1_min_bound                        0
% 10.42/1.99  --bmc1_max_bound                        -1
% 10.42/1.99  --bmc1_max_bound_default                -1
% 10.42/1.99  --bmc1_symbol_reachability              true
% 10.42/1.99  --bmc1_property_lemmas                  false
% 10.42/1.99  --bmc1_k_induction                      false
% 10.42/1.99  --bmc1_non_equiv_states                 false
% 10.42/1.99  --bmc1_deadlock                         false
% 10.42/1.99  --bmc1_ucm                              false
% 10.42/1.99  --bmc1_add_unsat_core                   none
% 10.42/1.99  --bmc1_unsat_core_children              false
% 10.42/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 10.42/1.99  --bmc1_out_stat                         full
% 10.42/1.99  --bmc1_ground_init                      false
% 10.42/1.99  --bmc1_pre_inst_next_state              false
% 10.42/1.99  --bmc1_pre_inst_state                   false
% 10.42/1.99  --bmc1_pre_inst_reach_state             false
% 10.42/1.99  --bmc1_out_unsat_core                   false
% 10.42/1.99  --bmc1_aig_witness_out                  false
% 10.42/1.99  --bmc1_verbose                          false
% 10.42/1.99  --bmc1_dump_clauses_tptp                false
% 10.42/1.99  --bmc1_dump_unsat_core_tptp             false
% 10.42/1.99  --bmc1_dump_file                        -
% 10.42/1.99  --bmc1_ucm_expand_uc_limit              128
% 10.42/1.99  --bmc1_ucm_n_expand_iterations          6
% 10.42/1.99  --bmc1_ucm_extend_mode                  1
% 10.42/1.99  --bmc1_ucm_init_mode                    2
% 10.42/1.99  --bmc1_ucm_cone_mode                    none
% 10.42/1.99  --bmc1_ucm_reduced_relation_type        0
% 10.42/1.99  --bmc1_ucm_relax_model                  4
% 10.42/1.99  --bmc1_ucm_full_tr_after_sat            true
% 10.42/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 10.42/1.99  --bmc1_ucm_layered_model                none
% 10.42/1.99  --bmc1_ucm_max_lemma_size               10
% 10.42/1.99  
% 10.42/1.99  ------ AIG Options
% 10.42/1.99  
% 10.42/1.99  --aig_mode                              false
% 10.42/1.99  
% 10.42/1.99  ------ Instantiation Options
% 10.42/1.99  
% 10.42/1.99  --instantiation_flag                    true
% 10.42/1.99  --inst_sos_flag                         false
% 10.42/1.99  --inst_sos_phase                        true
% 10.42/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 10.42/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 10.42/1.99  --inst_lit_sel_side                     none
% 10.42/1.99  --inst_solver_per_active                1400
% 10.42/1.99  --inst_solver_calls_frac                1.
% 10.42/1.99  --inst_passive_queue_type               priority_queues
% 10.42/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 10.42/1.99  --inst_passive_queues_freq              [25;2]
% 10.42/1.99  --inst_dismatching                      true
% 10.42/1.99  --inst_eager_unprocessed_to_passive     true
% 10.42/1.99  --inst_prop_sim_given                   true
% 10.42/1.99  --inst_prop_sim_new                     false
% 10.42/1.99  --inst_subs_new                         false
% 10.42/1.99  --inst_eq_res_simp                      false
% 10.42/1.99  --inst_subs_given                       false
% 10.42/1.99  --inst_orphan_elimination               true
% 10.42/1.99  --inst_learning_loop_flag               true
% 10.42/1.99  --inst_learning_start                   3000
% 10.42/1.99  --inst_learning_factor                  2
% 10.42/1.99  --inst_start_prop_sim_after_learn       3
% 10.42/1.99  --inst_sel_renew                        solver
% 10.42/1.99  --inst_lit_activity_flag                true
% 10.42/1.99  --inst_restr_to_given                   false
% 10.42/1.99  --inst_activity_threshold               500
% 10.42/1.99  --inst_out_proof                        true
% 10.42/1.99  
% 10.42/1.99  ------ Resolution Options
% 10.42/1.99  
% 10.42/1.99  --resolution_flag                       false
% 10.42/1.99  --res_lit_sel                           adaptive
% 10.42/1.99  --res_lit_sel_side                      none
% 10.42/1.99  --res_ordering                          kbo
% 10.42/1.99  --res_to_prop_solver                    active
% 10.42/1.99  --res_prop_simpl_new                    false
% 10.42/1.99  --res_prop_simpl_given                  true
% 10.42/1.99  --res_passive_queue_type                priority_queues
% 10.42/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 10.42/1.99  --res_passive_queues_freq               [15;5]
% 10.42/1.99  --res_forward_subs                      full
% 10.42/1.99  --res_backward_subs                     full
% 10.42/1.99  --res_forward_subs_resolution           true
% 10.42/1.99  --res_backward_subs_resolution          true
% 10.42/1.99  --res_orphan_elimination                true
% 10.42/1.99  --res_time_limit                        2.
% 10.42/1.99  --res_out_proof                         true
% 10.42/1.99  
% 10.42/1.99  ------ Superposition Options
% 10.42/1.99  
% 10.42/1.99  --superposition_flag                    true
% 10.42/1.99  --sup_passive_queue_type                priority_queues
% 10.42/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 10.42/1.99  --sup_passive_queues_freq               [8;1;4]
% 10.42/1.99  --demod_completeness_check              fast
% 10.42/1.99  --demod_use_ground                      true
% 10.42/1.99  --sup_to_prop_solver                    passive
% 10.42/1.99  --sup_prop_simpl_new                    true
% 10.42/1.99  --sup_prop_simpl_given                  true
% 10.42/1.99  --sup_fun_splitting                     false
% 10.42/1.99  --sup_smt_interval                      50000
% 10.42/1.99  
% 10.42/1.99  ------ Superposition Simplification Setup
% 10.42/1.99  
% 10.42/1.99  --sup_indices_passive                   []
% 10.42/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 10.42/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 10.42/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 10.42/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 10.42/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 10.42/1.99  --sup_full_bw                           [BwDemod]
% 10.42/1.99  --sup_immed_triv                        [TrivRules]
% 10.42/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 10.42/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 10.42/1.99  --sup_immed_bw_main                     []
% 10.42/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 10.42/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 10.42/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 10.42/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 10.42/1.99  
% 10.42/1.99  ------ Combination Options
% 10.42/1.99  
% 10.42/1.99  --comb_res_mult                         3
% 10.42/1.99  --comb_sup_mult                         2
% 10.42/1.99  --comb_inst_mult                        10
% 10.42/1.99  
% 10.42/1.99  ------ Debug Options
% 10.42/1.99  
% 10.42/1.99  --dbg_backtrace                         false
% 10.42/1.99  --dbg_dump_prop_clauses                 false
% 10.42/1.99  --dbg_dump_prop_clauses_file            -
% 10.42/1.99  --dbg_out_stat                          false
% 10.42/1.99  
% 10.42/1.99  
% 10.42/1.99  
% 10.42/1.99  
% 10.42/1.99  ------ Proving...
% 10.42/1.99  
% 10.42/1.99  
% 10.42/1.99  % SZS status Theorem for theBenchmark.p
% 10.42/1.99  
% 10.42/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 10.42/1.99  
% 10.42/1.99  fof(f2,axiom,(
% 10.42/1.99    v1_xboole_0(k1_xboole_0)),
% 10.42/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.42/1.99  
% 10.42/1.99  fof(f60,plain,(
% 10.42/1.99    v1_xboole_0(k1_xboole_0)),
% 10.42/1.99    inference(cnf_transformation,[],[f2])).
% 10.42/1.99  
% 10.42/1.99  fof(f9,axiom,(
% 10.42/1.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (k4_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0)))))),
% 10.42/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.42/1.99  
% 10.42/1.99  fof(f28,plain,(
% 10.42/1.99    ! [X0] : (! [X1] : ((k4_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 10.42/1.99    inference(ennf_transformation,[],[f9])).
% 10.42/1.99  
% 10.42/1.99  fof(f50,plain,(
% 10.42/1.99    ! [X0] : (! [X1] : (((k4_relat_1(X0) = X1 | ? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X3,X2),X0)) & (r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1))) | k4_relat_1(X0) != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 10.42/1.99    inference(nnf_transformation,[],[f28])).
% 10.42/1.99  
% 10.42/1.99  fof(f51,plain,(
% 10.42/1.99    ! [X0] : (! [X1] : (((k4_relat_1(X0) = X1 | ? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0)) & (r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k4_relat_1(X0) != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 10.42/1.99    inference(rectify,[],[f50])).
% 10.42/1.99  
% 10.42/1.99  fof(f52,plain,(
% 10.42/1.99    ! [X1,X0] : (? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1))) => ((~r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)) & (r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1))))),
% 10.42/1.99    introduced(choice_axiom,[])).
% 10.42/1.99  
% 10.42/1.99  fof(f53,plain,(
% 10.42/1.99    ! [X0] : (! [X1] : (((k4_relat_1(X0) = X1 | ((~r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)) & (r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0)) & (r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k4_relat_1(X0) != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 10.42/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f51,f52])).
% 10.42/1.99  
% 10.42/1.99  fof(f72,plain,(
% 10.42/1.99    ( ! [X0,X1] : (k4_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 10.42/1.99    inference(cnf_transformation,[],[f53])).
% 10.42/1.99  
% 10.42/1.99  fof(f1,axiom,(
% 10.42/1.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 10.42/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.42/1.99  
% 10.42/1.99  fof(f40,plain,(
% 10.42/1.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 10.42/1.99    inference(nnf_transformation,[],[f1])).
% 10.42/1.99  
% 10.42/1.99  fof(f41,plain,(
% 10.42/1.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 10.42/1.99    inference(rectify,[],[f40])).
% 10.42/1.99  
% 10.42/1.99  fof(f42,plain,(
% 10.42/1.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 10.42/1.99    introduced(choice_axiom,[])).
% 10.42/1.99  
% 10.42/1.99  fof(f43,plain,(
% 10.42/1.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 10.42/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).
% 10.42/1.99  
% 10.42/1.99  fof(f58,plain,(
% 10.42/1.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 10.42/1.99    inference(cnf_transformation,[],[f43])).
% 10.42/1.99  
% 10.42/1.99  fof(f8,axiom,(
% 10.42/1.99    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 10.42/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.42/1.99  
% 10.42/1.99  fof(f27,plain,(
% 10.42/1.99    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 10.42/1.99    inference(ennf_transformation,[],[f8])).
% 10.42/1.99  
% 10.42/1.99  fof(f69,plain,(
% 10.42/1.99    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 10.42/1.99    inference(cnf_transformation,[],[f27])).
% 10.42/1.99  
% 10.42/1.99  fof(f10,axiom,(
% 10.42/1.99    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 10.42/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.42/1.99  
% 10.42/1.99  fof(f29,plain,(
% 10.42/1.99    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 10.42/1.99    inference(ennf_transformation,[],[f10])).
% 10.42/1.99  
% 10.42/1.99  fof(f74,plain,(
% 10.42/1.99    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 10.42/1.99    inference(cnf_transformation,[],[f29])).
% 10.42/1.99  
% 10.42/1.99  fof(f11,axiom,(
% 10.42/1.99    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 10.42/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.42/1.99  
% 10.42/1.99  fof(f30,plain,(
% 10.42/1.99    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 10.42/1.99    inference(ennf_transformation,[],[f11])).
% 10.42/1.99  
% 10.42/1.99  fof(f31,plain,(
% 10.42/1.99    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 10.42/1.99    inference(flattening,[],[f30])).
% 10.42/1.99  
% 10.42/1.99  fof(f75,plain,(
% 10.42/1.99    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 10.42/1.99    inference(cnf_transformation,[],[f31])).
% 10.42/1.99  
% 10.42/1.99  fof(f18,conjecture,(
% 10.42/1.99    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 10.42/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.42/1.99  
% 10.42/1.99  fof(f19,negated_conjecture,(
% 10.42/1.99    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 10.42/1.99    inference(negated_conjecture,[],[f18])).
% 10.42/1.99  
% 10.42/1.99  fof(f39,plain,(
% 10.42/1.99    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 10.42/1.99    inference(ennf_transformation,[],[f19])).
% 10.42/1.99  
% 10.42/1.99  fof(f56,plain,(
% 10.42/1.99    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK8,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK8)) & v1_relat_1(sK8))),
% 10.42/1.99    introduced(choice_axiom,[])).
% 10.42/1.99  
% 10.42/1.99  fof(f57,plain,(
% 10.42/1.99    (k1_xboole_0 != k5_relat_1(sK8,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK8)) & v1_relat_1(sK8)),
% 10.42/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f39,f56])).
% 10.42/1.99  
% 10.42/1.99  fof(f83,plain,(
% 10.42/1.99    v1_relat_1(sK8)),
% 10.42/1.99    inference(cnf_transformation,[],[f57])).
% 10.42/1.99  
% 10.42/1.99  fof(f15,axiom,(
% 10.42/1.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 10.42/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.42/1.99  
% 10.42/1.99  fof(f36,plain,(
% 10.42/1.99    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 10.42/1.99    inference(ennf_transformation,[],[f15])).
% 10.42/1.99  
% 10.42/1.99  fof(f79,plain,(
% 10.42/1.99    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 10.42/1.99    inference(cnf_transformation,[],[f36])).
% 10.42/1.99  
% 10.42/1.99  fof(f13,axiom,(
% 10.42/1.99    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 10.42/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.42/1.99  
% 10.42/1.99  fof(f34,plain,(
% 10.42/1.99    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 10.42/1.99    inference(ennf_transformation,[],[f13])).
% 10.42/1.99  
% 10.42/1.99  fof(f77,plain,(
% 10.42/1.99    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 10.42/1.99    inference(cnf_transformation,[],[f34])).
% 10.42/1.99  
% 10.42/1.99  fof(f7,axiom,(
% 10.42/1.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 10.42/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.42/1.99  
% 10.42/1.99  fof(f26,plain,(
% 10.42/1.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 10.42/1.99    inference(ennf_transformation,[],[f7])).
% 10.42/1.99  
% 10.42/1.99  fof(f68,plain,(
% 10.42/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 10.42/1.99    inference(cnf_transformation,[],[f26])).
% 10.42/1.99  
% 10.42/1.99  fof(f14,axiom,(
% 10.42/1.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 10.42/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.42/1.99  
% 10.42/1.99  fof(f35,plain,(
% 10.42/1.99    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 10.42/1.99    inference(ennf_transformation,[],[f14])).
% 10.42/1.99  
% 10.42/1.99  fof(f78,plain,(
% 10.42/1.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 10.42/1.99    inference(cnf_transformation,[],[f35])).
% 10.42/1.99  
% 10.42/1.99  fof(f17,axiom,(
% 10.42/1.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 10.42/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.42/1.99  
% 10.42/1.99  fof(f82,plain,(
% 10.42/1.99    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 10.42/1.99    inference(cnf_transformation,[],[f17])).
% 10.42/1.99  
% 10.42/1.99  fof(f59,plain,(
% 10.42/1.99    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 10.42/1.99    inference(cnf_transformation,[],[f43])).
% 10.42/1.99  
% 10.42/1.99  fof(f5,axiom,(
% 10.42/1.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 10.42/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.42/1.99  
% 10.42/1.99  fof(f21,plain,(
% 10.42/1.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 10.42/1.99    inference(rectify,[],[f5])).
% 10.42/1.99  
% 10.42/1.99  fof(f24,plain,(
% 10.42/1.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 10.42/1.99    inference(ennf_transformation,[],[f21])).
% 10.42/1.99  
% 10.42/1.99  fof(f46,plain,(
% 10.42/1.99    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 10.42/1.99    introduced(choice_axiom,[])).
% 10.42/1.99  
% 10.42/1.99  fof(f47,plain,(
% 10.42/1.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 10.42/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f46])).
% 10.42/1.99  
% 10.42/1.99  fof(f66,plain,(
% 10.42/1.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 10.42/1.99    inference(cnf_transformation,[],[f47])).
% 10.42/1.99  
% 10.42/1.99  fof(f4,axiom,(
% 10.42/1.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 10.42/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.42/1.99  
% 10.42/1.99  fof(f20,plain,(
% 10.42/1.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 10.42/1.99    inference(rectify,[],[f4])).
% 10.42/1.99  
% 10.42/1.99  fof(f23,plain,(
% 10.42/1.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 10.42/1.99    inference(ennf_transformation,[],[f20])).
% 10.42/1.99  
% 10.42/1.99  fof(f44,plain,(
% 10.42/1.99    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 10.42/1.99    introduced(choice_axiom,[])).
% 10.42/1.99  
% 10.42/1.99  fof(f45,plain,(
% 10.42/1.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 10.42/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f44])).
% 10.42/1.99  
% 10.42/1.99  fof(f63,plain,(
% 10.42/1.99    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 10.42/1.99    inference(cnf_transformation,[],[f45])).
% 10.42/1.99  
% 10.42/1.99  fof(f62,plain,(
% 10.42/1.99    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 10.42/1.99    inference(cnf_transformation,[],[f45])).
% 10.42/1.99  
% 10.42/1.99  fof(f6,axiom,(
% 10.42/1.99    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 10.42/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.42/1.99  
% 10.42/1.99  fof(f25,plain,(
% 10.42/1.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 10.42/1.99    inference(ennf_transformation,[],[f6])).
% 10.42/1.99  
% 10.42/1.99  fof(f48,plain,(
% 10.42/1.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 10.42/1.99    introduced(choice_axiom,[])).
% 10.42/1.99  
% 10.42/1.99  fof(f49,plain,(
% 10.42/1.99    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 10.42/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f48])).
% 10.42/1.99  
% 10.42/1.99  fof(f67,plain,(
% 10.42/1.99    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 10.42/1.99    inference(cnf_transformation,[],[f49])).
% 10.42/1.99  
% 10.42/1.99  fof(f12,axiom,(
% 10.42/1.99    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 10.42/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.42/1.99  
% 10.42/1.99  fof(f32,plain,(
% 10.42/1.99    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 10.42/1.99    inference(ennf_transformation,[],[f12])).
% 10.42/1.99  
% 10.42/1.99  fof(f33,plain,(
% 10.42/1.99    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 10.42/1.99    inference(flattening,[],[f32])).
% 10.42/1.99  
% 10.42/1.99  fof(f76,plain,(
% 10.42/1.99    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 10.42/1.99    inference(cnf_transformation,[],[f33])).
% 10.42/1.99  
% 10.42/1.99  fof(f3,axiom,(
% 10.42/1.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 10.42/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.42/1.99  
% 10.42/1.99  fof(f22,plain,(
% 10.42/1.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 10.42/1.99    inference(ennf_transformation,[],[f3])).
% 10.42/1.99  
% 10.42/1.99  fof(f61,plain,(
% 10.42/1.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 10.42/1.99    inference(cnf_transformation,[],[f22])).
% 10.42/1.99  
% 10.42/1.99  fof(f84,plain,(
% 10.42/1.99    k1_xboole_0 != k5_relat_1(sK8,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK8)),
% 10.42/1.99    inference(cnf_transformation,[],[f57])).
% 10.42/1.99  
% 10.42/1.99  cnf(c_2,plain,
% 10.42/1.99      ( v1_xboole_0(k1_xboole_0) ),
% 10.42/1.99      inference(cnf_transformation,[],[f60]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_1053,plain,
% 10.42/1.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 10.42/1.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_13,plain,
% 10.42/1.99      ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
% 10.42/1.99      | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
% 10.42/1.99      | ~ v1_relat_1(X1)
% 10.42/1.99      | ~ v1_relat_1(X0)
% 10.42/1.99      | k4_relat_1(X0) = X1 ),
% 10.42/1.99      inference(cnf_transformation,[],[f72]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_1043,plain,
% 10.42/1.99      ( k4_relat_1(X0) = X1
% 10.42/1.99      | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) = iProver_top
% 10.42/1.99      | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) = iProver_top
% 10.42/1.99      | v1_relat_1(X0) != iProver_top
% 10.42/1.99      | v1_relat_1(X1) != iProver_top ),
% 10.42/1.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_1,plain,
% 10.42/1.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 10.42/1.99      inference(cnf_transformation,[],[f58]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_1054,plain,
% 10.42/1.99      ( r2_hidden(X0,X1) != iProver_top
% 10.42/1.99      | v1_xboole_0(X1) != iProver_top ),
% 10.42/1.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_3087,plain,
% 10.42/1.99      ( k4_relat_1(X0) = X1
% 10.42/1.99      | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) = iProver_top
% 10.42/1.99      | v1_relat_1(X0) != iProver_top
% 10.42/1.99      | v1_relat_1(X1) != iProver_top
% 10.42/1.99      | v1_xboole_0(X0) != iProver_top ),
% 10.42/1.99      inference(superposition,[status(thm)],[c_1043,c_1054]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_11,plain,
% 10.42/1.99      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 10.42/1.99      inference(cnf_transformation,[],[f69]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_61,plain,
% 10.42/1.99      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 10.42/1.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_37179,plain,
% 10.42/1.99      ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) = iProver_top
% 10.42/1.99      | k4_relat_1(X0) = X1
% 10.42/1.99      | v1_relat_1(X1) != iProver_top
% 10.42/1.99      | v1_xboole_0(X0) != iProver_top ),
% 10.42/1.99      inference(global_propositional_subsumption,
% 10.42/1.99                [status(thm)],
% 10.42/1.99                [c_3087,c_61]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_37180,plain,
% 10.42/1.99      ( k4_relat_1(X0) = X1
% 10.42/1.99      | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) = iProver_top
% 10.42/1.99      | v1_relat_1(X1) != iProver_top
% 10.42/1.99      | v1_xboole_0(X0) != iProver_top ),
% 10.42/1.99      inference(renaming,[status(thm)],[c_37179]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_37187,plain,
% 10.42/1.99      ( k4_relat_1(X0) = X1
% 10.42/1.99      | v1_relat_1(X1) != iProver_top
% 10.42/1.99      | v1_xboole_0(X0) != iProver_top
% 10.42/1.99      | v1_xboole_0(X1) != iProver_top ),
% 10.42/1.99      inference(superposition,[status(thm)],[c_37180,c_1054]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_1045,plain,
% 10.42/1.99      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 10.42/1.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_37335,plain,
% 10.42/1.99      ( k4_relat_1(X0) = X1
% 10.42/1.99      | v1_xboole_0(X0) != iProver_top
% 10.42/1.99      | v1_xboole_0(X1) != iProver_top ),
% 10.42/1.99      inference(forward_subsumption_resolution,
% 10.42/1.99                [status(thm)],
% 10.42/1.99                [c_37187,c_1045]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_37339,plain,
% 10.42/1.99      ( k4_relat_1(k1_xboole_0) = X0 | v1_xboole_0(X0) != iProver_top ),
% 10.42/1.99      inference(superposition,[status(thm)],[c_1053,c_37335]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_38545,plain,
% 10.42/1.99      ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 10.42/1.99      inference(superposition,[status(thm)],[c_1053,c_37339]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_16,plain,
% 10.42/1.99      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 10.42/1.99      inference(cnf_transformation,[],[f74]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_1040,plain,
% 10.42/1.99      ( v1_relat_1(X0) != iProver_top
% 10.42/1.99      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 10.42/1.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_17,plain,
% 10.42/1.99      ( ~ v1_relat_1(X0)
% 10.42/1.99      | ~ v1_relat_1(X1)
% 10.42/1.99      | v1_relat_1(k5_relat_1(X1,X0)) ),
% 10.42/1.99      inference(cnf_transformation,[],[f75]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_1039,plain,
% 10.42/1.99      ( v1_relat_1(X0) != iProver_top
% 10.42/1.99      | v1_relat_1(X1) != iProver_top
% 10.42/1.99      | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
% 10.42/1.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_26,negated_conjecture,
% 10.42/1.99      ( v1_relat_1(sK8) ),
% 10.42/1.99      inference(cnf_transformation,[],[f83]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_1034,plain,
% 10.42/1.99      ( v1_relat_1(sK8) = iProver_top ),
% 10.42/1.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_1274,plain,
% 10.42/1.99      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 10.42/1.99      inference(superposition,[status(thm)],[c_1053,c_1045]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_21,plain,
% 10.42/1.99      ( ~ v1_relat_1(X0)
% 10.42/1.99      | ~ v1_relat_1(X1)
% 10.42/1.99      | k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0)) ),
% 10.42/1.99      inference(cnf_transformation,[],[f79]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_1036,plain,
% 10.42/1.99      ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
% 10.42/1.99      | v1_relat_1(X0) != iProver_top
% 10.42/1.99      | v1_relat_1(X1) != iProver_top ),
% 10.42/1.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_3218,plain,
% 10.42/1.99      ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k1_xboole_0))
% 10.42/1.99      | v1_relat_1(X0) != iProver_top ),
% 10.42/1.99      inference(superposition,[status(thm)],[c_1274,c_1036]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_6947,plain,
% 10.42/1.99      ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(X0))) = k4_relat_1(k5_relat_1(k4_relat_1(X0),k1_xboole_0))
% 10.42/1.99      | v1_relat_1(X0) != iProver_top ),
% 10.42/1.99      inference(superposition,[status(thm)],[c_1040,c_3218]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_11353,plain,
% 10.42/1.99      ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(sK8))) = k4_relat_1(k5_relat_1(k4_relat_1(sK8),k1_xboole_0)) ),
% 10.42/1.99      inference(superposition,[status(thm)],[c_1034,c_6947]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_19,plain,
% 10.42/1.99      ( ~ v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0 ),
% 10.42/1.99      inference(cnf_transformation,[],[f77]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_1037,plain,
% 10.42/1.99      ( k4_relat_1(k4_relat_1(X0)) = X0 | v1_relat_1(X0) != iProver_top ),
% 10.42/1.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_1347,plain,
% 10.42/1.99      ( k4_relat_1(k4_relat_1(sK8)) = sK8 ),
% 10.42/1.99      inference(superposition,[status(thm)],[c_1034,c_1037]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_11383,plain,
% 10.42/1.99      ( k4_relat_1(k5_relat_1(k4_relat_1(sK8),k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),sK8) ),
% 10.42/1.99      inference(light_normalisation,[status(thm)],[c_11353,c_1347]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_12194,plain,
% 10.42/1.99      ( v1_relat_1(k5_relat_1(k4_relat_1(sK8),k1_xboole_0)) != iProver_top
% 10.42/1.99      | v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK8)) = iProver_top ),
% 10.42/1.99      inference(superposition,[status(thm)],[c_11383,c_1040]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_14683,plain,
% 10.42/1.99      ( v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK8)) = iProver_top
% 10.42/1.99      | v1_relat_1(k4_relat_1(sK8)) != iProver_top
% 10.42/1.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 10.42/1.99      inference(superposition,[status(thm)],[c_1039,c_12194]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_63,plain,
% 10.42/1.99      ( v1_relat_1(k1_xboole_0) = iProver_top
% 10.42/1.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 10.42/1.99      inference(instantiation,[status(thm)],[c_61]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_86,plain,
% 10.42/1.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 10.42/1.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_18919,plain,
% 10.42/1.99      ( v1_relat_1(k4_relat_1(sK8)) != iProver_top
% 10.42/1.99      | v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK8)) = iProver_top ),
% 10.42/1.99      inference(global_propositional_subsumption,
% 10.42/1.99                [status(thm)],
% 10.42/1.99                [c_14683,c_63,c_86]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_18920,plain,
% 10.42/1.99      ( v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK8)) = iProver_top
% 10.42/1.99      | v1_relat_1(k4_relat_1(sK8)) != iProver_top ),
% 10.42/1.99      inference(renaming,[status(thm)],[c_18919]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_18978,plain,
% 10.42/1.99      ( k4_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK8))) = k5_relat_1(k4_relat_1(k1_xboole_0),sK8)
% 10.42/1.99      | v1_relat_1(k4_relat_1(sK8)) != iProver_top ),
% 10.42/1.99      inference(superposition,[status(thm)],[c_18920,c_1037]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_20614,plain,
% 10.42/1.99      ( k4_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK8))) = k5_relat_1(k4_relat_1(k1_xboole_0),sK8)
% 10.42/1.99      | v1_relat_1(sK8) != iProver_top ),
% 10.42/1.99      inference(superposition,[status(thm)],[c_1040,c_18978]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_27,plain,
% 10.42/1.99      ( v1_relat_1(sK8) = iProver_top ),
% 10.42/1.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_20698,plain,
% 10.42/1.99      ( k4_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK8))) = k5_relat_1(k4_relat_1(k1_xboole_0),sK8) ),
% 10.42/1.99      inference(global_propositional_subsumption,
% 10.42/1.99                [status(thm)],
% 10.42/1.99                [c_20614,c_27]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_38616,plain,
% 10.42/1.99      ( k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK8))) = k5_relat_1(k1_xboole_0,sK8) ),
% 10.42/1.99      inference(demodulation,[status(thm)],[c_38545,c_20698]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_2101,plain,
% 10.42/1.99      ( k5_relat_1(k4_relat_1(sK8),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,sK8))
% 10.42/1.99      | v1_relat_1(X0) != iProver_top ),
% 10.42/1.99      inference(superposition,[status(thm)],[c_1034,c_1036]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_3217,plain,
% 10.42/1.99      ( k5_relat_1(k4_relat_1(sK8),k4_relat_1(k1_xboole_0)) = k4_relat_1(k5_relat_1(k1_xboole_0,sK8)) ),
% 10.42/1.99      inference(superposition,[status(thm)],[c_1274,c_2101]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_38626,plain,
% 10.42/1.99      ( k5_relat_1(k4_relat_1(sK8),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,sK8)) ),
% 10.42/1.99      inference(demodulation,[status(thm)],[c_38545,c_3217]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_10,plain,
% 10.42/1.99      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 10.42/1.99      inference(cnf_transformation,[],[f68]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_20,plain,
% 10.42/1.99      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 10.42/1.99      | ~ v1_relat_1(X1)
% 10.42/1.99      | ~ v1_relat_1(X0) ),
% 10.42/1.99      inference(cnf_transformation,[],[f78]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_283,plain,
% 10.42/1.99      ( ~ v1_relat_1(X0)
% 10.42/1.99      | ~ v1_relat_1(X1)
% 10.42/1.99      | k3_xboole_0(X2,X3) = X2
% 10.42/1.99      | k2_relat_1(X1) != X3
% 10.42/1.99      | k2_relat_1(k5_relat_1(X0,X1)) != X2 ),
% 10.42/1.99      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_284,plain,
% 10.42/1.99      ( ~ v1_relat_1(X0)
% 10.42/1.99      | ~ v1_relat_1(X1)
% 10.42/1.99      | k3_xboole_0(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X0,X1)) ),
% 10.42/1.99      inference(unflattening,[status(thm)],[c_283]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_1033,plain,
% 10.42/1.99      ( k3_xboole_0(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X0,X1))
% 10.42/1.99      | v1_relat_1(X0) != iProver_top
% 10.42/1.99      | v1_relat_1(X1) != iProver_top ),
% 10.42/1.99      inference(predicate_to_equality,[status(thm)],[c_284]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_1410,plain,
% 10.42/1.99      ( k3_xboole_0(k2_relat_1(k5_relat_1(k4_relat_1(X0),X1)),k2_relat_1(X1)) = k2_relat_1(k5_relat_1(k4_relat_1(X0),X1))
% 10.42/1.99      | v1_relat_1(X0) != iProver_top
% 10.42/1.99      | v1_relat_1(X1) != iProver_top ),
% 10.42/1.99      inference(superposition,[status(thm)],[c_1040,c_1033]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_6204,plain,
% 10.42/1.99      ( k3_xboole_0(k2_relat_1(k5_relat_1(k4_relat_1(sK8),X0)),k2_relat_1(X0)) = k2_relat_1(k5_relat_1(k4_relat_1(sK8),X0))
% 10.42/1.99      | v1_relat_1(X0) != iProver_top ),
% 10.42/1.99      inference(superposition,[status(thm)],[c_1034,c_1410]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_7082,plain,
% 10.42/1.99      ( k3_xboole_0(k2_relat_1(k5_relat_1(k4_relat_1(sK8),k1_xboole_0)),k2_relat_1(k1_xboole_0)) = k2_relat_1(k5_relat_1(k4_relat_1(sK8),k1_xboole_0)) ),
% 10.42/1.99      inference(superposition,[status(thm)],[c_1274,c_6204]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_23,plain,
% 10.42/1.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 10.42/1.99      inference(cnf_transformation,[],[f82]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_7107,plain,
% 10.42/1.99      ( k3_xboole_0(k2_relat_1(k5_relat_1(k4_relat_1(sK8),k1_xboole_0)),k1_xboole_0) = k2_relat_1(k5_relat_1(k4_relat_1(sK8),k1_xboole_0)) ),
% 10.42/1.99      inference(light_normalisation,[status(thm)],[c_7082,c_23]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_0,plain,
% 10.42/1.99      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 10.42/1.99      inference(cnf_transformation,[],[f59]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_1055,plain,
% 10.42/1.99      ( r2_hidden(sK0(X0),X0) = iProver_top
% 10.42/1.99      | v1_xboole_0(X0) = iProver_top ),
% 10.42/1.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_7,plain,
% 10.42/1.99      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 10.42/1.99      inference(cnf_transformation,[],[f66]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_1048,plain,
% 10.42/1.99      ( r1_xboole_0(X0,X1) != iProver_top
% 10.42/1.99      | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
% 10.42/1.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_2183,plain,
% 10.42/1.99      ( r1_xboole_0(X0,X1) != iProver_top
% 10.42/1.99      | v1_xboole_0(k3_xboole_0(X0,X1)) = iProver_top ),
% 10.42/1.99      inference(superposition,[status(thm)],[c_1055,c_1048]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_7840,plain,
% 10.42/1.99      ( r1_xboole_0(k2_relat_1(k5_relat_1(k4_relat_1(sK8),k1_xboole_0)),k1_xboole_0) != iProver_top
% 10.42/1.99      | v1_xboole_0(k2_relat_1(k5_relat_1(k4_relat_1(sK8),k1_xboole_0))) = iProver_top ),
% 10.42/1.99      inference(superposition,[status(thm)],[c_7107,c_2183]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_5,plain,
% 10.42/1.99      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 10.42/1.99      inference(cnf_transformation,[],[f63]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_1050,plain,
% 10.42/1.99      ( r1_xboole_0(X0,X1) = iProver_top
% 10.42/1.99      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 10.42/1.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_1280,plain,
% 10.42/1.99      ( k3_xboole_0(k2_relat_1(k5_relat_1(sK8,X0)),k2_relat_1(X0)) = k2_relat_1(k5_relat_1(sK8,X0))
% 10.42/1.99      | v1_relat_1(X0) != iProver_top ),
% 10.42/1.99      inference(superposition,[status(thm)],[c_1034,c_1033]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_3227,plain,
% 10.42/1.99      ( k3_xboole_0(k2_relat_1(k5_relat_1(sK8,k1_xboole_0)),k2_relat_1(k1_xboole_0)) = k2_relat_1(k5_relat_1(sK8,k1_xboole_0)) ),
% 10.42/1.99      inference(superposition,[status(thm)],[c_1274,c_1280]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_3237,plain,
% 10.42/1.99      ( k3_xboole_0(k2_relat_1(k5_relat_1(sK8,k1_xboole_0)),k1_xboole_0) = k2_relat_1(k5_relat_1(sK8,k1_xboole_0)) ),
% 10.42/1.99      inference(light_normalisation,[status(thm)],[c_3227,c_23]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_3260,plain,
% 10.42/1.99      ( r1_xboole_0(k2_relat_1(k5_relat_1(sK8,k1_xboole_0)),k1_xboole_0) != iProver_top
% 10.42/1.99      | r2_hidden(X0,k2_relat_1(k5_relat_1(sK8,k1_xboole_0))) != iProver_top ),
% 10.42/1.99      inference(superposition,[status(thm)],[c_3237,c_1048]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_1841,plain,
% 10.42/1.99      ( r1_xboole_0(X0,X1) = iProver_top
% 10.42/1.99      | v1_xboole_0(X1) != iProver_top ),
% 10.42/1.99      inference(superposition,[status(thm)],[c_1050,c_1054]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_6,plain,
% 10.42/1.99      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 10.42/1.99      inference(cnf_transformation,[],[f62]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_1049,plain,
% 10.42/1.99      ( r1_xboole_0(X0,X1) = iProver_top
% 10.42/1.99      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 10.42/1.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_2185,plain,
% 10.42/1.99      ( r1_xboole_0(X0,X1) != iProver_top
% 10.42/1.99      | r1_xboole_0(k3_xboole_0(X0,X1),X2) = iProver_top ),
% 10.42/1.99      inference(superposition,[status(thm)],[c_1049,c_1048]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_6378,plain,
% 10.42/1.99      ( r1_xboole_0(k2_relat_1(k5_relat_1(sK8,k1_xboole_0)),X0) = iProver_top
% 10.42/1.99      | r1_xboole_0(k2_relat_1(k5_relat_1(sK8,k1_xboole_0)),k1_xboole_0) != iProver_top ),
% 10.42/1.99      inference(superposition,[status(thm)],[c_3237,c_2185]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_11337,plain,
% 10.42/1.99      ( r1_xboole_0(k2_relat_1(k5_relat_1(sK8,k1_xboole_0)),X0) = iProver_top
% 10.42/1.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 10.42/1.99      inference(superposition,[status(thm)],[c_1841,c_6378]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_11346,plain,
% 10.42/1.99      ( r1_xboole_0(k2_relat_1(k5_relat_1(sK8,k1_xboole_0)),k1_xboole_0) = iProver_top
% 10.42/1.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 10.42/1.99      inference(instantiation,[status(thm)],[c_11337]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_11684,plain,
% 10.42/1.99      ( r2_hidden(X0,k2_relat_1(k5_relat_1(sK8,k1_xboole_0))) != iProver_top ),
% 10.42/1.99      inference(global_propositional_subsumption,
% 10.42/1.99                [status(thm)],
% 10.42/1.99                [c_3260,c_86,c_11346]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_11692,plain,
% 10.42/1.99      ( r1_xboole_0(X0,k2_relat_1(k5_relat_1(sK8,k1_xboole_0))) = iProver_top ),
% 10.42/1.99      inference(superposition,[status(thm)],[c_1050,c_11684]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_9,plain,
% 10.42/1.99      ( r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0 ),
% 10.42/1.99      inference(cnf_transformation,[],[f67]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_1046,plain,
% 10.42/1.99      ( k1_xboole_0 = X0 | r2_hidden(sK3(X0),X0) = iProver_top ),
% 10.42/1.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_11694,plain,
% 10.42/1.99      ( k2_relat_1(k5_relat_1(sK8,k1_xboole_0)) = k1_xboole_0 ),
% 10.42/1.99      inference(superposition,[status(thm)],[c_1046,c_11684]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_12981,plain,
% 10.42/1.99      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 10.42/1.99      inference(light_normalisation,[status(thm)],[c_11692,c_11694]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_14978,plain,
% 10.42/1.99      ( v1_xboole_0(k2_relat_1(k5_relat_1(k4_relat_1(sK8),k1_xboole_0))) = iProver_top ),
% 10.42/1.99      inference(forward_subsumption_resolution,
% 10.42/1.99                [status(thm)],
% 10.42/1.99                [c_7840,c_12981]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_18,plain,
% 10.42/1.99      ( ~ v1_relat_1(X0)
% 10.42/1.99      | v1_xboole_0(X0)
% 10.42/1.99      | ~ v1_xboole_0(k2_relat_1(X0)) ),
% 10.42/1.99      inference(cnf_transformation,[],[f76]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_1038,plain,
% 10.42/1.99      ( v1_relat_1(X0) != iProver_top
% 10.42/1.99      | v1_xboole_0(X0) = iProver_top
% 10.42/1.99      | v1_xboole_0(k2_relat_1(X0)) != iProver_top ),
% 10.42/1.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_14982,plain,
% 10.42/1.99      ( v1_relat_1(k5_relat_1(k4_relat_1(sK8),k1_xboole_0)) != iProver_top
% 10.42/1.99      | v1_xboole_0(k5_relat_1(k4_relat_1(sK8),k1_xboole_0)) = iProver_top ),
% 10.42/1.99      inference(superposition,[status(thm)],[c_14978,c_1038]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_15798,plain,
% 10.42/1.99      ( v1_relat_1(k4_relat_1(sK8)) != iProver_top
% 10.42/1.99      | v1_relat_1(k1_xboole_0) != iProver_top
% 10.42/1.99      | v1_xboole_0(k5_relat_1(k4_relat_1(sK8),k1_xboole_0)) = iProver_top ),
% 10.42/1.99      inference(superposition,[status(thm)],[c_1039,c_14982]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_22138,plain,
% 10.42/1.99      ( v1_relat_1(k4_relat_1(sK8)) != iProver_top
% 10.42/1.99      | v1_xboole_0(k5_relat_1(k4_relat_1(sK8),k1_xboole_0)) = iProver_top ),
% 10.42/1.99      inference(global_propositional_subsumption,
% 10.42/1.99                [status(thm)],
% 10.42/1.99                [c_15798,c_63,c_86]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_3,plain,
% 10.42/1.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 10.42/1.99      inference(cnf_transformation,[],[f61]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_1052,plain,
% 10.42/1.99      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 10.42/1.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_22145,plain,
% 10.42/1.99      ( k5_relat_1(k4_relat_1(sK8),k1_xboole_0) = k1_xboole_0
% 10.42/1.99      | v1_relat_1(k4_relat_1(sK8)) != iProver_top ),
% 10.42/1.99      inference(superposition,[status(thm)],[c_22138,c_1052]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_23570,plain,
% 10.42/1.99      ( k5_relat_1(k4_relat_1(sK8),k1_xboole_0) = k1_xboole_0
% 10.42/1.99      | v1_relat_1(sK8) != iProver_top ),
% 10.42/1.99      inference(superposition,[status(thm)],[c_1040,c_22145]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_23601,plain,
% 10.42/1.99      ( k5_relat_1(k4_relat_1(sK8),k1_xboole_0) = k1_xboole_0 ),
% 10.42/1.99      inference(global_propositional_subsumption,
% 10.42/1.99                [status(thm)],
% 10.42/1.99                [c_23570,c_27]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_38629,plain,
% 10.42/1.99      ( k4_relat_1(k5_relat_1(k1_xboole_0,sK8)) = k1_xboole_0 ),
% 10.42/1.99      inference(light_normalisation,[status(thm)],[c_38626,c_23601]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_38660,plain,
% 10.42/1.99      ( k5_relat_1(k1_xboole_0,sK8) = k4_relat_1(k1_xboole_0) ),
% 10.42/1.99      inference(light_normalisation,[status(thm)],[c_38616,c_38629]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_38662,plain,
% 10.42/1.99      ( k5_relat_1(k1_xboole_0,sK8) = k1_xboole_0 ),
% 10.42/1.99      inference(light_normalisation,[status(thm)],[c_38660,c_38545]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_5181,plain,
% 10.42/1.99      ( r1_xboole_0(k2_relat_1(k5_relat_1(sK8,k1_xboole_0)),k1_xboole_0) != iProver_top
% 10.42/1.99      | v1_xboole_0(k2_relat_1(k5_relat_1(sK8,k1_xboole_0))) = iProver_top ),
% 10.42/1.99      inference(superposition,[status(thm)],[c_3237,c_2183]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_8065,plain,
% 10.42/1.99      ( v1_xboole_0(k2_relat_1(k5_relat_1(sK8,k1_xboole_0))) = iProver_top
% 10.42/1.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 10.42/1.99      inference(superposition,[status(thm)],[c_1841,c_5181]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_1356,plain,
% 10.42/1.99      ( v1_relat_1(k5_relat_1(sK8,k1_xboole_0))
% 10.42/1.99      | ~ v1_relat_1(sK8)
% 10.42/1.99      | ~ v1_relat_1(k1_xboole_0) ),
% 10.42/1.99      inference(instantiation,[status(thm)],[c_17]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_1357,plain,
% 10.42/1.99      ( v1_relat_1(k5_relat_1(sK8,k1_xboole_0)) = iProver_top
% 10.42/1.99      | v1_relat_1(sK8) != iProver_top
% 10.42/1.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 10.42/1.99      inference(predicate_to_equality,[status(thm)],[c_1356]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_1318,plain,
% 10.42/1.99      ( ~ v1_relat_1(k5_relat_1(sK8,k1_xboole_0))
% 10.42/1.99      | v1_xboole_0(k5_relat_1(sK8,k1_xboole_0))
% 10.42/1.99      | ~ v1_xboole_0(k2_relat_1(k5_relat_1(sK8,k1_xboole_0))) ),
% 10.42/1.99      inference(instantiation,[status(thm)],[c_18]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_1319,plain,
% 10.42/1.99      ( v1_relat_1(k5_relat_1(sK8,k1_xboole_0)) != iProver_top
% 10.42/1.99      | v1_xboole_0(k5_relat_1(sK8,k1_xboole_0)) = iProver_top
% 10.42/1.99      | v1_xboole_0(k2_relat_1(k5_relat_1(sK8,k1_xboole_0))) != iProver_top ),
% 10.42/1.99      inference(predicate_to_equality,[status(thm)],[c_1318]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_629,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_1269,plain,
% 10.42/1.99      ( k5_relat_1(k1_xboole_0,sK8) != X0
% 10.42/1.99      | k1_xboole_0 != X0
% 10.42/1.99      | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK8) ),
% 10.42/1.99      inference(instantiation,[status(thm)],[c_629]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_1270,plain,
% 10.42/1.99      ( k5_relat_1(k1_xboole_0,sK8) != k1_xboole_0
% 10.42/1.99      | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK8)
% 10.42/1.99      | k1_xboole_0 != k1_xboole_0 ),
% 10.42/1.99      inference(instantiation,[status(thm)],[c_1269]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_1237,plain,
% 10.42/1.99      ( ~ v1_xboole_0(k5_relat_1(sK8,k1_xboole_0))
% 10.42/1.99      | k1_xboole_0 = k5_relat_1(sK8,k1_xboole_0) ),
% 10.42/1.99      inference(instantiation,[status(thm)],[c_3]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_1238,plain,
% 10.42/1.99      ( k1_xboole_0 = k5_relat_1(sK8,k1_xboole_0)
% 10.42/1.99      | v1_xboole_0(k5_relat_1(sK8,k1_xboole_0)) != iProver_top ),
% 10.42/1.99      inference(predicate_to_equality,[status(thm)],[c_1237]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_84,plain,
% 10.42/1.99      ( ~ v1_xboole_0(k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 10.42/1.99      inference(instantiation,[status(thm)],[c_3]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(c_25,negated_conjecture,
% 10.42/1.99      ( k1_xboole_0 != k5_relat_1(sK8,k1_xboole_0)
% 10.42/1.99      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK8) ),
% 10.42/1.99      inference(cnf_transformation,[],[f84]) ).
% 10.42/1.99  
% 10.42/1.99  cnf(contradiction,plain,
% 10.42/1.99      ( $false ),
% 10.42/1.99      inference(minisat,
% 10.42/1.99                [status(thm)],
% 10.42/1.99                [c_38662,c_8065,c_1357,c_1319,c_1270,c_1238,c_86,c_2,
% 10.42/1.99                 c_84,c_63,c_25,c_27]) ).
% 10.42/1.99  
% 10.42/1.99  
% 10.42/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 10.42/1.99  
% 10.42/1.99  ------                               Statistics
% 10.42/1.99  
% 10.42/1.99  ------ General
% 10.42/1.99  
% 10.42/1.99  abstr_ref_over_cycles:                  0
% 10.42/1.99  abstr_ref_under_cycles:                 0
% 10.42/1.99  gc_basic_clause_elim:                   0
% 10.42/1.99  forced_gc_time:                         0
% 10.42/1.99  parsing_time:                           0.011
% 10.42/1.99  unif_index_cands_time:                  0.
% 10.42/1.99  unif_index_add_time:                    0.
% 10.42/1.99  orderings_time:                         0.
% 10.42/1.99  out_proof_time:                         0.016
% 10.42/1.99  total_time:                             1.064
% 10.42/1.99  num_of_symbols:                         52
% 10.42/1.99  num_of_terms:                           28809
% 10.42/1.99  
% 10.42/1.99  ------ Preprocessing
% 10.42/1.99  
% 10.42/1.99  num_of_splits:                          0
% 10.42/1.99  num_of_split_atoms:                     0
% 10.42/1.99  num_of_reused_defs:                     0
% 10.42/1.99  num_eq_ax_congr_red:                    44
% 10.42/1.99  num_of_sem_filtered_clauses:            1
% 10.42/1.99  num_of_subtypes:                        0
% 10.42/1.99  monotx_restored_types:                  0
% 10.42/1.99  sat_num_of_epr_types:                   0
% 10.42/1.99  sat_num_of_non_cyclic_types:            0
% 10.42/1.99  sat_guarded_non_collapsed_types:        0
% 10.42/1.99  num_pure_diseq_elim:                    0
% 10.42/1.99  simp_replaced_by:                       0
% 10.42/1.99  res_preprocessed:                       128
% 10.42/1.99  prep_upred:                             0
% 10.42/1.99  prep_unflattend:                        2
% 10.42/1.99  smt_new_axioms:                         0
% 10.42/1.99  pred_elim_cands:                        4
% 10.42/1.99  pred_elim:                              1
% 10.42/1.99  pred_elim_cl:                           1
% 10.42/1.99  pred_elim_cycles:                       3
% 10.42/1.99  merged_defs:                            0
% 10.42/1.99  merged_defs_ncl:                        0
% 10.42/1.99  bin_hyper_res:                          0
% 10.42/1.99  prep_cycles:                            4
% 10.42/1.99  pred_elim_time:                         0.002
% 10.42/1.99  splitting_time:                         0.
% 10.42/1.99  sem_filter_time:                        0.
% 10.42/1.99  monotx_time:                            0.001
% 10.42/1.99  subtype_inf_time:                       0.
% 10.42/1.99  
% 10.42/1.99  ------ Problem properties
% 10.42/1.99  
% 10.42/1.99  clauses:                                26
% 10.42/1.99  conjectures:                            2
% 10.42/1.99  epr:                                    6
% 10.42/1.99  horn:                                   19
% 10.42/1.99  ground:                                 5
% 10.42/1.99  unary:                                  4
% 10.42/1.99  binary:                                 12
% 10.42/1.99  lits:                                   64
% 10.42/1.99  lits_eq:                                12
% 10.42/1.99  fd_pure:                                0
% 10.42/1.99  fd_pseudo:                              0
% 10.42/1.99  fd_cond:                                3
% 10.42/1.99  fd_pseudo_cond:                         2
% 10.42/1.99  ac_symbols:                             0
% 10.42/1.99  
% 10.42/1.99  ------ Propositional Solver
% 10.42/1.99  
% 10.42/1.99  prop_solver_calls:                      34
% 10.42/1.99  prop_fast_solver_calls:                 1561
% 10.42/1.99  smt_solver_calls:                       0
% 10.42/1.99  smt_fast_solver_calls:                  0
% 10.42/1.99  prop_num_of_clauses:                    12507
% 10.42/1.99  prop_preprocess_simplified:             17594
% 10.42/1.99  prop_fo_subsumed:                       60
% 10.42/1.99  prop_solver_time:                       0.
% 10.42/1.99  smt_solver_time:                        0.
% 10.42/1.99  smt_fast_solver_time:                   0.
% 10.42/1.99  prop_fast_solver_time:                  0.
% 10.42/1.99  prop_unsat_core_time:                   0.001
% 10.42/1.99  
% 10.42/1.99  ------ QBF
% 10.42/1.99  
% 10.42/1.99  qbf_q_res:                              0
% 10.42/1.99  qbf_num_tautologies:                    0
% 10.42/1.99  qbf_prep_cycles:                        0
% 10.42/1.99  
% 10.42/1.99  ------ BMC1
% 10.42/1.99  
% 10.42/1.99  bmc1_current_bound:                     -1
% 10.42/1.99  bmc1_last_solved_bound:                 -1
% 10.42/1.99  bmc1_unsat_core_size:                   -1
% 10.42/1.99  bmc1_unsat_core_parents_size:           -1
% 10.42/1.99  bmc1_merge_next_fun:                    0
% 10.42/1.99  bmc1_unsat_core_clauses_time:           0.
% 10.42/1.99  
% 10.42/1.99  ------ Instantiation
% 10.42/1.99  
% 10.42/1.99  inst_num_of_clauses:                    2992
% 10.42/1.99  inst_num_in_passive:                    1229
% 10.42/1.99  inst_num_in_active:                     1396
% 10.42/1.99  inst_num_in_unprocessed:                367
% 10.42/1.99  inst_num_of_loops:                      2000
% 10.42/1.99  inst_num_of_learning_restarts:          0
% 10.42/1.99  inst_num_moves_active_passive:          598
% 10.42/1.99  inst_lit_activity:                      0
% 10.42/1.99  inst_lit_activity_moves:                0
% 10.42/1.99  inst_num_tautologies:                   0
% 10.42/1.99  inst_num_prop_implied:                  0
% 10.42/1.99  inst_num_existing_simplified:           0
% 10.42/1.99  inst_num_eq_res_simplified:             0
% 10.42/1.99  inst_num_child_elim:                    0
% 10.42/1.99  inst_num_of_dismatching_blockings:      2079
% 10.42/1.99  inst_num_of_non_proper_insts:           3394
% 10.42/1.99  inst_num_of_duplicates:                 0
% 10.42/1.99  inst_inst_num_from_inst_to_res:         0
% 10.42/1.99  inst_dismatching_checking_time:         0.
% 10.42/1.99  
% 10.42/1.99  ------ Resolution
% 10.42/1.99  
% 10.42/1.99  res_num_of_clauses:                     0
% 10.42/1.99  res_num_in_passive:                     0
% 10.42/1.99  res_num_in_active:                      0
% 10.42/1.99  res_num_of_loops:                       132
% 10.42/1.99  res_forward_subset_subsumed:            209
% 10.42/1.99  res_backward_subset_subsumed:           0
% 10.42/1.99  res_forward_subsumed:                   0
% 10.42/1.99  res_backward_subsumed:                  0
% 10.42/1.99  res_forward_subsumption_resolution:     0
% 10.42/1.99  res_backward_subsumption_resolution:    0
% 10.42/1.99  res_clause_to_clause_subsumption:       8792
% 10.42/1.99  res_orphan_elimination:                 0
% 10.42/1.99  res_tautology_del:                      415
% 10.42/1.99  res_num_eq_res_simplified:              0
% 10.42/1.99  res_num_sel_changes:                    0
% 10.42/1.99  res_moves_from_active_to_pass:          0
% 10.42/1.99  
% 10.42/1.99  ------ Superposition
% 10.42/1.99  
% 10.42/1.99  sup_time_total:                         0.
% 10.42/1.99  sup_time_generating:                    0.
% 10.42/1.99  sup_time_sim_full:                      0.
% 10.42/1.99  sup_time_sim_immed:                     0.
% 10.42/1.99  
% 10.42/1.99  sup_num_of_clauses:                     1927
% 10.42/1.99  sup_num_in_active:                      295
% 10.42/1.99  sup_num_in_passive:                     1632
% 10.42/1.99  sup_num_of_loops:                       398
% 10.42/1.99  sup_fw_superposition:                   1171
% 10.42/1.99  sup_bw_superposition:                   1416
% 10.42/1.99  sup_immediate_simplified:               673
% 10.42/1.99  sup_given_eliminated:                   6
% 10.42/1.99  comparisons_done:                       0
% 10.42/1.99  comparisons_avoided:                    0
% 10.42/1.99  
% 10.42/1.99  ------ Simplifications
% 10.42/1.99  
% 10.42/1.99  
% 10.42/1.99  sim_fw_subset_subsumed:                 31
% 10.42/1.99  sim_bw_subset_subsumed:                 72
% 10.42/1.99  sim_fw_subsumed:                        102
% 10.42/1.99  sim_bw_subsumed:                        0
% 10.42/1.99  sim_fw_subsumption_res:                 8
% 10.42/1.99  sim_bw_subsumption_res:                 0
% 10.42/1.99  sim_tautology_del:                      31
% 10.42/1.99  sim_eq_tautology_del:                   186
% 10.42/1.99  sim_eq_res_simp:                        1
% 10.42/1.99  sim_fw_demodulated:                     3
% 10.42/1.99  sim_bw_demodulated:                     136
% 10.42/1.99  sim_light_normalised:                   545
% 10.42/1.99  sim_joinable_taut:                      0
% 10.42/1.99  sim_joinable_simp:                      0
% 10.42/1.99  sim_ac_normalised:                      0
% 10.42/1.99  sim_smt_subsumption:                    0
% 10.42/1.99  
%------------------------------------------------------------------------------
