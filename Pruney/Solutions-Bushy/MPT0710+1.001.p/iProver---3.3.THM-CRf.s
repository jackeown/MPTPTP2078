%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0710+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:57 EST 2020

% Result     : Theorem 19.75s
% Output     : CNFRefutation 19.75s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 427 expanded)
%              Number of clauses        :  136 ( 172 expanded)
%              Number of leaves         :   19 ( 108 expanded)
%              Depth                    :   15
%              Number of atoms          :  649 (2960 expanded)
%              Number of equality atoms :  364 (1148 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( r1_tarski(X2,k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) )
             => ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              <=> ! [X3] :
                    ( r2_hidden(X3,X2)
                   => k1_funct_1(X0,X3) = k1_funct_1(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( r1_tarski(X2,k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) )
               => ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
                <=> ! [X3] :
                      ( r2_hidden(X3,X2)
                     => k1_funct_1(X0,X3) = k1_funct_1(X1,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              <~> ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,X2) ) )
              & r1_tarski(X2,k1_relat_1(X1))
              & r1_tarski(X2,k1_relat_1(X0)) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              <~> ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,X2) ) )
              & r1_tarski(X2,k1_relat_1(X1))
              & r1_tarski(X2,k1_relat_1(X0)) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
                    & r2_hidden(X3,X2) )
                | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) )
              & ( ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,X2) )
                | k7_relat_1(X0,X2) = k7_relat_1(X1,X2) )
              & r1_tarski(X2,k1_relat_1(X1))
              & r1_tarski(X2,k1_relat_1(X0)) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
                    & r2_hidden(X3,X2) )
                | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) )
              & ( ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,X2) )
                | k7_relat_1(X0,X2) = k7_relat_1(X1,X2) )
              & r1_tarski(X2,k1_relat_1(X1))
              & r1_tarski(X2,k1_relat_1(X0)) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
                    & r2_hidden(X3,X2) )
                | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) )
              & ( ! [X4] :
                    ( k1_funct_1(X0,X4) = k1_funct_1(X1,X4)
                    | ~ r2_hidden(X4,X2) )
                | k7_relat_1(X0,X2) = k7_relat_1(X1,X2) )
              & r1_tarski(X2,k1_relat_1(X1))
              & r1_tarski(X2,k1_relat_1(X0)) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(rectify,[],[f22])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
          & r2_hidden(X3,X2) )
     => ( k1_funct_1(X0,sK4) != k1_funct_1(X1,sK4)
        & r2_hidden(sK4,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
                & r2_hidden(X3,X2) )
            | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) )
          & ( ! [X4] :
                ( k1_funct_1(X0,X4) = k1_funct_1(X1,X4)
                | ~ r2_hidden(X4,X2) )
            | k7_relat_1(X0,X2) = k7_relat_1(X1,X2) )
          & r1_tarski(X2,k1_relat_1(X1))
          & r1_tarski(X2,k1_relat_1(X0)) )
     => ( ( ? [X3] :
              ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
              & r2_hidden(X3,sK3) )
          | k7_relat_1(X0,sK3) != k7_relat_1(X1,sK3) )
        & ( ! [X4] :
              ( k1_funct_1(X0,X4) = k1_funct_1(X1,X4)
              | ~ r2_hidden(X4,sK3) )
          | k7_relat_1(X0,sK3) = k7_relat_1(X1,sK3) )
        & r1_tarski(sK3,k1_relat_1(X1))
        & r1_tarski(sK3,k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
                    & r2_hidden(X3,X2) )
                | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) )
              & ( ! [X4] :
                    ( k1_funct_1(X0,X4) = k1_funct_1(X1,X4)
                    | ~ r2_hidden(X4,X2) )
                | k7_relat_1(X0,X2) = k7_relat_1(X1,X2) )
              & r1_tarski(X2,k1_relat_1(X1))
              & r1_tarski(X2,k1_relat_1(X0)) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( ( ? [X3] :
                  ( k1_funct_1(sK2,X3) != k1_funct_1(X0,X3)
                  & r2_hidden(X3,X2) )
              | k7_relat_1(sK2,X2) != k7_relat_1(X0,X2) )
            & ( ! [X4] :
                  ( k1_funct_1(sK2,X4) = k1_funct_1(X0,X4)
                  | ~ r2_hidden(X4,X2) )
              | k7_relat_1(sK2,X2) = k7_relat_1(X0,X2) )
            & r1_tarski(X2,k1_relat_1(sK2))
            & r1_tarski(X2,k1_relat_1(X0)) )
        & v1_funct_1(sK2)
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
                      & r2_hidden(X3,X2) )
                  | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) )
                & ( ! [X4] :
                      ( k1_funct_1(X0,X4) = k1_funct_1(X1,X4)
                      | ~ r2_hidden(X4,X2) )
                  | k7_relat_1(X0,X2) = k7_relat_1(X1,X2) )
                & r1_tarski(X2,k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) )
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( k1_funct_1(sK1,X3) != k1_funct_1(X1,X3)
                    & r2_hidden(X3,X2) )
                | k7_relat_1(sK1,X2) != k7_relat_1(X1,X2) )
              & ( ! [X4] :
                    ( k1_funct_1(sK1,X4) = k1_funct_1(X1,X4)
                    | ~ r2_hidden(X4,X2) )
                | k7_relat_1(sK1,X2) = k7_relat_1(X1,X2) )
              & r1_tarski(X2,k1_relat_1(X1))
              & r1_tarski(X2,k1_relat_1(sK1)) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ( ( k1_funct_1(sK1,sK4) != k1_funct_1(sK2,sK4)
        & r2_hidden(sK4,sK3) )
      | k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) )
    & ( ! [X4] :
          ( k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4)
          | ~ r2_hidden(X4,sK3) )
      | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3) )
    & r1_tarski(sK3,k1_relat_1(sK2))
    & r1_tarski(sK3,k1_relat_1(sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f23,f27,f26,f25,f24])).

fof(f37,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f41,plain,(
    r1_tarski(sK3,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f39,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f42,plain,(
    r1_tarski(sK3,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,X1)
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f43,plain,(
    ! [X4] :
      ( k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4)
      | ~ r2_hidden(X4,sK3)
      | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
        & r2_hidden(sK0(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
            & r2_hidden(sK0(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f19])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f35,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f44,plain,
    ( r2_hidden(sK4,sK3)
    | k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f45,plain,
    ( k1_funct_1(sK1,sK4) != k1_funct_1(sK2,sK4)
    | k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f40,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f38,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_154,plain,
    ( k3_xboole_0(X0_42,X1_42) = k3_xboole_0(X1_42,X0_42) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_138,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_70464,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_138])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_149,plain,
    ( ~ v1_relat_1(X0_41)
    | k1_relat_1(k7_relat_1(X0_41,X0_42)) = k3_xboole_0(k1_relat_1(X0_41),X0_42) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_70461,plain,
    ( k1_relat_1(k7_relat_1(X0_41,X0_42)) = k3_xboole_0(k1_relat_1(X0_41),X0_42)
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_149])).

cnf(c_70920,plain,
    ( k1_relat_1(k7_relat_1(sK1,X0_42)) = k3_xboole_0(k1_relat_1(sK1),X0_42) ),
    inference(superposition,[status(thm)],[c_70464,c_70461])).

cnf(c_71251,plain,
    ( k1_relat_1(k7_relat_1(sK1,X0_42)) = k3_xboole_0(X0_42,k1_relat_1(sK1)) ),
    inference(superposition,[status(thm)],[c_154,c_70920])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(sK3,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_142,negated_conjecture,
    ( r1_tarski(sK3,k1_relat_1(sK1)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_70468,plain,
    ( r1_tarski(sK3,k1_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_142])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_151,plain,
    ( ~ r1_tarski(X0_42,X1_42)
    | k3_xboole_0(X0_42,X1_42) = X0_42 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_70459,plain,
    ( k3_xboole_0(X0_42,X1_42) = X0_42
    | r1_tarski(X0_42,X1_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_151])).

cnf(c_70911,plain,
    ( k3_xboole_0(sK3,k1_relat_1(sK1)) = sK3 ),
    inference(superposition,[status(thm)],[c_70468,c_70459])).

cnf(c_71355,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_71251,c_70911])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_140,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_70466,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_140])).

cnf(c_70919,plain,
    ( k1_relat_1(k7_relat_1(sK2,X0_42)) = k3_xboole_0(k1_relat_1(sK2),X0_42) ),
    inference(superposition,[status(thm)],[c_70466,c_70461])).

cnf(c_71138,plain,
    ( k1_relat_1(k7_relat_1(sK2,X0_42)) = k3_xboole_0(X0_42,k1_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_154,c_70919])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK3,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_143,negated_conjecture,
    ( r1_tarski(sK3,k1_relat_1(sK2)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_70469,plain,
    ( r1_tarski(sK3,k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_143])).

cnf(c_70910,plain,
    ( k3_xboole_0(sK3,k1_relat_1(sK2)) = sK3 ),
    inference(superposition,[status(thm)],[c_70469,c_70459])).

cnf(c_71263,plain,
    ( k1_relat_1(k7_relat_1(sK2,sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_71138,c_70910])).

cnf(c_162,plain,
    ( X0_44 != X1_44
    | X2_44 != X1_44
    | X2_44 = X0_44 ),
    theory(equality)).

cnf(c_44574,plain,
    ( X0_44 != X1_44
    | X0_44 = k1_funct_1(X0_41,X0_43)
    | k1_funct_1(X0_41,X0_43) != X1_44 ),
    inference(instantiation,[status(thm)],[c_162])).

cnf(c_44661,plain,
    ( X0_44 != k1_funct_1(X0_41,X0_43)
    | X0_44 = k1_funct_1(X1_41,X1_43)
    | k1_funct_1(X1_41,X1_43) != k1_funct_1(X0_41,X0_43) ),
    inference(instantiation,[status(thm)],[c_44574])).

cnf(c_44667,plain,
    ( k1_funct_1(X0_41,X0_43) != k1_funct_1(X1_41,X1_43)
    | k1_funct_1(X2_41,X2_43) != k1_funct_1(X1_41,X1_43)
    | k1_funct_1(X0_41,X0_43) = k1_funct_1(X2_41,X2_43) ),
    inference(instantiation,[status(thm)],[c_44661])).

cnf(c_55772,plain,
    ( k1_funct_1(X0_41,X0_43) != k1_funct_1(X1_41,X1_43)
    | k1_funct_1(k7_relat_1(X2_41,X0_42),sK0(k7_relat_1(X2_41,X0_42),X3_41)) != k1_funct_1(X1_41,X1_43)
    | k1_funct_1(k7_relat_1(X2_41,X0_42),sK0(k7_relat_1(X2_41,X0_42),X3_41)) = k1_funct_1(X0_41,X0_43) ),
    inference(instantiation,[status(thm)],[c_44667])).

cnf(c_66330,plain,
    ( k1_funct_1(X0_41,X0_43) != k1_funct_1(sK2,sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3)))
    | k1_funct_1(k7_relat_1(sK2,sK3),sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3))) = k1_funct_1(X0_41,X0_43)
    | k1_funct_1(k7_relat_1(sK2,sK3),sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3))) != k1_funct_1(sK2,sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3))) ),
    inference(instantiation,[status(thm)],[c_55772])).

cnf(c_70044,plain,
    ( k1_funct_1(k7_relat_1(sK2,sK3),sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3))) != k1_funct_1(sK2,sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3)))
    | k1_funct_1(k7_relat_1(sK2,sK3),sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3))) = k1_funct_1(sK1,sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3)))
    | k1_funct_1(sK1,sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3))) != k1_funct_1(sK2,sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3))) ),
    inference(instantiation,[status(thm)],[c_66330])).

cnf(c_50420,plain,
    ( k1_funct_1(X0_41,sK0(X0_41,k7_relat_1(X1_41,X0_42))) != k1_funct_1(X2_41,X0_43)
    | k1_funct_1(k7_relat_1(X1_41,X0_42),sK0(X0_41,k7_relat_1(X1_41,X0_42))) != k1_funct_1(X2_41,X0_43)
    | k1_funct_1(k7_relat_1(X1_41,X0_42),sK0(X0_41,k7_relat_1(X1_41,X0_42))) = k1_funct_1(X0_41,sK0(X0_41,k7_relat_1(X1_41,X0_42))) ),
    inference(instantiation,[status(thm)],[c_44667])).

cnf(c_58383,plain,
    ( k1_funct_1(k7_relat_1(sK2,sK3),sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3))) != k1_funct_1(sK1,sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3)))
    | k1_funct_1(k7_relat_1(sK1,sK3),sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3))) = k1_funct_1(k7_relat_1(sK2,sK3),sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3)))
    | k1_funct_1(k7_relat_1(sK1,sK3),sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3))) != k1_funct_1(sK1,sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3))) ),
    inference(instantiation,[status(thm)],[c_50420])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_150,plain,
    ( ~ r2_hidden(X0_43,X0_42)
    | ~ v1_relat_1(X0_41)
    | ~ v1_funct_1(X0_41)
    | k1_funct_1(k7_relat_1(X0_41,X0_42),X0_43) = k1_funct_1(X0_41,X0_43) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_47292,plain,
    ( ~ r2_hidden(sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3)),X0_42)
    | ~ v1_relat_1(X0_41)
    | ~ v1_funct_1(X0_41)
    | k1_funct_1(k7_relat_1(X0_41,X0_42),sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3))) = k1_funct_1(X0_41,sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3))) ),
    inference(instantiation,[status(thm)],[c_150])).

cnf(c_54865,plain,
    ( ~ r2_hidden(sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3)),X0_42)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_funct_1(k7_relat_1(sK2,X0_42),sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3))) = k1_funct_1(sK2,sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3))) ),
    inference(instantiation,[status(thm)],[c_47292])).

cnf(c_54866,plain,
    ( k1_funct_1(k7_relat_1(sK2,X0_42),sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3))) = k1_funct_1(sK2,sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3)))
    | r2_hidden(sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3)),X0_42) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54865])).

cnf(c_54868,plain,
    ( k1_funct_1(k7_relat_1(sK2,sK3),sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3))) = k1_funct_1(sK2,sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3)))
    | r2_hidden(sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3)),sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_54866])).

cnf(c_10,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)
    | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_144,negated_conjecture,
    ( ~ r2_hidden(X0_43,sK3)
    | k1_funct_1(sK1,X0_43) = k1_funct_1(sK2,X0_43)
    | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_53019,plain,
    ( ~ r2_hidden(sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3)),sK3)
    | k1_funct_1(sK1,sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3))) = k1_funct_1(sK2,sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3)))
    | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_144])).

cnf(c_53020,plain,
    ( k1_funct_1(sK1,sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3))) = k1_funct_1(sK2,sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3)))
    | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3)
    | r2_hidden(sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3)),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53019])).

cnf(c_47298,plain,
    ( k1_funct_1(k7_relat_1(X0_41,X0_42),sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3))) = k1_funct_1(X0_41,sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3)))
    | r2_hidden(sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3)),X0_42) != iProver_top
    | v1_relat_1(X0_41) != iProver_top
    | v1_funct_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47292])).

cnf(c_47300,plain,
    ( k1_funct_1(k7_relat_1(sK1,sK3),sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3))) = k1_funct_1(sK1,sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3)))
    | r2_hidden(sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3)),sK3) != iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_47298])).

cnf(c_161,plain,
    ( X0_42 != X1_42
    | X2_42 != X1_42
    | X2_42 = X0_42 ),
    theory(equality)).

cnf(c_45357,plain,
    ( X0_42 != X1_42
    | X0_42 = k1_relat_1(k7_relat_1(sK2,sK3))
    | k1_relat_1(k7_relat_1(sK2,sK3)) != X1_42 ),
    inference(instantiation,[status(thm)],[c_161])).

cnf(c_45358,plain,
    ( k1_relat_1(k7_relat_1(sK2,sK3)) != sK3
    | sK3 = k1_relat_1(k7_relat_1(sK2,sK3))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_45357])).

cnf(c_169,plain,
    ( ~ r2_hidden(X0_43,X0_42)
    | r2_hidden(X1_43,X1_42)
    | X1_43 != X0_43
    | X1_42 != X0_42 ),
    theory(equality)).

cnf(c_42982,plain,
    ( r2_hidden(X0_43,X0_42)
    | ~ r2_hidden(sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3)),k1_relat_1(k7_relat_1(sK2,sK3)))
    | X0_43 != sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3))
    | X0_42 != k1_relat_1(k7_relat_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_169])).

cnf(c_44718,plain,
    ( r2_hidden(sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3)),X0_42)
    | ~ r2_hidden(sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3)),k1_relat_1(k7_relat_1(sK2,sK3)))
    | sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3)) != sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3))
    | X0_42 != k1_relat_1(k7_relat_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_42982])).

cnf(c_44719,plain,
    ( r2_hidden(sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3)),X0_42)
    | ~ r2_hidden(sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3)),k1_relat_1(k7_relat_1(sK2,sK3)))
    | X0_42 != k1_relat_1(k7_relat_1(sK2,sK3)) ),
    inference(equality_resolution_simp,[status(thm)],[c_44718])).

cnf(c_44720,plain,
    ( X0_42 != k1_relat_1(k7_relat_1(sK2,sK3))
    | r2_hidden(sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3)),X0_42) = iProver_top
    | r2_hidden(sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3)),k1_relat_1(k7_relat_1(sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44719])).

cnf(c_44722,plain,
    ( sK3 != k1_relat_1(k7_relat_1(sK2,sK3))
    | r2_hidden(sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3)),k1_relat_1(k7_relat_1(sK2,sK3))) != iProver_top
    | r2_hidden(sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3)),sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_44720])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X1 = X0
    | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1))
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_148,plain,
    ( ~ v1_relat_1(X0_41)
    | ~ v1_relat_1(X1_41)
    | ~ v1_funct_1(X0_41)
    | ~ v1_funct_1(X1_41)
    | k1_funct_1(X1_41,sK0(X0_41,X1_41)) != k1_funct_1(X0_41,sK0(X0_41,X1_41))
    | k1_relat_1(X0_41) != k1_relat_1(X1_41)
    | X1_41 = X0_41 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_37287,plain,
    ( ~ v1_relat_1(X0_41)
    | ~ v1_relat_1(k7_relat_1(X1_41,X0_42))
    | ~ v1_funct_1(X0_41)
    | ~ v1_funct_1(k7_relat_1(X1_41,X0_42))
    | k1_funct_1(X0_41,sK0(k7_relat_1(X1_41,X0_42),X0_41)) != k1_funct_1(k7_relat_1(X1_41,X0_42),sK0(k7_relat_1(X1_41,X0_42),X0_41))
    | k1_relat_1(k7_relat_1(X1_41,X0_42)) != k1_relat_1(X0_41)
    | X0_41 = k7_relat_1(X1_41,X0_42) ),
    inference(instantiation,[status(thm)],[c_148])).

cnf(c_41311,plain,
    ( ~ v1_relat_1(k7_relat_1(X0_41,X0_42))
    | ~ v1_relat_1(k7_relat_1(X1_41,X1_42))
    | ~ v1_funct_1(k7_relat_1(X0_41,X0_42))
    | ~ v1_funct_1(k7_relat_1(X1_41,X1_42))
    | k1_funct_1(k7_relat_1(X0_41,X0_42),sK0(k7_relat_1(X1_41,X1_42),k7_relat_1(X0_41,X0_42))) != k1_funct_1(k7_relat_1(X1_41,X1_42),sK0(k7_relat_1(X1_41,X1_42),k7_relat_1(X0_41,X0_42)))
    | k1_relat_1(k7_relat_1(X1_41,X1_42)) != k1_relat_1(k7_relat_1(X0_41,X0_42))
    | k7_relat_1(X0_41,X0_42) = k7_relat_1(X1_41,X1_42) ),
    inference(instantiation,[status(thm)],[c_37287])).

cnf(c_41658,plain,
    ( ~ v1_relat_1(k7_relat_1(X0_41,X0_42))
    | ~ v1_relat_1(k7_relat_1(sK2,X1_42))
    | ~ v1_funct_1(k7_relat_1(X0_41,X0_42))
    | ~ v1_funct_1(k7_relat_1(sK2,X1_42))
    | k1_funct_1(k7_relat_1(X0_41,X0_42),sK0(k7_relat_1(sK2,X1_42),k7_relat_1(X0_41,X0_42))) != k1_funct_1(k7_relat_1(sK2,X1_42),sK0(k7_relat_1(sK2,X1_42),k7_relat_1(X0_41,X0_42)))
    | k1_relat_1(k7_relat_1(sK2,X1_42)) != k1_relat_1(k7_relat_1(X0_41,X0_42))
    | k7_relat_1(X0_41,X0_42) = k7_relat_1(sK2,X1_42) ),
    inference(instantiation,[status(thm)],[c_41311])).

cnf(c_41659,plain,
    ( k1_funct_1(k7_relat_1(X0_41,X0_42),sK0(k7_relat_1(sK2,X1_42),k7_relat_1(X0_41,X0_42))) != k1_funct_1(k7_relat_1(sK2,X1_42),sK0(k7_relat_1(sK2,X1_42),k7_relat_1(X0_41,X0_42)))
    | k1_relat_1(k7_relat_1(sK2,X1_42)) != k1_relat_1(k7_relat_1(X0_41,X0_42))
    | k7_relat_1(X0_41,X0_42) = k7_relat_1(sK2,X1_42)
    | v1_relat_1(k7_relat_1(X0_41,X0_42)) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,X1_42)) != iProver_top
    | v1_funct_1(k7_relat_1(X0_41,X0_42)) != iProver_top
    | v1_funct_1(k7_relat_1(sK2,X1_42)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41658])).

cnf(c_41661,plain,
    ( k1_funct_1(k7_relat_1(sK1,sK3),sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3))) != k1_funct_1(k7_relat_1(sK2,sK3),sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3)))
    | k1_relat_1(k7_relat_1(sK2,sK3)) != k1_relat_1(k7_relat_1(sK1,sK3))
    | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3)
    | v1_relat_1(k7_relat_1(sK2,sK3)) != iProver_top
    | v1_relat_1(k7_relat_1(sK1,sK3)) != iProver_top
    | v1_funct_1(k7_relat_1(sK2,sK3)) != iProver_top
    | v1_funct_1(k7_relat_1(sK1,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_41659])).

cnf(c_7,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X1 = X0
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_147,plain,
    ( r2_hidden(sK0(X0_41,X1_41),k1_relat_1(X0_41))
    | ~ v1_relat_1(X0_41)
    | ~ v1_relat_1(X1_41)
    | ~ v1_funct_1(X0_41)
    | ~ v1_funct_1(X1_41)
    | k1_relat_1(X0_41) != k1_relat_1(X1_41)
    | X1_41 = X0_41 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_37288,plain,
    ( r2_hidden(sK0(k7_relat_1(X0_41,X0_42),X1_41),k1_relat_1(k7_relat_1(X0_41,X0_42)))
    | ~ v1_relat_1(X1_41)
    | ~ v1_relat_1(k7_relat_1(X0_41,X0_42))
    | ~ v1_funct_1(X1_41)
    | ~ v1_funct_1(k7_relat_1(X0_41,X0_42))
    | k1_relat_1(k7_relat_1(X0_41,X0_42)) != k1_relat_1(X1_41)
    | X1_41 = k7_relat_1(X0_41,X0_42) ),
    inference(instantiation,[status(thm)],[c_147])).

cnf(c_40404,plain,
    ( r2_hidden(sK0(k7_relat_1(X0_41,X0_42),k7_relat_1(X1_41,X1_42)),k1_relat_1(k7_relat_1(X0_41,X0_42)))
    | ~ v1_relat_1(k7_relat_1(X0_41,X0_42))
    | ~ v1_relat_1(k7_relat_1(X1_41,X1_42))
    | ~ v1_funct_1(k7_relat_1(X0_41,X0_42))
    | ~ v1_funct_1(k7_relat_1(X1_41,X1_42))
    | k1_relat_1(k7_relat_1(X0_41,X0_42)) != k1_relat_1(k7_relat_1(X1_41,X1_42))
    | k7_relat_1(X1_41,X1_42) = k7_relat_1(X0_41,X0_42) ),
    inference(instantiation,[status(thm)],[c_37288])).

cnf(c_41318,plain,
    ( r2_hidden(sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3)),k1_relat_1(k7_relat_1(sK2,sK3)))
    | ~ v1_relat_1(k7_relat_1(sK2,sK3))
    | ~ v1_relat_1(k7_relat_1(sK1,sK3))
    | ~ v1_funct_1(k7_relat_1(sK2,sK3))
    | ~ v1_funct_1(k7_relat_1(sK1,sK3))
    | k1_relat_1(k7_relat_1(sK2,sK3)) != k1_relat_1(k7_relat_1(sK1,sK3))
    | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_40404])).

cnf(c_41319,plain,
    ( k1_relat_1(k7_relat_1(sK2,sK3)) != k1_relat_1(k7_relat_1(sK1,sK3))
    | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3)
    | r2_hidden(sK0(k7_relat_1(sK2,sK3),k7_relat_1(sK1,sK3)),k1_relat_1(k7_relat_1(sK2,sK3))) = iProver_top
    | v1_relat_1(k7_relat_1(sK2,sK3)) != iProver_top
    | v1_relat_1(k7_relat_1(sK1,sK3)) != iProver_top
    | v1_funct_1(k7_relat_1(sK2,sK3)) != iProver_top
    | v1_funct_1(k7_relat_1(sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41318])).

cnf(c_168,plain,
    ( k1_funct_1(X0_41,X0_43) = k1_funct_1(X1_41,X1_43)
    | X0_43 != X1_43
    | X0_41 != X1_41 ),
    theory(equality)).

cnf(c_21708,plain,
    ( k1_funct_1(X0_41,X0_43) = k1_funct_1(k7_relat_1(sK2,X0_42),sK4)
    | X0_43 != sK4
    | X0_41 != k7_relat_1(sK2,X0_42) ),
    inference(instantiation,[status(thm)],[c_168])).

cnf(c_25096,plain,
    ( k1_funct_1(k7_relat_1(sK1,sK3),X0_43) = k1_funct_1(k7_relat_1(sK2,sK3),sK4)
    | X0_43 != sK4
    | k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_21708])).

cnf(c_25097,plain,
    ( k1_funct_1(k7_relat_1(sK1,sK3),sK4) = k1_funct_1(k7_relat_1(sK2,sK3),sK4)
    | sK4 != sK4
    | k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_25096])).

cnf(c_20714,plain,
    ( X0_44 != X1_44
    | X0_44 = k1_funct_1(X0_41,X0_43)
    | k1_funct_1(X0_41,X0_43) != X1_44 ),
    inference(instantiation,[status(thm)],[c_162])).

cnf(c_20750,plain,
    ( X0_44 != k1_funct_1(X0_41,X0_43)
    | X0_44 = k1_funct_1(X1_41,X1_43)
    | k1_funct_1(X1_41,X1_43) != k1_funct_1(X0_41,X0_43) ),
    inference(instantiation,[status(thm)],[c_20714])).

cnf(c_20776,plain,
    ( k1_funct_1(X0_41,X0_43) != k1_funct_1(X1_41,X1_43)
    | k1_funct_1(X2_41,X2_43) != k1_funct_1(X1_41,X1_43)
    | k1_funct_1(X0_41,X0_43) = k1_funct_1(X2_41,X2_43) ),
    inference(instantiation,[status(thm)],[c_20750])).

cnf(c_20785,plain,
    ( k1_funct_1(X0_41,X0_43) != k1_funct_1(X1_41,X1_43)
    | k1_funct_1(sK2,sK4) != k1_funct_1(X1_41,X1_43)
    | k1_funct_1(sK2,sK4) = k1_funct_1(X0_41,X0_43) ),
    inference(instantiation,[status(thm)],[c_20776])).

cnf(c_20915,plain,
    ( k1_funct_1(X0_41,X0_43) != k1_funct_1(k7_relat_1(X1_41,X0_42),X1_43)
    | k1_funct_1(sK2,sK4) = k1_funct_1(X0_41,X0_43)
    | k1_funct_1(sK2,sK4) != k1_funct_1(k7_relat_1(X1_41,X0_42),X1_43) ),
    inference(instantiation,[status(thm)],[c_20785])).

cnf(c_21005,plain,
    ( k1_funct_1(X0_41,X0_43) != k1_funct_1(k7_relat_1(sK2,X0_42),sK4)
    | k1_funct_1(sK2,sK4) = k1_funct_1(X0_41,X0_43)
    | k1_funct_1(sK2,sK4) != k1_funct_1(k7_relat_1(sK2,X0_42),sK4) ),
    inference(instantiation,[status(thm)],[c_20915])).

cnf(c_21715,plain,
    ( k1_funct_1(k7_relat_1(X0_41,X0_42),X0_43) != k1_funct_1(k7_relat_1(sK2,X1_42),sK4)
    | k1_funct_1(sK2,sK4) = k1_funct_1(k7_relat_1(X0_41,X0_42),X0_43)
    | k1_funct_1(sK2,sK4) != k1_funct_1(k7_relat_1(sK2,X1_42),sK4) ),
    inference(instantiation,[status(thm)],[c_21005])).

cnf(c_21716,plain,
    ( k1_funct_1(k7_relat_1(sK1,sK3),sK4) != k1_funct_1(k7_relat_1(sK2,sK3),sK4)
    | k1_funct_1(sK2,sK4) != k1_funct_1(k7_relat_1(sK2,sK3),sK4)
    | k1_funct_1(sK2,sK4) = k1_funct_1(k7_relat_1(sK1,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_21715])).

cnf(c_12697,plain,
    ( X0_44 != X1_44
    | X0_44 = k1_funct_1(X0_41,X0_43)
    | k1_funct_1(X0_41,X0_43) != X1_44 ),
    inference(instantiation,[status(thm)],[c_162])).

cnf(c_12782,plain,
    ( X0_44 != k1_funct_1(X0_41,X0_43)
    | X0_44 = k1_funct_1(X1_41,X1_43)
    | k1_funct_1(X1_41,X1_43) != k1_funct_1(X0_41,X0_43) ),
    inference(instantiation,[status(thm)],[c_12697])).

cnf(c_12963,plain,
    ( k1_funct_1(X0_41,X0_43) != k1_funct_1(X1_41,X1_43)
    | k1_funct_1(X2_41,X2_43) != k1_funct_1(X1_41,X1_43)
    | k1_funct_1(X0_41,X0_43) = k1_funct_1(X2_41,X2_43) ),
    inference(instantiation,[status(thm)],[c_12782])).

cnf(c_13056,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(X0_41,X0_43)
    | k1_funct_1(sK2,sK4) = k1_funct_1(sK1,sK4)
    | k1_funct_1(sK1,sK4) != k1_funct_1(X0_41,X0_43) ),
    inference(instantiation,[status(thm)],[c_12963])).

cnf(c_13359,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(k7_relat_1(X0_41,X0_42),X0_43)
    | k1_funct_1(sK2,sK4) = k1_funct_1(sK1,sK4)
    | k1_funct_1(sK1,sK4) != k1_funct_1(k7_relat_1(X0_41,X0_42),X0_43) ),
    inference(instantiation,[status(thm)],[c_13056])).

cnf(c_13360,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(k7_relat_1(sK1,sK3),sK4)
    | k1_funct_1(sK2,sK4) = k1_funct_1(sK1,sK4)
    | k1_funct_1(sK1,sK4) != k1_funct_1(k7_relat_1(sK1,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_13359])).

cnf(c_11426,plain,
    ( X0_44 != X1_44
    | k1_funct_1(sK1,sK4) != X1_44
    | k1_funct_1(sK1,sK4) = X0_44 ),
    inference(instantiation,[status(thm)],[c_162])).

cnf(c_12553,plain,
    ( X0_44 != k1_funct_1(X0_41,X0_43)
    | k1_funct_1(sK1,sK4) = X0_44
    | k1_funct_1(sK1,sK4) != k1_funct_1(X0_41,X0_43) ),
    inference(instantiation,[status(thm)],[c_11426])).

cnf(c_12694,plain,
    ( k1_funct_1(k7_relat_1(X0_41,X0_42),X0_43) != k1_funct_1(X0_41,X0_43)
    | k1_funct_1(sK1,sK4) != k1_funct_1(X0_41,X0_43)
    | k1_funct_1(sK1,sK4) = k1_funct_1(k7_relat_1(X0_41,X0_42),X0_43) ),
    inference(instantiation,[status(thm)],[c_12553])).

cnf(c_12695,plain,
    ( k1_funct_1(k7_relat_1(sK1,sK3),sK4) != k1_funct_1(sK1,sK4)
    | k1_funct_1(sK1,sK4) = k1_funct_1(k7_relat_1(sK1,sK3),sK4)
    | k1_funct_1(sK1,sK4) != k1_funct_1(sK1,sK4) ),
    inference(instantiation,[status(thm)],[c_12694])).

cnf(c_12223,plain,
    ( ~ r2_hidden(sK4,X0_42)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_funct_1(k7_relat_1(sK2,X0_42),sK4) = k1_funct_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_150])).

cnf(c_12225,plain,
    ( ~ r2_hidden(sK4,sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_funct_1(k7_relat_1(sK2,sK3),sK4) = k1_funct_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_12223])).

cnf(c_11453,plain,
    ( k1_funct_1(X0_41,X0_43) != X0_44
    | k1_funct_1(sK2,sK4) != X0_44
    | k1_funct_1(sK2,sK4) = k1_funct_1(X0_41,X0_43) ),
    inference(instantiation,[status(thm)],[c_162])).

cnf(c_12179,plain,
    ( k1_funct_1(X0_41,X0_43) != k1_funct_1(sK2,sK4)
    | k1_funct_1(sK2,sK4) = k1_funct_1(X0_41,X0_43)
    | k1_funct_1(sK2,sK4) != k1_funct_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_11453])).

cnf(c_12180,plain,
    ( k1_funct_1(X0_41,X0_43) != k1_funct_1(sK2,sK4)
    | k1_funct_1(sK2,sK4) = k1_funct_1(X0_41,X0_43) ),
    inference(equality_resolution_simp,[status(thm)],[c_12179])).

cnf(c_12209,plain,
    ( k1_funct_1(k7_relat_1(sK2,X0_42),sK4) != k1_funct_1(sK2,sK4)
    | k1_funct_1(sK2,sK4) = k1_funct_1(k7_relat_1(sK2,X0_42),sK4) ),
    inference(instantiation,[status(thm)],[c_12180])).

cnf(c_12210,plain,
    ( k1_funct_1(k7_relat_1(sK2,sK3),sK4) != k1_funct_1(sK2,sK4)
    | k1_funct_1(sK2,sK4) = k1_funct_1(k7_relat_1(sK2,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_12209])).

cnf(c_11090,plain,
    ( k1_funct_1(sK2,sK4) != X0_44
    | k1_funct_1(sK1,sK4) != X0_44
    | k1_funct_1(sK1,sK4) = k1_funct_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_162])).

cnf(c_11424,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK1,sK4)
    | k1_funct_1(sK1,sK4) = k1_funct_1(sK2,sK4)
    | k1_funct_1(sK1,sK4) != k1_funct_1(sK1,sK4) ),
    inference(instantiation,[status(thm)],[c_11090])).

cnf(c_11425,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK1,sK4)
    | k1_funct_1(sK1,sK4) = k1_funct_1(sK2,sK4) ),
    inference(equality_resolution_simp,[status(thm)],[c_11424])).

cnf(c_3555,plain,
    ( k1_relat_1(k7_relat_1(sK2,sK3)) != X0_42
    | k1_relat_1(k7_relat_1(sK2,sK3)) = k1_relat_1(k7_relat_1(sK1,sK3))
    | k1_relat_1(k7_relat_1(sK1,sK3)) != X0_42 ),
    inference(instantiation,[status(thm)],[c_161])).

cnf(c_3556,plain,
    ( k1_relat_1(k7_relat_1(sK2,sK3)) = k1_relat_1(k7_relat_1(sK1,sK3))
    | k1_relat_1(k7_relat_1(sK2,sK3)) != sK3
    | k1_relat_1(k7_relat_1(sK1,sK3)) != sK3 ),
    inference(instantiation,[status(thm)],[c_3555])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_152,plain,
    ( ~ v1_relat_1(X0_41)
    | v1_relat_1(k7_relat_1(X0_41,X0_42))
    | ~ v1_funct_1(X0_41) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_3475,plain,
    ( v1_relat_1(k7_relat_1(sK2,sK3))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_152])).

cnf(c_3476,plain,
    ( v1_relat_1(k7_relat_1(sK2,sK3)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3475])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_153,plain,
    ( ~ v1_relat_1(X0_41)
    | ~ v1_funct_1(X0_41)
    | v1_funct_1(k7_relat_1(X0_41,X0_42)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_3464,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k7_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_153])).

cnf(c_3465,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(k7_relat_1(sK2,sK3)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3464])).

cnf(c_9,negated_conjecture,
    ( r2_hidden(sK4,sK3)
    | k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_145,negated_conjecture,
    ( r2_hidden(sK4,sK3)
    | k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_8,negated_conjecture,
    ( k1_funct_1(sK1,sK4) != k1_funct_1(sK2,sK4)
    | k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_146,negated_conjecture,
    ( k1_funct_1(sK1,sK4) != k1_funct_1(sK2,sK4)
    | k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_195,plain,
    ( ~ r2_hidden(sK4,sK3)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | k1_funct_1(k7_relat_1(sK1,sK3),sK4) = k1_funct_1(sK1,sK4) ),
    inference(instantiation,[status(thm)],[c_150])).

cnf(c_188,plain,
    ( v1_relat_1(X0_41) != iProver_top
    | v1_relat_1(k7_relat_1(X0_41,X0_42)) = iProver_top
    | v1_funct_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_152])).

cnf(c_190,plain,
    ( v1_relat_1(k7_relat_1(sK1,sK3)) = iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_188])).

cnf(c_185,plain,
    ( v1_relat_1(X0_41) != iProver_top
    | v1_funct_1(X0_41) != iProver_top
    | v1_funct_1(k7_relat_1(X0_41,X0_42)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_153])).

cnf(c_187,plain,
    ( v1_relat_1(sK1) != iProver_top
    | v1_funct_1(k7_relat_1(sK1,sK3)) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_185])).

cnf(c_158,plain,
    ( X0_43 = X0_43 ),
    theory(equality)).

cnf(c_182,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_158])).

cnf(c_157,plain,
    ( X0_42 = X0_42 ),
    theory(equality)).

cnf(c_181,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_157])).

cnf(c_156,plain,
    ( X0_41 = X0_41 ),
    theory(equality)).

cnf(c_180,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_156])).

cnf(c_176,plain,
    ( k1_funct_1(sK1,sK4) = k1_funct_1(sK1,sK4)
    | sK4 != sK4
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_168])).

cnf(c_13,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_20,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_19,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_18,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_17,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_71355,c_71263,c_70044,c_58383,c_54868,c_53020,c_47300,c_45358,c_44722,c_41661,c_41319,c_25097,c_21716,c_13360,c_12695,c_12225,c_12210,c_11425,c_3556,c_3476,c_3465,c_145,c_146,c_195,c_190,c_187,c_182,c_181,c_180,c_176,c_20,c_13,c_19,c_14,c_18,c_15,c_17,c_16])).


%------------------------------------------------------------------------------
