%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0698+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:56 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 488 expanded)
%              Number of clauses        :   64 ( 122 expanded)
%              Number of leaves         :   13 ( 102 expanded)
%              Depth                    :   17
%              Number of atoms          :  424 (2160 expanded)
%              Number of equality atoms :  152 ( 386 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ! [X1] : r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( ! [X1] : r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
         => v2_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f19,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ! [X1] : r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ! [X1] : r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f34,plain,
    ( ? [X0] :
        ( ~ v2_funct_1(X0)
        & ! [X1] : r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v2_funct_1(sK5)
      & ! [X1] : r1_tarski(k10_relat_1(sK5,k9_relat_1(sK5,X1)),X1)
      & v1_funct_1(sK5)
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ~ v2_funct_1(sK5)
    & ! [X1] : r1_tarski(k10_relat_1(sK5,k9_relat_1(sK5,X1)),X1)
    & v1_funct_1(sK5)
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f34])).

fof(f55,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f57,plain,(
    ! [X1] : r1_tarski(k10_relat_1(sK5,k9_relat_1(sK5,X1)),X1) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f32])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f27,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK3(X0) != sK4(X0)
        & k1_funct_1(X0,sK3(X0)) = k1_funct_1(X0,sK4(X0))
        & r2_hidden(sK4(X0),k1_relat_1(X0))
        & r2_hidden(sK3(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK3(X0) != sK4(X0)
            & k1_funct_1(X0,sK3(X0)) = k1_funct_1(X0,sK4(X0))
            & r2_hidden(sK4(X0),k1_relat_1(X0))
            & r2_hidden(sK3(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f28,f29])).

fof(f44,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK3(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f56,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f58,plain,(
    ~ v2_funct_1(sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK4(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f46,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK3(X0)) = k1_funct_1(X0,sK4(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k2_relat_1(X1))
          | k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0 )
        & ( k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0
          | ~ r2_hidden(X0,k2_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f21])).

fof(f25,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X5)) = X5
        & r2_hidden(sK2(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1)) = X2
        & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK0(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK0(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK0(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK0(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1)
                  & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK0(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK2(X0,X5)) = X5
                    & r2_hidden(sK2(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f25,f24,f23])).

fof(f39,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f59,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f60,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f47,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | sK3(X0) != sK4(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_22,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_521,plain,
    ( k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_22])).

cnf(c_522,plain,
    ( k9_relat_1(sK5,k1_tarski(X0)) = k11_relat_1(sK5,X0) ),
    inference(unflattening,[status(thm)],[c_521])).

cnf(c_20,negated_conjecture,
    ( r1_tarski(k10_relat_1(sK5,k9_relat_1(sK5,X0)),X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1188,plain,
    ( r1_tarski(k10_relat_1(sK5,k9_relat_1(sK5,X0)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1335,plain,
    ( r1_tarski(k10_relat_1(sK5,k11_relat_1(sK5,X0)),k1_tarski(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_522,c_1188])).

cnf(c_17,plain,
    ( ~ r1_tarski(X0,k1_tarski(X1))
    | k1_tarski(X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1190,plain,
    ( k1_tarski(X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k1_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2158,plain,
    ( k10_relat_1(sK5,k11_relat_1(sK5,X0)) = k1_tarski(X0)
    | k10_relat_1(sK5,k11_relat_1(sK5,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1335,c_1190])).

cnf(c_10,plain,
    ( r2_hidden(sK3(X0),k1_relat_1(X0))
    | v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_312,plain,
    ( r2_hidden(sK3(X0),k1_relat_1(X0))
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_313,plain,
    ( r2_hidden(sK3(sK5),k1_relat_1(sK5))
    | v2_funct_1(sK5)
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_312])).

cnf(c_19,negated_conjecture,
    ( ~ v2_funct_1(sK5) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_52,plain,
    ( r2_hidden(sK3(sK5),k1_relat_1(sK5))
    | v2_funct_1(sK5)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_315,plain,
    ( r2_hidden(sK3(sK5),k1_relat_1(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_313,c_22,c_21,c_19,c_52])).

cnf(c_1187,plain,
    ( r2_hidden(sK3(sK5),k1_relat_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_315])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_392,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_21])).

cnf(c_393,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | ~ v1_relat_1(sK5)
    | k1_tarski(k1_funct_1(sK5,X0)) = k11_relat_1(sK5,X0) ),
    inference(unflattening,[status(thm)],[c_392])).

cnf(c_397,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | k1_tarski(k1_funct_1(sK5,X0)) = k11_relat_1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_393,c_22])).

cnf(c_1183,plain,
    ( k1_tarski(k1_funct_1(sK5,X0)) = k11_relat_1(sK5,X0)
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_397])).

cnf(c_1921,plain,
    ( k1_tarski(k1_funct_1(sK5,sK3(sK5))) = k11_relat_1(sK5,sK3(sK5)) ),
    inference(superposition,[status(thm)],[c_1187,c_1183])).

cnf(c_9,plain,
    ( r2_hidden(sK4(X0),k1_relat_1(X0))
    | v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_323,plain,
    ( r2_hidden(sK4(X0),k1_relat_1(X0))
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_324,plain,
    ( r2_hidden(sK4(sK5),k1_relat_1(sK5))
    | v2_funct_1(sK5)
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_323])).

cnf(c_55,plain,
    ( r2_hidden(sK4(sK5),k1_relat_1(sK5))
    | v2_funct_1(sK5)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_326,plain,
    ( r2_hidden(sK4(sK5),k1_relat_1(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_324,c_22,c_21,c_19,c_55])).

cnf(c_1186,plain,
    ( r2_hidden(sK4(sK5),k1_relat_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_326])).

cnf(c_1922,plain,
    ( k1_tarski(k1_funct_1(sK5,sK4(sK5))) = k11_relat_1(sK5,sK4(sK5)) ),
    inference(superposition,[status(thm)],[c_1186,c_1183])).

cnf(c_8,plain,
    ( v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK3(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_334,plain,
    ( v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK3(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_21])).

cnf(c_335,plain,
    ( v2_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | k1_funct_1(sK5,sK4(sK5)) = k1_funct_1(sK5,sK3(sK5)) ),
    inference(unflattening,[status(thm)],[c_334])).

cnf(c_58,plain,
    ( v2_funct_1(sK5)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | k1_funct_1(sK5,sK4(sK5)) = k1_funct_1(sK5,sK3(sK5)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_337,plain,
    ( k1_funct_1(sK5,sK4(sK5)) = k1_funct_1(sK5,sK3(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_335,c_22,c_21,c_19,c_58])).

cnf(c_1929,plain,
    ( k1_tarski(k1_funct_1(sK5,sK3(sK5))) = k11_relat_1(sK5,sK4(sK5)) ),
    inference(light_normalisation,[status(thm)],[c_1922,c_337])).

cnf(c_1932,plain,
    ( k11_relat_1(sK5,sK4(sK5)) = k11_relat_1(sK5,sK3(sK5)) ),
    inference(demodulation,[status(thm)],[c_1921,c_1929])).

cnf(c_2324,plain,
    ( r1_tarski(k10_relat_1(sK5,k11_relat_1(sK5,sK3(sK5))),k1_tarski(sK4(sK5))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1932,c_1335])).

cnf(c_2623,plain,
    ( k10_relat_1(sK5,k11_relat_1(sK5,sK3(sK5))) = k1_xboole_0
    | r1_tarski(k1_tarski(sK3(sK5)),k1_tarski(sK4(sK5))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2158,c_2324])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_527,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_528,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK5))
    | k10_relat_1(sK5,k1_tarski(X0)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_527])).

cnf(c_613,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK5))
    | k10_relat_1(sK5,k1_tarski(X0)) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_528])).

cnf(c_1178,plain,
    ( k10_relat_1(sK5,k1_tarski(X0)) != k1_xboole_0
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_613])).

cnf(c_2488,plain,
    ( k10_relat_1(sK5,k11_relat_1(sK5,sK3(sK5))) != k1_xboole_0
    | r2_hidden(k1_funct_1(sK5,sK3(sK5)),k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1921,c_1178])).

cnf(c_18,plain,
    ( ~ r1_tarski(k1_tarski(X0),k1_tarski(X1))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1311,plain,
    ( ~ r1_tarski(k1_tarski(sK3(sK5)),k1_tarski(sK4(sK5)))
    | sK4(sK5) = sK3(sK5) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1312,plain,
    ( sK4(sK5) = sK3(sK5)
    | r1_tarski(k1_tarski(sK3(sK5)),k1_tarski(sK4(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1311])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_448,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_21])).

cnf(c_449,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5))
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_453,plain,
    ( r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5))
    | ~ r2_hidden(X0,k1_relat_1(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_449,c_22])).

cnf(c_454,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) ),
    inference(renaming,[status(thm)],[c_453])).

cnf(c_1297,plain,
    ( r2_hidden(k1_funct_1(sK5,sK3(sK5)),k2_relat_1(sK5))
    | ~ r2_hidden(sK3(sK5),k1_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_454])).

cnf(c_1298,plain,
    ( r2_hidden(k1_funct_1(sK5,sK3(sK5)),k2_relat_1(sK5)) = iProver_top
    | r2_hidden(sK3(sK5),k1_relat_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1297])).

cnf(c_7,plain,
    ( v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK4(X0) != sK3(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_61,plain,
    ( v2_funct_1(sK5)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | sK4(sK5) != sK3(sK5) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_51,plain,
    ( r2_hidden(sK3(X0),k1_relat_1(X0)) = iProver_top
    | v2_funct_1(X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_53,plain,
    ( r2_hidden(sK3(sK5),k1_relat_1(sK5)) = iProver_top
    | v2_funct_1(sK5) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_51])).

cnf(c_28,plain,
    ( v2_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_24,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_23,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2623,c_2488,c_1312,c_1298,c_61,c_53,c_28,c_19,c_24,c_21,c_23,c_22])).


%------------------------------------------------------------------------------
