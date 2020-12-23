%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:33 EST 2020

% Result     : Theorem 23.26s
% Output     : CNFRefutation 23.26s
% Verified   : 
% Statistics : Number of formulae       :  215 (3480 expanded)
%              Number of clauses        :  149 (1248 expanded)
%              Number of leaves         :   20 ( 813 expanded)
%              Depth                    :   29
%              Number of atoms          :  678 (14814 expanded)
%              Number of equality atoms :  370 (6825 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK5(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK5(X0)) = X0
        & v1_funct_1(sK5(X0))
        & v1_relat_1(sK5(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK5(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK5(X0)) = X0
      & v1_funct_1(sK5(X0))
      & v1_relat_1(sK5(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f15,f34])).

fof(f56,plain,(
    ! [X0] : v1_relat_1(sK5(X0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f32,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X5)) = X5
        & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1)) = X2
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
              ( k1_funct_1(X0,X3) != sK2(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK2(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK2(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK2(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK3(X0,X1)) = sK2(X0,X1)
                  & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK2(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK4(X0,X5)) = X5
                    & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f29,f32,f31,f30])).

fof(f51,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f70,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f23])).

fof(f43,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( k1_tarski(X1) = k2_relat_1(sK6(X0,X1))
        & k1_relat_1(sK6(X0,X1)) = X0
        & v1_funct_1(sK6(X0,X1))
        & v1_relat_1(sK6(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tarski(X1) = k2_relat_1(sK6(X0,X1))
          & k1_relat_1(sK6(X0,X1)) = X0
          & v1_funct_1(sK6(X0,X1))
          & v1_relat_1(sK6(X0,X1)) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f16,f36])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK6(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK6(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f17])).

fof(f38,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ~ r1_tarski(k2_relat_1(X2),X0)
            | k1_relat_1(X2) != X1
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 != X0 ) )
   => ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),sK7)
          | k1_relat_1(X2) != sK8
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = sK8
        | k1_xboole_0 != sK7 ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK7)
        | k1_relat_1(X2) != sK8
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK8
      | k1_xboole_0 != sK7 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f18,f38])).

fof(f65,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK7)
      | k1_relat_1(X2) != sK8
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK6(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK6(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f64,plain,
    ( k1_xboole_0 = sK8
    | k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f39])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f66,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f58,plain,(
    ! [X0] : k1_relat_1(sK5(X0)) = X0 ),
    inference(cnf_transformation,[],[f35])).

fof(f57,plain,(
    ! [X0] : v1_funct_1(sK5(X0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f52,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f68,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f69,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f50,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f71,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f59,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = k1_funct_1(sK5(X0),X2)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_1697,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_75948,plain,
    ( sK4(sK5(X0),X1) != X2
    | sK0(k2_relat_1(sK5(X3)),sK7) != X2
    | sK0(k2_relat_1(sK5(X3)),sK7) = sK4(sK5(X0),X1) ),
    inference(instantiation,[status(thm)],[c_1697])).

cnf(c_75950,plain,
    ( sK4(sK5(k1_xboole_0),k1_xboole_0) != k1_xboole_0
    | sK0(k2_relat_1(sK5(k1_xboole_0)),sK7) = sK4(sK5(k1_xboole_0),k1_xboole_0)
    | sK0(k2_relat_1(sK5(k1_xboole_0)),sK7) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_75948])).

cnf(c_19,plain,
    ( v1_relat_1(sK5(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2186,plain,
    ( v1_relat_1(sK5(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2202,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,sK4(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2190,plain,
    ( k1_funct_1(X0,sK4(X0,X1)) = X1
    | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3504,plain,
    ( k1_funct_1(X0,sK4(X0,sK0(k2_relat_1(X0),X1))) = sK0(k2_relat_1(X0),X1)
    | r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2202,c_2190])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2200,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2196,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k1_tarski(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_20,plain,
    ( k2_relat_1(sK6(X0,X1)) = k1_tarski(X1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_21,plain,
    ( k1_relat_1(sK6(X0,X1)) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_24,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(X0),sK7)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) != sK8 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2183,plain,
    ( k1_relat_1(X0) != sK8
    | r1_tarski(k2_relat_1(X0),sK7) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2541,plain,
    ( sK8 != X0
    | k1_xboole_0 = X0
    | r1_tarski(k2_relat_1(sK6(X0,X1)),sK7) != iProver_top
    | v1_relat_1(sK6(X0,X1)) != iProver_top
    | v1_funct_1(sK6(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_2183])).

cnf(c_23,plain,
    ( v1_relat_1(sK6(X0,X1))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_29,plain,
    ( k1_xboole_0 = X0
    | v1_relat_1(sK6(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,plain,
    ( v1_funct_1(sK6(X0,X1))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_32,plain,
    ( k1_xboole_0 = X0
    | v1_funct_1(sK6(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2664,plain,
    ( sK8 != X0
    | k1_xboole_0 = X0
    | r1_tarski(k2_relat_1(sK6(X0,X1)),sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2541,c_29,c_32])).

cnf(c_2668,plain,
    ( sK8 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK6(sK8,X0)),sK7) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2664])).

cnf(c_2777,plain,
    ( sK8 = k1_xboole_0
    | r1_tarski(k1_tarski(X0),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_2668])).

cnf(c_2984,plain,
    ( sK8 = k1_xboole_0
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2196,c_2777])).

cnf(c_3194,plain,
    ( sK8 = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2200,c_2984])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 = sK8
    | k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_7,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_72,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_77,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2246,plain,
    ( sK7 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_1697])).

cnf(c_2247,plain,
    ( sK7 != k1_xboole_0
    | k1_xboole_0 = sK7
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2246])).

cnf(c_2353,plain,
    ( ~ r1_tarski(X0,sK8)
    | ~ r1_tarski(sK8,X0)
    | sK8 = X0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2519,plain,
    ( ~ r1_tarski(sK8,sK8)
    | sK8 = sK8 ),
    inference(instantiation,[status(thm)],[c_2353])).

cnf(c_2359,plain,
    ( X0 != X1
    | sK8 != X1
    | sK8 = X0 ),
    inference(instantiation,[status(thm)],[c_1697])).

cnf(c_2536,plain,
    ( X0 != sK8
    | sK8 = X0
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_2359])).

cnf(c_2537,plain,
    ( sK8 != sK8
    | sK8 = k1_xboole_0
    | k1_xboole_0 != sK8 ),
    inference(instantiation,[status(thm)],[c_2536])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2802,plain,
    ( r1_tarski(sK8,sK8) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3198,plain,
    ( sK8 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3194,c_25,c_72,c_77,c_2247,c_2519,c_2537,c_2802])).

cnf(c_17,plain,
    ( k1_relat_1(sK5(X0)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2325,plain,
    ( sK8 != X0
    | r1_tarski(k2_relat_1(sK5(X0)),sK7) != iProver_top
    | v1_relat_1(sK5(X0)) != iProver_top
    | v1_funct_1(sK5(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_2183])).

cnf(c_37,plain,
    ( v1_relat_1(sK5(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,plain,
    ( v1_funct_1(sK5(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_40,plain,
    ( v1_funct_1(sK5(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2330,plain,
    ( sK8 != X0
    | r1_tarski(k2_relat_1(sK5(X0)),sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2325,c_37,c_40])).

cnf(c_2336,plain,
    ( r1_tarski(k2_relat_1(sK5(sK8)),sK7) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2330])).

cnf(c_3201,plain,
    ( r1_tarski(k2_relat_1(sK5(k1_xboole_0)),sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3198,c_2336])).

cnf(c_8429,plain,
    ( k1_funct_1(sK5(k1_xboole_0),sK4(sK5(k1_xboole_0),sK0(k2_relat_1(sK5(k1_xboole_0)),sK7))) = sK0(k2_relat_1(sK5(k1_xboole_0)),sK7)
    | v1_relat_1(sK5(k1_xboole_0)) != iProver_top
    | v1_funct_1(sK5(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3504,c_3201])).

cnf(c_39,plain,
    ( v1_relat_1(sK5(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_42,plain,
    ( v1_funct_1(sK5(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_9101,plain,
    ( k1_funct_1(sK5(k1_xboole_0),sK4(sK5(k1_xboole_0),sK0(k2_relat_1(sK5(k1_xboole_0)),sK7))) = sK0(k2_relat_1(sK5(k1_xboole_0)),sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8429,c_39,c_42])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2191,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_9104,plain,
    ( r2_hidden(sK4(sK5(k1_xboole_0),sK0(k2_relat_1(sK5(k1_xboole_0)),sK7)),k1_relat_1(sK5(k1_xboole_0))) != iProver_top
    | r2_hidden(sK0(k2_relat_1(sK5(k1_xboole_0)),sK7),k2_relat_1(sK5(k1_xboole_0))) = iProver_top
    | v1_relat_1(sK5(k1_xboole_0)) != iProver_top
    | v1_funct_1(sK5(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9101,c_2191])).

cnf(c_9105,plain,
    ( r2_hidden(sK4(sK5(k1_xboole_0),sK0(k2_relat_1(sK5(k1_xboole_0)),sK7)),k1_xboole_0) != iProver_top
    | r2_hidden(sK0(k2_relat_1(sK5(k1_xboole_0)),sK7),k2_relat_1(sK5(k1_xboole_0))) = iProver_top
    | v1_relat_1(sK5(k1_xboole_0)) != iProver_top
    | v1_funct_1(sK5(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9104,c_17])).

cnf(c_2259,plain,
    ( r2_hidden(sK0(k2_relat_1(sK5(X0)),sK7),k2_relat_1(sK5(X0)))
    | r1_tarski(k2_relat_1(sK5(X0)),sK7) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2260,plain,
    ( r2_hidden(sK0(k2_relat_1(sK5(X0)),sK7),k2_relat_1(sK5(X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK5(X0)),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2259])).

cnf(c_2262,plain,
    ( r2_hidden(sK0(k2_relat_1(sK5(k1_xboole_0)),sK7),k2_relat_1(sK5(k1_xboole_0))) = iProver_top
    | r1_tarski(k2_relat_1(sK5(k1_xboole_0)),sK7) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2260])).

cnf(c_2333,plain,
    ( sK8 != k1_xboole_0
    | r1_tarski(k2_relat_1(sK5(k1_xboole_0)),sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2330])).

cnf(c_9362,plain,
    ( r2_hidden(sK0(k2_relat_1(sK5(k1_xboole_0)),sK7),k2_relat_1(sK5(k1_xboole_0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9105,c_25,c_72,c_77,c_2247,c_2262,c_2333,c_2519,c_2537,c_2802,c_3194])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK4(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2189,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK4(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2989,plain,
    ( r2_hidden(X0,k2_relat_1(sK5(X1))) != iProver_top
    | r2_hidden(sK4(sK5(X1),X0),X1) = iProver_top
    | v1_relat_1(sK5(X1)) != iProver_top
    | v1_funct_1(sK5(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_2189])).

cnf(c_2187,plain,
    ( v1_funct_1(sK5(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2198,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2195,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k1_tarski(X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2844,plain,
    ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2198,c_2195])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(sK5(X1),X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2188,plain,
    ( k1_funct_1(sK5(X0),X1) = k1_xboole_0
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2914,plain,
    ( k1_funct_1(sK5(k1_tarski(X0)),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2844,c_2188])).

cnf(c_3586,plain,
    ( r2_hidden(X0,k1_relat_1(sK5(k1_tarski(X0)))) != iProver_top
    | r2_hidden(k1_xboole_0,k2_relat_1(sK5(k1_tarski(X0)))) = iProver_top
    | v1_relat_1(sK5(k1_tarski(X0))) != iProver_top
    | v1_funct_1(sK5(k1_tarski(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2914,c_2191])).

cnf(c_3591,plain,
    ( r2_hidden(X0,k1_tarski(X0)) != iProver_top
    | r2_hidden(k1_xboole_0,k2_relat_1(sK5(k1_tarski(X0)))) = iProver_top
    | v1_relat_1(sK5(k1_tarski(X0))) != iProver_top
    | v1_funct_1(sK5(k1_tarski(X0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3586,c_17])).

cnf(c_3671,plain,
    ( r2_hidden(k1_xboole_0,k2_relat_1(sK5(k1_tarski(X0)))) = iProver_top
    | v1_relat_1(sK5(k1_tarski(X0))) != iProver_top
    | v1_funct_1(sK5(k1_tarski(X0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3591,c_2844])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2201,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3578,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK4(X1,X0),X2) = iProver_top
    | r1_tarski(k1_relat_1(X1),X2) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2189,c_2201])).

cnf(c_2197,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2199,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3139,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2197,c_2199])).

cnf(c_3370,plain,
    ( k1_tarski(X0) = k1_xboole_0
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2196,c_3139])).

cnf(c_7042,plain,
    ( k1_tarski(sK4(X0,X1)) = k1_xboole_0
    | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3578,c_3370])).

cnf(c_7108,plain,
    ( k1_tarski(sK4(sK5(k1_tarski(X0)),k1_xboole_0)) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK5(k1_tarski(X0))),k1_xboole_0) != iProver_top
    | v1_relat_1(sK5(k1_tarski(X0))) != iProver_top
    | v1_funct_1(sK5(k1_tarski(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3671,c_7042])).

cnf(c_7115,plain,
    ( k1_tarski(sK4(sK5(k1_tarski(X0)),k1_xboole_0)) = k1_xboole_0
    | r1_tarski(k1_tarski(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(sK5(k1_tarski(X0))) != iProver_top
    | v1_funct_1(sK5(k1_tarski(X0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7108,c_17])).

cnf(c_7214,plain,
    ( k1_tarski(sK4(sK5(k1_tarski(X0)),k1_xboole_0)) = k1_xboole_0
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(sK5(k1_tarski(X0))) != iProver_top
    | v1_funct_1(sK5(k1_tarski(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2196,c_7115])).

cnf(c_7219,plain,
    ( k1_tarski(sK4(sK5(k1_tarski(X0)),k1_xboole_0)) = k1_xboole_0
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | v1_funct_1(sK5(k1_tarski(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2186,c_7214])).

cnf(c_7412,plain,
    ( k1_tarski(sK4(sK5(k1_tarski(X0)),k1_xboole_0)) = k1_xboole_0
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2187,c_7219])).

cnf(c_7422,plain,
    ( k1_tarski(sK4(sK5(k1_tarski(sK4(sK5(k1_xboole_0),X0))),k1_xboole_0)) = k1_xboole_0
    | r2_hidden(X0,k2_relat_1(sK5(k1_xboole_0))) != iProver_top
    | v1_relat_1(sK5(k1_xboole_0)) != iProver_top
    | v1_funct_1(sK5(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2989,c_7412])).

cnf(c_7496,plain,
    ( k1_tarski(sK4(sK5(k1_tarski(sK4(sK5(k1_xboole_0),X0))),k1_xboole_0)) = k1_xboole_0
    | r2_hidden(X0,k2_relat_1(sK5(k1_xboole_0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7422,c_39,c_42])).

cnf(c_9380,plain,
    ( k1_tarski(sK4(sK5(k1_tarski(sK4(sK5(k1_xboole_0),sK0(k2_relat_1(sK5(k1_xboole_0)),sK7)))),k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9362,c_7496])).

cnf(c_3659,plain,
    ( k1_tarski(sK4(sK5(k1_xboole_0),X0)) = k1_xboole_0
    | r2_hidden(X0,k2_relat_1(sK5(k1_xboole_0))) != iProver_top
    | v1_relat_1(sK5(k1_xboole_0)) != iProver_top
    | v1_funct_1(sK5(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2989,c_3370])).

cnf(c_4534,plain,
    ( k1_tarski(sK4(sK5(k1_xboole_0),X0)) = k1_xboole_0
    | r2_hidden(X0,k2_relat_1(sK5(k1_xboole_0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3659,c_39,c_42])).

cnf(c_9381,plain,
    ( k1_tarski(sK4(sK5(k1_xboole_0),sK0(k2_relat_1(sK5(k1_xboole_0)),sK7))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9362,c_4534])).

cnf(c_9382,plain,
    ( k1_tarski(sK4(sK5(k1_xboole_0),k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9380,c_9381])).

cnf(c_12151,plain,
    ( r2_hidden(sK4(sK5(k1_xboole_0),k1_xboole_0),X0) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9382,c_2195])).

cnf(c_71,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_20228,plain,
    ( r2_hidden(sK4(sK5(k1_xboole_0),k1_xboole_0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12151,c_71])).

cnf(c_20247,plain,
    ( k1_funct_1(X0,sK4(X0,sK4(sK5(k1_xboole_0),k1_xboole_0))) = sK4(sK5(k1_xboole_0),k1_xboole_0)
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_20228,c_2190])).

cnf(c_50433,plain,
    ( k1_funct_1(sK5(X0),sK4(sK5(X0),sK4(sK5(k1_xboole_0),k1_xboole_0))) = sK4(sK5(k1_xboole_0),k1_xboole_0)
    | v1_funct_1(sK5(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2186,c_20247])).

cnf(c_3657,plain,
    ( k1_funct_1(sK5(X0),sK4(sK5(X0),X1)) = k1_xboole_0
    | r2_hidden(X1,k2_relat_1(sK5(X0))) != iProver_top
    | v1_relat_1(sK5(X0)) != iProver_top
    | v1_funct_1(sK5(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2989,c_2188])).

cnf(c_6472,plain,
    ( k1_funct_1(sK5(X0),sK4(sK5(X0),X1)) = k1_xboole_0
    | r2_hidden(X1,k2_relat_1(sK5(X0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3657,c_37,c_40])).

cnf(c_20248,plain,
    ( k1_funct_1(sK5(X0),sK4(sK5(X0),sK4(sK5(k1_xboole_0),k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_20228,c_6472])).

cnf(c_50435,plain,
    ( sK4(sK5(k1_xboole_0),k1_xboole_0) = k1_xboole_0
    | v1_funct_1(sK5(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_50433,c_20248])).

cnf(c_2478,plain,
    ( ~ r2_hidden(sK0(k2_relat_1(sK5(X0)),sK7),X1)
    | r2_hidden(sK0(k2_relat_1(sK5(X0)),sK7),sK7)
    | ~ r1_tarski(X1,sK7) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_13231,plain,
    ( ~ r2_hidden(sK0(k2_relat_1(sK5(X0)),sK7),sK8)
    | r2_hidden(sK0(k2_relat_1(sK5(X0)),sK7),sK7)
    | ~ r1_tarski(sK8,sK7) ),
    inference(instantiation,[status(thm)],[c_2478])).

cnf(c_13233,plain,
    ( ~ r2_hidden(sK0(k2_relat_1(sK5(k1_xboole_0)),sK7),sK8)
    | r2_hidden(sK0(k2_relat_1(sK5(k1_xboole_0)),sK7),sK7)
    | ~ r1_tarski(sK8,sK7) ),
    inference(instantiation,[status(thm)],[c_13231])).

cnf(c_2991,plain,
    ( k1_funct_1(sK5(k1_relat_1(X0)),sK4(X0,X1)) = k1_xboole_0
    | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2189,c_2188])).

cnf(c_9377,plain,
    ( k1_funct_1(sK5(k1_relat_1(sK5(k1_xboole_0))),sK4(sK5(k1_xboole_0),sK0(k2_relat_1(sK5(k1_xboole_0)),sK7))) = k1_xboole_0
    | v1_relat_1(sK5(k1_xboole_0)) != iProver_top
    | v1_funct_1(sK5(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9362,c_2991])).

cnf(c_9383,plain,
    ( sK0(k2_relat_1(sK5(k1_xboole_0)),sK7) = k1_xboole_0
    | v1_relat_1(sK5(k1_xboole_0)) != iProver_top
    | v1_funct_1(sK5(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9377,c_17,c_9101])).

cnf(c_9609,plain,
    ( sK0(k2_relat_1(sK5(k1_xboole_0)),sK7) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9383,c_39,c_42])).

cnf(c_9611,plain,
    ( r2_hidden(k1_xboole_0,k2_relat_1(sK5(k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9609,c_9362])).

cnf(c_9614,plain,
    ( r2_hidden(k1_xboole_0,k2_relat_1(sK5(k1_xboole_0))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9611])).

cnf(c_1699,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3353,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(k2_relat_1(sK5(X2)),sK7),X3)
    | X3 != X1
    | sK0(k2_relat_1(sK5(X2)),sK7) != X0 ),
    inference(instantiation,[status(thm)],[c_1699])).

cnf(c_4314,plain,
    ( ~ r2_hidden(sK4(X0,X1),k1_relat_1(X0))
    | r2_hidden(sK0(k2_relat_1(sK5(X2)),sK7),X3)
    | X3 != k1_relat_1(X0)
    | sK0(k2_relat_1(sK5(X2)),sK7) != sK4(X0,X1) ),
    inference(instantiation,[status(thm)],[c_3353])).

cnf(c_8922,plain,
    ( ~ r2_hidden(sK4(sK5(X0),X1),k1_relat_1(sK5(X0)))
    | r2_hidden(sK0(k2_relat_1(sK5(X2)),sK7),sK8)
    | sK0(k2_relat_1(sK5(X2)),sK7) != sK4(sK5(X0),X1)
    | sK8 != k1_relat_1(sK5(X0)) ),
    inference(instantiation,[status(thm)],[c_4314])).

cnf(c_8924,plain,
    ( ~ r2_hidden(sK4(sK5(k1_xboole_0),k1_xboole_0),k1_relat_1(sK5(k1_xboole_0)))
    | r2_hidden(sK0(k2_relat_1(sK5(k1_xboole_0)),sK7),sK8)
    | sK0(k2_relat_1(sK5(k1_xboole_0)),sK7) != sK4(sK5(k1_xboole_0),k1_xboole_0)
    | sK8 != k1_relat_1(sK5(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_8922])).

cnf(c_1698,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2733,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,sK7)
    | X2 != X0
    | sK7 != X1 ),
    inference(instantiation,[status(thm)],[c_1698])).

cnf(c_3415,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK8,sK7)
    | sK8 != X0
    | sK7 != X1 ),
    inference(instantiation,[status(thm)],[c_2733])).

cnf(c_8115,plain,
    ( ~ r1_tarski(X0,sK7)
    | r1_tarski(sK8,sK7)
    | sK8 != X0
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_3415])).

cnf(c_8117,plain,
    ( r1_tarski(sK8,sK7)
    | ~ r1_tarski(k1_xboole_0,sK7)
    | sK8 != k1_xboole_0
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_8115])).

cnf(c_3607,plain,
    ( r1_tarski(k1_xboole_0,sK7) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2808,plain,
    ( r1_tarski(sK7,sK7) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2488,plain,
    ( ~ r1_tarski(X0,sK7)
    | ~ r1_tarski(sK7,X0)
    | sK7 = X0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2722,plain,
    ( ~ r1_tarski(sK7,sK7)
    | sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_2488])).

cnf(c_2504,plain,
    ( ~ r1_tarski(k1_relat_1(sK5(X0)),sK8)
    | ~ r1_tarski(sK8,k1_relat_1(sK5(X0)))
    | sK8 = k1_relat_1(sK5(X0)) ),
    inference(instantiation,[status(thm)],[c_2353])).

cnf(c_2506,plain,
    ( ~ r1_tarski(k1_relat_1(sK5(k1_xboole_0)),sK8)
    | ~ r1_tarski(sK8,k1_relat_1(sK5(k1_xboole_0)))
    | sK8 = k1_relat_1(sK5(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_2504])).

cnf(c_2459,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK8,k1_relat_1(sK5(X2)))
    | k1_relat_1(sK5(X2)) != X1
    | sK8 != X0 ),
    inference(instantiation,[status(thm)],[c_1698])).

cnf(c_2461,plain,
    ( r1_tarski(sK8,k1_relat_1(sK5(k1_xboole_0)))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_relat_1(sK5(k1_xboole_0)) != k1_xboole_0
    | sK8 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2459])).

cnf(c_2348,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(sK5(X2)),sK8)
    | k1_relat_1(sK5(X2)) != X0
    | sK8 != X1 ),
    inference(instantiation,[status(thm)],[c_1698])).

cnf(c_2350,plain,
    ( r1_tarski(k1_relat_1(sK5(k1_xboole_0)),sK8)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_relat_1(sK5(k1_xboole_0)) != k1_xboole_0
    | sK8 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2348])).

cnf(c_2332,plain,
    ( ~ r1_tarski(k2_relat_1(sK5(X0)),sK7)
    | sK8 != X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2330])).

cnf(c_2334,plain,
    ( ~ r1_tarski(k2_relat_1(sK5(k1_xboole_0)),sK7)
    | sK8 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2332])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2258,plain,
    ( ~ r2_hidden(sK0(k2_relat_1(sK5(X0)),sK7),sK7)
    | r1_tarski(k2_relat_1(sK5(X0)),sK7) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2265,plain,
    ( ~ r2_hidden(sK0(k2_relat_1(sK5(k1_xboole_0)),sK7),sK7)
    | r1_tarski(k2_relat_1(sK5(k1_xboole_0)),sK7) ),
    inference(instantiation,[status(thm)],[c_2258])).

cnf(c_432,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK4(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK5(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_18])).

cnf(c_433,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK5(X1)))
    | r2_hidden(sK4(sK5(X1),X0),k1_relat_1(sK5(X1)))
    | ~ v1_relat_1(sK5(X1)) ),
    inference(unflattening,[status(thm)],[c_432])).

cnf(c_435,plain,
    ( r2_hidden(sK4(sK5(k1_xboole_0),k1_xboole_0),k1_relat_1(sK5(k1_xboole_0)))
    | ~ r2_hidden(k1_xboole_0,k2_relat_1(sK5(k1_xboole_0)))
    | ~ v1_relat_1(sK5(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_433])).

cnf(c_43,plain,
    ( k1_relat_1(sK5(k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_38,plain,
    ( v1_relat_1(sK5(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_75951,plain,
    ( sK4(sK5(k1_xboole_0),k1_xboole_0) = k1_xboole_0
    | v1_funct_1(sK5(k1_xboole_0)) != iProver_top ),
    inference(grounding,[status(thm)],[c_50435:[bind(X0,$fot(k1_xboole_0))]])).

cnf(c_75952,plain,
    ( v1_funct_1(sK5(k1_xboole_0)) = iProver_top ),
    inference(grounding,[status(thm)],[c_40:[bind(X0,$fot(k1_xboole_0))]])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_75950,c_75951,c_13233,c_9614,c_9383,c_8924,c_8117,c_3607,c_3198,c_2808,c_2722,c_2506,c_2461,c_2350,c_2334,c_2265,c_435,c_72,c_43,c_42,c_75952,c_39,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : iproveropt_run.sh %d %s
% 0.12/0.31  % Computer   : n010.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 16:17:44 EST 2020
% 0.18/0.31  % CPUTime    : 
% 0.18/0.32  % Running in FOF mode
% 23.26/3.47  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.26/3.47  
% 23.26/3.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.26/3.47  
% 23.26/3.47  ------  iProver source info
% 23.26/3.47  
% 23.26/3.47  git: date: 2020-06-30 10:37:57 +0100
% 23.26/3.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.26/3.47  git: non_committed_changes: false
% 23.26/3.47  git: last_make_outside_of_git: false
% 23.26/3.47  
% 23.26/3.47  ------ 
% 23.26/3.47  
% 23.26/3.47  ------ Input Options
% 23.26/3.47  
% 23.26/3.47  --out_options                           all
% 23.26/3.47  --tptp_safe_out                         true
% 23.26/3.47  --problem_path                          ""
% 23.26/3.47  --include_path                          ""
% 23.26/3.47  --clausifier                            res/vclausify_rel
% 23.26/3.47  --clausifier_options                    ""
% 23.26/3.47  --stdin                                 false
% 23.26/3.47  --stats_out                             all
% 23.26/3.47  
% 23.26/3.47  ------ General Options
% 23.26/3.47  
% 23.26/3.47  --fof                                   false
% 23.26/3.47  --time_out_real                         305.
% 23.26/3.47  --time_out_virtual                      -1.
% 23.26/3.47  --symbol_type_check                     false
% 23.26/3.47  --clausify_out                          false
% 23.26/3.47  --sig_cnt_out                           false
% 23.26/3.47  --trig_cnt_out                          false
% 23.26/3.47  --trig_cnt_out_tolerance                1.
% 23.26/3.47  --trig_cnt_out_sk_spl                   false
% 23.26/3.47  --abstr_cl_out                          false
% 23.26/3.47  
% 23.26/3.47  ------ Global Options
% 23.26/3.47  
% 23.26/3.47  --schedule                              default
% 23.26/3.47  --add_important_lit                     false
% 23.26/3.47  --prop_solver_per_cl                    1000
% 23.26/3.47  --min_unsat_core                        false
% 23.26/3.47  --soft_assumptions                      false
% 23.26/3.47  --soft_lemma_size                       3
% 23.26/3.47  --prop_impl_unit_size                   0
% 23.26/3.47  --prop_impl_unit                        []
% 23.26/3.47  --share_sel_clauses                     true
% 23.26/3.47  --reset_solvers                         false
% 23.26/3.47  --bc_imp_inh                            [conj_cone]
% 23.26/3.47  --conj_cone_tolerance                   3.
% 23.26/3.47  --extra_neg_conj                        none
% 23.26/3.47  --large_theory_mode                     true
% 23.26/3.47  --prolific_symb_bound                   200
% 23.26/3.47  --lt_threshold                          2000
% 23.26/3.47  --clause_weak_htbl                      true
% 23.26/3.47  --gc_record_bc_elim                     false
% 23.26/3.47  
% 23.26/3.47  ------ Preprocessing Options
% 23.26/3.47  
% 23.26/3.47  --preprocessing_flag                    true
% 23.26/3.47  --time_out_prep_mult                    0.1
% 23.26/3.47  --splitting_mode                        input
% 23.26/3.47  --splitting_grd                         true
% 23.26/3.47  --splitting_cvd                         false
% 23.26/3.47  --splitting_cvd_svl                     false
% 23.26/3.47  --splitting_nvd                         32
% 23.26/3.47  --sub_typing                            true
% 23.26/3.47  --prep_gs_sim                           true
% 23.26/3.47  --prep_unflatten                        true
% 23.26/3.47  --prep_res_sim                          true
% 23.26/3.47  --prep_upred                            true
% 23.26/3.47  --prep_sem_filter                       exhaustive
% 23.26/3.47  --prep_sem_filter_out                   false
% 23.26/3.47  --pred_elim                             true
% 23.26/3.47  --res_sim_input                         true
% 23.26/3.47  --eq_ax_congr_red                       true
% 23.26/3.47  --pure_diseq_elim                       true
% 23.26/3.47  --brand_transform                       false
% 23.26/3.47  --non_eq_to_eq                          false
% 23.26/3.47  --prep_def_merge                        true
% 23.26/3.47  --prep_def_merge_prop_impl              false
% 23.26/3.47  --prep_def_merge_mbd                    true
% 23.26/3.47  --prep_def_merge_tr_red                 false
% 23.26/3.47  --prep_def_merge_tr_cl                  false
% 23.26/3.47  --smt_preprocessing                     true
% 23.26/3.47  --smt_ac_axioms                         fast
% 23.26/3.47  --preprocessed_out                      false
% 23.26/3.47  --preprocessed_stats                    false
% 23.26/3.47  
% 23.26/3.47  ------ Abstraction refinement Options
% 23.26/3.47  
% 23.26/3.47  --abstr_ref                             []
% 23.26/3.47  --abstr_ref_prep                        false
% 23.26/3.47  --abstr_ref_until_sat                   false
% 23.26/3.47  --abstr_ref_sig_restrict                funpre
% 23.26/3.47  --abstr_ref_af_restrict_to_split_sk     false
% 23.26/3.47  --abstr_ref_under                       []
% 23.26/3.47  
% 23.26/3.47  ------ SAT Options
% 23.26/3.47  
% 23.26/3.47  --sat_mode                              false
% 23.26/3.47  --sat_fm_restart_options                ""
% 23.26/3.47  --sat_gr_def                            false
% 23.26/3.47  --sat_epr_types                         true
% 23.26/3.47  --sat_non_cyclic_types                  false
% 23.26/3.47  --sat_finite_models                     false
% 23.26/3.47  --sat_fm_lemmas                         false
% 23.26/3.47  --sat_fm_prep                           false
% 23.26/3.47  --sat_fm_uc_incr                        true
% 23.26/3.47  --sat_out_model                         small
% 23.26/3.47  --sat_out_clauses                       false
% 23.26/3.47  
% 23.26/3.47  ------ QBF Options
% 23.26/3.47  
% 23.26/3.47  --qbf_mode                              false
% 23.26/3.47  --qbf_elim_univ                         false
% 23.26/3.47  --qbf_dom_inst                          none
% 23.26/3.47  --qbf_dom_pre_inst                      false
% 23.26/3.47  --qbf_sk_in                             false
% 23.26/3.47  --qbf_pred_elim                         true
% 23.26/3.47  --qbf_split                             512
% 23.26/3.47  
% 23.26/3.47  ------ BMC1 Options
% 23.26/3.47  
% 23.26/3.47  --bmc1_incremental                      false
% 23.26/3.47  --bmc1_axioms                           reachable_all
% 23.26/3.47  --bmc1_min_bound                        0
% 23.26/3.47  --bmc1_max_bound                        -1
% 23.26/3.47  --bmc1_max_bound_default                -1
% 23.26/3.47  --bmc1_symbol_reachability              true
% 23.26/3.47  --bmc1_property_lemmas                  false
% 23.26/3.47  --bmc1_k_induction                      false
% 23.26/3.47  --bmc1_non_equiv_states                 false
% 23.26/3.47  --bmc1_deadlock                         false
% 23.26/3.47  --bmc1_ucm                              false
% 23.26/3.47  --bmc1_add_unsat_core                   none
% 23.26/3.47  --bmc1_unsat_core_children              false
% 23.26/3.47  --bmc1_unsat_core_extrapolate_axioms    false
% 23.26/3.47  --bmc1_out_stat                         full
% 23.26/3.47  --bmc1_ground_init                      false
% 23.26/3.47  --bmc1_pre_inst_next_state              false
% 23.26/3.47  --bmc1_pre_inst_state                   false
% 23.26/3.47  --bmc1_pre_inst_reach_state             false
% 23.26/3.47  --bmc1_out_unsat_core                   false
% 23.26/3.47  --bmc1_aig_witness_out                  false
% 23.26/3.47  --bmc1_verbose                          false
% 23.26/3.47  --bmc1_dump_clauses_tptp                false
% 23.26/3.47  --bmc1_dump_unsat_core_tptp             false
% 23.26/3.47  --bmc1_dump_file                        -
% 23.26/3.47  --bmc1_ucm_expand_uc_limit              128
% 23.26/3.47  --bmc1_ucm_n_expand_iterations          6
% 23.26/3.47  --bmc1_ucm_extend_mode                  1
% 23.26/3.47  --bmc1_ucm_init_mode                    2
% 23.26/3.47  --bmc1_ucm_cone_mode                    none
% 23.26/3.47  --bmc1_ucm_reduced_relation_type        0
% 23.26/3.47  --bmc1_ucm_relax_model                  4
% 23.26/3.47  --bmc1_ucm_full_tr_after_sat            true
% 23.26/3.47  --bmc1_ucm_expand_neg_assumptions       false
% 23.26/3.47  --bmc1_ucm_layered_model                none
% 23.26/3.47  --bmc1_ucm_max_lemma_size               10
% 23.26/3.47  
% 23.26/3.47  ------ AIG Options
% 23.26/3.47  
% 23.26/3.47  --aig_mode                              false
% 23.26/3.47  
% 23.26/3.47  ------ Instantiation Options
% 23.26/3.47  
% 23.26/3.47  --instantiation_flag                    true
% 23.26/3.47  --inst_sos_flag                         true
% 23.26/3.47  --inst_sos_phase                        true
% 23.26/3.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.26/3.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.26/3.47  --inst_lit_sel_side                     num_symb
% 23.26/3.47  --inst_solver_per_active                1400
% 23.26/3.47  --inst_solver_calls_frac                1.
% 23.26/3.47  --inst_passive_queue_type               priority_queues
% 23.26/3.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.26/3.47  --inst_passive_queues_freq              [25;2]
% 23.26/3.47  --inst_dismatching                      true
% 23.26/3.47  --inst_eager_unprocessed_to_passive     true
% 23.26/3.47  --inst_prop_sim_given                   true
% 23.26/3.47  --inst_prop_sim_new                     false
% 23.26/3.47  --inst_subs_new                         false
% 23.26/3.47  --inst_eq_res_simp                      false
% 23.26/3.47  --inst_subs_given                       false
% 23.26/3.47  --inst_orphan_elimination               true
% 23.26/3.47  --inst_learning_loop_flag               true
% 23.26/3.47  --inst_learning_start                   3000
% 23.26/3.47  --inst_learning_factor                  2
% 23.26/3.47  --inst_start_prop_sim_after_learn       3
% 23.26/3.47  --inst_sel_renew                        solver
% 23.26/3.47  --inst_lit_activity_flag                true
% 23.26/3.47  --inst_restr_to_given                   false
% 23.26/3.47  --inst_activity_threshold               500
% 23.26/3.47  --inst_out_proof                        true
% 23.26/3.47  
% 23.26/3.47  ------ Resolution Options
% 23.26/3.47  
% 23.26/3.47  --resolution_flag                       true
% 23.26/3.47  --res_lit_sel                           adaptive
% 23.26/3.47  --res_lit_sel_side                      none
% 23.26/3.47  --res_ordering                          kbo
% 23.26/3.47  --res_to_prop_solver                    active
% 23.26/3.47  --res_prop_simpl_new                    false
% 23.26/3.47  --res_prop_simpl_given                  true
% 23.26/3.47  --res_passive_queue_type                priority_queues
% 23.26/3.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.26/3.47  --res_passive_queues_freq               [15;5]
% 23.26/3.47  --res_forward_subs                      full
% 23.26/3.47  --res_backward_subs                     full
% 23.26/3.47  --res_forward_subs_resolution           true
% 23.26/3.47  --res_backward_subs_resolution          true
% 23.26/3.47  --res_orphan_elimination                true
% 23.26/3.47  --res_time_limit                        2.
% 23.26/3.47  --res_out_proof                         true
% 23.26/3.47  
% 23.26/3.47  ------ Superposition Options
% 23.26/3.47  
% 23.26/3.47  --superposition_flag                    true
% 23.26/3.47  --sup_passive_queue_type                priority_queues
% 23.26/3.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.26/3.47  --sup_passive_queues_freq               [8;1;4]
% 23.26/3.47  --demod_completeness_check              fast
% 23.26/3.47  --demod_use_ground                      true
% 23.26/3.47  --sup_to_prop_solver                    passive
% 23.26/3.47  --sup_prop_simpl_new                    true
% 23.26/3.47  --sup_prop_simpl_given                  true
% 23.26/3.47  --sup_fun_splitting                     true
% 23.26/3.47  --sup_smt_interval                      50000
% 23.26/3.47  
% 23.26/3.47  ------ Superposition Simplification Setup
% 23.26/3.47  
% 23.26/3.47  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.26/3.47  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.26/3.47  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.26/3.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.26/3.47  --sup_full_triv                         [TrivRules;PropSubs]
% 23.26/3.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.26/3.47  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.26/3.47  --sup_immed_triv                        [TrivRules]
% 23.26/3.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.26/3.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.26/3.47  --sup_immed_bw_main                     []
% 23.26/3.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.26/3.47  --sup_input_triv                        [Unflattening;TrivRules]
% 23.26/3.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.26/3.47  --sup_input_bw                          []
% 23.26/3.47  
% 23.26/3.47  ------ Combination Options
% 23.26/3.47  
% 23.26/3.47  --comb_res_mult                         3
% 23.26/3.47  --comb_sup_mult                         2
% 23.26/3.47  --comb_inst_mult                        10
% 23.26/3.47  
% 23.26/3.47  ------ Debug Options
% 23.26/3.47  
% 23.26/3.47  --dbg_backtrace                         false
% 23.26/3.47  --dbg_dump_prop_clauses                 false
% 23.26/3.47  --dbg_dump_prop_clauses_file            -
% 23.26/3.47  --dbg_out_stat                          false
% 23.26/3.47  ------ Parsing...
% 23.26/3.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.26/3.47  
% 23.26/3.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 23.26/3.47  
% 23.26/3.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.26/3.47  
% 23.26/3.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.26/3.47  ------ Proving...
% 23.26/3.47  ------ Problem Properties 
% 23.26/3.47  
% 23.26/3.47  
% 23.26/3.47  clauses                                 25
% 23.26/3.47  conjectures                             2
% 23.26/3.47  EPR                                     5
% 23.26/3.47  Horn                                    17
% 23.26/3.47  unary                                   5
% 23.26/3.47  binary                                  11
% 23.26/3.47  lits                                    65
% 23.26/3.47  lits eq                                 19
% 23.26/3.47  fd_pure                                 0
% 23.26/3.47  fd_pseudo                               0
% 23.26/3.47  fd_cond                                 4
% 23.26/3.47  fd_pseudo_cond                          4
% 23.26/3.47  AC symbols                              0
% 23.26/3.47  
% 23.26/3.47  ------ Schedule dynamic 5 is on 
% 23.26/3.47  
% 23.26/3.47  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.26/3.47  
% 23.26/3.47  
% 23.26/3.47  ------ 
% 23.26/3.47  Current options:
% 23.26/3.47  ------ 
% 23.26/3.47  
% 23.26/3.47  ------ Input Options
% 23.26/3.47  
% 23.26/3.47  --out_options                           all
% 23.26/3.47  --tptp_safe_out                         true
% 23.26/3.47  --problem_path                          ""
% 23.26/3.47  --include_path                          ""
% 23.26/3.47  --clausifier                            res/vclausify_rel
% 23.26/3.47  --clausifier_options                    ""
% 23.26/3.47  --stdin                                 false
% 23.26/3.47  --stats_out                             all
% 23.26/3.47  
% 23.26/3.47  ------ General Options
% 23.26/3.47  
% 23.26/3.47  --fof                                   false
% 23.26/3.47  --time_out_real                         305.
% 23.26/3.47  --time_out_virtual                      -1.
% 23.26/3.47  --symbol_type_check                     false
% 23.26/3.47  --clausify_out                          false
% 23.26/3.47  --sig_cnt_out                           false
% 23.26/3.47  --trig_cnt_out                          false
% 23.26/3.47  --trig_cnt_out_tolerance                1.
% 23.26/3.47  --trig_cnt_out_sk_spl                   false
% 23.26/3.47  --abstr_cl_out                          false
% 23.26/3.47  
% 23.26/3.47  ------ Global Options
% 23.26/3.47  
% 23.26/3.47  --schedule                              default
% 23.26/3.47  --add_important_lit                     false
% 23.26/3.47  --prop_solver_per_cl                    1000
% 23.26/3.47  --min_unsat_core                        false
% 23.26/3.47  --soft_assumptions                      false
% 23.26/3.47  --soft_lemma_size                       3
% 23.26/3.47  --prop_impl_unit_size                   0
% 23.26/3.47  --prop_impl_unit                        []
% 23.26/3.47  --share_sel_clauses                     true
% 23.26/3.47  --reset_solvers                         false
% 23.26/3.47  --bc_imp_inh                            [conj_cone]
% 23.26/3.47  --conj_cone_tolerance                   3.
% 23.26/3.47  --extra_neg_conj                        none
% 23.26/3.47  --large_theory_mode                     true
% 23.26/3.47  --prolific_symb_bound                   200
% 23.26/3.47  --lt_threshold                          2000
% 23.26/3.47  --clause_weak_htbl                      true
% 23.26/3.47  --gc_record_bc_elim                     false
% 23.26/3.47  
% 23.26/3.47  ------ Preprocessing Options
% 23.26/3.47  
% 23.26/3.47  --preprocessing_flag                    true
% 23.26/3.47  --time_out_prep_mult                    0.1
% 23.26/3.47  --splitting_mode                        input
% 23.26/3.47  --splitting_grd                         true
% 23.26/3.47  --splitting_cvd                         false
% 23.26/3.47  --splitting_cvd_svl                     false
% 23.26/3.47  --splitting_nvd                         32
% 23.26/3.47  --sub_typing                            true
% 23.26/3.47  --prep_gs_sim                           true
% 23.26/3.47  --prep_unflatten                        true
% 23.26/3.47  --prep_res_sim                          true
% 23.26/3.47  --prep_upred                            true
% 23.26/3.47  --prep_sem_filter                       exhaustive
% 23.26/3.47  --prep_sem_filter_out                   false
% 23.26/3.47  --pred_elim                             true
% 23.26/3.47  --res_sim_input                         true
% 23.26/3.47  --eq_ax_congr_red                       true
% 23.26/3.47  --pure_diseq_elim                       true
% 23.26/3.47  --brand_transform                       false
% 23.26/3.47  --non_eq_to_eq                          false
% 23.26/3.47  --prep_def_merge                        true
% 23.26/3.47  --prep_def_merge_prop_impl              false
% 23.26/3.47  --prep_def_merge_mbd                    true
% 23.26/3.47  --prep_def_merge_tr_red                 false
% 23.26/3.47  --prep_def_merge_tr_cl                  false
% 23.26/3.47  --smt_preprocessing                     true
% 23.26/3.47  --smt_ac_axioms                         fast
% 23.26/3.47  --preprocessed_out                      false
% 23.26/3.47  --preprocessed_stats                    false
% 23.26/3.47  
% 23.26/3.47  ------ Abstraction refinement Options
% 23.26/3.47  
% 23.26/3.47  --abstr_ref                             []
% 23.26/3.47  --abstr_ref_prep                        false
% 23.26/3.47  --abstr_ref_until_sat                   false
% 23.26/3.47  --abstr_ref_sig_restrict                funpre
% 23.26/3.47  --abstr_ref_af_restrict_to_split_sk     false
% 23.26/3.47  --abstr_ref_under                       []
% 23.26/3.47  
% 23.26/3.47  ------ SAT Options
% 23.26/3.47  
% 23.26/3.47  --sat_mode                              false
% 23.26/3.47  --sat_fm_restart_options                ""
% 23.26/3.47  --sat_gr_def                            false
% 23.26/3.47  --sat_epr_types                         true
% 23.26/3.47  --sat_non_cyclic_types                  false
% 23.26/3.47  --sat_finite_models                     false
% 23.26/3.47  --sat_fm_lemmas                         false
% 23.26/3.47  --sat_fm_prep                           false
% 23.26/3.47  --sat_fm_uc_incr                        true
% 23.26/3.47  --sat_out_model                         small
% 23.26/3.47  --sat_out_clauses                       false
% 23.26/3.47  
% 23.26/3.47  ------ QBF Options
% 23.26/3.47  
% 23.26/3.47  --qbf_mode                              false
% 23.26/3.47  --qbf_elim_univ                         false
% 23.26/3.47  --qbf_dom_inst                          none
% 23.26/3.47  --qbf_dom_pre_inst                      false
% 23.26/3.47  --qbf_sk_in                             false
% 23.26/3.47  --qbf_pred_elim                         true
% 23.26/3.47  --qbf_split                             512
% 23.26/3.47  
% 23.26/3.47  ------ BMC1 Options
% 23.26/3.47  
% 23.26/3.47  --bmc1_incremental                      false
% 23.26/3.47  --bmc1_axioms                           reachable_all
% 23.26/3.47  --bmc1_min_bound                        0
% 23.26/3.47  --bmc1_max_bound                        -1
% 23.26/3.47  --bmc1_max_bound_default                -1
% 23.26/3.47  --bmc1_symbol_reachability              true
% 23.26/3.47  --bmc1_property_lemmas                  false
% 23.26/3.47  --bmc1_k_induction                      false
% 23.26/3.47  --bmc1_non_equiv_states                 false
% 23.26/3.47  --bmc1_deadlock                         false
% 23.26/3.47  --bmc1_ucm                              false
% 23.26/3.47  --bmc1_add_unsat_core                   none
% 23.26/3.47  --bmc1_unsat_core_children              false
% 23.26/3.47  --bmc1_unsat_core_extrapolate_axioms    false
% 23.26/3.47  --bmc1_out_stat                         full
% 23.26/3.47  --bmc1_ground_init                      false
% 23.26/3.47  --bmc1_pre_inst_next_state              false
% 23.26/3.47  --bmc1_pre_inst_state                   false
% 23.26/3.47  --bmc1_pre_inst_reach_state             false
% 23.26/3.47  --bmc1_out_unsat_core                   false
% 23.26/3.47  --bmc1_aig_witness_out                  false
% 23.26/3.47  --bmc1_verbose                          false
% 23.26/3.47  --bmc1_dump_clauses_tptp                false
% 23.26/3.47  --bmc1_dump_unsat_core_tptp             false
% 23.26/3.47  --bmc1_dump_file                        -
% 23.26/3.47  --bmc1_ucm_expand_uc_limit              128
% 23.26/3.47  --bmc1_ucm_n_expand_iterations          6
% 23.26/3.47  --bmc1_ucm_extend_mode                  1
% 23.26/3.47  --bmc1_ucm_init_mode                    2
% 23.26/3.47  --bmc1_ucm_cone_mode                    none
% 23.26/3.47  --bmc1_ucm_reduced_relation_type        0
% 23.26/3.47  --bmc1_ucm_relax_model                  4
% 23.26/3.47  --bmc1_ucm_full_tr_after_sat            true
% 23.26/3.47  --bmc1_ucm_expand_neg_assumptions       false
% 23.26/3.47  --bmc1_ucm_layered_model                none
% 23.26/3.47  --bmc1_ucm_max_lemma_size               10
% 23.26/3.47  
% 23.26/3.47  ------ AIG Options
% 23.26/3.47  
% 23.26/3.47  --aig_mode                              false
% 23.26/3.47  
% 23.26/3.47  ------ Instantiation Options
% 23.26/3.47  
% 23.26/3.47  --instantiation_flag                    true
% 23.26/3.47  --inst_sos_flag                         true
% 23.26/3.47  --inst_sos_phase                        true
% 23.26/3.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.26/3.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.26/3.47  --inst_lit_sel_side                     none
% 23.26/3.47  --inst_solver_per_active                1400
% 23.26/3.47  --inst_solver_calls_frac                1.
% 23.26/3.47  --inst_passive_queue_type               priority_queues
% 23.26/3.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.26/3.47  --inst_passive_queues_freq              [25;2]
% 23.26/3.47  --inst_dismatching                      true
% 23.26/3.47  --inst_eager_unprocessed_to_passive     true
% 23.26/3.47  --inst_prop_sim_given                   true
% 23.26/3.47  --inst_prop_sim_new                     false
% 23.26/3.47  --inst_subs_new                         false
% 23.26/3.47  --inst_eq_res_simp                      false
% 23.26/3.47  --inst_subs_given                       false
% 23.26/3.47  --inst_orphan_elimination               true
% 23.26/3.47  --inst_learning_loop_flag               true
% 23.26/3.47  --inst_learning_start                   3000
% 23.26/3.47  --inst_learning_factor                  2
% 23.26/3.47  --inst_start_prop_sim_after_learn       3
% 23.26/3.47  --inst_sel_renew                        solver
% 23.26/3.47  --inst_lit_activity_flag                true
% 23.26/3.47  --inst_restr_to_given                   false
% 23.26/3.47  --inst_activity_threshold               500
% 23.26/3.47  --inst_out_proof                        true
% 23.26/3.47  
% 23.26/3.47  ------ Resolution Options
% 23.26/3.47  
% 23.26/3.47  --resolution_flag                       false
% 23.26/3.47  --res_lit_sel                           adaptive
% 23.26/3.47  --res_lit_sel_side                      none
% 23.26/3.47  --res_ordering                          kbo
% 23.26/3.47  --res_to_prop_solver                    active
% 23.26/3.47  --res_prop_simpl_new                    false
% 23.26/3.47  --res_prop_simpl_given                  true
% 23.26/3.47  --res_passive_queue_type                priority_queues
% 23.26/3.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.26/3.47  --res_passive_queues_freq               [15;5]
% 23.26/3.47  --res_forward_subs                      full
% 23.26/3.47  --res_backward_subs                     full
% 23.26/3.47  --res_forward_subs_resolution           true
% 23.26/3.47  --res_backward_subs_resolution          true
% 23.26/3.47  --res_orphan_elimination                true
% 23.26/3.47  --res_time_limit                        2.
% 23.26/3.47  --res_out_proof                         true
% 23.26/3.47  
% 23.26/3.47  ------ Superposition Options
% 23.26/3.47  
% 23.26/3.47  --superposition_flag                    true
% 23.26/3.47  --sup_passive_queue_type                priority_queues
% 23.26/3.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.26/3.47  --sup_passive_queues_freq               [8;1;4]
% 23.26/3.47  --demod_completeness_check              fast
% 23.26/3.47  --demod_use_ground                      true
% 23.26/3.47  --sup_to_prop_solver                    passive
% 23.26/3.47  --sup_prop_simpl_new                    true
% 23.26/3.47  --sup_prop_simpl_given                  true
% 23.26/3.47  --sup_fun_splitting                     true
% 23.26/3.47  --sup_smt_interval                      50000
% 23.26/3.47  
% 23.26/3.47  ------ Superposition Simplification Setup
% 23.26/3.47  
% 23.26/3.47  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.26/3.47  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.26/3.47  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.26/3.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.26/3.47  --sup_full_triv                         [TrivRules;PropSubs]
% 23.26/3.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.26/3.47  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.26/3.47  --sup_immed_triv                        [TrivRules]
% 23.26/3.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.26/3.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.26/3.47  --sup_immed_bw_main                     []
% 23.26/3.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.26/3.47  --sup_input_triv                        [Unflattening;TrivRules]
% 23.26/3.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.26/3.47  --sup_input_bw                          []
% 23.26/3.47  
% 23.26/3.47  ------ Combination Options
% 23.26/3.47  
% 23.26/3.47  --comb_res_mult                         3
% 23.26/3.47  --comb_sup_mult                         2
% 23.26/3.47  --comb_inst_mult                        10
% 23.26/3.47  
% 23.26/3.47  ------ Debug Options
% 23.26/3.47  
% 23.26/3.47  --dbg_backtrace                         false
% 23.26/3.47  --dbg_dump_prop_clauses                 false
% 23.26/3.47  --dbg_dump_prop_clauses_file            -
% 23.26/3.47  --dbg_out_stat                          false
% 23.26/3.47  
% 23.26/3.47  
% 23.26/3.47  
% 23.26/3.47  
% 23.26/3.47  ------ Proving...
% 23.26/3.47  
% 23.26/3.47  
% 23.26/3.47  % SZS status Theorem for theBenchmark.p
% 23.26/3.47  
% 23.26/3.47  % SZS output start CNFRefutation for theBenchmark.p
% 23.26/3.47  
% 23.26/3.47  fof(f7,axiom,(
% 23.26/3.47    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 23.26/3.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.26/3.47  
% 23.26/3.47  fof(f15,plain,(
% 23.26/3.47    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 23.26/3.47    inference(ennf_transformation,[],[f7])).
% 23.26/3.47  
% 23.26/3.47  fof(f34,plain,(
% 23.26/3.47    ! [X0] : (? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_xboole_0 = k1_funct_1(sK5(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK5(X0)) = X0 & v1_funct_1(sK5(X0)) & v1_relat_1(sK5(X0))))),
% 23.26/3.47    introduced(choice_axiom,[])).
% 23.26/3.47  
% 23.26/3.47  fof(f35,plain,(
% 23.26/3.47    ! [X0] : (! [X2] : (k1_xboole_0 = k1_funct_1(sK5(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK5(X0)) = X0 & v1_funct_1(sK5(X0)) & v1_relat_1(sK5(X0)))),
% 23.26/3.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f15,f34])).
% 23.26/3.47  
% 23.26/3.47  fof(f56,plain,(
% 23.26/3.47    ( ! [X0] : (v1_relat_1(sK5(X0))) )),
% 23.26/3.47    inference(cnf_transformation,[],[f35])).
% 23.26/3.47  
% 23.26/3.47  fof(f1,axiom,(
% 23.26/3.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 23.26/3.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.26/3.47  
% 23.26/3.47  fof(f11,plain,(
% 23.26/3.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 23.26/3.47    inference(ennf_transformation,[],[f1])).
% 23.26/3.47  
% 23.26/3.47  fof(f19,plain,(
% 23.26/3.47    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 23.26/3.47    inference(nnf_transformation,[],[f11])).
% 23.26/3.47  
% 23.26/3.47  fof(f20,plain,(
% 23.26/3.47    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 23.26/3.47    inference(rectify,[],[f19])).
% 23.26/3.47  
% 23.26/3.47  fof(f21,plain,(
% 23.26/3.47    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 23.26/3.47    introduced(choice_axiom,[])).
% 23.26/3.47  
% 23.26/3.47  fof(f22,plain,(
% 23.26/3.47    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 23.26/3.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).
% 23.26/3.47  
% 23.26/3.47  fof(f41,plain,(
% 23.26/3.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 23.26/3.47    inference(cnf_transformation,[],[f22])).
% 23.26/3.47  
% 23.26/3.47  fof(f6,axiom,(
% 23.26/3.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 23.26/3.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.26/3.47  
% 23.26/3.47  fof(f13,plain,(
% 23.26/3.47    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 23.26/3.47    inference(ennf_transformation,[],[f6])).
% 23.26/3.47  
% 23.26/3.47  fof(f14,plain,(
% 23.26/3.47    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 23.26/3.47    inference(flattening,[],[f13])).
% 23.26/3.47  
% 23.26/3.47  fof(f28,plain,(
% 23.26/3.47    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 23.26/3.47    inference(nnf_transformation,[],[f14])).
% 23.26/3.47  
% 23.26/3.47  fof(f29,plain,(
% 23.26/3.47    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 23.26/3.47    inference(rectify,[],[f28])).
% 23.26/3.47  
% 23.26/3.47  fof(f32,plain,(
% 23.26/3.47    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))))),
% 23.26/3.47    introduced(choice_axiom,[])).
% 23.26/3.47  
% 23.26/3.47  fof(f31,plain,(
% 23.26/3.47    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1)) = X2 & r2_hidden(sK3(X0,X1),k1_relat_1(X0))))) )),
% 23.26/3.47    introduced(choice_axiom,[])).
% 23.26/3.47  
% 23.26/3.47  fof(f30,plain,(
% 23.26/3.47    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK2(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1))))),
% 23.26/3.47    introduced(choice_axiom,[])).
% 23.26/3.47  
% 23.26/3.47  fof(f33,plain,(
% 23.26/3.47    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & ((k1_funct_1(X0,sK3(X0,X1)) = sK2(X0,X1) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 23.26/3.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f29,f32,f31,f30])).
% 23.26/3.47  
% 23.26/3.47  fof(f51,plain,(
% 23.26/3.47    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK4(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 23.26/3.47    inference(cnf_transformation,[],[f33])).
% 23.26/3.47  
% 23.26/3.47  fof(f70,plain,(
% 23.26/3.47    ( ! [X0,X5] : (k1_funct_1(X0,sK4(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 23.26/3.47    inference(equality_resolution,[],[f51])).
% 23.26/3.47  
% 23.26/3.47  fof(f2,axiom,(
% 23.26/3.47    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 23.26/3.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.26/3.47  
% 23.26/3.47  fof(f12,plain,(
% 23.26/3.47    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 23.26/3.47    inference(ennf_transformation,[],[f2])).
% 23.26/3.47  
% 23.26/3.47  fof(f23,plain,(
% 23.26/3.47    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 23.26/3.47    introduced(choice_axiom,[])).
% 23.26/3.47  
% 23.26/3.47  fof(f24,plain,(
% 23.26/3.47    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 23.26/3.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f23])).
% 23.26/3.47  
% 23.26/3.47  fof(f43,plain,(
% 23.26/3.47    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 23.26/3.47    inference(cnf_transformation,[],[f24])).
% 23.26/3.47  
% 23.26/3.47  fof(f5,axiom,(
% 23.26/3.47    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 23.26/3.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.26/3.47  
% 23.26/3.47  fof(f27,plain,(
% 23.26/3.47    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 23.26/3.47    inference(nnf_transformation,[],[f5])).
% 23.26/3.47  
% 23.26/3.47  fof(f49,plain,(
% 23.26/3.47    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 23.26/3.47    inference(cnf_transformation,[],[f27])).
% 23.26/3.47  
% 23.26/3.47  fof(f8,axiom,(
% 23.26/3.47    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 23.26/3.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.26/3.47  
% 23.26/3.47  fof(f16,plain,(
% 23.26/3.47    ! [X0] : (! [X1] : ? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 23.26/3.47    inference(ennf_transformation,[],[f8])).
% 23.26/3.47  
% 23.26/3.47  fof(f36,plain,(
% 23.26/3.47    ! [X1,X0] : (? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_tarski(X1) = k2_relat_1(sK6(X0,X1)) & k1_relat_1(sK6(X0,X1)) = X0 & v1_funct_1(sK6(X0,X1)) & v1_relat_1(sK6(X0,X1))))),
% 23.26/3.47    introduced(choice_axiom,[])).
% 23.26/3.47  
% 23.26/3.47  fof(f37,plain,(
% 23.26/3.47    ! [X0] : (! [X1] : (k1_tarski(X1) = k2_relat_1(sK6(X0,X1)) & k1_relat_1(sK6(X0,X1)) = X0 & v1_funct_1(sK6(X0,X1)) & v1_relat_1(sK6(X0,X1))) | k1_xboole_0 = X0)),
% 23.26/3.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f16,f36])).
% 23.26/3.47  
% 23.26/3.47  fof(f63,plain,(
% 23.26/3.47    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK6(X0,X1)) | k1_xboole_0 = X0) )),
% 23.26/3.47    inference(cnf_transformation,[],[f37])).
% 23.26/3.47  
% 23.26/3.47  fof(f62,plain,(
% 23.26/3.47    ( ! [X0,X1] : (k1_relat_1(sK6(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 23.26/3.47    inference(cnf_transformation,[],[f37])).
% 23.26/3.47  
% 23.26/3.47  fof(f9,conjecture,(
% 23.26/3.47    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 23.26/3.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.26/3.47  
% 23.26/3.47  fof(f10,negated_conjecture,(
% 23.26/3.47    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 23.26/3.47    inference(negated_conjecture,[],[f9])).
% 23.26/3.47  
% 23.26/3.47  fof(f17,plain,(
% 23.26/3.47    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 23.26/3.47    inference(ennf_transformation,[],[f10])).
% 23.26/3.47  
% 23.26/3.47  fof(f18,plain,(
% 23.26/3.47    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 23.26/3.47    inference(flattening,[],[f17])).
% 23.26/3.47  
% 23.26/3.47  fof(f38,plain,(
% 23.26/3.47    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0)) => (! [X2] : (~r1_tarski(k2_relat_1(X2),sK7) | k1_relat_1(X2) != sK8 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK8 | k1_xboole_0 != sK7))),
% 23.26/3.47    introduced(choice_axiom,[])).
% 23.26/3.47  
% 23.26/3.47  fof(f39,plain,(
% 23.26/3.47    ! [X2] : (~r1_tarski(k2_relat_1(X2),sK7) | k1_relat_1(X2) != sK8 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK8 | k1_xboole_0 != sK7)),
% 23.26/3.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f18,f38])).
% 23.26/3.47  
% 23.26/3.47  fof(f65,plain,(
% 23.26/3.47    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK7) | k1_relat_1(X2) != sK8 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 23.26/3.47    inference(cnf_transformation,[],[f39])).
% 23.26/3.47  
% 23.26/3.47  fof(f60,plain,(
% 23.26/3.47    ( ! [X0,X1] : (v1_relat_1(sK6(X0,X1)) | k1_xboole_0 = X0) )),
% 23.26/3.47    inference(cnf_transformation,[],[f37])).
% 23.26/3.47  
% 23.26/3.47  fof(f61,plain,(
% 23.26/3.47    ( ! [X0,X1] : (v1_funct_1(sK6(X0,X1)) | k1_xboole_0 = X0) )),
% 23.26/3.47    inference(cnf_transformation,[],[f37])).
% 23.26/3.47  
% 23.26/3.47  fof(f64,plain,(
% 23.26/3.47    k1_xboole_0 = sK8 | k1_xboole_0 != sK7),
% 23.26/3.47    inference(cnf_transformation,[],[f39])).
% 23.26/3.47  
% 23.26/3.47  fof(f4,axiom,(
% 23.26/3.47    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 23.26/3.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.26/3.47  
% 23.26/3.47  fof(f47,plain,(
% 23.26/3.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 23.26/3.47    inference(cnf_transformation,[],[f4])).
% 23.26/3.47  
% 23.26/3.47  fof(f3,axiom,(
% 23.26/3.47    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 23.26/3.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.26/3.47  
% 23.26/3.47  fof(f25,plain,(
% 23.26/3.47    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.26/3.47    inference(nnf_transformation,[],[f3])).
% 23.26/3.47  
% 23.26/3.47  fof(f26,plain,(
% 23.26/3.47    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.26/3.47    inference(flattening,[],[f25])).
% 23.26/3.47  
% 23.26/3.47  fof(f46,plain,(
% 23.26/3.47    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 23.26/3.47    inference(cnf_transformation,[],[f26])).
% 23.26/3.47  
% 23.26/3.47  fof(f45,plain,(
% 23.26/3.47    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 23.26/3.47    inference(cnf_transformation,[],[f26])).
% 23.26/3.47  
% 23.26/3.47  fof(f66,plain,(
% 23.26/3.47    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 23.26/3.47    inference(equality_resolution,[],[f45])).
% 23.26/3.47  
% 23.26/3.47  fof(f58,plain,(
% 23.26/3.47    ( ! [X0] : (k1_relat_1(sK5(X0)) = X0) )),
% 23.26/3.47    inference(cnf_transformation,[],[f35])).
% 23.26/3.47  
% 23.26/3.47  fof(f57,plain,(
% 23.26/3.47    ( ! [X0] : (v1_funct_1(sK5(X0))) )),
% 23.26/3.47    inference(cnf_transformation,[],[f35])).
% 23.26/3.47  
% 23.26/3.47  fof(f52,plain,(
% 23.26/3.47    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 23.26/3.47    inference(cnf_transformation,[],[f33])).
% 23.26/3.47  
% 23.26/3.47  fof(f68,plain,(
% 23.26/3.47    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 23.26/3.47    inference(equality_resolution,[],[f52])).
% 23.26/3.47  
% 23.26/3.47  fof(f69,plain,(
% 23.26/3.47    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 23.26/3.47    inference(equality_resolution,[],[f68])).
% 23.26/3.47  
% 23.26/3.47  fof(f50,plain,(
% 23.26/3.47    ( ! [X0,X5,X1] : (r2_hidden(sK4(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 23.26/3.47    inference(cnf_transformation,[],[f33])).
% 23.26/3.47  
% 23.26/3.47  fof(f71,plain,(
% 23.26/3.47    ( ! [X0,X5] : (r2_hidden(sK4(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 23.26/3.47    inference(equality_resolution,[],[f50])).
% 23.26/3.47  
% 23.26/3.47  fof(f48,plain,(
% 23.26/3.47    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 23.26/3.47    inference(cnf_transformation,[],[f27])).
% 23.26/3.47  
% 23.26/3.47  fof(f59,plain,(
% 23.26/3.47    ( ! [X2,X0] : (k1_xboole_0 = k1_funct_1(sK5(X0),X2) | ~r2_hidden(X2,X0)) )),
% 23.26/3.47    inference(cnf_transformation,[],[f35])).
% 23.26/3.47  
% 23.26/3.47  fof(f40,plain,(
% 23.26/3.47    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 23.26/3.47    inference(cnf_transformation,[],[f22])).
% 23.26/3.47  
% 23.26/3.47  fof(f42,plain,(
% 23.26/3.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 23.26/3.47    inference(cnf_transformation,[],[f22])).
% 23.26/3.47  
% 23.26/3.47  cnf(c_1697,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_75948,plain,
% 23.26/3.47      ( sK4(sK5(X0),X1) != X2
% 23.26/3.47      | sK0(k2_relat_1(sK5(X3)),sK7) != X2
% 23.26/3.47      | sK0(k2_relat_1(sK5(X3)),sK7) = sK4(sK5(X0),X1) ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_1697]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_75950,plain,
% 23.26/3.47      ( sK4(sK5(k1_xboole_0),k1_xboole_0) != k1_xboole_0
% 23.26/3.47      | sK0(k2_relat_1(sK5(k1_xboole_0)),sK7) = sK4(sK5(k1_xboole_0),k1_xboole_0)
% 23.26/3.47      | sK0(k2_relat_1(sK5(k1_xboole_0)),sK7) != k1_xboole_0 ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_75948]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_19,plain,
% 23.26/3.47      ( v1_relat_1(sK5(X0)) ),
% 23.26/3.47      inference(cnf_transformation,[],[f56]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2186,plain,
% 23.26/3.47      ( v1_relat_1(sK5(X0)) = iProver_top ),
% 23.26/3.47      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_1,plain,
% 23.26/3.47      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 23.26/3.47      inference(cnf_transformation,[],[f41]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2202,plain,
% 23.26/3.47      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 23.26/3.47      | r1_tarski(X0,X1) = iProver_top ),
% 23.26/3.47      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_14,plain,
% 23.26/3.47      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 23.26/3.47      | ~ v1_relat_1(X1)
% 23.26/3.47      | ~ v1_funct_1(X1)
% 23.26/3.47      | k1_funct_1(X1,sK4(X1,X0)) = X0 ),
% 23.26/3.47      inference(cnf_transformation,[],[f70]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2190,plain,
% 23.26/3.47      ( k1_funct_1(X0,sK4(X0,X1)) = X1
% 23.26/3.47      | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
% 23.26/3.47      | v1_relat_1(X0) != iProver_top
% 23.26/3.47      | v1_funct_1(X0) != iProver_top ),
% 23.26/3.47      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_3504,plain,
% 23.26/3.47      ( k1_funct_1(X0,sK4(X0,sK0(k2_relat_1(X0),X1))) = sK0(k2_relat_1(X0),X1)
% 23.26/3.47      | r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 23.26/3.47      | v1_relat_1(X0) != iProver_top
% 23.26/3.47      | v1_funct_1(X0) != iProver_top ),
% 23.26/3.47      inference(superposition,[status(thm)],[c_2202,c_2190]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_3,plain,
% 23.26/3.47      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 23.26/3.47      inference(cnf_transformation,[],[f43]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2200,plain,
% 23.26/3.47      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 23.26/3.47      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_8,plain,
% 23.26/3.47      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1) ),
% 23.26/3.47      inference(cnf_transformation,[],[f49]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2196,plain,
% 23.26/3.47      ( r2_hidden(X0,X1) != iProver_top
% 23.26/3.47      | r1_tarski(k1_tarski(X0),X1) = iProver_top ),
% 23.26/3.47      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_20,plain,
% 23.26/3.47      ( k2_relat_1(sK6(X0,X1)) = k1_tarski(X1) | k1_xboole_0 = X0 ),
% 23.26/3.47      inference(cnf_transformation,[],[f63]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_21,plain,
% 23.26/3.47      ( k1_relat_1(sK6(X0,X1)) = X0 | k1_xboole_0 = X0 ),
% 23.26/3.47      inference(cnf_transformation,[],[f62]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_24,negated_conjecture,
% 23.26/3.47      ( ~ r1_tarski(k2_relat_1(X0),sK7)
% 23.26/3.47      | ~ v1_relat_1(X0)
% 23.26/3.47      | ~ v1_funct_1(X0)
% 23.26/3.47      | k1_relat_1(X0) != sK8 ),
% 23.26/3.47      inference(cnf_transformation,[],[f65]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2183,plain,
% 23.26/3.47      ( k1_relat_1(X0) != sK8
% 23.26/3.47      | r1_tarski(k2_relat_1(X0),sK7) != iProver_top
% 23.26/3.47      | v1_relat_1(X0) != iProver_top
% 23.26/3.47      | v1_funct_1(X0) != iProver_top ),
% 23.26/3.47      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2541,plain,
% 23.26/3.47      ( sK8 != X0
% 23.26/3.47      | k1_xboole_0 = X0
% 23.26/3.47      | r1_tarski(k2_relat_1(sK6(X0,X1)),sK7) != iProver_top
% 23.26/3.47      | v1_relat_1(sK6(X0,X1)) != iProver_top
% 23.26/3.47      | v1_funct_1(sK6(X0,X1)) != iProver_top ),
% 23.26/3.47      inference(superposition,[status(thm)],[c_21,c_2183]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_23,plain,
% 23.26/3.47      ( v1_relat_1(sK6(X0,X1)) | k1_xboole_0 = X0 ),
% 23.26/3.47      inference(cnf_transformation,[],[f60]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_29,plain,
% 23.26/3.47      ( k1_xboole_0 = X0 | v1_relat_1(sK6(X0,X1)) = iProver_top ),
% 23.26/3.47      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_22,plain,
% 23.26/3.47      ( v1_funct_1(sK6(X0,X1)) | k1_xboole_0 = X0 ),
% 23.26/3.47      inference(cnf_transformation,[],[f61]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_32,plain,
% 23.26/3.47      ( k1_xboole_0 = X0 | v1_funct_1(sK6(X0,X1)) = iProver_top ),
% 23.26/3.47      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2664,plain,
% 23.26/3.47      ( sK8 != X0
% 23.26/3.47      | k1_xboole_0 = X0
% 23.26/3.47      | r1_tarski(k2_relat_1(sK6(X0,X1)),sK7) != iProver_top ),
% 23.26/3.47      inference(global_propositional_subsumption,
% 23.26/3.47                [status(thm)],
% 23.26/3.47                [c_2541,c_29,c_32]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2668,plain,
% 23.26/3.47      ( sK8 = k1_xboole_0
% 23.26/3.47      | r1_tarski(k2_relat_1(sK6(sK8,X0)),sK7) != iProver_top ),
% 23.26/3.47      inference(equality_resolution,[status(thm)],[c_2664]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2777,plain,
% 23.26/3.47      ( sK8 = k1_xboole_0 | r1_tarski(k1_tarski(X0),sK7) != iProver_top ),
% 23.26/3.47      inference(superposition,[status(thm)],[c_20,c_2668]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2984,plain,
% 23.26/3.47      ( sK8 = k1_xboole_0 | r2_hidden(X0,sK7) != iProver_top ),
% 23.26/3.47      inference(superposition,[status(thm)],[c_2196,c_2777]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_3194,plain,
% 23.26/3.47      ( sK8 = k1_xboole_0 | sK7 = k1_xboole_0 ),
% 23.26/3.47      inference(superposition,[status(thm)],[c_2200,c_2984]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_25,negated_conjecture,
% 23.26/3.47      ( k1_xboole_0 = sK8 | k1_xboole_0 != sK7 ),
% 23.26/3.47      inference(cnf_transformation,[],[f64]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_7,plain,
% 23.26/3.47      ( r1_tarski(k1_xboole_0,X0) ),
% 23.26/3.47      inference(cnf_transformation,[],[f47]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_72,plain,
% 23.26/3.47      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_7]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_4,plain,
% 23.26/3.47      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 23.26/3.47      inference(cnf_transformation,[],[f46]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_77,plain,
% 23.26/3.47      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 23.26/3.47      | k1_xboole_0 = k1_xboole_0 ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_4]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2246,plain,
% 23.26/3.47      ( sK7 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK7 ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_1697]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2247,plain,
% 23.26/3.47      ( sK7 != k1_xboole_0
% 23.26/3.47      | k1_xboole_0 = sK7
% 23.26/3.47      | k1_xboole_0 != k1_xboole_0 ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_2246]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2353,plain,
% 23.26/3.47      ( ~ r1_tarski(X0,sK8) | ~ r1_tarski(sK8,X0) | sK8 = X0 ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_4]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2519,plain,
% 23.26/3.47      ( ~ r1_tarski(sK8,sK8) | sK8 = sK8 ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_2353]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2359,plain,
% 23.26/3.47      ( X0 != X1 | sK8 != X1 | sK8 = X0 ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_1697]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2536,plain,
% 23.26/3.47      ( X0 != sK8 | sK8 = X0 | sK8 != sK8 ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_2359]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2537,plain,
% 23.26/3.47      ( sK8 != sK8 | sK8 = k1_xboole_0 | k1_xboole_0 != sK8 ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_2536]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_5,plain,
% 23.26/3.47      ( r1_tarski(X0,X0) ),
% 23.26/3.47      inference(cnf_transformation,[],[f66]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2802,plain,
% 23.26/3.47      ( r1_tarski(sK8,sK8) ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_5]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_3198,plain,
% 23.26/3.47      ( sK8 = k1_xboole_0 ),
% 23.26/3.47      inference(global_propositional_subsumption,
% 23.26/3.47                [status(thm)],
% 23.26/3.47                [c_3194,c_25,c_72,c_77,c_2247,c_2519,c_2537,c_2802]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_17,plain,
% 23.26/3.47      ( k1_relat_1(sK5(X0)) = X0 ),
% 23.26/3.47      inference(cnf_transformation,[],[f58]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2325,plain,
% 23.26/3.47      ( sK8 != X0
% 23.26/3.47      | r1_tarski(k2_relat_1(sK5(X0)),sK7) != iProver_top
% 23.26/3.47      | v1_relat_1(sK5(X0)) != iProver_top
% 23.26/3.47      | v1_funct_1(sK5(X0)) != iProver_top ),
% 23.26/3.47      inference(superposition,[status(thm)],[c_17,c_2183]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_37,plain,
% 23.26/3.47      ( v1_relat_1(sK5(X0)) = iProver_top ),
% 23.26/3.47      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_18,plain,
% 23.26/3.47      ( v1_funct_1(sK5(X0)) ),
% 23.26/3.47      inference(cnf_transformation,[],[f57]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_40,plain,
% 23.26/3.47      ( v1_funct_1(sK5(X0)) = iProver_top ),
% 23.26/3.47      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2330,plain,
% 23.26/3.47      ( sK8 != X0 | r1_tarski(k2_relat_1(sK5(X0)),sK7) != iProver_top ),
% 23.26/3.47      inference(global_propositional_subsumption,
% 23.26/3.47                [status(thm)],
% 23.26/3.47                [c_2325,c_37,c_40]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2336,plain,
% 23.26/3.47      ( r1_tarski(k2_relat_1(sK5(sK8)),sK7) != iProver_top ),
% 23.26/3.47      inference(equality_resolution,[status(thm)],[c_2330]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_3201,plain,
% 23.26/3.47      ( r1_tarski(k2_relat_1(sK5(k1_xboole_0)),sK7) != iProver_top ),
% 23.26/3.47      inference(demodulation,[status(thm)],[c_3198,c_2336]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_8429,plain,
% 23.26/3.47      ( k1_funct_1(sK5(k1_xboole_0),sK4(sK5(k1_xboole_0),sK0(k2_relat_1(sK5(k1_xboole_0)),sK7))) = sK0(k2_relat_1(sK5(k1_xboole_0)),sK7)
% 23.26/3.47      | v1_relat_1(sK5(k1_xboole_0)) != iProver_top
% 23.26/3.47      | v1_funct_1(sK5(k1_xboole_0)) != iProver_top ),
% 23.26/3.47      inference(superposition,[status(thm)],[c_3504,c_3201]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_39,plain,
% 23.26/3.47      ( v1_relat_1(sK5(k1_xboole_0)) = iProver_top ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_37]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_42,plain,
% 23.26/3.47      ( v1_funct_1(sK5(k1_xboole_0)) = iProver_top ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_40]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_9101,plain,
% 23.26/3.47      ( k1_funct_1(sK5(k1_xboole_0),sK4(sK5(k1_xboole_0),sK0(k2_relat_1(sK5(k1_xboole_0)),sK7))) = sK0(k2_relat_1(sK5(k1_xboole_0)),sK7) ),
% 23.26/3.47      inference(global_propositional_subsumption,
% 23.26/3.47                [status(thm)],
% 23.26/3.47                [c_8429,c_39,c_42]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_13,plain,
% 23.26/3.47      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 23.26/3.47      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 23.26/3.47      | ~ v1_relat_1(X1)
% 23.26/3.47      | ~ v1_funct_1(X1) ),
% 23.26/3.47      inference(cnf_transformation,[],[f69]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2191,plain,
% 23.26/3.47      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 23.26/3.47      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 23.26/3.47      | v1_relat_1(X1) != iProver_top
% 23.26/3.47      | v1_funct_1(X1) != iProver_top ),
% 23.26/3.47      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_9104,plain,
% 23.26/3.47      ( r2_hidden(sK4(sK5(k1_xboole_0),sK0(k2_relat_1(sK5(k1_xboole_0)),sK7)),k1_relat_1(sK5(k1_xboole_0))) != iProver_top
% 23.26/3.47      | r2_hidden(sK0(k2_relat_1(sK5(k1_xboole_0)),sK7),k2_relat_1(sK5(k1_xboole_0))) = iProver_top
% 23.26/3.47      | v1_relat_1(sK5(k1_xboole_0)) != iProver_top
% 23.26/3.47      | v1_funct_1(sK5(k1_xboole_0)) != iProver_top ),
% 23.26/3.47      inference(superposition,[status(thm)],[c_9101,c_2191]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_9105,plain,
% 23.26/3.47      ( r2_hidden(sK4(sK5(k1_xboole_0),sK0(k2_relat_1(sK5(k1_xboole_0)),sK7)),k1_xboole_0) != iProver_top
% 23.26/3.47      | r2_hidden(sK0(k2_relat_1(sK5(k1_xboole_0)),sK7),k2_relat_1(sK5(k1_xboole_0))) = iProver_top
% 23.26/3.47      | v1_relat_1(sK5(k1_xboole_0)) != iProver_top
% 23.26/3.47      | v1_funct_1(sK5(k1_xboole_0)) != iProver_top ),
% 23.26/3.47      inference(demodulation,[status(thm)],[c_9104,c_17]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2259,plain,
% 23.26/3.47      ( r2_hidden(sK0(k2_relat_1(sK5(X0)),sK7),k2_relat_1(sK5(X0)))
% 23.26/3.47      | r1_tarski(k2_relat_1(sK5(X0)),sK7) ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_1]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2260,plain,
% 23.26/3.47      ( r2_hidden(sK0(k2_relat_1(sK5(X0)),sK7),k2_relat_1(sK5(X0))) = iProver_top
% 23.26/3.47      | r1_tarski(k2_relat_1(sK5(X0)),sK7) = iProver_top ),
% 23.26/3.47      inference(predicate_to_equality,[status(thm)],[c_2259]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2262,plain,
% 23.26/3.47      ( r2_hidden(sK0(k2_relat_1(sK5(k1_xboole_0)),sK7),k2_relat_1(sK5(k1_xboole_0))) = iProver_top
% 23.26/3.47      | r1_tarski(k2_relat_1(sK5(k1_xboole_0)),sK7) = iProver_top ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_2260]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2333,plain,
% 23.26/3.47      ( sK8 != k1_xboole_0
% 23.26/3.47      | r1_tarski(k2_relat_1(sK5(k1_xboole_0)),sK7) != iProver_top ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_2330]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_9362,plain,
% 23.26/3.47      ( r2_hidden(sK0(k2_relat_1(sK5(k1_xboole_0)),sK7),k2_relat_1(sK5(k1_xboole_0))) = iProver_top ),
% 23.26/3.47      inference(global_propositional_subsumption,
% 23.26/3.47                [status(thm)],
% 23.26/3.47                [c_9105,c_25,c_72,c_77,c_2247,c_2262,c_2333,c_2519,
% 23.26/3.47                 c_2537,c_2802,c_3194]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_15,plain,
% 23.26/3.47      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 23.26/3.47      | r2_hidden(sK4(X1,X0),k1_relat_1(X1))
% 23.26/3.47      | ~ v1_relat_1(X1)
% 23.26/3.47      | ~ v1_funct_1(X1) ),
% 23.26/3.47      inference(cnf_transformation,[],[f71]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2189,plain,
% 23.26/3.47      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 23.26/3.47      | r2_hidden(sK4(X1,X0),k1_relat_1(X1)) = iProver_top
% 23.26/3.47      | v1_relat_1(X1) != iProver_top
% 23.26/3.47      | v1_funct_1(X1) != iProver_top ),
% 23.26/3.47      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2989,plain,
% 23.26/3.47      ( r2_hidden(X0,k2_relat_1(sK5(X1))) != iProver_top
% 23.26/3.47      | r2_hidden(sK4(sK5(X1),X0),X1) = iProver_top
% 23.26/3.47      | v1_relat_1(sK5(X1)) != iProver_top
% 23.26/3.47      | v1_funct_1(sK5(X1)) != iProver_top ),
% 23.26/3.47      inference(superposition,[status(thm)],[c_17,c_2189]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2187,plain,
% 23.26/3.47      ( v1_funct_1(sK5(X0)) = iProver_top ),
% 23.26/3.47      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2198,plain,
% 23.26/3.47      ( r1_tarski(X0,X0) = iProver_top ),
% 23.26/3.47      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_9,plain,
% 23.26/3.47      ( r2_hidden(X0,X1) | ~ r1_tarski(k1_tarski(X0),X1) ),
% 23.26/3.47      inference(cnf_transformation,[],[f48]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2195,plain,
% 23.26/3.47      ( r2_hidden(X0,X1) = iProver_top
% 23.26/3.47      | r1_tarski(k1_tarski(X0),X1) != iProver_top ),
% 23.26/3.47      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2844,plain,
% 23.26/3.47      ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
% 23.26/3.47      inference(superposition,[status(thm)],[c_2198,c_2195]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_16,plain,
% 23.26/3.47      ( ~ r2_hidden(X0,X1) | k1_funct_1(sK5(X1),X0) = k1_xboole_0 ),
% 23.26/3.47      inference(cnf_transformation,[],[f59]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2188,plain,
% 23.26/3.47      ( k1_funct_1(sK5(X0),X1) = k1_xboole_0
% 23.26/3.47      | r2_hidden(X1,X0) != iProver_top ),
% 23.26/3.47      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2914,plain,
% 23.26/3.47      ( k1_funct_1(sK5(k1_tarski(X0)),X0) = k1_xboole_0 ),
% 23.26/3.47      inference(superposition,[status(thm)],[c_2844,c_2188]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_3586,plain,
% 23.26/3.47      ( r2_hidden(X0,k1_relat_1(sK5(k1_tarski(X0)))) != iProver_top
% 23.26/3.47      | r2_hidden(k1_xboole_0,k2_relat_1(sK5(k1_tarski(X0)))) = iProver_top
% 23.26/3.47      | v1_relat_1(sK5(k1_tarski(X0))) != iProver_top
% 23.26/3.47      | v1_funct_1(sK5(k1_tarski(X0))) != iProver_top ),
% 23.26/3.47      inference(superposition,[status(thm)],[c_2914,c_2191]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_3591,plain,
% 23.26/3.47      ( r2_hidden(X0,k1_tarski(X0)) != iProver_top
% 23.26/3.47      | r2_hidden(k1_xboole_0,k2_relat_1(sK5(k1_tarski(X0)))) = iProver_top
% 23.26/3.47      | v1_relat_1(sK5(k1_tarski(X0))) != iProver_top
% 23.26/3.47      | v1_funct_1(sK5(k1_tarski(X0))) != iProver_top ),
% 23.26/3.47      inference(demodulation,[status(thm)],[c_3586,c_17]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_3671,plain,
% 23.26/3.47      ( r2_hidden(k1_xboole_0,k2_relat_1(sK5(k1_tarski(X0)))) = iProver_top
% 23.26/3.47      | v1_relat_1(sK5(k1_tarski(X0))) != iProver_top
% 23.26/3.47      | v1_funct_1(sK5(k1_tarski(X0))) != iProver_top ),
% 23.26/3.47      inference(global_propositional_subsumption,
% 23.26/3.47                [status(thm)],
% 23.26/3.47                [c_3591,c_2844]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2,plain,
% 23.26/3.47      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 23.26/3.47      inference(cnf_transformation,[],[f40]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2201,plain,
% 23.26/3.47      ( r2_hidden(X0,X1) != iProver_top
% 23.26/3.47      | r2_hidden(X0,X2) = iProver_top
% 23.26/3.47      | r1_tarski(X1,X2) != iProver_top ),
% 23.26/3.47      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_3578,plain,
% 23.26/3.47      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 23.26/3.47      | r2_hidden(sK4(X1,X0),X2) = iProver_top
% 23.26/3.47      | r1_tarski(k1_relat_1(X1),X2) != iProver_top
% 23.26/3.47      | v1_relat_1(X1) != iProver_top
% 23.26/3.47      | v1_funct_1(X1) != iProver_top ),
% 23.26/3.47      inference(superposition,[status(thm)],[c_2189,c_2201]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2197,plain,
% 23.26/3.47      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 23.26/3.47      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2199,plain,
% 23.26/3.47      ( X0 = X1
% 23.26/3.47      | r1_tarski(X1,X0) != iProver_top
% 23.26/3.47      | r1_tarski(X0,X1) != iProver_top ),
% 23.26/3.47      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_3139,plain,
% 23.26/3.47      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 23.26/3.47      inference(superposition,[status(thm)],[c_2197,c_2199]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_3370,plain,
% 23.26/3.47      ( k1_tarski(X0) = k1_xboole_0
% 23.26/3.47      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 23.26/3.47      inference(superposition,[status(thm)],[c_2196,c_3139]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_7042,plain,
% 23.26/3.47      ( k1_tarski(sK4(X0,X1)) = k1_xboole_0
% 23.26/3.47      | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
% 23.26/3.47      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 23.26/3.47      | v1_relat_1(X0) != iProver_top
% 23.26/3.47      | v1_funct_1(X0) != iProver_top ),
% 23.26/3.47      inference(superposition,[status(thm)],[c_3578,c_3370]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_7108,plain,
% 23.26/3.47      ( k1_tarski(sK4(sK5(k1_tarski(X0)),k1_xboole_0)) = k1_xboole_0
% 23.26/3.47      | r1_tarski(k1_relat_1(sK5(k1_tarski(X0))),k1_xboole_0) != iProver_top
% 23.26/3.47      | v1_relat_1(sK5(k1_tarski(X0))) != iProver_top
% 23.26/3.47      | v1_funct_1(sK5(k1_tarski(X0))) != iProver_top ),
% 23.26/3.47      inference(superposition,[status(thm)],[c_3671,c_7042]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_7115,plain,
% 23.26/3.47      ( k1_tarski(sK4(sK5(k1_tarski(X0)),k1_xboole_0)) = k1_xboole_0
% 23.26/3.47      | r1_tarski(k1_tarski(X0),k1_xboole_0) != iProver_top
% 23.26/3.47      | v1_relat_1(sK5(k1_tarski(X0))) != iProver_top
% 23.26/3.47      | v1_funct_1(sK5(k1_tarski(X0))) != iProver_top ),
% 23.26/3.47      inference(demodulation,[status(thm)],[c_7108,c_17]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_7214,plain,
% 23.26/3.47      ( k1_tarski(sK4(sK5(k1_tarski(X0)),k1_xboole_0)) = k1_xboole_0
% 23.26/3.47      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 23.26/3.47      | v1_relat_1(sK5(k1_tarski(X0))) != iProver_top
% 23.26/3.47      | v1_funct_1(sK5(k1_tarski(X0))) != iProver_top ),
% 23.26/3.47      inference(superposition,[status(thm)],[c_2196,c_7115]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_7219,plain,
% 23.26/3.47      ( k1_tarski(sK4(sK5(k1_tarski(X0)),k1_xboole_0)) = k1_xboole_0
% 23.26/3.47      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 23.26/3.47      | v1_funct_1(sK5(k1_tarski(X0))) != iProver_top ),
% 23.26/3.47      inference(superposition,[status(thm)],[c_2186,c_7214]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_7412,plain,
% 23.26/3.47      ( k1_tarski(sK4(sK5(k1_tarski(X0)),k1_xboole_0)) = k1_xboole_0
% 23.26/3.47      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 23.26/3.47      inference(superposition,[status(thm)],[c_2187,c_7219]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_7422,plain,
% 23.26/3.47      ( k1_tarski(sK4(sK5(k1_tarski(sK4(sK5(k1_xboole_0),X0))),k1_xboole_0)) = k1_xboole_0
% 23.26/3.47      | r2_hidden(X0,k2_relat_1(sK5(k1_xboole_0))) != iProver_top
% 23.26/3.47      | v1_relat_1(sK5(k1_xboole_0)) != iProver_top
% 23.26/3.47      | v1_funct_1(sK5(k1_xboole_0)) != iProver_top ),
% 23.26/3.47      inference(superposition,[status(thm)],[c_2989,c_7412]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_7496,plain,
% 23.26/3.47      ( k1_tarski(sK4(sK5(k1_tarski(sK4(sK5(k1_xboole_0),X0))),k1_xboole_0)) = k1_xboole_0
% 23.26/3.47      | r2_hidden(X0,k2_relat_1(sK5(k1_xboole_0))) != iProver_top ),
% 23.26/3.47      inference(global_propositional_subsumption,
% 23.26/3.47                [status(thm)],
% 23.26/3.47                [c_7422,c_39,c_42]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_9380,plain,
% 23.26/3.47      ( k1_tarski(sK4(sK5(k1_tarski(sK4(sK5(k1_xboole_0),sK0(k2_relat_1(sK5(k1_xboole_0)),sK7)))),k1_xboole_0)) = k1_xboole_0 ),
% 23.26/3.47      inference(superposition,[status(thm)],[c_9362,c_7496]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_3659,plain,
% 23.26/3.47      ( k1_tarski(sK4(sK5(k1_xboole_0),X0)) = k1_xboole_0
% 23.26/3.47      | r2_hidden(X0,k2_relat_1(sK5(k1_xboole_0))) != iProver_top
% 23.26/3.47      | v1_relat_1(sK5(k1_xboole_0)) != iProver_top
% 23.26/3.47      | v1_funct_1(sK5(k1_xboole_0)) != iProver_top ),
% 23.26/3.47      inference(superposition,[status(thm)],[c_2989,c_3370]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_4534,plain,
% 23.26/3.47      ( k1_tarski(sK4(sK5(k1_xboole_0),X0)) = k1_xboole_0
% 23.26/3.47      | r2_hidden(X0,k2_relat_1(sK5(k1_xboole_0))) != iProver_top ),
% 23.26/3.47      inference(global_propositional_subsumption,
% 23.26/3.47                [status(thm)],
% 23.26/3.47                [c_3659,c_39,c_42]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_9381,plain,
% 23.26/3.47      ( k1_tarski(sK4(sK5(k1_xboole_0),sK0(k2_relat_1(sK5(k1_xboole_0)),sK7))) = k1_xboole_0 ),
% 23.26/3.47      inference(superposition,[status(thm)],[c_9362,c_4534]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_9382,plain,
% 23.26/3.47      ( k1_tarski(sK4(sK5(k1_xboole_0),k1_xboole_0)) = k1_xboole_0 ),
% 23.26/3.47      inference(demodulation,[status(thm)],[c_9380,c_9381]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_12151,plain,
% 23.26/3.47      ( r2_hidden(sK4(sK5(k1_xboole_0),k1_xboole_0),X0) = iProver_top
% 23.26/3.47      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 23.26/3.47      inference(superposition,[status(thm)],[c_9382,c_2195]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_71,plain,
% 23.26/3.47      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 23.26/3.47      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_20228,plain,
% 23.26/3.47      ( r2_hidden(sK4(sK5(k1_xboole_0),k1_xboole_0),X0) = iProver_top ),
% 23.26/3.47      inference(global_propositional_subsumption,
% 23.26/3.47                [status(thm)],
% 23.26/3.47                [c_12151,c_71]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_20247,plain,
% 23.26/3.47      ( k1_funct_1(X0,sK4(X0,sK4(sK5(k1_xboole_0),k1_xboole_0))) = sK4(sK5(k1_xboole_0),k1_xboole_0)
% 23.26/3.47      | v1_relat_1(X0) != iProver_top
% 23.26/3.47      | v1_funct_1(X0) != iProver_top ),
% 23.26/3.47      inference(superposition,[status(thm)],[c_20228,c_2190]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_50433,plain,
% 23.26/3.47      ( k1_funct_1(sK5(X0),sK4(sK5(X0),sK4(sK5(k1_xboole_0),k1_xboole_0))) = sK4(sK5(k1_xboole_0),k1_xboole_0)
% 23.26/3.47      | v1_funct_1(sK5(X0)) != iProver_top ),
% 23.26/3.47      inference(superposition,[status(thm)],[c_2186,c_20247]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_3657,plain,
% 23.26/3.47      ( k1_funct_1(sK5(X0),sK4(sK5(X0),X1)) = k1_xboole_0
% 23.26/3.47      | r2_hidden(X1,k2_relat_1(sK5(X0))) != iProver_top
% 23.26/3.47      | v1_relat_1(sK5(X0)) != iProver_top
% 23.26/3.47      | v1_funct_1(sK5(X0)) != iProver_top ),
% 23.26/3.47      inference(superposition,[status(thm)],[c_2989,c_2188]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_6472,plain,
% 23.26/3.47      ( k1_funct_1(sK5(X0),sK4(sK5(X0),X1)) = k1_xboole_0
% 23.26/3.47      | r2_hidden(X1,k2_relat_1(sK5(X0))) != iProver_top ),
% 23.26/3.47      inference(global_propositional_subsumption,
% 23.26/3.47                [status(thm)],
% 23.26/3.47                [c_3657,c_37,c_40]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_20248,plain,
% 23.26/3.47      ( k1_funct_1(sK5(X0),sK4(sK5(X0),sK4(sK5(k1_xboole_0),k1_xboole_0))) = k1_xboole_0 ),
% 23.26/3.47      inference(superposition,[status(thm)],[c_20228,c_6472]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_50435,plain,
% 23.26/3.47      ( sK4(sK5(k1_xboole_0),k1_xboole_0) = k1_xboole_0
% 23.26/3.47      | v1_funct_1(sK5(X0)) != iProver_top ),
% 23.26/3.47      inference(light_normalisation,[status(thm)],[c_50433,c_20248]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2478,plain,
% 23.26/3.47      ( ~ r2_hidden(sK0(k2_relat_1(sK5(X0)),sK7),X1)
% 23.26/3.47      | r2_hidden(sK0(k2_relat_1(sK5(X0)),sK7),sK7)
% 23.26/3.47      | ~ r1_tarski(X1,sK7) ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_2]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_13231,plain,
% 23.26/3.47      ( ~ r2_hidden(sK0(k2_relat_1(sK5(X0)),sK7),sK8)
% 23.26/3.47      | r2_hidden(sK0(k2_relat_1(sK5(X0)),sK7),sK7)
% 23.26/3.47      | ~ r1_tarski(sK8,sK7) ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_2478]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_13233,plain,
% 23.26/3.47      ( ~ r2_hidden(sK0(k2_relat_1(sK5(k1_xboole_0)),sK7),sK8)
% 23.26/3.47      | r2_hidden(sK0(k2_relat_1(sK5(k1_xboole_0)),sK7),sK7)
% 23.26/3.47      | ~ r1_tarski(sK8,sK7) ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_13231]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2991,plain,
% 23.26/3.47      ( k1_funct_1(sK5(k1_relat_1(X0)),sK4(X0,X1)) = k1_xboole_0
% 23.26/3.47      | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
% 23.26/3.47      | v1_relat_1(X0) != iProver_top
% 23.26/3.47      | v1_funct_1(X0) != iProver_top ),
% 23.26/3.47      inference(superposition,[status(thm)],[c_2189,c_2188]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_9377,plain,
% 23.26/3.47      ( k1_funct_1(sK5(k1_relat_1(sK5(k1_xboole_0))),sK4(sK5(k1_xboole_0),sK0(k2_relat_1(sK5(k1_xboole_0)),sK7))) = k1_xboole_0
% 23.26/3.47      | v1_relat_1(sK5(k1_xboole_0)) != iProver_top
% 23.26/3.47      | v1_funct_1(sK5(k1_xboole_0)) != iProver_top ),
% 23.26/3.47      inference(superposition,[status(thm)],[c_9362,c_2991]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_9383,plain,
% 23.26/3.47      ( sK0(k2_relat_1(sK5(k1_xboole_0)),sK7) = k1_xboole_0
% 23.26/3.47      | v1_relat_1(sK5(k1_xboole_0)) != iProver_top
% 23.26/3.47      | v1_funct_1(sK5(k1_xboole_0)) != iProver_top ),
% 23.26/3.47      inference(demodulation,[status(thm)],[c_9377,c_17,c_9101]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_9609,plain,
% 23.26/3.47      ( sK0(k2_relat_1(sK5(k1_xboole_0)),sK7) = k1_xboole_0 ),
% 23.26/3.47      inference(global_propositional_subsumption,
% 23.26/3.47                [status(thm)],
% 23.26/3.47                [c_9383,c_39,c_42]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_9611,plain,
% 23.26/3.47      ( r2_hidden(k1_xboole_0,k2_relat_1(sK5(k1_xboole_0))) = iProver_top ),
% 23.26/3.47      inference(demodulation,[status(thm)],[c_9609,c_9362]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_9614,plain,
% 23.26/3.47      ( r2_hidden(k1_xboole_0,k2_relat_1(sK5(k1_xboole_0))) ),
% 23.26/3.47      inference(predicate_to_equality_rev,[status(thm)],[c_9611]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_1699,plain,
% 23.26/3.47      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.26/3.47      theory(equality) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_3353,plain,
% 23.26/3.47      ( ~ r2_hidden(X0,X1)
% 23.26/3.47      | r2_hidden(sK0(k2_relat_1(sK5(X2)),sK7),X3)
% 23.26/3.47      | X3 != X1
% 23.26/3.47      | sK0(k2_relat_1(sK5(X2)),sK7) != X0 ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_1699]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_4314,plain,
% 23.26/3.47      ( ~ r2_hidden(sK4(X0,X1),k1_relat_1(X0))
% 23.26/3.47      | r2_hidden(sK0(k2_relat_1(sK5(X2)),sK7),X3)
% 23.26/3.47      | X3 != k1_relat_1(X0)
% 23.26/3.47      | sK0(k2_relat_1(sK5(X2)),sK7) != sK4(X0,X1) ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_3353]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_8922,plain,
% 23.26/3.47      ( ~ r2_hidden(sK4(sK5(X0),X1),k1_relat_1(sK5(X0)))
% 23.26/3.47      | r2_hidden(sK0(k2_relat_1(sK5(X2)),sK7),sK8)
% 23.26/3.47      | sK0(k2_relat_1(sK5(X2)),sK7) != sK4(sK5(X0),X1)
% 23.26/3.47      | sK8 != k1_relat_1(sK5(X0)) ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_4314]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_8924,plain,
% 23.26/3.47      ( ~ r2_hidden(sK4(sK5(k1_xboole_0),k1_xboole_0),k1_relat_1(sK5(k1_xboole_0)))
% 23.26/3.47      | r2_hidden(sK0(k2_relat_1(sK5(k1_xboole_0)),sK7),sK8)
% 23.26/3.47      | sK0(k2_relat_1(sK5(k1_xboole_0)),sK7) != sK4(sK5(k1_xboole_0),k1_xboole_0)
% 23.26/3.47      | sK8 != k1_relat_1(sK5(k1_xboole_0)) ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_8922]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_1698,plain,
% 23.26/3.47      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.26/3.47      theory(equality) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2733,plain,
% 23.26/3.47      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,sK7) | X2 != X0 | sK7 != X1 ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_1698]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_3415,plain,
% 23.26/3.47      ( ~ r1_tarski(X0,X1) | r1_tarski(sK8,sK7) | sK8 != X0 | sK7 != X1 ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_2733]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_8115,plain,
% 23.26/3.47      ( ~ r1_tarski(X0,sK7)
% 23.26/3.47      | r1_tarski(sK8,sK7)
% 23.26/3.47      | sK8 != X0
% 23.26/3.47      | sK7 != sK7 ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_3415]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_8117,plain,
% 23.26/3.47      ( r1_tarski(sK8,sK7)
% 23.26/3.47      | ~ r1_tarski(k1_xboole_0,sK7)
% 23.26/3.47      | sK8 != k1_xboole_0
% 23.26/3.47      | sK7 != sK7 ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_8115]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_3607,plain,
% 23.26/3.47      ( r1_tarski(k1_xboole_0,sK7) ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_7]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2808,plain,
% 23.26/3.47      ( r1_tarski(sK7,sK7) ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_5]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2488,plain,
% 23.26/3.47      ( ~ r1_tarski(X0,sK7) | ~ r1_tarski(sK7,X0) | sK7 = X0 ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_4]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2722,plain,
% 23.26/3.47      ( ~ r1_tarski(sK7,sK7) | sK7 = sK7 ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_2488]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2504,plain,
% 23.26/3.47      ( ~ r1_tarski(k1_relat_1(sK5(X0)),sK8)
% 23.26/3.47      | ~ r1_tarski(sK8,k1_relat_1(sK5(X0)))
% 23.26/3.47      | sK8 = k1_relat_1(sK5(X0)) ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_2353]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2506,plain,
% 23.26/3.47      ( ~ r1_tarski(k1_relat_1(sK5(k1_xboole_0)),sK8)
% 23.26/3.47      | ~ r1_tarski(sK8,k1_relat_1(sK5(k1_xboole_0)))
% 23.26/3.47      | sK8 = k1_relat_1(sK5(k1_xboole_0)) ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_2504]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2459,plain,
% 23.26/3.47      ( ~ r1_tarski(X0,X1)
% 23.26/3.47      | r1_tarski(sK8,k1_relat_1(sK5(X2)))
% 23.26/3.47      | k1_relat_1(sK5(X2)) != X1
% 23.26/3.47      | sK8 != X0 ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_1698]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2461,plain,
% 23.26/3.47      ( r1_tarski(sK8,k1_relat_1(sK5(k1_xboole_0)))
% 23.26/3.47      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 23.26/3.47      | k1_relat_1(sK5(k1_xboole_0)) != k1_xboole_0
% 23.26/3.47      | sK8 != k1_xboole_0 ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_2459]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2348,plain,
% 23.26/3.47      ( ~ r1_tarski(X0,X1)
% 23.26/3.47      | r1_tarski(k1_relat_1(sK5(X2)),sK8)
% 23.26/3.47      | k1_relat_1(sK5(X2)) != X0
% 23.26/3.47      | sK8 != X1 ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_1698]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2350,plain,
% 23.26/3.47      ( r1_tarski(k1_relat_1(sK5(k1_xboole_0)),sK8)
% 23.26/3.47      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 23.26/3.47      | k1_relat_1(sK5(k1_xboole_0)) != k1_xboole_0
% 23.26/3.47      | sK8 != k1_xboole_0 ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_2348]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2332,plain,
% 23.26/3.47      ( ~ r1_tarski(k2_relat_1(sK5(X0)),sK7) | sK8 != X0 ),
% 23.26/3.47      inference(predicate_to_equality_rev,[status(thm)],[c_2330]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2334,plain,
% 23.26/3.47      ( ~ r1_tarski(k2_relat_1(sK5(k1_xboole_0)),sK7)
% 23.26/3.47      | sK8 != k1_xboole_0 ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_2332]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_0,plain,
% 23.26/3.47      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 23.26/3.47      inference(cnf_transformation,[],[f42]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2258,plain,
% 23.26/3.47      ( ~ r2_hidden(sK0(k2_relat_1(sK5(X0)),sK7),sK7)
% 23.26/3.47      | r1_tarski(k2_relat_1(sK5(X0)),sK7) ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_0]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_2265,plain,
% 23.26/3.47      ( ~ r2_hidden(sK0(k2_relat_1(sK5(k1_xboole_0)),sK7),sK7)
% 23.26/3.47      | r1_tarski(k2_relat_1(sK5(k1_xboole_0)),sK7) ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_2258]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_432,plain,
% 23.26/3.47      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 23.26/3.47      | r2_hidden(sK4(X1,X0),k1_relat_1(X1))
% 23.26/3.47      | ~ v1_relat_1(X1)
% 23.26/3.47      | sK5(X2) != X1 ),
% 23.26/3.47      inference(resolution_lifted,[status(thm)],[c_15,c_18]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_433,plain,
% 23.26/3.47      ( ~ r2_hidden(X0,k2_relat_1(sK5(X1)))
% 23.26/3.47      | r2_hidden(sK4(sK5(X1),X0),k1_relat_1(sK5(X1)))
% 23.26/3.47      | ~ v1_relat_1(sK5(X1)) ),
% 23.26/3.47      inference(unflattening,[status(thm)],[c_432]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_435,plain,
% 23.26/3.47      ( r2_hidden(sK4(sK5(k1_xboole_0),k1_xboole_0),k1_relat_1(sK5(k1_xboole_0)))
% 23.26/3.47      | ~ r2_hidden(k1_xboole_0,k2_relat_1(sK5(k1_xboole_0)))
% 23.26/3.47      | ~ v1_relat_1(sK5(k1_xboole_0)) ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_433]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_43,plain,
% 23.26/3.47      ( k1_relat_1(sK5(k1_xboole_0)) = k1_xboole_0 ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_17]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_38,plain,
% 23.26/3.47      ( v1_relat_1(sK5(k1_xboole_0)) ),
% 23.26/3.47      inference(instantiation,[status(thm)],[c_19]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_75951,plain,
% 23.26/3.47      ( sK4(sK5(k1_xboole_0),k1_xboole_0) = k1_xboole_0
% 23.26/3.47      | v1_funct_1(sK5(k1_xboole_0)) != iProver_top ),
% 23.26/3.47      inference(grounding,
% 23.26/3.47                [status(thm)],
% 23.26/3.47                [c_50435:[bind(X0,$fot(k1_xboole_0))]]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(c_75952,plain,
% 23.26/3.47      ( v1_funct_1(sK5(k1_xboole_0)) = iProver_top ),
% 23.26/3.47      inference(grounding,
% 23.26/3.47                [status(thm)],
% 23.26/3.47                [c_40:[bind(X0,$fot(k1_xboole_0))]]) ).
% 23.26/3.47  
% 23.26/3.47  cnf(contradiction,plain,
% 23.26/3.47      ( $false ),
% 23.26/3.47      inference(minisat,
% 23.26/3.47                [status(thm)],
% 23.26/3.47                [c_75950,c_75951,c_13233,c_9614,c_9383,c_8924,c_8117,
% 23.26/3.47                 c_3607,c_3198,c_2808,c_2722,c_2506,c_2461,c_2350,c_2334,
% 23.26/3.47                 c_2265,c_435,c_72,c_43,c_42,c_75952,c_39,c_38]) ).
% 23.26/3.47  
% 23.26/3.47  
% 23.26/3.47  % SZS output end CNFRefutation for theBenchmark.p
% 23.26/3.47  
% 23.26/3.47  ------                               Statistics
% 23.26/3.47  
% 23.26/3.47  ------ General
% 23.26/3.47  
% 23.26/3.47  abstr_ref_over_cycles:                  0
% 23.26/3.47  abstr_ref_under_cycles:                 0
% 23.26/3.47  gc_basic_clause_elim:                   0
% 23.26/3.47  forced_gc_time:                         0
% 23.26/3.47  parsing_time:                           0.008
% 23.26/3.47  unif_index_cands_time:                  0.
% 23.26/3.47  unif_index_add_time:                    0.
% 23.26/3.47  orderings_time:                         0.
% 23.26/3.47  out_proof_time:                         0.017
% 23.26/3.47  total_time:                             2.646
% 23.26/3.47  num_of_symbols:                         49
% 23.26/3.47  num_of_terms:                           76115
% 23.26/3.47  
% 23.26/3.47  ------ Preprocessing
% 23.26/3.47  
% 23.26/3.47  num_of_splits:                          0
% 23.26/3.47  num_of_split_atoms:                     0
% 23.26/3.47  num_of_reused_defs:                     0
% 23.26/3.47  num_eq_ax_congr_red:                    39
% 23.26/3.47  num_of_sem_filtered_clauses:            1
% 23.26/3.47  num_of_subtypes:                        0
% 23.26/3.47  monotx_restored_types:                  0
% 23.26/3.47  sat_num_of_epr_types:                   0
% 23.26/3.47  sat_num_of_non_cyclic_types:            0
% 23.26/3.47  sat_guarded_non_collapsed_types:        0
% 23.26/3.47  num_pure_diseq_elim:                    0
% 23.26/3.47  simp_replaced_by:                       0
% 23.26/3.47  res_preprocessed:                       119
% 23.26/3.47  prep_upred:                             0
% 23.26/3.47  prep_unflattend:                        56
% 23.26/3.47  smt_new_axioms:                         0
% 23.26/3.47  pred_elim_cands:                        4
% 23.26/3.47  pred_elim:                              0
% 23.26/3.47  pred_elim_cl:                           0
% 23.26/3.47  pred_elim_cycles:                       4
% 23.26/3.47  merged_defs:                            8
% 23.26/3.47  merged_defs_ncl:                        0
% 23.26/3.47  bin_hyper_res:                          8
% 23.26/3.47  prep_cycles:                            4
% 23.26/3.47  pred_elim_time:                         0.015
% 23.26/3.47  splitting_time:                         0.
% 23.26/3.47  sem_filter_time:                        0.
% 23.26/3.47  monotx_time:                            0.
% 23.26/3.47  subtype_inf_time:                       0.
% 23.26/3.47  
% 23.26/3.47  ------ Problem properties
% 23.26/3.47  
% 23.26/3.47  clauses:                                25
% 23.26/3.47  conjectures:                            2
% 23.26/3.47  epr:                                    5
% 23.26/3.47  horn:                                   17
% 23.26/3.47  ground:                                 1
% 23.26/3.47  unary:                                  5
% 23.26/3.47  binary:                                 11
% 23.26/3.47  lits:                                   65
% 23.26/3.47  lits_eq:                                19
% 23.26/3.47  fd_pure:                                0
% 23.26/3.47  fd_pseudo:                              0
% 23.26/3.47  fd_cond:                                4
% 23.26/3.47  fd_pseudo_cond:                         4
% 23.26/3.47  ac_symbols:                             0
% 23.26/3.47  
% 23.26/3.47  ------ Propositional Solver
% 23.26/3.47  
% 23.26/3.47  prop_solver_calls:                      44
% 23.26/3.47  prop_fast_solver_calls:                 4657
% 23.26/3.47  smt_solver_calls:                       0
% 23.26/3.47  smt_fast_solver_calls:                  0
% 23.26/3.47  prop_num_of_clauses:                    32609
% 23.26/3.47  prop_preprocess_simplified:             51132
% 23.26/3.47  prop_fo_subsumed:                       454
% 23.26/3.47  prop_solver_time:                       0.
% 23.26/3.47  smt_solver_time:                        0.
% 23.26/3.47  smt_fast_solver_time:                   0.
% 23.26/3.47  prop_fast_solver_time:                  0.
% 23.26/3.47  prop_unsat_core_time:                   0.003
% 23.26/3.47  
% 23.26/3.47  ------ QBF
% 23.26/3.47  
% 23.26/3.47  qbf_q_res:                              0
% 23.26/3.47  qbf_num_tautologies:                    0
% 23.26/3.47  qbf_prep_cycles:                        0
% 23.26/3.47  
% 23.26/3.47  ------ BMC1
% 23.26/3.47  
% 23.26/3.47  bmc1_current_bound:                     -1
% 23.26/3.47  bmc1_last_solved_bound:                 -1
% 23.26/3.47  bmc1_unsat_core_size:                   -1
% 23.26/3.47  bmc1_unsat_core_parents_size:           -1
% 23.26/3.47  bmc1_merge_next_fun:                    0
% 23.26/3.47  bmc1_unsat_core_clauses_time:           0.
% 23.26/3.47  
% 23.26/3.47  ------ Instantiation
% 23.26/3.47  
% 23.26/3.47  inst_num_of_clauses:                    908
% 23.26/3.47  inst_num_in_passive:                    255
% 23.26/3.47  inst_num_in_active:                     2683
% 23.26/3.47  inst_num_in_unprocessed:                290
% 23.26/3.47  inst_num_of_loops:                      3387
% 23.26/3.47  inst_num_of_learning_restarts:          1
% 23.26/3.47  inst_num_moves_active_passive:          696
% 23.26/3.47  inst_lit_activity:                      0
% 23.26/3.47  inst_lit_activity_moves:                0
% 23.26/3.47  inst_num_tautologies:                   0
% 23.26/3.47  inst_num_prop_implied:                  0
% 23.26/3.47  inst_num_existing_simplified:           0
% 23.26/3.47  inst_num_eq_res_simplified:             0
% 23.26/3.47  inst_num_child_elim:                    0
% 23.26/3.47  inst_num_of_dismatching_blockings:      6234
% 23.26/3.47  inst_num_of_non_proper_insts:           9732
% 23.26/3.47  inst_num_of_duplicates:                 0
% 23.26/3.47  inst_inst_num_from_inst_to_res:         0
% 23.26/3.47  inst_dismatching_checking_time:         0.
% 23.26/3.47  
% 23.26/3.47  ------ Resolution
% 23.26/3.47  
% 23.26/3.47  res_num_of_clauses:                     34
% 23.26/3.47  res_num_in_passive:                     34
% 23.26/3.47  res_num_in_active:                      0
% 23.26/3.47  res_num_of_loops:                       123
% 23.26/3.47  res_forward_subset_subsumed:            166
% 23.26/3.47  res_backward_subset_subsumed:           2
% 23.26/3.47  res_forward_subsumed:                   0
% 23.26/3.47  res_backward_subsumed:                  0
% 23.26/3.47  res_forward_subsumption_resolution:     8
% 23.26/3.47  res_backward_subsumption_resolution:    0
% 23.26/3.47  res_clause_to_clause_subsumption:       22959
% 23.26/3.47  res_orphan_elimination:                 0
% 23.26/3.47  res_tautology_del:                      641
% 23.26/3.47  res_num_eq_res_simplified:              0
% 23.26/3.47  res_num_sel_changes:                    0
% 23.26/3.47  res_moves_from_active_to_pass:          0
% 23.26/3.47  
% 23.26/3.47  ------ Superposition
% 23.26/3.47  
% 23.26/3.47  sup_time_total:                         0.
% 23.26/3.47  sup_time_generating:                    0.
% 23.26/3.47  sup_time_sim_full:                      0.
% 23.26/3.47  sup_time_sim_immed:                     0.
% 23.26/3.47  
% 23.26/3.47  sup_num_of_clauses:                     4403
% 23.26/3.47  sup_num_in_active:                      499
% 23.26/3.47  sup_num_in_passive:                     3904
% 23.26/3.47  sup_num_of_loops:                       676
% 23.26/3.47  sup_fw_superposition:                   3325
% 23.26/3.47  sup_bw_superposition:                   3713
% 23.26/3.47  sup_immediate_simplified:               2115
% 23.26/3.47  sup_given_eliminated:                   16
% 23.26/3.47  comparisons_done:                       0
% 23.26/3.47  comparisons_avoided:                    472
% 23.26/3.47  
% 23.26/3.47  ------ Simplifications
% 23.26/3.47  
% 23.26/3.47  
% 23.26/3.47  sim_fw_subset_subsumed:                 482
% 23.26/3.47  sim_bw_subset_subsumed:                 108
% 23.26/3.47  sim_fw_subsumed:                        653
% 23.26/3.47  sim_bw_subsumed:                        257
% 23.26/3.47  sim_fw_subsumption_res:                 0
% 23.26/3.47  sim_bw_subsumption_res:                 0
% 23.26/3.47  sim_tautology_del:                      108
% 23.26/3.47  sim_eq_tautology_del:                   437
% 23.26/3.47  sim_eq_res_simp:                        0
% 23.26/3.47  sim_fw_demodulated:                     772
% 23.26/3.47  sim_bw_demodulated:                     14
% 23.26/3.47  sim_light_normalised:                   445
% 23.26/3.47  sim_joinable_taut:                      0
% 23.26/3.47  sim_joinable_simp:                      0
% 23.26/3.47  sim_ac_normalised:                      0
% 23.26/3.47  sim_smt_subsumption:                    0
% 23.26/3.47  
%------------------------------------------------------------------------------
