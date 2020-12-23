%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:34 EST 2020

% Result     : Theorem 23.83s
% Output     : CNFRefutation 23.83s
% Verified   : 
% Statistics : Number of formulae       :  177 (12283 expanded)
%              Number of clauses        :  122 (4068 expanded)
%              Number of leaves         :   16 (2947 expanded)
%              Depth                    :   39
%              Number of atoms          :  578 (56146 expanded)
%              Number of equality atoms :  334 (22970 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK4(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK4(X0,X1)) = X0
        & v1_funct_1(sK4(X0,X1))
        & v1_relat_1(sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK4(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK4(X0,X1)) = X0
      & v1_funct_1(sK4(X0,X1))
      & v1_relat_1(sK4(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f31])).

fof(f51,plain,(
    ! [X0,X1] : k1_relat_1(sK4(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

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

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f29,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) = X2
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
              ( k1_funct_1(X0,X3) != sK1(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK1(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK1(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK1(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
                  & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK1(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK3(X0,X5)) = X5
                    & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f26,f29,f28,f27])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK1(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,(
    ! [X0,X1] : v1_relat_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f50,plain,(
    ! [X0,X1] : v1_funct_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k1_xboole_0
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k1_xboole_0
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0] :
      ( ( ( k1_relat_1(X0) = k1_xboole_0
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_relat_1(X0) != k1_xboole_0 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f41,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_relat_1(X0) != k1_xboole_0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f44,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f60,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK4(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f43,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f61,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f16])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ~ r1_tarski(k2_relat_1(X2),X0)
            | k1_relat_1(X2) != X1
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 != X0 ) )
   => ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),sK5)
          | k1_relat_1(X2) != sK6
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = sK6
        | k1_xboole_0 != sK5 ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK5)
        | k1_relat_1(X2) != sK6
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK6
      | k1_xboole_0 != sK5 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f17,f33])).

fof(f55,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK5)
      | k1_relat_1(X2) != sK6
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f54,plain,
    ( k1_xboole_0 = sK6
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f34])).

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

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

cnf(c_15,plain,
    ( k1_relat_1(sK4(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_10,plain,
    ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
    | r2_hidden(sK1(X0,X1),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1197,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_17,plain,
    ( v1_relat_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1191,plain,
    ( v1_relat_1(sK4(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,plain,
    ( v1_funct_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1192,plain,
    ( v1_funct_1(sK4(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1200,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1657,plain,
    ( k2_relat_1(sK4(X0,X1)) = k1_xboole_0
    | k1_xboole_0 != X0
    | v1_relat_1(sK4(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_1200])).

cnf(c_1658,plain,
    ( ~ v1_relat_1(sK4(X0,X1))
    | k2_relat_1(sK4(X0,X1)) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1657])).

cnf(c_1777,plain,
    ( k1_xboole_0 != X0
    | k2_relat_1(sK4(X0,X1)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1657,c_17,c_1658])).

cnf(c_1778,plain,
    ( k2_relat_1(sK4(X0,X1)) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(renaming,[status(thm)],[c_1777])).

cnf(c_1780,plain,
    ( k2_relat_1(sK4(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_1778])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK3(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1195,plain,
    ( k1_funct_1(X0,sK3(X0,X1)) = X1
    | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1849,plain,
    ( k1_funct_1(sK4(k1_xboole_0,X0),sK3(sK4(k1_xboole_0,X0),X1)) = X1
    | r2_hidden(X1,k1_xboole_0) != iProver_top
    | v1_funct_1(sK4(k1_xboole_0,X0)) != iProver_top
    | v1_relat_1(sK4(k1_xboole_0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1780,c_1195])).

cnf(c_2506,plain,
    ( k1_funct_1(sK4(k1_xboole_0,X0),sK3(sK4(k1_xboole_0,X0),X1)) = X1
    | r2_hidden(X1,k1_xboole_0) != iProver_top
    | v1_relat_1(sK4(k1_xboole_0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1192,c_1849])).

cnf(c_2511,plain,
    ( k1_funct_1(sK4(k1_xboole_0,X0),sK3(sK4(k1_xboole_0,X0),X1)) = X1
    | r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1191,c_2506])).

cnf(c_2598,plain,
    ( k1_funct_1(sK4(k1_xboole_0,X0),sK3(sK4(k1_xboole_0,X0),sK1(X1,k1_xboole_0))) = sK1(X1,k1_xboole_0)
    | k2_relat_1(X1) = k1_xboole_0
    | r2_hidden(sK2(X1,k1_xboole_0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1197,c_2511])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1205,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(sK4(X1,X2),X0) = X2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1193,plain,
    ( k1_funct_1(sK4(X0,X1),X2) = X1
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1593,plain,
    ( k1_funct_1(sK4(X0,X1),sK0(X0,X2)) = X1
    | r1_tarski(X0,X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1205,c_1193])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1194,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1204,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1709,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK3(X1,X0),X2) = iProver_top
    | r1_tarski(k1_relat_1(X1),X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1194,c_1204])).

cnf(c_1848,plain,
    ( k1_funct_1(X0,sK3(X0,sK0(k2_relat_1(X0),X1))) = sK0(k2_relat_1(X0),X1)
    | r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1205,c_1195])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(X0),sK5)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) != sK6 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1190,plain,
    ( k1_relat_1(X0) != sK6
    | r1_tarski(k2_relat_1(X0),sK5) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1331,plain,
    ( sK6 != X0
    | r1_tarski(k2_relat_1(sK4(X0,X1)),sK5) != iProver_top
    | v1_funct_1(sK4(X0,X1)) != iProver_top
    | v1_relat_1(sK4(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_1190])).

cnf(c_27,plain,
    ( v1_relat_1(sK4(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_30,plain,
    ( v1_funct_1(sK4(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1374,plain,
    ( sK6 != X0
    | r1_tarski(k2_relat_1(sK4(X0,X1)),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1331,c_27,c_30])).

cnf(c_1380,plain,
    ( r1_tarski(k2_relat_1(sK4(sK6,X0)),sK5) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1374])).

cnf(c_5201,plain,
    ( k1_funct_1(sK4(sK6,X0),sK3(sK4(sK6,X0),sK0(k2_relat_1(sK4(sK6,X0)),sK5))) = sK0(k2_relat_1(sK4(sK6,X0)),sK5)
    | v1_funct_1(sK4(sK6,X0)) != iProver_top
    | v1_relat_1(sK4(sK6,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1848,c_1380])).

cnf(c_1335,plain,
    ( v1_funct_1(sK4(sK6,X0)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1336,plain,
    ( v1_funct_1(sK4(sK6,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1335])).

cnf(c_1392,plain,
    ( v1_relat_1(sK4(sK6,X0)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1393,plain,
    ( v1_relat_1(sK4(sK6,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1392])).

cnf(c_5790,plain,
    ( k1_funct_1(sK4(sK6,X0),sK3(sK4(sK6,X0),sK0(k2_relat_1(sK4(sK6,X0)),sK5))) = sK0(k2_relat_1(sK4(sK6,X0)),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5201,c_1336,c_1393])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1196,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5794,plain,
    ( r2_hidden(sK3(sK4(sK6,X0),sK0(k2_relat_1(sK4(sK6,X0)),sK5)),k1_relat_1(sK4(sK6,X0))) != iProver_top
    | r2_hidden(sK0(k2_relat_1(sK4(sK6,X0)),sK5),k2_relat_1(sK4(sK6,X0))) = iProver_top
    | v1_funct_1(sK4(sK6,X0)) != iProver_top
    | v1_relat_1(sK4(sK6,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5790,c_1196])).

cnf(c_5795,plain,
    ( r2_hidden(sK3(sK4(sK6,X0),sK0(k2_relat_1(sK4(sK6,X0)),sK5)),sK6) != iProver_top
    | r2_hidden(sK0(k2_relat_1(sK4(sK6,X0)),sK5),k2_relat_1(sK4(sK6,X0))) = iProver_top
    | v1_funct_1(sK4(sK6,X0)) != iProver_top
    | v1_relat_1(sK4(sK6,X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5794,c_15])).

cnf(c_1290,plain,
    ( r2_hidden(sK0(X0,sK5),X0)
    | r1_tarski(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1472,plain,
    ( r2_hidden(sK0(k2_relat_1(sK4(sK6,X0)),sK5),k2_relat_1(sK4(sK6,X0)))
    | r1_tarski(k2_relat_1(sK4(sK6,X0)),sK5) ),
    inference(instantiation,[status(thm)],[c_1290])).

cnf(c_1478,plain,
    ( r2_hidden(sK0(k2_relat_1(sK4(sK6,X0)),sK5),k2_relat_1(sK4(sK6,X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK4(sK6,X0)),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1472])).

cnf(c_5804,plain,
    ( r2_hidden(sK0(k2_relat_1(sK4(sK6,X0)),sK5),k2_relat_1(sK4(sK6,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5795,c_1380,c_1478])).

cnf(c_1594,plain,
    ( k1_funct_1(sK4(k1_relat_1(X0),X1),sK3(X0,X2)) = X1
    | r2_hidden(X2,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1194,c_1193])).

cnf(c_5815,plain,
    ( k1_funct_1(sK4(k1_relat_1(sK4(sK6,X0)),X1),sK3(sK4(sK6,X0),sK0(k2_relat_1(sK4(sK6,X0)),sK5))) = X1
    | v1_funct_1(sK4(sK6,X0)) != iProver_top
    | v1_relat_1(sK4(sK6,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5804,c_1594])).

cnf(c_5819,plain,
    ( k1_funct_1(sK4(sK6,X0),sK3(sK4(sK6,X1),sK0(k2_relat_1(sK4(sK6,X1)),sK5))) = X0
    | v1_funct_1(sK4(sK6,X1)) != iProver_top
    | v1_relat_1(sK4(sK6,X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5815,c_15])).

cnf(c_6560,plain,
    ( k1_funct_1(sK4(sK6,X0),sK3(sK4(sK6,X1),sK0(k2_relat_1(sK4(sK6,X1)),sK5))) = X0
    | v1_relat_1(sK4(sK6,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1192,c_5819])).

cnf(c_7954,plain,
    ( k1_funct_1(sK4(sK6,X0),sK3(sK4(sK6,X1),sK0(k2_relat_1(sK4(sK6,X1)),sK5))) = X0 ),
    inference(superposition,[status(thm)],[c_1191,c_6560])).

cnf(c_8154,plain,
    ( sK0(k2_relat_1(sK4(sK6,X0)),sK5) = X0 ),
    inference(demodulation,[status(thm)],[c_7954,c_5790])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1206,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8561,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r1_tarski(k2_relat_1(sK4(sK6,X0)),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_8154,c_1206])).

cnf(c_8849,plain,
    ( r2_hidden(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8561,c_1380])).

cnf(c_8861,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r1_tarski(k1_relat_1(X1),sK5) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1709,c_8849])).

cnf(c_11727,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(sK4(k1_xboole_0,X1)),sK5) != iProver_top
    | v1_funct_1(sK4(k1_xboole_0,X1)) != iProver_top
    | v1_relat_1(sK4(k1_xboole_0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1780,c_8861])).

cnf(c_11728,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK5) != iProver_top
    | v1_funct_1(sK4(k1_xboole_0,X1)) != iProver_top
    | v1_relat_1(sK4(k1_xboole_0,X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11727,c_15])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 = sK6
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1225,plain,
    ( ~ r1_tarski(sK5,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK5)
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1226,plain,
    ( k1_xboole_0 = sK5
    | r1_tarski(sK5,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1225])).

cnf(c_1249,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,X0)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1295,plain,
    ( ~ r1_tarski(sK5,sK5)
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1249])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1342,plain,
    ( r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_899,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1372,plain,
    ( X0 != X1
    | sK6 != X1
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_899])).

cnf(c_1653,plain,
    ( X0 != sK6
    | sK6 = X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1372])).

cnf(c_1654,plain,
    ( sK6 != sK6
    | sK6 = k1_xboole_0
    | k1_xboole_0 != sK6 ),
    inference(instantiation,[status(thm)],[c_1653])).

cnf(c_898,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1922,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_898])).

cnf(c_900,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1977,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK6,X2)
    | X2 != X1
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_900])).

cnf(c_2481,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK6,sK5)
    | sK6 != X0
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_1977])).

cnf(c_4667,plain,
    ( ~ r1_tarski(X0,sK5)
    | r1_tarski(sK6,sK5)
    | sK6 != X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2481])).

cnf(c_4668,plain,
    ( sK6 != X0
    | sK5 != sK5
    | r1_tarski(X0,sK5) != iProver_top
    | r1_tarski(sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4667])).

cnf(c_4670,plain,
    ( sK6 != k1_xboole_0
    | sK5 != sK5
    | r1_tarski(sK6,sK5) = iProver_top
    | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4668])).

cnf(c_8855,plain,
    ( r1_tarski(sK5,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1205,c_8849])).

cnf(c_8866,plain,
    ( r1_tarski(sK5,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_8855])).

cnf(c_8487,plain,
    ( r2_hidden(X0,k2_relat_1(sK4(sK6,X0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8154,c_5804])).

cnf(c_11726,plain,
    ( r1_tarski(k1_relat_1(sK4(sK6,X0)),sK5) != iProver_top
    | v1_funct_1(sK4(sK6,X0)) != iProver_top
    | v1_relat_1(sK4(sK6,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8487,c_8861])).

cnf(c_11729,plain,
    ( r1_tarski(sK6,sK5) != iProver_top
    | v1_funct_1(sK4(sK6,X0)) != iProver_top
    | v1_relat_1(sK4(sK6,X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11726,c_15])).

cnf(c_12579,plain,
    ( r1_tarski(k1_xboole_0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11728,c_20,c_1226,c_1295,c_1336,c_1342,c_1393,c_1654,c_1922,c_4670,c_8866,c_11729])).

cnf(c_12583,plain,
    ( k1_funct_1(sK4(k1_xboole_0,X0),sK0(k1_xboole_0,sK5)) = X0 ),
    inference(superposition,[status(thm)],[c_1593,c_12579])).

cnf(c_1858,plain,
    ( k1_funct_1(sK4(k2_relat_1(X0),X1),k1_funct_1(X0,X2)) = X1
    | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1196,c_1193])).

cnf(c_2239,plain,
    ( k1_funct_1(sK4(k2_relat_1(sK4(X0,X1)),X2),k1_funct_1(sK4(X0,X1),X3)) = X2
    | r2_hidden(X3,X0) != iProver_top
    | v1_funct_1(sK4(X0,X1)) != iProver_top
    | v1_relat_1(sK4(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_1858])).

cnf(c_2744,plain,
    ( k1_funct_1(sK4(k2_relat_1(sK4(X0,X1)),X2),k1_funct_1(sK4(X0,X1),X3)) = X2
    | r2_hidden(X3,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2239,c_27,c_30])).

cnf(c_2750,plain,
    ( k1_funct_1(sK4(k2_relat_1(sK4(X0,X1)),X2),k1_funct_1(sK4(X0,X1),sK0(X0,X3))) = X2
    | r1_tarski(X0,X3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1205,c_2744])).

cnf(c_12585,plain,
    ( k1_funct_1(sK4(k2_relat_1(sK4(k1_xboole_0,X0)),X1),k1_funct_1(sK4(k1_xboole_0,X0),sK0(k1_xboole_0,sK5))) = X1 ),
    inference(superposition,[status(thm)],[c_2750,c_12579])).

cnf(c_12586,plain,
    ( k1_funct_1(sK4(k1_xboole_0,X0),k1_funct_1(sK4(k1_xboole_0,X1),sK0(k1_xboole_0,sK5))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_12585,c_1780])).

cnf(c_12587,plain,
    ( k1_funct_1(sK4(k1_xboole_0,X0),X1) = X0 ),
    inference(demodulation,[status(thm)],[c_12583,c_12586])).

cnf(c_55132,plain,
    ( sK1(X0,k1_xboole_0) = X1
    | k2_relat_1(X0) = k1_xboole_0
    | r2_hidden(sK2(X0,k1_xboole_0),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2598,c_12587])).

cnf(c_55136,plain,
    ( sK1(sK4(X0,X1),k1_xboole_0) = X2
    | k2_relat_1(sK4(X0,X1)) = k1_xboole_0
    | r2_hidden(sK2(sK4(X0,X1),k1_xboole_0),X0) = iProver_top
    | v1_funct_1(sK4(X0,X1)) != iProver_top
    | v1_relat_1(sK4(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_55132])).

cnf(c_55167,plain,
    ( sK1(sK4(X0,X1),k1_xboole_0) = X2
    | k2_relat_1(sK4(X0,X1)) = k1_xboole_0
    | r2_hidden(sK2(sK4(X0,X1),k1_xboole_0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_55136,c_27,c_30])).

cnf(c_55187,plain,
    ( sK1(sK4(sK5,X0),k1_xboole_0) = X1
    | k2_relat_1(sK4(sK5,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_55167,c_8849])).

cnf(c_1925,plain,
    ( k2_relat_1(sK4(X0,X1)) = X2
    | r2_hidden(sK2(sK4(X0,X1),X2),X0) = iProver_top
    | r2_hidden(sK1(sK4(X0,X1),X2),X2) = iProver_top
    | v1_funct_1(sK4(X0,X1)) != iProver_top
    | v1_relat_1(sK4(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_1197])).

cnf(c_2846,plain,
    ( k2_relat_1(sK4(X0,X1)) = X2
    | r2_hidden(sK2(sK4(X0,X1),X2),X0) = iProver_top
    | r2_hidden(sK1(sK4(X0,X1),X2),X2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1925,c_27,c_30])).

cnf(c_8858,plain,
    ( k2_relat_1(sK4(X0,X1)) = sK5
    | r2_hidden(sK2(sK4(X0,X1),sK5),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2846,c_8849])).

cnf(c_11913,plain,
    ( k2_relat_1(sK4(sK5,X0)) = sK5 ),
    inference(superposition,[status(thm)],[c_8858,c_8849])).

cnf(c_55199,plain,
    ( sK1(sK4(sK5,X0),k1_xboole_0) = X1
    | sK5 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_55187,c_11913])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_60,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_59,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_61,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_59])).

cnf(c_64,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1284,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_xboole_0,sK5)
    | sK5 != X1
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_900])).

cnf(c_1285,plain,
    ( sK5 != X0
    | k1_xboole_0 != X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k1_xboole_0,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1284])).

cnf(c_1287,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_xboole_0,sK5) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1285])).

cnf(c_73921,plain,
    ( sK1(sK4(sK5,X0),k1_xboole_0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_55199,c_20,c_60,c_61,c_64,c_1226,c_1287,c_1295,c_1336,c_1342,c_1393,c_1654,c_1922,c_4670,c_8866,c_11729])).

cnf(c_74888,plain,
    ( k1_relat_1(sK1(sK4(sK5,X0),k1_xboole_0)) = X1 ),
    inference(superposition,[status(thm)],[c_73921,c_15])).

cnf(c_75538,plain,
    ( k2_relat_1(k1_relat_1(sK1(sK4(sK5,X0),k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_74888,c_1780])).

cnf(c_75551,plain,
    ( k2_relat_1(k1_relat_1(sK1(sK4(sK5,X0),k1_xboole_0))) = sK5 ),
    inference(superposition,[status(thm)],[c_74888,c_11913])).

cnf(c_75740,plain,
    ( sK5 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_75538,c_75551])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_75740,c_12579,c_1287,c_64,c_61,c_60])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:53:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 23.83/3.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.83/3.50  
% 23.83/3.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.83/3.50  
% 23.83/3.50  ------  iProver source info
% 23.83/3.50  
% 23.83/3.50  git: date: 2020-06-30 10:37:57 +0100
% 23.83/3.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.83/3.50  git: non_committed_changes: false
% 23.83/3.50  git: last_make_outside_of_git: false
% 23.83/3.50  
% 23.83/3.50  ------ 
% 23.83/3.50  
% 23.83/3.50  ------ Input Options
% 23.83/3.50  
% 23.83/3.50  --out_options                           all
% 23.83/3.50  --tptp_safe_out                         true
% 23.83/3.50  --problem_path                          ""
% 23.83/3.50  --include_path                          ""
% 23.83/3.50  --clausifier                            res/vclausify_rel
% 23.83/3.50  --clausifier_options                    ""
% 23.83/3.50  --stdin                                 false
% 23.83/3.50  --stats_out                             all
% 23.83/3.50  
% 23.83/3.50  ------ General Options
% 23.83/3.50  
% 23.83/3.50  --fof                                   false
% 23.83/3.50  --time_out_real                         305.
% 23.83/3.50  --time_out_virtual                      -1.
% 23.83/3.50  --symbol_type_check                     false
% 23.83/3.50  --clausify_out                          false
% 23.83/3.50  --sig_cnt_out                           false
% 23.83/3.50  --trig_cnt_out                          false
% 23.83/3.50  --trig_cnt_out_tolerance                1.
% 23.83/3.50  --trig_cnt_out_sk_spl                   false
% 23.83/3.50  --abstr_cl_out                          false
% 23.83/3.50  
% 23.83/3.50  ------ Global Options
% 23.83/3.50  
% 23.83/3.50  --schedule                              default
% 23.83/3.50  --add_important_lit                     false
% 23.83/3.50  --prop_solver_per_cl                    1000
% 23.83/3.50  --min_unsat_core                        false
% 23.83/3.50  --soft_assumptions                      false
% 23.83/3.50  --soft_lemma_size                       3
% 23.83/3.50  --prop_impl_unit_size                   0
% 23.83/3.50  --prop_impl_unit                        []
% 23.83/3.50  --share_sel_clauses                     true
% 23.83/3.50  --reset_solvers                         false
% 23.83/3.50  --bc_imp_inh                            [conj_cone]
% 23.83/3.50  --conj_cone_tolerance                   3.
% 23.83/3.50  --extra_neg_conj                        none
% 23.83/3.50  --large_theory_mode                     true
% 23.83/3.50  --prolific_symb_bound                   200
% 23.83/3.50  --lt_threshold                          2000
% 23.83/3.50  --clause_weak_htbl                      true
% 23.83/3.50  --gc_record_bc_elim                     false
% 23.83/3.50  
% 23.83/3.50  ------ Preprocessing Options
% 23.83/3.50  
% 23.83/3.50  --preprocessing_flag                    true
% 23.83/3.50  --time_out_prep_mult                    0.1
% 23.83/3.50  --splitting_mode                        input
% 23.83/3.50  --splitting_grd                         true
% 23.83/3.50  --splitting_cvd                         false
% 23.83/3.50  --splitting_cvd_svl                     false
% 23.83/3.50  --splitting_nvd                         32
% 23.83/3.50  --sub_typing                            true
% 23.83/3.50  --prep_gs_sim                           true
% 23.83/3.50  --prep_unflatten                        true
% 23.83/3.50  --prep_res_sim                          true
% 23.83/3.50  --prep_upred                            true
% 23.83/3.50  --prep_sem_filter                       exhaustive
% 23.83/3.50  --prep_sem_filter_out                   false
% 23.83/3.50  --pred_elim                             true
% 23.83/3.50  --res_sim_input                         true
% 23.83/3.50  --eq_ax_congr_red                       true
% 23.83/3.50  --pure_diseq_elim                       true
% 23.83/3.50  --brand_transform                       false
% 23.83/3.50  --non_eq_to_eq                          false
% 23.83/3.50  --prep_def_merge                        true
% 23.83/3.50  --prep_def_merge_prop_impl              false
% 23.83/3.50  --prep_def_merge_mbd                    true
% 23.83/3.50  --prep_def_merge_tr_red                 false
% 23.83/3.50  --prep_def_merge_tr_cl                  false
% 23.83/3.50  --smt_preprocessing                     true
% 23.83/3.50  --smt_ac_axioms                         fast
% 23.83/3.50  --preprocessed_out                      false
% 23.83/3.50  --preprocessed_stats                    false
% 23.83/3.50  
% 23.83/3.50  ------ Abstraction refinement Options
% 23.83/3.50  
% 23.83/3.50  --abstr_ref                             []
% 23.83/3.50  --abstr_ref_prep                        false
% 23.83/3.50  --abstr_ref_until_sat                   false
% 23.83/3.50  --abstr_ref_sig_restrict                funpre
% 23.83/3.50  --abstr_ref_af_restrict_to_split_sk     false
% 23.83/3.50  --abstr_ref_under                       []
% 23.83/3.50  
% 23.83/3.50  ------ SAT Options
% 23.83/3.50  
% 23.83/3.50  --sat_mode                              false
% 23.83/3.50  --sat_fm_restart_options                ""
% 23.83/3.50  --sat_gr_def                            false
% 23.83/3.50  --sat_epr_types                         true
% 23.83/3.50  --sat_non_cyclic_types                  false
% 23.83/3.50  --sat_finite_models                     false
% 23.83/3.50  --sat_fm_lemmas                         false
% 23.83/3.50  --sat_fm_prep                           false
% 23.83/3.50  --sat_fm_uc_incr                        true
% 23.83/3.50  --sat_out_model                         small
% 23.83/3.50  --sat_out_clauses                       false
% 23.83/3.50  
% 23.83/3.50  ------ QBF Options
% 23.83/3.50  
% 23.83/3.50  --qbf_mode                              false
% 23.83/3.50  --qbf_elim_univ                         false
% 23.83/3.50  --qbf_dom_inst                          none
% 23.83/3.50  --qbf_dom_pre_inst                      false
% 23.83/3.50  --qbf_sk_in                             false
% 23.83/3.50  --qbf_pred_elim                         true
% 23.83/3.50  --qbf_split                             512
% 23.83/3.50  
% 23.83/3.50  ------ BMC1 Options
% 23.83/3.50  
% 23.83/3.50  --bmc1_incremental                      false
% 23.83/3.50  --bmc1_axioms                           reachable_all
% 23.83/3.50  --bmc1_min_bound                        0
% 23.83/3.50  --bmc1_max_bound                        -1
% 23.83/3.50  --bmc1_max_bound_default                -1
% 23.83/3.50  --bmc1_symbol_reachability              true
% 23.83/3.50  --bmc1_property_lemmas                  false
% 23.83/3.50  --bmc1_k_induction                      false
% 23.83/3.50  --bmc1_non_equiv_states                 false
% 23.83/3.50  --bmc1_deadlock                         false
% 23.83/3.50  --bmc1_ucm                              false
% 23.83/3.50  --bmc1_add_unsat_core                   none
% 23.83/3.50  --bmc1_unsat_core_children              false
% 23.83/3.50  --bmc1_unsat_core_extrapolate_axioms    false
% 23.83/3.50  --bmc1_out_stat                         full
% 23.83/3.50  --bmc1_ground_init                      false
% 23.83/3.50  --bmc1_pre_inst_next_state              false
% 23.83/3.50  --bmc1_pre_inst_state                   false
% 23.83/3.50  --bmc1_pre_inst_reach_state             false
% 23.83/3.50  --bmc1_out_unsat_core                   false
% 23.83/3.50  --bmc1_aig_witness_out                  false
% 23.83/3.50  --bmc1_verbose                          false
% 23.83/3.50  --bmc1_dump_clauses_tptp                false
% 23.83/3.50  --bmc1_dump_unsat_core_tptp             false
% 23.83/3.50  --bmc1_dump_file                        -
% 23.83/3.50  --bmc1_ucm_expand_uc_limit              128
% 23.83/3.50  --bmc1_ucm_n_expand_iterations          6
% 23.83/3.50  --bmc1_ucm_extend_mode                  1
% 23.83/3.50  --bmc1_ucm_init_mode                    2
% 23.83/3.50  --bmc1_ucm_cone_mode                    none
% 23.83/3.50  --bmc1_ucm_reduced_relation_type        0
% 23.83/3.50  --bmc1_ucm_relax_model                  4
% 23.83/3.50  --bmc1_ucm_full_tr_after_sat            true
% 23.83/3.50  --bmc1_ucm_expand_neg_assumptions       false
% 23.83/3.50  --bmc1_ucm_layered_model                none
% 23.83/3.50  --bmc1_ucm_max_lemma_size               10
% 23.83/3.50  
% 23.83/3.50  ------ AIG Options
% 23.83/3.50  
% 23.83/3.50  --aig_mode                              false
% 23.83/3.50  
% 23.83/3.50  ------ Instantiation Options
% 23.83/3.50  
% 23.83/3.50  --instantiation_flag                    true
% 23.83/3.50  --inst_sos_flag                         true
% 23.83/3.50  --inst_sos_phase                        true
% 23.83/3.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.83/3.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.83/3.50  --inst_lit_sel_side                     num_symb
% 23.83/3.50  --inst_solver_per_active                1400
% 23.83/3.50  --inst_solver_calls_frac                1.
% 23.83/3.50  --inst_passive_queue_type               priority_queues
% 23.83/3.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.83/3.50  --inst_passive_queues_freq              [25;2]
% 23.83/3.50  --inst_dismatching                      true
% 23.83/3.50  --inst_eager_unprocessed_to_passive     true
% 23.83/3.50  --inst_prop_sim_given                   true
% 23.83/3.50  --inst_prop_sim_new                     false
% 23.83/3.50  --inst_subs_new                         false
% 23.83/3.50  --inst_eq_res_simp                      false
% 23.83/3.50  --inst_subs_given                       false
% 23.83/3.50  --inst_orphan_elimination               true
% 23.83/3.50  --inst_learning_loop_flag               true
% 23.83/3.50  --inst_learning_start                   3000
% 23.83/3.50  --inst_learning_factor                  2
% 23.83/3.50  --inst_start_prop_sim_after_learn       3
% 23.83/3.50  --inst_sel_renew                        solver
% 23.83/3.50  --inst_lit_activity_flag                true
% 23.83/3.50  --inst_restr_to_given                   false
% 23.83/3.50  --inst_activity_threshold               500
% 23.83/3.50  --inst_out_proof                        true
% 23.83/3.50  
% 23.83/3.50  ------ Resolution Options
% 23.83/3.50  
% 23.83/3.50  --resolution_flag                       true
% 23.83/3.50  --res_lit_sel                           adaptive
% 23.83/3.50  --res_lit_sel_side                      none
% 23.83/3.50  --res_ordering                          kbo
% 23.83/3.50  --res_to_prop_solver                    active
% 23.83/3.50  --res_prop_simpl_new                    false
% 23.83/3.50  --res_prop_simpl_given                  true
% 23.83/3.50  --res_passive_queue_type                priority_queues
% 23.83/3.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.83/3.50  --res_passive_queues_freq               [15;5]
% 23.83/3.50  --res_forward_subs                      full
% 23.83/3.50  --res_backward_subs                     full
% 23.83/3.50  --res_forward_subs_resolution           true
% 23.83/3.50  --res_backward_subs_resolution          true
% 23.83/3.50  --res_orphan_elimination                true
% 23.83/3.50  --res_time_limit                        2.
% 23.83/3.50  --res_out_proof                         true
% 23.83/3.50  
% 23.83/3.50  ------ Superposition Options
% 23.83/3.50  
% 23.83/3.50  --superposition_flag                    true
% 23.83/3.50  --sup_passive_queue_type                priority_queues
% 23.83/3.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.83/3.50  --sup_passive_queues_freq               [8;1;4]
% 23.83/3.50  --demod_completeness_check              fast
% 23.83/3.50  --demod_use_ground                      true
% 23.83/3.50  --sup_to_prop_solver                    passive
% 23.83/3.50  --sup_prop_simpl_new                    true
% 23.83/3.50  --sup_prop_simpl_given                  true
% 23.83/3.50  --sup_fun_splitting                     true
% 23.83/3.50  --sup_smt_interval                      50000
% 23.83/3.50  
% 23.83/3.50  ------ Superposition Simplification Setup
% 23.83/3.50  
% 23.83/3.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.83/3.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.83/3.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.83/3.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.83/3.50  --sup_full_triv                         [TrivRules;PropSubs]
% 23.83/3.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.83/3.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.83/3.50  --sup_immed_triv                        [TrivRules]
% 23.83/3.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.83/3.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.83/3.50  --sup_immed_bw_main                     []
% 23.83/3.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.83/3.50  --sup_input_triv                        [Unflattening;TrivRules]
% 23.83/3.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.83/3.50  --sup_input_bw                          []
% 23.83/3.50  
% 23.83/3.50  ------ Combination Options
% 23.83/3.50  
% 23.83/3.50  --comb_res_mult                         3
% 23.83/3.50  --comb_sup_mult                         2
% 23.83/3.50  --comb_inst_mult                        10
% 23.83/3.50  
% 23.83/3.50  ------ Debug Options
% 23.83/3.50  
% 23.83/3.50  --dbg_backtrace                         false
% 23.83/3.50  --dbg_dump_prop_clauses                 false
% 23.83/3.50  --dbg_dump_prop_clauses_file            -
% 23.83/3.50  --dbg_out_stat                          false
% 23.83/3.50  ------ Parsing...
% 23.83/3.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.83/3.50  
% 23.83/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 23.83/3.50  
% 23.83/3.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.83/3.50  
% 23.83/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.83/3.50  ------ Proving...
% 23.83/3.50  ------ Problem Properties 
% 23.83/3.50  
% 23.83/3.50  
% 23.83/3.50  clauses                                 19
% 23.83/3.50  conjectures                             2
% 23.83/3.50  EPR                                     4
% 23.83/3.50  Horn                                    16
% 23.83/3.50  unary                                   4
% 23.83/3.50  binary                                  4
% 23.83/3.50  lits                                    56
% 23.83/3.50  lits eq                                 16
% 23.83/3.50  fd_pure                                 0
% 23.83/3.50  fd_pseudo                               0
% 23.83/3.50  fd_cond                                 0
% 23.83/3.50  fd_pseudo_cond                          4
% 23.83/3.50  AC symbols                              0
% 23.83/3.50  
% 23.83/3.50  ------ Schedule dynamic 5 is on 
% 23.83/3.50  
% 23.83/3.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.83/3.50  
% 23.83/3.50  
% 23.83/3.50  ------ 
% 23.83/3.50  Current options:
% 23.83/3.50  ------ 
% 23.83/3.50  
% 23.83/3.50  ------ Input Options
% 23.83/3.50  
% 23.83/3.50  --out_options                           all
% 23.83/3.50  --tptp_safe_out                         true
% 23.83/3.50  --problem_path                          ""
% 23.83/3.50  --include_path                          ""
% 23.83/3.50  --clausifier                            res/vclausify_rel
% 23.83/3.50  --clausifier_options                    ""
% 23.83/3.50  --stdin                                 false
% 23.83/3.50  --stats_out                             all
% 23.83/3.50  
% 23.83/3.50  ------ General Options
% 23.83/3.50  
% 23.83/3.50  --fof                                   false
% 23.83/3.50  --time_out_real                         305.
% 23.83/3.50  --time_out_virtual                      -1.
% 23.83/3.50  --symbol_type_check                     false
% 23.83/3.50  --clausify_out                          false
% 23.83/3.50  --sig_cnt_out                           false
% 23.83/3.50  --trig_cnt_out                          false
% 23.83/3.50  --trig_cnt_out_tolerance                1.
% 23.83/3.50  --trig_cnt_out_sk_spl                   false
% 23.83/3.50  --abstr_cl_out                          false
% 23.83/3.50  
% 23.83/3.50  ------ Global Options
% 23.83/3.50  
% 23.83/3.50  --schedule                              default
% 23.83/3.50  --add_important_lit                     false
% 23.83/3.50  --prop_solver_per_cl                    1000
% 23.83/3.50  --min_unsat_core                        false
% 23.83/3.50  --soft_assumptions                      false
% 23.83/3.50  --soft_lemma_size                       3
% 23.83/3.50  --prop_impl_unit_size                   0
% 23.83/3.50  --prop_impl_unit                        []
% 23.83/3.50  --share_sel_clauses                     true
% 23.83/3.50  --reset_solvers                         false
% 23.83/3.50  --bc_imp_inh                            [conj_cone]
% 23.83/3.50  --conj_cone_tolerance                   3.
% 23.83/3.50  --extra_neg_conj                        none
% 23.83/3.50  --large_theory_mode                     true
% 23.83/3.50  --prolific_symb_bound                   200
% 23.83/3.50  --lt_threshold                          2000
% 23.83/3.50  --clause_weak_htbl                      true
% 23.83/3.50  --gc_record_bc_elim                     false
% 23.83/3.50  
% 23.83/3.50  ------ Preprocessing Options
% 23.83/3.50  
% 23.83/3.50  --preprocessing_flag                    true
% 23.83/3.50  --time_out_prep_mult                    0.1
% 23.83/3.50  --splitting_mode                        input
% 23.83/3.50  --splitting_grd                         true
% 23.83/3.50  --splitting_cvd                         false
% 23.83/3.50  --splitting_cvd_svl                     false
% 23.83/3.50  --splitting_nvd                         32
% 23.83/3.50  --sub_typing                            true
% 23.83/3.50  --prep_gs_sim                           true
% 23.83/3.50  --prep_unflatten                        true
% 23.83/3.50  --prep_res_sim                          true
% 23.83/3.50  --prep_upred                            true
% 23.83/3.50  --prep_sem_filter                       exhaustive
% 23.83/3.50  --prep_sem_filter_out                   false
% 23.83/3.50  --pred_elim                             true
% 23.83/3.50  --res_sim_input                         true
% 23.83/3.50  --eq_ax_congr_red                       true
% 23.83/3.50  --pure_diseq_elim                       true
% 23.83/3.50  --brand_transform                       false
% 23.83/3.50  --non_eq_to_eq                          false
% 23.83/3.50  --prep_def_merge                        true
% 23.83/3.50  --prep_def_merge_prop_impl              false
% 23.83/3.50  --prep_def_merge_mbd                    true
% 23.83/3.50  --prep_def_merge_tr_red                 false
% 23.83/3.50  --prep_def_merge_tr_cl                  false
% 23.83/3.50  --smt_preprocessing                     true
% 23.83/3.50  --smt_ac_axioms                         fast
% 23.83/3.50  --preprocessed_out                      false
% 23.83/3.50  --preprocessed_stats                    false
% 23.83/3.50  
% 23.83/3.50  ------ Abstraction refinement Options
% 23.83/3.50  
% 23.83/3.50  --abstr_ref                             []
% 23.83/3.50  --abstr_ref_prep                        false
% 23.83/3.50  --abstr_ref_until_sat                   false
% 23.83/3.50  --abstr_ref_sig_restrict                funpre
% 23.83/3.50  --abstr_ref_af_restrict_to_split_sk     false
% 23.83/3.50  --abstr_ref_under                       []
% 23.83/3.50  
% 23.83/3.50  ------ SAT Options
% 23.83/3.50  
% 23.83/3.50  --sat_mode                              false
% 23.83/3.50  --sat_fm_restart_options                ""
% 23.83/3.50  --sat_gr_def                            false
% 23.83/3.50  --sat_epr_types                         true
% 23.83/3.50  --sat_non_cyclic_types                  false
% 23.83/3.50  --sat_finite_models                     false
% 23.83/3.50  --sat_fm_lemmas                         false
% 23.83/3.50  --sat_fm_prep                           false
% 23.83/3.50  --sat_fm_uc_incr                        true
% 23.83/3.50  --sat_out_model                         small
% 23.83/3.50  --sat_out_clauses                       false
% 23.83/3.50  
% 23.83/3.50  ------ QBF Options
% 23.83/3.50  
% 23.83/3.50  --qbf_mode                              false
% 23.83/3.50  --qbf_elim_univ                         false
% 23.83/3.50  --qbf_dom_inst                          none
% 23.83/3.50  --qbf_dom_pre_inst                      false
% 23.83/3.50  --qbf_sk_in                             false
% 23.83/3.50  --qbf_pred_elim                         true
% 23.83/3.50  --qbf_split                             512
% 23.83/3.50  
% 23.83/3.50  ------ BMC1 Options
% 23.83/3.50  
% 23.83/3.50  --bmc1_incremental                      false
% 23.83/3.50  --bmc1_axioms                           reachable_all
% 23.83/3.50  --bmc1_min_bound                        0
% 23.83/3.50  --bmc1_max_bound                        -1
% 23.83/3.50  --bmc1_max_bound_default                -1
% 23.83/3.50  --bmc1_symbol_reachability              true
% 23.83/3.50  --bmc1_property_lemmas                  false
% 23.83/3.50  --bmc1_k_induction                      false
% 23.83/3.50  --bmc1_non_equiv_states                 false
% 23.83/3.50  --bmc1_deadlock                         false
% 23.83/3.50  --bmc1_ucm                              false
% 23.83/3.50  --bmc1_add_unsat_core                   none
% 23.83/3.50  --bmc1_unsat_core_children              false
% 23.83/3.50  --bmc1_unsat_core_extrapolate_axioms    false
% 23.83/3.50  --bmc1_out_stat                         full
% 23.83/3.50  --bmc1_ground_init                      false
% 23.83/3.50  --bmc1_pre_inst_next_state              false
% 23.83/3.50  --bmc1_pre_inst_state                   false
% 23.83/3.50  --bmc1_pre_inst_reach_state             false
% 23.83/3.50  --bmc1_out_unsat_core                   false
% 23.83/3.50  --bmc1_aig_witness_out                  false
% 23.83/3.50  --bmc1_verbose                          false
% 23.83/3.50  --bmc1_dump_clauses_tptp                false
% 23.83/3.50  --bmc1_dump_unsat_core_tptp             false
% 23.83/3.50  --bmc1_dump_file                        -
% 23.83/3.50  --bmc1_ucm_expand_uc_limit              128
% 23.83/3.50  --bmc1_ucm_n_expand_iterations          6
% 23.83/3.50  --bmc1_ucm_extend_mode                  1
% 23.83/3.50  --bmc1_ucm_init_mode                    2
% 23.83/3.50  --bmc1_ucm_cone_mode                    none
% 23.83/3.50  --bmc1_ucm_reduced_relation_type        0
% 23.83/3.50  --bmc1_ucm_relax_model                  4
% 23.83/3.50  --bmc1_ucm_full_tr_after_sat            true
% 23.83/3.50  --bmc1_ucm_expand_neg_assumptions       false
% 23.83/3.50  --bmc1_ucm_layered_model                none
% 23.83/3.50  --bmc1_ucm_max_lemma_size               10
% 23.83/3.50  
% 23.83/3.50  ------ AIG Options
% 23.83/3.50  
% 23.83/3.50  --aig_mode                              false
% 23.83/3.50  
% 23.83/3.50  ------ Instantiation Options
% 23.83/3.50  
% 23.83/3.50  --instantiation_flag                    true
% 23.83/3.50  --inst_sos_flag                         true
% 23.83/3.50  --inst_sos_phase                        true
% 23.83/3.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.83/3.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.83/3.50  --inst_lit_sel_side                     none
% 23.83/3.50  --inst_solver_per_active                1400
% 23.83/3.50  --inst_solver_calls_frac                1.
% 23.83/3.50  --inst_passive_queue_type               priority_queues
% 23.83/3.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.83/3.50  --inst_passive_queues_freq              [25;2]
% 23.83/3.50  --inst_dismatching                      true
% 23.83/3.50  --inst_eager_unprocessed_to_passive     true
% 23.83/3.50  --inst_prop_sim_given                   true
% 23.83/3.50  --inst_prop_sim_new                     false
% 23.83/3.50  --inst_subs_new                         false
% 23.83/3.50  --inst_eq_res_simp                      false
% 23.83/3.50  --inst_subs_given                       false
% 23.83/3.50  --inst_orphan_elimination               true
% 23.83/3.50  --inst_learning_loop_flag               true
% 23.83/3.50  --inst_learning_start                   3000
% 23.83/3.50  --inst_learning_factor                  2
% 23.83/3.50  --inst_start_prop_sim_after_learn       3
% 23.83/3.50  --inst_sel_renew                        solver
% 23.83/3.50  --inst_lit_activity_flag                true
% 23.83/3.50  --inst_restr_to_given                   false
% 23.83/3.50  --inst_activity_threshold               500
% 23.83/3.50  --inst_out_proof                        true
% 23.83/3.50  
% 23.83/3.50  ------ Resolution Options
% 23.83/3.50  
% 23.83/3.50  --resolution_flag                       false
% 23.83/3.50  --res_lit_sel                           adaptive
% 23.83/3.50  --res_lit_sel_side                      none
% 23.83/3.50  --res_ordering                          kbo
% 23.83/3.50  --res_to_prop_solver                    active
% 23.83/3.50  --res_prop_simpl_new                    false
% 23.83/3.50  --res_prop_simpl_given                  true
% 23.83/3.50  --res_passive_queue_type                priority_queues
% 23.83/3.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.83/3.50  --res_passive_queues_freq               [15;5]
% 23.83/3.50  --res_forward_subs                      full
% 23.83/3.50  --res_backward_subs                     full
% 23.83/3.50  --res_forward_subs_resolution           true
% 23.83/3.50  --res_backward_subs_resolution          true
% 23.83/3.50  --res_orphan_elimination                true
% 23.83/3.50  --res_time_limit                        2.
% 23.83/3.50  --res_out_proof                         true
% 23.83/3.50  
% 23.83/3.50  ------ Superposition Options
% 23.83/3.50  
% 23.83/3.50  --superposition_flag                    true
% 23.83/3.50  --sup_passive_queue_type                priority_queues
% 23.83/3.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.83/3.50  --sup_passive_queues_freq               [8;1;4]
% 23.83/3.50  --demod_completeness_check              fast
% 23.83/3.50  --demod_use_ground                      true
% 23.83/3.50  --sup_to_prop_solver                    passive
% 23.83/3.50  --sup_prop_simpl_new                    true
% 23.83/3.50  --sup_prop_simpl_given                  true
% 23.83/3.50  --sup_fun_splitting                     true
% 23.83/3.50  --sup_smt_interval                      50000
% 23.83/3.50  
% 23.83/3.50  ------ Superposition Simplification Setup
% 23.83/3.50  
% 23.83/3.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.83/3.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.83/3.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.83/3.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.83/3.50  --sup_full_triv                         [TrivRules;PropSubs]
% 23.83/3.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.83/3.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.83/3.50  --sup_immed_triv                        [TrivRules]
% 23.83/3.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.83/3.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.83/3.50  --sup_immed_bw_main                     []
% 23.83/3.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.83/3.50  --sup_input_triv                        [Unflattening;TrivRules]
% 23.83/3.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.83/3.50  --sup_input_bw                          []
% 23.83/3.50  
% 23.83/3.50  ------ Combination Options
% 23.83/3.50  
% 23.83/3.50  --comb_res_mult                         3
% 23.83/3.50  --comb_sup_mult                         2
% 23.83/3.50  --comb_inst_mult                        10
% 23.83/3.50  
% 23.83/3.50  ------ Debug Options
% 23.83/3.50  
% 23.83/3.50  --dbg_backtrace                         false
% 23.83/3.50  --dbg_dump_prop_clauses                 false
% 23.83/3.50  --dbg_dump_prop_clauses_file            -
% 23.83/3.50  --dbg_out_stat                          false
% 23.83/3.50  
% 23.83/3.50  
% 23.83/3.50  
% 23.83/3.50  
% 23.83/3.50  ------ Proving...
% 23.83/3.50  
% 23.83/3.50  
% 23.83/3.50  % SZS status Theorem for theBenchmark.p
% 23.83/3.50  
% 23.83/3.50  % SZS output start CNFRefutation for theBenchmark.p
% 23.83/3.50  
% 23.83/3.50  fof(f5,axiom,(
% 23.83/3.50    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 23.83/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.83/3.50  
% 23.83/3.50  fof(f13,plain,(
% 23.83/3.50    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 23.83/3.50    inference(ennf_transformation,[],[f5])).
% 23.83/3.50  
% 23.83/3.50  fof(f31,plain,(
% 23.83/3.50    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK4(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK4(X0,X1)) = X0 & v1_funct_1(sK4(X0,X1)) & v1_relat_1(sK4(X0,X1))))),
% 23.83/3.50    introduced(choice_axiom,[])).
% 23.83/3.50  
% 23.83/3.50  fof(f32,plain,(
% 23.83/3.50    ! [X0,X1] : (! [X3] : (k1_funct_1(sK4(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK4(X0,X1)) = X0 & v1_funct_1(sK4(X0,X1)) & v1_relat_1(sK4(X0,X1)))),
% 23.83/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f31])).
% 23.83/3.50  
% 23.83/3.50  fof(f51,plain,(
% 23.83/3.50    ( ! [X0,X1] : (k1_relat_1(sK4(X0,X1)) = X0) )),
% 23.83/3.50    inference(cnf_transformation,[],[f32])).
% 23.83/3.50  
% 23.83/3.50  fof(f4,axiom,(
% 23.83/3.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 23.83/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.83/3.50  
% 23.83/3.50  fof(f11,plain,(
% 23.83/3.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 23.83/3.50    inference(ennf_transformation,[],[f4])).
% 23.83/3.50  
% 23.83/3.50  fof(f12,plain,(
% 23.83/3.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 23.83/3.50    inference(flattening,[],[f11])).
% 23.83/3.50  
% 23.83/3.50  fof(f25,plain,(
% 23.83/3.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 23.83/3.50    inference(nnf_transformation,[],[f12])).
% 23.83/3.50  
% 23.83/3.50  fof(f26,plain,(
% 23.83/3.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 23.83/3.50    inference(rectify,[],[f25])).
% 23.83/3.50  
% 23.83/3.50  fof(f29,plain,(
% 23.83/3.50    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))))),
% 23.83/3.50    introduced(choice_axiom,[])).
% 23.83/3.50  
% 23.83/3.50  fof(f28,plain,(
% 23.83/3.50    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) = X2 & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))) )),
% 23.83/3.50    introduced(choice_axiom,[])).
% 23.83/3.50  
% 23.83/3.50  fof(f27,plain,(
% 23.83/3.50    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1))))),
% 23.83/3.50    introduced(choice_axiom,[])).
% 23.83/3.50  
% 23.83/3.50  fof(f30,plain,(
% 23.83/3.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & ((k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 23.83/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f26,f29,f28,f27])).
% 23.83/3.50  
% 23.83/3.50  fof(f46,plain,(
% 23.83/3.50    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) | r2_hidden(sK1(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 23.83/3.50    inference(cnf_transformation,[],[f30])).
% 23.83/3.50  
% 23.83/3.50  fof(f49,plain,(
% 23.83/3.50    ( ! [X0,X1] : (v1_relat_1(sK4(X0,X1))) )),
% 23.83/3.50    inference(cnf_transformation,[],[f32])).
% 23.83/3.50  
% 23.83/3.50  fof(f50,plain,(
% 23.83/3.50    ( ! [X0,X1] : (v1_funct_1(sK4(X0,X1))) )),
% 23.83/3.50    inference(cnf_transformation,[],[f32])).
% 23.83/3.50  
% 23.83/3.50  fof(f3,axiom,(
% 23.83/3.50    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k1_xboole_0 <=> k1_xboole_0 = k2_relat_1(X0)))),
% 23.83/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.83/3.50  
% 23.83/3.50  fof(f10,plain,(
% 23.83/3.50    ! [X0] : ((k1_relat_1(X0) = k1_xboole_0 <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 23.83/3.50    inference(ennf_transformation,[],[f3])).
% 23.83/3.50  
% 23.83/3.50  fof(f24,plain,(
% 23.83/3.50    ! [X0] : (((k1_relat_1(X0) = k1_xboole_0 | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 23.83/3.50    inference(nnf_transformation,[],[f10])).
% 23.83/3.50  
% 23.83/3.50  fof(f41,plain,(
% 23.83/3.50    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | ~v1_relat_1(X0)) )),
% 23.83/3.50    inference(cnf_transformation,[],[f24])).
% 23.83/3.50  
% 23.83/3.50  fof(f44,plain,(
% 23.83/3.50    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK3(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 23.83/3.50    inference(cnf_transformation,[],[f30])).
% 23.83/3.50  
% 23.83/3.50  fof(f60,plain,(
% 23.83/3.50    ( ! [X0,X5] : (k1_funct_1(X0,sK3(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 23.83/3.50    inference(equality_resolution,[],[f44])).
% 23.83/3.50  
% 23.83/3.50  fof(f1,axiom,(
% 23.83/3.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 23.83/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.83/3.50  
% 23.83/3.50  fof(f9,plain,(
% 23.83/3.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 23.83/3.50    inference(ennf_transformation,[],[f1])).
% 23.83/3.50  
% 23.83/3.50  fof(f18,plain,(
% 23.83/3.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 23.83/3.50    inference(nnf_transformation,[],[f9])).
% 23.83/3.50  
% 23.83/3.50  fof(f19,plain,(
% 23.83/3.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 23.83/3.50    inference(rectify,[],[f18])).
% 23.83/3.50  
% 23.83/3.50  fof(f20,plain,(
% 23.83/3.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 23.83/3.50    introduced(choice_axiom,[])).
% 23.83/3.50  
% 23.83/3.50  fof(f21,plain,(
% 23.83/3.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 23.83/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).
% 23.83/3.50  
% 23.83/3.50  fof(f36,plain,(
% 23.83/3.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 23.83/3.50    inference(cnf_transformation,[],[f21])).
% 23.83/3.50  
% 23.83/3.50  fof(f52,plain,(
% 23.83/3.50    ( ! [X0,X3,X1] : (k1_funct_1(sK4(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 23.83/3.50    inference(cnf_transformation,[],[f32])).
% 23.83/3.50  
% 23.83/3.50  fof(f43,plain,(
% 23.83/3.50    ( ! [X0,X5,X1] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 23.83/3.50    inference(cnf_transformation,[],[f30])).
% 23.83/3.50  
% 23.83/3.50  fof(f61,plain,(
% 23.83/3.50    ( ! [X0,X5] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 23.83/3.50    inference(equality_resolution,[],[f43])).
% 23.83/3.50  
% 23.83/3.50  fof(f35,plain,(
% 23.83/3.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 23.83/3.50    inference(cnf_transformation,[],[f21])).
% 23.83/3.50  
% 23.83/3.50  fof(f7,conjecture,(
% 23.83/3.50    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 23.83/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.83/3.50  
% 23.83/3.50  fof(f8,negated_conjecture,(
% 23.83/3.50    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 23.83/3.50    inference(negated_conjecture,[],[f7])).
% 23.83/3.50  
% 23.83/3.50  fof(f16,plain,(
% 23.83/3.50    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 23.83/3.50    inference(ennf_transformation,[],[f8])).
% 23.83/3.50  
% 23.83/3.50  fof(f17,plain,(
% 23.83/3.50    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 23.83/3.50    inference(flattening,[],[f16])).
% 23.83/3.50  
% 23.83/3.50  fof(f33,plain,(
% 23.83/3.50    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0)) => (! [X2] : (~r1_tarski(k2_relat_1(X2),sK5) | k1_relat_1(X2) != sK6 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK6 | k1_xboole_0 != sK5))),
% 23.83/3.50    introduced(choice_axiom,[])).
% 23.83/3.50  
% 23.83/3.50  fof(f34,plain,(
% 23.83/3.50    ! [X2] : (~r1_tarski(k2_relat_1(X2),sK5) | k1_relat_1(X2) != sK6 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK6 | k1_xboole_0 != sK5)),
% 23.83/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f17,f33])).
% 23.83/3.50  
% 23.83/3.50  fof(f55,plain,(
% 23.83/3.50    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK5) | k1_relat_1(X2) != sK6 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 23.83/3.50    inference(cnf_transformation,[],[f34])).
% 23.83/3.50  
% 23.83/3.50  fof(f6,axiom,(
% 23.83/3.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 23.83/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.83/3.50  
% 23.83/3.50  fof(f14,plain,(
% 23.83/3.50    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 23.83/3.50    inference(ennf_transformation,[],[f6])).
% 23.83/3.50  
% 23.83/3.50  fof(f15,plain,(
% 23.83/3.50    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 23.83/3.50    inference(flattening,[],[f14])).
% 23.83/3.50  
% 23.83/3.50  fof(f53,plain,(
% 23.83/3.50    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 23.83/3.50    inference(cnf_transformation,[],[f15])).
% 23.83/3.50  
% 23.83/3.50  fof(f37,plain,(
% 23.83/3.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 23.83/3.50    inference(cnf_transformation,[],[f21])).
% 23.83/3.50  
% 23.83/3.50  fof(f54,plain,(
% 23.83/3.50    k1_xboole_0 = sK6 | k1_xboole_0 != sK5),
% 23.83/3.50    inference(cnf_transformation,[],[f34])).
% 23.83/3.50  
% 23.83/3.50  fof(f2,axiom,(
% 23.83/3.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 23.83/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.83/3.50  
% 23.83/3.50  fof(f22,plain,(
% 23.83/3.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.83/3.50    inference(nnf_transformation,[],[f2])).
% 23.83/3.50  
% 23.83/3.50  fof(f23,plain,(
% 23.83/3.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.83/3.50    inference(flattening,[],[f22])).
% 23.83/3.50  
% 23.83/3.50  fof(f40,plain,(
% 23.83/3.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 23.83/3.50    inference(cnf_transformation,[],[f23])).
% 23.83/3.50  
% 23.83/3.50  fof(f39,plain,(
% 23.83/3.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 23.83/3.50    inference(cnf_transformation,[],[f23])).
% 23.83/3.50  
% 23.83/3.50  fof(f56,plain,(
% 23.83/3.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 23.83/3.50    inference(equality_resolution,[],[f39])).
% 23.83/3.50  
% 23.83/3.50  fof(f38,plain,(
% 23.83/3.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 23.83/3.50    inference(cnf_transformation,[],[f23])).
% 23.83/3.50  
% 23.83/3.50  fof(f57,plain,(
% 23.83/3.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 23.83/3.50    inference(equality_resolution,[],[f38])).
% 23.83/3.50  
% 23.83/3.50  cnf(c_15,plain,
% 23.83/3.50      ( k1_relat_1(sK4(X0,X1)) = X0 ),
% 23.83/3.50      inference(cnf_transformation,[],[f51]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_10,plain,
% 23.83/3.50      ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
% 23.83/3.50      | r2_hidden(sK1(X0,X1),X1)
% 23.83/3.50      | ~ v1_funct_1(X0)
% 23.83/3.50      | ~ v1_relat_1(X0)
% 23.83/3.50      | k2_relat_1(X0) = X1 ),
% 23.83/3.50      inference(cnf_transformation,[],[f46]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1197,plain,
% 23.83/3.50      ( k2_relat_1(X0) = X1
% 23.83/3.50      | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) = iProver_top
% 23.83/3.50      | r2_hidden(sK1(X0,X1),X1) = iProver_top
% 23.83/3.50      | v1_funct_1(X0) != iProver_top
% 23.83/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.83/3.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_17,plain,
% 23.83/3.50      ( v1_relat_1(sK4(X0,X1)) ),
% 23.83/3.50      inference(cnf_transformation,[],[f49]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1191,plain,
% 23.83/3.50      ( v1_relat_1(sK4(X0,X1)) = iProver_top ),
% 23.83/3.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_16,plain,
% 23.83/3.50      ( v1_funct_1(sK4(X0,X1)) ),
% 23.83/3.50      inference(cnf_transformation,[],[f50]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1192,plain,
% 23.83/3.50      ( v1_funct_1(sK4(X0,X1)) = iProver_top ),
% 23.83/3.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_7,plain,
% 23.83/3.50      ( ~ v1_relat_1(X0)
% 23.83/3.50      | k2_relat_1(X0) = k1_xboole_0
% 23.83/3.50      | k1_relat_1(X0) != k1_xboole_0 ),
% 23.83/3.50      inference(cnf_transformation,[],[f41]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1200,plain,
% 23.83/3.50      ( k2_relat_1(X0) = k1_xboole_0
% 23.83/3.50      | k1_relat_1(X0) != k1_xboole_0
% 23.83/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.83/3.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1657,plain,
% 23.83/3.50      ( k2_relat_1(sK4(X0,X1)) = k1_xboole_0
% 23.83/3.50      | k1_xboole_0 != X0
% 23.83/3.50      | v1_relat_1(sK4(X0,X1)) != iProver_top ),
% 23.83/3.50      inference(superposition,[status(thm)],[c_15,c_1200]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1658,plain,
% 23.83/3.50      ( ~ v1_relat_1(sK4(X0,X1))
% 23.83/3.50      | k2_relat_1(sK4(X0,X1)) = k1_xboole_0
% 23.83/3.50      | k1_xboole_0 != X0 ),
% 23.83/3.50      inference(predicate_to_equality_rev,[status(thm)],[c_1657]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1777,plain,
% 23.83/3.50      ( k1_xboole_0 != X0 | k2_relat_1(sK4(X0,X1)) = k1_xboole_0 ),
% 23.83/3.50      inference(global_propositional_subsumption,
% 23.83/3.50                [status(thm)],
% 23.83/3.50                [c_1657,c_17,c_1658]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1778,plain,
% 23.83/3.50      ( k2_relat_1(sK4(X0,X1)) = k1_xboole_0 | k1_xboole_0 != X0 ),
% 23.83/3.50      inference(renaming,[status(thm)],[c_1777]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1780,plain,
% 23.83/3.50      ( k2_relat_1(sK4(k1_xboole_0,X0)) = k1_xboole_0 ),
% 23.83/3.50      inference(equality_resolution,[status(thm)],[c_1778]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_12,plain,
% 23.83/3.50      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 23.83/3.50      | ~ v1_funct_1(X1)
% 23.83/3.50      | ~ v1_relat_1(X1)
% 23.83/3.50      | k1_funct_1(X1,sK3(X1,X0)) = X0 ),
% 23.83/3.50      inference(cnf_transformation,[],[f60]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1195,plain,
% 23.83/3.50      ( k1_funct_1(X0,sK3(X0,X1)) = X1
% 23.83/3.50      | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
% 23.83/3.50      | v1_funct_1(X0) != iProver_top
% 23.83/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.83/3.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1849,plain,
% 23.83/3.50      ( k1_funct_1(sK4(k1_xboole_0,X0),sK3(sK4(k1_xboole_0,X0),X1)) = X1
% 23.83/3.50      | r2_hidden(X1,k1_xboole_0) != iProver_top
% 23.83/3.50      | v1_funct_1(sK4(k1_xboole_0,X0)) != iProver_top
% 23.83/3.50      | v1_relat_1(sK4(k1_xboole_0,X0)) != iProver_top ),
% 23.83/3.50      inference(superposition,[status(thm)],[c_1780,c_1195]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_2506,plain,
% 23.83/3.50      ( k1_funct_1(sK4(k1_xboole_0,X0),sK3(sK4(k1_xboole_0,X0),X1)) = X1
% 23.83/3.50      | r2_hidden(X1,k1_xboole_0) != iProver_top
% 23.83/3.50      | v1_relat_1(sK4(k1_xboole_0,X0)) != iProver_top ),
% 23.83/3.50      inference(superposition,[status(thm)],[c_1192,c_1849]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_2511,plain,
% 23.83/3.50      ( k1_funct_1(sK4(k1_xboole_0,X0),sK3(sK4(k1_xboole_0,X0),X1)) = X1
% 23.83/3.50      | r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 23.83/3.50      inference(superposition,[status(thm)],[c_1191,c_2506]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_2598,plain,
% 23.83/3.50      ( k1_funct_1(sK4(k1_xboole_0,X0),sK3(sK4(k1_xboole_0,X0),sK1(X1,k1_xboole_0))) = sK1(X1,k1_xboole_0)
% 23.83/3.50      | k2_relat_1(X1) = k1_xboole_0
% 23.83/3.50      | r2_hidden(sK2(X1,k1_xboole_0),k1_relat_1(X1)) = iProver_top
% 23.83/3.50      | v1_funct_1(X1) != iProver_top
% 23.83/3.50      | v1_relat_1(X1) != iProver_top ),
% 23.83/3.50      inference(superposition,[status(thm)],[c_1197,c_2511]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1,plain,
% 23.83/3.50      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 23.83/3.50      inference(cnf_transformation,[],[f36]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1205,plain,
% 23.83/3.50      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 23.83/3.50      | r1_tarski(X0,X1) = iProver_top ),
% 23.83/3.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_14,plain,
% 23.83/3.50      ( ~ r2_hidden(X0,X1) | k1_funct_1(sK4(X1,X2),X0) = X2 ),
% 23.83/3.50      inference(cnf_transformation,[],[f52]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1193,plain,
% 23.83/3.50      ( k1_funct_1(sK4(X0,X1),X2) = X1
% 23.83/3.50      | r2_hidden(X2,X0) != iProver_top ),
% 23.83/3.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1593,plain,
% 23.83/3.50      ( k1_funct_1(sK4(X0,X1),sK0(X0,X2)) = X1
% 23.83/3.50      | r1_tarski(X0,X2) = iProver_top ),
% 23.83/3.50      inference(superposition,[status(thm)],[c_1205,c_1193]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_13,plain,
% 23.83/3.50      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 23.83/3.50      | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
% 23.83/3.50      | ~ v1_funct_1(X1)
% 23.83/3.50      | ~ v1_relat_1(X1) ),
% 23.83/3.50      inference(cnf_transformation,[],[f61]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1194,plain,
% 23.83/3.50      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 23.83/3.50      | r2_hidden(sK3(X1,X0),k1_relat_1(X1)) = iProver_top
% 23.83/3.50      | v1_funct_1(X1) != iProver_top
% 23.83/3.50      | v1_relat_1(X1) != iProver_top ),
% 23.83/3.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_2,plain,
% 23.83/3.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 23.83/3.50      inference(cnf_transformation,[],[f35]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1204,plain,
% 23.83/3.50      ( r2_hidden(X0,X1) != iProver_top
% 23.83/3.50      | r2_hidden(X0,X2) = iProver_top
% 23.83/3.50      | r1_tarski(X1,X2) != iProver_top ),
% 23.83/3.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1709,plain,
% 23.83/3.50      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 23.83/3.50      | r2_hidden(sK3(X1,X0),X2) = iProver_top
% 23.83/3.50      | r1_tarski(k1_relat_1(X1),X2) != iProver_top
% 23.83/3.50      | v1_funct_1(X1) != iProver_top
% 23.83/3.50      | v1_relat_1(X1) != iProver_top ),
% 23.83/3.50      inference(superposition,[status(thm)],[c_1194,c_1204]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1848,plain,
% 23.83/3.50      ( k1_funct_1(X0,sK3(X0,sK0(k2_relat_1(X0),X1))) = sK0(k2_relat_1(X0),X1)
% 23.83/3.50      | r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 23.83/3.50      | v1_funct_1(X0) != iProver_top
% 23.83/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.83/3.50      inference(superposition,[status(thm)],[c_1205,c_1195]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_19,negated_conjecture,
% 23.83/3.50      ( ~ r1_tarski(k2_relat_1(X0),sK5)
% 23.83/3.50      | ~ v1_funct_1(X0)
% 23.83/3.50      | ~ v1_relat_1(X0)
% 23.83/3.50      | k1_relat_1(X0) != sK6 ),
% 23.83/3.50      inference(cnf_transformation,[],[f55]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1190,plain,
% 23.83/3.50      ( k1_relat_1(X0) != sK6
% 23.83/3.50      | r1_tarski(k2_relat_1(X0),sK5) != iProver_top
% 23.83/3.50      | v1_funct_1(X0) != iProver_top
% 23.83/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.83/3.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1331,plain,
% 23.83/3.50      ( sK6 != X0
% 23.83/3.50      | r1_tarski(k2_relat_1(sK4(X0,X1)),sK5) != iProver_top
% 23.83/3.50      | v1_funct_1(sK4(X0,X1)) != iProver_top
% 23.83/3.50      | v1_relat_1(sK4(X0,X1)) != iProver_top ),
% 23.83/3.50      inference(superposition,[status(thm)],[c_15,c_1190]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_27,plain,
% 23.83/3.50      ( v1_relat_1(sK4(X0,X1)) = iProver_top ),
% 23.83/3.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_30,plain,
% 23.83/3.50      ( v1_funct_1(sK4(X0,X1)) = iProver_top ),
% 23.83/3.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1374,plain,
% 23.83/3.50      ( sK6 != X0
% 23.83/3.50      | r1_tarski(k2_relat_1(sK4(X0,X1)),sK5) != iProver_top ),
% 23.83/3.50      inference(global_propositional_subsumption,
% 23.83/3.50                [status(thm)],
% 23.83/3.50                [c_1331,c_27,c_30]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1380,plain,
% 23.83/3.50      ( r1_tarski(k2_relat_1(sK4(sK6,X0)),sK5) != iProver_top ),
% 23.83/3.50      inference(equality_resolution,[status(thm)],[c_1374]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_5201,plain,
% 23.83/3.50      ( k1_funct_1(sK4(sK6,X0),sK3(sK4(sK6,X0),sK0(k2_relat_1(sK4(sK6,X0)),sK5))) = sK0(k2_relat_1(sK4(sK6,X0)),sK5)
% 23.83/3.50      | v1_funct_1(sK4(sK6,X0)) != iProver_top
% 23.83/3.50      | v1_relat_1(sK4(sK6,X0)) != iProver_top ),
% 23.83/3.50      inference(superposition,[status(thm)],[c_1848,c_1380]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1335,plain,
% 23.83/3.50      ( v1_funct_1(sK4(sK6,X0)) ),
% 23.83/3.50      inference(instantiation,[status(thm)],[c_16]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1336,plain,
% 23.83/3.50      ( v1_funct_1(sK4(sK6,X0)) = iProver_top ),
% 23.83/3.50      inference(predicate_to_equality,[status(thm)],[c_1335]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1392,plain,
% 23.83/3.50      ( v1_relat_1(sK4(sK6,X0)) ),
% 23.83/3.50      inference(instantiation,[status(thm)],[c_17]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1393,plain,
% 23.83/3.50      ( v1_relat_1(sK4(sK6,X0)) = iProver_top ),
% 23.83/3.50      inference(predicate_to_equality,[status(thm)],[c_1392]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_5790,plain,
% 23.83/3.50      ( k1_funct_1(sK4(sK6,X0),sK3(sK4(sK6,X0),sK0(k2_relat_1(sK4(sK6,X0)),sK5))) = sK0(k2_relat_1(sK4(sK6,X0)),sK5) ),
% 23.83/3.50      inference(global_propositional_subsumption,
% 23.83/3.50                [status(thm)],
% 23.83/3.50                [c_5201,c_1336,c_1393]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_18,plain,
% 23.83/3.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 23.83/3.50      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 23.83/3.50      | ~ v1_funct_1(X1)
% 23.83/3.50      | ~ v1_relat_1(X1) ),
% 23.83/3.50      inference(cnf_transformation,[],[f53]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1196,plain,
% 23.83/3.50      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 23.83/3.50      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 23.83/3.50      | v1_funct_1(X1) != iProver_top
% 23.83/3.50      | v1_relat_1(X1) != iProver_top ),
% 23.83/3.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_5794,plain,
% 23.83/3.50      ( r2_hidden(sK3(sK4(sK6,X0),sK0(k2_relat_1(sK4(sK6,X0)),sK5)),k1_relat_1(sK4(sK6,X0))) != iProver_top
% 23.83/3.50      | r2_hidden(sK0(k2_relat_1(sK4(sK6,X0)),sK5),k2_relat_1(sK4(sK6,X0))) = iProver_top
% 23.83/3.50      | v1_funct_1(sK4(sK6,X0)) != iProver_top
% 23.83/3.50      | v1_relat_1(sK4(sK6,X0)) != iProver_top ),
% 23.83/3.50      inference(superposition,[status(thm)],[c_5790,c_1196]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_5795,plain,
% 23.83/3.50      ( r2_hidden(sK3(sK4(sK6,X0),sK0(k2_relat_1(sK4(sK6,X0)),sK5)),sK6) != iProver_top
% 23.83/3.50      | r2_hidden(sK0(k2_relat_1(sK4(sK6,X0)),sK5),k2_relat_1(sK4(sK6,X0))) = iProver_top
% 23.83/3.50      | v1_funct_1(sK4(sK6,X0)) != iProver_top
% 23.83/3.50      | v1_relat_1(sK4(sK6,X0)) != iProver_top ),
% 23.83/3.50      inference(demodulation,[status(thm)],[c_5794,c_15]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1290,plain,
% 23.83/3.50      ( r2_hidden(sK0(X0,sK5),X0) | r1_tarski(X0,sK5) ),
% 23.83/3.50      inference(instantiation,[status(thm)],[c_1]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1472,plain,
% 23.83/3.50      ( r2_hidden(sK0(k2_relat_1(sK4(sK6,X0)),sK5),k2_relat_1(sK4(sK6,X0)))
% 23.83/3.50      | r1_tarski(k2_relat_1(sK4(sK6,X0)),sK5) ),
% 23.83/3.50      inference(instantiation,[status(thm)],[c_1290]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1478,plain,
% 23.83/3.50      ( r2_hidden(sK0(k2_relat_1(sK4(sK6,X0)),sK5),k2_relat_1(sK4(sK6,X0))) = iProver_top
% 23.83/3.50      | r1_tarski(k2_relat_1(sK4(sK6,X0)),sK5) = iProver_top ),
% 23.83/3.50      inference(predicate_to_equality,[status(thm)],[c_1472]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_5804,plain,
% 23.83/3.50      ( r2_hidden(sK0(k2_relat_1(sK4(sK6,X0)),sK5),k2_relat_1(sK4(sK6,X0))) = iProver_top ),
% 23.83/3.50      inference(global_propositional_subsumption,
% 23.83/3.50                [status(thm)],
% 23.83/3.50                [c_5795,c_1380,c_1478]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1594,plain,
% 23.83/3.50      ( k1_funct_1(sK4(k1_relat_1(X0),X1),sK3(X0,X2)) = X1
% 23.83/3.50      | r2_hidden(X2,k2_relat_1(X0)) != iProver_top
% 23.83/3.50      | v1_funct_1(X0) != iProver_top
% 23.83/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.83/3.50      inference(superposition,[status(thm)],[c_1194,c_1193]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_5815,plain,
% 23.83/3.50      ( k1_funct_1(sK4(k1_relat_1(sK4(sK6,X0)),X1),sK3(sK4(sK6,X0),sK0(k2_relat_1(sK4(sK6,X0)),sK5))) = X1
% 23.83/3.50      | v1_funct_1(sK4(sK6,X0)) != iProver_top
% 23.83/3.50      | v1_relat_1(sK4(sK6,X0)) != iProver_top ),
% 23.83/3.50      inference(superposition,[status(thm)],[c_5804,c_1594]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_5819,plain,
% 23.83/3.50      ( k1_funct_1(sK4(sK6,X0),sK3(sK4(sK6,X1),sK0(k2_relat_1(sK4(sK6,X1)),sK5))) = X0
% 23.83/3.50      | v1_funct_1(sK4(sK6,X1)) != iProver_top
% 23.83/3.50      | v1_relat_1(sK4(sK6,X1)) != iProver_top ),
% 23.83/3.50      inference(demodulation,[status(thm)],[c_5815,c_15]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_6560,plain,
% 23.83/3.50      ( k1_funct_1(sK4(sK6,X0),sK3(sK4(sK6,X1),sK0(k2_relat_1(sK4(sK6,X1)),sK5))) = X0
% 23.83/3.50      | v1_relat_1(sK4(sK6,X1)) != iProver_top ),
% 23.83/3.50      inference(superposition,[status(thm)],[c_1192,c_5819]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_7954,plain,
% 23.83/3.50      ( k1_funct_1(sK4(sK6,X0),sK3(sK4(sK6,X1),sK0(k2_relat_1(sK4(sK6,X1)),sK5))) = X0 ),
% 23.83/3.50      inference(superposition,[status(thm)],[c_1191,c_6560]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_8154,plain,
% 23.83/3.50      ( sK0(k2_relat_1(sK4(sK6,X0)),sK5) = X0 ),
% 23.83/3.50      inference(demodulation,[status(thm)],[c_7954,c_5790]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_0,plain,
% 23.83/3.50      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 23.83/3.50      inference(cnf_transformation,[],[f37]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1206,plain,
% 23.83/3.50      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 23.83/3.50      | r1_tarski(X0,X1) = iProver_top ),
% 23.83/3.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_8561,plain,
% 23.83/3.50      ( r2_hidden(X0,sK5) != iProver_top
% 23.83/3.50      | r1_tarski(k2_relat_1(sK4(sK6,X0)),sK5) = iProver_top ),
% 23.83/3.50      inference(superposition,[status(thm)],[c_8154,c_1206]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_8849,plain,
% 23.83/3.50      ( r2_hidden(X0,sK5) != iProver_top ),
% 23.83/3.50      inference(global_propositional_subsumption,
% 23.83/3.50                [status(thm)],
% 23.83/3.50                [c_8561,c_1380]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_8861,plain,
% 23.83/3.50      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 23.83/3.50      | r1_tarski(k1_relat_1(X1),sK5) != iProver_top
% 23.83/3.50      | v1_funct_1(X1) != iProver_top
% 23.83/3.50      | v1_relat_1(X1) != iProver_top ),
% 23.83/3.50      inference(superposition,[status(thm)],[c_1709,c_8849]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_11727,plain,
% 23.83/3.50      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 23.83/3.50      | r1_tarski(k1_relat_1(sK4(k1_xboole_0,X1)),sK5) != iProver_top
% 23.83/3.50      | v1_funct_1(sK4(k1_xboole_0,X1)) != iProver_top
% 23.83/3.50      | v1_relat_1(sK4(k1_xboole_0,X1)) != iProver_top ),
% 23.83/3.50      inference(superposition,[status(thm)],[c_1780,c_8861]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_11728,plain,
% 23.83/3.50      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 23.83/3.50      | r1_tarski(k1_xboole_0,sK5) != iProver_top
% 23.83/3.50      | v1_funct_1(sK4(k1_xboole_0,X1)) != iProver_top
% 23.83/3.50      | v1_relat_1(sK4(k1_xboole_0,X1)) != iProver_top ),
% 23.83/3.50      inference(demodulation,[status(thm)],[c_11727,c_15]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_20,negated_conjecture,
% 23.83/3.50      ( k1_xboole_0 = sK6 | k1_xboole_0 != sK5 ),
% 23.83/3.50      inference(cnf_transformation,[],[f54]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_3,plain,
% 23.83/3.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 23.83/3.50      inference(cnf_transformation,[],[f40]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1225,plain,
% 23.83/3.50      ( ~ r1_tarski(sK5,k1_xboole_0)
% 23.83/3.50      | ~ r1_tarski(k1_xboole_0,sK5)
% 23.83/3.50      | k1_xboole_0 = sK5 ),
% 23.83/3.50      inference(instantiation,[status(thm)],[c_3]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1226,plain,
% 23.83/3.50      ( k1_xboole_0 = sK5
% 23.83/3.50      | r1_tarski(sK5,k1_xboole_0) != iProver_top
% 23.83/3.50      | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
% 23.83/3.50      inference(predicate_to_equality,[status(thm)],[c_1225]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1249,plain,
% 23.83/3.50      ( ~ r1_tarski(X0,sK5) | ~ r1_tarski(sK5,X0) | sK5 = X0 ),
% 23.83/3.50      inference(instantiation,[status(thm)],[c_3]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1295,plain,
% 23.83/3.50      ( ~ r1_tarski(sK5,sK5) | sK5 = sK5 ),
% 23.83/3.50      inference(instantiation,[status(thm)],[c_1249]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_4,plain,
% 23.83/3.50      ( r1_tarski(X0,X0) ),
% 23.83/3.50      inference(cnf_transformation,[],[f56]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1342,plain,
% 23.83/3.50      ( r1_tarski(sK5,sK5) ),
% 23.83/3.50      inference(instantiation,[status(thm)],[c_4]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_899,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1372,plain,
% 23.83/3.50      ( X0 != X1 | sK6 != X1 | sK6 = X0 ),
% 23.83/3.50      inference(instantiation,[status(thm)],[c_899]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1653,plain,
% 23.83/3.50      ( X0 != sK6 | sK6 = X0 | sK6 != sK6 ),
% 23.83/3.50      inference(instantiation,[status(thm)],[c_1372]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1654,plain,
% 23.83/3.50      ( sK6 != sK6 | sK6 = k1_xboole_0 | k1_xboole_0 != sK6 ),
% 23.83/3.50      inference(instantiation,[status(thm)],[c_1653]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_898,plain,( X0 = X0 ),theory(equality) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1922,plain,
% 23.83/3.50      ( sK6 = sK6 ),
% 23.83/3.50      inference(instantiation,[status(thm)],[c_898]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_900,plain,
% 23.83/3.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.83/3.50      theory(equality) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1977,plain,
% 23.83/3.50      ( ~ r1_tarski(X0,X1) | r1_tarski(sK6,X2) | X2 != X1 | sK6 != X0 ),
% 23.83/3.50      inference(instantiation,[status(thm)],[c_900]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_2481,plain,
% 23.83/3.50      ( ~ r1_tarski(X0,X1) | r1_tarski(sK6,sK5) | sK6 != X0 | sK5 != X1 ),
% 23.83/3.50      inference(instantiation,[status(thm)],[c_1977]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_4667,plain,
% 23.83/3.50      ( ~ r1_tarski(X0,sK5)
% 23.83/3.50      | r1_tarski(sK6,sK5)
% 23.83/3.50      | sK6 != X0
% 23.83/3.50      | sK5 != sK5 ),
% 23.83/3.50      inference(instantiation,[status(thm)],[c_2481]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_4668,plain,
% 23.83/3.50      ( sK6 != X0
% 23.83/3.50      | sK5 != sK5
% 23.83/3.50      | r1_tarski(X0,sK5) != iProver_top
% 23.83/3.50      | r1_tarski(sK6,sK5) = iProver_top ),
% 23.83/3.50      inference(predicate_to_equality,[status(thm)],[c_4667]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_4670,plain,
% 23.83/3.50      ( sK6 != k1_xboole_0
% 23.83/3.50      | sK5 != sK5
% 23.83/3.50      | r1_tarski(sK6,sK5) = iProver_top
% 23.83/3.50      | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
% 23.83/3.50      inference(instantiation,[status(thm)],[c_4668]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_8855,plain,
% 23.83/3.50      ( r1_tarski(sK5,X0) = iProver_top ),
% 23.83/3.50      inference(superposition,[status(thm)],[c_1205,c_8849]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_8866,plain,
% 23.83/3.50      ( r1_tarski(sK5,k1_xboole_0) = iProver_top ),
% 23.83/3.50      inference(instantiation,[status(thm)],[c_8855]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_8487,plain,
% 23.83/3.50      ( r2_hidden(X0,k2_relat_1(sK4(sK6,X0))) = iProver_top ),
% 23.83/3.50      inference(demodulation,[status(thm)],[c_8154,c_5804]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_11726,plain,
% 23.83/3.50      ( r1_tarski(k1_relat_1(sK4(sK6,X0)),sK5) != iProver_top
% 23.83/3.50      | v1_funct_1(sK4(sK6,X0)) != iProver_top
% 23.83/3.50      | v1_relat_1(sK4(sK6,X0)) != iProver_top ),
% 23.83/3.50      inference(superposition,[status(thm)],[c_8487,c_8861]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_11729,plain,
% 23.83/3.50      ( r1_tarski(sK6,sK5) != iProver_top
% 23.83/3.50      | v1_funct_1(sK4(sK6,X0)) != iProver_top
% 23.83/3.50      | v1_relat_1(sK4(sK6,X0)) != iProver_top ),
% 23.83/3.50      inference(demodulation,[status(thm)],[c_11726,c_15]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_12579,plain,
% 23.83/3.50      ( r1_tarski(k1_xboole_0,sK5) != iProver_top ),
% 23.83/3.50      inference(global_propositional_subsumption,
% 23.83/3.50                [status(thm)],
% 23.83/3.50                [c_11728,c_20,c_1226,c_1295,c_1336,c_1342,c_1393,c_1654,
% 23.83/3.50                 c_1922,c_4670,c_8866,c_11729]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_12583,plain,
% 23.83/3.50      ( k1_funct_1(sK4(k1_xboole_0,X0),sK0(k1_xboole_0,sK5)) = X0 ),
% 23.83/3.50      inference(superposition,[status(thm)],[c_1593,c_12579]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1858,plain,
% 23.83/3.50      ( k1_funct_1(sK4(k2_relat_1(X0),X1),k1_funct_1(X0,X2)) = X1
% 23.83/3.50      | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
% 23.83/3.50      | v1_funct_1(X0) != iProver_top
% 23.83/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.83/3.50      inference(superposition,[status(thm)],[c_1196,c_1193]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_2239,plain,
% 23.83/3.50      ( k1_funct_1(sK4(k2_relat_1(sK4(X0,X1)),X2),k1_funct_1(sK4(X0,X1),X3)) = X2
% 23.83/3.50      | r2_hidden(X3,X0) != iProver_top
% 23.83/3.50      | v1_funct_1(sK4(X0,X1)) != iProver_top
% 23.83/3.50      | v1_relat_1(sK4(X0,X1)) != iProver_top ),
% 23.83/3.50      inference(superposition,[status(thm)],[c_15,c_1858]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_2744,plain,
% 23.83/3.50      ( k1_funct_1(sK4(k2_relat_1(sK4(X0,X1)),X2),k1_funct_1(sK4(X0,X1),X3)) = X2
% 23.83/3.50      | r2_hidden(X3,X0) != iProver_top ),
% 23.83/3.50      inference(global_propositional_subsumption,
% 23.83/3.50                [status(thm)],
% 23.83/3.50                [c_2239,c_27,c_30]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_2750,plain,
% 23.83/3.50      ( k1_funct_1(sK4(k2_relat_1(sK4(X0,X1)),X2),k1_funct_1(sK4(X0,X1),sK0(X0,X3))) = X2
% 23.83/3.50      | r1_tarski(X0,X3) = iProver_top ),
% 23.83/3.50      inference(superposition,[status(thm)],[c_1205,c_2744]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_12585,plain,
% 23.83/3.50      ( k1_funct_1(sK4(k2_relat_1(sK4(k1_xboole_0,X0)),X1),k1_funct_1(sK4(k1_xboole_0,X0),sK0(k1_xboole_0,sK5))) = X1 ),
% 23.83/3.50      inference(superposition,[status(thm)],[c_2750,c_12579]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_12586,plain,
% 23.83/3.50      ( k1_funct_1(sK4(k1_xboole_0,X0),k1_funct_1(sK4(k1_xboole_0,X1),sK0(k1_xboole_0,sK5))) = X0 ),
% 23.83/3.50      inference(light_normalisation,[status(thm)],[c_12585,c_1780]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_12587,plain,
% 23.83/3.50      ( k1_funct_1(sK4(k1_xboole_0,X0),X1) = X0 ),
% 23.83/3.50      inference(demodulation,[status(thm)],[c_12583,c_12586]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_55132,plain,
% 23.83/3.50      ( sK1(X0,k1_xboole_0) = X1
% 23.83/3.50      | k2_relat_1(X0) = k1_xboole_0
% 23.83/3.50      | r2_hidden(sK2(X0,k1_xboole_0),k1_relat_1(X0)) = iProver_top
% 23.83/3.50      | v1_funct_1(X0) != iProver_top
% 23.83/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.83/3.50      inference(demodulation,[status(thm)],[c_2598,c_12587]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_55136,plain,
% 23.83/3.50      ( sK1(sK4(X0,X1),k1_xboole_0) = X2
% 23.83/3.50      | k2_relat_1(sK4(X0,X1)) = k1_xboole_0
% 23.83/3.50      | r2_hidden(sK2(sK4(X0,X1),k1_xboole_0),X0) = iProver_top
% 23.83/3.50      | v1_funct_1(sK4(X0,X1)) != iProver_top
% 23.83/3.50      | v1_relat_1(sK4(X0,X1)) != iProver_top ),
% 23.83/3.50      inference(superposition,[status(thm)],[c_15,c_55132]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_55167,plain,
% 23.83/3.50      ( sK1(sK4(X0,X1),k1_xboole_0) = X2
% 23.83/3.50      | k2_relat_1(sK4(X0,X1)) = k1_xboole_0
% 23.83/3.50      | r2_hidden(sK2(sK4(X0,X1),k1_xboole_0),X0) = iProver_top ),
% 23.83/3.50      inference(global_propositional_subsumption,
% 23.83/3.50                [status(thm)],
% 23.83/3.50                [c_55136,c_27,c_30]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_55187,plain,
% 23.83/3.50      ( sK1(sK4(sK5,X0),k1_xboole_0) = X1
% 23.83/3.50      | k2_relat_1(sK4(sK5,X0)) = k1_xboole_0 ),
% 23.83/3.50      inference(superposition,[status(thm)],[c_55167,c_8849]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1925,plain,
% 23.83/3.50      ( k2_relat_1(sK4(X0,X1)) = X2
% 23.83/3.50      | r2_hidden(sK2(sK4(X0,X1),X2),X0) = iProver_top
% 23.83/3.50      | r2_hidden(sK1(sK4(X0,X1),X2),X2) = iProver_top
% 23.83/3.50      | v1_funct_1(sK4(X0,X1)) != iProver_top
% 23.83/3.50      | v1_relat_1(sK4(X0,X1)) != iProver_top ),
% 23.83/3.50      inference(superposition,[status(thm)],[c_15,c_1197]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_2846,plain,
% 23.83/3.50      ( k2_relat_1(sK4(X0,X1)) = X2
% 23.83/3.50      | r2_hidden(sK2(sK4(X0,X1),X2),X0) = iProver_top
% 23.83/3.50      | r2_hidden(sK1(sK4(X0,X1),X2),X2) = iProver_top ),
% 23.83/3.50      inference(global_propositional_subsumption,
% 23.83/3.50                [status(thm)],
% 23.83/3.50                [c_1925,c_27,c_30]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_8858,plain,
% 23.83/3.50      ( k2_relat_1(sK4(X0,X1)) = sK5
% 23.83/3.50      | r2_hidden(sK2(sK4(X0,X1),sK5),X0) = iProver_top ),
% 23.83/3.50      inference(superposition,[status(thm)],[c_2846,c_8849]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_11913,plain,
% 23.83/3.50      ( k2_relat_1(sK4(sK5,X0)) = sK5 ),
% 23.83/3.50      inference(superposition,[status(thm)],[c_8858,c_8849]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_55199,plain,
% 23.83/3.50      ( sK1(sK4(sK5,X0),k1_xboole_0) = X1 | sK5 = k1_xboole_0 ),
% 23.83/3.50      inference(demodulation,[status(thm)],[c_55187,c_11913]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_5,plain,
% 23.83/3.50      ( r1_tarski(X0,X0) ),
% 23.83/3.50      inference(cnf_transformation,[],[f57]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_60,plain,
% 23.83/3.50      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 23.83/3.50      inference(instantiation,[status(thm)],[c_5]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_59,plain,
% 23.83/3.50      ( r1_tarski(X0,X0) = iProver_top ),
% 23.83/3.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_61,plain,
% 23.83/3.50      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 23.83/3.50      inference(instantiation,[status(thm)],[c_59]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_64,plain,
% 23.83/3.50      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 23.83/3.50      | k1_xboole_0 = k1_xboole_0 ),
% 23.83/3.50      inference(instantiation,[status(thm)],[c_3]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1284,plain,
% 23.83/3.50      ( ~ r1_tarski(X0,X1)
% 23.83/3.50      | r1_tarski(k1_xboole_0,sK5)
% 23.83/3.50      | sK5 != X1
% 23.83/3.50      | k1_xboole_0 != X0 ),
% 23.83/3.50      inference(instantiation,[status(thm)],[c_900]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1285,plain,
% 23.83/3.50      ( sK5 != X0
% 23.83/3.50      | k1_xboole_0 != X1
% 23.83/3.50      | r1_tarski(X1,X0) != iProver_top
% 23.83/3.50      | r1_tarski(k1_xboole_0,sK5) = iProver_top ),
% 23.83/3.50      inference(predicate_to_equality,[status(thm)],[c_1284]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_1287,plain,
% 23.83/3.50      ( sK5 != k1_xboole_0
% 23.83/3.50      | k1_xboole_0 != k1_xboole_0
% 23.83/3.50      | r1_tarski(k1_xboole_0,sK5) = iProver_top
% 23.83/3.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 23.83/3.50      inference(instantiation,[status(thm)],[c_1285]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_73921,plain,
% 23.83/3.50      ( sK1(sK4(sK5,X0),k1_xboole_0) = X1 ),
% 23.83/3.50      inference(global_propositional_subsumption,
% 23.83/3.50                [status(thm)],
% 23.83/3.50                [c_55199,c_20,c_60,c_61,c_64,c_1226,c_1287,c_1295,c_1336,
% 23.83/3.50                 c_1342,c_1393,c_1654,c_1922,c_4670,c_8866,c_11729]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_74888,plain,
% 23.83/3.50      ( k1_relat_1(sK1(sK4(sK5,X0),k1_xboole_0)) = X1 ),
% 23.83/3.50      inference(superposition,[status(thm)],[c_73921,c_15]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_75538,plain,
% 23.83/3.50      ( k2_relat_1(k1_relat_1(sK1(sK4(sK5,X0),k1_xboole_0))) = k1_xboole_0 ),
% 23.83/3.50      inference(superposition,[status(thm)],[c_74888,c_1780]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_75551,plain,
% 23.83/3.50      ( k2_relat_1(k1_relat_1(sK1(sK4(sK5,X0),k1_xboole_0))) = sK5 ),
% 23.83/3.50      inference(superposition,[status(thm)],[c_74888,c_11913]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(c_75740,plain,
% 23.83/3.50      ( sK5 = k1_xboole_0 ),
% 23.83/3.50      inference(demodulation,[status(thm)],[c_75538,c_75551]) ).
% 23.83/3.50  
% 23.83/3.50  cnf(contradiction,plain,
% 23.83/3.50      ( $false ),
% 23.83/3.50      inference(minisat,
% 23.83/3.50                [status(thm)],
% 23.83/3.50                [c_75740,c_12579,c_1287,c_64,c_61,c_60]) ).
% 23.83/3.50  
% 23.83/3.50  
% 23.83/3.50  % SZS output end CNFRefutation for theBenchmark.p
% 23.83/3.50  
% 23.83/3.50  ------                               Statistics
% 23.83/3.50  
% 23.83/3.50  ------ General
% 23.83/3.50  
% 23.83/3.50  abstr_ref_over_cycles:                  0
% 23.83/3.50  abstr_ref_under_cycles:                 0
% 23.83/3.50  gc_basic_clause_elim:                   0
% 23.83/3.50  forced_gc_time:                         0
% 23.83/3.50  parsing_time:                           0.008
% 23.83/3.50  unif_index_cands_time:                  0.
% 23.83/3.50  unif_index_add_time:                    0.
% 23.83/3.50  orderings_time:                         0.
% 23.83/3.50  out_proof_time:                         0.019
% 23.83/3.50  total_time:                             2.995
% 23.83/3.50  num_of_symbols:                         47
% 23.83/3.50  num_of_terms:                           82759
% 23.83/3.50  
% 23.83/3.50  ------ Preprocessing
% 23.83/3.50  
% 23.83/3.50  num_of_splits:                          0
% 23.83/3.50  num_of_split_atoms:                     1
% 23.83/3.50  num_of_reused_defs:                     14
% 23.83/3.50  num_eq_ax_congr_red:                    33
% 23.83/3.50  num_of_sem_filtered_clauses:            1
% 23.83/3.50  num_of_subtypes:                        0
% 23.83/3.50  monotx_restored_types:                  0
% 23.83/3.50  sat_num_of_epr_types:                   0
% 23.83/3.50  sat_num_of_non_cyclic_types:            0
% 23.83/3.50  sat_guarded_non_collapsed_types:        0
% 23.83/3.50  num_pure_diseq_elim:                    0
% 23.83/3.50  simp_replaced_by:                       0
% 23.83/3.50  res_preprocessed:                       93
% 23.83/3.50  prep_upred:                             0
% 23.83/3.50  prep_unflattend:                        32
% 23.83/3.50  smt_new_axioms:                         0
% 23.83/3.50  pred_elim_cands:                        4
% 23.83/3.50  pred_elim:                              0
% 23.83/3.50  pred_elim_cl:                           0
% 23.83/3.50  pred_elim_cycles:                       4
% 23.83/3.50  merged_defs:                            0
% 23.83/3.50  merged_defs_ncl:                        0
% 23.83/3.50  bin_hyper_res:                          0
% 23.83/3.50  prep_cycles:                            4
% 23.83/3.50  pred_elim_time:                         0.009
% 23.83/3.50  splitting_time:                         0.
% 23.83/3.50  sem_filter_time:                        0.
% 23.83/3.50  monotx_time:                            0.001
% 23.83/3.50  subtype_inf_time:                       0.
% 23.83/3.50  
% 23.83/3.50  ------ Problem properties
% 23.83/3.50  
% 23.83/3.50  clauses:                                19
% 23.83/3.50  conjectures:                            2
% 23.83/3.50  epr:                                    4
% 23.83/3.50  horn:                                   16
% 23.83/3.50  ground:                                 1
% 23.83/3.50  unary:                                  4
% 23.83/3.50  binary:                                 4
% 23.83/3.50  lits:                                   56
% 23.83/3.50  lits_eq:                                16
% 23.83/3.50  fd_pure:                                0
% 23.83/3.50  fd_pseudo:                              0
% 23.83/3.50  fd_cond:                                0
% 23.83/3.50  fd_pseudo_cond:                         4
% 23.83/3.50  ac_symbols:                             0
% 23.83/3.50  
% 23.83/3.50  ------ Propositional Solver
% 23.83/3.50  
% 23.83/3.50  prop_solver_calls:                      37
% 23.83/3.50  prop_fast_solver_calls:                 4713
% 23.83/3.50  smt_solver_calls:                       0
% 23.83/3.50  smt_fast_solver_calls:                  0
% 23.83/3.50  prop_num_of_clauses:                    33615
% 23.83/3.50  prop_preprocess_simplified:             51471
% 23.83/3.50  prop_fo_subsumed:                       264
% 23.83/3.50  prop_solver_time:                       0.
% 23.83/3.50  smt_solver_time:                        0.
% 23.83/3.50  smt_fast_solver_time:                   0.
% 23.83/3.50  prop_fast_solver_time:                  0.
% 23.83/3.50  prop_unsat_core_time:                   0.003
% 23.83/3.50  
% 23.83/3.50  ------ QBF
% 23.83/3.50  
% 23.83/3.50  qbf_q_res:                              0
% 23.83/3.50  qbf_num_tautologies:                    0
% 23.83/3.50  qbf_prep_cycles:                        0
% 23.83/3.50  
% 23.83/3.50  ------ BMC1
% 23.83/3.50  
% 23.83/3.50  bmc1_current_bound:                     -1
% 23.83/3.50  bmc1_last_solved_bound:                 -1
% 23.83/3.50  bmc1_unsat_core_size:                   -1
% 23.83/3.50  bmc1_unsat_core_parents_size:           -1
% 23.83/3.50  bmc1_merge_next_fun:                    0
% 23.83/3.50  bmc1_unsat_core_clauses_time:           0.
% 23.83/3.50  
% 23.83/3.50  ------ Instantiation
% 23.83/3.50  
% 23.83/3.50  inst_num_of_clauses:                    6649
% 23.83/3.50  inst_num_in_passive:                    2477
% 23.83/3.50  inst_num_in_active:                     2251
% 23.83/3.50  inst_num_in_unprocessed:                1921
% 23.83/3.50  inst_num_of_loops:                      2710
% 23.83/3.50  inst_num_of_learning_restarts:          0
% 23.83/3.50  inst_num_moves_active_passive:          455
% 23.83/3.50  inst_lit_activity:                      0
% 23.83/3.50  inst_lit_activity_moves:                0
% 23.83/3.50  inst_num_tautologies:                   0
% 23.83/3.50  inst_num_prop_implied:                  0
% 23.83/3.50  inst_num_existing_simplified:           0
% 23.83/3.50  inst_num_eq_res_simplified:             0
% 23.83/3.50  inst_num_child_elim:                    0
% 23.83/3.50  inst_num_of_dismatching_blockings:      7440
% 23.83/3.50  inst_num_of_non_proper_insts:           8334
% 23.83/3.50  inst_num_of_duplicates:                 0
% 23.83/3.50  inst_inst_num_from_inst_to_res:         0
% 23.83/3.50  inst_dismatching_checking_time:         0.
% 23.83/3.50  
% 23.83/3.50  ------ Resolution
% 23.83/3.50  
% 23.83/3.50  res_num_of_clauses:                     0
% 23.83/3.50  res_num_in_passive:                     0
% 23.83/3.50  res_num_in_active:                      0
% 23.83/3.50  res_num_of_loops:                       97
% 23.83/3.50  res_forward_subset_subsumed:            373
% 23.83/3.50  res_backward_subset_subsumed:           0
% 23.83/3.50  res_forward_subsumed:                   0
% 23.83/3.50  res_backward_subsumed:                  0
% 23.83/3.50  res_forward_subsumption_resolution:     4
% 23.83/3.50  res_backward_subsumption_resolution:    0
% 23.83/3.50  res_clause_to_clause_subsumption:       28289
% 23.83/3.50  res_orphan_elimination:                 0
% 23.83/3.50  res_tautology_del:                      533
% 23.83/3.50  res_num_eq_res_simplified:              0
% 23.83/3.50  res_num_sel_changes:                    0
% 23.83/3.50  res_moves_from_active_to_pass:          0
% 23.83/3.50  
% 23.83/3.50  ------ Superposition
% 23.83/3.50  
% 23.83/3.50  sup_time_total:                         0.
% 23.83/3.50  sup_time_generating:                    0.
% 23.83/3.50  sup_time_sim_full:                      0.
% 23.83/3.50  sup_time_sim_immed:                     0.
% 23.83/3.50  
% 23.83/3.50  sup_num_of_clauses:                     3332
% 23.83/3.50  sup_num_in_active:                      137
% 23.83/3.50  sup_num_in_passive:                     3195
% 23.83/3.50  sup_num_of_loops:                       540
% 23.83/3.50  sup_fw_superposition:                   3770
% 23.83/3.50  sup_bw_superposition:                   2618
% 23.83/3.50  sup_immediate_simplified:               2092
% 23.83/3.50  sup_given_eliminated:                   36
% 23.83/3.50  comparisons_done:                       0
% 23.83/3.50  comparisons_avoided:                    303
% 23.83/3.50  
% 23.83/3.50  ------ Simplifications
% 23.83/3.50  
% 23.83/3.50  
% 23.83/3.50  sim_fw_subset_subsumed:                 374
% 23.83/3.50  sim_bw_subset_subsumed:                 225
% 23.83/3.50  sim_fw_subsumed:                        743
% 23.83/3.50  sim_bw_subsumed:                        225
% 23.83/3.50  sim_fw_subsumption_res:                 0
% 23.83/3.50  sim_bw_subsumption_res:                 0
% 23.83/3.50  sim_tautology_del:                      288
% 23.83/3.50  sim_eq_tautology_del:                   501
% 23.83/3.50  sim_eq_res_simp:                        0
% 23.83/3.50  sim_fw_demodulated:                     1010
% 23.83/3.50  sim_bw_demodulated:                     669
% 23.83/3.50  sim_light_normalised:                   299
% 23.83/3.50  sim_joinable_taut:                      0
% 23.83/3.50  sim_joinable_simp:                      0
% 23.83/3.50  sim_ac_normalised:                      0
% 23.83/3.50  sim_smt_subsumption:                    0
% 23.83/3.50  
%------------------------------------------------------------------------------
