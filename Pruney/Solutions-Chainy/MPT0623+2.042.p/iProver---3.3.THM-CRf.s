%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:38 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 396 expanded)
%              Number of clauses        :   72 ( 145 expanded)
%              Number of leaves         :   20 (  94 expanded)
%              Depth                    :   17
%              Number of atoms          :  472 (1662 expanded)
%              Number of equality atoms :  224 ( 812 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f29])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK2(X0,X1),X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f23])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f72,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
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
    inference(nnf_transformation,[],[f12])).

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

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f76,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f9,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( k1_tarski(X1) = k2_relat_1(sK5(X0,X1))
        & k1_relat_1(sK5(X0,X1)) = X0
        & v1_funct_1(sK5(X0,X1))
        & v1_relat_1(sK5(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tarski(X1) = k2_relat_1(sK5(X0,X1))
          & k1_relat_1(sK5(X0,X1)) = X0
          & v1_funct_1(sK5(X0,X1))
          & v1_relat_1(sK5(X0,X1)) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f16,f38])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK5(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK5(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f11])).

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

fof(f40,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ~ r1_tarski(k2_relat_1(X2),X0)
            | k1_relat_1(X2) != X1
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 != X0 ) )
   => ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),sK6)
          | k1_relat_1(X2) != sK7
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = sK7
        | k1_xboole_0 != sK6 ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK6)
        | k1_relat_1(X2) != sK7
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK7
      | k1_xboole_0 != sK6 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f18,f40])).

fof(f70,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK6)
      | k1_relat_1(X2) != sK7
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK5(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK5(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f8,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_funct_1(X1,X2) = np__1 )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = np__1
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_funct_1(X1,X2) = np__1
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_funct_1(sK4(X0),X2) = np__1
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK4(X0)) = X0
        & v1_funct_1(sK4(X0))
        & v1_relat_1(sK4(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_funct_1(sK4(X0),X2) = np__1
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK4(X0)) = X0
      & v1_funct_1(sK4(X0))
      & v1_relat_1(sK4(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f36])).

fof(f63,plain,(
    ! [X0] : k1_relat_1(sK4(X0)) = X0 ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f59,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f61,plain,(
    ! [X0] : v1_relat_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f37])).

fof(f62,plain,(
    ! [X0] : v1_funct_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f37])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f74,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f56])).

fof(f75,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f74])).

fof(f69,plain,
    ( k1_xboole_0 = sK7
    | k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_10,plain,
    ( r2_hidden(sK2(X0,X1),X1)
    | r2_hidden(sK2(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_958,plain,
    ( X0 = X1
    | r2_hidden(sK2(X1,X0),X0) = iProver_top
    | r2_hidden(sK2(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_12,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_961,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1749,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_961])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_11,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_472,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | X3 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_11])).

cnf(c_473,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_472])).

cnf(c_474,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_473])).

cnf(c_1884,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1749,c_474])).

cnf(c_2625,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(k1_xboole_0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_958,c_1884])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_967,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_953,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1683,plain,
    ( sK0(k1_tarski(X0),X1) = X0
    | r1_tarski(k1_tarski(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_967,c_953])).

cnf(c_23,plain,
    ( k2_relat_1(sK5(X0,X1)) = k1_tarski(X1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_24,plain,
    ( k1_relat_1(sK5(X0,X1)) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_27,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(X0),sK6)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) != sK7 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_945,plain,
    ( k1_relat_1(X0) != sK7
    | r1_tarski(k2_relat_1(X0),sK6) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1272,plain,
    ( sK7 != X0
    | k1_xboole_0 = X0
    | r1_tarski(k2_relat_1(sK5(X0,X1)),sK6) != iProver_top
    | v1_funct_1(sK5(X0,X1)) != iProver_top
    | v1_relat_1(sK5(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_24,c_945])).

cnf(c_26,plain,
    ( v1_relat_1(sK5(X0,X1))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_32,plain,
    ( k1_xboole_0 = X0
    | v1_relat_1(sK5(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,plain,
    ( v1_funct_1(sK5(X0,X1))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_35,plain,
    ( k1_xboole_0 = X0
    | v1_funct_1(sK5(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1463,plain,
    ( sK7 != X0
    | k1_xboole_0 = X0
    | r1_tarski(k2_relat_1(sK5(X0,X1)),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1272,c_32,c_35])).

cnf(c_1470,plain,
    ( sK7 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK5(sK7,X0)),sK6) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1463])).

cnf(c_1503,plain,
    ( sK7 = k1_xboole_0
    | r1_tarski(k1_tarski(X0),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_1470])).

cnf(c_3654,plain,
    ( sK0(k1_tarski(X0),sK6) = X0
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1683,c_1503])).

cnf(c_20,plain,
    ( k1_relat_1(sK4(X0)) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_46,plain,
    ( k1_relat_1(sK4(k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_22,plain,
    ( v1_relat_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_336,plain,
    ( sK4(X0) != X1
    | k2_relat_1(X1) = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_22])).

cnf(c_337,plain,
    ( k2_relat_1(sK4(X0)) = k1_xboole_0
    | k1_relat_1(sK4(X0)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_336])).

cnf(c_338,plain,
    ( k2_relat_1(sK4(k1_xboole_0)) = k1_xboole_0
    | k1_relat_1(sK4(k1_xboole_0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_337])).

cnf(c_1198,plain,
    ( sK7 != X0
    | r1_tarski(k2_relat_1(sK4(X0)),sK6) != iProver_top
    | v1_funct_1(sK4(X0)) != iProver_top
    | v1_relat_1(sK4(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_945])).

cnf(c_40,plain,
    ( v1_relat_1(sK4(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,plain,
    ( v1_funct_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_43,plain,
    ( v1_funct_1(sK4(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1221,plain,
    ( sK7 != X0
    | r1_tarski(k2_relat_1(sK4(X0)),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1198,c_40,c_43])).

cnf(c_1223,plain,
    ( ~ r1_tarski(k2_relat_1(sK4(X0)),sK6)
    | sK7 != X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1221])).

cnf(c_1225,plain,
    ( ~ r1_tarski(k2_relat_1(sK4(k1_xboole_0)),sK6)
    | sK7 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1223])).

cnf(c_523,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1262,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(sK4(X2)),sK6)
    | k2_relat_1(sK4(X2)) != X0
    | sK6 != X1 ),
    inference(instantiation,[status(thm)],[c_523])).

cnf(c_1722,plain,
    ( ~ r1_tarski(X0,sK6)
    | r1_tarski(k2_relat_1(sK4(X1)),sK6)
    | k2_relat_1(sK4(X1)) != X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1262])).

cnf(c_1725,plain,
    ( r1_tarski(k2_relat_1(sK4(k1_xboole_0)),sK6)
    | ~ r1_tarski(k1_xboole_0,sK6)
    | k2_relat_1(sK4(k1_xboole_0)) != k1_xboole_0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1722])).

cnf(c_521,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1723,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_521])).

cnf(c_2047,plain,
    ( r1_tarski(k1_xboole_0,sK6) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_4373,plain,
    ( sK0(k1_tarski(X0),sK6) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3654,c_46,c_338,c_1225,c_1725,c_1723,c_2047])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_968,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4377,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r1_tarski(k1_tarski(X0),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_4373,c_968])).

cnf(c_4387,plain,
    ( r2_hidden(X0,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4377,c_46,c_338,c_1225,c_1503,c_1725,c_1723,c_2047])).

cnf(c_4401,plain,
    ( sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2625,c_4387])).

cnf(c_522,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2147,plain,
    ( X0 != X1
    | sK7 != X1
    | sK7 = X0 ),
    inference(instantiation,[status(thm)],[c_522])).

cnf(c_3777,plain,
    ( X0 != sK7
    | sK7 = X0
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_2147])).

cnf(c_3779,plain,
    ( sK7 != sK7
    | sK7 = k1_xboole_0
    | k1_xboole_0 != sK7 ),
    inference(instantiation,[status(thm)],[c_3777])).

cnf(c_15,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3607,plain,
    ( r2_hidden(sK7,k1_tarski(sK7)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2132,plain,
    ( ~ r2_hidden(sK7,k1_tarski(X0))
    | sK7 = X0 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_3606,plain,
    ( ~ r2_hidden(sK7,k1_tarski(sK7))
    | sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_2132])).

cnf(c_1202,plain,
    ( sK6 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_522])).

cnf(c_1203,plain,
    ( sK6 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1202])).

cnf(c_60,plain,
    ( r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_57,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_28,negated_conjecture,
    ( k1_xboole_0 = sK7
    | k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f69])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4401,c_3779,c_3607,c_3606,c_2047,c_1723,c_1725,c_1225,c_1203,c_338,c_60,c_57,c_46,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:10:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.78/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.00  
% 2.78/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.78/1.00  
% 2.78/1.00  ------  iProver source info
% 2.78/1.00  
% 2.78/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.78/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.78/1.00  git: non_committed_changes: false
% 2.78/1.00  git: last_make_outside_of_git: false
% 2.78/1.00  
% 2.78/1.00  ------ 
% 2.78/1.00  
% 2.78/1.00  ------ Input Options
% 2.78/1.00  
% 2.78/1.00  --out_options                           all
% 2.78/1.00  --tptp_safe_out                         true
% 2.78/1.00  --problem_path                          ""
% 2.78/1.00  --include_path                          ""
% 2.78/1.00  --clausifier                            res/vclausify_rel
% 2.78/1.00  --clausifier_options                    --mode clausify
% 2.78/1.00  --stdin                                 false
% 2.78/1.00  --stats_out                             all
% 2.78/1.00  
% 2.78/1.00  ------ General Options
% 2.78/1.00  
% 2.78/1.00  --fof                                   false
% 2.78/1.00  --time_out_real                         305.
% 2.78/1.00  --time_out_virtual                      -1.
% 2.78/1.00  --symbol_type_check                     false
% 2.78/1.00  --clausify_out                          false
% 2.78/1.00  --sig_cnt_out                           false
% 2.78/1.00  --trig_cnt_out                          false
% 2.78/1.00  --trig_cnt_out_tolerance                1.
% 2.78/1.00  --trig_cnt_out_sk_spl                   false
% 2.78/1.00  --abstr_cl_out                          false
% 2.78/1.00  
% 2.78/1.00  ------ Global Options
% 2.78/1.00  
% 2.78/1.00  --schedule                              default
% 2.78/1.00  --add_important_lit                     false
% 2.78/1.00  --prop_solver_per_cl                    1000
% 2.78/1.00  --min_unsat_core                        false
% 2.78/1.00  --soft_assumptions                      false
% 2.78/1.00  --soft_lemma_size                       3
% 2.78/1.00  --prop_impl_unit_size                   0
% 2.78/1.00  --prop_impl_unit                        []
% 2.78/1.00  --share_sel_clauses                     true
% 2.78/1.00  --reset_solvers                         false
% 2.78/1.00  --bc_imp_inh                            [conj_cone]
% 2.78/1.00  --conj_cone_tolerance                   3.
% 2.78/1.00  --extra_neg_conj                        none
% 2.78/1.00  --large_theory_mode                     true
% 2.78/1.00  --prolific_symb_bound                   200
% 2.78/1.00  --lt_threshold                          2000
% 2.78/1.00  --clause_weak_htbl                      true
% 2.78/1.00  --gc_record_bc_elim                     false
% 2.78/1.00  
% 2.78/1.00  ------ Preprocessing Options
% 2.78/1.00  
% 2.78/1.00  --preprocessing_flag                    true
% 2.78/1.00  --time_out_prep_mult                    0.1
% 2.78/1.00  --splitting_mode                        input
% 2.78/1.00  --splitting_grd                         true
% 2.78/1.00  --splitting_cvd                         false
% 2.78/1.00  --splitting_cvd_svl                     false
% 2.78/1.00  --splitting_nvd                         32
% 2.78/1.00  --sub_typing                            true
% 2.78/1.00  --prep_gs_sim                           true
% 2.78/1.00  --prep_unflatten                        true
% 2.78/1.00  --prep_res_sim                          true
% 2.78/1.00  --prep_upred                            true
% 2.78/1.00  --prep_sem_filter                       exhaustive
% 2.78/1.00  --prep_sem_filter_out                   false
% 2.78/1.00  --pred_elim                             true
% 2.78/1.00  --res_sim_input                         true
% 2.78/1.00  --eq_ax_congr_red                       true
% 2.78/1.00  --pure_diseq_elim                       true
% 2.78/1.00  --brand_transform                       false
% 2.78/1.00  --non_eq_to_eq                          false
% 2.78/1.00  --prep_def_merge                        true
% 2.78/1.00  --prep_def_merge_prop_impl              false
% 2.78/1.00  --prep_def_merge_mbd                    true
% 2.78/1.00  --prep_def_merge_tr_red                 false
% 2.78/1.00  --prep_def_merge_tr_cl                  false
% 2.78/1.00  --smt_preprocessing                     true
% 2.78/1.00  --smt_ac_axioms                         fast
% 2.78/1.00  --preprocessed_out                      false
% 2.78/1.00  --preprocessed_stats                    false
% 2.78/1.00  
% 2.78/1.00  ------ Abstraction refinement Options
% 2.78/1.00  
% 2.78/1.00  --abstr_ref                             []
% 2.78/1.00  --abstr_ref_prep                        false
% 2.78/1.00  --abstr_ref_until_sat                   false
% 2.78/1.00  --abstr_ref_sig_restrict                funpre
% 2.78/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.78/1.00  --abstr_ref_under                       []
% 2.78/1.00  
% 2.78/1.00  ------ SAT Options
% 2.78/1.00  
% 2.78/1.00  --sat_mode                              false
% 2.78/1.00  --sat_fm_restart_options                ""
% 2.78/1.00  --sat_gr_def                            false
% 2.78/1.00  --sat_epr_types                         true
% 2.78/1.00  --sat_non_cyclic_types                  false
% 2.78/1.00  --sat_finite_models                     false
% 2.78/1.00  --sat_fm_lemmas                         false
% 2.78/1.00  --sat_fm_prep                           false
% 2.78/1.00  --sat_fm_uc_incr                        true
% 2.78/1.00  --sat_out_model                         small
% 2.78/1.00  --sat_out_clauses                       false
% 2.78/1.00  
% 2.78/1.00  ------ QBF Options
% 2.78/1.00  
% 2.78/1.00  --qbf_mode                              false
% 2.78/1.00  --qbf_elim_univ                         false
% 2.78/1.00  --qbf_dom_inst                          none
% 2.78/1.00  --qbf_dom_pre_inst                      false
% 2.78/1.00  --qbf_sk_in                             false
% 2.78/1.00  --qbf_pred_elim                         true
% 2.78/1.00  --qbf_split                             512
% 2.78/1.00  
% 2.78/1.00  ------ BMC1 Options
% 2.78/1.00  
% 2.78/1.00  --bmc1_incremental                      false
% 2.78/1.00  --bmc1_axioms                           reachable_all
% 2.78/1.00  --bmc1_min_bound                        0
% 2.78/1.00  --bmc1_max_bound                        -1
% 2.78/1.00  --bmc1_max_bound_default                -1
% 2.78/1.00  --bmc1_symbol_reachability              true
% 2.78/1.00  --bmc1_property_lemmas                  false
% 2.78/1.00  --bmc1_k_induction                      false
% 2.78/1.00  --bmc1_non_equiv_states                 false
% 2.78/1.00  --bmc1_deadlock                         false
% 2.78/1.00  --bmc1_ucm                              false
% 2.78/1.00  --bmc1_add_unsat_core                   none
% 2.78/1.00  --bmc1_unsat_core_children              false
% 2.78/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.78/1.00  --bmc1_out_stat                         full
% 2.78/1.00  --bmc1_ground_init                      false
% 2.78/1.00  --bmc1_pre_inst_next_state              false
% 2.78/1.00  --bmc1_pre_inst_state                   false
% 2.78/1.00  --bmc1_pre_inst_reach_state             false
% 2.78/1.00  --bmc1_out_unsat_core                   false
% 2.78/1.00  --bmc1_aig_witness_out                  false
% 2.78/1.00  --bmc1_verbose                          false
% 2.78/1.00  --bmc1_dump_clauses_tptp                false
% 2.78/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.78/1.00  --bmc1_dump_file                        -
% 2.78/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.78/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.78/1.00  --bmc1_ucm_extend_mode                  1
% 2.78/1.00  --bmc1_ucm_init_mode                    2
% 2.78/1.00  --bmc1_ucm_cone_mode                    none
% 2.78/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.78/1.00  --bmc1_ucm_relax_model                  4
% 2.78/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.78/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.78/1.00  --bmc1_ucm_layered_model                none
% 2.78/1.00  --bmc1_ucm_max_lemma_size               10
% 2.78/1.00  
% 2.78/1.00  ------ AIG Options
% 2.78/1.00  
% 2.78/1.00  --aig_mode                              false
% 2.78/1.00  
% 2.78/1.00  ------ Instantiation Options
% 2.78/1.00  
% 2.78/1.00  --instantiation_flag                    true
% 2.78/1.00  --inst_sos_flag                         false
% 2.78/1.00  --inst_sos_phase                        true
% 2.78/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.78/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.78/1.00  --inst_lit_sel_side                     num_symb
% 2.78/1.00  --inst_solver_per_active                1400
% 2.78/1.00  --inst_solver_calls_frac                1.
% 2.78/1.00  --inst_passive_queue_type               priority_queues
% 2.78/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.78/1.00  --inst_passive_queues_freq              [25;2]
% 2.78/1.00  --inst_dismatching                      true
% 2.78/1.00  --inst_eager_unprocessed_to_passive     true
% 2.78/1.00  --inst_prop_sim_given                   true
% 2.78/1.00  --inst_prop_sim_new                     false
% 2.78/1.00  --inst_subs_new                         false
% 2.78/1.00  --inst_eq_res_simp                      false
% 2.78/1.00  --inst_subs_given                       false
% 2.78/1.00  --inst_orphan_elimination               true
% 2.78/1.00  --inst_learning_loop_flag               true
% 2.78/1.00  --inst_learning_start                   3000
% 2.78/1.00  --inst_learning_factor                  2
% 2.78/1.00  --inst_start_prop_sim_after_learn       3
% 2.78/1.00  --inst_sel_renew                        solver
% 2.78/1.00  --inst_lit_activity_flag                true
% 2.78/1.00  --inst_restr_to_given                   false
% 2.78/1.00  --inst_activity_threshold               500
% 2.78/1.00  --inst_out_proof                        true
% 2.78/1.00  
% 2.78/1.00  ------ Resolution Options
% 2.78/1.00  
% 2.78/1.00  --resolution_flag                       true
% 2.78/1.00  --res_lit_sel                           adaptive
% 2.78/1.00  --res_lit_sel_side                      none
% 2.78/1.00  --res_ordering                          kbo
% 2.78/1.00  --res_to_prop_solver                    active
% 2.78/1.00  --res_prop_simpl_new                    false
% 2.78/1.00  --res_prop_simpl_given                  true
% 2.78/1.00  --res_passive_queue_type                priority_queues
% 2.78/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.78/1.00  --res_passive_queues_freq               [15;5]
% 2.78/1.00  --res_forward_subs                      full
% 2.78/1.00  --res_backward_subs                     full
% 2.78/1.00  --res_forward_subs_resolution           true
% 2.78/1.00  --res_backward_subs_resolution          true
% 2.78/1.00  --res_orphan_elimination                true
% 2.78/1.00  --res_time_limit                        2.
% 2.78/1.00  --res_out_proof                         true
% 2.78/1.00  
% 2.78/1.00  ------ Superposition Options
% 2.78/1.00  
% 2.78/1.00  --superposition_flag                    true
% 2.78/1.00  --sup_passive_queue_type                priority_queues
% 2.78/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.78/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.78/1.00  --demod_completeness_check              fast
% 2.78/1.00  --demod_use_ground                      true
% 2.78/1.00  --sup_to_prop_solver                    passive
% 2.78/1.00  --sup_prop_simpl_new                    true
% 2.78/1.00  --sup_prop_simpl_given                  true
% 2.78/1.00  --sup_fun_splitting                     false
% 2.78/1.00  --sup_smt_interval                      50000
% 2.78/1.00  
% 2.78/1.00  ------ Superposition Simplification Setup
% 2.78/1.00  
% 2.78/1.00  --sup_indices_passive                   []
% 2.78/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.78/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.00  --sup_full_bw                           [BwDemod]
% 2.78/1.00  --sup_immed_triv                        [TrivRules]
% 2.78/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.78/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.00  --sup_immed_bw_main                     []
% 2.78/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.78/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/1.00  
% 2.78/1.00  ------ Combination Options
% 2.78/1.00  
% 2.78/1.00  --comb_res_mult                         3
% 2.78/1.00  --comb_sup_mult                         2
% 2.78/1.00  --comb_inst_mult                        10
% 2.78/1.00  
% 2.78/1.00  ------ Debug Options
% 2.78/1.00  
% 2.78/1.00  --dbg_backtrace                         false
% 2.78/1.00  --dbg_dump_prop_clauses                 false
% 2.78/1.00  --dbg_dump_prop_clauses_file            -
% 2.78/1.00  --dbg_out_stat                          false
% 2.78/1.00  ------ Parsing...
% 2.78/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.78/1.00  
% 2.78/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.78/1.00  
% 2.78/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.78/1.00  
% 2.78/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.78/1.00  ------ Proving...
% 2.78/1.00  ------ Problem Properties 
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  clauses                                 29
% 2.78/1.00  conjectures                             2
% 2.78/1.00  EPR                                     3
% 2.78/1.00  Horn                                    18
% 2.78/1.00  unary                                   6
% 2.78/1.00  binary                                  11
% 2.78/1.00  lits                                    66
% 2.78/1.00  lits eq                                 26
% 2.78/1.00  fd_pure                                 0
% 2.78/1.00  fd_pseudo                               0
% 2.78/1.00  fd_cond                                 3
% 2.78/1.00  fd_pseudo_cond                          7
% 2.78/1.00  AC symbols                              0
% 2.78/1.00  
% 2.78/1.00  ------ Schedule dynamic 5 is on 
% 2.78/1.00  
% 2.78/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  ------ 
% 2.78/1.00  Current options:
% 2.78/1.00  ------ 
% 2.78/1.00  
% 2.78/1.00  ------ Input Options
% 2.78/1.00  
% 2.78/1.00  --out_options                           all
% 2.78/1.00  --tptp_safe_out                         true
% 2.78/1.00  --problem_path                          ""
% 2.78/1.00  --include_path                          ""
% 2.78/1.00  --clausifier                            res/vclausify_rel
% 2.78/1.00  --clausifier_options                    --mode clausify
% 2.78/1.00  --stdin                                 false
% 2.78/1.00  --stats_out                             all
% 2.78/1.00  
% 2.78/1.00  ------ General Options
% 2.78/1.00  
% 2.78/1.00  --fof                                   false
% 2.78/1.00  --time_out_real                         305.
% 2.78/1.00  --time_out_virtual                      -1.
% 2.78/1.00  --symbol_type_check                     false
% 2.78/1.00  --clausify_out                          false
% 2.78/1.00  --sig_cnt_out                           false
% 2.78/1.00  --trig_cnt_out                          false
% 2.78/1.00  --trig_cnt_out_tolerance                1.
% 2.78/1.00  --trig_cnt_out_sk_spl                   false
% 2.78/1.00  --abstr_cl_out                          false
% 2.78/1.00  
% 2.78/1.00  ------ Global Options
% 2.78/1.00  
% 2.78/1.00  --schedule                              default
% 2.78/1.00  --add_important_lit                     false
% 2.78/1.00  --prop_solver_per_cl                    1000
% 2.78/1.00  --min_unsat_core                        false
% 2.78/1.00  --soft_assumptions                      false
% 2.78/1.00  --soft_lemma_size                       3
% 2.78/1.00  --prop_impl_unit_size                   0
% 2.78/1.00  --prop_impl_unit                        []
% 2.78/1.00  --share_sel_clauses                     true
% 2.78/1.00  --reset_solvers                         false
% 2.78/1.00  --bc_imp_inh                            [conj_cone]
% 2.78/1.00  --conj_cone_tolerance                   3.
% 2.78/1.00  --extra_neg_conj                        none
% 2.78/1.00  --large_theory_mode                     true
% 2.78/1.00  --prolific_symb_bound                   200
% 2.78/1.00  --lt_threshold                          2000
% 2.78/1.00  --clause_weak_htbl                      true
% 2.78/1.00  --gc_record_bc_elim                     false
% 2.78/1.00  
% 2.78/1.00  ------ Preprocessing Options
% 2.78/1.00  
% 2.78/1.00  --preprocessing_flag                    true
% 2.78/1.00  --time_out_prep_mult                    0.1
% 2.78/1.00  --splitting_mode                        input
% 2.78/1.00  --splitting_grd                         true
% 2.78/1.00  --splitting_cvd                         false
% 2.78/1.00  --splitting_cvd_svl                     false
% 2.78/1.00  --splitting_nvd                         32
% 2.78/1.00  --sub_typing                            true
% 2.78/1.00  --prep_gs_sim                           true
% 2.78/1.00  --prep_unflatten                        true
% 2.78/1.00  --prep_res_sim                          true
% 2.78/1.00  --prep_upred                            true
% 2.78/1.00  --prep_sem_filter                       exhaustive
% 2.78/1.00  --prep_sem_filter_out                   false
% 2.78/1.00  --pred_elim                             true
% 2.78/1.00  --res_sim_input                         true
% 2.78/1.00  --eq_ax_congr_red                       true
% 2.78/1.00  --pure_diseq_elim                       true
% 2.78/1.00  --brand_transform                       false
% 2.78/1.00  --non_eq_to_eq                          false
% 2.78/1.00  --prep_def_merge                        true
% 2.78/1.00  --prep_def_merge_prop_impl              false
% 2.78/1.00  --prep_def_merge_mbd                    true
% 2.78/1.00  --prep_def_merge_tr_red                 false
% 2.78/1.00  --prep_def_merge_tr_cl                  false
% 2.78/1.00  --smt_preprocessing                     true
% 2.78/1.00  --smt_ac_axioms                         fast
% 2.78/1.00  --preprocessed_out                      false
% 2.78/1.00  --preprocessed_stats                    false
% 2.78/1.00  
% 2.78/1.00  ------ Abstraction refinement Options
% 2.78/1.00  
% 2.78/1.00  --abstr_ref                             []
% 2.78/1.00  --abstr_ref_prep                        false
% 2.78/1.00  --abstr_ref_until_sat                   false
% 2.78/1.00  --abstr_ref_sig_restrict                funpre
% 2.78/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.78/1.00  --abstr_ref_under                       []
% 2.78/1.00  
% 2.78/1.00  ------ SAT Options
% 2.78/1.00  
% 2.78/1.00  --sat_mode                              false
% 2.78/1.00  --sat_fm_restart_options                ""
% 2.78/1.00  --sat_gr_def                            false
% 2.78/1.00  --sat_epr_types                         true
% 2.78/1.00  --sat_non_cyclic_types                  false
% 2.78/1.00  --sat_finite_models                     false
% 2.78/1.00  --sat_fm_lemmas                         false
% 2.78/1.00  --sat_fm_prep                           false
% 2.78/1.00  --sat_fm_uc_incr                        true
% 2.78/1.00  --sat_out_model                         small
% 2.78/1.00  --sat_out_clauses                       false
% 2.78/1.00  
% 2.78/1.00  ------ QBF Options
% 2.78/1.00  
% 2.78/1.00  --qbf_mode                              false
% 2.78/1.00  --qbf_elim_univ                         false
% 2.78/1.00  --qbf_dom_inst                          none
% 2.78/1.00  --qbf_dom_pre_inst                      false
% 2.78/1.00  --qbf_sk_in                             false
% 2.78/1.00  --qbf_pred_elim                         true
% 2.78/1.00  --qbf_split                             512
% 2.78/1.00  
% 2.78/1.00  ------ BMC1 Options
% 2.78/1.00  
% 2.78/1.00  --bmc1_incremental                      false
% 2.78/1.00  --bmc1_axioms                           reachable_all
% 2.78/1.00  --bmc1_min_bound                        0
% 2.78/1.00  --bmc1_max_bound                        -1
% 2.78/1.00  --bmc1_max_bound_default                -1
% 2.78/1.00  --bmc1_symbol_reachability              true
% 2.78/1.00  --bmc1_property_lemmas                  false
% 2.78/1.00  --bmc1_k_induction                      false
% 2.78/1.00  --bmc1_non_equiv_states                 false
% 2.78/1.00  --bmc1_deadlock                         false
% 2.78/1.00  --bmc1_ucm                              false
% 2.78/1.00  --bmc1_add_unsat_core                   none
% 2.78/1.00  --bmc1_unsat_core_children              false
% 2.78/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.78/1.00  --bmc1_out_stat                         full
% 2.78/1.00  --bmc1_ground_init                      false
% 2.78/1.00  --bmc1_pre_inst_next_state              false
% 2.78/1.00  --bmc1_pre_inst_state                   false
% 2.78/1.00  --bmc1_pre_inst_reach_state             false
% 2.78/1.00  --bmc1_out_unsat_core                   false
% 2.78/1.00  --bmc1_aig_witness_out                  false
% 2.78/1.00  --bmc1_verbose                          false
% 2.78/1.00  --bmc1_dump_clauses_tptp                false
% 2.78/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.78/1.00  --bmc1_dump_file                        -
% 2.78/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.78/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.78/1.00  --bmc1_ucm_extend_mode                  1
% 2.78/1.00  --bmc1_ucm_init_mode                    2
% 2.78/1.00  --bmc1_ucm_cone_mode                    none
% 2.78/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.78/1.00  --bmc1_ucm_relax_model                  4
% 2.78/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.78/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.78/1.00  --bmc1_ucm_layered_model                none
% 2.78/1.00  --bmc1_ucm_max_lemma_size               10
% 2.78/1.00  
% 2.78/1.00  ------ AIG Options
% 2.78/1.00  
% 2.78/1.00  --aig_mode                              false
% 2.78/1.00  
% 2.78/1.00  ------ Instantiation Options
% 2.78/1.00  
% 2.78/1.00  --instantiation_flag                    true
% 2.78/1.00  --inst_sos_flag                         false
% 2.78/1.00  --inst_sos_phase                        true
% 2.78/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.78/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.78/1.00  --inst_lit_sel_side                     none
% 2.78/1.00  --inst_solver_per_active                1400
% 2.78/1.00  --inst_solver_calls_frac                1.
% 2.78/1.00  --inst_passive_queue_type               priority_queues
% 2.78/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.78/1.00  --inst_passive_queues_freq              [25;2]
% 2.78/1.00  --inst_dismatching                      true
% 2.78/1.00  --inst_eager_unprocessed_to_passive     true
% 2.78/1.00  --inst_prop_sim_given                   true
% 2.78/1.00  --inst_prop_sim_new                     false
% 2.78/1.00  --inst_subs_new                         false
% 2.78/1.00  --inst_eq_res_simp                      false
% 2.78/1.00  --inst_subs_given                       false
% 2.78/1.00  --inst_orphan_elimination               true
% 2.78/1.00  --inst_learning_loop_flag               true
% 2.78/1.00  --inst_learning_start                   3000
% 2.78/1.00  --inst_learning_factor                  2
% 2.78/1.00  --inst_start_prop_sim_after_learn       3
% 2.78/1.00  --inst_sel_renew                        solver
% 2.78/1.00  --inst_lit_activity_flag                true
% 2.78/1.00  --inst_restr_to_given                   false
% 2.78/1.00  --inst_activity_threshold               500
% 2.78/1.00  --inst_out_proof                        true
% 2.78/1.00  
% 2.78/1.00  ------ Resolution Options
% 2.78/1.00  
% 2.78/1.00  --resolution_flag                       false
% 2.78/1.00  --res_lit_sel                           adaptive
% 2.78/1.00  --res_lit_sel_side                      none
% 2.78/1.00  --res_ordering                          kbo
% 2.78/1.00  --res_to_prop_solver                    active
% 2.78/1.00  --res_prop_simpl_new                    false
% 2.78/1.00  --res_prop_simpl_given                  true
% 2.78/1.00  --res_passive_queue_type                priority_queues
% 2.78/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.78/1.00  --res_passive_queues_freq               [15;5]
% 2.78/1.00  --res_forward_subs                      full
% 2.78/1.00  --res_backward_subs                     full
% 2.78/1.00  --res_forward_subs_resolution           true
% 2.78/1.00  --res_backward_subs_resolution          true
% 2.78/1.00  --res_orphan_elimination                true
% 2.78/1.00  --res_time_limit                        2.
% 2.78/1.00  --res_out_proof                         true
% 2.78/1.00  
% 2.78/1.00  ------ Superposition Options
% 2.78/1.00  
% 2.78/1.00  --superposition_flag                    true
% 2.78/1.00  --sup_passive_queue_type                priority_queues
% 2.78/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.78/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.78/1.00  --demod_completeness_check              fast
% 2.78/1.00  --demod_use_ground                      true
% 2.78/1.00  --sup_to_prop_solver                    passive
% 2.78/1.00  --sup_prop_simpl_new                    true
% 2.78/1.00  --sup_prop_simpl_given                  true
% 2.78/1.00  --sup_fun_splitting                     false
% 2.78/1.00  --sup_smt_interval                      50000
% 2.78/1.00  
% 2.78/1.00  ------ Superposition Simplification Setup
% 2.78/1.00  
% 2.78/1.00  --sup_indices_passive                   []
% 2.78/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.78/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.00  --sup_full_bw                           [BwDemod]
% 2.78/1.00  --sup_immed_triv                        [TrivRules]
% 2.78/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.78/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.00  --sup_immed_bw_main                     []
% 2.78/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.78/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/1.00  
% 2.78/1.00  ------ Combination Options
% 2.78/1.00  
% 2.78/1.00  --comb_res_mult                         3
% 2.78/1.00  --comb_sup_mult                         2
% 2.78/1.00  --comb_inst_mult                        10
% 2.78/1.00  
% 2.78/1.00  ------ Debug Options
% 2.78/1.00  
% 2.78/1.00  --dbg_backtrace                         false
% 2.78/1.00  --dbg_dump_prop_clauses                 false
% 2.78/1.00  --dbg_dump_prop_clauses_file            -
% 2.78/1.00  --dbg_out_stat                          false
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  ------ Proving...
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  % SZS status Theorem for theBenchmark.p
% 2.78/1.00  
% 2.78/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.78/1.00  
% 2.78/1.00  fof(f3,axiom,(
% 2.78/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f13,plain,(
% 2.78/1.00    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 2.78/1.00    inference(ennf_transformation,[],[f3])).
% 2.78/1.00  
% 2.78/1.00  fof(f28,plain,(
% 2.78/1.00    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 2.78/1.00    inference(nnf_transformation,[],[f13])).
% 2.78/1.00  
% 2.78/1.00  fof(f29,plain,(
% 2.78/1.00    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(sK2(X0,X1),X0)) & (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0))))),
% 2.78/1.00    introduced(choice_axiom,[])).
% 2.78/1.00  
% 2.78/1.00  fof(f30,plain,(
% 2.78/1.00    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(sK2(X0,X1),X0)) & (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0))))),
% 2.78/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f29])).
% 2.78/1.00  
% 2.78/1.00  fof(f51,plain,(
% 2.78/1.00    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f30])).
% 2.78/1.00  
% 2.78/1.00  fof(f5,axiom,(
% 2.78/1.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f54,plain,(
% 2.78/1.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.78/1.00    inference(cnf_transformation,[],[f5])).
% 2.78/1.00  
% 2.78/1.00  fof(f2,axiom,(
% 2.78/1.00    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f23,plain,(
% 2.78/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.78/1.00    inference(nnf_transformation,[],[f2])).
% 2.78/1.00  
% 2.78/1.00  fof(f24,plain,(
% 2.78/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.78/1.00    inference(flattening,[],[f23])).
% 2.78/1.00  
% 2.78/1.00  fof(f25,plain,(
% 2.78/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.78/1.00    inference(rectify,[],[f24])).
% 2.78/1.00  
% 2.78/1.00  fof(f26,plain,(
% 2.78/1.00    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 2.78/1.00    introduced(choice_axiom,[])).
% 2.78/1.00  
% 2.78/1.00  fof(f27,plain,(
% 2.78/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.78/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).
% 2.78/1.00  
% 2.78/1.00  fof(f46,plain,(
% 2.78/1.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.78/1.00    inference(cnf_transformation,[],[f27])).
% 2.78/1.00  
% 2.78/1.00  fof(f72,plain,(
% 2.78/1.00    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.78/1.00    inference(equality_resolution,[],[f46])).
% 2.78/1.00  
% 2.78/1.00  fof(f1,axiom,(
% 2.78/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f12,plain,(
% 2.78/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.78/1.00    inference(ennf_transformation,[],[f1])).
% 2.78/1.00  
% 2.78/1.00  fof(f19,plain,(
% 2.78/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.78/1.00    inference(nnf_transformation,[],[f12])).
% 2.78/1.00  
% 2.78/1.00  fof(f20,plain,(
% 2.78/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.78/1.00    inference(rectify,[],[f19])).
% 2.78/1.00  
% 2.78/1.00  fof(f21,plain,(
% 2.78/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.78/1.00    introduced(choice_axiom,[])).
% 2.78/1.00  
% 2.78/1.00  fof(f22,plain,(
% 2.78/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.78/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).
% 2.78/1.00  
% 2.78/1.00  fof(f42,plain,(
% 2.78/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f22])).
% 2.78/1.00  
% 2.78/1.00  fof(f4,axiom,(
% 2.78/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f53,plain,(
% 2.78/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f4])).
% 2.78/1.00  
% 2.78/1.00  fof(f43,plain,(
% 2.78/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f22])).
% 2.78/1.00  
% 2.78/1.00  fof(f6,axiom,(
% 2.78/1.00    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f31,plain,(
% 2.78/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.78/1.00    inference(nnf_transformation,[],[f6])).
% 2.78/1.00  
% 2.78/1.00  fof(f32,plain,(
% 2.78/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.78/1.00    inference(rectify,[],[f31])).
% 2.78/1.00  
% 2.78/1.00  fof(f33,plain,(
% 2.78/1.00    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 2.78/1.00    introduced(choice_axiom,[])).
% 2.78/1.00  
% 2.78/1.00  fof(f34,plain,(
% 2.78/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.78/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).
% 2.78/1.00  
% 2.78/1.00  fof(f55,plain,(
% 2.78/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.78/1.00    inference(cnf_transformation,[],[f34])).
% 2.78/1.00  
% 2.78/1.00  fof(f76,plain,(
% 2.78/1.00    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 2.78/1.00    inference(equality_resolution,[],[f55])).
% 2.78/1.00  
% 2.78/1.00  fof(f9,axiom,(
% 2.78/1.00    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f16,plain,(
% 2.78/1.00    ! [X0] : (! [X1] : ? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 2.78/1.00    inference(ennf_transformation,[],[f9])).
% 2.78/1.00  
% 2.78/1.00  fof(f38,plain,(
% 2.78/1.00    ! [X1,X0] : (? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_tarski(X1) = k2_relat_1(sK5(X0,X1)) & k1_relat_1(sK5(X0,X1)) = X0 & v1_funct_1(sK5(X0,X1)) & v1_relat_1(sK5(X0,X1))))),
% 2.78/1.00    introduced(choice_axiom,[])).
% 2.78/1.00  
% 2.78/1.00  fof(f39,plain,(
% 2.78/1.00    ! [X0] : (! [X1] : (k1_tarski(X1) = k2_relat_1(sK5(X0,X1)) & k1_relat_1(sK5(X0,X1)) = X0 & v1_funct_1(sK5(X0,X1)) & v1_relat_1(sK5(X0,X1))) | k1_xboole_0 = X0)),
% 2.78/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f16,f38])).
% 2.78/1.00  
% 2.78/1.00  fof(f68,plain,(
% 2.78/1.00    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK5(X0,X1)) | k1_xboole_0 = X0) )),
% 2.78/1.00    inference(cnf_transformation,[],[f39])).
% 2.78/1.00  
% 2.78/1.00  fof(f67,plain,(
% 2.78/1.00    ( ! [X0,X1] : (k1_relat_1(sK5(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 2.78/1.00    inference(cnf_transformation,[],[f39])).
% 2.78/1.00  
% 2.78/1.00  fof(f10,conjecture,(
% 2.78/1.00    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f11,negated_conjecture,(
% 2.78/1.00    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 2.78/1.00    inference(negated_conjecture,[],[f10])).
% 2.78/1.00  
% 2.78/1.00  fof(f17,plain,(
% 2.78/1.00    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 2.78/1.00    inference(ennf_transformation,[],[f11])).
% 2.78/1.00  
% 2.78/1.00  fof(f18,plain,(
% 2.78/1.00    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 2.78/1.00    inference(flattening,[],[f17])).
% 2.78/1.00  
% 2.78/1.00  fof(f40,plain,(
% 2.78/1.00    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0)) => (! [X2] : (~r1_tarski(k2_relat_1(X2),sK6) | k1_relat_1(X2) != sK7 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK7 | k1_xboole_0 != sK6))),
% 2.78/1.00    introduced(choice_axiom,[])).
% 2.78/1.00  
% 2.78/1.00  fof(f41,plain,(
% 2.78/1.00    ! [X2] : (~r1_tarski(k2_relat_1(X2),sK6) | k1_relat_1(X2) != sK7 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK7 | k1_xboole_0 != sK6)),
% 2.78/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f18,f40])).
% 2.78/1.00  
% 2.78/1.00  fof(f70,plain,(
% 2.78/1.00    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK6) | k1_relat_1(X2) != sK7 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f41])).
% 2.78/1.00  
% 2.78/1.00  fof(f65,plain,(
% 2.78/1.00    ( ! [X0,X1] : (v1_relat_1(sK5(X0,X1)) | k1_xboole_0 = X0) )),
% 2.78/1.00    inference(cnf_transformation,[],[f39])).
% 2.78/1.00  
% 2.78/1.00  fof(f66,plain,(
% 2.78/1.00    ( ! [X0,X1] : (v1_funct_1(sK5(X0,X1)) | k1_xboole_0 = X0) )),
% 2.78/1.00    inference(cnf_transformation,[],[f39])).
% 2.78/1.00  
% 2.78/1.00  fof(f8,axiom,(
% 2.78/1.00    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = np__1) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f15,plain,(
% 2.78/1.00    ! [X0] : ? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.78/1.00    inference(ennf_transformation,[],[f8])).
% 2.78/1.00  
% 2.78/1.00  fof(f36,plain,(
% 2.78/1.00    ! [X0] : (? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_funct_1(sK4(X0),X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(sK4(X0)) = X0 & v1_funct_1(sK4(X0)) & v1_relat_1(sK4(X0))))),
% 2.78/1.00    introduced(choice_axiom,[])).
% 2.78/1.00  
% 2.78/1.00  fof(f37,plain,(
% 2.78/1.00    ! [X0] : (! [X2] : (k1_funct_1(sK4(X0),X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(sK4(X0)) = X0 & v1_funct_1(sK4(X0)) & v1_relat_1(sK4(X0)))),
% 2.78/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f36])).
% 2.78/1.00  
% 2.78/1.00  fof(f63,plain,(
% 2.78/1.00    ( ! [X0] : (k1_relat_1(sK4(X0)) = X0) )),
% 2.78/1.00    inference(cnf_transformation,[],[f37])).
% 2.78/1.00  
% 2.78/1.00  fof(f7,axiom,(
% 2.78/1.00    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f14,plain,(
% 2.78/1.00    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.78/1.00    inference(ennf_transformation,[],[f7])).
% 2.78/1.00  
% 2.78/1.00  fof(f35,plain,(
% 2.78/1.00    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.78/1.00    inference(nnf_transformation,[],[f14])).
% 2.78/1.00  
% 2.78/1.00  fof(f59,plain,(
% 2.78/1.00    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f35])).
% 2.78/1.00  
% 2.78/1.00  fof(f61,plain,(
% 2.78/1.00    ( ! [X0] : (v1_relat_1(sK4(X0))) )),
% 2.78/1.00    inference(cnf_transformation,[],[f37])).
% 2.78/1.00  
% 2.78/1.00  fof(f62,plain,(
% 2.78/1.00    ( ! [X0] : (v1_funct_1(sK4(X0))) )),
% 2.78/1.00    inference(cnf_transformation,[],[f37])).
% 2.78/1.00  
% 2.78/1.00  fof(f44,plain,(
% 2.78/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f22])).
% 2.78/1.00  
% 2.78/1.00  fof(f56,plain,(
% 2.78/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 2.78/1.00    inference(cnf_transformation,[],[f34])).
% 2.78/1.00  
% 2.78/1.00  fof(f74,plain,(
% 2.78/1.00    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 2.78/1.00    inference(equality_resolution,[],[f56])).
% 2.78/1.00  
% 2.78/1.00  fof(f75,plain,(
% 2.78/1.00    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 2.78/1.00    inference(equality_resolution,[],[f74])).
% 2.78/1.00  
% 2.78/1.00  fof(f69,plain,(
% 2.78/1.00    k1_xboole_0 = sK7 | k1_xboole_0 != sK6),
% 2.78/1.00    inference(cnf_transformation,[],[f41])).
% 2.78/1.00  
% 2.78/1.00  cnf(c_10,plain,
% 2.78/1.00      ( r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0) | X1 = X0 ),
% 2.78/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_958,plain,
% 2.78/1.00      ( X0 = X1
% 2.78/1.00      | r2_hidden(sK2(X1,X0),X0) = iProver_top
% 2.78/1.00      | r2_hidden(sK2(X1,X0),X1) = iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_12,plain,
% 2.78/1.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.78/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_7,plain,
% 2.78/1.00      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 2.78/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_961,plain,
% 2.78/1.00      ( r2_hidden(X0,X1) != iProver_top
% 2.78/1.00      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1749,plain,
% 2.78/1.00      ( r2_hidden(X0,X1) != iProver_top
% 2.78/1.00      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_12,c_961]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_2,plain,
% 2.78/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.78/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_11,plain,
% 2.78/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 2.78/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_472,plain,
% 2.78/1.00      ( ~ r2_hidden(X0,X1)
% 2.78/1.00      | r2_hidden(X0,X2)
% 2.78/1.00      | X3 != X2
% 2.78/1.00      | k1_xboole_0 != X1 ),
% 2.78/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_11]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_473,plain,
% 2.78/1.00      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k1_xboole_0) ),
% 2.78/1.00      inference(unflattening,[status(thm)],[c_472]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_474,plain,
% 2.78/1.00      ( r2_hidden(X0,X1) = iProver_top
% 2.78/1.00      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_473]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1884,plain,
% 2.78/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.78/1.00      inference(global_propositional_subsumption,
% 2.78/1.00                [status(thm)],
% 2.78/1.00                [c_1749,c_474]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_2625,plain,
% 2.78/1.00      ( k1_xboole_0 = X0
% 2.78/1.00      | r2_hidden(sK2(k1_xboole_0,X0),X0) = iProver_top ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_958,c_1884]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1,plain,
% 2.78/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.78/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_967,plain,
% 2.78/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.78/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_16,plain,
% 2.78/1.00      ( ~ r2_hidden(X0,k1_tarski(X1)) | X0 = X1 ),
% 2.78/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_953,plain,
% 2.78/1.00      ( X0 = X1 | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1683,plain,
% 2.78/1.00      ( sK0(k1_tarski(X0),X1) = X0
% 2.78/1.00      | r1_tarski(k1_tarski(X0),X1) = iProver_top ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_967,c_953]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_23,plain,
% 2.78/1.00      ( k2_relat_1(sK5(X0,X1)) = k1_tarski(X1) | k1_xboole_0 = X0 ),
% 2.78/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_24,plain,
% 2.78/1.00      ( k1_relat_1(sK5(X0,X1)) = X0 | k1_xboole_0 = X0 ),
% 2.78/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_27,negated_conjecture,
% 2.78/1.00      ( ~ r1_tarski(k2_relat_1(X0),sK6)
% 2.78/1.00      | ~ v1_funct_1(X0)
% 2.78/1.00      | ~ v1_relat_1(X0)
% 2.78/1.00      | k1_relat_1(X0) != sK7 ),
% 2.78/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_945,plain,
% 2.78/1.00      ( k1_relat_1(X0) != sK7
% 2.78/1.00      | r1_tarski(k2_relat_1(X0),sK6) != iProver_top
% 2.78/1.00      | v1_funct_1(X0) != iProver_top
% 2.78/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1272,plain,
% 2.78/1.00      ( sK7 != X0
% 2.78/1.00      | k1_xboole_0 = X0
% 2.78/1.00      | r1_tarski(k2_relat_1(sK5(X0,X1)),sK6) != iProver_top
% 2.78/1.00      | v1_funct_1(sK5(X0,X1)) != iProver_top
% 2.78/1.00      | v1_relat_1(sK5(X0,X1)) != iProver_top ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_24,c_945]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_26,plain,
% 2.78/1.00      ( v1_relat_1(sK5(X0,X1)) | k1_xboole_0 = X0 ),
% 2.78/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_32,plain,
% 2.78/1.00      ( k1_xboole_0 = X0 | v1_relat_1(sK5(X0,X1)) = iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_25,plain,
% 2.78/1.00      ( v1_funct_1(sK5(X0,X1)) | k1_xboole_0 = X0 ),
% 2.78/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_35,plain,
% 2.78/1.00      ( k1_xboole_0 = X0 | v1_funct_1(sK5(X0,X1)) = iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1463,plain,
% 2.78/1.00      ( sK7 != X0
% 2.78/1.00      | k1_xboole_0 = X0
% 2.78/1.00      | r1_tarski(k2_relat_1(sK5(X0,X1)),sK6) != iProver_top ),
% 2.78/1.00      inference(global_propositional_subsumption,
% 2.78/1.00                [status(thm)],
% 2.78/1.00                [c_1272,c_32,c_35]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1470,plain,
% 2.78/1.00      ( sK7 = k1_xboole_0
% 2.78/1.00      | r1_tarski(k2_relat_1(sK5(sK7,X0)),sK6) != iProver_top ),
% 2.78/1.00      inference(equality_resolution,[status(thm)],[c_1463]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1503,plain,
% 2.78/1.00      ( sK7 = k1_xboole_0 | r1_tarski(k1_tarski(X0),sK6) != iProver_top ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_23,c_1470]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_3654,plain,
% 2.78/1.00      ( sK0(k1_tarski(X0),sK6) = X0 | sK7 = k1_xboole_0 ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_1683,c_1503]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_20,plain,
% 2.78/1.00      ( k1_relat_1(sK4(X0)) = X0 ),
% 2.78/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_46,plain,
% 2.78/1.00      ( k1_relat_1(sK4(k1_xboole_0)) = k1_xboole_0 ),
% 2.78/1.00      inference(instantiation,[status(thm)],[c_20]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_18,plain,
% 2.78/1.00      ( ~ v1_relat_1(X0)
% 2.78/1.00      | k2_relat_1(X0) = k1_xboole_0
% 2.78/1.00      | k1_relat_1(X0) != k1_xboole_0 ),
% 2.78/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_22,plain,
% 2.78/1.00      ( v1_relat_1(sK4(X0)) ),
% 2.78/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_336,plain,
% 2.78/1.00      ( sK4(X0) != X1
% 2.78/1.00      | k2_relat_1(X1) = k1_xboole_0
% 2.78/1.00      | k1_relat_1(X1) != k1_xboole_0 ),
% 2.78/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_22]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_337,plain,
% 2.78/1.00      ( k2_relat_1(sK4(X0)) = k1_xboole_0
% 2.78/1.00      | k1_relat_1(sK4(X0)) != k1_xboole_0 ),
% 2.78/1.00      inference(unflattening,[status(thm)],[c_336]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_338,plain,
% 2.78/1.00      ( k2_relat_1(sK4(k1_xboole_0)) = k1_xboole_0
% 2.78/1.00      | k1_relat_1(sK4(k1_xboole_0)) != k1_xboole_0 ),
% 2.78/1.00      inference(instantiation,[status(thm)],[c_337]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1198,plain,
% 2.78/1.00      ( sK7 != X0
% 2.78/1.00      | r1_tarski(k2_relat_1(sK4(X0)),sK6) != iProver_top
% 2.78/1.00      | v1_funct_1(sK4(X0)) != iProver_top
% 2.78/1.00      | v1_relat_1(sK4(X0)) != iProver_top ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_20,c_945]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_40,plain,
% 2.78/1.00      ( v1_relat_1(sK4(X0)) = iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_21,plain,
% 2.78/1.00      ( v1_funct_1(sK4(X0)) ),
% 2.78/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_43,plain,
% 2.78/1.00      ( v1_funct_1(sK4(X0)) = iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1221,plain,
% 2.78/1.00      ( sK7 != X0 | r1_tarski(k2_relat_1(sK4(X0)),sK6) != iProver_top ),
% 2.78/1.00      inference(global_propositional_subsumption,
% 2.78/1.00                [status(thm)],
% 2.78/1.00                [c_1198,c_40,c_43]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1223,plain,
% 2.78/1.00      ( ~ r1_tarski(k2_relat_1(sK4(X0)),sK6) | sK7 != X0 ),
% 2.78/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1221]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1225,plain,
% 2.78/1.00      ( ~ r1_tarski(k2_relat_1(sK4(k1_xboole_0)),sK6)
% 2.78/1.00      | sK7 != k1_xboole_0 ),
% 2.78/1.00      inference(instantiation,[status(thm)],[c_1223]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_523,plain,
% 2.78/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.78/1.00      theory(equality) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1262,plain,
% 2.78/1.00      ( ~ r1_tarski(X0,X1)
% 2.78/1.00      | r1_tarski(k2_relat_1(sK4(X2)),sK6)
% 2.78/1.00      | k2_relat_1(sK4(X2)) != X0
% 2.78/1.00      | sK6 != X1 ),
% 2.78/1.00      inference(instantiation,[status(thm)],[c_523]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1722,plain,
% 2.78/1.00      ( ~ r1_tarski(X0,sK6)
% 2.78/1.00      | r1_tarski(k2_relat_1(sK4(X1)),sK6)
% 2.78/1.00      | k2_relat_1(sK4(X1)) != X0
% 2.78/1.00      | sK6 != sK6 ),
% 2.78/1.00      inference(instantiation,[status(thm)],[c_1262]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1725,plain,
% 2.78/1.00      ( r1_tarski(k2_relat_1(sK4(k1_xboole_0)),sK6)
% 2.78/1.00      | ~ r1_tarski(k1_xboole_0,sK6)
% 2.78/1.00      | k2_relat_1(sK4(k1_xboole_0)) != k1_xboole_0
% 2.78/1.00      | sK6 != sK6 ),
% 2.78/1.00      inference(instantiation,[status(thm)],[c_1722]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_521,plain,( X0 = X0 ),theory(equality) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1723,plain,
% 2.78/1.00      ( sK6 = sK6 ),
% 2.78/1.00      inference(instantiation,[status(thm)],[c_521]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_2047,plain,
% 2.78/1.00      ( r1_tarski(k1_xboole_0,sK6) ),
% 2.78/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_4373,plain,
% 2.78/1.00      ( sK0(k1_tarski(X0),sK6) = X0 ),
% 2.78/1.00      inference(global_propositional_subsumption,
% 2.78/1.00                [status(thm)],
% 2.78/1.00                [c_3654,c_46,c_338,c_1225,c_1725,c_1723,c_2047]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_0,plain,
% 2.78/1.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.78/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_968,plain,
% 2.78/1.00      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 2.78/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_4377,plain,
% 2.78/1.00      ( r2_hidden(X0,sK6) != iProver_top
% 2.78/1.00      | r1_tarski(k1_tarski(X0),sK6) = iProver_top ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_4373,c_968]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_4387,plain,
% 2.78/1.00      ( r2_hidden(X0,sK6) != iProver_top ),
% 2.78/1.00      inference(global_propositional_subsumption,
% 2.78/1.00                [status(thm)],
% 2.78/1.00                [c_4377,c_46,c_338,c_1225,c_1503,c_1725,c_1723,c_2047]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_4401,plain,
% 2.78/1.00      ( sK6 = k1_xboole_0 ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_2625,c_4387]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_522,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_2147,plain,
% 2.78/1.00      ( X0 != X1 | sK7 != X1 | sK7 = X0 ),
% 2.78/1.00      inference(instantiation,[status(thm)],[c_522]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_3777,plain,
% 2.78/1.00      ( X0 != sK7 | sK7 = X0 | sK7 != sK7 ),
% 2.78/1.00      inference(instantiation,[status(thm)],[c_2147]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_3779,plain,
% 2.78/1.00      ( sK7 != sK7 | sK7 = k1_xboole_0 | k1_xboole_0 != sK7 ),
% 2.78/1.00      inference(instantiation,[status(thm)],[c_3777]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_15,plain,
% 2.78/1.00      ( r2_hidden(X0,k1_tarski(X0)) ),
% 2.78/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_3607,plain,
% 2.78/1.00      ( r2_hidden(sK7,k1_tarski(sK7)) ),
% 2.78/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_2132,plain,
% 2.78/1.00      ( ~ r2_hidden(sK7,k1_tarski(X0)) | sK7 = X0 ),
% 2.78/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_3606,plain,
% 2.78/1.00      ( ~ r2_hidden(sK7,k1_tarski(sK7)) | sK7 = sK7 ),
% 2.78/1.00      inference(instantiation,[status(thm)],[c_2132]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1202,plain,
% 2.78/1.00      ( sK6 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK6 ),
% 2.78/1.00      inference(instantiation,[status(thm)],[c_522]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1203,plain,
% 2.78/1.00      ( sK6 != k1_xboole_0
% 2.78/1.00      | k1_xboole_0 = sK6
% 2.78/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 2.78/1.00      inference(instantiation,[status(thm)],[c_1202]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_60,plain,
% 2.78/1.00      ( r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
% 2.78/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_57,plain,
% 2.78/1.00      ( ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
% 2.78/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 2.78/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_28,negated_conjecture,
% 2.78/1.00      ( k1_xboole_0 = sK7 | k1_xboole_0 != sK6 ),
% 2.78/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(contradiction,plain,
% 2.78/1.00      ( $false ),
% 2.78/1.00      inference(minisat,
% 2.78/1.00                [status(thm)],
% 2.78/1.00                [c_4401,c_3779,c_3607,c_3606,c_2047,c_1723,c_1725,c_1225,
% 2.78/1.00                 c_1203,c_338,c_60,c_57,c_46,c_28]) ).
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.78/1.00  
% 2.78/1.00  ------                               Statistics
% 2.78/1.00  
% 2.78/1.00  ------ General
% 2.78/1.00  
% 2.78/1.00  abstr_ref_over_cycles:                  0
% 2.78/1.00  abstr_ref_under_cycles:                 0
% 2.78/1.00  gc_basic_clause_elim:                   0
% 2.78/1.00  forced_gc_time:                         0
% 2.78/1.00  parsing_time:                           0.01
% 2.78/1.00  unif_index_cands_time:                  0.
% 2.78/1.00  unif_index_add_time:                    0.
% 2.78/1.00  orderings_time:                         0.
% 2.78/1.00  out_proof_time:                         0.009
% 2.78/1.00  total_time:                             0.167
% 2.78/1.00  num_of_symbols:                         50
% 2.78/1.00  num_of_terms:                           5114
% 2.78/1.00  
% 2.78/1.00  ------ Preprocessing
% 2.78/1.00  
% 2.78/1.00  num_of_splits:                          0
% 2.78/1.00  num_of_split_atoms:                     0
% 2.78/1.00  num_of_reused_defs:                     0
% 2.78/1.00  num_eq_ax_congr_red:                    30
% 2.78/1.00  num_of_sem_filtered_clauses:            1
% 2.78/1.00  num_of_subtypes:                        0
% 2.78/1.00  monotx_restored_types:                  0
% 2.78/1.00  sat_num_of_epr_types:                   0
% 2.78/1.00  sat_num_of_non_cyclic_types:            0
% 2.78/1.00  sat_guarded_non_collapsed_types:        0
% 2.78/1.00  num_pure_diseq_elim:                    0
% 2.78/1.00  simp_replaced_by:                       0
% 2.78/1.00  res_preprocessed:                       108
% 2.78/1.00  prep_upred:                             0
% 2.78/1.00  prep_unflattend:                        19
% 2.78/1.00  smt_new_axioms:                         0
% 2.78/1.00  pred_elim_cands:                        4
% 2.78/1.00  pred_elim:                              0
% 2.78/1.00  pred_elim_cl:                           0
% 2.78/1.00  pred_elim_cycles:                       3
% 2.78/1.00  merged_defs:                            0
% 2.78/1.00  merged_defs_ncl:                        0
% 2.78/1.00  bin_hyper_res:                          0
% 2.78/1.00  prep_cycles:                            3
% 2.78/1.00  pred_elim_time:                         0.004
% 2.78/1.00  splitting_time:                         0.
% 2.78/1.00  sem_filter_time:                        0.
% 2.78/1.00  monotx_time:                            0.
% 2.78/1.00  subtype_inf_time:                       0.
% 2.78/1.00  
% 2.78/1.00  ------ Problem properties
% 2.78/1.00  
% 2.78/1.00  clauses:                                29
% 2.78/1.00  conjectures:                            2
% 2.78/1.00  epr:                                    3
% 2.78/1.00  horn:                                   18
% 2.78/1.00  ground:                                 1
% 2.78/1.00  unary:                                  6
% 2.78/1.00  binary:                                 11
% 2.78/1.00  lits:                                   66
% 2.78/1.00  lits_eq:                                26
% 2.78/1.00  fd_pure:                                0
% 2.78/1.00  fd_pseudo:                              0
% 2.78/1.00  fd_cond:                                3
% 2.78/1.00  fd_pseudo_cond:                         7
% 2.78/1.00  ac_symbols:                             0
% 2.78/1.00  
% 2.78/1.00  ------ Propositional Solver
% 2.78/1.00  
% 2.78/1.00  prop_solver_calls:                      23
% 2.78/1.00  prop_fast_solver_calls:                 682
% 2.78/1.00  smt_solver_calls:                       0
% 2.78/1.00  smt_fast_solver_calls:                  0
% 2.78/1.00  prop_num_of_clauses:                    1873
% 2.78/1.00  prop_preprocess_simplified:             5938
% 2.78/1.00  prop_fo_subsumed:                       13
% 2.78/1.00  prop_solver_time:                       0.
% 2.78/1.00  smt_solver_time:                        0.
% 2.78/1.00  smt_fast_solver_time:                   0.
% 2.78/1.00  prop_fast_solver_time:                  0.
% 2.78/1.00  prop_unsat_core_time:                   0.
% 2.78/1.00  
% 2.78/1.00  ------ QBF
% 2.78/1.00  
% 2.78/1.00  qbf_q_res:                              0
% 2.78/1.00  qbf_num_tautologies:                    0
% 2.78/1.00  qbf_prep_cycles:                        0
% 2.78/1.00  
% 2.78/1.00  ------ BMC1
% 2.78/1.00  
% 2.78/1.00  bmc1_current_bound:                     -1
% 2.78/1.00  bmc1_last_solved_bound:                 -1
% 2.78/1.00  bmc1_unsat_core_size:                   -1
% 2.78/1.00  bmc1_unsat_core_parents_size:           -1
% 2.78/1.00  bmc1_merge_next_fun:                    0
% 2.78/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.78/1.00  
% 2.78/1.00  ------ Instantiation
% 2.78/1.00  
% 2.78/1.00  inst_num_of_clauses:                    484
% 2.78/1.00  inst_num_in_passive:                    158
% 2.78/1.00  inst_num_in_active:                     178
% 2.78/1.00  inst_num_in_unprocessed:                148
% 2.78/1.00  inst_num_of_loops:                      260
% 2.78/1.00  inst_num_of_learning_restarts:          0
% 2.78/1.00  inst_num_moves_active_passive:          80
% 2.78/1.00  inst_lit_activity:                      0
% 2.78/1.00  inst_lit_activity_moves:                0
% 2.78/1.00  inst_num_tautologies:                   0
% 2.78/1.00  inst_num_prop_implied:                  0
% 2.78/1.00  inst_num_existing_simplified:           0
% 2.78/1.00  inst_num_eq_res_simplified:             0
% 2.78/1.00  inst_num_child_elim:                    0
% 2.78/1.00  inst_num_of_dismatching_blockings:      53
% 2.78/1.00  inst_num_of_non_proper_insts:           290
% 2.78/1.00  inst_num_of_duplicates:                 0
% 2.78/1.00  inst_inst_num_from_inst_to_res:         0
% 2.78/1.00  inst_dismatching_checking_time:         0.
% 2.78/1.00  
% 2.78/1.00  ------ Resolution
% 2.78/1.00  
% 2.78/1.00  res_num_of_clauses:                     0
% 2.78/1.00  res_num_in_passive:                     0
% 2.78/1.00  res_num_in_active:                      0
% 2.78/1.00  res_num_of_loops:                       111
% 2.78/1.00  res_forward_subset_subsumed:            7
% 2.78/1.00  res_backward_subset_subsumed:           0
% 2.78/1.00  res_forward_subsumed:                   0
% 2.78/1.00  res_backward_subsumed:                  0
% 2.78/1.00  res_forward_subsumption_resolution:     0
% 2.78/1.00  res_backward_subsumption_resolution:    0
% 2.78/1.00  res_clause_to_clause_subsumption:       388
% 2.78/1.00  res_orphan_elimination:                 0
% 2.78/1.00  res_tautology_del:                      19
% 2.78/1.00  res_num_eq_res_simplified:              0
% 2.78/1.00  res_num_sel_changes:                    0
% 2.78/1.00  res_moves_from_active_to_pass:          0
% 2.78/1.00  
% 2.78/1.00  ------ Superposition
% 2.78/1.00  
% 2.78/1.00  sup_time_total:                         0.
% 2.78/1.00  sup_time_generating:                    0.
% 2.78/1.00  sup_time_sim_full:                      0.
% 2.78/1.00  sup_time_sim_immed:                     0.
% 2.78/1.00  
% 2.78/1.00  sup_num_of_clauses:                     105
% 2.78/1.00  sup_num_in_active:                      52
% 2.78/1.00  sup_num_in_passive:                     53
% 2.78/1.00  sup_num_of_loops:                       51
% 2.78/1.00  sup_fw_superposition:                   40
% 2.78/1.00  sup_bw_superposition:                   63
% 2.78/1.00  sup_immediate_simplified:               10
% 2.78/1.00  sup_given_eliminated:                   1
% 2.78/1.00  comparisons_done:                       0
% 2.78/1.00  comparisons_avoided:                    5
% 2.78/1.00  
% 2.78/1.00  ------ Simplifications
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  sim_fw_subset_subsumed:                 2
% 2.78/1.00  sim_bw_subset_subsumed:                 0
% 2.78/1.00  sim_fw_subsumed:                        5
% 2.78/1.00  sim_bw_subsumed:                        0
% 2.78/1.00  sim_fw_subsumption_res:                 0
% 2.78/1.00  sim_bw_subsumption_res:                 0
% 2.78/1.00  sim_tautology_del:                      9
% 2.78/1.00  sim_eq_tautology_del:                   4
% 2.78/1.00  sim_eq_res_simp:                        1
% 2.78/1.00  sim_fw_demodulated:                     2
% 2.78/1.00  sim_bw_demodulated:                     1
% 2.78/1.00  sim_light_normalised:                   3
% 2.78/1.00  sim_joinable_taut:                      0
% 2.78/1.00  sim_joinable_simp:                      0
% 2.78/1.00  sim_ac_normalised:                      0
% 2.78/1.00  sim_smt_subsumption:                    0
% 2.78/1.00  
%------------------------------------------------------------------------------
