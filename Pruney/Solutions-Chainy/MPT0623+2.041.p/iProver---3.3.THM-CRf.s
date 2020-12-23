%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:38 EST 2020

% Result     : Theorem 0.71s
% Output     : CNFRefutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 536 expanded)
%              Number of clauses        :   82 ( 184 expanded)
%              Number of leaves         :   20 ( 121 expanded)
%              Depth                    :   22
%              Number of atoms          :  479 (2325 expanded)
%              Number of equality atoms :  245 (1145 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f39,plain,(
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

fof(f40,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f90,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f65])).

fof(f13,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f44,plain,(
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

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tarski(X1) = k2_relat_1(sK5(X0,X1))
          & k1_relat_1(sK5(X0,X1)) = X0
          & v1_funct_1(sK5(X0,X1))
          & v1_relat_1(sK5(X0,X1)) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f44])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK5(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK5(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f23])).

fof(f46,plain,
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

fof(f47,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK6)
        | k1_relat_1(X2) != sK7
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK7
      | k1_xboole_0 != sK6 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f24,f46])).

fof(f81,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK6)
      | k1_relat_1(X2) != sK7
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK5(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK5(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f84,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f69,f61])).

fof(f80,plain,
    ( k1_xboole_0 = sK7
    | k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f47])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f88,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f66])).

fof(f89,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f88])).

fof(f7,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f86,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f12,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK4(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK4(X0)) = X0
        & v1_funct_1(sK4(X0))
        & v1_relat_1(sK4(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK4(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK4(X0)) = X0
      & v1_funct_1(sK4(X0))
      & v1_relat_1(sK4(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f42])).

fof(f74,plain,(
    ! [X0] : k1_relat_1(sK4(X0)) = X0 ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,(
    ! [X0] : v1_relat_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f73,plain,(
    ! [X0] : v1_funct_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f41,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f70,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1316,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1320,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1302,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2659,plain,
    ( sK0(k1_tarski(X0),X1) = X0
    | r1_tarski(k1_tarski(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1320,c_1302])).

cnf(c_27,plain,
    ( k2_relat_1(sK5(X0,X1)) = k1_tarski(X1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_28,plain,
    ( k1_relat_1(sK5(X0,X1)) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_31,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(X0),sK6)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) != sK7 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1294,plain,
    ( k1_relat_1(X0) != sK7
    | r1_tarski(k2_relat_1(X0),sK6) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1780,plain,
    ( sK7 != X0
    | k1_xboole_0 = X0
    | r1_tarski(k2_relat_1(sK5(X0,X1)),sK6) != iProver_top
    | v1_funct_1(sK5(X0,X1)) != iProver_top
    | v1_relat_1(sK5(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_28,c_1294])).

cnf(c_30,plain,
    ( v1_relat_1(sK5(X0,X1))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_36,plain,
    ( k1_xboole_0 = X0
    | v1_relat_1(sK5(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,plain,
    ( v1_funct_1(sK5(X0,X1))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_39,plain,
    ( k1_xboole_0 = X0
    | v1_funct_1(sK5(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1913,plain,
    ( sK7 != X0
    | k1_xboole_0 = X0
    | r1_tarski(k2_relat_1(sK5(X0,X1)),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1780,c_36,c_39])).

cnf(c_1920,plain,
    ( sK7 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK5(sK7,X0)),sK6) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1913])).

cnf(c_1964,plain,
    ( sK7 = k1_xboole_0
    | r1_tarski(k1_tarski(X0),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_1920])).

cnf(c_6303,plain,
    ( sK0(k1_tarski(X0),sK6) = X0
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2659,c_1964])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1321,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7524,plain,
    ( sK7 = k1_xboole_0
    | r2_hidden(X0,sK6) != iProver_top
    | r1_tarski(k1_tarski(X0),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_6303,c_1321])).

cnf(c_7734,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | sK7 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7524,c_1964])).

cnf(c_7735,plain,
    ( sK7 = k1_xboole_0
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_7734])).

cnf(c_7743,plain,
    ( k4_xboole_0(sK6,X0) = X1
    | sK7 = k1_xboole_0
    | r2_hidden(sK1(sK6,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1316,c_7735])).

cnf(c_8282,plain,
    ( k4_xboole_0(sK6,X0) = sK6
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7743,c_7735])).

cnf(c_20,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_8390,plain,
    ( k1_setfam_1(k2_tarski(sK6,X0)) = sK6
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8282,c_20])).

cnf(c_32,negated_conjecture,
    ( k1_xboole_0 = sK7
    | k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_62,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_18,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_65,plain,
    ( r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_631,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1598,plain,
    ( sK6 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_631])).

cnf(c_1599,plain,
    ( sK6 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1598])).

cnf(c_2269,plain,
    ( ~ r2_hidden(sK7,k1_tarski(X0))
    | sK7 = X0 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2406,plain,
    ( ~ r2_hidden(sK7,k1_tarski(sK7))
    | sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_2269])).

cnf(c_2407,plain,
    ( r2_hidden(sK7,k1_tarski(sK7)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2268,plain,
    ( X0 != X1
    | sK7 != X1
    | sK7 = X0 ),
    inference(instantiation,[status(thm)],[c_631])).

cnf(c_2636,plain,
    ( X0 != sK7
    | sK7 = X0
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_2268])).

cnf(c_2638,plain,
    ( sK7 != sK7
    | sK7 = k1_xboole_0
    | k1_xboole_0 != sK7 ),
    inference(instantiation,[status(thm)],[c_2636])).

cnf(c_7744,plain,
    ( k4_xboole_0(X0,X1) = sK6
    | sK7 = k1_xboole_0
    | r2_hidden(sK1(X0,X1,sK6),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1316,c_7735])).

cnf(c_13,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1308,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1312,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2300,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1308,c_1312])).

cnf(c_15,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1306,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2305,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2300,c_1306])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1314,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2783,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2305,c_1314])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_12,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_581,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | X3 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_12])).

cnf(c_582,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_581])).

cnf(c_583,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_582])).

cnf(c_2917,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2783,c_583])).

cnf(c_8722,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = sK6
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7744,c_2917])).

cnf(c_8757,plain,
    ( sK7 = k1_xboole_0
    | sK6 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8722,c_2305])).

cnf(c_8956,plain,
    ( sK7 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8390,c_32,c_62,c_65,c_1599,c_2406,c_2407,c_2638,c_8757])).

cnf(c_24,plain,
    ( k1_relat_1(sK4(X0)) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1568,plain,
    ( sK7 != X0
    | r1_tarski(k2_relat_1(sK4(X0)),sK6) != iProver_top
    | v1_funct_1(sK4(X0)) != iProver_top
    | v1_relat_1(sK4(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_24,c_1294])).

cnf(c_26,plain,
    ( v1_relat_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_44,plain,
    ( v1_relat_1(sK4(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,plain,
    ( v1_funct_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_47,plain,
    ( v1_funct_1(sK4(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1573,plain,
    ( sK7 != X0
    | r1_tarski(k2_relat_1(sK4(X0)),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1568,c_44,c_47])).

cnf(c_1581,plain,
    ( r1_tarski(k2_relat_1(sK4(sK7)),sK6) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1573])).

cnf(c_8962,plain,
    ( r1_tarski(k2_relat_1(sK4(k1_xboole_0)),sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8956,c_1581])).

cnf(c_22,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1300,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2560,plain,
    ( k2_relat_1(sK4(X0)) = k1_xboole_0
    | k1_xboole_0 != X0
    | v1_relat_1(sK4(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_24,c_1300])).

cnf(c_3768,plain,
    ( k1_xboole_0 != X0
    | k2_relat_1(sK4(X0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2560,c_44])).

cnf(c_3769,plain,
    ( k2_relat_1(sK4(X0)) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(renaming,[status(thm)],[c_3768])).

cnf(c_3773,plain,
    ( k2_relat_1(sK4(k1_xboole_0)) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_3769])).

cnf(c_8979,plain,
    ( r1_tarski(k1_xboole_0,sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8962,c_3773])).

cnf(c_7819,plain,
    ( r1_tarski(k1_xboole_0,sK6) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_7822,plain,
    ( r1_tarski(k1_xboole_0,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7819])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8979,c_7822])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:26:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 0.71/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.71/1.03  
% 0.71/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.71/1.03  
% 0.71/1.03  ------  iProver source info
% 0.71/1.03  
% 0.71/1.03  git: date: 2020-06-30 10:37:57 +0100
% 0.71/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.71/1.03  git: non_committed_changes: false
% 0.71/1.03  git: last_make_outside_of_git: false
% 0.71/1.03  
% 0.71/1.03  ------ 
% 0.71/1.03  
% 0.71/1.03  ------ Input Options
% 0.71/1.03  
% 0.71/1.03  --out_options                           all
% 0.71/1.03  --tptp_safe_out                         true
% 0.71/1.03  --problem_path                          ""
% 0.71/1.03  --include_path                          ""
% 0.71/1.03  --clausifier                            res/vclausify_rel
% 0.71/1.03  --clausifier_options                    --mode clausify
% 0.71/1.03  --stdin                                 false
% 0.71/1.03  --stats_out                             all
% 0.71/1.03  
% 0.71/1.03  ------ General Options
% 0.71/1.03  
% 0.71/1.03  --fof                                   false
% 0.71/1.03  --time_out_real                         305.
% 0.71/1.03  --time_out_virtual                      -1.
% 0.71/1.03  --symbol_type_check                     false
% 0.71/1.03  --clausify_out                          false
% 0.71/1.03  --sig_cnt_out                           false
% 0.71/1.03  --trig_cnt_out                          false
% 0.71/1.03  --trig_cnt_out_tolerance                1.
% 0.71/1.03  --trig_cnt_out_sk_spl                   false
% 0.71/1.03  --abstr_cl_out                          false
% 0.71/1.03  
% 0.71/1.03  ------ Global Options
% 0.71/1.03  
% 0.71/1.03  --schedule                              default
% 0.71/1.03  --add_important_lit                     false
% 0.71/1.03  --prop_solver_per_cl                    1000
% 0.71/1.03  --min_unsat_core                        false
% 0.71/1.03  --soft_assumptions                      false
% 0.71/1.03  --soft_lemma_size                       3
% 0.71/1.03  --prop_impl_unit_size                   0
% 0.71/1.03  --prop_impl_unit                        []
% 0.71/1.03  --share_sel_clauses                     true
% 0.71/1.03  --reset_solvers                         false
% 0.71/1.03  --bc_imp_inh                            [conj_cone]
% 0.71/1.03  --conj_cone_tolerance                   3.
% 0.71/1.03  --extra_neg_conj                        none
% 0.71/1.03  --large_theory_mode                     true
% 0.71/1.03  --prolific_symb_bound                   200
% 0.71/1.03  --lt_threshold                          2000
% 0.71/1.03  --clause_weak_htbl                      true
% 0.71/1.03  --gc_record_bc_elim                     false
% 0.71/1.03  
% 0.71/1.03  ------ Preprocessing Options
% 0.71/1.03  
% 0.71/1.03  --preprocessing_flag                    true
% 0.71/1.03  --time_out_prep_mult                    0.1
% 0.71/1.03  --splitting_mode                        input
% 0.71/1.03  --splitting_grd                         true
% 0.71/1.03  --splitting_cvd                         false
% 0.71/1.03  --splitting_cvd_svl                     false
% 0.71/1.03  --splitting_nvd                         32
% 0.71/1.03  --sub_typing                            true
% 0.71/1.03  --prep_gs_sim                           true
% 0.71/1.03  --prep_unflatten                        true
% 0.71/1.03  --prep_res_sim                          true
% 0.71/1.03  --prep_upred                            true
% 0.71/1.03  --prep_sem_filter                       exhaustive
% 0.71/1.03  --prep_sem_filter_out                   false
% 0.71/1.03  --pred_elim                             true
% 0.71/1.03  --res_sim_input                         true
% 0.71/1.03  --eq_ax_congr_red                       true
% 0.71/1.03  --pure_diseq_elim                       true
% 0.71/1.03  --brand_transform                       false
% 0.71/1.03  --non_eq_to_eq                          false
% 0.71/1.03  --prep_def_merge                        true
% 0.71/1.03  --prep_def_merge_prop_impl              false
% 0.71/1.03  --prep_def_merge_mbd                    true
% 0.71/1.03  --prep_def_merge_tr_red                 false
% 0.71/1.03  --prep_def_merge_tr_cl                  false
% 0.71/1.03  --smt_preprocessing                     true
% 0.71/1.03  --smt_ac_axioms                         fast
% 0.71/1.03  --preprocessed_out                      false
% 0.71/1.03  --preprocessed_stats                    false
% 0.71/1.03  
% 0.71/1.03  ------ Abstraction refinement Options
% 0.71/1.03  
% 0.71/1.03  --abstr_ref                             []
% 0.71/1.03  --abstr_ref_prep                        false
% 0.71/1.03  --abstr_ref_until_sat                   false
% 0.71/1.03  --abstr_ref_sig_restrict                funpre
% 0.71/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 0.71/1.03  --abstr_ref_under                       []
% 0.71/1.03  
% 0.71/1.03  ------ SAT Options
% 0.71/1.03  
% 0.71/1.03  --sat_mode                              false
% 0.71/1.03  --sat_fm_restart_options                ""
% 0.71/1.03  --sat_gr_def                            false
% 0.71/1.03  --sat_epr_types                         true
% 0.71/1.03  --sat_non_cyclic_types                  false
% 0.71/1.03  --sat_finite_models                     false
% 0.71/1.03  --sat_fm_lemmas                         false
% 0.71/1.03  --sat_fm_prep                           false
% 0.71/1.03  --sat_fm_uc_incr                        true
% 0.71/1.03  --sat_out_model                         small
% 0.71/1.03  --sat_out_clauses                       false
% 0.71/1.03  
% 0.71/1.03  ------ QBF Options
% 0.71/1.03  
% 0.71/1.03  --qbf_mode                              false
% 0.71/1.03  --qbf_elim_univ                         false
% 0.71/1.03  --qbf_dom_inst                          none
% 0.71/1.03  --qbf_dom_pre_inst                      false
% 0.71/1.03  --qbf_sk_in                             false
% 0.71/1.03  --qbf_pred_elim                         true
% 0.71/1.03  --qbf_split                             512
% 0.71/1.03  
% 0.71/1.03  ------ BMC1 Options
% 0.71/1.03  
% 0.71/1.03  --bmc1_incremental                      false
% 0.71/1.03  --bmc1_axioms                           reachable_all
% 0.71/1.03  --bmc1_min_bound                        0
% 0.71/1.03  --bmc1_max_bound                        -1
% 0.71/1.03  --bmc1_max_bound_default                -1
% 0.71/1.03  --bmc1_symbol_reachability              true
% 0.71/1.03  --bmc1_property_lemmas                  false
% 0.71/1.03  --bmc1_k_induction                      false
% 0.71/1.03  --bmc1_non_equiv_states                 false
% 0.71/1.03  --bmc1_deadlock                         false
% 0.71/1.03  --bmc1_ucm                              false
% 0.71/1.03  --bmc1_add_unsat_core                   none
% 0.71/1.03  --bmc1_unsat_core_children              false
% 0.71/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 0.71/1.03  --bmc1_out_stat                         full
% 0.71/1.03  --bmc1_ground_init                      false
% 0.71/1.03  --bmc1_pre_inst_next_state              false
% 0.71/1.03  --bmc1_pre_inst_state                   false
% 0.71/1.03  --bmc1_pre_inst_reach_state             false
% 0.71/1.03  --bmc1_out_unsat_core                   false
% 0.71/1.03  --bmc1_aig_witness_out                  false
% 0.71/1.03  --bmc1_verbose                          false
% 0.71/1.03  --bmc1_dump_clauses_tptp                false
% 0.71/1.03  --bmc1_dump_unsat_core_tptp             false
% 0.71/1.03  --bmc1_dump_file                        -
% 0.71/1.03  --bmc1_ucm_expand_uc_limit              128
% 0.71/1.03  --bmc1_ucm_n_expand_iterations          6
% 0.71/1.03  --bmc1_ucm_extend_mode                  1
% 0.71/1.03  --bmc1_ucm_init_mode                    2
% 0.71/1.03  --bmc1_ucm_cone_mode                    none
% 0.71/1.03  --bmc1_ucm_reduced_relation_type        0
% 0.71/1.03  --bmc1_ucm_relax_model                  4
% 0.71/1.03  --bmc1_ucm_full_tr_after_sat            true
% 0.71/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 0.71/1.03  --bmc1_ucm_layered_model                none
% 0.71/1.03  --bmc1_ucm_max_lemma_size               10
% 0.71/1.03  
% 0.71/1.03  ------ AIG Options
% 0.71/1.03  
% 0.71/1.03  --aig_mode                              false
% 0.71/1.03  
% 0.71/1.03  ------ Instantiation Options
% 0.71/1.03  
% 0.71/1.03  --instantiation_flag                    true
% 0.71/1.03  --inst_sos_flag                         false
% 0.71/1.03  --inst_sos_phase                        true
% 0.71/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.71/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.71/1.03  --inst_lit_sel_side                     num_symb
% 0.71/1.03  --inst_solver_per_active                1400
% 0.71/1.03  --inst_solver_calls_frac                1.
% 0.71/1.03  --inst_passive_queue_type               priority_queues
% 0.71/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.71/1.03  --inst_passive_queues_freq              [25;2]
% 0.71/1.03  --inst_dismatching                      true
% 0.71/1.03  --inst_eager_unprocessed_to_passive     true
% 0.71/1.03  --inst_prop_sim_given                   true
% 0.71/1.03  --inst_prop_sim_new                     false
% 0.71/1.03  --inst_subs_new                         false
% 0.71/1.03  --inst_eq_res_simp                      false
% 0.71/1.03  --inst_subs_given                       false
% 0.71/1.03  --inst_orphan_elimination               true
% 0.71/1.03  --inst_learning_loop_flag               true
% 0.71/1.03  --inst_learning_start                   3000
% 0.71/1.03  --inst_learning_factor                  2
% 0.71/1.03  --inst_start_prop_sim_after_learn       3
% 0.71/1.03  --inst_sel_renew                        solver
% 0.71/1.03  --inst_lit_activity_flag                true
% 0.71/1.03  --inst_restr_to_given                   false
% 0.71/1.03  --inst_activity_threshold               500
% 0.71/1.03  --inst_out_proof                        true
% 0.71/1.03  
% 0.71/1.03  ------ Resolution Options
% 0.71/1.03  
% 0.71/1.03  --resolution_flag                       true
% 0.71/1.03  --res_lit_sel                           adaptive
% 0.71/1.03  --res_lit_sel_side                      none
% 0.71/1.03  --res_ordering                          kbo
% 0.71/1.03  --res_to_prop_solver                    active
% 0.71/1.03  --res_prop_simpl_new                    false
% 0.71/1.03  --res_prop_simpl_given                  true
% 0.71/1.03  --res_passive_queue_type                priority_queues
% 0.71/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.71/1.03  --res_passive_queues_freq               [15;5]
% 0.71/1.03  --res_forward_subs                      full
% 0.71/1.03  --res_backward_subs                     full
% 0.71/1.03  --res_forward_subs_resolution           true
% 0.71/1.03  --res_backward_subs_resolution          true
% 0.71/1.03  --res_orphan_elimination                true
% 0.71/1.03  --res_time_limit                        2.
% 0.71/1.03  --res_out_proof                         true
% 0.71/1.03  
% 0.71/1.03  ------ Superposition Options
% 0.71/1.03  
% 0.71/1.03  --superposition_flag                    true
% 0.71/1.03  --sup_passive_queue_type                priority_queues
% 0.71/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.71/1.03  --sup_passive_queues_freq               [8;1;4]
% 0.71/1.03  --demod_completeness_check              fast
% 0.71/1.03  --demod_use_ground                      true
% 0.71/1.03  --sup_to_prop_solver                    passive
% 0.71/1.03  --sup_prop_simpl_new                    true
% 0.71/1.03  --sup_prop_simpl_given                  true
% 0.71/1.03  --sup_fun_splitting                     false
% 0.71/1.03  --sup_smt_interval                      50000
% 0.71/1.03  
% 0.71/1.03  ------ Superposition Simplification Setup
% 0.71/1.03  
% 0.71/1.03  --sup_indices_passive                   []
% 0.71/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.71/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.71/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.71/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 0.71/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.71/1.03  --sup_full_bw                           [BwDemod]
% 0.71/1.03  --sup_immed_triv                        [TrivRules]
% 0.71/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.71/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.71/1.03  --sup_immed_bw_main                     []
% 0.71/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.71/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 0.71/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.71/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.71/1.03  
% 0.71/1.03  ------ Combination Options
% 0.71/1.03  
% 0.71/1.03  --comb_res_mult                         3
% 0.71/1.03  --comb_sup_mult                         2
% 0.71/1.03  --comb_inst_mult                        10
% 0.71/1.03  
% 0.71/1.03  ------ Debug Options
% 0.71/1.03  
% 0.71/1.03  --dbg_backtrace                         false
% 0.71/1.03  --dbg_dump_prop_clauses                 false
% 0.71/1.03  --dbg_dump_prop_clauses_file            -
% 0.71/1.03  --dbg_out_stat                          false
% 0.71/1.03  ------ Parsing...
% 0.71/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.71/1.03  
% 0.71/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 0.71/1.03  
% 0.71/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.71/1.03  
% 0.71/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.71/1.03  ------ Proving...
% 0.71/1.03  ------ Problem Properties 
% 0.71/1.03  
% 0.71/1.03  
% 0.71/1.03  clauses                                 33
% 0.71/1.03  conjectures                             2
% 0.71/1.03  EPR                                     5
% 0.71/1.03  Horn                                    22
% 0.71/1.03  unary                                   7
% 0.71/1.03  binary                                  16
% 0.71/1.03  lits                                    71
% 0.71/1.03  lits eq                                 26
% 0.71/1.03  fd_pure                                 0
% 0.71/1.03  fd_pseudo                               0
% 0.71/1.03  fd_cond                                 3
% 0.71/1.03  fd_pseudo_cond                          5
% 0.71/1.03  AC symbols                              0
% 0.71/1.03  
% 0.71/1.03  ------ Schedule dynamic 5 is on 
% 0.71/1.03  
% 0.71/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.71/1.03  
% 0.71/1.03  
% 0.71/1.03  ------ 
% 0.71/1.03  Current options:
% 0.71/1.03  ------ 
% 0.71/1.03  
% 0.71/1.03  ------ Input Options
% 0.71/1.03  
% 0.71/1.03  --out_options                           all
% 0.71/1.03  --tptp_safe_out                         true
% 0.71/1.03  --problem_path                          ""
% 0.71/1.03  --include_path                          ""
% 0.71/1.03  --clausifier                            res/vclausify_rel
% 0.71/1.03  --clausifier_options                    --mode clausify
% 0.71/1.03  --stdin                                 false
% 0.71/1.03  --stats_out                             all
% 0.71/1.03  
% 0.71/1.03  ------ General Options
% 0.71/1.03  
% 0.71/1.03  --fof                                   false
% 0.71/1.03  --time_out_real                         305.
% 0.71/1.03  --time_out_virtual                      -1.
% 0.71/1.03  --symbol_type_check                     false
% 0.71/1.03  --clausify_out                          false
% 0.71/1.03  --sig_cnt_out                           false
% 0.71/1.03  --trig_cnt_out                          false
% 0.71/1.03  --trig_cnt_out_tolerance                1.
% 0.71/1.03  --trig_cnt_out_sk_spl                   false
% 0.71/1.03  --abstr_cl_out                          false
% 0.71/1.03  
% 0.71/1.03  ------ Global Options
% 0.71/1.03  
% 0.71/1.03  --schedule                              default
% 0.71/1.03  --add_important_lit                     false
% 0.71/1.03  --prop_solver_per_cl                    1000
% 0.71/1.03  --min_unsat_core                        false
% 0.71/1.03  --soft_assumptions                      false
% 0.71/1.03  --soft_lemma_size                       3
% 0.71/1.03  --prop_impl_unit_size                   0
% 0.71/1.03  --prop_impl_unit                        []
% 0.71/1.03  --share_sel_clauses                     true
% 0.71/1.03  --reset_solvers                         false
% 0.71/1.03  --bc_imp_inh                            [conj_cone]
% 0.71/1.03  --conj_cone_tolerance                   3.
% 0.71/1.03  --extra_neg_conj                        none
% 0.71/1.03  --large_theory_mode                     true
% 0.71/1.03  --prolific_symb_bound                   200
% 0.71/1.03  --lt_threshold                          2000
% 0.71/1.03  --clause_weak_htbl                      true
% 0.71/1.03  --gc_record_bc_elim                     false
% 0.71/1.03  
% 0.71/1.03  ------ Preprocessing Options
% 0.71/1.03  
% 0.71/1.03  --preprocessing_flag                    true
% 0.71/1.03  --time_out_prep_mult                    0.1
% 0.71/1.03  --splitting_mode                        input
% 0.71/1.03  --splitting_grd                         true
% 0.71/1.03  --splitting_cvd                         false
% 0.71/1.03  --splitting_cvd_svl                     false
% 0.71/1.03  --splitting_nvd                         32
% 0.71/1.03  --sub_typing                            true
% 0.71/1.03  --prep_gs_sim                           true
% 0.71/1.03  --prep_unflatten                        true
% 0.71/1.03  --prep_res_sim                          true
% 0.71/1.03  --prep_upred                            true
% 0.71/1.03  --prep_sem_filter                       exhaustive
% 0.71/1.03  --prep_sem_filter_out                   false
% 0.71/1.03  --pred_elim                             true
% 0.71/1.03  --res_sim_input                         true
% 0.71/1.03  --eq_ax_congr_red                       true
% 0.71/1.03  --pure_diseq_elim                       true
% 0.71/1.03  --brand_transform                       false
% 0.71/1.03  --non_eq_to_eq                          false
% 0.71/1.03  --prep_def_merge                        true
% 0.71/1.03  --prep_def_merge_prop_impl              false
% 0.71/1.03  --prep_def_merge_mbd                    true
% 0.71/1.03  --prep_def_merge_tr_red                 false
% 0.71/1.03  --prep_def_merge_tr_cl                  false
% 0.71/1.03  --smt_preprocessing                     true
% 0.71/1.03  --smt_ac_axioms                         fast
% 0.71/1.03  --preprocessed_out                      false
% 0.71/1.03  --preprocessed_stats                    false
% 0.71/1.03  
% 0.71/1.03  ------ Abstraction refinement Options
% 0.71/1.03  
% 0.71/1.03  --abstr_ref                             []
% 0.71/1.03  --abstr_ref_prep                        false
% 0.71/1.03  --abstr_ref_until_sat                   false
% 0.71/1.03  --abstr_ref_sig_restrict                funpre
% 0.71/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 0.71/1.03  --abstr_ref_under                       []
% 0.71/1.03  
% 0.71/1.03  ------ SAT Options
% 0.71/1.03  
% 0.71/1.03  --sat_mode                              false
% 0.71/1.03  --sat_fm_restart_options                ""
% 0.71/1.03  --sat_gr_def                            false
% 0.71/1.03  --sat_epr_types                         true
% 0.71/1.03  --sat_non_cyclic_types                  false
% 0.71/1.03  --sat_finite_models                     false
% 0.71/1.03  --sat_fm_lemmas                         false
% 0.71/1.03  --sat_fm_prep                           false
% 0.71/1.03  --sat_fm_uc_incr                        true
% 0.71/1.03  --sat_out_model                         small
% 0.71/1.03  --sat_out_clauses                       false
% 0.71/1.03  
% 0.71/1.03  ------ QBF Options
% 0.71/1.03  
% 0.71/1.03  --qbf_mode                              false
% 0.71/1.03  --qbf_elim_univ                         false
% 0.71/1.03  --qbf_dom_inst                          none
% 0.71/1.03  --qbf_dom_pre_inst                      false
% 0.71/1.03  --qbf_sk_in                             false
% 0.71/1.03  --qbf_pred_elim                         true
% 0.71/1.03  --qbf_split                             512
% 0.71/1.03  
% 0.71/1.03  ------ BMC1 Options
% 0.71/1.03  
% 0.71/1.03  --bmc1_incremental                      false
% 0.71/1.03  --bmc1_axioms                           reachable_all
% 0.71/1.03  --bmc1_min_bound                        0
% 0.71/1.03  --bmc1_max_bound                        -1
% 0.71/1.03  --bmc1_max_bound_default                -1
% 0.71/1.03  --bmc1_symbol_reachability              true
% 0.71/1.03  --bmc1_property_lemmas                  false
% 0.71/1.03  --bmc1_k_induction                      false
% 0.71/1.03  --bmc1_non_equiv_states                 false
% 0.71/1.03  --bmc1_deadlock                         false
% 0.71/1.03  --bmc1_ucm                              false
% 0.71/1.03  --bmc1_add_unsat_core                   none
% 0.71/1.03  --bmc1_unsat_core_children              false
% 0.71/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 0.71/1.03  --bmc1_out_stat                         full
% 0.71/1.03  --bmc1_ground_init                      false
% 0.71/1.03  --bmc1_pre_inst_next_state              false
% 0.71/1.03  --bmc1_pre_inst_state                   false
% 0.71/1.03  --bmc1_pre_inst_reach_state             false
% 0.71/1.03  --bmc1_out_unsat_core                   false
% 0.71/1.03  --bmc1_aig_witness_out                  false
% 0.71/1.03  --bmc1_verbose                          false
% 0.71/1.03  --bmc1_dump_clauses_tptp                false
% 0.71/1.03  --bmc1_dump_unsat_core_tptp             false
% 0.71/1.03  --bmc1_dump_file                        -
% 0.71/1.03  --bmc1_ucm_expand_uc_limit              128
% 0.71/1.03  --bmc1_ucm_n_expand_iterations          6
% 0.71/1.03  --bmc1_ucm_extend_mode                  1
% 0.71/1.03  --bmc1_ucm_init_mode                    2
% 0.71/1.03  --bmc1_ucm_cone_mode                    none
% 0.71/1.03  --bmc1_ucm_reduced_relation_type        0
% 0.71/1.03  --bmc1_ucm_relax_model                  4
% 0.71/1.03  --bmc1_ucm_full_tr_after_sat            true
% 0.71/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 0.71/1.03  --bmc1_ucm_layered_model                none
% 0.71/1.03  --bmc1_ucm_max_lemma_size               10
% 0.71/1.03  
% 0.71/1.03  ------ AIG Options
% 0.71/1.03  
% 0.71/1.03  --aig_mode                              false
% 0.71/1.03  
% 0.71/1.03  ------ Instantiation Options
% 0.71/1.03  
% 0.71/1.03  --instantiation_flag                    true
% 0.71/1.03  --inst_sos_flag                         false
% 0.71/1.03  --inst_sos_phase                        true
% 0.71/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.71/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.71/1.03  --inst_lit_sel_side                     none
% 0.71/1.03  --inst_solver_per_active                1400
% 0.71/1.03  --inst_solver_calls_frac                1.
% 0.71/1.03  --inst_passive_queue_type               priority_queues
% 0.71/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.71/1.03  --inst_passive_queues_freq              [25;2]
% 0.71/1.03  --inst_dismatching                      true
% 0.71/1.03  --inst_eager_unprocessed_to_passive     true
% 0.71/1.03  --inst_prop_sim_given                   true
% 0.71/1.03  --inst_prop_sim_new                     false
% 0.71/1.03  --inst_subs_new                         false
% 0.71/1.03  --inst_eq_res_simp                      false
% 0.71/1.03  --inst_subs_given                       false
% 0.71/1.03  --inst_orphan_elimination               true
% 0.71/1.03  --inst_learning_loop_flag               true
% 0.71/1.03  --inst_learning_start                   3000
% 0.71/1.03  --inst_learning_factor                  2
% 0.71/1.03  --inst_start_prop_sim_after_learn       3
% 0.71/1.03  --inst_sel_renew                        solver
% 0.71/1.03  --inst_lit_activity_flag                true
% 0.71/1.03  --inst_restr_to_given                   false
% 0.71/1.03  --inst_activity_threshold               500
% 0.71/1.03  --inst_out_proof                        true
% 0.71/1.03  
% 0.71/1.03  ------ Resolution Options
% 0.71/1.03  
% 0.71/1.03  --resolution_flag                       false
% 0.71/1.03  --res_lit_sel                           adaptive
% 0.71/1.03  --res_lit_sel_side                      none
% 0.71/1.03  --res_ordering                          kbo
% 0.71/1.03  --res_to_prop_solver                    active
% 0.71/1.03  --res_prop_simpl_new                    false
% 0.71/1.03  --res_prop_simpl_given                  true
% 0.71/1.03  --res_passive_queue_type                priority_queues
% 0.71/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.71/1.03  --res_passive_queues_freq               [15;5]
% 0.71/1.03  --res_forward_subs                      full
% 0.71/1.03  --res_backward_subs                     full
% 0.71/1.03  --res_forward_subs_resolution           true
% 0.71/1.03  --res_backward_subs_resolution          true
% 0.71/1.03  --res_orphan_elimination                true
% 0.71/1.03  --res_time_limit                        2.
% 0.71/1.03  --res_out_proof                         true
% 0.71/1.03  
% 0.71/1.03  ------ Superposition Options
% 0.71/1.03  
% 0.71/1.03  --superposition_flag                    true
% 0.71/1.03  --sup_passive_queue_type                priority_queues
% 0.71/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.71/1.03  --sup_passive_queues_freq               [8;1;4]
% 0.71/1.03  --demod_completeness_check              fast
% 0.71/1.03  --demod_use_ground                      true
% 0.71/1.03  --sup_to_prop_solver                    passive
% 0.71/1.03  --sup_prop_simpl_new                    true
% 0.71/1.03  --sup_prop_simpl_given                  true
% 0.71/1.03  --sup_fun_splitting                     false
% 0.71/1.03  --sup_smt_interval                      50000
% 0.71/1.03  
% 0.71/1.03  ------ Superposition Simplification Setup
% 0.71/1.03  
% 0.71/1.03  --sup_indices_passive                   []
% 0.71/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.71/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.71/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.71/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 0.71/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.71/1.03  --sup_full_bw                           [BwDemod]
% 0.71/1.03  --sup_immed_triv                        [TrivRules]
% 0.71/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.71/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.71/1.03  --sup_immed_bw_main                     []
% 0.71/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.71/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 0.71/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.71/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.71/1.03  
% 0.71/1.03  ------ Combination Options
% 0.71/1.03  
% 0.71/1.03  --comb_res_mult                         3
% 0.71/1.03  --comb_sup_mult                         2
% 0.71/1.03  --comb_inst_mult                        10
% 0.71/1.03  
% 0.71/1.03  ------ Debug Options
% 0.71/1.03  
% 0.71/1.03  --dbg_backtrace                         false
% 0.71/1.03  --dbg_dump_prop_clauses                 false
% 0.71/1.03  --dbg_dump_prop_clauses_file            -
% 0.71/1.03  --dbg_out_stat                          false
% 0.71/1.03  
% 0.71/1.03  
% 0.71/1.03  
% 0.71/1.03  
% 0.71/1.03  ------ Proving...
% 0.71/1.03  
% 0.71/1.03  
% 0.71/1.03  % SZS status Theorem for theBenchmark.p
% 0.71/1.03  
% 0.71/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 0.71/1.03  
% 0.71/1.03  fof(f2,axiom,(
% 0.71/1.03    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.71/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.71/1.03  
% 0.71/1.03  fof(f29,plain,(
% 0.71/1.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.71/1.03    inference(nnf_transformation,[],[f2])).
% 0.71/1.03  
% 0.71/1.03  fof(f30,plain,(
% 0.71/1.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.71/1.03    inference(flattening,[],[f29])).
% 0.71/1.03  
% 0.71/1.03  fof(f31,plain,(
% 0.71/1.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.71/1.03    inference(rectify,[],[f30])).
% 0.71/1.03  
% 0.71/1.03  fof(f32,plain,(
% 0.71/1.03    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 0.71/1.03    introduced(choice_axiom,[])).
% 0.71/1.03  
% 0.71/1.03  fof(f33,plain,(
% 0.71/1.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.71/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).
% 0.71/1.03  
% 0.71/1.03  fof(f54,plain,(
% 0.71/1.03    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 0.71/1.03    inference(cnf_transformation,[],[f33])).
% 0.71/1.03  
% 0.71/1.03  fof(f1,axiom,(
% 0.71/1.03    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.71/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.71/1.03  
% 0.71/1.03  fof(f17,plain,(
% 0.71/1.03    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.71/1.03    inference(ennf_transformation,[],[f1])).
% 0.71/1.03  
% 0.71/1.03  fof(f25,plain,(
% 0.71/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.71/1.03    inference(nnf_transformation,[],[f17])).
% 0.71/1.03  
% 0.71/1.03  fof(f26,plain,(
% 0.71/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.71/1.03    inference(rectify,[],[f25])).
% 0.71/1.03  
% 0.71/1.03  fof(f27,plain,(
% 0.71/1.03    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 0.71/1.03    introduced(choice_axiom,[])).
% 0.71/1.03  
% 0.71/1.03  fof(f28,plain,(
% 0.71/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.71/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 0.71/1.03  
% 0.71/1.03  fof(f49,plain,(
% 0.71/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 0.71/1.03    inference(cnf_transformation,[],[f28])).
% 0.71/1.03  
% 0.71/1.03  fof(f9,axiom,(
% 0.71/1.03    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.71/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.71/1.03  
% 0.71/1.03  fof(f37,plain,(
% 0.71/1.03    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.71/1.03    inference(nnf_transformation,[],[f9])).
% 0.71/1.03  
% 0.71/1.03  fof(f38,plain,(
% 0.71/1.03    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.71/1.03    inference(rectify,[],[f37])).
% 0.71/1.03  
% 0.71/1.03  fof(f39,plain,(
% 0.71/1.03    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 0.71/1.03    introduced(choice_axiom,[])).
% 0.71/1.03  
% 0.71/1.03  fof(f40,plain,(
% 0.71/1.03    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.71/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).
% 0.71/1.03  
% 0.71/1.03  fof(f65,plain,(
% 0.71/1.03    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.71/1.03    inference(cnf_transformation,[],[f40])).
% 0.71/1.03  
% 0.71/1.03  fof(f90,plain,(
% 0.71/1.03    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 0.71/1.03    inference(equality_resolution,[],[f65])).
% 0.71/1.03  
% 0.71/1.03  fof(f13,axiom,(
% 0.71/1.03    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.71/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.71/1.03  
% 0.71/1.03  fof(f22,plain,(
% 0.71/1.03    ! [X0] : (! [X1] : ? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 0.71/1.03    inference(ennf_transformation,[],[f13])).
% 0.71/1.03  
% 0.71/1.03  fof(f44,plain,(
% 0.71/1.03    ! [X1,X0] : (? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_tarski(X1) = k2_relat_1(sK5(X0,X1)) & k1_relat_1(sK5(X0,X1)) = X0 & v1_funct_1(sK5(X0,X1)) & v1_relat_1(sK5(X0,X1))))),
% 0.71/1.03    introduced(choice_axiom,[])).
% 0.71/1.03  
% 0.71/1.03  fof(f45,plain,(
% 0.71/1.03    ! [X0] : (! [X1] : (k1_tarski(X1) = k2_relat_1(sK5(X0,X1)) & k1_relat_1(sK5(X0,X1)) = X0 & v1_funct_1(sK5(X0,X1)) & v1_relat_1(sK5(X0,X1))) | k1_xboole_0 = X0)),
% 0.71/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f44])).
% 0.71/1.03  
% 0.71/1.03  fof(f79,plain,(
% 0.71/1.03    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK5(X0,X1)) | k1_xboole_0 = X0) )),
% 0.71/1.03    inference(cnf_transformation,[],[f45])).
% 0.71/1.03  
% 0.71/1.03  fof(f78,plain,(
% 0.71/1.03    ( ! [X0,X1] : (k1_relat_1(sK5(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 0.71/1.03    inference(cnf_transformation,[],[f45])).
% 0.71/1.03  
% 0.71/1.03  fof(f14,conjecture,(
% 0.71/1.03    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.71/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.71/1.03  
% 0.71/1.03  fof(f15,negated_conjecture,(
% 0.71/1.03    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.71/1.03    inference(negated_conjecture,[],[f14])).
% 0.71/1.03  
% 0.71/1.03  fof(f23,plain,(
% 0.71/1.03    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.71/1.03    inference(ennf_transformation,[],[f15])).
% 0.71/1.03  
% 0.71/1.03  fof(f24,plain,(
% 0.71/1.03    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.71/1.03    inference(flattening,[],[f23])).
% 0.71/1.03  
% 0.71/1.03  fof(f46,plain,(
% 0.71/1.03    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0)) => (! [X2] : (~r1_tarski(k2_relat_1(X2),sK6) | k1_relat_1(X2) != sK7 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK7 | k1_xboole_0 != sK6))),
% 0.71/1.03    introduced(choice_axiom,[])).
% 0.71/1.03  
% 0.71/1.03  fof(f47,plain,(
% 0.71/1.03    ! [X2] : (~r1_tarski(k2_relat_1(X2),sK6) | k1_relat_1(X2) != sK7 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK7 | k1_xboole_0 != sK6)),
% 0.71/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f24,f46])).
% 0.71/1.03  
% 0.71/1.03  fof(f81,plain,(
% 0.71/1.03    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK6) | k1_relat_1(X2) != sK7 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.71/1.03    inference(cnf_transformation,[],[f47])).
% 0.71/1.03  
% 0.71/1.03  fof(f76,plain,(
% 0.71/1.03    ( ! [X0,X1] : (v1_relat_1(sK5(X0,X1)) | k1_xboole_0 = X0) )),
% 0.71/1.03    inference(cnf_transformation,[],[f45])).
% 0.71/1.03  
% 0.71/1.03  fof(f77,plain,(
% 0.71/1.03    ( ! [X0,X1] : (v1_funct_1(sK5(X0,X1)) | k1_xboole_0 = X0) )),
% 0.71/1.03    inference(cnf_transformation,[],[f45])).
% 0.71/1.03  
% 0.71/1.03  fof(f50,plain,(
% 0.71/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 0.71/1.03    inference(cnf_transformation,[],[f28])).
% 0.71/1.03  
% 0.71/1.03  fof(f10,axiom,(
% 0.71/1.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.71/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.71/1.03  
% 0.71/1.03  fof(f69,plain,(
% 0.71/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.71/1.03    inference(cnf_transformation,[],[f10])).
% 0.71/1.03  
% 0.71/1.03  fof(f6,axiom,(
% 0.71/1.03    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.71/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.71/1.03  
% 0.71/1.03  fof(f61,plain,(
% 0.71/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.71/1.03    inference(cnf_transformation,[],[f6])).
% 0.71/1.03  
% 0.71/1.03  fof(f84,plain,(
% 0.71/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.71/1.03    inference(definition_unfolding,[],[f69,f61])).
% 0.71/1.03  
% 0.71/1.03  fof(f80,plain,(
% 0.71/1.03    k1_xboole_0 = sK7 | k1_xboole_0 != sK6),
% 0.71/1.03    inference(cnf_transformation,[],[f47])).
% 0.71/1.03  
% 0.71/1.03  fof(f66,plain,(
% 0.71/1.03    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.71/1.03    inference(cnf_transformation,[],[f40])).
% 0.71/1.03  
% 0.71/1.03  fof(f88,plain,(
% 0.71/1.03    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 0.71/1.03    inference(equality_resolution,[],[f66])).
% 0.71/1.03  
% 0.71/1.03  fof(f89,plain,(
% 0.71/1.03    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 0.71/1.03    inference(equality_resolution,[],[f88])).
% 0.71/1.03  
% 0.71/1.03  fof(f7,axiom,(
% 0.71/1.03    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.71/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.71/1.03  
% 0.71/1.03  fof(f62,plain,(
% 0.71/1.03    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.71/1.03    inference(cnf_transformation,[],[f7])).
% 0.71/1.03  
% 0.71/1.03  fof(f3,axiom,(
% 0.71/1.03    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.71/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.71/1.03  
% 0.71/1.03  fof(f18,plain,(
% 0.71/1.03    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.71/1.03    inference(ennf_transformation,[],[f3])).
% 0.71/1.03  
% 0.71/1.03  fof(f57,plain,(
% 0.71/1.03    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.71/1.03    inference(cnf_transformation,[],[f18])).
% 0.71/1.03  
% 0.71/1.03  fof(f8,axiom,(
% 0.71/1.03    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.71/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.71/1.03  
% 0.71/1.03  fof(f36,plain,(
% 0.71/1.03    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.71/1.03    inference(nnf_transformation,[],[f8])).
% 0.71/1.03  
% 0.71/1.03  fof(f63,plain,(
% 0.71/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.71/1.03    inference(cnf_transformation,[],[f36])).
% 0.71/1.03  
% 0.71/1.03  fof(f52,plain,(
% 0.71/1.03    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.71/1.03    inference(cnf_transformation,[],[f33])).
% 0.71/1.03  
% 0.71/1.03  fof(f86,plain,(
% 0.71/1.03    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 0.71/1.03    inference(equality_resolution,[],[f52])).
% 0.71/1.03  
% 0.71/1.03  fof(f48,plain,(
% 0.71/1.03    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.71/1.03    inference(cnf_transformation,[],[f28])).
% 0.71/1.03  
% 0.71/1.03  fof(f5,axiom,(
% 0.71/1.03    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.71/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.71/1.03  
% 0.71/1.03  fof(f60,plain,(
% 0.71/1.03    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.71/1.03    inference(cnf_transformation,[],[f5])).
% 0.71/1.03  
% 0.71/1.03  fof(f12,axiom,(
% 0.71/1.03    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.71/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.71/1.03  
% 0.71/1.03  fof(f21,plain,(
% 0.71/1.03    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.71/1.03    inference(ennf_transformation,[],[f12])).
% 0.71/1.03  
% 0.71/1.03  fof(f42,plain,(
% 0.71/1.03    ! [X0] : (? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_xboole_0 = k1_funct_1(sK4(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK4(X0)) = X0 & v1_funct_1(sK4(X0)) & v1_relat_1(sK4(X0))))),
% 0.71/1.03    introduced(choice_axiom,[])).
% 0.71/1.03  
% 0.71/1.03  fof(f43,plain,(
% 0.71/1.03    ! [X0] : (! [X2] : (k1_xboole_0 = k1_funct_1(sK4(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK4(X0)) = X0 & v1_funct_1(sK4(X0)) & v1_relat_1(sK4(X0)))),
% 0.71/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f42])).
% 0.71/1.03  
% 0.71/1.03  fof(f74,plain,(
% 0.71/1.03    ( ! [X0] : (k1_relat_1(sK4(X0)) = X0) )),
% 0.71/1.03    inference(cnf_transformation,[],[f43])).
% 0.71/1.03  
% 0.71/1.03  fof(f72,plain,(
% 0.71/1.03    ( ! [X0] : (v1_relat_1(sK4(X0))) )),
% 0.71/1.03    inference(cnf_transformation,[],[f43])).
% 0.71/1.03  
% 0.71/1.03  fof(f73,plain,(
% 0.71/1.03    ( ! [X0] : (v1_funct_1(sK4(X0))) )),
% 0.71/1.03    inference(cnf_transformation,[],[f43])).
% 0.71/1.03  
% 0.71/1.03  fof(f11,axiom,(
% 0.71/1.03    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.71/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.71/1.03  
% 0.71/1.03  fof(f20,plain,(
% 0.71/1.03    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.71/1.03    inference(ennf_transformation,[],[f11])).
% 0.71/1.03  
% 0.71/1.03  fof(f41,plain,(
% 0.71/1.03    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.71/1.03    inference(nnf_transformation,[],[f20])).
% 0.71/1.03  
% 0.71/1.03  fof(f70,plain,(
% 0.71/1.03    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.71/1.03    inference(cnf_transformation,[],[f41])).
% 0.71/1.03  
% 0.71/1.03  cnf(c_5,plain,
% 0.71/1.03      ( r2_hidden(sK1(X0,X1,X2),X0)
% 0.71/1.03      | r2_hidden(sK1(X0,X1,X2),X2)
% 0.71/1.03      | k4_xboole_0(X0,X1) = X2 ),
% 0.71/1.03      inference(cnf_transformation,[],[f54]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_1316,plain,
% 0.71/1.03      ( k4_xboole_0(X0,X1) = X2
% 0.71/1.03      | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
% 0.71/1.03      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 0.71/1.03      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_1,plain,
% 0.71/1.03      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 0.71/1.03      inference(cnf_transformation,[],[f49]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_1320,plain,
% 0.71/1.03      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 0.71/1.03      | r1_tarski(X0,X1) = iProver_top ),
% 0.71/1.03      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_19,plain,
% 0.71/1.03      ( ~ r2_hidden(X0,k1_tarski(X1)) | X0 = X1 ),
% 0.71/1.03      inference(cnf_transformation,[],[f90]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_1302,plain,
% 0.71/1.03      ( X0 = X1 | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
% 0.71/1.03      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_2659,plain,
% 0.71/1.03      ( sK0(k1_tarski(X0),X1) = X0
% 0.71/1.03      | r1_tarski(k1_tarski(X0),X1) = iProver_top ),
% 0.71/1.03      inference(superposition,[status(thm)],[c_1320,c_1302]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_27,plain,
% 0.71/1.03      ( k2_relat_1(sK5(X0,X1)) = k1_tarski(X1) | k1_xboole_0 = X0 ),
% 0.71/1.03      inference(cnf_transformation,[],[f79]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_28,plain,
% 0.71/1.03      ( k1_relat_1(sK5(X0,X1)) = X0 | k1_xboole_0 = X0 ),
% 0.71/1.03      inference(cnf_transformation,[],[f78]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_31,negated_conjecture,
% 0.71/1.03      ( ~ r1_tarski(k2_relat_1(X0),sK6)
% 0.71/1.03      | ~ v1_funct_1(X0)
% 0.71/1.03      | ~ v1_relat_1(X0)
% 0.71/1.03      | k1_relat_1(X0) != sK7 ),
% 0.71/1.03      inference(cnf_transformation,[],[f81]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_1294,plain,
% 0.71/1.03      ( k1_relat_1(X0) != sK7
% 0.71/1.03      | r1_tarski(k2_relat_1(X0),sK6) != iProver_top
% 0.71/1.03      | v1_funct_1(X0) != iProver_top
% 0.71/1.03      | v1_relat_1(X0) != iProver_top ),
% 0.71/1.03      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_1780,plain,
% 0.71/1.03      ( sK7 != X0
% 0.71/1.03      | k1_xboole_0 = X0
% 0.71/1.03      | r1_tarski(k2_relat_1(sK5(X0,X1)),sK6) != iProver_top
% 0.71/1.03      | v1_funct_1(sK5(X0,X1)) != iProver_top
% 0.71/1.03      | v1_relat_1(sK5(X0,X1)) != iProver_top ),
% 0.71/1.03      inference(superposition,[status(thm)],[c_28,c_1294]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_30,plain,
% 0.71/1.03      ( v1_relat_1(sK5(X0,X1)) | k1_xboole_0 = X0 ),
% 0.71/1.03      inference(cnf_transformation,[],[f76]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_36,plain,
% 0.71/1.03      ( k1_xboole_0 = X0 | v1_relat_1(sK5(X0,X1)) = iProver_top ),
% 0.71/1.03      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_29,plain,
% 0.71/1.03      ( v1_funct_1(sK5(X0,X1)) | k1_xboole_0 = X0 ),
% 0.71/1.03      inference(cnf_transformation,[],[f77]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_39,plain,
% 0.71/1.03      ( k1_xboole_0 = X0 | v1_funct_1(sK5(X0,X1)) = iProver_top ),
% 0.71/1.03      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_1913,plain,
% 0.71/1.03      ( sK7 != X0
% 0.71/1.03      | k1_xboole_0 = X0
% 0.71/1.03      | r1_tarski(k2_relat_1(sK5(X0,X1)),sK6) != iProver_top ),
% 0.71/1.03      inference(global_propositional_subsumption,
% 0.71/1.03                [status(thm)],
% 0.71/1.03                [c_1780,c_36,c_39]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_1920,plain,
% 0.71/1.03      ( sK7 = k1_xboole_0
% 0.71/1.03      | r1_tarski(k2_relat_1(sK5(sK7,X0)),sK6) != iProver_top ),
% 0.71/1.03      inference(equality_resolution,[status(thm)],[c_1913]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_1964,plain,
% 0.71/1.03      ( sK7 = k1_xboole_0 | r1_tarski(k1_tarski(X0),sK6) != iProver_top ),
% 0.71/1.03      inference(superposition,[status(thm)],[c_27,c_1920]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_6303,plain,
% 0.71/1.03      ( sK0(k1_tarski(X0),sK6) = X0 | sK7 = k1_xboole_0 ),
% 0.71/1.03      inference(superposition,[status(thm)],[c_2659,c_1964]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_0,plain,
% 0.71/1.03      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 0.71/1.03      inference(cnf_transformation,[],[f50]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_1321,plain,
% 0.71/1.03      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 0.71/1.03      | r1_tarski(X0,X1) = iProver_top ),
% 0.71/1.03      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_7524,plain,
% 0.71/1.03      ( sK7 = k1_xboole_0
% 0.71/1.03      | r2_hidden(X0,sK6) != iProver_top
% 0.71/1.03      | r1_tarski(k1_tarski(X0),sK6) = iProver_top ),
% 0.71/1.03      inference(superposition,[status(thm)],[c_6303,c_1321]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_7734,plain,
% 0.71/1.03      ( r2_hidden(X0,sK6) != iProver_top | sK7 = k1_xboole_0 ),
% 0.71/1.03      inference(global_propositional_subsumption,
% 0.71/1.03                [status(thm)],
% 0.71/1.03                [c_7524,c_1964]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_7735,plain,
% 0.71/1.03      ( sK7 = k1_xboole_0 | r2_hidden(X0,sK6) != iProver_top ),
% 0.71/1.03      inference(renaming,[status(thm)],[c_7734]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_7743,plain,
% 0.71/1.03      ( k4_xboole_0(sK6,X0) = X1
% 0.71/1.03      | sK7 = k1_xboole_0
% 0.71/1.03      | r2_hidden(sK1(sK6,X0,X1),X1) = iProver_top ),
% 0.71/1.03      inference(superposition,[status(thm)],[c_1316,c_7735]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_8282,plain,
% 0.71/1.03      ( k4_xboole_0(sK6,X0) = sK6 | sK7 = k1_xboole_0 ),
% 0.71/1.03      inference(superposition,[status(thm)],[c_7743,c_7735]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_20,plain,
% 0.71/1.03      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 0.71/1.03      inference(cnf_transformation,[],[f84]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_8390,plain,
% 0.71/1.03      ( k1_setfam_1(k2_tarski(sK6,X0)) = sK6 | sK7 = k1_xboole_0 ),
% 0.71/1.03      inference(superposition,[status(thm)],[c_8282,c_20]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_32,negated_conjecture,
% 0.71/1.03      ( k1_xboole_0 = sK7 | k1_xboole_0 != sK6 ),
% 0.71/1.03      inference(cnf_transformation,[],[f80]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_62,plain,
% 0.71/1.03      ( ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
% 0.71/1.03      | k1_xboole_0 = k1_xboole_0 ),
% 0.71/1.03      inference(instantiation,[status(thm)],[c_19]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_18,plain,
% 0.71/1.03      ( r2_hidden(X0,k1_tarski(X0)) ),
% 0.71/1.03      inference(cnf_transformation,[],[f89]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_65,plain,
% 0.71/1.03      ( r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
% 0.71/1.03      inference(instantiation,[status(thm)],[c_18]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_631,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_1598,plain,
% 0.71/1.03      ( sK6 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK6 ),
% 0.71/1.03      inference(instantiation,[status(thm)],[c_631]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_1599,plain,
% 0.71/1.03      ( sK6 != k1_xboole_0
% 0.71/1.03      | k1_xboole_0 = sK6
% 0.71/1.03      | k1_xboole_0 != k1_xboole_0 ),
% 0.71/1.03      inference(instantiation,[status(thm)],[c_1598]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_2269,plain,
% 0.71/1.03      ( ~ r2_hidden(sK7,k1_tarski(X0)) | sK7 = X0 ),
% 0.71/1.03      inference(instantiation,[status(thm)],[c_19]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_2406,plain,
% 0.71/1.03      ( ~ r2_hidden(sK7,k1_tarski(sK7)) | sK7 = sK7 ),
% 0.71/1.03      inference(instantiation,[status(thm)],[c_2269]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_2407,plain,
% 0.71/1.03      ( r2_hidden(sK7,k1_tarski(sK7)) ),
% 0.71/1.03      inference(instantiation,[status(thm)],[c_18]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_2268,plain,
% 0.71/1.03      ( X0 != X1 | sK7 != X1 | sK7 = X0 ),
% 0.71/1.03      inference(instantiation,[status(thm)],[c_631]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_2636,plain,
% 0.71/1.03      ( X0 != sK7 | sK7 = X0 | sK7 != sK7 ),
% 0.71/1.03      inference(instantiation,[status(thm)],[c_2268]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_2638,plain,
% 0.71/1.03      ( sK7 != sK7 | sK7 = k1_xboole_0 | k1_xboole_0 != sK7 ),
% 0.71/1.03      inference(instantiation,[status(thm)],[c_2636]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_7744,plain,
% 0.71/1.03      ( k4_xboole_0(X0,X1) = sK6
% 0.71/1.03      | sK7 = k1_xboole_0
% 0.71/1.03      | r2_hidden(sK1(X0,X1,sK6),X0) = iProver_top ),
% 0.71/1.03      inference(superposition,[status(thm)],[c_1316,c_7735]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_13,plain,
% 0.71/1.03      ( r1_xboole_0(X0,k1_xboole_0) ),
% 0.71/1.03      inference(cnf_transformation,[],[f62]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_1308,plain,
% 0.71/1.03      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 0.71/1.03      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_9,plain,
% 0.71/1.03      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 0.71/1.03      inference(cnf_transformation,[],[f57]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_1312,plain,
% 0.71/1.03      ( r1_xboole_0(X0,X1) != iProver_top
% 0.71/1.03      | r1_xboole_0(X1,X0) = iProver_top ),
% 0.71/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_2300,plain,
% 0.71/1.03      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 0.71/1.03      inference(superposition,[status(thm)],[c_1308,c_1312]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_15,plain,
% 0.71/1.03      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 0.71/1.03      inference(cnf_transformation,[],[f63]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_1306,plain,
% 0.71/1.03      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 0.71/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_2305,plain,
% 0.71/1.03      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 0.71/1.03      inference(superposition,[status(thm)],[c_2300,c_1306]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_7,plain,
% 0.71/1.03      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 0.71/1.03      inference(cnf_transformation,[],[f86]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_1314,plain,
% 0.71/1.03      ( r2_hidden(X0,X1) != iProver_top
% 0.71/1.03      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 0.71/1.03      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_2783,plain,
% 0.71/1.03      ( r2_hidden(X0,X1) != iProver_top
% 0.71/1.03      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 0.71/1.03      inference(superposition,[status(thm)],[c_2305,c_1314]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_2,plain,
% 0.71/1.03      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 0.71/1.03      inference(cnf_transformation,[],[f48]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_12,plain,
% 0.71/1.03      ( r1_tarski(k1_xboole_0,X0) ),
% 0.71/1.03      inference(cnf_transformation,[],[f60]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_581,plain,
% 0.71/1.03      ( ~ r2_hidden(X0,X1)
% 0.71/1.03      | r2_hidden(X0,X2)
% 0.71/1.03      | X3 != X2
% 0.71/1.03      | k1_xboole_0 != X1 ),
% 0.71/1.03      inference(resolution_lifted,[status(thm)],[c_2,c_12]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_582,plain,
% 0.71/1.03      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k1_xboole_0) ),
% 0.71/1.03      inference(unflattening,[status(thm)],[c_581]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_583,plain,
% 0.71/1.03      ( r2_hidden(X0,X1) = iProver_top
% 0.71/1.03      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 0.71/1.03      inference(predicate_to_equality,[status(thm)],[c_582]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_2917,plain,
% 0.71/1.03      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 0.71/1.03      inference(global_propositional_subsumption,
% 0.71/1.03                [status(thm)],
% 0.71/1.03                [c_2783,c_583]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_8722,plain,
% 0.71/1.03      ( k4_xboole_0(k1_xboole_0,X0) = sK6 | sK7 = k1_xboole_0 ),
% 0.71/1.03      inference(superposition,[status(thm)],[c_7744,c_2917]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_8757,plain,
% 0.71/1.03      ( sK7 = k1_xboole_0 | sK6 = k1_xboole_0 ),
% 0.71/1.03      inference(light_normalisation,[status(thm)],[c_8722,c_2305]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_8956,plain,
% 0.71/1.03      ( sK7 = k1_xboole_0 ),
% 0.71/1.03      inference(global_propositional_subsumption,
% 0.71/1.03                [status(thm)],
% 0.71/1.03                [c_8390,c_32,c_62,c_65,c_1599,c_2406,c_2407,c_2638,
% 0.71/1.03                 c_8757]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_24,plain,
% 0.71/1.03      ( k1_relat_1(sK4(X0)) = X0 ),
% 0.71/1.03      inference(cnf_transformation,[],[f74]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_1568,plain,
% 0.71/1.03      ( sK7 != X0
% 0.71/1.03      | r1_tarski(k2_relat_1(sK4(X0)),sK6) != iProver_top
% 0.71/1.03      | v1_funct_1(sK4(X0)) != iProver_top
% 0.71/1.03      | v1_relat_1(sK4(X0)) != iProver_top ),
% 0.71/1.03      inference(superposition,[status(thm)],[c_24,c_1294]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_26,plain,
% 0.71/1.03      ( v1_relat_1(sK4(X0)) ),
% 0.71/1.03      inference(cnf_transformation,[],[f72]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_44,plain,
% 0.71/1.03      ( v1_relat_1(sK4(X0)) = iProver_top ),
% 0.71/1.03      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_25,plain,
% 0.71/1.03      ( v1_funct_1(sK4(X0)) ),
% 0.71/1.03      inference(cnf_transformation,[],[f73]) ).
% 0.71/1.03  
% 0.71/1.03  cnf(c_47,plain,
% 0.71/1.03      ( v1_funct_1(sK4(X0)) = iProver_top ),
% 0.71/1.03      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 0.71/1.04  
% 0.71/1.04  cnf(c_1573,plain,
% 0.71/1.04      ( sK7 != X0 | r1_tarski(k2_relat_1(sK4(X0)),sK6) != iProver_top ),
% 0.71/1.04      inference(global_propositional_subsumption,
% 0.71/1.04                [status(thm)],
% 0.71/1.04                [c_1568,c_44,c_47]) ).
% 0.71/1.04  
% 0.71/1.04  cnf(c_1581,plain,
% 0.71/1.04      ( r1_tarski(k2_relat_1(sK4(sK7)),sK6) != iProver_top ),
% 0.71/1.04      inference(equality_resolution,[status(thm)],[c_1573]) ).
% 0.71/1.04  
% 0.71/1.04  cnf(c_8962,plain,
% 0.71/1.04      ( r1_tarski(k2_relat_1(sK4(k1_xboole_0)),sK6) != iProver_top ),
% 0.71/1.04      inference(demodulation,[status(thm)],[c_8956,c_1581]) ).
% 0.71/1.04  
% 0.71/1.04  cnf(c_22,plain,
% 0.71/1.04      ( ~ v1_relat_1(X0)
% 0.71/1.04      | k2_relat_1(X0) = k1_xboole_0
% 0.71/1.04      | k1_relat_1(X0) != k1_xboole_0 ),
% 0.71/1.04      inference(cnf_transformation,[],[f70]) ).
% 0.71/1.04  
% 0.71/1.04  cnf(c_1300,plain,
% 0.71/1.04      ( k2_relat_1(X0) = k1_xboole_0
% 0.71/1.04      | k1_relat_1(X0) != k1_xboole_0
% 0.71/1.04      | v1_relat_1(X0) != iProver_top ),
% 0.71/1.04      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 0.71/1.04  
% 0.71/1.04  cnf(c_2560,plain,
% 0.71/1.04      ( k2_relat_1(sK4(X0)) = k1_xboole_0
% 0.71/1.04      | k1_xboole_0 != X0
% 0.71/1.04      | v1_relat_1(sK4(X0)) != iProver_top ),
% 0.71/1.04      inference(superposition,[status(thm)],[c_24,c_1300]) ).
% 0.71/1.04  
% 0.71/1.04  cnf(c_3768,plain,
% 0.71/1.04      ( k1_xboole_0 != X0 | k2_relat_1(sK4(X0)) = k1_xboole_0 ),
% 0.71/1.04      inference(global_propositional_subsumption,
% 0.71/1.04                [status(thm)],
% 0.71/1.04                [c_2560,c_44]) ).
% 0.71/1.04  
% 0.71/1.04  cnf(c_3769,plain,
% 0.71/1.04      ( k2_relat_1(sK4(X0)) = k1_xboole_0 | k1_xboole_0 != X0 ),
% 0.71/1.04      inference(renaming,[status(thm)],[c_3768]) ).
% 0.71/1.04  
% 0.71/1.04  cnf(c_3773,plain,
% 0.71/1.04      ( k2_relat_1(sK4(k1_xboole_0)) = k1_xboole_0 ),
% 0.71/1.04      inference(equality_resolution,[status(thm)],[c_3769]) ).
% 0.71/1.04  
% 0.71/1.04  cnf(c_8979,plain,
% 0.71/1.04      ( r1_tarski(k1_xboole_0,sK6) != iProver_top ),
% 0.71/1.04      inference(light_normalisation,[status(thm)],[c_8962,c_3773]) ).
% 0.71/1.04  
% 0.71/1.04  cnf(c_7819,plain,
% 0.71/1.04      ( r1_tarski(k1_xboole_0,sK6) ),
% 0.71/1.04      inference(instantiation,[status(thm)],[c_12]) ).
% 0.71/1.04  
% 0.71/1.04  cnf(c_7822,plain,
% 0.71/1.04      ( r1_tarski(k1_xboole_0,sK6) = iProver_top ),
% 0.71/1.04      inference(predicate_to_equality,[status(thm)],[c_7819]) ).
% 0.71/1.04  
% 0.71/1.04  cnf(contradiction,plain,
% 0.71/1.04      ( $false ),
% 0.71/1.04      inference(minisat,[status(thm)],[c_8979,c_7822]) ).
% 0.71/1.04  
% 0.71/1.04  
% 0.71/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 0.71/1.04  
% 0.71/1.04  ------                               Statistics
% 0.71/1.04  
% 0.71/1.04  ------ General
% 0.71/1.04  
% 0.71/1.04  abstr_ref_over_cycles:                  0
% 0.71/1.04  abstr_ref_under_cycles:                 0
% 0.71/1.04  gc_basic_clause_elim:                   0
% 0.71/1.04  forced_gc_time:                         0
% 0.71/1.04  parsing_time:                           0.01
% 0.71/1.04  unif_index_cands_time:                  0.
% 0.71/1.04  unif_index_add_time:                    0.
% 0.71/1.04  orderings_time:                         0.
% 0.71/1.04  out_proof_time:                         0.016
% 0.71/1.04  total_time:                             0.34
% 0.71/1.04  num_of_symbols:                         52
% 0.71/1.04  num_of_terms:                           9674
% 0.71/1.04  
% 0.71/1.04  ------ Preprocessing
% 0.71/1.04  
% 0.71/1.04  num_of_splits:                          0
% 0.71/1.04  num_of_split_atoms:                     0
% 0.71/1.04  num_of_reused_defs:                     0
% 0.71/1.04  num_eq_ax_congr_red:                    36
% 0.71/1.04  num_of_sem_filtered_clauses:            1
% 0.71/1.04  num_of_subtypes:                        0
% 0.71/1.04  monotx_restored_types:                  0
% 0.71/1.04  sat_num_of_epr_types:                   0
% 0.71/1.04  sat_num_of_non_cyclic_types:            0
% 0.71/1.04  sat_guarded_non_collapsed_types:        0
% 0.71/1.04  num_pure_diseq_elim:                    0
% 0.71/1.04  simp_replaced_by:                       0
% 0.71/1.04  res_preprocessed:                       124
% 0.71/1.04  prep_upred:                             0
% 0.71/1.04  prep_unflattend:                        19
% 0.71/1.04  smt_new_axioms:                         0
% 0.71/1.04  pred_elim_cands:                        5
% 0.71/1.04  pred_elim:                              0
% 0.71/1.04  pred_elim_cl:                           0
% 0.71/1.04  pred_elim_cycles:                       3
% 0.71/1.04  merged_defs:                            6
% 0.71/1.04  merged_defs_ncl:                        0
% 0.71/1.04  bin_hyper_res:                          6
% 0.71/1.04  prep_cycles:                            3
% 0.71/1.04  pred_elim_time:                         0.004
% 0.71/1.04  splitting_time:                         0.
% 0.71/1.04  sem_filter_time:                        0.
% 0.71/1.04  monotx_time:                            0.001
% 0.71/1.04  subtype_inf_time:                       0.
% 0.71/1.04  
% 0.71/1.04  ------ Problem properties
% 0.71/1.04  
% 0.71/1.04  clauses:                                33
% 0.71/1.04  conjectures:                            2
% 0.71/1.04  epr:                                    5
% 0.71/1.04  horn:                                   22
% 0.71/1.04  ground:                                 1
% 0.71/1.04  unary:                                  7
% 0.71/1.04  binary:                                 16
% 0.71/1.04  lits:                                   71
% 0.71/1.04  lits_eq:                                26
% 0.71/1.04  fd_pure:                                0
% 0.71/1.04  fd_pseudo:                              0
% 0.71/1.04  fd_cond:                                3
% 0.71/1.04  fd_pseudo_cond:                         5
% 0.71/1.04  ac_symbols:                             0
% 0.71/1.04  
% 0.71/1.04  ------ Propositional Solver
% 0.71/1.04  
% 0.71/1.04  prop_solver_calls:                      25
% 0.71/1.04  prop_fast_solver_calls:                 782
% 0.71/1.04  smt_solver_calls:                       0
% 0.71/1.04  smt_fast_solver_calls:                  0
% 0.71/1.04  prop_num_of_clauses:                    3652
% 0.71/1.04  prop_preprocess_simplified:             9139
% 0.71/1.04  prop_fo_subsumed:                       15
% 0.71/1.04  prop_solver_time:                       0.
% 0.71/1.04  smt_solver_time:                        0.
% 0.71/1.04  smt_fast_solver_time:                   0.
% 0.71/1.04  prop_fast_solver_time:                  0.
% 0.71/1.04  prop_unsat_core_time:                   0.
% 0.71/1.04  
% 0.71/1.04  ------ QBF
% 0.71/1.04  
% 0.71/1.04  qbf_q_res:                              0
% 0.71/1.04  qbf_num_tautologies:                    0
% 0.71/1.04  qbf_prep_cycles:                        0
% 0.71/1.04  
% 0.71/1.04  ------ BMC1
% 0.71/1.04  
% 0.71/1.04  bmc1_current_bound:                     -1
% 0.71/1.04  bmc1_last_solved_bound:                 -1
% 0.71/1.04  bmc1_unsat_core_size:                   -1
% 0.71/1.04  bmc1_unsat_core_parents_size:           -1
% 0.71/1.04  bmc1_merge_next_fun:                    0
% 0.71/1.04  bmc1_unsat_core_clauses_time:           0.
% 0.71/1.04  
% 0.71/1.04  ------ Instantiation
% 0.71/1.04  
% 0.71/1.04  inst_num_of_clauses:                    956
% 0.71/1.04  inst_num_in_passive:                    437
% 0.71/1.04  inst_num_in_active:                     333
% 0.71/1.04  inst_num_in_unprocessed:                186
% 0.71/1.04  inst_num_of_loops:                      430
% 0.71/1.04  inst_num_of_learning_restarts:          0
% 0.71/1.04  inst_num_moves_active_passive:          94
% 0.71/1.04  inst_lit_activity:                      0
% 0.71/1.04  inst_lit_activity_moves:                0
% 0.71/1.04  inst_num_tautologies:                   0
% 0.71/1.04  inst_num_prop_implied:                  0
% 0.71/1.04  inst_num_existing_simplified:           0
% 0.71/1.04  inst_num_eq_res_simplified:             0
% 0.71/1.04  inst_num_child_elim:                    0
% 0.71/1.04  inst_num_of_dismatching_blockings:      401
% 0.71/1.04  inst_num_of_non_proper_insts:           689
% 0.71/1.04  inst_num_of_duplicates:                 0
% 0.71/1.04  inst_inst_num_from_inst_to_res:         0
% 0.71/1.04  inst_dismatching_checking_time:         0.
% 0.71/1.04  
% 0.71/1.04  ------ Resolution
% 0.71/1.04  
% 0.71/1.04  res_num_of_clauses:                     0
% 0.71/1.04  res_num_in_passive:                     0
% 0.71/1.04  res_num_in_active:                      0
% 0.71/1.04  res_num_of_loops:                       127
% 0.71/1.04  res_forward_subset_subsumed:            30
% 0.71/1.04  res_backward_subset_subsumed:           0
% 0.71/1.04  res_forward_subsumed:                   0
% 0.71/1.04  res_backward_subsumed:                  0
% 0.71/1.04  res_forward_subsumption_resolution:     0
% 0.71/1.04  res_backward_subsumption_resolution:    0
% 0.71/1.04  res_clause_to_clause_subsumption:       811
% 0.71/1.04  res_orphan_elimination:                 0
% 0.71/1.04  res_tautology_del:                      38
% 0.71/1.04  res_num_eq_res_simplified:              0
% 0.71/1.04  res_num_sel_changes:                    0
% 0.71/1.04  res_moves_from_active_to_pass:          0
% 0.71/1.04  
% 0.71/1.04  ------ Superposition
% 0.71/1.04  
% 0.71/1.04  sup_time_total:                         0.
% 0.71/1.04  sup_time_generating:                    0.
% 0.71/1.04  sup_time_sim_full:                      0.
% 0.71/1.04  sup_time_sim_immed:                     0.
% 0.71/1.04  
% 0.71/1.04  sup_num_of_clauses:                     217
% 0.71/1.04  sup_num_in_active:                      72
% 0.71/1.04  sup_num_in_passive:                     145
% 0.71/1.04  sup_num_of_loops:                       84
% 0.71/1.04  sup_fw_superposition:                   242
% 0.71/1.04  sup_bw_superposition:                   172
% 0.71/1.04  sup_immediate_simplified:               149
% 0.71/1.04  sup_given_eliminated:                   0
% 0.71/1.04  comparisons_done:                       0
% 0.71/1.04  comparisons_avoided:                    20
% 0.71/1.04  
% 0.71/1.04  ------ Simplifications
% 0.71/1.04  
% 0.71/1.04  
% 0.71/1.04  sim_fw_subset_subsumed:                 10
% 0.71/1.04  sim_bw_subset_subsumed:                 8
% 0.71/1.04  sim_fw_subsumed:                        35
% 0.71/1.04  sim_bw_subsumed:                        30
% 0.71/1.04  sim_fw_subsumption_res:                 0
% 0.71/1.04  sim_bw_subsumption_res:                 0
% 0.71/1.04  sim_tautology_del:                      19
% 0.71/1.04  sim_eq_tautology_del:                   20
% 0.71/1.04  sim_eq_res_simp:                        2
% 0.71/1.04  sim_fw_demodulated:                     40
% 0.71/1.04  sim_bw_demodulated:                     7
% 0.71/1.04  sim_light_normalised:                   50
% 0.71/1.04  sim_joinable_taut:                      0
% 0.71/1.04  sim_joinable_simp:                      0
% 0.71/1.04  sim_ac_normalised:                      0
% 0.71/1.04  sim_smt_subsumption:                    0
% 0.71/1.04  
%------------------------------------------------------------------------------
