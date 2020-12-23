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
% DateTime   : Thu Dec  3 11:49:33 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :  167 (9326 expanded)
%              Number of clauses        :  106 (3186 expanded)
%              Number of leaves         :   18 (2055 expanded)
%              Depth                    :   34
%              Number of atoms          :  483 (40183 expanded)
%              Number of equality atoms :  306 (21084 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f66,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f6,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK2(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK2(X0,X1)) = X0
        & v1_funct_1(sK2(X0,X1))
        & v1_relat_1(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK2(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK2(X0,X1)) = X0
      & v1_funct_1(sK2(X0,X1))
      & v1_relat_1(sK2(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f29])).

fof(f53,plain,(
    ! [X0,X1] : k1_relat_1(sK2(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f51,plain,(
    ! [X0,X1] : v1_relat_1(sK2(X0,X1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK2(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f69,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( k1_tarski(X1) = k2_relat_1(sK4(X0,X1))
        & k1_relat_1(sK4(X0,X1)) = X0
        & v1_funct_1(sK4(X0,X1))
        & v1_relat_1(sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tarski(X1) = k2_relat_1(sK4(X0,X1))
          & k1_relat_1(sK4(X0,X1)) = X0
          & v1_funct_1(sK4(X0,X1))
          & v1_relat_1(sK4(X0,X1)) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f33])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK4(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK4(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f35,plain,
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

fof(f36,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK5)
        | k1_relat_1(X2) != sK6
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK6
      | k1_xboole_0 != sK5 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f18,f35])).

fof(f64,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK5)
      | k1_relat_1(X2) != sK6
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK4(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK4(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f63,plain,
    ( k1_xboole_0 = sK6
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f36])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f67,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f44])).

fof(f68,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f67])).

fof(f7,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK3(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK3(X0)) = X0
        & v1_funct_1(sK3(X0))
        & v1_relat_1(sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK3(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK3(X0)) = X0
      & v1_funct_1(sK3(X0))
      & v1_relat_1(sK3(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f31])).

fof(f57,plain,(
    ! [X0] : k1_relat_1(sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    ! [X0] : v1_relat_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f56,plain,(
    ! [X0] : v1_funct_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X0,X1] : v1_funct_1(sK2(X0,X1)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1128,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_15,plain,
    ( k1_relat_1(sK2(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1122,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2498,plain,
    ( sK2(X0,X1) = k1_xboole_0
    | k1_xboole_0 != X0
    | v1_relat_1(sK2(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_1122])).

cnf(c_17,plain,
    ( v1_relat_1(sK2(X0,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_49,plain,
    ( v1_relat_1(sK2(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3110,plain,
    ( k1_xboole_0 != X0
    | sK2(X0,X1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2498,c_49])).

cnf(c_3111,plain,
    ( sK2(X0,X1) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(renaming,[status(thm)],[c_3110])).

cnf(c_3115,plain,
    ( sK2(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_3111])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1131,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(sK2(X1,X2),X0) = X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1121,plain,
    ( k1_funct_1(sK2(X0,X1),X2) = X1
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2832,plain,
    ( k1_funct_1(sK2(X0,X1),sK0(X0,X2)) = X1
    | r1_tarski(X0,X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1131,c_1121])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1124,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2833,plain,
    ( sK0(k1_tarski(X0),X1) = X0
    | r1_tarski(k1_tarski(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1131,c_1124])).

cnf(c_22,plain,
    ( k2_relat_1(sK4(X0,X1)) = k1_tarski(X1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_23,plain,
    ( k1_relat_1(sK4(X0,X1)) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_26,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(X0),sK5)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) != sK6 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1113,plain,
    ( k1_relat_1(X0) != sK6
    | r1_tarski(k2_relat_1(X0),sK5) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1541,plain,
    ( sK6 != X0
    | k1_xboole_0 = X0
    | r1_tarski(k2_relat_1(sK4(X0,X1)),sK5) != iProver_top
    | v1_funct_1(sK4(X0,X1)) != iProver_top
    | v1_relat_1(sK4(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_1113])).

cnf(c_25,plain,
    ( v1_relat_1(sK4(X0,X1))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_31,plain,
    ( k1_xboole_0 = X0
    | v1_relat_1(sK4(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,plain,
    ( v1_funct_1(sK4(X0,X1))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_34,plain,
    ( k1_xboole_0 = X0
    | v1_funct_1(sK4(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1618,plain,
    ( sK6 != X0
    | k1_xboole_0 = X0
    | r1_tarski(k2_relat_1(sK4(X0,X1)),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1541,c_31,c_34])).

cnf(c_1625,plain,
    ( sK6 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK4(sK6,X0)),sK5) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1618])).

cnf(c_1647,plain,
    ( sK6 = k1_xboole_0
    | r1_tarski(k1_tarski(X0),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_1625])).

cnf(c_3678,plain,
    ( sK0(k1_tarski(X0),sK5) = X0
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2833,c_1647])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1132,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3703,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(X0,sK5) != iProver_top
    | r1_tarski(k1_tarski(X0),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3678,c_1132])).

cnf(c_4131,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3703,c_1647])).

cnf(c_4132,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_4131])).

cnf(c_4139,plain,
    ( sK6 = k1_xboole_0
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1131,c_4132])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1129,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4214,plain,
    ( sK6 = k1_xboole_0
    | sK5 = X0
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4139,c_1129])).

cnf(c_4289,plain,
    ( k1_funct_1(sK2(X0,X1),sK0(X0,sK5)) = X1
    | sK6 = k1_xboole_0
    | sK5 = X0 ),
    inference(superposition,[status(thm)],[c_2832,c_4214])).

cnf(c_4702,plain,
    ( k1_funct_1(k1_xboole_0,sK0(k1_xboole_0,sK5)) = X0
    | sK6 = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3115,c_4289])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 = sK6
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_66,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_69,plain,
    ( r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_750,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1372,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_750])).

cnf(c_1373,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1372])).

cnf(c_1757,plain,
    ( ~ r2_hidden(sK6,k1_tarski(X0))
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2156,plain,
    ( ~ r2_hidden(sK6,k1_tarski(sK6))
    | sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_1757])).

cnf(c_2157,plain,
    ( r2_hidden(sK6,k1_tarski(sK6)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1767,plain,
    ( X0 != X1
    | sK6 != X1
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_750])).

cnf(c_2356,plain,
    ( X0 != sK6
    | sK6 = X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1767])).

cnf(c_2358,plain,
    ( sK6 != sK6
    | sK6 = k1_xboole_0
    | k1_xboole_0 != sK6 ),
    inference(instantiation,[status(thm)],[c_2356])).

cnf(c_4782,plain,
    ( sK6 = k1_xboole_0
    | k1_funct_1(k1_xboole_0,sK0(k1_xboole_0,sK5)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4702,c_27,c_66,c_69,c_1373,c_2156,c_2157,c_2358])).

cnf(c_4783,plain,
    ( k1_funct_1(k1_xboole_0,sK0(k1_xboole_0,sK5)) = X0
    | sK6 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4782])).

cnf(c_4869,plain,
    ( X0 = X1
    | sK6 = k1_xboole_0
    | r2_hidden(X1,k1_funct_1(k1_xboole_0,sK0(k1_xboole_0,sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4783,c_1124])).

cnf(c_1125,plain,
    ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4882,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(X0,k1_funct_1(k1_xboole_0,sK0(k1_xboole_0,sK5))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4783,c_1125])).

cnf(c_4957,plain,
    ( X0 = X1
    | sK6 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4869,c_4882])).

cnf(c_5399,plain,
    ( sK6 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(equality_factoring,[status(thm)],[c_4957])).

cnf(c_5414,plain,
    ( sK6 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5399,c_4957])).

cnf(c_19,plain,
    ( k1_relat_1(sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1368,plain,
    ( sK6 != X0
    | r1_tarski(k2_relat_1(sK3(X0)),sK5) != iProver_top
    | v1_funct_1(sK3(X0)) != iProver_top
    | v1_relat_1(sK3(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_1113])).

cnf(c_21,plain,
    ( v1_relat_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_39,plain,
    ( v1_relat_1(sK3(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,plain,
    ( v1_funct_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_42,plain,
    ( v1_funct_1(sK3(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1380,plain,
    ( sK6 != X0
    | r1_tarski(k2_relat_1(sK3(X0)),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1368,c_39,c_42])).

cnf(c_1388,plain,
    ( r1_tarski(k2_relat_1(sK3(sK6)),sK5) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1380])).

cnf(c_3809,plain,
    ( k1_funct_1(sK2(k2_relat_1(sK3(sK6)),X0),sK0(k2_relat_1(sK3(sK6)),sK5)) = X0 ),
    inference(superposition,[status(thm)],[c_2832,c_1388])).

cnf(c_5423,plain,
    ( k1_funct_1(sK2(k2_relat_1(sK3(k1_xboole_0)),X0),sK0(k2_relat_1(sK3(k1_xboole_0)),sK5)) = X0 ),
    inference(demodulation,[status(thm)],[c_5414,c_3809])).

cnf(c_10,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2499,plain,
    ( sK3(X0) = k1_xboole_0
    | k1_xboole_0 != X0
    | v1_relat_1(sK3(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_1122])).

cnf(c_2683,plain,
    ( k1_xboole_0 != X0
    | sK3(X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2499,c_39])).

cnf(c_2684,plain,
    ( sK3(X0) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(renaming,[status(thm)],[c_2683])).

cnf(c_2688,plain,
    ( sK3(k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_2684])).

cnf(c_5460,plain,
    ( k1_funct_1(k1_xboole_0,sK0(k1_xboole_0,sK5)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_5423,c_10,c_2688,c_3115])).

cnf(c_5800,plain,
    ( k1_relat_1(k1_funct_1(k1_xboole_0,sK0(k1_xboole_0,sK5))) = X0 ),
    inference(superposition,[status(thm)],[c_5460,c_15])).

cnf(c_5431,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | r1_tarski(k2_relat_1(X0),sK5) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5414,c_1113])).

cnf(c_5801,plain,
    ( k1_funct_1(k1_xboole_0,sK0(k1_xboole_0,sK5)) != k1_xboole_0
    | r1_tarski(k2_relat_1(X0),sK5) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5460,c_5431])).

cnf(c_5506,plain,
    ( k1_funct_1(k1_xboole_0,sK0(k1_xboole_0,sK5)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5460])).

cnf(c_6433,plain,
    ( r1_tarski(k2_relat_1(X0),sK5) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5801,c_5506])).

cnf(c_7342,plain,
    ( r1_tarski(k1_relat_1(k1_funct_1(k1_xboole_0,sK0(k1_xboole_0,sK5))),sK5) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5800,c_6433])).

cnf(c_51,plain,
    ( v1_relat_1(sK2(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_49])).

cnf(c_16,plain,
    ( v1_funct_1(sK2(X0,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_52,plain,
    ( v1_funct_1(sK2(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_54,plain,
    ( v1_funct_1(sK2(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_52])).

cnf(c_55,plain,
    ( k1_relat_1(sK2(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_325,plain,
    ( sK2(X0,X1) != X2
    | k1_relat_1(X2) != k1_xboole_0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_17])).

cnf(c_326,plain,
    ( k1_relat_1(sK2(X0,X1)) != k1_xboole_0
    | k1_xboole_0 = sK2(X0,X1) ),
    inference(unflattening,[status(thm)],[c_325])).

cnf(c_327,plain,
    ( k1_relat_1(sK2(k1_xboole_0,k1_xboole_0)) != k1_xboole_0
    | k1_xboole_0 = sK2(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_326])).

cnf(c_755,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1322,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(sK2(X1,X2))
    | X0 != sK2(X1,X2) ),
    inference(instantiation,[status(thm)],[c_755])).

cnf(c_1323,plain,
    ( X0 != sK2(X1,X2)
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(sK2(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1322])).

cnf(c_1325,plain,
    ( k1_xboole_0 != sK2(k1_xboole_0,k1_xboole_0)
    | v1_relat_1(sK2(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1323])).

cnf(c_757,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1332,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK2(X1,X2))
    | X0 != sK2(X1,X2) ),
    inference(instantiation,[status(thm)],[c_757])).

cnf(c_1333,plain,
    ( X0 != sK2(X1,X2)
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK2(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1332])).

cnf(c_1335,plain,
    ( k1_xboole_0 != sK2(k1_xboole_0,k1_xboole_0)
    | v1_funct_1(sK2(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1333])).

cnf(c_7474,plain,
    ( r1_tarski(k1_relat_1(k1_funct_1(k1_xboole_0,sK0(k1_xboole_0,sK5))),sK5) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7342])).

cnf(c_8648,plain,
    ( r1_tarski(k1_relat_1(k1_funct_1(k1_xboole_0,sK0(k1_xboole_0,sK5))),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7342,c_51,c_54,c_55,c_327,c_1325,c_1335,c_7474])).

cnf(c_8654,plain,
    ( r1_tarski(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5800,c_8648])).

cnf(c_8841,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1128,c_8654])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:13:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.21/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.00  
% 3.21/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.21/1.00  
% 3.21/1.00  ------  iProver source info
% 3.21/1.00  
% 3.21/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.21/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.21/1.00  git: non_committed_changes: false
% 3.21/1.00  git: last_make_outside_of_git: false
% 3.21/1.00  
% 3.21/1.00  ------ 
% 3.21/1.00  
% 3.21/1.00  ------ Input Options
% 3.21/1.00  
% 3.21/1.00  --out_options                           all
% 3.21/1.00  --tptp_safe_out                         true
% 3.21/1.00  --problem_path                          ""
% 3.21/1.00  --include_path                          ""
% 3.21/1.00  --clausifier                            res/vclausify_rel
% 3.21/1.00  --clausifier_options                    --mode clausify
% 3.21/1.00  --stdin                                 false
% 3.21/1.00  --stats_out                             all
% 3.21/1.00  
% 3.21/1.00  ------ General Options
% 3.21/1.00  
% 3.21/1.00  --fof                                   false
% 3.21/1.00  --time_out_real                         305.
% 3.21/1.00  --time_out_virtual                      -1.
% 3.21/1.00  --symbol_type_check                     false
% 3.21/1.00  --clausify_out                          false
% 3.21/1.00  --sig_cnt_out                           false
% 3.21/1.00  --trig_cnt_out                          false
% 3.21/1.00  --trig_cnt_out_tolerance                1.
% 3.21/1.00  --trig_cnt_out_sk_spl                   false
% 3.21/1.00  --abstr_cl_out                          false
% 3.21/1.00  
% 3.21/1.00  ------ Global Options
% 3.21/1.00  
% 3.21/1.00  --schedule                              default
% 3.21/1.00  --add_important_lit                     false
% 3.21/1.00  --prop_solver_per_cl                    1000
% 3.21/1.00  --min_unsat_core                        false
% 3.21/1.00  --soft_assumptions                      false
% 3.21/1.00  --soft_lemma_size                       3
% 3.21/1.00  --prop_impl_unit_size                   0
% 3.21/1.00  --prop_impl_unit                        []
% 3.21/1.00  --share_sel_clauses                     true
% 3.21/1.00  --reset_solvers                         false
% 3.21/1.00  --bc_imp_inh                            [conj_cone]
% 3.21/1.00  --conj_cone_tolerance                   3.
% 3.21/1.00  --extra_neg_conj                        none
% 3.21/1.00  --large_theory_mode                     true
% 3.21/1.00  --prolific_symb_bound                   200
% 3.21/1.00  --lt_threshold                          2000
% 3.21/1.00  --clause_weak_htbl                      true
% 3.21/1.00  --gc_record_bc_elim                     false
% 3.21/1.00  
% 3.21/1.00  ------ Preprocessing Options
% 3.21/1.00  
% 3.21/1.00  --preprocessing_flag                    true
% 3.21/1.00  --time_out_prep_mult                    0.1
% 3.21/1.00  --splitting_mode                        input
% 3.21/1.00  --splitting_grd                         true
% 3.21/1.00  --splitting_cvd                         false
% 3.21/1.00  --splitting_cvd_svl                     false
% 3.21/1.00  --splitting_nvd                         32
% 3.21/1.00  --sub_typing                            true
% 3.21/1.00  --prep_gs_sim                           true
% 3.21/1.00  --prep_unflatten                        true
% 3.21/1.00  --prep_res_sim                          true
% 3.21/1.00  --prep_upred                            true
% 3.21/1.00  --prep_sem_filter                       exhaustive
% 3.21/1.00  --prep_sem_filter_out                   false
% 3.21/1.00  --pred_elim                             true
% 3.21/1.00  --res_sim_input                         true
% 3.21/1.00  --eq_ax_congr_red                       true
% 3.21/1.00  --pure_diseq_elim                       true
% 3.21/1.00  --brand_transform                       false
% 3.21/1.00  --non_eq_to_eq                          false
% 3.21/1.00  --prep_def_merge                        true
% 3.21/1.00  --prep_def_merge_prop_impl              false
% 3.21/1.00  --prep_def_merge_mbd                    true
% 3.21/1.00  --prep_def_merge_tr_red                 false
% 3.21/1.00  --prep_def_merge_tr_cl                  false
% 3.21/1.00  --smt_preprocessing                     true
% 3.21/1.00  --smt_ac_axioms                         fast
% 3.21/1.00  --preprocessed_out                      false
% 3.21/1.00  --preprocessed_stats                    false
% 3.21/1.00  
% 3.21/1.00  ------ Abstraction refinement Options
% 3.21/1.00  
% 3.21/1.00  --abstr_ref                             []
% 3.21/1.00  --abstr_ref_prep                        false
% 3.21/1.00  --abstr_ref_until_sat                   false
% 3.21/1.00  --abstr_ref_sig_restrict                funpre
% 3.21/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.21/1.00  --abstr_ref_under                       []
% 3.21/1.00  
% 3.21/1.00  ------ SAT Options
% 3.21/1.00  
% 3.21/1.00  --sat_mode                              false
% 3.21/1.00  --sat_fm_restart_options                ""
% 3.21/1.00  --sat_gr_def                            false
% 3.21/1.00  --sat_epr_types                         true
% 3.21/1.00  --sat_non_cyclic_types                  false
% 3.21/1.00  --sat_finite_models                     false
% 3.21/1.00  --sat_fm_lemmas                         false
% 3.21/1.00  --sat_fm_prep                           false
% 3.21/1.00  --sat_fm_uc_incr                        true
% 3.21/1.00  --sat_out_model                         small
% 3.21/1.00  --sat_out_clauses                       false
% 3.21/1.00  
% 3.21/1.00  ------ QBF Options
% 3.21/1.00  
% 3.21/1.00  --qbf_mode                              false
% 3.21/1.00  --qbf_elim_univ                         false
% 3.21/1.00  --qbf_dom_inst                          none
% 3.21/1.00  --qbf_dom_pre_inst                      false
% 3.21/1.00  --qbf_sk_in                             false
% 3.21/1.00  --qbf_pred_elim                         true
% 3.21/1.00  --qbf_split                             512
% 3.21/1.00  
% 3.21/1.00  ------ BMC1 Options
% 3.21/1.00  
% 3.21/1.00  --bmc1_incremental                      false
% 3.21/1.00  --bmc1_axioms                           reachable_all
% 3.21/1.00  --bmc1_min_bound                        0
% 3.21/1.00  --bmc1_max_bound                        -1
% 3.21/1.00  --bmc1_max_bound_default                -1
% 3.21/1.00  --bmc1_symbol_reachability              true
% 3.21/1.00  --bmc1_property_lemmas                  false
% 3.21/1.00  --bmc1_k_induction                      false
% 3.21/1.00  --bmc1_non_equiv_states                 false
% 3.21/1.00  --bmc1_deadlock                         false
% 3.21/1.00  --bmc1_ucm                              false
% 3.21/1.00  --bmc1_add_unsat_core                   none
% 3.21/1.00  --bmc1_unsat_core_children              false
% 3.21/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.21/1.00  --bmc1_out_stat                         full
% 3.21/1.00  --bmc1_ground_init                      false
% 3.21/1.00  --bmc1_pre_inst_next_state              false
% 3.21/1.00  --bmc1_pre_inst_state                   false
% 3.21/1.00  --bmc1_pre_inst_reach_state             false
% 3.21/1.00  --bmc1_out_unsat_core                   false
% 3.21/1.00  --bmc1_aig_witness_out                  false
% 3.21/1.00  --bmc1_verbose                          false
% 3.21/1.00  --bmc1_dump_clauses_tptp                false
% 3.21/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.21/1.00  --bmc1_dump_file                        -
% 3.21/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.21/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.21/1.00  --bmc1_ucm_extend_mode                  1
% 3.21/1.00  --bmc1_ucm_init_mode                    2
% 3.21/1.00  --bmc1_ucm_cone_mode                    none
% 3.21/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.21/1.00  --bmc1_ucm_relax_model                  4
% 3.21/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.21/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.21/1.00  --bmc1_ucm_layered_model                none
% 3.21/1.00  --bmc1_ucm_max_lemma_size               10
% 3.21/1.00  
% 3.21/1.00  ------ AIG Options
% 3.21/1.00  
% 3.21/1.00  --aig_mode                              false
% 3.21/1.00  
% 3.21/1.00  ------ Instantiation Options
% 3.21/1.00  
% 3.21/1.00  --instantiation_flag                    true
% 3.21/1.00  --inst_sos_flag                         false
% 3.21/1.00  --inst_sos_phase                        true
% 3.21/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.21/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.21/1.00  --inst_lit_sel_side                     num_symb
% 3.21/1.00  --inst_solver_per_active                1400
% 3.21/1.00  --inst_solver_calls_frac                1.
% 3.21/1.00  --inst_passive_queue_type               priority_queues
% 3.21/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.21/1.00  --inst_passive_queues_freq              [25;2]
% 3.21/1.00  --inst_dismatching                      true
% 3.21/1.00  --inst_eager_unprocessed_to_passive     true
% 3.21/1.00  --inst_prop_sim_given                   true
% 3.21/1.00  --inst_prop_sim_new                     false
% 3.21/1.00  --inst_subs_new                         false
% 3.21/1.00  --inst_eq_res_simp                      false
% 3.21/1.00  --inst_subs_given                       false
% 3.21/1.00  --inst_orphan_elimination               true
% 3.21/1.00  --inst_learning_loop_flag               true
% 3.21/1.00  --inst_learning_start                   3000
% 3.21/1.00  --inst_learning_factor                  2
% 3.21/1.00  --inst_start_prop_sim_after_learn       3
% 3.21/1.00  --inst_sel_renew                        solver
% 3.21/1.00  --inst_lit_activity_flag                true
% 3.21/1.00  --inst_restr_to_given                   false
% 3.21/1.00  --inst_activity_threshold               500
% 3.21/1.00  --inst_out_proof                        true
% 3.21/1.00  
% 3.21/1.00  ------ Resolution Options
% 3.21/1.00  
% 3.21/1.00  --resolution_flag                       true
% 3.21/1.00  --res_lit_sel                           adaptive
% 3.21/1.00  --res_lit_sel_side                      none
% 3.21/1.00  --res_ordering                          kbo
% 3.21/1.00  --res_to_prop_solver                    active
% 3.21/1.00  --res_prop_simpl_new                    false
% 3.21/1.00  --res_prop_simpl_given                  true
% 3.21/1.00  --res_passive_queue_type                priority_queues
% 3.21/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.21/1.00  --res_passive_queues_freq               [15;5]
% 3.21/1.00  --res_forward_subs                      full
% 3.21/1.00  --res_backward_subs                     full
% 3.21/1.00  --res_forward_subs_resolution           true
% 3.21/1.00  --res_backward_subs_resolution          true
% 3.21/1.00  --res_orphan_elimination                true
% 3.21/1.00  --res_time_limit                        2.
% 3.21/1.00  --res_out_proof                         true
% 3.21/1.00  
% 3.21/1.00  ------ Superposition Options
% 3.21/1.00  
% 3.21/1.00  --superposition_flag                    true
% 3.21/1.00  --sup_passive_queue_type                priority_queues
% 3.21/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.21/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.21/1.00  --demod_completeness_check              fast
% 3.21/1.00  --demod_use_ground                      true
% 3.21/1.00  --sup_to_prop_solver                    passive
% 3.21/1.00  --sup_prop_simpl_new                    true
% 3.21/1.00  --sup_prop_simpl_given                  true
% 3.21/1.00  --sup_fun_splitting                     false
% 3.21/1.00  --sup_smt_interval                      50000
% 3.21/1.00  
% 3.21/1.00  ------ Superposition Simplification Setup
% 3.21/1.00  
% 3.21/1.00  --sup_indices_passive                   []
% 3.21/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.21/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/1.00  --sup_full_bw                           [BwDemod]
% 3.21/1.00  --sup_immed_triv                        [TrivRules]
% 3.21/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.21/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/1.00  --sup_immed_bw_main                     []
% 3.21/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.21/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.21/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.21/1.00  
% 3.21/1.00  ------ Combination Options
% 3.21/1.00  
% 3.21/1.00  --comb_res_mult                         3
% 3.21/1.00  --comb_sup_mult                         2
% 3.21/1.00  --comb_inst_mult                        10
% 3.21/1.00  
% 3.21/1.00  ------ Debug Options
% 3.21/1.00  
% 3.21/1.00  --dbg_backtrace                         false
% 3.21/1.00  --dbg_dump_prop_clauses                 false
% 3.21/1.00  --dbg_dump_prop_clauses_file            -
% 3.21/1.00  --dbg_out_stat                          false
% 3.21/1.00  ------ Parsing...
% 3.21/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.21/1.00  
% 3.21/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.21/1.00  
% 3.21/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.21/1.00  
% 3.21/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.21/1.00  ------ Proving...
% 3.21/1.00  ------ Problem Properties 
% 3.21/1.00  
% 3.21/1.00  
% 3.21/1.00  clauses                                 27
% 3.21/1.00  conjectures                             2
% 3.21/1.00  EPR                                     4
% 3.21/1.00  Horn                                    21
% 3.21/1.00  unary                                   10
% 3.21/1.00  binary                                  10
% 3.21/1.00  lits                                    52
% 3.21/1.00  lits eq                                 25
% 3.21/1.00  fd_pure                                 0
% 3.21/1.00  fd_pseudo                               0
% 3.21/1.00  fd_cond                                 5
% 3.21/1.00  fd_pseudo_cond                          3
% 3.21/1.00  AC symbols                              0
% 3.21/1.00  
% 3.21/1.00  ------ Schedule dynamic 5 is on 
% 3.21/1.00  
% 3.21/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.21/1.00  
% 3.21/1.00  
% 3.21/1.00  ------ 
% 3.21/1.00  Current options:
% 3.21/1.00  ------ 
% 3.21/1.00  
% 3.21/1.00  ------ Input Options
% 3.21/1.00  
% 3.21/1.00  --out_options                           all
% 3.21/1.00  --tptp_safe_out                         true
% 3.21/1.00  --problem_path                          ""
% 3.21/1.00  --include_path                          ""
% 3.21/1.00  --clausifier                            res/vclausify_rel
% 3.21/1.00  --clausifier_options                    --mode clausify
% 3.21/1.00  --stdin                                 false
% 3.21/1.00  --stats_out                             all
% 3.21/1.00  
% 3.21/1.00  ------ General Options
% 3.21/1.00  
% 3.21/1.00  --fof                                   false
% 3.21/1.00  --time_out_real                         305.
% 3.21/1.00  --time_out_virtual                      -1.
% 3.21/1.00  --symbol_type_check                     false
% 3.21/1.00  --clausify_out                          false
% 3.21/1.00  --sig_cnt_out                           false
% 3.21/1.00  --trig_cnt_out                          false
% 3.21/1.00  --trig_cnt_out_tolerance                1.
% 3.21/1.00  --trig_cnt_out_sk_spl                   false
% 3.21/1.00  --abstr_cl_out                          false
% 3.21/1.00  
% 3.21/1.00  ------ Global Options
% 3.21/1.00  
% 3.21/1.00  --schedule                              default
% 3.21/1.00  --add_important_lit                     false
% 3.21/1.00  --prop_solver_per_cl                    1000
% 3.21/1.00  --min_unsat_core                        false
% 3.21/1.00  --soft_assumptions                      false
% 3.21/1.00  --soft_lemma_size                       3
% 3.21/1.00  --prop_impl_unit_size                   0
% 3.21/1.00  --prop_impl_unit                        []
% 3.21/1.00  --share_sel_clauses                     true
% 3.21/1.00  --reset_solvers                         false
% 3.21/1.00  --bc_imp_inh                            [conj_cone]
% 3.21/1.00  --conj_cone_tolerance                   3.
% 3.21/1.00  --extra_neg_conj                        none
% 3.21/1.00  --large_theory_mode                     true
% 3.21/1.00  --prolific_symb_bound                   200
% 3.21/1.00  --lt_threshold                          2000
% 3.21/1.00  --clause_weak_htbl                      true
% 3.21/1.00  --gc_record_bc_elim                     false
% 3.21/1.00  
% 3.21/1.00  ------ Preprocessing Options
% 3.21/1.00  
% 3.21/1.00  --preprocessing_flag                    true
% 3.21/1.00  --time_out_prep_mult                    0.1
% 3.21/1.00  --splitting_mode                        input
% 3.21/1.00  --splitting_grd                         true
% 3.21/1.00  --splitting_cvd                         false
% 3.21/1.00  --splitting_cvd_svl                     false
% 3.21/1.00  --splitting_nvd                         32
% 3.21/1.00  --sub_typing                            true
% 3.21/1.00  --prep_gs_sim                           true
% 3.21/1.00  --prep_unflatten                        true
% 3.21/1.00  --prep_res_sim                          true
% 3.21/1.00  --prep_upred                            true
% 3.21/1.00  --prep_sem_filter                       exhaustive
% 3.21/1.00  --prep_sem_filter_out                   false
% 3.21/1.00  --pred_elim                             true
% 3.21/1.00  --res_sim_input                         true
% 3.21/1.00  --eq_ax_congr_red                       true
% 3.21/1.00  --pure_diseq_elim                       true
% 3.21/1.00  --brand_transform                       false
% 3.21/1.00  --non_eq_to_eq                          false
% 3.21/1.00  --prep_def_merge                        true
% 3.21/1.00  --prep_def_merge_prop_impl              false
% 3.21/1.00  --prep_def_merge_mbd                    true
% 3.21/1.00  --prep_def_merge_tr_red                 false
% 3.21/1.00  --prep_def_merge_tr_cl                  false
% 3.21/1.00  --smt_preprocessing                     true
% 3.21/1.00  --smt_ac_axioms                         fast
% 3.21/1.00  --preprocessed_out                      false
% 3.21/1.00  --preprocessed_stats                    false
% 3.21/1.00  
% 3.21/1.00  ------ Abstraction refinement Options
% 3.21/1.00  
% 3.21/1.00  --abstr_ref                             []
% 3.21/1.00  --abstr_ref_prep                        false
% 3.21/1.00  --abstr_ref_until_sat                   false
% 3.21/1.00  --abstr_ref_sig_restrict                funpre
% 3.21/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.21/1.00  --abstr_ref_under                       []
% 3.21/1.00  
% 3.21/1.00  ------ SAT Options
% 3.21/1.00  
% 3.21/1.00  --sat_mode                              false
% 3.21/1.00  --sat_fm_restart_options                ""
% 3.21/1.00  --sat_gr_def                            false
% 3.21/1.00  --sat_epr_types                         true
% 3.21/1.00  --sat_non_cyclic_types                  false
% 3.21/1.00  --sat_finite_models                     false
% 3.21/1.00  --sat_fm_lemmas                         false
% 3.21/1.00  --sat_fm_prep                           false
% 3.21/1.00  --sat_fm_uc_incr                        true
% 3.21/1.00  --sat_out_model                         small
% 3.21/1.00  --sat_out_clauses                       false
% 3.21/1.00  
% 3.21/1.00  ------ QBF Options
% 3.21/1.00  
% 3.21/1.00  --qbf_mode                              false
% 3.21/1.00  --qbf_elim_univ                         false
% 3.21/1.00  --qbf_dom_inst                          none
% 3.21/1.00  --qbf_dom_pre_inst                      false
% 3.21/1.00  --qbf_sk_in                             false
% 3.21/1.00  --qbf_pred_elim                         true
% 3.21/1.00  --qbf_split                             512
% 3.21/1.00  
% 3.21/1.00  ------ BMC1 Options
% 3.21/1.00  
% 3.21/1.00  --bmc1_incremental                      false
% 3.21/1.00  --bmc1_axioms                           reachable_all
% 3.21/1.00  --bmc1_min_bound                        0
% 3.21/1.00  --bmc1_max_bound                        -1
% 3.21/1.00  --bmc1_max_bound_default                -1
% 3.21/1.00  --bmc1_symbol_reachability              true
% 3.21/1.00  --bmc1_property_lemmas                  false
% 3.21/1.00  --bmc1_k_induction                      false
% 3.21/1.00  --bmc1_non_equiv_states                 false
% 3.21/1.00  --bmc1_deadlock                         false
% 3.21/1.00  --bmc1_ucm                              false
% 3.21/1.00  --bmc1_add_unsat_core                   none
% 3.21/1.00  --bmc1_unsat_core_children              false
% 3.21/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.21/1.00  --bmc1_out_stat                         full
% 3.21/1.00  --bmc1_ground_init                      false
% 3.21/1.00  --bmc1_pre_inst_next_state              false
% 3.21/1.00  --bmc1_pre_inst_state                   false
% 3.21/1.00  --bmc1_pre_inst_reach_state             false
% 3.21/1.00  --bmc1_out_unsat_core                   false
% 3.21/1.00  --bmc1_aig_witness_out                  false
% 3.21/1.00  --bmc1_verbose                          false
% 3.21/1.00  --bmc1_dump_clauses_tptp                false
% 3.21/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.21/1.00  --bmc1_dump_file                        -
% 3.21/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.21/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.21/1.00  --bmc1_ucm_extend_mode                  1
% 3.21/1.00  --bmc1_ucm_init_mode                    2
% 3.21/1.00  --bmc1_ucm_cone_mode                    none
% 3.21/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.21/1.00  --bmc1_ucm_relax_model                  4
% 3.21/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.21/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.21/1.00  --bmc1_ucm_layered_model                none
% 3.21/1.00  --bmc1_ucm_max_lemma_size               10
% 3.21/1.00  
% 3.21/1.00  ------ AIG Options
% 3.21/1.00  
% 3.21/1.00  --aig_mode                              false
% 3.21/1.00  
% 3.21/1.00  ------ Instantiation Options
% 3.21/1.00  
% 3.21/1.00  --instantiation_flag                    true
% 3.21/1.00  --inst_sos_flag                         false
% 3.21/1.00  --inst_sos_phase                        true
% 3.21/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.21/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.21/1.00  --inst_lit_sel_side                     none
% 3.21/1.00  --inst_solver_per_active                1400
% 3.21/1.00  --inst_solver_calls_frac                1.
% 3.21/1.00  --inst_passive_queue_type               priority_queues
% 3.21/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.21/1.00  --inst_passive_queues_freq              [25;2]
% 3.21/1.00  --inst_dismatching                      true
% 3.21/1.00  --inst_eager_unprocessed_to_passive     true
% 3.21/1.00  --inst_prop_sim_given                   true
% 3.21/1.00  --inst_prop_sim_new                     false
% 3.21/1.00  --inst_subs_new                         false
% 3.21/1.00  --inst_eq_res_simp                      false
% 3.21/1.00  --inst_subs_given                       false
% 3.21/1.00  --inst_orphan_elimination               true
% 3.21/1.00  --inst_learning_loop_flag               true
% 3.21/1.00  --inst_learning_start                   3000
% 3.21/1.00  --inst_learning_factor                  2
% 3.21/1.00  --inst_start_prop_sim_after_learn       3
% 3.21/1.00  --inst_sel_renew                        solver
% 3.21/1.00  --inst_lit_activity_flag                true
% 3.21/1.00  --inst_restr_to_given                   false
% 3.21/1.00  --inst_activity_threshold               500
% 3.21/1.00  --inst_out_proof                        true
% 3.21/1.00  
% 3.21/1.00  ------ Resolution Options
% 3.21/1.00  
% 3.21/1.00  --resolution_flag                       false
% 3.21/1.00  --res_lit_sel                           adaptive
% 3.21/1.00  --res_lit_sel_side                      none
% 3.21/1.00  --res_ordering                          kbo
% 3.21/1.00  --res_to_prop_solver                    active
% 3.21/1.00  --res_prop_simpl_new                    false
% 3.21/1.00  --res_prop_simpl_given                  true
% 3.21/1.00  --res_passive_queue_type                priority_queues
% 3.21/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.21/1.00  --res_passive_queues_freq               [15;5]
% 3.21/1.00  --res_forward_subs                      full
% 3.21/1.00  --res_backward_subs                     full
% 3.21/1.00  --res_forward_subs_resolution           true
% 3.21/1.00  --res_backward_subs_resolution          true
% 3.21/1.00  --res_orphan_elimination                true
% 3.21/1.00  --res_time_limit                        2.
% 3.21/1.00  --res_out_proof                         true
% 3.21/1.00  
% 3.21/1.00  ------ Superposition Options
% 3.21/1.00  
% 3.21/1.00  --superposition_flag                    true
% 3.21/1.00  --sup_passive_queue_type                priority_queues
% 3.21/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.21/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.21/1.00  --demod_completeness_check              fast
% 3.21/1.00  --demod_use_ground                      true
% 3.21/1.00  --sup_to_prop_solver                    passive
% 3.21/1.00  --sup_prop_simpl_new                    true
% 3.21/1.00  --sup_prop_simpl_given                  true
% 3.21/1.00  --sup_fun_splitting                     false
% 3.21/1.00  --sup_smt_interval                      50000
% 3.21/1.00  
% 3.21/1.00  ------ Superposition Simplification Setup
% 3.21/1.00  
% 3.21/1.00  --sup_indices_passive                   []
% 3.21/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.21/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/1.00  --sup_full_bw                           [BwDemod]
% 3.21/1.00  --sup_immed_triv                        [TrivRules]
% 3.21/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.21/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/1.00  --sup_immed_bw_main                     []
% 3.21/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.21/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.21/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.21/1.00  
% 3.21/1.00  ------ Combination Options
% 3.21/1.00  
% 3.21/1.00  --comb_res_mult                         3
% 3.21/1.00  --comb_sup_mult                         2
% 3.21/1.00  --comb_inst_mult                        10
% 3.21/1.00  
% 3.21/1.00  ------ Debug Options
% 3.21/1.00  
% 3.21/1.00  --dbg_backtrace                         false
% 3.21/1.00  --dbg_dump_prop_clauses                 false
% 3.21/1.00  --dbg_dump_prop_clauses_file            -
% 3.21/1.00  --dbg_out_stat                          false
% 3.21/1.00  
% 3.21/1.00  
% 3.21/1.00  
% 3.21/1.00  
% 3.21/1.00  ------ Proving...
% 3.21/1.00  
% 3.21/1.00  
% 3.21/1.00  % SZS status Theorem for theBenchmark.p
% 3.21/1.00  
% 3.21/1.00   Resolution empty clause
% 3.21/1.00  
% 3.21/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.21/1.00  
% 3.21/1.00  fof(f2,axiom,(
% 3.21/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.21/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/1.01  
% 3.21/1.01  fof(f23,plain,(
% 3.21/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.21/1.01    inference(nnf_transformation,[],[f2])).
% 3.21/1.01  
% 3.21/1.01  fof(f24,plain,(
% 3.21/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.21/1.01    inference(flattening,[],[f23])).
% 3.21/1.01  
% 3.21/1.01  fof(f40,plain,(
% 3.21/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.21/1.01    inference(cnf_transformation,[],[f24])).
% 3.21/1.01  
% 3.21/1.01  fof(f66,plain,(
% 3.21/1.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.21/1.01    inference(equality_resolution,[],[f40])).
% 3.21/1.01  
% 3.21/1.01  fof(f6,axiom,(
% 3.21/1.01    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 3.21/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/1.01  
% 3.21/1.01  fof(f14,plain,(
% 3.21/1.01    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 3.21/1.01    inference(ennf_transformation,[],[f6])).
% 3.21/1.01  
% 3.21/1.01  fof(f29,plain,(
% 3.21/1.01    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK2(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))))),
% 3.21/1.01    introduced(choice_axiom,[])).
% 3.21/1.01  
% 3.21/1.01  fof(f30,plain,(
% 3.21/1.01    ! [X0,X1] : (! [X3] : (k1_funct_1(sK2(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1)))),
% 3.21/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f29])).
% 3.21/1.01  
% 3.21/1.01  fof(f53,plain,(
% 3.21/1.01    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0) )),
% 3.21/1.01    inference(cnf_transformation,[],[f30])).
% 3.21/1.01  
% 3.21/1.01  fof(f5,axiom,(
% 3.21/1.01    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 3.21/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/1.01  
% 3.21/1.01  fof(f12,plain,(
% 3.21/1.01    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.21/1.01    inference(ennf_transformation,[],[f5])).
% 3.21/1.01  
% 3.21/1.01  fof(f13,plain,(
% 3.21/1.01    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.21/1.01    inference(flattening,[],[f12])).
% 3.21/1.01  
% 3.21/1.01  fof(f49,plain,(
% 3.21/1.01    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.21/1.01    inference(cnf_transformation,[],[f13])).
% 3.21/1.01  
% 3.21/1.01  fof(f51,plain,(
% 3.21/1.01    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1))) )),
% 3.21/1.01    inference(cnf_transformation,[],[f30])).
% 3.21/1.01  
% 3.21/1.01  fof(f1,axiom,(
% 3.21/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.21/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/1.01  
% 3.21/1.01  fof(f11,plain,(
% 3.21/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.21/1.01    inference(ennf_transformation,[],[f1])).
% 3.21/1.01  
% 3.21/1.01  fof(f19,plain,(
% 3.21/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.21/1.01    inference(nnf_transformation,[],[f11])).
% 3.21/1.01  
% 3.21/1.01  fof(f20,plain,(
% 3.21/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.21/1.01    inference(rectify,[],[f19])).
% 3.21/1.01  
% 3.21/1.01  fof(f21,plain,(
% 3.21/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.21/1.01    introduced(choice_axiom,[])).
% 3.21/1.01  
% 3.21/1.01  fof(f22,plain,(
% 3.21/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.21/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).
% 3.21/1.01  
% 3.21/1.01  fof(f38,plain,(
% 3.21/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.21/1.01    inference(cnf_transformation,[],[f22])).
% 3.21/1.01  
% 3.21/1.01  fof(f54,plain,(
% 3.21/1.01    ( ! [X0,X3,X1] : (k1_funct_1(sK2(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 3.21/1.01    inference(cnf_transformation,[],[f30])).
% 3.21/1.01  
% 3.21/1.01  fof(f3,axiom,(
% 3.21/1.01    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.21/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/1.01  
% 3.21/1.01  fof(f25,plain,(
% 3.21/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.21/1.01    inference(nnf_transformation,[],[f3])).
% 3.21/1.01  
% 3.21/1.01  fof(f26,plain,(
% 3.21/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.21/1.01    inference(rectify,[],[f25])).
% 3.21/1.01  
% 3.21/1.01  fof(f27,plain,(
% 3.21/1.01    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 3.21/1.01    introduced(choice_axiom,[])).
% 3.21/1.01  
% 3.21/1.01  fof(f28,plain,(
% 3.21/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.21/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).
% 3.21/1.01  
% 3.21/1.01  fof(f43,plain,(
% 3.21/1.01    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.21/1.01    inference(cnf_transformation,[],[f28])).
% 3.21/1.01  
% 3.21/1.01  fof(f69,plain,(
% 3.21/1.01    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 3.21/1.01    inference(equality_resolution,[],[f43])).
% 3.21/1.01  
% 3.21/1.01  fof(f8,axiom,(
% 3.21/1.01    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 3.21/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/1.01  
% 3.21/1.01  fof(f16,plain,(
% 3.21/1.01    ! [X0] : (! [X1] : ? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 3.21/1.01    inference(ennf_transformation,[],[f8])).
% 3.21/1.01  
% 3.21/1.01  fof(f33,plain,(
% 3.21/1.01    ! [X1,X0] : (? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_tarski(X1) = k2_relat_1(sK4(X0,X1)) & k1_relat_1(sK4(X0,X1)) = X0 & v1_funct_1(sK4(X0,X1)) & v1_relat_1(sK4(X0,X1))))),
% 3.21/1.01    introduced(choice_axiom,[])).
% 3.21/1.01  
% 3.21/1.01  fof(f34,plain,(
% 3.21/1.01    ! [X0] : (! [X1] : (k1_tarski(X1) = k2_relat_1(sK4(X0,X1)) & k1_relat_1(sK4(X0,X1)) = X0 & v1_funct_1(sK4(X0,X1)) & v1_relat_1(sK4(X0,X1))) | k1_xboole_0 = X0)),
% 3.21/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f33])).
% 3.21/1.01  
% 3.21/1.01  fof(f62,plain,(
% 3.21/1.01    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK4(X0,X1)) | k1_xboole_0 = X0) )),
% 3.21/1.01    inference(cnf_transformation,[],[f34])).
% 3.21/1.01  
% 3.21/1.01  fof(f61,plain,(
% 3.21/1.01    ( ! [X0,X1] : (k1_relat_1(sK4(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 3.21/1.01    inference(cnf_transformation,[],[f34])).
% 3.21/1.01  
% 3.21/1.01  fof(f9,conjecture,(
% 3.21/1.01    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 3.21/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/1.01  
% 3.21/1.01  fof(f10,negated_conjecture,(
% 3.21/1.01    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 3.21/1.01    inference(negated_conjecture,[],[f9])).
% 3.21/1.01  
% 3.21/1.01  fof(f17,plain,(
% 3.21/1.01    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 3.21/1.01    inference(ennf_transformation,[],[f10])).
% 3.21/1.01  
% 3.21/1.01  fof(f18,plain,(
% 3.21/1.01    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 3.21/1.01    inference(flattening,[],[f17])).
% 3.21/1.01  
% 3.21/1.01  fof(f35,plain,(
% 3.21/1.01    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0)) => (! [X2] : (~r1_tarski(k2_relat_1(X2),sK5) | k1_relat_1(X2) != sK6 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK6 | k1_xboole_0 != sK5))),
% 3.21/1.01    introduced(choice_axiom,[])).
% 3.21/1.01  
% 3.21/1.01  fof(f36,plain,(
% 3.21/1.01    ! [X2] : (~r1_tarski(k2_relat_1(X2),sK5) | k1_relat_1(X2) != sK6 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK6 | k1_xboole_0 != sK5)),
% 3.21/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f18,f35])).
% 3.21/1.01  
% 3.21/1.01  fof(f64,plain,(
% 3.21/1.01    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK5) | k1_relat_1(X2) != sK6 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.21/1.01    inference(cnf_transformation,[],[f36])).
% 3.21/1.01  
% 3.21/1.01  fof(f59,plain,(
% 3.21/1.01    ( ! [X0,X1] : (v1_relat_1(sK4(X0,X1)) | k1_xboole_0 = X0) )),
% 3.21/1.01    inference(cnf_transformation,[],[f34])).
% 3.21/1.01  
% 3.21/1.01  fof(f60,plain,(
% 3.21/1.01    ( ! [X0,X1] : (v1_funct_1(sK4(X0,X1)) | k1_xboole_0 = X0) )),
% 3.21/1.01    inference(cnf_transformation,[],[f34])).
% 3.21/1.01  
% 3.21/1.01  fof(f39,plain,(
% 3.21/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.21/1.01    inference(cnf_transformation,[],[f22])).
% 3.21/1.01  
% 3.21/1.01  fof(f42,plain,(
% 3.21/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.21/1.01    inference(cnf_transformation,[],[f24])).
% 3.21/1.01  
% 3.21/1.01  fof(f63,plain,(
% 3.21/1.01    k1_xboole_0 = sK6 | k1_xboole_0 != sK5),
% 3.21/1.01    inference(cnf_transformation,[],[f36])).
% 3.21/1.01  
% 3.21/1.01  fof(f44,plain,(
% 3.21/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.21/1.01    inference(cnf_transformation,[],[f28])).
% 3.21/1.01  
% 3.21/1.01  fof(f67,plain,(
% 3.21/1.01    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 3.21/1.01    inference(equality_resolution,[],[f44])).
% 3.21/1.01  
% 3.21/1.01  fof(f68,plain,(
% 3.21/1.01    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 3.21/1.01    inference(equality_resolution,[],[f67])).
% 3.21/1.01  
% 3.21/1.01  fof(f7,axiom,(
% 3.21/1.01    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.21/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/1.01  
% 3.21/1.01  fof(f15,plain,(
% 3.21/1.01    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.21/1.01    inference(ennf_transformation,[],[f7])).
% 3.21/1.01  
% 3.21/1.01  fof(f31,plain,(
% 3.21/1.01    ! [X0] : (? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_xboole_0 = k1_funct_1(sK3(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK3(X0)) = X0 & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0))))),
% 3.21/1.01    introduced(choice_axiom,[])).
% 3.21/1.01  
% 3.21/1.01  fof(f32,plain,(
% 3.21/1.01    ! [X0] : (! [X2] : (k1_xboole_0 = k1_funct_1(sK3(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK3(X0)) = X0 & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0)))),
% 3.21/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f31])).
% 3.21/1.01  
% 3.21/1.01  fof(f57,plain,(
% 3.21/1.01    ( ! [X0] : (k1_relat_1(sK3(X0)) = X0) )),
% 3.21/1.01    inference(cnf_transformation,[],[f32])).
% 3.21/1.01  
% 3.21/1.01  fof(f55,plain,(
% 3.21/1.01    ( ! [X0] : (v1_relat_1(sK3(X0))) )),
% 3.21/1.01    inference(cnf_transformation,[],[f32])).
% 3.21/1.01  
% 3.21/1.01  fof(f56,plain,(
% 3.21/1.01    ( ! [X0] : (v1_funct_1(sK3(X0))) )),
% 3.21/1.01    inference(cnf_transformation,[],[f32])).
% 3.21/1.01  
% 3.21/1.01  fof(f4,axiom,(
% 3.21/1.01    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.21/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/1.01  
% 3.21/1.01  fof(f48,plain,(
% 3.21/1.01    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.21/1.01    inference(cnf_transformation,[],[f4])).
% 3.21/1.01  
% 3.21/1.01  fof(f52,plain,(
% 3.21/1.01    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1))) )),
% 3.21/1.01    inference(cnf_transformation,[],[f30])).
% 3.21/1.01  
% 3.21/1.01  cnf(c_5,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f66]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_1128,plain,
% 3.21/1.01      ( r1_tarski(X0,X0) = iProver_top ),
% 3.21/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_15,plain,
% 3.21/1.01      ( k1_relat_1(sK2(X0,X1)) = X0 ),
% 3.21/1.01      inference(cnf_transformation,[],[f53]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_13,plain,
% 3.21/1.01      ( ~ v1_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 3.21/1.01      inference(cnf_transformation,[],[f49]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_1122,plain,
% 3.21/1.01      ( k1_relat_1(X0) != k1_xboole_0
% 3.21/1.01      | k1_xboole_0 = X0
% 3.21/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.21/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_2498,plain,
% 3.21/1.01      ( sK2(X0,X1) = k1_xboole_0
% 3.21/1.01      | k1_xboole_0 != X0
% 3.21/1.01      | v1_relat_1(sK2(X0,X1)) != iProver_top ),
% 3.21/1.01      inference(superposition,[status(thm)],[c_15,c_1122]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_17,plain,
% 3.21/1.01      ( v1_relat_1(sK2(X0,X1)) ),
% 3.21/1.01      inference(cnf_transformation,[],[f51]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_49,plain,
% 3.21/1.01      ( v1_relat_1(sK2(X0,X1)) = iProver_top ),
% 3.21/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_3110,plain,
% 3.21/1.01      ( k1_xboole_0 != X0 | sK2(X0,X1) = k1_xboole_0 ),
% 3.21/1.01      inference(global_propositional_subsumption,[status(thm)],[c_2498,c_49]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_3111,plain,
% 3.21/1.01      ( sK2(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.21/1.01      inference(renaming,[status(thm)],[c_3110]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_3115,plain,
% 3.21/1.01      ( sK2(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.21/1.01      inference(equality_resolution,[status(thm)],[c_3111]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_1,plain,
% 3.21/1.01      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.21/1.01      inference(cnf_transformation,[],[f38]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_1131,plain,
% 3.21/1.01      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.21/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 3.21/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_14,plain,
% 3.21/1.01      ( ~ r2_hidden(X0,X1) | k1_funct_1(sK2(X1,X2),X0) = X2 ),
% 3.21/1.01      inference(cnf_transformation,[],[f54]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_1121,plain,
% 3.21/1.01      ( k1_funct_1(sK2(X0,X1),X2) = X1 | r2_hidden(X2,X0) != iProver_top ),
% 3.21/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_2832,plain,
% 3.21/1.01      ( k1_funct_1(sK2(X0,X1),sK0(X0,X2)) = X1
% 3.21/1.01      | r1_tarski(X0,X2) = iProver_top ),
% 3.21/1.01      inference(superposition,[status(thm)],[c_1131,c_1121]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_9,plain,
% 3.21/1.01      ( ~ r2_hidden(X0,k1_tarski(X1)) | X0 = X1 ),
% 3.21/1.01      inference(cnf_transformation,[],[f69]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_1124,plain,
% 3.21/1.01      ( X0 = X1 | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
% 3.21/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_2833,plain,
% 3.21/1.01      ( sK0(k1_tarski(X0),X1) = X0
% 3.21/1.01      | r1_tarski(k1_tarski(X0),X1) = iProver_top ),
% 3.21/1.01      inference(superposition,[status(thm)],[c_1131,c_1124]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_22,plain,
% 3.21/1.01      ( k2_relat_1(sK4(X0,X1)) = k1_tarski(X1) | k1_xboole_0 = X0 ),
% 3.21/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_23,plain,
% 3.21/1.01      ( k1_relat_1(sK4(X0,X1)) = X0 | k1_xboole_0 = X0 ),
% 3.21/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_26,negated_conjecture,
% 3.21/1.01      ( ~ r1_tarski(k2_relat_1(X0),sK5)
% 3.21/1.01      | ~ v1_funct_1(X0)
% 3.21/1.01      | ~ v1_relat_1(X0)
% 3.21/1.01      | k1_relat_1(X0) != sK6 ),
% 3.21/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_1113,plain,
% 3.21/1.01      ( k1_relat_1(X0) != sK6
% 3.21/1.01      | r1_tarski(k2_relat_1(X0),sK5) != iProver_top
% 3.21/1.01      | v1_funct_1(X0) != iProver_top
% 3.21/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.21/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_1541,plain,
% 3.21/1.01      ( sK6 != X0
% 3.21/1.01      | k1_xboole_0 = X0
% 3.21/1.01      | r1_tarski(k2_relat_1(sK4(X0,X1)),sK5) != iProver_top
% 3.21/1.01      | v1_funct_1(sK4(X0,X1)) != iProver_top
% 3.21/1.01      | v1_relat_1(sK4(X0,X1)) != iProver_top ),
% 3.21/1.01      inference(superposition,[status(thm)],[c_23,c_1113]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_25,plain,
% 3.21/1.01      ( v1_relat_1(sK4(X0,X1)) | k1_xboole_0 = X0 ),
% 3.21/1.01      inference(cnf_transformation,[],[f59]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_31,plain,
% 3.21/1.01      ( k1_xboole_0 = X0 | v1_relat_1(sK4(X0,X1)) = iProver_top ),
% 3.21/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_24,plain,
% 3.21/1.01      ( v1_funct_1(sK4(X0,X1)) | k1_xboole_0 = X0 ),
% 3.21/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_34,plain,
% 3.21/1.01      ( k1_xboole_0 = X0 | v1_funct_1(sK4(X0,X1)) = iProver_top ),
% 3.21/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_1618,plain,
% 3.21/1.01      ( sK6 != X0
% 3.21/1.01      | k1_xboole_0 = X0
% 3.21/1.01      | r1_tarski(k2_relat_1(sK4(X0,X1)),sK5) != iProver_top ),
% 3.21/1.01      inference(global_propositional_subsumption,
% 3.21/1.01                [status(thm)],
% 3.21/1.01                [c_1541,c_31,c_34]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_1625,plain,
% 3.21/1.01      ( sK6 = k1_xboole_0
% 3.21/1.01      | r1_tarski(k2_relat_1(sK4(sK6,X0)),sK5) != iProver_top ),
% 3.21/1.01      inference(equality_resolution,[status(thm)],[c_1618]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_1647,plain,
% 3.21/1.01      ( sK6 = k1_xboole_0 | r1_tarski(k1_tarski(X0),sK5) != iProver_top ),
% 3.21/1.01      inference(superposition,[status(thm)],[c_22,c_1625]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_3678,plain,
% 3.21/1.01      ( sK0(k1_tarski(X0),sK5) = X0 | sK6 = k1_xboole_0 ),
% 3.21/1.01      inference(superposition,[status(thm)],[c_2833,c_1647]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_0,plain,
% 3.21/1.01      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.21/1.01      inference(cnf_transformation,[],[f39]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_1132,plain,
% 3.21/1.01      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.21/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 3.21/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_3703,plain,
% 3.21/1.01      ( sK6 = k1_xboole_0
% 3.21/1.01      | r2_hidden(X0,sK5) != iProver_top
% 3.21/1.01      | r1_tarski(k1_tarski(X0),sK5) = iProver_top ),
% 3.21/1.01      inference(superposition,[status(thm)],[c_3678,c_1132]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_4131,plain,
% 3.21/1.01      ( r2_hidden(X0,sK5) != iProver_top | sK6 = k1_xboole_0 ),
% 3.21/1.01      inference(global_propositional_subsumption,[status(thm)],[c_3703,c_1647]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_4132,plain,
% 3.21/1.01      ( sK6 = k1_xboole_0 | r2_hidden(X0,sK5) != iProver_top ),
% 3.21/1.01      inference(renaming,[status(thm)],[c_4131]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_4139,plain,
% 3.21/1.01      ( sK6 = k1_xboole_0 | r1_tarski(sK5,X0) = iProver_top ),
% 3.21/1.01      inference(superposition,[status(thm)],[c_1131,c_4132]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_3,plain,
% 3.21/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.21/1.01      inference(cnf_transformation,[],[f42]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_1129,plain,
% 3.21/1.01      ( X0 = X1
% 3.21/1.01      | r1_tarski(X1,X0) != iProver_top
% 3.21/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 3.21/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_4214,plain,
% 3.21/1.01      ( sK6 = k1_xboole_0 | sK5 = X0 | r1_tarski(X0,sK5) != iProver_top ),
% 3.21/1.01      inference(superposition,[status(thm)],[c_4139,c_1129]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_4289,plain,
% 3.21/1.01      ( k1_funct_1(sK2(X0,X1),sK0(X0,sK5)) = X1
% 3.21/1.01      | sK6 = k1_xboole_0
% 3.21/1.01      | sK5 = X0 ),
% 3.21/1.01      inference(superposition,[status(thm)],[c_2832,c_4214]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_4702,plain,
% 3.21/1.01      ( k1_funct_1(k1_xboole_0,sK0(k1_xboole_0,sK5)) = X0
% 3.21/1.01      | sK6 = k1_xboole_0
% 3.21/1.01      | sK5 = k1_xboole_0 ),
% 3.21/1.01      inference(superposition,[status(thm)],[c_3115,c_4289]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_27,negated_conjecture,
% 3.21/1.01      ( k1_xboole_0 = sK6 | k1_xboole_0 != sK5 ),
% 3.21/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_66,plain,
% 3.21/1.01      ( ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
% 3.21/1.01      | k1_xboole_0 = k1_xboole_0 ),
% 3.21/1.01      inference(instantiation,[status(thm)],[c_9]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_8,plain,
% 3.21/1.01      ( r2_hidden(X0,k1_tarski(X0)) ),
% 3.21/1.01      inference(cnf_transformation,[],[f68]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_69,plain,
% 3.21/1.01      ( r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
% 3.21/1.01      inference(instantiation,[status(thm)],[c_8]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_750,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_1372,plain,
% 3.21/1.01      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 3.21/1.01      inference(instantiation,[status(thm)],[c_750]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_1373,plain,
% 3.21/1.01      ( sK5 != k1_xboole_0 | k1_xboole_0 = sK5 | k1_xboole_0 != k1_xboole_0 ),
% 3.21/1.01      inference(instantiation,[status(thm)],[c_1372]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_1757,plain,
% 3.21/1.01      ( ~ r2_hidden(sK6,k1_tarski(X0)) | sK6 = X0 ),
% 3.21/1.01      inference(instantiation,[status(thm)],[c_9]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_2156,plain,
% 3.21/1.01      ( ~ r2_hidden(sK6,k1_tarski(sK6)) | sK6 = sK6 ),
% 3.21/1.01      inference(instantiation,[status(thm)],[c_1757]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_2157,plain,
% 3.21/1.01      ( r2_hidden(sK6,k1_tarski(sK6)) ),
% 3.21/1.01      inference(instantiation,[status(thm)],[c_8]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_1767,plain,
% 3.21/1.01      ( X0 != X1 | sK6 != X1 | sK6 = X0 ),
% 3.21/1.01      inference(instantiation,[status(thm)],[c_750]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_2356,plain,
% 3.21/1.01      ( X0 != sK6 | sK6 = X0 | sK6 != sK6 ),
% 3.21/1.01      inference(instantiation,[status(thm)],[c_1767]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_2358,plain,
% 3.21/1.01      ( sK6 != sK6 | sK6 = k1_xboole_0 | k1_xboole_0 != sK6 ),
% 3.21/1.01      inference(instantiation,[status(thm)],[c_2356]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_4782,plain,
% 3.21/1.01      ( sK6 = k1_xboole_0 | k1_funct_1(k1_xboole_0,sK0(k1_xboole_0,sK5)) = X0 ),
% 3.21/1.01      inference(global_propositional_subsumption,
% 3.21/1.01                [status(thm)],
% 3.21/1.01                [c_4702,c_27,c_66,c_69,c_1373,c_2156,c_2157,c_2358]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_4783,plain,
% 3.21/1.01      ( k1_funct_1(k1_xboole_0,sK0(k1_xboole_0,sK5)) = X0 | sK6 = k1_xboole_0 ),
% 3.21/1.01      inference(renaming,[status(thm)],[c_4782]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_4869,plain,
% 3.21/1.01      ( X0 = X1
% 3.21/1.01      | sK6 = k1_xboole_0
% 3.21/1.01      | r2_hidden(X1,k1_funct_1(k1_xboole_0,sK0(k1_xboole_0,sK5))) != iProver_top ),
% 3.21/1.01      inference(superposition,[status(thm)],[c_4783,c_1124]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_1125,plain,
% 3.21/1.01      ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
% 3.21/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_4882,plain,
% 3.21/1.01      ( sK6 = k1_xboole_0
% 3.21/1.01      | r2_hidden(X0,k1_funct_1(k1_xboole_0,sK0(k1_xboole_0,sK5))) = iProver_top ),
% 3.21/1.01      inference(superposition,[status(thm)],[c_4783,c_1125]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_4957,plain,
% 3.21/1.01      ( X0 = X1 | sK6 = k1_xboole_0 ),
% 3.21/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_4869,c_4882]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_5399,plain,
% 3.21/1.01      ( sK6 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.21/1.01      inference(equality_factoring,[status(thm)],[c_4957]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_5414,plain,
% 3.21/1.01      ( sK6 = k1_xboole_0 ),
% 3.21/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_5399,c_4957]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_19,plain,
% 3.21/1.01      ( k1_relat_1(sK3(X0)) = X0 ),
% 3.21/1.01      inference(cnf_transformation,[],[f57]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_1368,plain,
% 3.21/1.01      ( sK6 != X0
% 3.21/1.01      | r1_tarski(k2_relat_1(sK3(X0)),sK5) != iProver_top
% 3.21/1.01      | v1_funct_1(sK3(X0)) != iProver_top
% 3.21/1.01      | v1_relat_1(sK3(X0)) != iProver_top ),
% 3.21/1.01      inference(superposition,[status(thm)],[c_19,c_1113]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_21,plain,
% 3.21/1.01      ( v1_relat_1(sK3(X0)) ),
% 3.21/1.01      inference(cnf_transformation,[],[f55]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_39,plain,
% 3.21/1.01      ( v1_relat_1(sK3(X0)) = iProver_top ),
% 3.21/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_20,plain,
% 3.21/1.01      ( v1_funct_1(sK3(X0)) ),
% 3.21/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_42,plain,
% 3.21/1.01      ( v1_funct_1(sK3(X0)) = iProver_top ),
% 3.21/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_1380,plain,
% 3.21/1.01      ( sK6 != X0 | r1_tarski(k2_relat_1(sK3(X0)),sK5) != iProver_top ),
% 3.21/1.01      inference(global_propositional_subsumption,
% 3.21/1.01                [status(thm)],
% 3.21/1.01                [c_1368,c_39,c_42]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_1388,plain,
% 3.21/1.01      ( r1_tarski(k2_relat_1(sK3(sK6)),sK5) != iProver_top ),
% 3.21/1.01      inference(equality_resolution,[status(thm)],[c_1380]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_3809,plain,
% 3.21/1.01      ( k1_funct_1(sK2(k2_relat_1(sK3(sK6)),X0),sK0(k2_relat_1(sK3(sK6)),sK5)) = X0 ),
% 3.21/1.01      inference(superposition,[status(thm)],[c_2832,c_1388]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_5423,plain,
% 3.21/1.01      ( k1_funct_1(sK2(k2_relat_1(sK3(k1_xboole_0)),X0),sK0(k2_relat_1(sK3(k1_xboole_0)),sK5)) = X0 ),
% 3.21/1.01      inference(demodulation,[status(thm)],[c_5414,c_3809]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_10,plain,
% 3.21/1.01      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.21/1.01      inference(cnf_transformation,[],[f48]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_2499,plain,
% 3.21/1.01      ( sK3(X0) = k1_xboole_0
% 3.21/1.01      | k1_xboole_0 != X0
% 3.21/1.01      | v1_relat_1(sK3(X0)) != iProver_top ),
% 3.21/1.01      inference(superposition,[status(thm)],[c_19,c_1122]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_2683,plain,
% 3.21/1.01      ( k1_xboole_0 != X0 | sK3(X0) = k1_xboole_0 ),
% 3.21/1.01      inference(global_propositional_subsumption,[status(thm)],[c_2499,c_39]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_2684,plain,
% 3.21/1.01      ( sK3(X0) = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.21/1.01      inference(renaming,[status(thm)],[c_2683]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_2688,plain,
% 3.21/1.01      ( sK3(k1_xboole_0) = k1_xboole_0 ),
% 3.21/1.01      inference(equality_resolution,[status(thm)],[c_2684]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_5460,plain,
% 3.21/1.01      ( k1_funct_1(k1_xboole_0,sK0(k1_xboole_0,sK5)) = X0 ),
% 3.21/1.01      inference(light_normalisation,[status(thm)],[c_5423,c_10,c_2688,c_3115]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_5800,plain,
% 3.21/1.01      ( k1_relat_1(k1_funct_1(k1_xboole_0,sK0(k1_xboole_0,sK5))) = X0 ),
% 3.21/1.01      inference(superposition,[status(thm)],[c_5460,c_15]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_5431,plain,
% 3.21/1.01      ( k1_relat_1(X0) != k1_xboole_0
% 3.21/1.01      | r1_tarski(k2_relat_1(X0),sK5) != iProver_top
% 3.21/1.01      | v1_funct_1(X0) != iProver_top
% 3.21/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.21/1.01      inference(demodulation,[status(thm)],[c_5414,c_1113]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_5801,plain,
% 3.21/1.01      ( k1_funct_1(k1_xboole_0,sK0(k1_xboole_0,sK5)) != k1_xboole_0
% 3.21/1.01      | r1_tarski(k2_relat_1(X0),sK5) != iProver_top
% 3.21/1.01      | v1_funct_1(X0) != iProver_top
% 3.21/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.21/1.01      inference(superposition,[status(thm)],[c_5460,c_5431]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_5506,plain,
% 3.21/1.01      ( k1_funct_1(k1_xboole_0,sK0(k1_xboole_0,sK5)) = k1_xboole_0 ),
% 3.21/1.01      inference(instantiation,[status(thm)],[c_5460]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_6433,plain,
% 3.21/1.01      ( r1_tarski(k2_relat_1(X0),sK5) != iProver_top
% 3.21/1.01      | v1_funct_1(X0) != iProver_top
% 3.21/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.21/1.01      inference(global_propositional_subsumption,[status(thm)],[c_5801,c_5506]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_7342,plain,
% 3.21/1.01      ( r1_tarski(k1_relat_1(k1_funct_1(k1_xboole_0,sK0(k1_xboole_0,sK5))),sK5) != iProver_top
% 3.21/1.01      | v1_funct_1(X0) != iProver_top
% 3.21/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.21/1.01      inference(superposition,[status(thm)],[c_5800,c_6433]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_51,plain,
% 3.21/1.01      ( v1_relat_1(sK2(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.21/1.01      inference(instantiation,[status(thm)],[c_49]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_16,plain,
% 3.21/1.01      ( v1_funct_1(sK2(X0,X1)) ),
% 3.21/1.01      inference(cnf_transformation,[],[f52]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_52,plain,
% 3.21/1.01      ( v1_funct_1(sK2(X0,X1)) = iProver_top ),
% 3.21/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_54,plain,
% 3.21/1.01      ( v1_funct_1(sK2(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.21/1.01      inference(instantiation,[status(thm)],[c_52]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_55,plain,
% 3.21/1.01      ( k1_relat_1(sK2(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
% 3.21/1.01      inference(instantiation,[status(thm)],[c_15]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_325,plain,
% 3.21/1.01      ( sK2(X0,X1) != X2 | k1_relat_1(X2) != k1_xboole_0 | k1_xboole_0 = X2 ),
% 3.21/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_17]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_326,plain,
% 3.21/1.01      ( k1_relat_1(sK2(X0,X1)) != k1_xboole_0 | k1_xboole_0 = sK2(X0,X1) ),
% 3.21/1.01      inference(unflattening,[status(thm)],[c_325]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_327,plain,
% 3.21/1.01      ( k1_relat_1(sK2(k1_xboole_0,k1_xboole_0)) != k1_xboole_0
% 3.21/1.01      | k1_xboole_0 = sK2(k1_xboole_0,k1_xboole_0) ),
% 3.21/1.01      inference(instantiation,[status(thm)],[c_326]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_755,plain,
% 3.21/1.01      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 3.21/1.01      theory(equality) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_1322,plain,
% 3.21/1.01      ( v1_relat_1(X0) | ~ v1_relat_1(sK2(X1,X2)) | X0 != sK2(X1,X2) ),
% 3.21/1.01      inference(instantiation,[status(thm)],[c_755]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_1323,plain,
% 3.21/1.01      ( X0 != sK2(X1,X2)
% 3.21/1.01      | v1_relat_1(X0) = iProver_top
% 3.21/1.01      | v1_relat_1(sK2(X1,X2)) != iProver_top ),
% 3.21/1.01      inference(predicate_to_equality,[status(thm)],[c_1322]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_1325,plain,
% 3.21/1.01      ( k1_xboole_0 != sK2(k1_xboole_0,k1_xboole_0)
% 3.21/1.01      | v1_relat_1(sK2(k1_xboole_0,k1_xboole_0)) != iProver_top
% 3.21/1.01      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.21/1.01      inference(instantiation,[status(thm)],[c_1323]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_757,plain,
% 3.21/1.01      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 3.21/1.01      theory(equality) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_1332,plain,
% 3.21/1.01      ( v1_funct_1(X0) | ~ v1_funct_1(sK2(X1,X2)) | X0 != sK2(X1,X2) ),
% 3.21/1.01      inference(instantiation,[status(thm)],[c_757]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_1333,plain,
% 3.21/1.01      ( X0 != sK2(X1,X2)
% 3.21/1.01      | v1_funct_1(X0) = iProver_top
% 3.21/1.01      | v1_funct_1(sK2(X1,X2)) != iProver_top ),
% 3.21/1.01      inference(predicate_to_equality,[status(thm)],[c_1332]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_1335,plain,
% 3.21/1.01      ( k1_xboole_0 != sK2(k1_xboole_0,k1_xboole_0)
% 3.21/1.01      | v1_funct_1(sK2(k1_xboole_0,k1_xboole_0)) != iProver_top
% 3.21/1.01      | v1_funct_1(k1_xboole_0) = iProver_top ),
% 3.21/1.01      inference(instantiation,[status(thm)],[c_1333]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_7474,plain,
% 3.21/1.01      ( r1_tarski(k1_relat_1(k1_funct_1(k1_xboole_0,sK0(k1_xboole_0,sK5))),sK5) != iProver_top
% 3.21/1.01      | v1_funct_1(k1_xboole_0) != iProver_top
% 3.21/1.01      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.21/1.01      inference(instantiation,[status(thm)],[c_7342]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_8648,plain,
% 3.21/1.01      ( r1_tarski(k1_relat_1(k1_funct_1(k1_xboole_0,sK0(k1_xboole_0,sK5))),sK5) != iProver_top ),
% 3.21/1.01      inference(global_propositional_subsumption,
% 3.21/1.01                [status(thm)],
% 3.21/1.01                [c_7342,c_51,c_54,c_55,c_327,c_1325,c_1335,c_7474]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_8654,plain,
% 3.21/1.01      ( r1_tarski(X0,sK5) != iProver_top ),
% 3.21/1.01      inference(superposition,[status(thm)],[c_5800,c_8648]) ).
% 3.21/1.01  
% 3.21/1.01  cnf(c_8841,plain,
% 3.21/1.01      ( $false ),
% 3.21/1.01      inference(superposition,[status(thm)],[c_1128,c_8654]) ).
% 3.21/1.01  
% 3.21/1.01  
% 3.21/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.21/1.01  
% 3.21/1.01  ------                               Statistics
% 3.21/1.01  
% 3.21/1.01  ------ General
% 3.21/1.01  
% 3.21/1.01  abstr_ref_over_cycles:                  0
% 3.21/1.01  abstr_ref_under_cycles:                 0
% 3.21/1.01  gc_basic_clause_elim:                   0
% 3.21/1.01  forced_gc_time:                         0
% 3.21/1.01  parsing_time:                           0.015
% 3.21/1.01  unif_index_cands_time:                  0.
% 3.21/1.01  unif_index_add_time:                    0.
% 3.21/1.01  orderings_time:                         0.
% 3.21/1.01  out_proof_time:                         0.011
% 3.21/1.01  total_time:                             0.25
% 3.21/1.01  num_of_symbols:                         47
% 3.21/1.01  num_of_terms:                           8487
% 3.21/1.01  
% 3.21/1.01  ------ Preprocessing
% 3.21/1.01  
% 3.21/1.01  num_of_splits:                          0
% 3.21/1.01  num_of_split_atoms:                     0
% 3.21/1.01  num_of_reused_defs:                     0
% 3.21/1.01  num_eq_ax_congr_red:                    33
% 3.21/1.01  num_of_sem_filtered_clauses:            1
% 3.21/1.01  num_of_subtypes:                        0
% 3.21/1.01  monotx_restored_types:                  0
% 3.21/1.01  sat_num_of_epr_types:                   0
% 3.21/1.01  sat_num_of_non_cyclic_types:            0
% 3.21/1.01  sat_guarded_non_collapsed_types:        0
% 3.21/1.01  num_pure_diseq_elim:                    0
% 3.21/1.01  simp_replaced_by:                       0
% 3.21/1.01  res_preprocessed:                       127
% 3.21/1.01  prep_upred:                             0
% 3.21/1.01  prep_unflattend:                        24
% 3.21/1.01  smt_new_axioms:                         0
% 3.21/1.01  pred_elim_cands:                        4
% 3.21/1.01  pred_elim:                              0
% 3.21/1.01  pred_elim_cl:                           0
% 3.21/1.01  pred_elim_cycles:                       4
% 3.21/1.01  merged_defs:                            0
% 3.21/1.01  merged_defs_ncl:                        0
% 3.21/1.01  bin_hyper_res:                          0
% 3.21/1.01  prep_cycles:                            4
% 3.21/1.01  pred_elim_time:                         0.005
% 3.21/1.01  splitting_time:                         0.
% 3.21/1.01  sem_filter_time:                        0.
% 3.21/1.01  monotx_time:                            0.
% 3.21/1.01  subtype_inf_time:                       0.
% 3.21/1.01  
% 3.21/1.01  ------ Problem properties
% 3.21/1.01  
% 3.21/1.01  clauses:                                27
% 3.21/1.01  conjectures:                            2
% 3.21/1.01  epr:                                    4
% 3.21/1.01  horn:                                   21
% 3.21/1.01  ground:                                 3
% 3.21/1.01  unary:                                  10
% 3.21/1.01  binary:                                 10
% 3.21/1.01  lits:                                   52
% 3.21/1.01  lits_eq:                                25
% 3.21/1.01  fd_pure:                                0
% 3.21/1.01  fd_pseudo:                              0
% 3.21/1.01  fd_cond:                                5
% 3.21/1.01  fd_pseudo_cond:                         3
% 3.21/1.01  ac_symbols:                             0
% 3.21/1.01  
% 3.21/1.01  ------ Propositional Solver
% 3.21/1.01  
% 3.21/1.01  prop_solver_calls:                      30
% 3.21/1.01  prop_fast_solver_calls:                 835
% 3.21/1.01  smt_solver_calls:                       0
% 3.21/1.01  smt_fast_solver_calls:                  0
% 3.21/1.01  prop_num_of_clauses:                    2874
% 3.21/1.01  prop_preprocess_simplified:             8113
% 3.21/1.01  prop_fo_subsumed:                       34
% 3.21/1.01  prop_solver_time:                       0.
% 3.21/1.01  smt_solver_time:                        0.
% 3.21/1.01  smt_fast_solver_time:                   0.
% 3.21/1.01  prop_fast_solver_time:                  0.
% 3.21/1.01  prop_unsat_core_time:                   0.
% 3.21/1.01  
% 3.21/1.01  ------ QBF
% 3.21/1.01  
% 3.21/1.01  qbf_q_res:                              0
% 3.21/1.01  qbf_num_tautologies:                    0
% 3.21/1.01  qbf_prep_cycles:                        0
% 3.21/1.01  
% 3.21/1.01  ------ BMC1
% 3.21/1.01  
% 3.21/1.01  bmc1_current_bound:                     -1
% 3.21/1.01  bmc1_last_solved_bound:                 -1
% 3.21/1.01  bmc1_unsat_core_size:                   -1
% 3.21/1.01  bmc1_unsat_core_parents_size:           -1
% 3.21/1.01  bmc1_merge_next_fun:                    0
% 3.21/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.21/1.01  
% 3.21/1.01  ------ Instantiation
% 3.21/1.01  
% 3.21/1.01  inst_num_of_clauses:                    745
% 3.21/1.01  inst_num_in_passive:                    359
% 3.21/1.01  inst_num_in_active:                     356
% 3.21/1.01  inst_num_in_unprocessed:                30
% 3.21/1.01  inst_num_of_loops:                      440
% 3.21/1.01  inst_num_of_learning_restarts:          0
% 3.21/1.01  inst_num_moves_active_passive:          80
% 3.21/1.01  inst_lit_activity:                      0
% 3.21/1.01  inst_lit_activity_moves:                0
% 3.21/1.01  inst_num_tautologies:                   0
% 3.21/1.01  inst_num_prop_implied:                  0
% 3.21/1.01  inst_num_existing_simplified:           0
% 3.21/1.01  inst_num_eq_res_simplified:             0
% 3.21/1.01  inst_num_child_elim:                    0
% 3.21/1.01  inst_num_of_dismatching_blockings:      491
% 3.21/1.01  inst_num_of_non_proper_insts:           917
% 3.21/1.01  inst_num_of_duplicates:                 0
% 3.21/1.01  inst_inst_num_from_inst_to_res:         0
% 3.21/1.01  inst_dismatching_checking_time:         0.
% 3.21/1.01  
% 3.21/1.01  ------ Resolution
% 3.21/1.01  
% 3.21/1.01  res_num_of_clauses:                     0
% 3.21/1.01  res_num_in_passive:                     0
% 3.21/1.01  res_num_in_active:                      0
% 3.21/1.01  res_num_of_loops:                       131
% 3.21/1.01  res_forward_subset_subsumed:            55
% 3.21/1.01  res_backward_subset_subsumed:           2
% 3.21/1.01  res_forward_subsumed:                   0
% 3.21/1.01  res_backward_subsumed:                  0
% 3.21/1.01  res_forward_subsumption_resolution:     0
% 3.21/1.01  res_backward_subsumption_resolution:    0
% 3.21/1.01  res_clause_to_clause_subsumption:       746
% 3.21/1.01  res_orphan_elimination:                 0
% 3.21/1.01  res_tautology_del:                      36
% 3.21/1.01  res_num_eq_res_simplified:              0
% 3.21/1.01  res_num_sel_changes:                    0
% 3.21/1.01  res_moves_from_active_to_pass:          0
% 3.21/1.01  
% 3.21/1.01  ------ Superposition
% 3.21/1.01  
% 3.21/1.01  sup_time_total:                         0.
% 3.21/1.01  sup_time_generating:                    0.
% 3.21/1.01  sup_time_sim_full:                      0.
% 3.21/1.01  sup_time_sim_immed:                     0.
% 3.21/1.01  
% 3.21/1.01  sup_num_of_clauses:                     132
% 3.21/1.01  sup_num_in_active:                      53
% 3.21/1.01  sup_num_in_passive:                     79
% 3.21/1.01  sup_num_of_loops:                       86
% 3.21/1.01  sup_fw_superposition:                   87
% 3.21/1.01  sup_bw_superposition:                   873
% 3.21/1.01  sup_immediate_simplified:               517
% 3.21/1.01  sup_given_eliminated:                   5
% 3.21/1.01  comparisons_done:                       0
% 3.21/1.01  comparisons_avoided:                    37
% 3.21/1.01  
% 3.21/1.01  ------ Simplifications
% 3.21/1.01  
% 3.21/1.01  
% 3.21/1.01  sim_fw_subset_subsumed:                 375
% 3.21/1.01  sim_bw_subset_subsumed:                 22
% 3.21/1.01  sim_fw_subsumed:                        65
% 3.21/1.01  sim_bw_subsumed:                        27
% 3.21/1.01  sim_fw_subsumption_res:                 11
% 3.21/1.01  sim_bw_subsumption_res:                 1
% 3.21/1.01  sim_tautology_del:                      9
% 3.21/1.01  sim_eq_tautology_del:                   15
% 3.21/1.01  sim_eq_res_simp:                        3
% 3.21/1.01  sim_fw_demodulated:                     16
% 3.21/1.01  sim_bw_demodulated:                     86
% 3.21/1.01  sim_light_normalised:                   29
% 3.21/1.01  sim_joinable_taut:                      0
% 3.21/1.01  sim_joinable_simp:                      0
% 3.21/1.01  sim_ac_normalised:                      0
% 3.21/1.01  sim_smt_subsumption:                    0
% 3.21/1.01  
%------------------------------------------------------------------------------
