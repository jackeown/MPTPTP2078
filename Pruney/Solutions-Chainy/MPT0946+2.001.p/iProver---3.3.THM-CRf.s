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
% DateTime   : Thu Dec  3 11:59:41 EST 2020

% Result     : Theorem 11.36s
% Output     : CNFRefutation 11.36s
% Verified   : 
% Statistics : Number of formulae       :  217 (10696 expanded)
%              Number of clauses        :  143 (3714 expanded)
%              Number of leaves         :   24 (2225 expanded)
%              Depth                    :   43
%              Number of atoms          :  741 (39250 expanded)
%              Number of equality atoms :  363 (11148 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   17 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f77,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_xboole_0(X0,X1)
           => r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_xboole_0(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f21,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f57,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f15,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
     => ( sK4 != X0
        & r4_wellord1(k1_wellord2(X0),k1_wellord2(sK4))
        & v3_ordinal1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( sK3 != X1
          & r4_wellord1(k1_wellord2(sK3),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( sK3 != sK4
    & r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4))
    & v3_ordinal1(sK4)
    & v3_ordinal1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f42,f54,f53])).

fof(f79,plain,(
    v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f80,plain,(
    v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
           => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_wellord1(k1_wellord2(X1),X0) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f82,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f55])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
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

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f50,plain,(
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
    inference(rectify,[],[f49])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK1(X0,X1),sK2(X0,X1))
          | ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) )
        & ( r1_tarski(sK1(X0,X1),sK2(X0,X1))
          | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) )
        & r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK1(X0,X1),sK2(X0,X1))
              | ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) )
            & ( r1_tarski(sK1(X0,X1),sK2(X0,X1))
              | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) )
            & r2_hidden(sK2(X0,X1),X0)
            & r2_hidden(sK1(X0,X1),X0) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f50,f51])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f89,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f68])).

fof(f11,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f81,plain,(
    r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) ),
    inference(cnf_transformation,[],[f55])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r4_wellord1(X1,X0)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( r1_tarski(X1,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK0(X0),X0)
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ( ~ r1_tarski(sK0(X0),X0)
          & r2_hidden(sK0(X0),X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f44,f45])).

fof(f59,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_21,plain,
    ( v2_wellord1(k1_wellord2(X0))
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_697,plain,
    ( v2_wellord1(k1_wellord2(X0)) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2,plain,
    ( r1_ordinal1(X0,X1)
    | r1_ordinal1(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_714,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r1_ordinal1(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_7,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_709,plain,
    ( r1_ordinal1(X0,X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2028,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r1_tarski(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_714,c_709])).

cnf(c_3281,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2028,c_709])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_716,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r2_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3294,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) = iProver_top
    | r2_xboole_0(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3281,c_716])).

cnf(c_4127,plain,
    ( X0 = X1
    | r2_xboole_0(X1,X0) = iProver_top
    | r2_xboole_0(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3294,c_716])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_xboole_0(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_708,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_xboole_0(X0,X1) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v1_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5028,plain,
    ( X0 = X1
    | r2_hidden(X1,X0) = iProver_top
    | r2_xboole_0(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v1_ordinal1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4127,c_708])).

cnf(c_1,plain,
    ( ~ v3_ordinal1(X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_715,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v1_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5438,plain,
    ( X0 = X1
    | r2_hidden(X0,X1) = iProver_top
    | r2_xboole_0(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5028,c_715])).

cnf(c_26,negated_conjecture,
    ( v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_693,plain,
    ( v3_ordinal1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_694,plain,
    ( v3_ordinal1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_22,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_696,plain,
    ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3295,plain,
    ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3281,c_696])).

cnf(c_3522,plain,
    ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3295,c_696])).

cnf(c_4280,plain,
    ( k2_wellord1(k1_wellord2(X0),sK4) = k1_wellord2(sK4)
    | k2_wellord1(k1_wellord2(sK4),X0) = k1_wellord2(X0)
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_694,c_3522])).

cnf(c_4335,plain,
    ( k2_wellord1(k1_wellord2(sK4),sK3) = k1_wellord2(sK3)
    | k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4) ),
    inference(superposition,[status(thm)],[c_693,c_4280])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | k1_wellord1(k1_wellord2(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_222,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | k1_wellord1(k1_wellord2(X1),X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_9])).

cnf(c_692,plain,
    ( k1_wellord1(k1_wellord2(X0),X1) = X1
    | r2_hidden(X1,X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_222])).

cnf(c_5444,plain,
    ( X0 = X1
    | k1_wellord1(k1_wellord2(X0),X1) = X1
    | r2_xboole_0(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5438,c_692])).

cnf(c_16363,plain,
    ( X0 = X1
    | k1_wellord1(k1_wellord2(X1),X0) = X0
    | r2_hidden(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v1_ordinal1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5444,c_708])).

cnf(c_16372,plain,
    ( X0 = X1
    | k1_wellord1(k1_wellord2(X0),X1) = X1
    | r2_hidden(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_16363,c_715])).

cnf(c_16382,plain,
    ( X0 = X1
    | k1_wellord1(k1_wellord2(X0),X1) = X1
    | k1_wellord1(k1_wellord2(X1),X0) = X0
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16372,c_692])).

cnf(c_23801,plain,
    ( k1_wellord1(k1_wellord2(X0),sK4) = sK4
    | k1_wellord1(k1_wellord2(sK4),X0) = X0
    | sK4 = X0
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_694,c_16382])).

cnf(c_24277,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3
    | k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | sK4 = sK3 ),
    inference(superposition,[status(thm)],[c_693,c_23801])).

cnf(c_23,negated_conjecture,
    ( sK3 != sK4 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_255,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_284,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_255])).

cnf(c_256,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1000,plain,
    ( sK4 != X0
    | sK3 != X0
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_256])).

cnf(c_1001,plain,
    ( sK4 != sK3
    | sK3 = sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1000])).

cnf(c_24512,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | k1_wellord1(k1_wellord2(sK4),sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_24277,c_23,c_284,c_1001])).

cnf(c_24513,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3
    | k1_wellord1(k1_wellord2(sK3),sK4) = sK4 ),
    inference(renaming,[status(thm)],[c_24512])).

cnf(c_11,plain,
    ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
    | ~ r2_hidden(X1,k3_relat_1(X0))
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_705,plain,
    ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) != iProver_top
    | r2_hidden(X1,k3_relat_1(X0)) != iProver_top
    | v2_wellord1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_24516,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) != iProver_top
    | r2_hidden(sK3,k3_relat_1(k1_wellord2(sK4))) != iProver_top
    | v2_wellord1(k1_wellord2(sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_24513,c_705])).

cnf(c_18,plain,
    ( ~ v1_relat_1(k1_wellord2(X0))
    | k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_19,plain,
    ( v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_200,plain,
    ( k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_19])).

cnf(c_24517,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) != iProver_top
    | r2_hidden(sK3,sK4) != iProver_top
    | v2_wellord1(k1_wellord2(sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_24516,c_200])).

cnf(c_27,plain,
    ( v3_ordinal1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_28,plain,
    ( v3_ordinal1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_89,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v1_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_91,plain,
    ( v3_ordinal1(sK3) != iProver_top
    | v1_ordinal1(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_89])).

cnf(c_977,plain,
    ( v1_ordinal1(sK4) ),
    inference(resolution,[status(thm)],[c_1,c_25])).

cnf(c_978,plain,
    ( v1_ordinal1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_977])).

cnf(c_1498,plain,
    ( ~ r2_hidden(sK4,X0)
    | ~ v3_ordinal1(X0)
    | k1_wellord1(k1_wellord2(X0),sK4) = sK4 ),
    inference(instantiation,[status(thm)],[c_222])).

cnf(c_1500,plain,
    ( k1_wellord1(k1_wellord2(X0),sK4) = sK4
    | r2_hidden(sK4,X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1498])).

cnf(c_1502,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | r2_hidden(sK4,sK3) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1500])).

cnf(c_2081,plain,
    ( r2_hidden(sK4,X0)
    | ~ r2_xboole_0(sK4,X0)
    | ~ v3_ordinal1(X0)
    | ~ v1_ordinal1(sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2082,plain,
    ( r2_hidden(sK4,X0) = iProver_top
    | r2_xboole_0(sK4,X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v1_ordinal1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2081])).

cnf(c_2084,plain,
    ( r2_hidden(sK4,sK3) = iProver_top
    | r2_xboole_0(sK4,sK3) != iProver_top
    | v3_ordinal1(sK3) != iProver_top
    | v1_ordinal1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2082])).

cnf(c_2247,plain,
    ( v1_relat_1(k1_wellord2(sK4)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2248,plain,
    ( v1_relat_1(k1_wellord2(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2247])).

cnf(c_2145,plain,
    ( r1_ordinal1(X0,X1)
    | r1_tarski(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(resolution,[status(thm)],[c_7,c_2])).

cnf(c_2987,plain,
    ( r1_tarski(X0,X1)
    | r1_tarski(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(resolution,[status(thm)],[c_2145,c_7])).

cnf(c_2465,plain,
    ( ~ r1_tarski(sK4,sK3)
    | r2_xboole_0(sK4,sK3) ),
    inference(resolution,[status(thm)],[c_0,c_23])).

cnf(c_19854,plain,
    ( r1_tarski(sK3,sK4)
    | r2_xboole_0(sK4,sK3)
    | ~ v3_ordinal1(sK4)
    | ~ v3_ordinal1(sK3) ),
    inference(resolution,[status(thm)],[c_2987,c_2465])).

cnf(c_20377,plain,
    ( r1_tarski(sK3,sK4)
    | r2_xboole_0(sK4,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19854,c_26,c_25])).

cnf(c_261,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2468,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | ~ v1_relat_1(X0)
    | v1_relat_1(X1) ),
    inference(resolution,[status(thm)],[c_0,c_261])).

cnf(c_20394,plain,
    ( r2_xboole_0(sK4,sK3)
    | r2_xboole_0(sK3,sK4)
    | v1_relat_1(sK4)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[status(thm)],[c_20377,c_2468])).

cnf(c_9204,plain,
    ( ~ r1_tarski(sK3,sK4)
    | r2_xboole_0(sK3,sK4)
    | sK4 = sK3 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_20399,plain,
    ( r2_xboole_0(sK4,sK3)
    | r2_xboole_0(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20394,c_23,c_284,c_1001,c_9204,c_20377])).

cnf(c_20401,plain,
    ( r2_xboole_0(sK4,sK3) = iProver_top
    | r2_xboole_0(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20399])).

cnf(c_22150,plain,
    ( r2_hidden(X0,sK4)
    | ~ r2_xboole_0(X0,sK4)
    | ~ v3_ordinal1(sK4)
    | ~ v1_ordinal1(X0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_22151,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | r2_xboole_0(X0,sK4) != iProver_top
    | v3_ordinal1(sK4) != iProver_top
    | v1_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22150])).

cnf(c_22153,plain,
    ( r2_hidden(sK3,sK4) = iProver_top
    | r2_xboole_0(sK3,sK4) != iProver_top
    | v3_ordinal1(sK4) != iProver_top
    | v1_ordinal1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_22151])).

cnf(c_25568,plain,
    ( v2_wellord1(k1_wellord2(sK4)) != iProver_top
    | k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24517,c_27,c_28,c_91,c_978,c_1502,c_2084,c_2248,c_20401,c_22153])).

cnf(c_25569,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) != iProver_top
    | v2_wellord1(k1_wellord2(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_25568])).

cnf(c_25575,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
    | k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) != iProver_top
    | v2_wellord1(k1_wellord2(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4335,c_25569])).

cnf(c_39,plain,
    ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_41,plain,
    ( v1_relat_1(k1_wellord2(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_24,negated_conjecture,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_695,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_10,plain,
    ( ~ r4_wellord1(X0,X1)
    | r4_wellord1(X1,X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_706,plain,
    ( r4_wellord1(X0,X1) != iProver_top
    | r4_wellord1(X1,X0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1827,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_695,c_706])).

cnf(c_3521,plain,
    ( X0 = X1
    | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
    | r2_xboole_0(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3295,c_716])).

cnf(c_5064,plain,
    ( X0 = X1
    | k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | r2_hidden(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v1_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3521,c_708])).

cnf(c_6430,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | X0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5064,c_89])).

cnf(c_6431,plain,
    ( X0 = X1
    | k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | r2_hidden(X0,X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_6430])).

cnf(c_6444,plain,
    ( X0 = X1
    | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
    | k1_wellord1(k1_wellord2(X0),X1) = X1
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6431,c_692])).

cnf(c_27747,plain,
    ( k2_wellord1(k1_wellord2(X0),sK3) = k1_wellord2(sK3)
    | k1_wellord1(k1_wellord2(sK3),X0) = X0
    | sK3 = X0
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_693,c_6444])).

cnf(c_29016,plain,
    ( k2_wellord1(k1_wellord2(sK4),sK3) = k1_wellord2(sK3)
    | k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | sK4 = sK3 ),
    inference(superposition,[status(thm)],[c_694,c_27747])).

cnf(c_29328,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | k2_wellord1(k1_wellord2(sK4),sK3) = k1_wellord2(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_29016,c_23,c_284,c_1001])).

cnf(c_29329,plain,
    ( k2_wellord1(k1_wellord2(sK4),sK3) = k1_wellord2(sK3)
    | k1_wellord1(k1_wellord2(sK3),sK4) = sK4 ),
    inference(renaming,[status(thm)],[c_29328])).

cnf(c_29332,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) != iProver_top
    | v2_wellord1(k1_wellord2(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_29329,c_25569])).

cnf(c_40984,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | v2_wellord1(k1_wellord2(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25575,c_41,c_1827,c_2248,c_29332])).

cnf(c_40990,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | v3_ordinal1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_697,c_40984])).

cnf(c_41495,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_40990,c_28])).

cnf(c_41498,plain,
    ( r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK4)) != iProver_top
    | r2_hidden(sK4,k3_relat_1(k1_wellord2(sK3))) != iProver_top
    | v2_wellord1(k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_41495,c_705])).

cnf(c_41499,plain,
    ( r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK4)) != iProver_top
    | r2_hidden(sK4,sK3) != iProver_top
    | v2_wellord1(k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_41498,c_200])).

cnf(c_29,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_33,plain,
    ( v2_wellord1(k1_wellord2(X0)) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_35,plain,
    ( v2_wellord1(k1_wellord2(sK3)) = iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_266,plain,
    ( X0 != X1
    | k1_wellord2(X0) = k1_wellord2(X1) ),
    theory(equality)).

cnf(c_279,plain,
    ( k1_wellord2(sK3) = k1_wellord2(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_266])).

cnf(c_260,plain,
    ( ~ r4_wellord1(X0,X1)
    | r4_wellord1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1020,plain,
    ( r4_wellord1(X0,X1)
    | ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4))
    | X1 != k1_wellord2(sK4)
    | X0 != k1_wellord2(sK3) ),
    inference(instantiation,[status(thm)],[c_260])).

cnf(c_1105,plain,
    ( r4_wellord1(k1_wellord2(sK3),X0)
    | ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4))
    | X0 != k1_wellord2(sK4)
    | k1_wellord2(sK3) != k1_wellord2(sK3) ),
    inference(instantiation,[status(thm)],[c_1020])).

cnf(c_1237,plain,
    ( r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(X0),sK4))
    | ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4))
    | k2_wellord1(k1_wellord2(X0),sK4) != k1_wellord2(sK4)
    | k1_wellord2(sK3) != k1_wellord2(sK3) ),
    inference(instantiation,[status(thm)],[c_1105])).

cnf(c_1239,plain,
    ( k2_wellord1(k1_wellord2(X0),sK4) != k1_wellord2(sK4)
    | k1_wellord2(sK3) != k1_wellord2(sK3)
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(X0),sK4)) = iProver_top
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1237])).

cnf(c_1241,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK4) != k1_wellord2(sK4)
    | k1_wellord2(sK3) != k1_wellord2(sK3)
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK4)) = iProver_top
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1239])).

cnf(c_1238,plain,
    ( ~ r1_tarski(sK4,X0)
    | k2_wellord1(k1_wellord2(X0),sK4) = k1_wellord2(sK4) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1243,plain,
    ( k2_wellord1(k1_wellord2(X0),sK4) = k1_wellord2(sK4)
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1238])).

cnf(c_1245,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
    | r1_tarski(sK4,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1243])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v1_ordinal1(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1467,plain,
    ( ~ r2_hidden(sK4,X0)
    | r1_tarski(sK4,X0)
    | ~ v1_ordinal1(X0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1473,plain,
    ( r2_hidden(sK4,X0) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1467])).

cnf(c_1475,plain,
    ( r2_hidden(sK4,sK3) != iProver_top
    | r1_tarski(sK4,sK3) = iProver_top
    | v1_ordinal1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1473])).

cnf(c_41502,plain,
    ( r2_hidden(sK4,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_41499,c_27,c_29,c_35,c_41,c_91,c_279,c_284,c_1241,c_1245,c_1475])).

cnf(c_41509,plain,
    ( sK4 = sK3
    | r2_xboole_0(sK3,sK4) = iProver_top
    | v3_ordinal1(sK4) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5438,c_41502])).

cnf(c_43148,plain,
    ( r2_xboole_0(sK3,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_41509,c_27,c_29,c_35,c_41,c_91,c_279,c_284,c_978,c_1241,c_1245,c_1475,c_2084,c_20401,c_41499])).

cnf(c_43153,plain,
    ( r2_hidden(sK3,sK4) = iProver_top
    | v3_ordinal1(sK4) != iProver_top
    | v1_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_43148,c_708])).

cnf(c_43491,plain,
    ( r2_hidden(sK3,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_43153,c_27,c_28,c_29,c_35,c_41,c_91,c_279,c_284,c_978,c_1241,c_1245,c_1475,c_2084,c_20401,c_22153,c_41499])).

cnf(c_43507,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3
    | v3_ordinal1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_43491,c_692])).

cnf(c_41507,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3
    | sK4 = sK3
    | v3_ordinal1(sK4) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_16372,c_41502])).

cnf(c_45373,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_43507,c_27,c_28,c_23,c_284,c_1001,c_41507])).

cnf(c_45376,plain,
    ( r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) != iProver_top
    | r2_hidden(sK3,k3_relat_1(k1_wellord2(sK4))) != iProver_top
    | v2_wellord1(k1_wellord2(sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_45373,c_705])).

cnf(c_711,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v1_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_43501,plain,
    ( r1_tarski(sK3,sK4) = iProver_top
    | v1_ordinal1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_43491,c_711])).

cnf(c_20379,plain,
    ( r1_tarski(sK3,sK4) = iProver_top
    | r2_xboole_0(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20377])).

cnf(c_43631,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_43501,c_27,c_29,c_35,c_41,c_91,c_279,c_284,c_978,c_1241,c_1245,c_1475,c_2084,c_20379,c_41499])).

cnf(c_43638,plain,
    ( k2_wellord1(k1_wellord2(sK4),sK3) = k1_wellord2(sK3) ),
    inference(superposition,[status(thm)],[c_43631,c_696])).

cnf(c_45377,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) != iProver_top
    | r2_hidden(sK3,k3_relat_1(k1_wellord2(sK4))) != iProver_top
    | v2_wellord1(k1_wellord2(sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_45376,c_43638])).

cnf(c_45378,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) != iProver_top
    | r2_hidden(sK3,sK4) != iProver_top
    | v2_wellord1(k1_wellord2(sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_45377,c_200])).

cnf(c_45817,plain,
    ( v2_wellord1(k1_wellord2(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_45378,c_27,c_28,c_29,c_35,c_41,c_91,c_279,c_284,c_978,c_1241,c_1245,c_1475,c_1827,c_2084,c_2248,c_20401,c_22153,c_41499])).

cnf(c_45822,plain,
    ( v3_ordinal1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_697,c_45817])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_45822,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:58:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.36/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.36/1.99  
% 11.36/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.36/1.99  
% 11.36/1.99  ------  iProver source info
% 11.36/1.99  
% 11.36/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.36/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.36/1.99  git: non_committed_changes: false
% 11.36/1.99  git: last_make_outside_of_git: false
% 11.36/1.99  
% 11.36/1.99  ------ 
% 11.36/1.99  
% 11.36/1.99  ------ Input Options
% 11.36/1.99  
% 11.36/1.99  --out_options                           all
% 11.36/1.99  --tptp_safe_out                         true
% 11.36/1.99  --problem_path                          ""
% 11.36/1.99  --include_path                          ""
% 11.36/1.99  --clausifier                            res/vclausify_rel
% 11.36/1.99  --clausifier_options                    --mode clausify
% 11.36/1.99  --stdin                                 false
% 11.36/1.99  --stats_out                             sel
% 11.36/1.99  
% 11.36/1.99  ------ General Options
% 11.36/1.99  
% 11.36/1.99  --fof                                   false
% 11.36/1.99  --time_out_real                         604.99
% 11.36/1.99  --time_out_virtual                      -1.
% 11.36/1.99  --symbol_type_check                     false
% 11.36/1.99  --clausify_out                          false
% 11.36/1.99  --sig_cnt_out                           false
% 11.36/1.99  --trig_cnt_out                          false
% 11.36/1.99  --trig_cnt_out_tolerance                1.
% 11.36/1.99  --trig_cnt_out_sk_spl                   false
% 11.36/1.99  --abstr_cl_out                          false
% 11.36/1.99  
% 11.36/1.99  ------ Global Options
% 11.36/1.99  
% 11.36/1.99  --schedule                              none
% 11.36/1.99  --add_important_lit                     false
% 11.36/1.99  --prop_solver_per_cl                    1000
% 11.36/1.99  --min_unsat_core                        false
% 11.36/1.99  --soft_assumptions                      false
% 11.36/1.99  --soft_lemma_size                       3
% 11.36/1.99  --prop_impl_unit_size                   0
% 11.36/1.99  --prop_impl_unit                        []
% 11.36/1.99  --share_sel_clauses                     true
% 11.36/1.99  --reset_solvers                         false
% 11.36/1.99  --bc_imp_inh                            [conj_cone]
% 11.36/1.99  --conj_cone_tolerance                   3.
% 11.36/1.99  --extra_neg_conj                        none
% 11.36/1.99  --large_theory_mode                     true
% 11.36/1.99  --prolific_symb_bound                   200
% 11.36/1.99  --lt_threshold                          2000
% 11.36/1.99  --clause_weak_htbl                      true
% 11.36/1.99  --gc_record_bc_elim                     false
% 11.36/1.99  
% 11.36/1.99  ------ Preprocessing Options
% 11.36/1.99  
% 11.36/1.99  --preprocessing_flag                    true
% 11.36/1.99  --time_out_prep_mult                    0.1
% 11.36/1.99  --splitting_mode                        input
% 11.36/1.99  --splitting_grd                         true
% 11.36/1.99  --splitting_cvd                         false
% 11.36/1.99  --splitting_cvd_svl                     false
% 11.36/1.99  --splitting_nvd                         32
% 11.36/1.99  --sub_typing                            true
% 11.36/1.99  --prep_gs_sim                           false
% 11.36/1.99  --prep_unflatten                        true
% 11.36/1.99  --prep_res_sim                          true
% 11.36/1.99  --prep_upred                            true
% 11.36/1.99  --prep_sem_filter                       exhaustive
% 11.36/1.99  --prep_sem_filter_out                   false
% 11.36/1.99  --pred_elim                             false
% 11.36/1.99  --res_sim_input                         true
% 11.36/1.99  --eq_ax_congr_red                       true
% 11.36/1.99  --pure_diseq_elim                       true
% 11.36/1.99  --brand_transform                       false
% 11.36/1.99  --non_eq_to_eq                          false
% 11.36/1.99  --prep_def_merge                        true
% 11.36/1.99  --prep_def_merge_prop_impl              false
% 11.36/1.99  --prep_def_merge_mbd                    true
% 11.36/1.99  --prep_def_merge_tr_red                 false
% 11.36/1.99  --prep_def_merge_tr_cl                  false
% 11.36/1.99  --smt_preprocessing                     true
% 11.36/1.99  --smt_ac_axioms                         fast
% 11.36/1.99  --preprocessed_out                      false
% 11.36/1.99  --preprocessed_stats                    false
% 11.36/1.99  
% 11.36/1.99  ------ Abstraction refinement Options
% 11.36/1.99  
% 11.36/1.99  --abstr_ref                             []
% 11.36/1.99  --abstr_ref_prep                        false
% 11.36/1.99  --abstr_ref_until_sat                   false
% 11.36/1.99  --abstr_ref_sig_restrict                funpre
% 11.36/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.36/1.99  --abstr_ref_under                       []
% 11.36/1.99  
% 11.36/1.99  ------ SAT Options
% 11.36/1.99  
% 11.36/1.99  --sat_mode                              false
% 11.36/1.99  --sat_fm_restart_options                ""
% 11.36/1.99  --sat_gr_def                            false
% 11.36/1.99  --sat_epr_types                         true
% 11.36/1.99  --sat_non_cyclic_types                  false
% 11.36/1.99  --sat_finite_models                     false
% 11.36/1.99  --sat_fm_lemmas                         false
% 11.36/1.99  --sat_fm_prep                           false
% 11.36/1.99  --sat_fm_uc_incr                        true
% 11.36/1.99  --sat_out_model                         small
% 11.36/1.99  --sat_out_clauses                       false
% 11.36/1.99  
% 11.36/1.99  ------ QBF Options
% 11.36/1.99  
% 11.36/1.99  --qbf_mode                              false
% 11.36/1.99  --qbf_elim_univ                         false
% 11.36/1.99  --qbf_dom_inst                          none
% 11.36/1.99  --qbf_dom_pre_inst                      false
% 11.36/1.99  --qbf_sk_in                             false
% 11.36/1.99  --qbf_pred_elim                         true
% 11.36/1.99  --qbf_split                             512
% 11.36/1.99  
% 11.36/1.99  ------ BMC1 Options
% 11.36/1.99  
% 11.36/1.99  --bmc1_incremental                      false
% 11.36/1.99  --bmc1_axioms                           reachable_all
% 11.36/1.99  --bmc1_min_bound                        0
% 11.36/1.99  --bmc1_max_bound                        -1
% 11.36/1.99  --bmc1_max_bound_default                -1
% 11.36/1.99  --bmc1_symbol_reachability              true
% 11.36/1.99  --bmc1_property_lemmas                  false
% 11.36/1.99  --bmc1_k_induction                      false
% 11.36/1.99  --bmc1_non_equiv_states                 false
% 11.36/1.99  --bmc1_deadlock                         false
% 11.36/1.99  --bmc1_ucm                              false
% 11.36/1.99  --bmc1_add_unsat_core                   none
% 11.36/1.99  --bmc1_unsat_core_children              false
% 11.36/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.36/1.99  --bmc1_out_stat                         full
% 11.36/1.99  --bmc1_ground_init                      false
% 11.36/1.99  --bmc1_pre_inst_next_state              false
% 11.36/1.99  --bmc1_pre_inst_state                   false
% 11.36/1.99  --bmc1_pre_inst_reach_state             false
% 11.36/1.99  --bmc1_out_unsat_core                   false
% 11.36/1.99  --bmc1_aig_witness_out                  false
% 11.36/1.99  --bmc1_verbose                          false
% 11.36/1.99  --bmc1_dump_clauses_tptp                false
% 11.36/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.36/1.99  --bmc1_dump_file                        -
% 11.36/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.36/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.36/1.99  --bmc1_ucm_extend_mode                  1
% 11.36/1.99  --bmc1_ucm_init_mode                    2
% 11.36/1.99  --bmc1_ucm_cone_mode                    none
% 11.36/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.36/1.99  --bmc1_ucm_relax_model                  4
% 11.36/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.36/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.36/1.99  --bmc1_ucm_layered_model                none
% 11.36/1.99  --bmc1_ucm_max_lemma_size               10
% 11.36/1.99  
% 11.36/1.99  ------ AIG Options
% 11.36/1.99  
% 11.36/1.99  --aig_mode                              false
% 11.36/1.99  
% 11.36/1.99  ------ Instantiation Options
% 11.36/1.99  
% 11.36/1.99  --instantiation_flag                    true
% 11.36/1.99  --inst_sos_flag                         false
% 11.36/1.99  --inst_sos_phase                        true
% 11.36/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.36/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.36/1.99  --inst_lit_sel_side                     num_symb
% 11.36/1.99  --inst_solver_per_active                1400
% 11.36/1.99  --inst_solver_calls_frac                1.
% 11.36/1.99  --inst_passive_queue_type               priority_queues
% 11.36/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.36/1.99  --inst_passive_queues_freq              [25;2]
% 11.36/1.99  --inst_dismatching                      true
% 11.36/1.99  --inst_eager_unprocessed_to_passive     true
% 11.36/1.99  --inst_prop_sim_given                   true
% 11.36/1.99  --inst_prop_sim_new                     false
% 11.36/1.99  --inst_subs_new                         false
% 11.36/1.99  --inst_eq_res_simp                      false
% 11.36/1.99  --inst_subs_given                       false
% 11.36/1.99  --inst_orphan_elimination               true
% 11.36/1.99  --inst_learning_loop_flag               true
% 11.36/1.99  --inst_learning_start                   3000
% 11.36/1.99  --inst_learning_factor                  2
% 11.36/1.99  --inst_start_prop_sim_after_learn       3
% 11.36/1.99  --inst_sel_renew                        solver
% 11.36/1.99  --inst_lit_activity_flag                true
% 11.36/1.99  --inst_restr_to_given                   false
% 11.36/1.99  --inst_activity_threshold               500
% 11.36/1.99  --inst_out_proof                        true
% 11.36/1.99  
% 11.36/1.99  ------ Resolution Options
% 11.36/1.99  
% 11.36/1.99  --resolution_flag                       true
% 11.36/1.99  --res_lit_sel                           adaptive
% 11.36/1.99  --res_lit_sel_side                      none
% 11.36/1.99  --res_ordering                          kbo
% 11.36/1.99  --res_to_prop_solver                    active
% 11.36/1.99  --res_prop_simpl_new                    false
% 11.36/1.99  --res_prop_simpl_given                  true
% 11.36/1.99  --res_passive_queue_type                priority_queues
% 11.36/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.36/1.99  --res_passive_queues_freq               [15;5]
% 11.36/1.99  --res_forward_subs                      full
% 11.36/1.99  --res_backward_subs                     full
% 11.36/1.99  --res_forward_subs_resolution           true
% 11.36/1.99  --res_backward_subs_resolution          true
% 11.36/1.99  --res_orphan_elimination                true
% 11.36/1.99  --res_time_limit                        2.
% 11.36/1.99  --res_out_proof                         true
% 11.36/1.99  
% 11.36/1.99  ------ Superposition Options
% 11.36/1.99  
% 11.36/1.99  --superposition_flag                    true
% 11.36/1.99  --sup_passive_queue_type                priority_queues
% 11.36/1.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.36/1.99  --sup_passive_queues_freq               [1;4]
% 11.36/1.99  --demod_completeness_check              fast
% 11.36/1.99  --demod_use_ground                      true
% 11.36/1.99  --sup_to_prop_solver                    passive
% 11.36/1.99  --sup_prop_simpl_new                    true
% 11.36/1.99  --sup_prop_simpl_given                  true
% 11.36/1.99  --sup_fun_splitting                     false
% 11.36/1.99  --sup_smt_interval                      50000
% 11.36/1.99  
% 11.36/1.99  ------ Superposition Simplification Setup
% 11.36/1.99  
% 11.36/1.99  --sup_indices_passive                   []
% 11.36/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.36/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.36/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.36/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.36/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.36/1.99  --sup_full_bw                           [BwDemod]
% 11.36/1.99  --sup_immed_triv                        [TrivRules]
% 11.36/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.36/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.36/1.99  --sup_immed_bw_main                     []
% 11.36/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.36/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.36/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.36/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.36/1.99  
% 11.36/1.99  ------ Combination Options
% 11.36/1.99  
% 11.36/1.99  --comb_res_mult                         3
% 11.36/1.99  --comb_sup_mult                         2
% 11.36/1.99  --comb_inst_mult                        10
% 11.36/1.99  
% 11.36/1.99  ------ Debug Options
% 11.36/1.99  
% 11.36/1.99  --dbg_backtrace                         false
% 11.36/1.99  --dbg_dump_prop_clauses                 false
% 11.36/1.99  --dbg_dump_prop_clauses_file            -
% 11.36/1.99  --dbg_out_stat                          false
% 11.36/1.99  ------ Parsing...
% 11.36/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.36/1.99  
% 11.36/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 11.36/1.99  
% 11.36/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.36/1.99  
% 11.36/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.36/1.99  ------ Proving...
% 11.36/1.99  ------ Problem Properties 
% 11.36/1.99  
% 11.36/1.99  
% 11.36/1.99  clauses                                 27
% 11.36/1.99  conjectures                             4
% 11.36/1.99  EPR                                     12
% 11.36/1.99  Horn                                    21
% 11.36/1.99  unary                                   6
% 11.36/1.99  binary                                  5
% 11.36/1.99  lits                                    76
% 11.36/1.99  lits eq                                 9
% 11.36/1.99  fd_pure                                 0
% 11.36/1.99  fd_pseudo                               0
% 11.36/1.99  fd_cond                                 0
% 11.36/1.99  fd_pseudo_cond                          1
% 11.36/1.99  AC symbols                              0
% 11.36/1.99  
% 11.36/1.99  ------ Input Options Time Limit: Unbounded
% 11.36/1.99  
% 11.36/1.99  
% 11.36/1.99  ------ 
% 11.36/1.99  Current options:
% 11.36/1.99  ------ 
% 11.36/1.99  
% 11.36/1.99  ------ Input Options
% 11.36/1.99  
% 11.36/1.99  --out_options                           all
% 11.36/1.99  --tptp_safe_out                         true
% 11.36/1.99  --problem_path                          ""
% 11.36/1.99  --include_path                          ""
% 11.36/1.99  --clausifier                            res/vclausify_rel
% 11.36/1.99  --clausifier_options                    --mode clausify
% 11.36/1.99  --stdin                                 false
% 11.36/1.99  --stats_out                             sel
% 11.36/1.99  
% 11.36/1.99  ------ General Options
% 11.36/1.99  
% 11.36/1.99  --fof                                   false
% 11.36/1.99  --time_out_real                         604.99
% 11.36/1.99  --time_out_virtual                      -1.
% 11.36/1.99  --symbol_type_check                     false
% 11.36/1.99  --clausify_out                          false
% 11.36/1.99  --sig_cnt_out                           false
% 11.36/1.99  --trig_cnt_out                          false
% 11.36/1.99  --trig_cnt_out_tolerance                1.
% 11.36/1.99  --trig_cnt_out_sk_spl                   false
% 11.36/1.99  --abstr_cl_out                          false
% 11.36/1.99  
% 11.36/1.99  ------ Global Options
% 11.36/1.99  
% 11.36/1.99  --schedule                              none
% 11.36/1.99  --add_important_lit                     false
% 11.36/1.99  --prop_solver_per_cl                    1000
% 11.36/1.99  --min_unsat_core                        false
% 11.36/1.99  --soft_assumptions                      false
% 11.36/1.99  --soft_lemma_size                       3
% 11.36/1.99  --prop_impl_unit_size                   0
% 11.36/1.99  --prop_impl_unit                        []
% 11.36/1.99  --share_sel_clauses                     true
% 11.36/1.99  --reset_solvers                         false
% 11.36/1.99  --bc_imp_inh                            [conj_cone]
% 11.36/1.99  --conj_cone_tolerance                   3.
% 11.36/1.99  --extra_neg_conj                        none
% 11.36/1.99  --large_theory_mode                     true
% 11.36/1.99  --prolific_symb_bound                   200
% 11.36/1.99  --lt_threshold                          2000
% 11.36/1.99  --clause_weak_htbl                      true
% 11.36/1.99  --gc_record_bc_elim                     false
% 11.36/1.99  
% 11.36/1.99  ------ Preprocessing Options
% 11.36/1.99  
% 11.36/1.99  --preprocessing_flag                    true
% 11.36/1.99  --time_out_prep_mult                    0.1
% 11.36/1.99  --splitting_mode                        input
% 11.36/1.99  --splitting_grd                         true
% 11.36/1.99  --splitting_cvd                         false
% 11.36/1.99  --splitting_cvd_svl                     false
% 11.36/1.99  --splitting_nvd                         32
% 11.36/1.99  --sub_typing                            true
% 11.36/1.99  --prep_gs_sim                           false
% 11.36/1.99  --prep_unflatten                        true
% 11.36/1.99  --prep_res_sim                          true
% 11.36/1.99  --prep_upred                            true
% 11.36/1.99  --prep_sem_filter                       exhaustive
% 11.36/1.99  --prep_sem_filter_out                   false
% 11.36/1.99  --pred_elim                             false
% 11.36/1.99  --res_sim_input                         true
% 11.36/1.99  --eq_ax_congr_red                       true
% 11.36/1.99  --pure_diseq_elim                       true
% 11.36/1.99  --brand_transform                       false
% 11.36/1.99  --non_eq_to_eq                          false
% 11.36/1.99  --prep_def_merge                        true
% 11.36/1.99  --prep_def_merge_prop_impl              false
% 11.36/1.99  --prep_def_merge_mbd                    true
% 11.36/1.99  --prep_def_merge_tr_red                 false
% 11.36/1.99  --prep_def_merge_tr_cl                  false
% 11.36/1.99  --smt_preprocessing                     true
% 11.36/1.99  --smt_ac_axioms                         fast
% 11.36/1.99  --preprocessed_out                      false
% 11.36/1.99  --preprocessed_stats                    false
% 11.36/1.99  
% 11.36/1.99  ------ Abstraction refinement Options
% 11.36/1.99  
% 11.36/1.99  --abstr_ref                             []
% 11.36/1.99  --abstr_ref_prep                        false
% 11.36/1.99  --abstr_ref_until_sat                   false
% 11.36/1.99  --abstr_ref_sig_restrict                funpre
% 11.36/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.36/1.99  --abstr_ref_under                       []
% 11.36/1.99  
% 11.36/1.99  ------ SAT Options
% 11.36/1.99  
% 11.36/1.99  --sat_mode                              false
% 11.36/1.99  --sat_fm_restart_options                ""
% 11.36/1.99  --sat_gr_def                            false
% 11.36/1.99  --sat_epr_types                         true
% 11.36/1.99  --sat_non_cyclic_types                  false
% 11.36/1.99  --sat_finite_models                     false
% 11.36/1.99  --sat_fm_lemmas                         false
% 11.36/1.99  --sat_fm_prep                           false
% 11.36/1.99  --sat_fm_uc_incr                        true
% 11.36/1.99  --sat_out_model                         small
% 11.36/1.99  --sat_out_clauses                       false
% 11.36/1.99  
% 11.36/1.99  ------ QBF Options
% 11.36/1.99  
% 11.36/1.99  --qbf_mode                              false
% 11.36/1.99  --qbf_elim_univ                         false
% 11.36/1.99  --qbf_dom_inst                          none
% 11.36/1.99  --qbf_dom_pre_inst                      false
% 11.36/1.99  --qbf_sk_in                             false
% 11.36/1.99  --qbf_pred_elim                         true
% 11.36/1.99  --qbf_split                             512
% 11.36/1.99  
% 11.36/1.99  ------ BMC1 Options
% 11.36/1.99  
% 11.36/1.99  --bmc1_incremental                      false
% 11.36/1.99  --bmc1_axioms                           reachable_all
% 11.36/1.99  --bmc1_min_bound                        0
% 11.36/1.99  --bmc1_max_bound                        -1
% 11.36/1.99  --bmc1_max_bound_default                -1
% 11.36/1.99  --bmc1_symbol_reachability              true
% 11.36/1.99  --bmc1_property_lemmas                  false
% 11.36/1.99  --bmc1_k_induction                      false
% 11.36/1.99  --bmc1_non_equiv_states                 false
% 11.36/1.99  --bmc1_deadlock                         false
% 11.36/1.99  --bmc1_ucm                              false
% 11.36/1.99  --bmc1_add_unsat_core                   none
% 11.36/1.99  --bmc1_unsat_core_children              false
% 11.36/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.36/1.99  --bmc1_out_stat                         full
% 11.36/1.99  --bmc1_ground_init                      false
% 11.36/1.99  --bmc1_pre_inst_next_state              false
% 11.36/1.99  --bmc1_pre_inst_state                   false
% 11.36/1.99  --bmc1_pre_inst_reach_state             false
% 11.36/1.99  --bmc1_out_unsat_core                   false
% 11.36/1.99  --bmc1_aig_witness_out                  false
% 11.36/1.99  --bmc1_verbose                          false
% 11.36/1.99  --bmc1_dump_clauses_tptp                false
% 11.36/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.36/1.99  --bmc1_dump_file                        -
% 11.36/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.36/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.36/1.99  --bmc1_ucm_extend_mode                  1
% 11.36/1.99  --bmc1_ucm_init_mode                    2
% 11.36/1.99  --bmc1_ucm_cone_mode                    none
% 11.36/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.36/1.99  --bmc1_ucm_relax_model                  4
% 11.36/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.36/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.36/1.99  --bmc1_ucm_layered_model                none
% 11.36/1.99  --bmc1_ucm_max_lemma_size               10
% 11.36/1.99  
% 11.36/1.99  ------ AIG Options
% 11.36/1.99  
% 11.36/1.99  --aig_mode                              false
% 11.36/1.99  
% 11.36/1.99  ------ Instantiation Options
% 11.36/1.99  
% 11.36/1.99  --instantiation_flag                    true
% 11.36/1.99  --inst_sos_flag                         false
% 11.36/1.99  --inst_sos_phase                        true
% 11.36/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.36/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.36/1.99  --inst_lit_sel_side                     num_symb
% 11.36/1.99  --inst_solver_per_active                1400
% 11.36/1.99  --inst_solver_calls_frac                1.
% 11.36/1.99  --inst_passive_queue_type               priority_queues
% 11.36/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.36/1.99  --inst_passive_queues_freq              [25;2]
% 11.36/1.99  --inst_dismatching                      true
% 11.36/1.99  --inst_eager_unprocessed_to_passive     true
% 11.36/1.99  --inst_prop_sim_given                   true
% 11.36/1.99  --inst_prop_sim_new                     false
% 11.36/1.99  --inst_subs_new                         false
% 11.36/1.99  --inst_eq_res_simp                      false
% 11.36/1.99  --inst_subs_given                       false
% 11.36/1.99  --inst_orphan_elimination               true
% 11.36/1.99  --inst_learning_loop_flag               true
% 11.36/1.99  --inst_learning_start                   3000
% 11.36/1.99  --inst_learning_factor                  2
% 11.36/1.99  --inst_start_prop_sim_after_learn       3
% 11.36/1.99  --inst_sel_renew                        solver
% 11.36/1.99  --inst_lit_activity_flag                true
% 11.36/1.99  --inst_restr_to_given                   false
% 11.36/1.99  --inst_activity_threshold               500
% 11.36/1.99  --inst_out_proof                        true
% 11.36/1.99  
% 11.36/1.99  ------ Resolution Options
% 11.36/1.99  
% 11.36/1.99  --resolution_flag                       true
% 11.36/1.99  --res_lit_sel                           adaptive
% 11.36/1.99  --res_lit_sel_side                      none
% 11.36/1.99  --res_ordering                          kbo
% 11.36/1.99  --res_to_prop_solver                    active
% 11.36/1.99  --res_prop_simpl_new                    false
% 11.36/1.99  --res_prop_simpl_given                  true
% 11.36/1.99  --res_passive_queue_type                priority_queues
% 11.36/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.36/1.99  --res_passive_queues_freq               [15;5]
% 11.36/1.99  --res_forward_subs                      full
% 11.36/1.99  --res_backward_subs                     full
% 11.36/1.99  --res_forward_subs_resolution           true
% 11.36/1.99  --res_backward_subs_resolution          true
% 11.36/1.99  --res_orphan_elimination                true
% 11.36/1.99  --res_time_limit                        2.
% 11.36/1.99  --res_out_proof                         true
% 11.36/1.99  
% 11.36/1.99  ------ Superposition Options
% 11.36/1.99  
% 11.36/1.99  --superposition_flag                    true
% 11.36/1.99  --sup_passive_queue_type                priority_queues
% 11.36/1.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.36/1.99  --sup_passive_queues_freq               [1;4]
% 11.36/1.99  --demod_completeness_check              fast
% 11.36/1.99  --demod_use_ground                      true
% 11.36/1.99  --sup_to_prop_solver                    passive
% 11.36/1.99  --sup_prop_simpl_new                    true
% 11.36/1.99  --sup_prop_simpl_given                  true
% 11.36/1.99  --sup_fun_splitting                     false
% 11.36/1.99  --sup_smt_interval                      50000
% 11.36/1.99  
% 11.36/1.99  ------ Superposition Simplification Setup
% 11.36/1.99  
% 11.36/1.99  --sup_indices_passive                   []
% 11.36/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.36/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.36/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.36/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.36/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.36/1.99  --sup_full_bw                           [BwDemod]
% 11.36/1.99  --sup_immed_triv                        [TrivRules]
% 11.36/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.36/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.36/1.99  --sup_immed_bw_main                     []
% 11.36/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.36/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.36/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.36/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.36/1.99  
% 11.36/1.99  ------ Combination Options
% 11.36/1.99  
% 11.36/1.99  --comb_res_mult                         3
% 11.36/1.99  --comb_sup_mult                         2
% 11.36/1.99  --comb_inst_mult                        10
% 11.36/1.99  
% 11.36/1.99  ------ Debug Options
% 11.36/1.99  
% 11.36/1.99  --dbg_backtrace                         false
% 11.36/1.99  --dbg_dump_prop_clauses                 false
% 11.36/1.99  --dbg_dump_prop_clauses_file            -
% 11.36/1.99  --dbg_out_stat                          false
% 11.36/1.99  
% 11.36/1.99  
% 11.36/1.99  
% 11.36/1.99  
% 11.36/1.99  ------ Proving...
% 11.36/1.99  
% 11.36/1.99  
% 11.36/1.99  % SZS status Theorem for theBenchmark.p
% 11.36/1.99  
% 11.36/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.36/1.99  
% 11.36/1.99  fof(f13,axiom,(
% 11.36/1.99    ! [X0] : (v3_ordinal1(X0) => v2_wellord1(k1_wellord2(X0)))),
% 11.36/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.36/1.99  
% 11.36/1.99  fof(f39,plain,(
% 11.36/1.99    ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0))),
% 11.36/1.99    inference(ennf_transformation,[],[f13])).
% 11.36/1.99  
% 11.36/1.99  fof(f77,plain,(
% 11.36/1.99    ( ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 11.36/1.99    inference(cnf_transformation,[],[f39])).
% 11.36/1.99  
% 11.36/1.99  fof(f3,axiom,(
% 11.36/1.99    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 11.36/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.36/1.99  
% 11.36/1.99  fof(f22,plain,(
% 11.36/1.99    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 11.36/1.99    inference(ennf_transformation,[],[f3])).
% 11.36/1.99  
% 11.36/1.99  fof(f23,plain,(
% 11.36/1.99    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 11.36/1.99    inference(flattening,[],[f22])).
% 11.36/1.99  
% 11.36/1.99  fof(f58,plain,(
% 11.36/1.99    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 11.36/1.99    inference(cnf_transformation,[],[f23])).
% 11.36/1.99  
% 11.36/1.99  fof(f5,axiom,(
% 11.36/1.99    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 11.36/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.36/1.99  
% 11.36/1.99  fof(f25,plain,(
% 11.36/1.99    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 11.36/1.99    inference(ennf_transformation,[],[f5])).
% 11.36/1.99  
% 11.36/1.99  fof(f26,plain,(
% 11.36/1.99    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 11.36/1.99    inference(flattening,[],[f25])).
% 11.36/1.99  
% 11.36/1.99  fof(f47,plain,(
% 11.36/1.99    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 11.36/1.99    inference(nnf_transformation,[],[f26])).
% 11.36/1.99  
% 11.36/1.99  fof(f62,plain,(
% 11.36/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 11.36/1.99    inference(cnf_transformation,[],[f47])).
% 11.36/1.99  
% 11.36/1.99  fof(f1,axiom,(
% 11.36/1.99    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 11.36/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.36/1.99  
% 11.36/1.99  fof(f17,plain,(
% 11.36/1.99    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 11.36/1.99    inference(unused_predicate_definition_removal,[],[f1])).
% 11.36/1.99  
% 11.36/1.99  fof(f19,plain,(
% 11.36/1.99    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 11.36/1.99    inference(ennf_transformation,[],[f17])).
% 11.36/1.99  
% 11.36/1.99  fof(f20,plain,(
% 11.36/1.99    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 11.36/1.99    inference(flattening,[],[f19])).
% 11.36/1.99  
% 11.36/1.99  fof(f56,plain,(
% 11.36/1.99    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 11.36/1.99    inference(cnf_transformation,[],[f20])).
% 11.36/1.99  
% 11.36/1.99  fof(f6,axiom,(
% 11.36/1.99    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_xboole_0(X0,X1) => r2_hidden(X0,X1))))),
% 11.36/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.36/1.99  
% 11.36/1.99  fof(f27,plain,(
% 11.36/1.99    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 11.36/1.99    inference(ennf_transformation,[],[f6])).
% 11.36/1.99  
% 11.36/1.99  fof(f28,plain,(
% 11.36/1.99    ! [X0] : (! [X1] : (r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 11.36/1.99    inference(flattening,[],[f27])).
% 11.36/1.99  
% 11.36/1.99  fof(f64,plain,(
% 11.36/1.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1) | ~v1_ordinal1(X0)) )),
% 11.36/1.99    inference(cnf_transformation,[],[f28])).
% 11.36/1.99  
% 11.36/1.99  fof(f2,axiom,(
% 11.36/1.99    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 11.36/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.36/1.99  
% 11.36/1.99  fof(f18,plain,(
% 11.36/1.99    ! [X0] : (v3_ordinal1(X0) => v1_ordinal1(X0))),
% 11.36/1.99    inference(pure_predicate_removal,[],[f2])).
% 11.36/1.99  
% 11.36/1.99  fof(f21,plain,(
% 11.36/1.99    ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0))),
% 11.36/1.99    inference(ennf_transformation,[],[f18])).
% 11.36/1.99  
% 11.36/1.99  fof(f57,plain,(
% 11.36/1.99    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 11.36/1.99    inference(cnf_transformation,[],[f21])).
% 11.36/1.99  
% 11.36/1.99  fof(f15,conjecture,(
% 11.36/1.99    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 11.36/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.36/1.99  
% 11.36/1.99  fof(f16,negated_conjecture,(
% 11.36/1.99    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 11.36/1.99    inference(negated_conjecture,[],[f15])).
% 11.36/1.99  
% 11.36/1.99  fof(f41,plain,(
% 11.36/1.99    ? [X0] : (? [X1] : ((X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 11.36/1.99    inference(ennf_transformation,[],[f16])).
% 11.36/1.99  
% 11.36/1.99  fof(f42,plain,(
% 11.36/1.99    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 11.36/1.99    inference(flattening,[],[f41])).
% 11.36/1.99  
% 11.36/1.99  fof(f54,plain,(
% 11.36/1.99    ( ! [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) => (sK4 != X0 & r4_wellord1(k1_wellord2(X0),k1_wellord2(sK4)) & v3_ordinal1(sK4))) )),
% 11.36/1.99    introduced(choice_axiom,[])).
% 11.36/1.99  
% 11.36/1.99  fof(f53,plain,(
% 11.36/1.99    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : (sK3 != X1 & r4_wellord1(k1_wellord2(sK3),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK3))),
% 11.36/1.99    introduced(choice_axiom,[])).
% 11.36/1.99  
% 11.36/1.99  fof(f55,plain,(
% 11.36/1.99    (sK3 != sK4 & r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) & v3_ordinal1(sK4)) & v3_ordinal1(sK3)),
% 11.36/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f42,f54,f53])).
% 11.36/1.99  
% 11.36/1.99  fof(f79,plain,(
% 11.36/1.99    v3_ordinal1(sK3)),
% 11.36/1.99    inference(cnf_transformation,[],[f55])).
% 11.36/1.99  
% 11.36/1.99  fof(f80,plain,(
% 11.36/1.99    v3_ordinal1(sK4)),
% 11.36/1.99    inference(cnf_transformation,[],[f55])).
% 11.36/1.99  
% 11.36/1.99  fof(f14,axiom,(
% 11.36/1.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0))),
% 11.36/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.36/1.99  
% 11.36/1.99  fof(f40,plain,(
% 11.36/1.99    ! [X0,X1] : (k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) | ~r1_tarski(X0,X1))),
% 11.36/1.99    inference(ennf_transformation,[],[f14])).
% 11.36/1.99  
% 11.36/1.99  fof(f78,plain,(
% 11.36/1.99    ( ! [X0,X1] : (k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) | ~r1_tarski(X0,X1)) )),
% 11.36/1.99    inference(cnf_transformation,[],[f40])).
% 11.36/1.99  
% 11.36/1.99  fof(f12,axiom,(
% 11.36/1.99    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => k1_wellord1(k1_wellord2(X1),X0) = X0)))),
% 11.36/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.36/1.99  
% 11.36/1.99  fof(f37,plain,(
% 11.36/1.99    ! [X0] : (! [X1] : ((k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 11.36/1.99    inference(ennf_transformation,[],[f12])).
% 11.36/1.99  
% 11.36/1.99  fof(f38,plain,(
% 11.36/1.99    ! [X0] : (! [X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 11.36/1.99    inference(flattening,[],[f37])).
% 11.36/1.99  
% 11.36/1.99  fof(f76,plain,(
% 11.36/1.99    ( ! [X0,X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 11.36/1.99    inference(cnf_transformation,[],[f38])).
% 11.36/1.99  
% 11.36/1.99  fof(f7,axiom,(
% 11.36/1.99    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 11.36/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.36/1.99  
% 11.36/1.99  fof(f29,plain,(
% 11.36/1.99    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 11.36/1.99    inference(ennf_transformation,[],[f7])).
% 11.36/1.99  
% 11.36/1.99  fof(f30,plain,(
% 11.36/1.99    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 11.36/1.99    inference(flattening,[],[f29])).
% 11.36/1.99  
% 11.36/1.99  fof(f65,plain,(
% 11.36/1.99    ( ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) )),
% 11.36/1.99    inference(cnf_transformation,[],[f30])).
% 11.36/1.99  
% 11.36/1.99  fof(f82,plain,(
% 11.36/1.99    sK3 != sK4),
% 11.36/1.99    inference(cnf_transformation,[],[f55])).
% 11.36/1.99  
% 11.36/1.99  fof(f9,axiom,(
% 11.36/1.99    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 11.36/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.36/1.99  
% 11.36/1.99  fof(f33,plain,(
% 11.36/1.99    ! [X0] : ((! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 11.36/1.99    inference(ennf_transformation,[],[f9])).
% 11.36/1.99  
% 11.36/1.99  fof(f34,plain,(
% 11.36/1.99    ! [X0] : (! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 11.36/1.99    inference(flattening,[],[f33])).
% 11.36/1.99  
% 11.36/1.99  fof(f67,plain,(
% 11.36/1.99    ( ! [X0,X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0)) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 11.36/1.99    inference(cnf_transformation,[],[f34])).
% 11.36/1.99  
% 11.36/1.99  fof(f10,axiom,(
% 11.36/1.99    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 11.36/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.36/1.99  
% 11.36/1.99  fof(f35,plain,(
% 11.36/1.99    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 11.36/1.99    inference(ennf_transformation,[],[f10])).
% 11.36/1.99  
% 11.36/1.99  fof(f36,plain,(
% 11.36/1.99    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 11.36/1.99    inference(flattening,[],[f35])).
% 11.36/1.99  
% 11.36/1.99  fof(f48,plain,(
% 11.36/1.99    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 11.36/1.99    inference(nnf_transformation,[],[f36])).
% 11.36/1.99  
% 11.36/1.99  fof(f49,plain,(
% 11.36/1.99    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 11.36/1.99    inference(flattening,[],[f48])).
% 11.36/1.99  
% 11.36/1.99  fof(f50,plain,(
% 11.36/1.99    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 11.36/1.99    inference(rectify,[],[f49])).
% 11.36/1.99  
% 11.36/1.99  fof(f51,plain,(
% 11.36/1.99    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK1(X0,X1),sK2(X0,X1)) | ~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)) & (r1_tarski(sK1(X0,X1),sK2(X0,X1)) | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)) & r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),X0)))),
% 11.36/1.99    introduced(choice_axiom,[])).
% 11.36/1.99  
% 11.36/1.99  fof(f52,plain,(
% 11.36/1.99    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK1(X0,X1),sK2(X0,X1)) | ~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)) & (r1_tarski(sK1(X0,X1),sK2(X0,X1)) | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)) & r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 11.36/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f50,f51])).
% 11.36/1.99  
% 11.36/1.99  fof(f68,plain,(
% 11.36/1.99    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 11.36/1.99    inference(cnf_transformation,[],[f52])).
% 11.36/1.99  
% 11.36/1.99  fof(f89,plain,(
% 11.36/1.99    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 11.36/1.99    inference(equality_resolution,[],[f68])).
% 11.36/1.99  
% 11.36/1.99  fof(f11,axiom,(
% 11.36/1.99    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 11.36/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.36/1.99  
% 11.36/1.99  fof(f75,plain,(
% 11.36/1.99    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 11.36/1.99    inference(cnf_transformation,[],[f11])).
% 11.36/1.99  
% 11.36/1.99  fof(f81,plain,(
% 11.36/1.99    r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4))),
% 11.36/1.99    inference(cnf_transformation,[],[f55])).
% 11.36/1.99  
% 11.36/1.99  fof(f8,axiom,(
% 11.36/1.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 11.36/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.36/1.99  
% 11.36/1.99  fof(f31,plain,(
% 11.36/1.99    ! [X0] : (! [X1] : ((r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.36/1.99    inference(ennf_transformation,[],[f8])).
% 11.36/1.99  
% 11.36/1.99  fof(f32,plain,(
% 11.36/1.99    ! [X0] : (! [X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.36/1.99    inference(flattening,[],[f31])).
% 11.36/1.99  
% 11.36/1.99  fof(f66,plain,(
% 11.36/1.99    ( ! [X0,X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.36/1.99    inference(cnf_transformation,[],[f32])).
% 11.36/1.99  
% 11.36/1.99  fof(f4,axiom,(
% 11.36/1.99    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 11.36/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.36/1.99  
% 11.36/1.99  fof(f24,plain,(
% 11.36/1.99    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)))),
% 11.36/1.99    inference(ennf_transformation,[],[f4])).
% 11.36/1.99  
% 11.36/1.99  fof(f43,plain,(
% 11.36/1.99    ! [X0] : ((v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0))) & (! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)) | ~v1_ordinal1(X0)))),
% 11.36/1.99    inference(nnf_transformation,[],[f24])).
% 11.36/1.99  
% 11.36/1.99  fof(f44,plain,(
% 11.36/1.99    ! [X0] : ((v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0))) & (! [X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0)) | ~v1_ordinal1(X0)))),
% 11.36/1.99    inference(rectify,[],[f43])).
% 11.36/1.99  
% 11.36/1.99  fof(f45,plain,(
% 11.36/1.99    ! [X0] : (? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0)) => (~r1_tarski(sK0(X0),X0) & r2_hidden(sK0(X0),X0)))),
% 11.36/1.99    introduced(choice_axiom,[])).
% 11.36/1.99  
% 11.36/1.99  fof(f46,plain,(
% 11.36/1.99    ! [X0] : ((v1_ordinal1(X0) | (~r1_tarski(sK0(X0),X0) & r2_hidden(sK0(X0),X0))) & (! [X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0)) | ~v1_ordinal1(X0)))),
% 11.36/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f44,f45])).
% 11.36/1.99  
% 11.36/1.99  fof(f59,plain,(
% 11.36/1.99    ( ! [X2,X0] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0) | ~v1_ordinal1(X0)) )),
% 11.36/1.99    inference(cnf_transformation,[],[f46])).
% 11.36/1.99  
% 11.36/1.99  cnf(c_21,plain,
% 11.36/1.99      ( v2_wellord1(k1_wellord2(X0)) | ~ v3_ordinal1(X0) ),
% 11.36/1.99      inference(cnf_transformation,[],[f77]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_697,plain,
% 11.36/1.99      ( v2_wellord1(k1_wellord2(X0)) = iProver_top
% 11.36/1.99      | v3_ordinal1(X0) != iProver_top ),
% 11.36/1.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_2,plain,
% 11.36/1.99      ( r1_ordinal1(X0,X1)
% 11.36/1.99      | r1_ordinal1(X1,X0)
% 11.36/1.99      | ~ v3_ordinal1(X0)
% 11.36/1.99      | ~ v3_ordinal1(X1) ),
% 11.36/1.99      inference(cnf_transformation,[],[f58]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_714,plain,
% 11.36/1.99      ( r1_ordinal1(X0,X1) = iProver_top
% 11.36/1.99      | r1_ordinal1(X1,X0) = iProver_top
% 11.36/1.99      | v3_ordinal1(X0) != iProver_top
% 11.36/1.99      | v3_ordinal1(X1) != iProver_top ),
% 11.36/1.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_7,plain,
% 11.36/1.99      ( ~ r1_ordinal1(X0,X1)
% 11.36/1.99      | r1_tarski(X0,X1)
% 11.36/1.99      | ~ v3_ordinal1(X0)
% 11.36/1.99      | ~ v3_ordinal1(X1) ),
% 11.36/1.99      inference(cnf_transformation,[],[f62]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_709,plain,
% 11.36/1.99      ( r1_ordinal1(X0,X1) != iProver_top
% 11.36/1.99      | r1_tarski(X0,X1) = iProver_top
% 11.36/1.99      | v3_ordinal1(X0) != iProver_top
% 11.36/1.99      | v3_ordinal1(X1) != iProver_top ),
% 11.36/1.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_2028,plain,
% 11.36/1.99      ( r1_ordinal1(X0,X1) = iProver_top
% 11.36/1.99      | r1_tarski(X1,X0) = iProver_top
% 11.36/1.99      | v3_ordinal1(X0) != iProver_top
% 11.36/1.99      | v3_ordinal1(X1) != iProver_top ),
% 11.36/1.99      inference(superposition,[status(thm)],[c_714,c_709]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_3281,plain,
% 11.36/1.99      ( r1_tarski(X0,X1) = iProver_top
% 11.36/1.99      | r1_tarski(X1,X0) = iProver_top
% 11.36/1.99      | v3_ordinal1(X0) != iProver_top
% 11.36/1.99      | v3_ordinal1(X1) != iProver_top ),
% 11.36/1.99      inference(superposition,[status(thm)],[c_2028,c_709]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_0,plain,
% 11.36/1.99      ( ~ r1_tarski(X0,X1) | r2_xboole_0(X0,X1) | X1 = X0 ),
% 11.36/1.99      inference(cnf_transformation,[],[f56]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_716,plain,
% 11.36/1.99      ( X0 = X1
% 11.36/1.99      | r1_tarski(X1,X0) != iProver_top
% 11.36/1.99      | r2_xboole_0(X1,X0) = iProver_top ),
% 11.36/1.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_3294,plain,
% 11.36/1.99      ( X0 = X1
% 11.36/1.99      | r1_tarski(X1,X0) = iProver_top
% 11.36/1.99      | r2_xboole_0(X0,X1) = iProver_top
% 11.36/1.99      | v3_ordinal1(X1) != iProver_top
% 11.36/1.99      | v3_ordinal1(X0) != iProver_top ),
% 11.36/1.99      inference(superposition,[status(thm)],[c_3281,c_716]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_4127,plain,
% 11.36/1.99      ( X0 = X1
% 11.36/1.99      | r2_xboole_0(X1,X0) = iProver_top
% 11.36/1.99      | r2_xboole_0(X0,X1) = iProver_top
% 11.36/1.99      | v3_ordinal1(X1) != iProver_top
% 11.36/1.99      | v3_ordinal1(X0) != iProver_top ),
% 11.36/1.99      inference(superposition,[status(thm)],[c_3294,c_716]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_8,plain,
% 11.36/1.99      ( r2_hidden(X0,X1)
% 11.36/1.99      | ~ r2_xboole_0(X0,X1)
% 11.36/1.99      | ~ v3_ordinal1(X1)
% 11.36/1.99      | ~ v1_ordinal1(X0) ),
% 11.36/1.99      inference(cnf_transformation,[],[f64]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_708,plain,
% 11.36/1.99      ( r2_hidden(X0,X1) = iProver_top
% 11.36/1.99      | r2_xboole_0(X0,X1) != iProver_top
% 11.36/1.99      | v3_ordinal1(X1) != iProver_top
% 11.36/1.99      | v1_ordinal1(X0) != iProver_top ),
% 11.36/1.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_5028,plain,
% 11.36/1.99      ( X0 = X1
% 11.36/1.99      | r2_hidden(X1,X0) = iProver_top
% 11.36/1.99      | r2_xboole_0(X0,X1) = iProver_top
% 11.36/1.99      | v3_ordinal1(X1) != iProver_top
% 11.36/1.99      | v3_ordinal1(X0) != iProver_top
% 11.36/1.99      | v1_ordinal1(X1) != iProver_top ),
% 11.36/1.99      inference(superposition,[status(thm)],[c_4127,c_708]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_1,plain,
% 11.36/1.99      ( ~ v3_ordinal1(X0) | v1_ordinal1(X0) ),
% 11.36/1.99      inference(cnf_transformation,[],[f57]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_715,plain,
% 11.36/1.99      ( v3_ordinal1(X0) != iProver_top | v1_ordinal1(X0) = iProver_top ),
% 11.36/1.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_5438,plain,
% 11.36/1.99      ( X0 = X1
% 11.36/1.99      | r2_hidden(X0,X1) = iProver_top
% 11.36/1.99      | r2_xboole_0(X1,X0) = iProver_top
% 11.36/1.99      | v3_ordinal1(X1) != iProver_top
% 11.36/1.99      | v3_ordinal1(X0) != iProver_top ),
% 11.36/1.99      inference(forward_subsumption_resolution,
% 11.36/1.99                [status(thm)],
% 11.36/1.99                [c_5028,c_715]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_26,negated_conjecture,
% 11.36/1.99      ( v3_ordinal1(sK3) ),
% 11.36/1.99      inference(cnf_transformation,[],[f79]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_693,plain,
% 11.36/1.99      ( v3_ordinal1(sK3) = iProver_top ),
% 11.36/1.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_25,negated_conjecture,
% 11.36/1.99      ( v3_ordinal1(sK4) ),
% 11.36/1.99      inference(cnf_transformation,[],[f80]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_694,plain,
% 11.36/1.99      ( v3_ordinal1(sK4) = iProver_top ),
% 11.36/1.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_22,plain,
% 11.36/1.99      ( ~ r1_tarski(X0,X1)
% 11.36/1.99      | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ),
% 11.36/1.99      inference(cnf_transformation,[],[f78]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_696,plain,
% 11.36/1.99      ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 11.36/1.99      | r1_tarski(X1,X0) != iProver_top ),
% 11.36/1.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_3295,plain,
% 11.36/1.99      ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 11.36/1.99      | r1_tarski(X0,X1) = iProver_top
% 11.36/1.99      | v3_ordinal1(X0) != iProver_top
% 11.36/1.99      | v3_ordinal1(X1) != iProver_top ),
% 11.36/1.99      inference(superposition,[status(thm)],[c_3281,c_696]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_3522,plain,
% 11.36/1.99      ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 11.36/1.99      | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
% 11.36/1.99      | v3_ordinal1(X1) != iProver_top
% 11.36/1.99      | v3_ordinal1(X0) != iProver_top ),
% 11.36/1.99      inference(superposition,[status(thm)],[c_3295,c_696]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_4280,plain,
% 11.36/1.99      ( k2_wellord1(k1_wellord2(X0),sK4) = k1_wellord2(sK4)
% 11.36/1.99      | k2_wellord1(k1_wellord2(sK4),X0) = k1_wellord2(X0)
% 11.36/1.99      | v3_ordinal1(X0) != iProver_top ),
% 11.36/1.99      inference(superposition,[status(thm)],[c_694,c_3522]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_4335,plain,
% 11.36/1.99      ( k2_wellord1(k1_wellord2(sK4),sK3) = k1_wellord2(sK3)
% 11.36/1.99      | k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4) ),
% 11.36/1.99      inference(superposition,[status(thm)],[c_693,c_4280]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_20,plain,
% 11.36/1.99      ( ~ r2_hidden(X0,X1)
% 11.36/1.99      | ~ v3_ordinal1(X0)
% 11.36/1.99      | ~ v3_ordinal1(X1)
% 11.36/1.99      | k1_wellord1(k1_wellord2(X1),X0) = X0 ),
% 11.36/1.99      inference(cnf_transformation,[],[f76]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_9,plain,
% 11.36/1.99      ( ~ r2_hidden(X0,X1) | ~ v3_ordinal1(X1) | v3_ordinal1(X0) ),
% 11.36/1.99      inference(cnf_transformation,[],[f65]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_222,plain,
% 11.36/1.99      ( ~ r2_hidden(X0,X1)
% 11.36/1.99      | ~ v3_ordinal1(X1)
% 11.36/1.99      | k1_wellord1(k1_wellord2(X1),X0) = X0 ),
% 11.36/1.99      inference(global_propositional_subsumption,
% 11.36/1.99                [status(thm)],
% 11.36/1.99                [c_20,c_9]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_692,plain,
% 11.36/1.99      ( k1_wellord1(k1_wellord2(X0),X1) = X1
% 11.36/1.99      | r2_hidden(X1,X0) != iProver_top
% 11.36/1.99      | v3_ordinal1(X0) != iProver_top ),
% 11.36/1.99      inference(predicate_to_equality,[status(thm)],[c_222]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_5444,plain,
% 11.36/1.99      ( X0 = X1
% 11.36/1.99      | k1_wellord1(k1_wellord2(X0),X1) = X1
% 11.36/1.99      | r2_xboole_0(X0,X1) = iProver_top
% 11.36/1.99      | v3_ordinal1(X1) != iProver_top
% 11.36/1.99      | v3_ordinal1(X0) != iProver_top ),
% 11.36/1.99      inference(superposition,[status(thm)],[c_5438,c_692]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_16363,plain,
% 11.36/1.99      ( X0 = X1
% 11.36/1.99      | k1_wellord1(k1_wellord2(X1),X0) = X0
% 11.36/1.99      | r2_hidden(X1,X0) = iProver_top
% 11.36/1.99      | v3_ordinal1(X1) != iProver_top
% 11.36/1.99      | v3_ordinal1(X0) != iProver_top
% 11.36/1.99      | v1_ordinal1(X1) != iProver_top ),
% 11.36/1.99      inference(superposition,[status(thm)],[c_5444,c_708]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_16372,plain,
% 11.36/1.99      ( X0 = X1
% 11.36/1.99      | k1_wellord1(k1_wellord2(X0),X1) = X1
% 11.36/1.99      | r2_hidden(X0,X1) = iProver_top
% 11.36/1.99      | v3_ordinal1(X1) != iProver_top
% 11.36/1.99      | v3_ordinal1(X0) != iProver_top ),
% 11.36/1.99      inference(forward_subsumption_resolution,
% 11.36/1.99                [status(thm)],
% 11.36/1.99                [c_16363,c_715]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_16382,plain,
% 11.36/1.99      ( X0 = X1
% 11.36/1.99      | k1_wellord1(k1_wellord2(X0),X1) = X1
% 11.36/1.99      | k1_wellord1(k1_wellord2(X1),X0) = X0
% 11.36/1.99      | v3_ordinal1(X1) != iProver_top
% 11.36/1.99      | v3_ordinal1(X0) != iProver_top ),
% 11.36/1.99      inference(superposition,[status(thm)],[c_16372,c_692]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_23801,plain,
% 11.36/1.99      ( k1_wellord1(k1_wellord2(X0),sK4) = sK4
% 11.36/1.99      | k1_wellord1(k1_wellord2(sK4),X0) = X0
% 11.36/1.99      | sK4 = X0
% 11.36/1.99      | v3_ordinal1(X0) != iProver_top ),
% 11.36/1.99      inference(superposition,[status(thm)],[c_694,c_16382]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_24277,plain,
% 11.36/1.99      ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3
% 11.36/1.99      | k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 11.36/1.99      | sK4 = sK3 ),
% 11.36/1.99      inference(superposition,[status(thm)],[c_693,c_23801]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_23,negated_conjecture,
% 11.36/1.99      ( sK3 != sK4 ),
% 11.36/1.99      inference(cnf_transformation,[],[f82]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_255,plain,( X0 = X0 ),theory(equality) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_284,plain,
% 11.36/1.99      ( sK3 = sK3 ),
% 11.36/1.99      inference(instantiation,[status(thm)],[c_255]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_256,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_1000,plain,
% 11.36/1.99      ( sK4 != X0 | sK3 != X0 | sK3 = sK4 ),
% 11.36/1.99      inference(instantiation,[status(thm)],[c_256]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_1001,plain,
% 11.36/1.99      ( sK4 != sK3 | sK3 = sK4 | sK3 != sK3 ),
% 11.36/1.99      inference(instantiation,[status(thm)],[c_1000]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_24512,plain,
% 11.36/1.99      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 11.36/1.99      | k1_wellord1(k1_wellord2(sK4),sK3) = sK3 ),
% 11.36/1.99      inference(global_propositional_subsumption,
% 11.36/1.99                [status(thm)],
% 11.36/1.99                [c_24277,c_23,c_284,c_1001]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_24513,plain,
% 11.36/1.99      ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3
% 11.36/1.99      | k1_wellord1(k1_wellord2(sK3),sK4) = sK4 ),
% 11.36/1.99      inference(renaming,[status(thm)],[c_24512]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_11,plain,
% 11.36/1.99      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
% 11.36/1.99      | ~ r2_hidden(X1,k3_relat_1(X0))
% 11.36/1.99      | ~ v2_wellord1(X0)
% 11.36/1.99      | ~ v1_relat_1(X0) ),
% 11.36/1.99      inference(cnf_transformation,[],[f67]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_705,plain,
% 11.36/1.99      ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) != iProver_top
% 11.36/1.99      | r2_hidden(X1,k3_relat_1(X0)) != iProver_top
% 11.36/1.99      | v2_wellord1(X0) != iProver_top
% 11.36/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.36/1.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_24516,plain,
% 11.36/1.99      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 11.36/1.99      | r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) != iProver_top
% 11.36/1.99      | r2_hidden(sK3,k3_relat_1(k1_wellord2(sK4))) != iProver_top
% 11.36/1.99      | v2_wellord1(k1_wellord2(sK4)) != iProver_top
% 11.36/1.99      | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
% 11.36/1.99      inference(superposition,[status(thm)],[c_24513,c_705]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_18,plain,
% 11.36/1.99      ( ~ v1_relat_1(k1_wellord2(X0))
% 11.36/1.99      | k3_relat_1(k1_wellord2(X0)) = X0 ),
% 11.36/1.99      inference(cnf_transformation,[],[f89]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_19,plain,
% 11.36/1.99      ( v1_relat_1(k1_wellord2(X0)) ),
% 11.36/1.99      inference(cnf_transformation,[],[f75]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_200,plain,
% 11.36/1.99      ( k3_relat_1(k1_wellord2(X0)) = X0 ),
% 11.36/1.99      inference(global_propositional_subsumption,
% 11.36/1.99                [status(thm)],
% 11.36/1.99                [c_18,c_19]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_24517,plain,
% 11.36/1.99      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 11.36/1.99      | r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) != iProver_top
% 11.36/1.99      | r2_hidden(sK3,sK4) != iProver_top
% 11.36/1.99      | v2_wellord1(k1_wellord2(sK4)) != iProver_top
% 11.36/1.99      | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
% 11.36/1.99      inference(demodulation,[status(thm)],[c_24516,c_200]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_27,plain,
% 11.36/1.99      ( v3_ordinal1(sK3) = iProver_top ),
% 11.36/1.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_28,plain,
% 11.36/1.99      ( v3_ordinal1(sK4) = iProver_top ),
% 11.36/1.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_89,plain,
% 11.36/1.99      ( v3_ordinal1(X0) != iProver_top | v1_ordinal1(X0) = iProver_top ),
% 11.36/1.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_91,plain,
% 11.36/1.99      ( v3_ordinal1(sK3) != iProver_top
% 11.36/1.99      | v1_ordinal1(sK3) = iProver_top ),
% 11.36/1.99      inference(instantiation,[status(thm)],[c_89]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_977,plain,
% 11.36/1.99      ( v1_ordinal1(sK4) ),
% 11.36/1.99      inference(resolution,[status(thm)],[c_1,c_25]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_978,plain,
% 11.36/1.99      ( v1_ordinal1(sK4) = iProver_top ),
% 11.36/1.99      inference(predicate_to_equality,[status(thm)],[c_977]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_1498,plain,
% 11.36/1.99      ( ~ r2_hidden(sK4,X0)
% 11.36/1.99      | ~ v3_ordinal1(X0)
% 11.36/1.99      | k1_wellord1(k1_wellord2(X0),sK4) = sK4 ),
% 11.36/1.99      inference(instantiation,[status(thm)],[c_222]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_1500,plain,
% 11.36/1.99      ( k1_wellord1(k1_wellord2(X0),sK4) = sK4
% 11.36/1.99      | r2_hidden(sK4,X0) != iProver_top
% 11.36/1.99      | v3_ordinal1(X0) != iProver_top ),
% 11.36/1.99      inference(predicate_to_equality,[status(thm)],[c_1498]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_1502,plain,
% 11.36/1.99      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 11.36/1.99      | r2_hidden(sK4,sK3) != iProver_top
% 11.36/1.99      | v3_ordinal1(sK3) != iProver_top ),
% 11.36/1.99      inference(instantiation,[status(thm)],[c_1500]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_2081,plain,
% 11.36/1.99      ( r2_hidden(sK4,X0)
% 11.36/1.99      | ~ r2_xboole_0(sK4,X0)
% 11.36/1.99      | ~ v3_ordinal1(X0)
% 11.36/1.99      | ~ v1_ordinal1(sK4) ),
% 11.36/1.99      inference(instantiation,[status(thm)],[c_8]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_2082,plain,
% 11.36/1.99      ( r2_hidden(sK4,X0) = iProver_top
% 11.36/1.99      | r2_xboole_0(sK4,X0) != iProver_top
% 11.36/1.99      | v3_ordinal1(X0) != iProver_top
% 11.36/1.99      | v1_ordinal1(sK4) != iProver_top ),
% 11.36/1.99      inference(predicate_to_equality,[status(thm)],[c_2081]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_2084,plain,
% 11.36/1.99      ( r2_hidden(sK4,sK3) = iProver_top
% 11.36/1.99      | r2_xboole_0(sK4,sK3) != iProver_top
% 11.36/1.99      | v3_ordinal1(sK3) != iProver_top
% 11.36/1.99      | v1_ordinal1(sK4) != iProver_top ),
% 11.36/1.99      inference(instantiation,[status(thm)],[c_2082]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_2247,plain,
% 11.36/1.99      ( v1_relat_1(k1_wellord2(sK4)) ),
% 11.36/1.99      inference(instantiation,[status(thm)],[c_19]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_2248,plain,
% 11.36/1.99      ( v1_relat_1(k1_wellord2(sK4)) = iProver_top ),
% 11.36/1.99      inference(predicate_to_equality,[status(thm)],[c_2247]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_2145,plain,
% 11.36/1.99      ( r1_ordinal1(X0,X1)
% 11.36/1.99      | r1_tarski(X1,X0)
% 11.36/1.99      | ~ v3_ordinal1(X0)
% 11.36/1.99      | ~ v3_ordinal1(X1) ),
% 11.36/1.99      inference(resolution,[status(thm)],[c_7,c_2]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_2987,plain,
% 11.36/1.99      ( r1_tarski(X0,X1)
% 11.36/1.99      | r1_tarski(X1,X0)
% 11.36/1.99      | ~ v3_ordinal1(X0)
% 11.36/1.99      | ~ v3_ordinal1(X1) ),
% 11.36/1.99      inference(resolution,[status(thm)],[c_2145,c_7]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_2465,plain,
% 11.36/1.99      ( ~ r1_tarski(sK4,sK3) | r2_xboole_0(sK4,sK3) ),
% 11.36/1.99      inference(resolution,[status(thm)],[c_0,c_23]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_19854,plain,
% 11.36/1.99      ( r1_tarski(sK3,sK4)
% 11.36/1.99      | r2_xboole_0(sK4,sK3)
% 11.36/1.99      | ~ v3_ordinal1(sK4)
% 11.36/1.99      | ~ v3_ordinal1(sK3) ),
% 11.36/1.99      inference(resolution,[status(thm)],[c_2987,c_2465]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_20377,plain,
% 11.36/1.99      ( r1_tarski(sK3,sK4) | r2_xboole_0(sK4,sK3) ),
% 11.36/1.99      inference(global_propositional_subsumption,
% 11.36/1.99                [status(thm)],
% 11.36/1.99                [c_19854,c_26,c_25]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_261,plain,
% 11.36/1.99      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 11.36/1.99      theory(equality) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_2468,plain,
% 11.36/1.99      ( ~ r1_tarski(X0,X1)
% 11.36/1.99      | r2_xboole_0(X0,X1)
% 11.36/1.99      | ~ v1_relat_1(X0)
% 11.36/1.99      | v1_relat_1(X1) ),
% 11.36/1.99      inference(resolution,[status(thm)],[c_0,c_261]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_20394,plain,
% 11.36/1.99      ( r2_xboole_0(sK4,sK3)
% 11.36/1.99      | r2_xboole_0(sK3,sK4)
% 11.36/1.99      | v1_relat_1(sK4)
% 11.36/1.99      | ~ v1_relat_1(sK3) ),
% 11.36/1.99      inference(resolution,[status(thm)],[c_20377,c_2468]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_9204,plain,
% 11.36/1.99      ( ~ r1_tarski(sK3,sK4) | r2_xboole_0(sK3,sK4) | sK4 = sK3 ),
% 11.36/1.99      inference(instantiation,[status(thm)],[c_0]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_20399,plain,
% 11.36/1.99      ( r2_xboole_0(sK4,sK3) | r2_xboole_0(sK3,sK4) ),
% 11.36/1.99      inference(global_propositional_subsumption,
% 11.36/1.99                [status(thm)],
% 11.36/1.99                [c_20394,c_23,c_284,c_1001,c_9204,c_20377]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_20401,plain,
% 11.36/1.99      ( r2_xboole_0(sK4,sK3) = iProver_top
% 11.36/1.99      | r2_xboole_0(sK3,sK4) = iProver_top ),
% 11.36/1.99      inference(predicate_to_equality,[status(thm)],[c_20399]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_22150,plain,
% 11.36/1.99      ( r2_hidden(X0,sK4)
% 11.36/1.99      | ~ r2_xboole_0(X0,sK4)
% 11.36/1.99      | ~ v3_ordinal1(sK4)
% 11.36/1.99      | ~ v1_ordinal1(X0) ),
% 11.36/1.99      inference(instantiation,[status(thm)],[c_8]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_22151,plain,
% 11.36/1.99      ( r2_hidden(X0,sK4) = iProver_top
% 11.36/1.99      | r2_xboole_0(X0,sK4) != iProver_top
% 11.36/1.99      | v3_ordinal1(sK4) != iProver_top
% 11.36/1.99      | v1_ordinal1(X0) != iProver_top ),
% 11.36/1.99      inference(predicate_to_equality,[status(thm)],[c_22150]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_22153,plain,
% 11.36/1.99      ( r2_hidden(sK3,sK4) = iProver_top
% 11.36/1.99      | r2_xboole_0(sK3,sK4) != iProver_top
% 11.36/1.99      | v3_ordinal1(sK4) != iProver_top
% 11.36/1.99      | v1_ordinal1(sK3) != iProver_top ),
% 11.36/1.99      inference(instantiation,[status(thm)],[c_22151]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_25568,plain,
% 11.36/1.99      ( v2_wellord1(k1_wellord2(sK4)) != iProver_top
% 11.36/1.99      | k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 11.36/1.99      | r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) != iProver_top ),
% 11.36/1.99      inference(global_propositional_subsumption,
% 11.36/1.99                [status(thm)],
% 11.36/1.99                [c_24517,c_27,c_28,c_91,c_978,c_1502,c_2084,c_2248,
% 11.36/1.99                 c_20401,c_22153]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_25569,plain,
% 11.36/1.99      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 11.36/1.99      | r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) != iProver_top
% 11.36/1.99      | v2_wellord1(k1_wellord2(sK4)) != iProver_top ),
% 11.36/1.99      inference(renaming,[status(thm)],[c_25568]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_25575,plain,
% 11.36/1.99      ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
% 11.36/1.99      | k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 11.36/1.99      | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) != iProver_top
% 11.36/1.99      | v2_wellord1(k1_wellord2(sK4)) != iProver_top ),
% 11.36/1.99      inference(superposition,[status(thm)],[c_4335,c_25569]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_39,plain,
% 11.36/1.99      ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
% 11.36/1.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_41,plain,
% 11.36/1.99      ( v1_relat_1(k1_wellord2(sK3)) = iProver_top ),
% 11.36/1.99      inference(instantiation,[status(thm)],[c_39]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_24,negated_conjecture,
% 11.36/1.99      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) ),
% 11.36/1.99      inference(cnf_transformation,[],[f81]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_695,plain,
% 11.36/1.99      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) = iProver_top ),
% 11.36/1.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_10,plain,
% 11.36/1.99      ( ~ r4_wellord1(X0,X1)
% 11.36/1.99      | r4_wellord1(X1,X0)
% 11.36/1.99      | ~ v1_relat_1(X1)
% 11.36/1.99      | ~ v1_relat_1(X0) ),
% 11.36/1.99      inference(cnf_transformation,[],[f66]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_706,plain,
% 11.36/1.99      ( r4_wellord1(X0,X1) != iProver_top
% 11.36/1.99      | r4_wellord1(X1,X0) = iProver_top
% 11.36/1.99      | v1_relat_1(X0) != iProver_top
% 11.36/1.99      | v1_relat_1(X1) != iProver_top ),
% 11.36/1.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_1827,plain,
% 11.36/1.99      ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
% 11.36/1.99      | v1_relat_1(k1_wellord2(sK4)) != iProver_top
% 11.36/1.99      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 11.36/1.99      inference(superposition,[status(thm)],[c_695,c_706]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_3521,plain,
% 11.36/1.99      ( X0 = X1
% 11.36/1.99      | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
% 11.36/1.99      | r2_xboole_0(X1,X0) = iProver_top
% 11.36/1.99      | v3_ordinal1(X1) != iProver_top
% 11.36/1.99      | v3_ordinal1(X0) != iProver_top ),
% 11.36/1.99      inference(superposition,[status(thm)],[c_3295,c_716]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_5064,plain,
% 11.36/1.99      ( X0 = X1
% 11.36/1.99      | k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 11.36/1.99      | r2_hidden(X0,X1) = iProver_top
% 11.36/1.99      | v3_ordinal1(X1) != iProver_top
% 11.36/1.99      | v3_ordinal1(X0) != iProver_top
% 11.36/1.99      | v1_ordinal1(X0) != iProver_top ),
% 11.36/1.99      inference(superposition,[status(thm)],[c_3521,c_708]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_6430,plain,
% 11.36/1.99      ( v3_ordinal1(X0) != iProver_top
% 11.36/1.99      | v3_ordinal1(X1) != iProver_top
% 11.36/1.99      | r2_hidden(X0,X1) = iProver_top
% 11.36/1.99      | k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 11.36/1.99      | X0 = X1 ),
% 11.36/1.99      inference(global_propositional_subsumption,
% 11.36/1.99                [status(thm)],
% 11.36/1.99                [c_5064,c_89]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_6431,plain,
% 11.36/1.99      ( X0 = X1
% 11.36/1.99      | k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 11.36/1.99      | r2_hidden(X0,X1) = iProver_top
% 11.36/1.99      | v3_ordinal1(X0) != iProver_top
% 11.36/1.99      | v3_ordinal1(X1) != iProver_top ),
% 11.36/1.99      inference(renaming,[status(thm)],[c_6430]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_6444,plain,
% 11.36/1.99      ( X0 = X1
% 11.36/1.99      | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
% 11.36/1.99      | k1_wellord1(k1_wellord2(X0),X1) = X1
% 11.36/1.99      | v3_ordinal1(X1) != iProver_top
% 11.36/1.99      | v3_ordinal1(X0) != iProver_top ),
% 11.36/1.99      inference(superposition,[status(thm)],[c_6431,c_692]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_27747,plain,
% 11.36/1.99      ( k2_wellord1(k1_wellord2(X0),sK3) = k1_wellord2(sK3)
% 11.36/1.99      | k1_wellord1(k1_wellord2(sK3),X0) = X0
% 11.36/1.99      | sK3 = X0
% 11.36/1.99      | v3_ordinal1(X0) != iProver_top ),
% 11.36/1.99      inference(superposition,[status(thm)],[c_693,c_6444]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_29016,plain,
% 11.36/1.99      ( k2_wellord1(k1_wellord2(sK4),sK3) = k1_wellord2(sK3)
% 11.36/1.99      | k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 11.36/1.99      | sK4 = sK3 ),
% 11.36/1.99      inference(superposition,[status(thm)],[c_694,c_27747]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_29328,plain,
% 11.36/1.99      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 11.36/1.99      | k2_wellord1(k1_wellord2(sK4),sK3) = k1_wellord2(sK3) ),
% 11.36/1.99      inference(global_propositional_subsumption,
% 11.36/1.99                [status(thm)],
% 11.36/1.99                [c_29016,c_23,c_284,c_1001]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_29329,plain,
% 11.36/1.99      ( k2_wellord1(k1_wellord2(sK4),sK3) = k1_wellord2(sK3)
% 11.36/1.99      | k1_wellord1(k1_wellord2(sK3),sK4) = sK4 ),
% 11.36/1.99      inference(renaming,[status(thm)],[c_29328]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_29332,plain,
% 11.36/1.99      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 11.36/1.99      | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) != iProver_top
% 11.36/1.99      | v2_wellord1(k1_wellord2(sK4)) != iProver_top ),
% 11.36/1.99      inference(superposition,[status(thm)],[c_29329,c_25569]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_40984,plain,
% 11.36/1.99      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 11.36/1.99      | v2_wellord1(k1_wellord2(sK4)) != iProver_top ),
% 11.36/1.99      inference(global_propositional_subsumption,
% 11.36/1.99                [status(thm)],
% 11.36/1.99                [c_25575,c_41,c_1827,c_2248,c_29332]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_40990,plain,
% 11.36/1.99      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 11.36/1.99      | v3_ordinal1(sK4) != iProver_top ),
% 11.36/1.99      inference(superposition,[status(thm)],[c_697,c_40984]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_41495,plain,
% 11.36/1.99      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4 ),
% 11.36/1.99      inference(global_propositional_subsumption,
% 11.36/1.99                [status(thm)],
% 11.36/1.99                [c_40990,c_28]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_41498,plain,
% 11.36/1.99      ( r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK4)) != iProver_top
% 11.36/1.99      | r2_hidden(sK4,k3_relat_1(k1_wellord2(sK3))) != iProver_top
% 11.36/1.99      | v2_wellord1(k1_wellord2(sK3)) != iProver_top
% 11.36/1.99      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 11.36/1.99      inference(superposition,[status(thm)],[c_41495,c_705]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_41499,plain,
% 11.36/1.99      ( r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK4)) != iProver_top
% 11.36/1.99      | r2_hidden(sK4,sK3) != iProver_top
% 11.36/1.99      | v2_wellord1(k1_wellord2(sK3)) != iProver_top
% 11.36/1.99      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 11.36/1.99      inference(demodulation,[status(thm)],[c_41498,c_200]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_29,plain,
% 11.36/1.99      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) = iProver_top ),
% 11.36/1.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_33,plain,
% 11.36/1.99      ( v2_wellord1(k1_wellord2(X0)) = iProver_top
% 11.36/1.99      | v3_ordinal1(X0) != iProver_top ),
% 11.36/1.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_35,plain,
% 11.36/1.99      ( v2_wellord1(k1_wellord2(sK3)) = iProver_top
% 11.36/1.99      | v3_ordinal1(sK3) != iProver_top ),
% 11.36/1.99      inference(instantiation,[status(thm)],[c_33]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_266,plain,
% 11.36/1.99      ( X0 != X1 | k1_wellord2(X0) = k1_wellord2(X1) ),
% 11.36/1.99      theory(equality) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_279,plain,
% 11.36/1.99      ( k1_wellord2(sK3) = k1_wellord2(sK3) | sK3 != sK3 ),
% 11.36/1.99      inference(instantiation,[status(thm)],[c_266]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_260,plain,
% 11.36/1.99      ( ~ r4_wellord1(X0,X1) | r4_wellord1(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.36/1.99      theory(equality) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_1020,plain,
% 11.36/1.99      ( r4_wellord1(X0,X1)
% 11.36/1.99      | ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4))
% 11.36/1.99      | X1 != k1_wellord2(sK4)
% 11.36/1.99      | X0 != k1_wellord2(sK3) ),
% 11.36/1.99      inference(instantiation,[status(thm)],[c_260]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_1105,plain,
% 11.36/1.99      ( r4_wellord1(k1_wellord2(sK3),X0)
% 11.36/1.99      | ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4))
% 11.36/1.99      | X0 != k1_wellord2(sK4)
% 11.36/1.99      | k1_wellord2(sK3) != k1_wellord2(sK3) ),
% 11.36/1.99      inference(instantiation,[status(thm)],[c_1020]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_1237,plain,
% 11.36/1.99      ( r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(X0),sK4))
% 11.36/1.99      | ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4))
% 11.36/1.99      | k2_wellord1(k1_wellord2(X0),sK4) != k1_wellord2(sK4)
% 11.36/1.99      | k1_wellord2(sK3) != k1_wellord2(sK3) ),
% 11.36/1.99      inference(instantiation,[status(thm)],[c_1105]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_1239,plain,
% 11.36/1.99      ( k2_wellord1(k1_wellord2(X0),sK4) != k1_wellord2(sK4)
% 11.36/1.99      | k1_wellord2(sK3) != k1_wellord2(sK3)
% 11.36/1.99      | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(X0),sK4)) = iProver_top
% 11.36/1.99      | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) != iProver_top ),
% 11.36/1.99      inference(predicate_to_equality,[status(thm)],[c_1237]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_1241,plain,
% 11.36/1.99      ( k2_wellord1(k1_wellord2(sK3),sK4) != k1_wellord2(sK4)
% 11.36/1.99      | k1_wellord2(sK3) != k1_wellord2(sK3)
% 11.36/1.99      | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK4)) = iProver_top
% 11.36/1.99      | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) != iProver_top ),
% 11.36/1.99      inference(instantiation,[status(thm)],[c_1239]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_1238,plain,
% 11.36/1.99      ( ~ r1_tarski(sK4,X0)
% 11.36/1.99      | k2_wellord1(k1_wellord2(X0),sK4) = k1_wellord2(sK4) ),
% 11.36/1.99      inference(instantiation,[status(thm)],[c_22]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_1243,plain,
% 11.36/1.99      ( k2_wellord1(k1_wellord2(X0),sK4) = k1_wellord2(sK4)
% 11.36/1.99      | r1_tarski(sK4,X0) != iProver_top ),
% 11.36/1.99      inference(predicate_to_equality,[status(thm)],[c_1238]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_1245,plain,
% 11.36/1.99      ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
% 11.36/1.99      | r1_tarski(sK4,sK3) != iProver_top ),
% 11.36/1.99      inference(instantiation,[status(thm)],[c_1243]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_5,plain,
% 11.36/1.99      ( ~ r2_hidden(X0,X1) | r1_tarski(X0,X1) | ~ v1_ordinal1(X1) ),
% 11.36/1.99      inference(cnf_transformation,[],[f59]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_1467,plain,
% 11.36/1.99      ( ~ r2_hidden(sK4,X0) | r1_tarski(sK4,X0) | ~ v1_ordinal1(X0) ),
% 11.36/1.99      inference(instantiation,[status(thm)],[c_5]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_1473,plain,
% 11.36/1.99      ( r2_hidden(sK4,X0) != iProver_top
% 11.36/1.99      | r1_tarski(sK4,X0) = iProver_top
% 11.36/1.99      | v1_ordinal1(X0) != iProver_top ),
% 11.36/1.99      inference(predicate_to_equality,[status(thm)],[c_1467]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_1475,plain,
% 11.36/1.99      ( r2_hidden(sK4,sK3) != iProver_top
% 11.36/1.99      | r1_tarski(sK4,sK3) = iProver_top
% 11.36/1.99      | v1_ordinal1(sK3) != iProver_top ),
% 11.36/1.99      inference(instantiation,[status(thm)],[c_1473]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_41502,plain,
% 11.36/1.99      ( r2_hidden(sK4,sK3) != iProver_top ),
% 11.36/1.99      inference(global_propositional_subsumption,
% 11.36/1.99                [status(thm)],
% 11.36/1.99                [c_41499,c_27,c_29,c_35,c_41,c_91,c_279,c_284,c_1241,
% 11.36/1.99                 c_1245,c_1475]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_41509,plain,
% 11.36/1.99      ( sK4 = sK3
% 11.36/1.99      | r2_xboole_0(sK3,sK4) = iProver_top
% 11.36/1.99      | v3_ordinal1(sK4) != iProver_top
% 11.36/1.99      | v3_ordinal1(sK3) != iProver_top ),
% 11.36/1.99      inference(superposition,[status(thm)],[c_5438,c_41502]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_43148,plain,
% 11.36/1.99      ( r2_xboole_0(sK3,sK4) = iProver_top ),
% 11.36/1.99      inference(global_propositional_subsumption,
% 11.36/1.99                [status(thm)],
% 11.36/1.99                [c_41509,c_27,c_29,c_35,c_41,c_91,c_279,c_284,c_978,
% 11.36/1.99                 c_1241,c_1245,c_1475,c_2084,c_20401,c_41499]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_43153,plain,
% 11.36/1.99      ( r2_hidden(sK3,sK4) = iProver_top
% 11.36/1.99      | v3_ordinal1(sK4) != iProver_top
% 11.36/1.99      | v1_ordinal1(sK3) != iProver_top ),
% 11.36/1.99      inference(superposition,[status(thm)],[c_43148,c_708]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_43491,plain,
% 11.36/1.99      ( r2_hidden(sK3,sK4) = iProver_top ),
% 11.36/1.99      inference(global_propositional_subsumption,
% 11.36/1.99                [status(thm)],
% 11.36/1.99                [c_43153,c_27,c_28,c_29,c_35,c_41,c_91,c_279,c_284,c_978,
% 11.36/1.99                 c_1241,c_1245,c_1475,c_2084,c_20401,c_22153,c_41499]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_43507,plain,
% 11.36/1.99      ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3
% 11.36/1.99      | v3_ordinal1(sK4) != iProver_top ),
% 11.36/1.99      inference(superposition,[status(thm)],[c_43491,c_692]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_41507,plain,
% 11.36/1.99      ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3
% 11.36/1.99      | sK4 = sK3
% 11.36/1.99      | v3_ordinal1(sK4) != iProver_top
% 11.36/1.99      | v3_ordinal1(sK3) != iProver_top ),
% 11.36/1.99      inference(superposition,[status(thm)],[c_16372,c_41502]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_45373,plain,
% 11.36/1.99      ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3 ),
% 11.36/1.99      inference(global_propositional_subsumption,
% 11.36/1.99                [status(thm)],
% 11.36/1.99                [c_43507,c_27,c_28,c_23,c_284,c_1001,c_41507]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_45376,plain,
% 11.36/1.99      ( r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) != iProver_top
% 11.36/1.99      | r2_hidden(sK3,k3_relat_1(k1_wellord2(sK4))) != iProver_top
% 11.36/1.99      | v2_wellord1(k1_wellord2(sK4)) != iProver_top
% 11.36/1.99      | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
% 11.36/1.99      inference(superposition,[status(thm)],[c_45373,c_705]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_711,plain,
% 11.36/1.99      ( r2_hidden(X0,X1) != iProver_top
% 11.36/1.99      | r1_tarski(X0,X1) = iProver_top
% 11.36/1.99      | v1_ordinal1(X1) != iProver_top ),
% 11.36/1.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_43501,plain,
% 11.36/1.99      ( r1_tarski(sK3,sK4) = iProver_top
% 11.36/1.99      | v1_ordinal1(sK4) != iProver_top ),
% 11.36/1.99      inference(superposition,[status(thm)],[c_43491,c_711]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_20379,plain,
% 11.36/1.99      ( r1_tarski(sK3,sK4) = iProver_top
% 11.36/1.99      | r2_xboole_0(sK4,sK3) = iProver_top ),
% 11.36/1.99      inference(predicate_to_equality,[status(thm)],[c_20377]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_43631,plain,
% 11.36/1.99      ( r1_tarski(sK3,sK4) = iProver_top ),
% 11.36/1.99      inference(global_propositional_subsumption,
% 11.36/1.99                [status(thm)],
% 11.36/1.99                [c_43501,c_27,c_29,c_35,c_41,c_91,c_279,c_284,c_978,
% 11.36/1.99                 c_1241,c_1245,c_1475,c_2084,c_20379,c_41499]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_43638,plain,
% 11.36/1.99      ( k2_wellord1(k1_wellord2(sK4),sK3) = k1_wellord2(sK3) ),
% 11.36/1.99      inference(superposition,[status(thm)],[c_43631,c_696]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_45377,plain,
% 11.36/1.99      ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) != iProver_top
% 11.36/1.99      | r2_hidden(sK3,k3_relat_1(k1_wellord2(sK4))) != iProver_top
% 11.36/1.99      | v2_wellord1(k1_wellord2(sK4)) != iProver_top
% 11.36/1.99      | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
% 11.36/1.99      inference(light_normalisation,[status(thm)],[c_45376,c_43638]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_45378,plain,
% 11.36/1.99      ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) != iProver_top
% 11.36/1.99      | r2_hidden(sK3,sK4) != iProver_top
% 11.36/1.99      | v2_wellord1(k1_wellord2(sK4)) != iProver_top
% 11.36/1.99      | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
% 11.36/1.99      inference(demodulation,[status(thm)],[c_45377,c_200]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_45817,plain,
% 11.36/1.99      ( v2_wellord1(k1_wellord2(sK4)) != iProver_top ),
% 11.36/1.99      inference(global_propositional_subsumption,
% 11.36/1.99                [status(thm)],
% 11.36/1.99                [c_45378,c_27,c_28,c_29,c_35,c_41,c_91,c_279,c_284,c_978,
% 11.36/1.99                 c_1241,c_1245,c_1475,c_1827,c_2084,c_2248,c_20401,
% 11.36/1.99                 c_22153,c_41499]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(c_45822,plain,
% 11.36/1.99      ( v3_ordinal1(sK4) != iProver_top ),
% 11.36/1.99      inference(superposition,[status(thm)],[c_697,c_45817]) ).
% 11.36/1.99  
% 11.36/1.99  cnf(contradiction,plain,
% 11.36/1.99      ( $false ),
% 11.36/1.99      inference(minisat,[status(thm)],[c_45822,c_28]) ).
% 11.36/1.99  
% 11.36/1.99  
% 11.36/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.36/1.99  
% 11.36/1.99  ------                               Statistics
% 11.36/1.99  
% 11.36/1.99  ------ Selected
% 11.36/1.99  
% 11.36/1.99  total_time:                             1.215
% 11.36/1.99  
%------------------------------------------------------------------------------
