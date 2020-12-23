%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:41 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :  210 (13712 expanded)
%              Number of clauses        :  147 (4825 expanded)
%              Number of leaves         :   17 (2800 expanded)
%              Depth                    :   36
%              Number of atoms          :  709 (51101 expanded)
%              Number of equality atoms :  371 (15364 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   17 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_xboole_0(X1,X0)
              & X0 != X1
              & ~ r2_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_xboole_0(X1,X0)
          | X0 = X1
          | r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_xboole_0(X1,X0)
          | X0 = X1
          | r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X1,X0)
      | X0 = X1
      | r2_xboole_0(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f36])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f17,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f54,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_xboole_0(X0,X1)
           => r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_xboole_0(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f14,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
     => ( sK3 != X0
        & r4_wellord1(k1_wellord2(X0),k1_wellord2(sK3))
        & v3_ordinal1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( sK2 != X1
          & r4_wellord1(k1_wellord2(sK2),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( sK2 != sK3
    & r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
    & v3_ordinal1(sK3)
    & v3_ordinal1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f35,f46,f45])).

fof(f71,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f72,plain,(
    v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f74,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f47])).

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f75,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
           => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_wellord1(k1_wellord2(X1),X0) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f69,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
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

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK0(X0,X1),sK1(X0,X1))
          | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
        & ( r1_tarski(sK0(X0,X1),sK1(X0,X1))
          | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
        & r2_hidden(sK1(X0,X1),X0)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK0(X0,X1),sK1(X0,X1))
              | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
            & ( r1_tarski(sK0(X0,X1),sK1(X0,X1))
              | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
            & r2_hidden(sK1(X0,X1),X0)
            & r2_hidden(sK0(X0,X1),X0) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f43])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f84,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f60])).

fof(f73,plain,(
    r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) ),
    inference(cnf_transformation,[],[f47])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r4_wellord1(X1,X0)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_9,plain,
    ( r2_xboole_0(X0,X1)
    | r2_xboole_0(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_17080,plain,
    ( X0 = X1
    | r2_xboole_0(X1,X0) = iProver_top
    | r2_xboole_0(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_17082,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_17264,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) = iProver_top
    | r2_xboole_0(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17080,c_17082])).

cnf(c_22,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_17077,plain,
    ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_17348,plain,
    ( X0 = X1
    | k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | r2_xboole_0(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17264,c_17077])).

cnf(c_6,plain,
    ( ~ v3_ordinal1(X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_xboole_0(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_288,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_xboole_0(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(resolution,[status(thm)],[c_6,c_7])).

cnf(c_17072,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_xboole_0(X0,X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_288])).

cnf(c_17451,plain,
    ( X0 = X1
    | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
    | r2_hidden(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17348,c_17072])).

cnf(c_26,negated_conjecture,
    ( v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_17074,plain,
    ( v3_ordinal1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_17075,plain,
    ( v3_ordinal1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_17261,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) = iProver_top
    | r2_xboole_0(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17080,c_17082])).

cnf(c_17320,plain,
    ( X0 = X1
    | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
    | r2_xboole_0(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17261,c_17077])).

cnf(c_17406,plain,
    ( X0 = X1
    | k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17320,c_17082])).

cnf(c_17481,plain,
    ( X0 = X1
    | k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17406,c_17077])).

cnf(c_17827,plain,
    ( k2_wellord1(k1_wellord2(X0),sK3) = k1_wellord2(sK3)
    | k2_wellord1(k1_wellord2(sK3),X0) = k1_wellord2(X0)
    | sK3 = X0
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17075,c_17481])).

cnf(c_17876,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_17074,c_17827])).

cnf(c_14764,plain,
    ( v3_ordinal1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_14765,plain,
    ( v3_ordinal1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_14767,plain,
    ( X0 = X1
    | r2_xboole_0(X1,X0) = iProver_top
    | r2_xboole_0(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_14769,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_14849,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) = iProver_top
    | r2_xboole_0(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14767,c_14769])).

cnf(c_14766,plain,
    ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_14886,plain,
    ( X0 = X1
    | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
    | r2_xboole_0(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14849,c_14766])).

cnf(c_14908,plain,
    ( X0 = X1
    | k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14886,c_14769])).

cnf(c_14947,plain,
    ( X0 = X1
    | k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14908,c_14766])).

cnf(c_14970,plain,
    ( k2_wellord1(k1_wellord2(X0),sK3) = k1_wellord2(sK3)
    | k2_wellord1(k1_wellord2(sK3),X0) = k1_wellord2(X0)
    | sK3 = X0
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14765,c_14947])).

cnf(c_14998,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_14764,c_14970])).

cnf(c_27,plain,
    ( v3_ordinal1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_23,negated_conjecture,
    ( sK2 != sK3 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1,negated_conjecture,
    ( ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_34,plain,
    ( ~ r2_xboole_0(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_71,plain,
    ( r2_xboole_0(sK2,sK2)
    | ~ v3_ordinal1(sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_484,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1918,plain,
    ( X0 = X1
    | X1 != sK2
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_484])).

cnf(c_2079,plain,
    ( sK3 != sK2
    | sK2 = sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1918])).

cnf(c_14989,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | sK3 = sK2
    | v3_ordinal1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_14970])).

cnf(c_15011,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14998,c_26,c_27,c_23,c_34,c_71,c_2079,c_14989])).

cnf(c_15012,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
    inference(renaming,[status(thm)],[c_15011])).

cnf(c_17887,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17876,c_26,c_27,c_23,c_34,c_71,c_2079,c_14989])).

cnf(c_17888,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
    inference(renaming,[status(thm)],[c_17887])).

cnf(c_17262,plain,
    ( X0 = X1
    | r2_hidden(X1,X0) = iProver_top
    | r2_xboole_0(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17080,c_17072])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | k1_wellord1(k1_wellord2(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_147,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | k1_wellord1(k1_wellord2(X1),X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_8])).

cnf(c_17073,plain,
    ( k1_wellord1(k1_wellord2(X0),X1) = X1
    | r2_hidden(X1,X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_147])).

cnf(c_17329,plain,
    ( X0 = X1
    | k1_wellord1(k1_wellord2(X1),X0) = X0
    | r2_xboole_0(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17262,c_17073])).

cnf(c_17375,plain,
    ( X0 = X1
    | k1_wellord1(k1_wellord2(X0),X1) = X1
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17329,c_17082])).

cnf(c_17442,plain,
    ( X0 = X1
    | k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | k1_wellord1(k1_wellord2(X1),X0) = X0
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17375,c_17077])).

cnf(c_17654,plain,
    ( k2_wellord1(k1_wellord2(sK2),X0) = k1_wellord2(X0)
    | k1_wellord1(k1_wellord2(X0),sK2) = sK2
    | sK2 = X0
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17074,c_17442])).

cnf(c_17714,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_17075,c_17654])).

cnf(c_17727,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17714,c_26,c_23,c_34,c_71,c_2079])).

cnf(c_17728,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
    inference(renaming,[status(thm)],[c_17727])).

cnf(c_17653,plain,
    ( k2_wellord1(k1_wellord2(sK3),X0) = k1_wellord2(X0)
    | k1_wellord1(k1_wellord2(X0),sK3) = sK3
    | sK3 = X0
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17075,c_17442])).

cnf(c_17698,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
    | k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_17074,c_17653])).

cnf(c_17672,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
    | k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | sK3 = sK2
    | v3_ordinal1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_17653])).

cnf(c_17705,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17698,c_26,c_27,c_23,c_34,c_71,c_2079,c_17672])).

cnf(c_17706,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
    | k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
    inference(renaming,[status(thm)],[c_17705])).

cnf(c_17376,plain,
    ( X0 = X1
    | k1_wellord1(k1_wellord2(X0),X1) = X1
    | r2_hidden(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17329,c_17072])).

cnf(c_17541,plain,
    ( X0 = X1
    | k1_wellord1(k1_wellord2(X0),X1) = X1
    | k1_wellord1(k1_wellord2(X1),X0) = X0
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17376,c_17073])).

cnf(c_17609,plain,
    ( k1_wellord1(k1_wellord2(X0),sK3) = sK3
    | k1_wellord1(k1_wellord2(sK3),X0) = X0
    | sK3 = X0
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17075,c_17541])).

cnf(c_17639,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_17074,c_17609])).

cnf(c_17628,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | sK3 = sK2
    | v3_ordinal1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_17609])).

cnf(c_17677,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17639,c_26,c_27,c_23,c_34,c_71,c_2079,c_17628])).

cnf(c_17678,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
    inference(renaming,[status(thm)],[c_17677])).

cnf(c_11,negated_conjecture,
    ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
    | ~ r2_hidden(X1,k3_relat_1(X0))
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_21,plain,
    ( v2_wellord1(k1_wellord2(X0))
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_308,plain,
    ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
    | ~ r2_hidden(X1,k3_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v3_ordinal1(X2)
    | k1_wellord2(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_309,plain,
    ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
    | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
    | ~ v1_relat_1(k1_wellord2(X0))
    | ~ v3_ordinal1(X0) ),
    inference(unflattening,[status(thm)],[c_308])).

cnf(c_19,plain,
    ( v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_313,plain,
    ( ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
    | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
    | ~ v3_ordinal1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_309,c_19])).

cnf(c_314,plain,
    ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
    | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
    | ~ v3_ordinal1(X0) ),
    inference(renaming,[status(thm)],[c_313])).

cnf(c_17071,plain,
    ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
    | r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_314])).

cnf(c_18,plain,
    ( ~ v1_relat_1(k1_wellord2(X0))
    | k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_153,plain,
    ( k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_19])).

cnf(c_17145,plain,
    ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17071,c_153])).

cnf(c_17681,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_17678,c_17145])).

cnf(c_28,plain,
    ( v3_ordinal1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1149,plain,
    ( r2_xboole_0(X0,sK3)
    | r2_xboole_0(sK3,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK3)
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1150,plain,
    ( X0 = sK3
    | r2_xboole_0(X0,sK3) = iProver_top
    | r2_xboole_0(sK3,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1149])).

cnf(c_1152,plain,
    ( sK2 = sK3
    | r2_xboole_0(sK3,sK2) = iProver_top
    | r2_xboole_0(sK2,sK3) = iProver_top
    | v3_ordinal1(sK3) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1150])).

cnf(c_3269,plain,
    ( r2_hidden(sK3,X0)
    | ~ r2_xboole_0(sK3,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK3) ),
    inference(instantiation,[status(thm)],[c_288])).

cnf(c_3275,plain,
    ( r2_hidden(sK3,X0) = iProver_top
    | r2_xboole_0(sK3,X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3269])).

cnf(c_3277,plain,
    ( r2_hidden(sK3,sK2) = iProver_top
    | r2_xboole_0(sK3,sK2) != iProver_top
    | v3_ordinal1(sK3) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3275])).

cnf(c_13115,plain,
    ( r2_hidden(X0,sK3)
    | ~ r2_xboole_0(X0,sK3)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK3) ),
    inference(instantiation,[status(thm)],[c_288])).

cnf(c_13119,plain,
    ( r2_hidden(X0,sK3) = iProver_top
    | r2_xboole_0(X0,sK3) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13115])).

cnf(c_13121,plain,
    ( r2_hidden(sK2,sK3) = iProver_top
    | r2_xboole_0(sK2,sK3) != iProver_top
    | v3_ordinal1(sK3) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_13119])).

cnf(c_17576,plain,
    ( ~ r2_hidden(sK3,X0)
    | ~ v3_ordinal1(X0)
    | k1_wellord1(k1_wellord2(X0),sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_147])).

cnf(c_17578,plain,
    ( k1_wellord1(k1_wellord2(X0),sK3) = sK3
    | r2_hidden(sK3,X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17576])).

cnf(c_17580,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | r2_hidden(sK3,sK2) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_17578])).

cnf(c_17736,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17681,c_27,c_28,c_23,c_1152,c_3277,c_13121,c_17580])).

cnf(c_17742,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17706,c_17736])).

cnf(c_24,negated_conjecture,
    ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_17076,plain,
    ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_10,plain,
    ( ~ r4_wellord1(X0,X1)
    | r4_wellord1(X1,X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_17079,plain,
    ( r4_wellord1(X0,X1) != iProver_top
    | r4_wellord1(X1,X0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_17227,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17076,c_17079])).

cnf(c_29,plain,
    ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_45,plain,
    ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_47,plain,
    ( v1_relat_1(k1_wellord2(sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_45])).

cnf(c_17172,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2))
    | ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
    | ~ v1_relat_1(k1_wellord2(sK3))
    | ~ v1_relat_1(k1_wellord2(sK2)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_17173,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top
    | r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17172])).

cnf(c_17231,plain,
    ( v1_relat_1(k1_wellord2(sK3)) != iProver_top
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17227,c_29,c_47,c_17173])).

cnf(c_17232,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_17231])).

cnf(c_17078,plain,
    ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_17237,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_17232,c_17078])).

cnf(c_17750,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17742,c_17237])).

cnf(c_17753,plain,
    ( r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top
    | r2_hidden(sK3,sK2) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_17750,c_17145])).

cnf(c_17758,plain,
    ( r2_hidden(sK3,sK2) != iProver_top
    | r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17753,c_27])).

cnf(c_17759,plain,
    ( r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top
    | r2_hidden(sK3,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_17758])).

cnf(c_17764,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) != iProver_top
    | r2_hidden(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_17728,c_17759])).

cnf(c_1151,plain,
    ( r2_xboole_0(sK3,sK2)
    | r2_xboole_0(sK2,sK3)
    | ~ v3_ordinal1(sK3)
    | ~ v3_ordinal1(sK2)
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_1149])).

cnf(c_3276,plain,
    ( r2_hidden(sK3,sK2)
    | ~ r2_xboole_0(sK3,sK2)
    | ~ v3_ordinal1(sK3)
    | ~ v3_ordinal1(sK2) ),
    inference(instantiation,[status(thm)],[c_3269])).

cnf(c_13120,plain,
    ( r2_hidden(sK2,sK3)
    | ~ r2_xboole_0(sK2,sK3)
    | ~ v3_ordinal1(sK3)
    | ~ v3_ordinal1(sK2) ),
    inference(instantiation,[status(thm)],[c_13115])).

cnf(c_17240,plain,
    ( ~ r2_hidden(X0,sK3)
    | ~ v3_ordinal1(sK3)
    | k1_wellord1(k1_wellord2(sK3),X0) = X0 ),
    inference(instantiation,[status(thm)],[c_147])).

cnf(c_17245,plain,
    ( ~ r2_hidden(sK2,sK3)
    | ~ v3_ordinal1(sK3)
    | k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
    inference(instantiation,[status(thm)],[c_17240])).

cnf(c_17765,plain,
    ( ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
    | ~ r2_hidden(sK3,sK2)
    | k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_17764])).

cnf(c_17768,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17764,c_26,c_25,c_24,c_23,c_1151,c_3276,c_13120,c_17245,c_17765])).

cnf(c_17771,plain,
    ( r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_17768,c_17145])).

cnf(c_17774,plain,
    ( r2_hidden(sK2,sK3) != iProver_top
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17771,c_28])).

cnf(c_17775,plain,
    ( r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_17774])).

cnf(c_17891,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_17888,c_17775])).

cnf(c_11147,plain,
    ( r1_tarski(sK3,X0)
    | ~ r2_xboole_0(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_11149,plain,
    ( r1_tarski(sK3,sK2)
    | ~ r2_xboole_0(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_11147])).

cnf(c_15593,plain,
    ( ~ r1_tarski(sK3,X0)
    | k2_wellord1(k1_wellord2(X0),sK3) = k1_wellord2(sK3) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_15598,plain,
    ( ~ r1_tarski(sK3,sK2)
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
    inference(instantiation,[status(thm)],[c_15593])).

cnf(c_17238,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_17237])).

cnf(c_17892,plain,
    ( ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2))
    | ~ r2_hidden(sK2,sK3)
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_17891])).

cnf(c_17906,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17891,c_26,c_25,c_23,c_1151,c_11149,c_13120,c_15598,c_17238,c_17892])).

cnf(c_17909,plain,
    ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) != iProver_top
    | r2_hidden(sK3,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_17906,c_17759])).

cnf(c_17912,plain,
    ( r2_hidden(sK3,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17909,c_29])).

cnf(c_17920,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
    | sK3 = sK2
    | v3_ordinal1(sK3) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_17451,c_17912])).

cnf(c_11396,plain,
    ( r1_tarski(X0,sK3)
    | ~ r2_xboole_0(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_11397,plain,
    ( r1_tarski(X0,sK3) = iProver_top
    | r2_xboole_0(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11396])).

cnf(c_11399,plain,
    ( r1_tarski(sK2,sK3) = iProver_top
    | r2_xboole_0(sK2,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11397])).

cnf(c_14888,plain,
    ( ~ r1_tarski(X0,sK3)
    | k2_wellord1(k1_wellord2(sK3),X0) = k1_wellord2(X0) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_14889,plain,
    ( k2_wellord1(k1_wellord2(sK3),X0) = k1_wellord2(X0)
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14888])).

cnf(c_14891,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_14889])).

cnf(c_17965,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17920,c_27,c_28,c_29,c_23,c_1152,c_3277,c_11399,c_14891,c_17909])).

cnf(c_17968,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_17965,c_17775])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17968,c_17909,c_17237,c_13121,c_3277,c_1152,c_23,c_29,c_28,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:05:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.65/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.65/1.00  
% 3.65/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.65/1.00  
% 3.65/1.00  ------  iProver source info
% 3.65/1.00  
% 3.65/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.65/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.65/1.00  git: non_committed_changes: false
% 3.65/1.00  git: last_make_outside_of_git: false
% 3.65/1.00  
% 3.65/1.00  ------ 
% 3.65/1.00  ------ Parsing...
% 3.65/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  ------ Proving...
% 3.65/1.00  ------ Problem Properties 
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  clauses                                 24
% 3.65/1.00  conjectures                             5
% 3.65/1.00  EPR                                     12
% 3.65/1.00  Horn                                    19
% 3.65/1.00  unary                                   8
% 3.65/1.00  binary                                  2
% 3.65/1.00  lits                                    64
% 3.65/1.00  lits eq                                 11
% 3.65/1.00  fd_pure                                 0
% 3.65/1.00  fd_pseudo                               0
% 3.65/1.00  fd_cond                                 0
% 3.65/1.00  fd_pseudo_cond                          3
% 3.65/1.00  AC symbols                              0
% 3.65/1.00  
% 3.65/1.00  ------ Input Options Time Limit: Unbounded
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.65/1.00  Current options:
% 3.65/1.00  ------ 
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  % SZS status Theorem for theBenchmark.p
% 3.65/1.00  
% 3.65/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.65/1.00  
% 3.65/1.00  fof(f6,axiom,(
% 3.65/1.00    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1))))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f22,plain,(
% 3.65/1.00    ! [X0] : (! [X1] : ((r2_xboole_0(X1,X0) | X0 = X1 | r2_xboole_0(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.65/1.00    inference(ennf_transformation,[],[f6])).
% 3.65/1.00  
% 3.65/1.00  fof(f23,plain,(
% 3.65/1.00    ! [X0] : (! [X1] : (r2_xboole_0(X1,X0) | X0 = X1 | r2_xboole_0(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.65/1.00    inference(flattening,[],[f22])).
% 3.65/1.00  
% 3.65/1.00  fof(f57,plain,(
% 3.65/1.00    ( ! [X0,X1] : (r2_xboole_0(X1,X0) | X0 = X1 | r2_xboole_0(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f23])).
% 3.65/1.00  
% 3.65/1.00  fof(f1,axiom,(
% 3.65/1.00    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f36,plain,(
% 3.65/1.00    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 3.65/1.00    inference(nnf_transformation,[],[f1])).
% 3.65/1.00  
% 3.65/1.00  fof(f37,plain,(
% 3.65/1.00    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 3.65/1.00    inference(flattening,[],[f36])).
% 3.65/1.00  
% 3.65/1.00  fof(f48,plain,(
% 3.65/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f37])).
% 3.65/1.00  
% 3.65/1.00  fof(f13,axiom,(
% 3.65/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f33,plain,(
% 3.65/1.00    ! [X0,X1] : (k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) | ~r1_tarski(X0,X1))),
% 3.65/1.00    inference(ennf_transformation,[],[f13])).
% 3.65/1.00  
% 3.65/1.00  fof(f70,plain,(
% 3.65/1.00    ( ! [X0,X1] : (k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) | ~r1_tarski(X0,X1)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f33])).
% 3.65/1.00  
% 3.65/1.00  fof(f3,axiom,(
% 3.65/1.00    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f16,plain,(
% 3.65/1.00    ! [X0] : (v3_ordinal1(X0) => v1_ordinal1(X0))),
% 3.65/1.00    inference(pure_predicate_removal,[],[f3])).
% 3.65/1.00  
% 3.65/1.00  fof(f17,plain,(
% 3.65/1.00    ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0))),
% 3.65/1.00    inference(ennf_transformation,[],[f16])).
% 3.65/1.00  
% 3.65/1.00  fof(f54,plain,(
% 3.65/1.00    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f17])).
% 3.65/1.00  
% 3.65/1.00  fof(f4,axiom,(
% 3.65/1.00    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_xboole_0(X0,X1) => r2_hidden(X0,X1))))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f18,plain,(
% 3.65/1.00    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 3.65/1.00    inference(ennf_transformation,[],[f4])).
% 3.65/1.00  
% 3.65/1.00  fof(f19,plain,(
% 3.65/1.00    ! [X0] : (! [X1] : (r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 3.65/1.00    inference(flattening,[],[f18])).
% 3.65/1.00  
% 3.65/1.00  fof(f55,plain,(
% 3.65/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1) | ~v1_ordinal1(X0)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f19])).
% 3.65/1.00  
% 3.65/1.00  fof(f14,conjecture,(
% 3.65/1.00    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f15,negated_conjecture,(
% 3.65/1.00    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 3.65/1.00    inference(negated_conjecture,[],[f14])).
% 3.65/1.00  
% 3.65/1.00  fof(f34,plain,(
% 3.65/1.00    ? [X0] : (? [X1] : ((X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.65/1.00    inference(ennf_transformation,[],[f15])).
% 3.65/1.00  
% 3.65/1.00  fof(f35,plain,(
% 3.65/1.00    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.65/1.00    inference(flattening,[],[f34])).
% 3.65/1.00  
% 3.65/1.00  fof(f46,plain,(
% 3.65/1.00    ( ! [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) => (sK3 != X0 & r4_wellord1(k1_wellord2(X0),k1_wellord2(sK3)) & v3_ordinal1(sK3))) )),
% 3.65/1.00    introduced(choice_axiom,[])).
% 3.65/1.00  
% 3.65/1.00  fof(f45,plain,(
% 3.65/1.00    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : (sK2 != X1 & r4_wellord1(k1_wellord2(sK2),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK2))),
% 3.65/1.00    introduced(choice_axiom,[])).
% 3.65/1.00  
% 3.65/1.00  fof(f47,plain,(
% 3.65/1.00    (sK2 != sK3 & r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) & v3_ordinal1(sK3)) & v3_ordinal1(sK2)),
% 3.65/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f35,f46,f45])).
% 3.65/1.00  
% 3.65/1.00  fof(f71,plain,(
% 3.65/1.00    v3_ordinal1(sK2)),
% 3.65/1.00    inference(cnf_transformation,[],[f47])).
% 3.65/1.00  
% 3.65/1.00  fof(f72,plain,(
% 3.65/1.00    v3_ordinal1(sK3)),
% 3.65/1.00    inference(cnf_transformation,[],[f47])).
% 3.65/1.00  
% 3.65/1.00  fof(f74,plain,(
% 3.65/1.00    sK2 != sK3),
% 3.65/1.00    inference(cnf_transformation,[],[f47])).
% 3.65/1.00  
% 3.65/1.00  fof(f49,plain,(
% 3.65/1.00    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f37])).
% 3.65/1.00  
% 3.65/1.00  fof(f75,plain,(
% 3.65/1.00    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 3.65/1.00    inference(equality_resolution,[],[f49])).
% 3.65/1.00  
% 3.65/1.00  fof(f11,axiom,(
% 3.65/1.00    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => k1_wellord1(k1_wellord2(X1),X0) = X0)))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f30,plain,(
% 3.65/1.00    ! [X0] : (! [X1] : ((k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.65/1.00    inference(ennf_transformation,[],[f11])).
% 3.65/1.00  
% 3.65/1.00  fof(f31,plain,(
% 3.65/1.00    ! [X0] : (! [X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.65/1.00    inference(flattening,[],[f30])).
% 3.65/1.00  
% 3.65/1.00  fof(f68,plain,(
% 3.65/1.00    ( ! [X0,X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f31])).
% 3.65/1.00  
% 3.65/1.00  fof(f5,axiom,(
% 3.65/1.00    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f20,plain,(
% 3.65/1.00    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 3.65/1.00    inference(ennf_transformation,[],[f5])).
% 3.65/1.00  
% 3.65/1.00  fof(f21,plain,(
% 3.65/1.00    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 3.65/1.00    inference(flattening,[],[f20])).
% 3.65/1.00  
% 3.65/1.00  fof(f56,plain,(
% 3.65/1.00    ( ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f21])).
% 3.65/1.00  
% 3.65/1.00  fof(f8,axiom,(
% 3.65/1.00    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f26,plain,(
% 3.65/1.00    ! [X0] : ((! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 3.65/1.00    inference(ennf_transformation,[],[f8])).
% 3.65/1.00  
% 3.65/1.00  fof(f27,plain,(
% 3.65/1.00    ! [X0] : (! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 3.65/1.00    inference(flattening,[],[f26])).
% 3.65/1.00  
% 3.65/1.00  fof(f59,plain,(
% 3.65/1.00    ( ! [X0,X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0)) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f27])).
% 3.65/1.00  
% 3.65/1.00  fof(f12,axiom,(
% 3.65/1.00    ! [X0] : (v3_ordinal1(X0) => v2_wellord1(k1_wellord2(X0)))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f32,plain,(
% 3.65/1.00    ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0))),
% 3.65/1.00    inference(ennf_transformation,[],[f12])).
% 3.65/1.00  
% 3.65/1.00  fof(f69,plain,(
% 3.65/1.00    ( ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f32])).
% 3.65/1.00  
% 3.65/1.00  fof(f10,axiom,(
% 3.65/1.00    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f67,plain,(
% 3.65/1.00    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 3.65/1.00    inference(cnf_transformation,[],[f10])).
% 3.65/1.00  
% 3.65/1.00  fof(f9,axiom,(
% 3.65/1.00    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f28,plain,(
% 3.65/1.00    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 3.65/1.00    inference(ennf_transformation,[],[f9])).
% 3.65/1.00  
% 3.65/1.00  fof(f29,plain,(
% 3.65/1.00    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 3.65/1.00    inference(flattening,[],[f28])).
% 3.65/1.00  
% 3.65/1.00  fof(f40,plain,(
% 3.65/1.00    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 3.65/1.00    inference(nnf_transformation,[],[f29])).
% 3.65/1.00  
% 3.65/1.00  fof(f41,plain,(
% 3.65/1.00    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 3.65/1.00    inference(flattening,[],[f40])).
% 3.65/1.00  
% 3.65/1.00  fof(f42,plain,(
% 3.65/1.00    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 3.65/1.00    inference(rectify,[],[f41])).
% 3.65/1.00  
% 3.65/1.00  fof(f43,plain,(
% 3.65/1.00    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK0(X0,X1),sK1(X0,X1)) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & (r1_tarski(sK0(X0,X1),sK1(X0,X1)) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & r2_hidden(sK1(X0,X1),X0) & r2_hidden(sK0(X0,X1),X0)))),
% 3.65/1.00    introduced(choice_axiom,[])).
% 3.65/1.00  
% 3.65/1.00  fof(f44,plain,(
% 3.65/1.00    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK0(X0,X1),sK1(X0,X1)) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & (r1_tarski(sK0(X0,X1),sK1(X0,X1)) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & r2_hidden(sK1(X0,X1),X0) & r2_hidden(sK0(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 3.65/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f43])).
% 3.65/1.00  
% 3.65/1.00  fof(f60,plain,(
% 3.65/1.00    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f44])).
% 3.65/1.00  
% 3.65/1.00  fof(f84,plain,(
% 3.65/1.00    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 3.65/1.00    inference(equality_resolution,[],[f60])).
% 3.65/1.00  
% 3.65/1.00  fof(f73,plain,(
% 3.65/1.00    r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))),
% 3.65/1.00    inference(cnf_transformation,[],[f47])).
% 3.65/1.00  
% 3.65/1.00  fof(f7,axiom,(
% 3.65/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f24,plain,(
% 3.65/1.00    ! [X0] : (! [X1] : ((r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.65/1.00    inference(ennf_transformation,[],[f7])).
% 3.65/1.00  
% 3.65/1.00  fof(f25,plain,(
% 3.65/1.00    ! [X0] : (! [X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.65/1.00    inference(flattening,[],[f24])).
% 3.65/1.00  
% 3.65/1.00  fof(f58,plain,(
% 3.65/1.00    ( ! [X0,X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f25])).
% 3.65/1.00  
% 3.65/1.00  cnf(c_9,plain,
% 3.65/1.00      ( r2_xboole_0(X0,X1)
% 3.65/1.00      | r2_xboole_0(X1,X0)
% 3.65/1.00      | ~ v3_ordinal1(X0)
% 3.65/1.00      | ~ v3_ordinal1(X1)
% 3.65/1.00      | X1 = X0 ),
% 3.65/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17080,plain,
% 3.65/1.00      ( X0 = X1
% 3.65/1.00      | r2_xboole_0(X1,X0) = iProver_top
% 3.65/1.00      | r2_xboole_0(X0,X1) = iProver_top
% 3.65/1.00      | v3_ordinal1(X1) != iProver_top
% 3.65/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_2,plain,
% 3.65/1.00      ( r1_tarski(X0,X1) | ~ r2_xboole_0(X0,X1) ),
% 3.65/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17082,plain,
% 3.65/1.00      ( r1_tarski(X0,X1) = iProver_top
% 3.65/1.00      | r2_xboole_0(X0,X1) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17264,plain,
% 3.65/1.00      ( X0 = X1
% 3.65/1.00      | r1_tarski(X0,X1) = iProver_top
% 3.65/1.00      | r2_xboole_0(X1,X0) = iProver_top
% 3.65/1.00      | v3_ordinal1(X1) != iProver_top
% 3.65/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_17080,c_17082]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_22,plain,
% 3.65/1.00      ( ~ r1_tarski(X0,X1)
% 3.65/1.00      | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ),
% 3.65/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17077,plain,
% 3.65/1.00      ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 3.65/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17348,plain,
% 3.65/1.00      ( X0 = X1
% 3.65/1.00      | k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 3.65/1.00      | r2_xboole_0(X0,X1) = iProver_top
% 3.65/1.00      | v3_ordinal1(X1) != iProver_top
% 3.65/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_17264,c_17077]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_6,plain,
% 3.65/1.00      ( ~ v3_ordinal1(X0) | v1_ordinal1(X0) ),
% 3.65/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_7,plain,
% 3.65/1.00      ( r2_hidden(X0,X1)
% 3.65/1.00      | ~ r2_xboole_0(X0,X1)
% 3.65/1.00      | ~ v3_ordinal1(X1)
% 3.65/1.00      | ~ v1_ordinal1(X0) ),
% 3.65/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_288,plain,
% 3.65/1.00      ( r2_hidden(X0,X1)
% 3.65/1.00      | ~ r2_xboole_0(X0,X1)
% 3.65/1.00      | ~ v3_ordinal1(X0)
% 3.65/1.00      | ~ v3_ordinal1(X1) ),
% 3.65/1.00      inference(resolution,[status(thm)],[c_6,c_7]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17072,plain,
% 3.65/1.00      ( r2_hidden(X0,X1) = iProver_top
% 3.65/1.00      | r2_xboole_0(X0,X1) != iProver_top
% 3.65/1.00      | v3_ordinal1(X0) != iProver_top
% 3.65/1.00      | v3_ordinal1(X1) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_288]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17451,plain,
% 3.65/1.00      ( X0 = X1
% 3.65/1.00      | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
% 3.65/1.00      | r2_hidden(X1,X0) = iProver_top
% 3.65/1.00      | v3_ordinal1(X1) != iProver_top
% 3.65/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_17348,c_17072]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_26,negated_conjecture,
% 3.65/1.00      ( v3_ordinal1(sK2) ),
% 3.65/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17074,plain,
% 3.65/1.00      ( v3_ordinal1(sK2) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_25,negated_conjecture,
% 3.65/1.00      ( v3_ordinal1(sK3) ),
% 3.65/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17075,plain,
% 3.65/1.00      ( v3_ordinal1(sK3) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17261,plain,
% 3.65/1.00      ( X0 = X1
% 3.65/1.00      | r1_tarski(X1,X0) = iProver_top
% 3.65/1.00      | r2_xboole_0(X0,X1) = iProver_top
% 3.65/1.00      | v3_ordinal1(X1) != iProver_top
% 3.65/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_17080,c_17082]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17320,plain,
% 3.65/1.00      ( X0 = X1
% 3.65/1.00      | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
% 3.65/1.00      | r2_xboole_0(X1,X0) = iProver_top
% 3.65/1.00      | v3_ordinal1(X1) != iProver_top
% 3.65/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_17261,c_17077]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17406,plain,
% 3.65/1.00      ( X0 = X1
% 3.65/1.00      | k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 3.65/1.00      | r1_tarski(X0,X1) = iProver_top
% 3.65/1.00      | v3_ordinal1(X1) != iProver_top
% 3.65/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_17320,c_17082]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17481,plain,
% 3.65/1.00      ( X0 = X1
% 3.65/1.00      | k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 3.65/1.00      | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
% 3.65/1.00      | v3_ordinal1(X1) != iProver_top
% 3.65/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_17406,c_17077]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17827,plain,
% 3.65/1.00      ( k2_wellord1(k1_wellord2(X0),sK3) = k1_wellord2(sK3)
% 3.65/1.00      | k2_wellord1(k1_wellord2(sK3),X0) = k1_wellord2(X0)
% 3.65/1.00      | sK3 = X0
% 3.65/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_17075,c_17481]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17876,plain,
% 3.65/1.00      ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
% 3.65/1.00      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.65/1.00      | sK3 = sK2 ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_17074,c_17827]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_14764,plain,
% 3.65/1.00      ( v3_ordinal1(sK2) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_14765,plain,
% 3.65/1.00      ( v3_ordinal1(sK3) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_14767,plain,
% 3.65/1.00      ( X0 = X1
% 3.65/1.00      | r2_xboole_0(X1,X0) = iProver_top
% 3.65/1.00      | r2_xboole_0(X0,X1) = iProver_top
% 3.65/1.00      | v3_ordinal1(X1) != iProver_top
% 3.65/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_14769,plain,
% 3.65/1.00      ( r1_tarski(X0,X1) = iProver_top
% 3.65/1.00      | r2_xboole_0(X0,X1) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_14849,plain,
% 3.65/1.00      ( X0 = X1
% 3.65/1.00      | r1_tarski(X1,X0) = iProver_top
% 3.65/1.00      | r2_xboole_0(X0,X1) = iProver_top
% 3.65/1.00      | v3_ordinal1(X1) != iProver_top
% 3.65/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_14767,c_14769]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_14766,plain,
% 3.65/1.00      ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 3.65/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_14886,plain,
% 3.65/1.00      ( X0 = X1
% 3.65/1.00      | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
% 3.65/1.00      | r2_xboole_0(X1,X0) = iProver_top
% 3.65/1.00      | v3_ordinal1(X1) != iProver_top
% 3.65/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_14849,c_14766]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_14908,plain,
% 3.65/1.00      ( X0 = X1
% 3.65/1.00      | k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 3.65/1.00      | r1_tarski(X0,X1) = iProver_top
% 3.65/1.00      | v3_ordinal1(X1) != iProver_top
% 3.65/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_14886,c_14769]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_14947,plain,
% 3.65/1.00      ( X0 = X1
% 3.65/1.00      | k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 3.65/1.00      | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
% 3.65/1.00      | v3_ordinal1(X1) != iProver_top
% 3.65/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_14908,c_14766]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_14970,plain,
% 3.65/1.00      ( k2_wellord1(k1_wellord2(X0),sK3) = k1_wellord2(sK3)
% 3.65/1.00      | k2_wellord1(k1_wellord2(sK3),X0) = k1_wellord2(X0)
% 3.65/1.00      | sK3 = X0
% 3.65/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_14765,c_14947]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_14998,plain,
% 3.65/1.00      ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
% 3.65/1.00      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.65/1.00      | sK3 = sK2 ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_14764,c_14970]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_27,plain,
% 3.65/1.00      ( v3_ordinal1(sK2) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_23,negated_conjecture,
% 3.65/1.00      ( sK2 != sK3 ),
% 3.65/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1,negated_conjecture,
% 3.65/1.00      ( ~ r2_xboole_0(X0,X0) ),
% 3.65/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_34,plain,
% 3.65/1.00      ( ~ r2_xboole_0(sK2,sK2) ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_71,plain,
% 3.65/1.00      ( r2_xboole_0(sK2,sK2) | ~ v3_ordinal1(sK2) | sK2 = sK2 ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_484,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1918,plain,
% 3.65/1.00      ( X0 = X1 | X1 != sK2 | X0 != sK2 ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_484]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_2079,plain,
% 3.65/1.00      ( sK3 != sK2 | sK2 = sK3 | sK2 != sK2 ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_1918]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_14989,plain,
% 3.65/1.00      ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
% 3.65/1.00      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.65/1.00      | sK3 = sK2
% 3.65/1.00      | v3_ordinal1(sK2) != iProver_top ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_14970]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_15011,plain,
% 3.65/1.00      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.65/1.00      | k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2) ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_14998,c_26,c_27,c_23,c_34,c_71,c_2079,c_14989]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_15012,plain,
% 3.65/1.00      ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
% 3.65/1.00      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
% 3.65/1.00      inference(renaming,[status(thm)],[c_15011]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17887,plain,
% 3.65/1.00      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.65/1.00      | k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2) ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_17876,c_26,c_27,c_23,c_34,c_71,c_2079,c_14989]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17888,plain,
% 3.65/1.00      ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
% 3.65/1.00      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
% 3.65/1.00      inference(renaming,[status(thm)],[c_17887]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17262,plain,
% 3.65/1.00      ( X0 = X1
% 3.65/1.00      | r2_hidden(X1,X0) = iProver_top
% 3.65/1.00      | r2_xboole_0(X0,X1) = iProver_top
% 3.65/1.00      | v3_ordinal1(X1) != iProver_top
% 3.65/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_17080,c_17072]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_20,plain,
% 3.65/1.00      ( ~ r2_hidden(X0,X1)
% 3.65/1.00      | ~ v3_ordinal1(X0)
% 3.65/1.00      | ~ v3_ordinal1(X1)
% 3.65/1.00      | k1_wellord1(k1_wellord2(X1),X0) = X0 ),
% 3.65/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_8,plain,
% 3.65/1.00      ( ~ r2_hidden(X0,X1) | ~ v3_ordinal1(X1) | v3_ordinal1(X0) ),
% 3.65/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_147,plain,
% 3.65/1.00      ( ~ r2_hidden(X0,X1)
% 3.65/1.00      | ~ v3_ordinal1(X1)
% 3.65/1.00      | k1_wellord1(k1_wellord2(X1),X0) = X0 ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_20,c_8]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17073,plain,
% 3.65/1.00      ( k1_wellord1(k1_wellord2(X0),X1) = X1
% 3.65/1.00      | r2_hidden(X1,X0) != iProver_top
% 3.65/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_147]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17329,plain,
% 3.65/1.00      ( X0 = X1
% 3.65/1.00      | k1_wellord1(k1_wellord2(X1),X0) = X0
% 3.65/1.00      | r2_xboole_0(X1,X0) = iProver_top
% 3.65/1.00      | v3_ordinal1(X1) != iProver_top
% 3.65/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_17262,c_17073]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17375,plain,
% 3.65/1.00      ( X0 = X1
% 3.65/1.00      | k1_wellord1(k1_wellord2(X0),X1) = X1
% 3.65/1.00      | r1_tarski(X0,X1) = iProver_top
% 3.65/1.00      | v3_ordinal1(X1) != iProver_top
% 3.65/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_17329,c_17082]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17442,plain,
% 3.65/1.00      ( X0 = X1
% 3.65/1.00      | k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 3.65/1.00      | k1_wellord1(k1_wellord2(X1),X0) = X0
% 3.65/1.00      | v3_ordinal1(X1) != iProver_top
% 3.65/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_17375,c_17077]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17654,plain,
% 3.65/1.00      ( k2_wellord1(k1_wellord2(sK2),X0) = k1_wellord2(X0)
% 3.65/1.00      | k1_wellord1(k1_wellord2(X0),sK2) = sK2
% 3.65/1.00      | sK2 = X0
% 3.65/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_17074,c_17442]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17714,plain,
% 3.65/1.00      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.65/1.00      | k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.65/1.00      | sK3 = sK2 ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_17075,c_17654]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17727,plain,
% 3.65/1.00      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.65/1.00      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_17714,c_26,c_23,c_34,c_71,c_2079]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17728,plain,
% 3.65/1.00      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.65/1.00      | k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
% 3.65/1.00      inference(renaming,[status(thm)],[c_17727]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17653,plain,
% 3.65/1.00      ( k2_wellord1(k1_wellord2(sK3),X0) = k1_wellord2(X0)
% 3.65/1.00      | k1_wellord1(k1_wellord2(X0),sK3) = sK3
% 3.65/1.00      | sK3 = X0
% 3.65/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_17075,c_17442]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17698,plain,
% 3.65/1.00      ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
% 3.65/1.00      | k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.65/1.00      | sK3 = sK2 ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_17074,c_17653]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17672,plain,
% 3.65/1.00      ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
% 3.65/1.00      | k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.65/1.00      | sK3 = sK2
% 3.65/1.00      | v3_ordinal1(sK2) != iProver_top ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_17653]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17705,plain,
% 3.65/1.00      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.65/1.00      | k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2) ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_17698,c_26,c_27,c_23,c_34,c_71,c_2079,c_17672]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17706,plain,
% 3.65/1.00      ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
% 3.65/1.00      | k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
% 3.65/1.00      inference(renaming,[status(thm)],[c_17705]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17376,plain,
% 3.65/1.00      ( X0 = X1
% 3.65/1.00      | k1_wellord1(k1_wellord2(X0),X1) = X1
% 3.65/1.00      | r2_hidden(X0,X1) = iProver_top
% 3.65/1.00      | v3_ordinal1(X1) != iProver_top
% 3.65/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_17329,c_17072]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17541,plain,
% 3.65/1.00      ( X0 = X1
% 3.65/1.00      | k1_wellord1(k1_wellord2(X0),X1) = X1
% 3.65/1.00      | k1_wellord1(k1_wellord2(X1),X0) = X0
% 3.65/1.00      | v3_ordinal1(X1) != iProver_top
% 3.65/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_17376,c_17073]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17609,plain,
% 3.65/1.00      ( k1_wellord1(k1_wellord2(X0),sK3) = sK3
% 3.65/1.00      | k1_wellord1(k1_wellord2(sK3),X0) = X0
% 3.65/1.00      | sK3 = X0
% 3.65/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_17075,c_17541]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17639,plain,
% 3.65/1.00      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.65/1.00      | k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.65/1.00      | sK3 = sK2 ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_17074,c_17609]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17628,plain,
% 3.65/1.00      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.65/1.00      | k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.65/1.00      | sK3 = sK2
% 3.65/1.00      | v3_ordinal1(sK2) != iProver_top ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_17609]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17677,plain,
% 3.65/1.00      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.65/1.00      | k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_17639,c_26,c_27,c_23,c_34,c_71,c_2079,c_17628]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17678,plain,
% 3.65/1.00      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.65/1.00      | k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
% 3.65/1.00      inference(renaming,[status(thm)],[c_17677]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_11,negated_conjecture,
% 3.65/1.00      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
% 3.65/1.00      | ~ r2_hidden(X1,k3_relat_1(X0))
% 3.65/1.00      | ~ v2_wellord1(X0)
% 3.65/1.00      | ~ v1_relat_1(X0) ),
% 3.65/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_21,plain,
% 3.65/1.00      ( v2_wellord1(k1_wellord2(X0)) | ~ v3_ordinal1(X0) ),
% 3.65/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_308,plain,
% 3.65/1.00      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
% 3.65/1.00      | ~ r2_hidden(X1,k3_relat_1(X0))
% 3.65/1.00      | ~ v1_relat_1(X0)
% 3.65/1.00      | ~ v3_ordinal1(X2)
% 3.65/1.00      | k1_wellord2(X2) != X0 ),
% 3.65/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_309,plain,
% 3.65/1.00      ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
% 3.65/1.00      | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
% 3.65/1.00      | ~ v1_relat_1(k1_wellord2(X0))
% 3.65/1.00      | ~ v3_ordinal1(X0) ),
% 3.65/1.00      inference(unflattening,[status(thm)],[c_308]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_19,plain,
% 3.65/1.00      ( v1_relat_1(k1_wellord2(X0)) ),
% 3.65/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_313,plain,
% 3.65/1.00      ( ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
% 3.65/1.00      | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
% 3.65/1.00      | ~ v3_ordinal1(X0) ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_309,c_19]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_314,plain,
% 3.65/1.00      ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
% 3.65/1.00      | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
% 3.65/1.00      | ~ v3_ordinal1(X0) ),
% 3.65/1.00      inference(renaming,[status(thm)],[c_313]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17071,plain,
% 3.65/1.00      ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
% 3.65/1.00      | r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) != iProver_top
% 3.65/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_314]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_18,plain,
% 3.65/1.00      ( ~ v1_relat_1(k1_wellord2(X0))
% 3.65/1.00      | k3_relat_1(k1_wellord2(X0)) = X0 ),
% 3.65/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_153,plain,
% 3.65/1.00      ( k3_relat_1(k1_wellord2(X0)) = X0 ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_18,c_19]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17145,plain,
% 3.65/1.00      ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
% 3.65/1.00      | r2_hidden(X1,X0) != iProver_top
% 3.65/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.65/1.00      inference(light_normalisation,[status(thm)],[c_17071,c_153]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17681,plain,
% 3.65/1.00      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.65/1.00      | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top
% 3.65/1.00      | r2_hidden(sK2,sK3) != iProver_top
% 3.65/1.00      | v3_ordinal1(sK3) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_17678,c_17145]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_28,plain,
% 3.65/1.00      ( v3_ordinal1(sK3) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1149,plain,
% 3.65/1.00      ( r2_xboole_0(X0,sK3)
% 3.65/1.00      | r2_xboole_0(sK3,X0)
% 3.65/1.00      | ~ v3_ordinal1(X0)
% 3.65/1.00      | ~ v3_ordinal1(sK3)
% 3.65/1.00      | X0 = sK3 ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1150,plain,
% 3.65/1.00      ( X0 = sK3
% 3.65/1.00      | r2_xboole_0(X0,sK3) = iProver_top
% 3.65/1.00      | r2_xboole_0(sK3,X0) = iProver_top
% 3.65/1.00      | v3_ordinal1(X0) != iProver_top
% 3.65/1.00      | v3_ordinal1(sK3) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_1149]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1152,plain,
% 3.65/1.00      ( sK2 = sK3
% 3.65/1.00      | r2_xboole_0(sK3,sK2) = iProver_top
% 3.65/1.00      | r2_xboole_0(sK2,sK3) = iProver_top
% 3.65/1.00      | v3_ordinal1(sK3) != iProver_top
% 3.65/1.00      | v3_ordinal1(sK2) != iProver_top ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_1150]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_3269,plain,
% 3.65/1.00      ( r2_hidden(sK3,X0)
% 3.65/1.00      | ~ r2_xboole_0(sK3,X0)
% 3.65/1.00      | ~ v3_ordinal1(X0)
% 3.65/1.00      | ~ v3_ordinal1(sK3) ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_288]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_3275,plain,
% 3.65/1.00      ( r2_hidden(sK3,X0) = iProver_top
% 3.65/1.00      | r2_xboole_0(sK3,X0) != iProver_top
% 3.65/1.00      | v3_ordinal1(X0) != iProver_top
% 3.65/1.00      | v3_ordinal1(sK3) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_3269]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_3277,plain,
% 3.65/1.00      ( r2_hidden(sK3,sK2) = iProver_top
% 3.65/1.00      | r2_xboole_0(sK3,sK2) != iProver_top
% 3.65/1.00      | v3_ordinal1(sK3) != iProver_top
% 3.65/1.00      | v3_ordinal1(sK2) != iProver_top ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_3275]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_13115,plain,
% 3.65/1.00      ( r2_hidden(X0,sK3)
% 3.65/1.00      | ~ r2_xboole_0(X0,sK3)
% 3.65/1.00      | ~ v3_ordinal1(X0)
% 3.65/1.00      | ~ v3_ordinal1(sK3) ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_288]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_13119,plain,
% 3.65/1.00      ( r2_hidden(X0,sK3) = iProver_top
% 3.65/1.00      | r2_xboole_0(X0,sK3) != iProver_top
% 3.65/1.00      | v3_ordinal1(X0) != iProver_top
% 3.65/1.00      | v3_ordinal1(sK3) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_13115]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_13121,plain,
% 3.65/1.00      ( r2_hidden(sK2,sK3) = iProver_top
% 3.65/1.00      | r2_xboole_0(sK2,sK3) != iProver_top
% 3.65/1.00      | v3_ordinal1(sK3) != iProver_top
% 3.65/1.00      | v3_ordinal1(sK2) != iProver_top ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_13119]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17576,plain,
% 3.65/1.00      ( ~ r2_hidden(sK3,X0)
% 3.65/1.00      | ~ v3_ordinal1(X0)
% 3.65/1.00      | k1_wellord1(k1_wellord2(X0),sK3) = sK3 ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_147]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17578,plain,
% 3.65/1.00      ( k1_wellord1(k1_wellord2(X0),sK3) = sK3
% 3.65/1.00      | r2_hidden(sK3,X0) != iProver_top
% 3.65/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_17576]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17580,plain,
% 3.65/1.00      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.65/1.00      | r2_hidden(sK3,sK2) != iProver_top
% 3.65/1.00      | v3_ordinal1(sK2) != iProver_top ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_17578]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17736,plain,
% 3.65/1.00      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.65/1.00      | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_17681,c_27,c_28,c_23,c_1152,c_3277,c_13121,c_17580]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17742,plain,
% 3.65/1.00      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.65/1.00      | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_17706,c_17736]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_24,negated_conjecture,
% 3.65/1.00      ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) ),
% 3.65/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17076,plain,
% 3.65/1.00      ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_10,plain,
% 3.65/1.00      ( ~ r4_wellord1(X0,X1)
% 3.65/1.00      | r4_wellord1(X1,X0)
% 3.65/1.00      | ~ v1_relat_1(X1)
% 3.65/1.00      | ~ v1_relat_1(X0) ),
% 3.65/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17079,plain,
% 3.65/1.00      ( r4_wellord1(X0,X1) != iProver_top
% 3.65/1.00      | r4_wellord1(X1,X0) = iProver_top
% 3.65/1.00      | v1_relat_1(X0) != iProver_top
% 3.65/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17227,plain,
% 3.65/1.00      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top
% 3.65/1.00      | v1_relat_1(k1_wellord2(sK3)) != iProver_top
% 3.65/1.00      | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_17076,c_17079]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_29,plain,
% 3.65/1.00      ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_45,plain,
% 3.65/1.00      ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_47,plain,
% 3.65/1.00      ( v1_relat_1(k1_wellord2(sK2)) = iProver_top ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_45]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17172,plain,
% 3.65/1.00      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2))
% 3.65/1.00      | ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
% 3.65/1.00      | ~ v1_relat_1(k1_wellord2(sK3))
% 3.65/1.00      | ~ v1_relat_1(k1_wellord2(sK2)) ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17173,plain,
% 3.65/1.00      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top
% 3.65/1.00      | r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) != iProver_top
% 3.65/1.00      | v1_relat_1(k1_wellord2(sK3)) != iProver_top
% 3.65/1.00      | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_17172]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17231,plain,
% 3.65/1.00      ( v1_relat_1(k1_wellord2(sK3)) != iProver_top
% 3.65/1.00      | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_17227,c_29,c_47,c_17173]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17232,plain,
% 3.65/1.00      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top
% 3.65/1.00      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 3.65/1.00      inference(renaming,[status(thm)],[c_17231]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17078,plain,
% 3.65/1.00      ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17237,plain,
% 3.65/1.00      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top ),
% 3.65/1.00      inference(forward_subsumption_resolution,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_17232,c_17078]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17750,plain,
% 3.65/1.00      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_17742,c_17237]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17753,plain,
% 3.65/1.00      ( r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top
% 3.65/1.00      | r2_hidden(sK3,sK2) != iProver_top
% 3.65/1.00      | v3_ordinal1(sK2) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_17750,c_17145]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17758,plain,
% 3.65/1.00      ( r2_hidden(sK3,sK2) != iProver_top
% 3.65/1.00      | r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_17753,c_27]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17759,plain,
% 3.65/1.00      ( r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top
% 3.65/1.00      | r2_hidden(sK3,sK2) != iProver_top ),
% 3.65/1.00      inference(renaming,[status(thm)],[c_17758]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17764,plain,
% 3.65/1.00      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.65/1.00      | r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) != iProver_top
% 3.65/1.00      | r2_hidden(sK3,sK2) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_17728,c_17759]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1151,plain,
% 3.65/1.00      ( r2_xboole_0(sK3,sK2)
% 3.65/1.00      | r2_xboole_0(sK2,sK3)
% 3.65/1.00      | ~ v3_ordinal1(sK3)
% 3.65/1.00      | ~ v3_ordinal1(sK2)
% 3.65/1.00      | sK2 = sK3 ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_1149]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_3276,plain,
% 3.65/1.00      ( r2_hidden(sK3,sK2)
% 3.65/1.00      | ~ r2_xboole_0(sK3,sK2)
% 3.65/1.00      | ~ v3_ordinal1(sK3)
% 3.65/1.00      | ~ v3_ordinal1(sK2) ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_3269]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_13120,plain,
% 3.65/1.00      ( r2_hidden(sK2,sK3)
% 3.65/1.00      | ~ r2_xboole_0(sK2,sK3)
% 3.65/1.00      | ~ v3_ordinal1(sK3)
% 3.65/1.00      | ~ v3_ordinal1(sK2) ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_13115]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17240,plain,
% 3.65/1.00      ( ~ r2_hidden(X0,sK3)
% 3.65/1.00      | ~ v3_ordinal1(sK3)
% 3.65/1.00      | k1_wellord1(k1_wellord2(sK3),X0) = X0 ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_147]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17245,plain,
% 3.65/1.00      ( ~ r2_hidden(sK2,sK3)
% 3.65/1.00      | ~ v3_ordinal1(sK3)
% 3.65/1.00      | k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_17240]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17765,plain,
% 3.65/1.00      ( ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
% 3.65/1.00      | ~ r2_hidden(sK3,sK2)
% 3.65/1.00      | k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
% 3.65/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_17764]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17768,plain,
% 3.65/1.00      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_17764,c_26,c_25,c_24,c_23,c_1151,c_3276,c_13120,
% 3.65/1.00                 c_17245,c_17765]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17771,plain,
% 3.65/1.00      ( r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top
% 3.65/1.00      | r2_hidden(sK2,sK3) != iProver_top
% 3.65/1.00      | v3_ordinal1(sK3) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_17768,c_17145]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17774,plain,
% 3.65/1.00      ( r2_hidden(sK2,sK3) != iProver_top
% 3.65/1.00      | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_17771,c_28]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17775,plain,
% 3.65/1.00      ( r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top
% 3.65/1.00      | r2_hidden(sK2,sK3) != iProver_top ),
% 3.65/1.00      inference(renaming,[status(thm)],[c_17774]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17891,plain,
% 3.65/1.00      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.65/1.00      | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) != iProver_top
% 3.65/1.00      | r2_hidden(sK2,sK3) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_17888,c_17775]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_11147,plain,
% 3.65/1.00      ( r1_tarski(sK3,X0) | ~ r2_xboole_0(sK3,X0) ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_11149,plain,
% 3.65/1.00      ( r1_tarski(sK3,sK2) | ~ r2_xboole_0(sK3,sK2) ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_11147]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_15593,plain,
% 3.65/1.00      ( ~ r1_tarski(sK3,X0)
% 3.65/1.00      | k2_wellord1(k1_wellord2(X0),sK3) = k1_wellord2(sK3) ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_22]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_15598,plain,
% 3.65/1.00      ( ~ r1_tarski(sK3,sK2)
% 3.65/1.00      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_15593]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17238,plain,
% 3.65/1.00      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) ),
% 3.65/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_17237]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17892,plain,
% 3.65/1.00      ( ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2))
% 3.65/1.00      | ~ r2_hidden(sK2,sK3)
% 3.65/1.00      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
% 3.65/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_17891]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17906,plain,
% 3.65/1.00      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_17891,c_26,c_25,c_23,c_1151,c_11149,c_13120,c_15598,
% 3.65/1.00                 c_17238,c_17892]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17909,plain,
% 3.65/1.00      ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) != iProver_top
% 3.65/1.00      | r2_hidden(sK3,sK2) != iProver_top ),
% 3.65/1.00      inference(demodulation,[status(thm)],[c_17906,c_17759]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17912,plain,
% 3.65/1.00      ( r2_hidden(sK3,sK2) != iProver_top ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_17909,c_29]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17920,plain,
% 3.65/1.00      ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
% 3.65/1.00      | sK3 = sK2
% 3.65/1.00      | v3_ordinal1(sK3) != iProver_top
% 3.65/1.00      | v3_ordinal1(sK2) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_17451,c_17912]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_11396,plain,
% 3.65/1.00      ( r1_tarski(X0,sK3) | ~ r2_xboole_0(X0,sK3) ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_11397,plain,
% 3.65/1.00      ( r1_tarski(X0,sK3) = iProver_top
% 3.65/1.00      | r2_xboole_0(X0,sK3) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_11396]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_11399,plain,
% 3.65/1.00      ( r1_tarski(sK2,sK3) = iProver_top
% 3.65/1.00      | r2_xboole_0(sK2,sK3) != iProver_top ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_11397]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_14888,plain,
% 3.65/1.00      ( ~ r1_tarski(X0,sK3)
% 3.65/1.00      | k2_wellord1(k1_wellord2(sK3),X0) = k1_wellord2(X0) ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_22]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_14889,plain,
% 3.65/1.00      ( k2_wellord1(k1_wellord2(sK3),X0) = k1_wellord2(X0)
% 3.65/1.00      | r1_tarski(X0,sK3) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_14888]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_14891,plain,
% 3.65/1.00      ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
% 3.65/1.00      | r1_tarski(sK2,sK3) != iProver_top ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_14889]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17965,plain,
% 3.65/1.00      ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2) ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_17920,c_27,c_28,c_29,c_23,c_1152,c_3277,c_11399,
% 3.65/1.00                 c_14891,c_17909]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17968,plain,
% 3.65/1.00      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) != iProver_top
% 3.65/1.00      | r2_hidden(sK2,sK3) != iProver_top ),
% 3.65/1.00      inference(demodulation,[status(thm)],[c_17965,c_17775]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(contradiction,plain,
% 3.65/1.00      ( $false ),
% 3.65/1.00      inference(minisat,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_17968,c_17909,c_17237,c_13121,c_3277,c_1152,c_23,c_29,
% 3.65/1.00                 c_28,c_27]) ).
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.65/1.00  
% 3.65/1.00  ------                               Statistics
% 3.65/1.00  
% 3.65/1.00  ------ Selected
% 3.65/1.00  
% 3.65/1.00  total_time:                             0.362
% 3.65/1.00  
%------------------------------------------------------------------------------
