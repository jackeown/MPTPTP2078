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
% DateTime   : Thu Dec  3 11:59:46 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :  165 (3667 expanded)
%              Number of clauses        :  107 (1317 expanded)
%              Number of leaves         :   18 ( 797 expanded)
%              Depth                    :   28
%              Number of atoms          :  558 (13844 expanded)
%              Number of equality atoms :  263 (4634 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   17 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_xboole_0(X1,X0)
              & X0 != X1
              & ~ r2_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_xboole_0(X1,X0)
          | X0 = X1
          | r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_xboole_0(X1,X0)
          | X0 = X1
          | r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X1,X0)
      | X0 = X1
      | r2_xboole_0(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
     => ( sK3 != X0
        & r4_wellord1(k1_wellord2(X0),k1_wellord2(sK3))
        & v3_ordinal1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
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

fof(f40,plain,
    ( sK2 != sK3
    & r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
    & v3_ordinal1(sK3)
    & v3_ordinal1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f32,f39,f38])).

fof(f59,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f60,plain,(
    v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
           => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_wellord1(k1_wellord2(X1),X0) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f62,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f40])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f63,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f61,plain,(
    r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r4_wellord1(X1,X0)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f57,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
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

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f36,plain,(
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

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f36])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f70,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f48])).

cnf(c_2,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1298,plain,
    ( X0 = X1
    | r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( r2_xboole_0(X0,X1)
    | r2_xboole_0(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1297,plain,
    ( X0 = X1
    | r2_xboole_0(X0,X1) = iProver_top
    | r2_xboole_0(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1299,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2270,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) = iProver_top
    | r2_xboole_0(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1297,c_1299])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1296,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2449,plain,
    ( X0 = X1
    | r2_hidden(X0,X1) != iProver_top
    | r2_xboole_0(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2270,c_1296])).

cnf(c_2746,plain,
    ( X0 = X1
    | r2_hidden(X0,X1) = iProver_top
    | r2_xboole_0(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1298,c_2449])).

cnf(c_21,negated_conjecture,
    ( v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1283,plain,
    ( v3_ordinal1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1284,plain,
    ( v3_ordinal1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | k1_wellord1(k1_wellord2(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1287,plain,
    ( k1_wellord1(k1_wellord2(X0),X1) = X1
    | r2_hidden(X1,X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2378,plain,
    ( X0 = X1
    | k1_wellord1(k1_wellord2(X1),X0) = X0
    | r2_hidden(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1298,c_1287])).

cnf(c_2743,plain,
    ( X0 = X1
    | k1_wellord1(k1_wellord2(X0),X1) = X1
    | r2_xboole_0(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2378,c_2449])).

cnf(c_3126,plain,
    ( X0 = X1
    | k1_wellord1(k1_wellord2(X1),X0) = X0
    | r1_tarski(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2743,c_1299])).

cnf(c_17,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1286,plain,
    ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3223,plain,
    ( X0 = X1
    | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
    | k1_wellord1(k1_wellord2(X0),X1) = X1
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3126,c_1286])).

cnf(c_4036,plain,
    ( k2_wellord1(k1_wellord2(X0),sK3) = k1_wellord2(sK3)
    | k1_wellord1(k1_wellord2(sK3),X0) = X0
    | sK3 = X0
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1284,c_3223])).

cnf(c_4117,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_1283,c_4036])).

cnf(c_18,negated_conjecture,
    ( sK2 != sK3 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_66,plain,
    ( r2_xboole_0(sK2,sK2)
    | ~ v3_ordinal1(sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_75,plain,
    ( ~ r2_xboole_0(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_918,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1481,plain,
    ( sK3 != X0
    | sK2 != X0
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_918])).

cnf(c_1482,plain,
    ( sK3 != sK2
    | sK2 = sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1481])).

cnf(c_4210,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4117,c_21,c_18,c_66,c_75,c_1482])).

cnf(c_4211,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
    inference(renaming,[status(thm)],[c_4210])).

cnf(c_4037,plain,
    ( k2_wellord1(k1_wellord2(X0),sK2) = k1_wellord2(sK2)
    | k1_wellord1(k1_wellord2(sK2),X0) = X0
    | sK2 = X0
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1283,c_3223])).

cnf(c_4219,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
    | k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_1284,c_4037])).

cnf(c_917,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1567,plain,
    ( k1_wellord2(sK3) = k1_wellord2(sK3) ),
    inference(instantiation,[status(thm)],[c_917])).

cnf(c_19,negated_conjecture,
    ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1285,plain,
    ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5,plain,
    ( ~ r4_wellord1(X0,X1)
    | r4_wellord1(X1,X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1295,plain,
    ( r4_wellord1(X0,X1) != iProver_top
    | r4_wellord1(X1,X0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1836,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1285,c_1295])).

cnf(c_14,plain,
    ( v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_34,plain,
    ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_36,plain,
    ( v1_relat_1(k1_wellord2(sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_1943,plain,
    ( v1_relat_1(k1_wellord2(sK3)) != iProver_top
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1836,c_36])).

cnf(c_1944,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1943])).

cnf(c_1288,plain,
    ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1949,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1944,c_1288])).

cnf(c_2556,plain,
    ( X0 = X1
    | k1_wellord1(k1_wellord2(X1),X0) = X0
    | k1_wellord1(k1_wellord2(X0),X1) = X1
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2378,c_1287])).

cnf(c_3603,plain,
    ( k1_wellord1(k1_wellord2(X0),sK3) = sK3
    | k1_wellord1(k1_wellord2(sK3),X0) = X0
    | sK3 = X0
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1284,c_2556])).

cnf(c_3631,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_1283,c_3603])).

cnf(c_3816,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3631,c_21,c_18,c_66,c_75,c_1482])).

cnf(c_3817,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
    inference(renaming,[status(thm)],[c_3816])).

cnf(c_6,plain,
    ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
    | ~ r2_hidden(X1,k3_relat_1(X0))
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_16,plain,
    ( v2_wellord1(k1_wellord2(X0))
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_243,plain,
    ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
    | ~ r2_hidden(X1,k3_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v3_ordinal1(X2)
    | k1_wellord2(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_16])).

cnf(c_244,plain,
    ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
    | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
    | ~ v1_relat_1(k1_wellord2(X0))
    | ~ v3_ordinal1(X0) ),
    inference(unflattening,[status(thm)],[c_243])).

cnf(c_248,plain,
    ( ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
    | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
    | ~ v3_ordinal1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_244,c_14])).

cnf(c_249,plain,
    ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
    | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
    | ~ v3_ordinal1(X0) ),
    inference(renaming,[status(thm)],[c_248])).

cnf(c_1282,plain,
    ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
    | r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_249])).

cnf(c_13,plain,
    ( ~ v1_relat_1(k1_wellord2(X0))
    | k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_127,plain,
    ( k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_14])).

cnf(c_1375,plain,
    ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1282,c_127])).

cnf(c_3820,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3817,c_1375])).

cnf(c_22,plain,
    ( v3_ordinal1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_23,plain,
    ( v3_ordinal1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1487,plain,
    ( r2_hidden(sK3,sK2)
    | r2_hidden(sK2,sK3)
    | ~ v3_ordinal1(sK3)
    | ~ v3_ordinal1(sK2)
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1488,plain,
    ( sK2 = sK3
    | r2_hidden(sK3,sK2) = iProver_top
    | r2_hidden(sK2,sK3) = iProver_top
    | v3_ordinal1(sK3) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1487])).

cnf(c_1520,plain,
    ( ~ r2_hidden(sK3,sK2)
    | ~ v3_ordinal1(sK3)
    | ~ v3_ordinal1(sK2)
    | k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1521,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | r2_hidden(sK3,sK2) != iProver_top
    | v3_ordinal1(sK3) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1520])).

cnf(c_3894,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3820,c_22,c_23,c_18,c_1488,c_1521])).

cnf(c_922,plain,
    ( ~ r4_wellord1(X0,X1)
    | r4_wellord1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1968,plain,
    ( r4_wellord1(X0,X1)
    | ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2))
    | X0 != k1_wellord2(sK3)
    | X1 != k1_wellord2(sK2) ),
    inference(instantiation,[status(thm)],[c_922])).

cnf(c_2205,plain,
    ( r4_wellord1(k1_wellord2(sK3),X0)
    | ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2))
    | X0 != k1_wellord2(sK2)
    | k1_wellord2(sK3) != k1_wellord2(sK3) ),
    inference(instantiation,[status(thm)],[c_1968])).

cnf(c_4326,plain,
    ( r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2))
    | ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2))
    | k2_wellord1(k1_wellord2(sK3),sK2) != k1_wellord2(sK2)
    | k1_wellord2(sK3) != k1_wellord2(sK3) ),
    inference(instantiation,[status(thm)],[c_2205])).

cnf(c_4327,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK2) != k1_wellord2(sK2)
    | k1_wellord2(sK3) != k1_wellord2(sK3)
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) = iProver_top
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4326])).

cnf(c_4331,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4219,c_21,c_18,c_66,c_75,c_1482,c_1567,c_1949,c_3894,c_4327])).

cnf(c_4334,plain,
    ( r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top
    | r2_hidden(sK3,sK2) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4331,c_1375])).

cnf(c_4504,plain,
    ( r2_hidden(sK3,sK2) != iProver_top
    | r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4334,c_22])).

cnf(c_4505,plain,
    ( r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top
    | r2_hidden(sK3,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4504])).

cnf(c_4510,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) != iProver_top
    | r2_hidden(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4211,c_4505])).

cnf(c_1627,plain,
    ( ~ r2_hidden(sK2,sK3)
    | ~ v3_ordinal1(sK3)
    | ~ v3_ordinal1(sK2)
    | k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_4511,plain,
    ( ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
    | ~ r2_hidden(sK3,sK2)
    | k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4510])).

cnf(c_4513,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4510,c_21,c_20,c_19,c_18,c_1487,c_1627,c_4511])).

cnf(c_4516,plain,
    ( r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4513,c_1375])).

cnf(c_1490,plain,
    ( r2_xboole_0(sK3,sK2)
    | r2_xboole_0(sK2,sK3)
    | ~ v3_ordinal1(sK3)
    | ~ v3_ordinal1(sK2)
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1491,plain,
    ( sK2 = sK3
    | r2_xboole_0(sK3,sK2) = iProver_top
    | r2_xboole_0(sK2,sK3) = iProver_top
    | v3_ordinal1(sK3) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1490])).

cnf(c_1535,plain,
    ( r1_tarski(sK3,sK2)
    | ~ r2_xboole_0(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1536,plain,
    ( r1_tarski(sK3,sK2) = iProver_top
    | r2_xboole_0(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1535])).

cnf(c_1623,plain,
    ( ~ r2_hidden(sK2,sK3)
    | ~ r1_tarski(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1640,plain,
    ( r2_hidden(sK2,sK3) != iProver_top
    | r1_tarski(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1623])).

cnf(c_1655,plain,
    ( r1_tarski(sK2,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1656,plain,
    ( r1_tarski(sK2,sK3) = iProver_top
    | r2_xboole_0(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1655])).

cnf(c_1958,plain,
    ( ~ r1_tarski(sK2,sK3)
    | k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1959,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1958])).

cnf(c_4544,plain,
    ( r2_hidden(sK2,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4516,c_22,c_23,c_18,c_1491,c_1536,c_1567,c_1640,c_1656,c_1949,c_1959,c_4327])).

cnf(c_4552,plain,
    ( sK3 = sK2
    | r2_xboole_0(sK3,sK2) = iProver_top
    | v3_ordinal1(sK3) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2746,c_4544])).

cnf(c_1516,plain,
    ( ~ r2_hidden(sK3,sK2)
    | ~ r1_tarski(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1533,plain,
    ( r2_hidden(sK3,sK2) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1516])).

cnf(c_4574,plain,
    ( r2_xboole_0(sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4552,c_22,c_23,c_18,c_1488,c_1491,c_1533,c_1536,c_1567,c_1640,c_1656,c_1949,c_1959,c_4327,c_4516])).

cnf(c_4579,plain,
    ( r1_tarski(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4574,c_1299])).

cnf(c_4672,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
    inference(superposition,[status(thm)],[c_4579,c_1286])).

cnf(c_4786,plain,
    ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) != iProver_top
    | r2_hidden(sK3,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4672,c_4505])).

cnf(c_24,plain,
    ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4786,c_4544,c_1488,c_18,c_24,c_23,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:41:24 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.36/0.92  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/0.92  
% 2.36/0.92  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.36/0.92  
% 2.36/0.92  ------  iProver source info
% 2.36/0.92  
% 2.36/0.92  git: date: 2020-06-30 10:37:57 +0100
% 2.36/0.92  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.36/0.92  git: non_committed_changes: false
% 2.36/0.92  git: last_make_outside_of_git: false
% 2.36/0.92  
% 2.36/0.92  ------ 
% 2.36/0.92  
% 2.36/0.92  ------ Input Options
% 2.36/0.92  
% 2.36/0.92  --out_options                           all
% 2.36/0.92  --tptp_safe_out                         true
% 2.36/0.92  --problem_path                          ""
% 2.36/0.92  --include_path                          ""
% 2.36/0.92  --clausifier                            res/vclausify_rel
% 2.36/0.92  --clausifier_options                    --mode clausify
% 2.36/0.92  --stdin                                 false
% 2.36/0.92  --stats_out                             all
% 2.36/0.92  
% 2.36/0.92  ------ General Options
% 2.36/0.92  
% 2.36/0.92  --fof                                   false
% 2.36/0.92  --time_out_real                         305.
% 2.36/0.92  --time_out_virtual                      -1.
% 2.36/0.92  --symbol_type_check                     false
% 2.36/0.92  --clausify_out                          false
% 2.36/0.92  --sig_cnt_out                           false
% 2.36/0.92  --trig_cnt_out                          false
% 2.36/0.92  --trig_cnt_out_tolerance                1.
% 2.36/0.92  --trig_cnt_out_sk_spl                   false
% 2.36/0.92  --abstr_cl_out                          false
% 2.36/0.92  
% 2.36/0.92  ------ Global Options
% 2.36/0.92  
% 2.36/0.92  --schedule                              default
% 2.36/0.92  --add_important_lit                     false
% 2.36/0.92  --prop_solver_per_cl                    1000
% 2.36/0.92  --min_unsat_core                        false
% 2.36/0.92  --soft_assumptions                      false
% 2.36/0.92  --soft_lemma_size                       3
% 2.36/0.92  --prop_impl_unit_size                   0
% 2.36/0.92  --prop_impl_unit                        []
% 2.36/0.92  --share_sel_clauses                     true
% 2.36/0.92  --reset_solvers                         false
% 2.36/0.92  --bc_imp_inh                            [conj_cone]
% 2.36/0.92  --conj_cone_tolerance                   3.
% 2.36/0.92  --extra_neg_conj                        none
% 2.36/0.92  --large_theory_mode                     true
% 2.36/0.92  --prolific_symb_bound                   200
% 2.36/0.92  --lt_threshold                          2000
% 2.36/0.92  --clause_weak_htbl                      true
% 2.36/0.92  --gc_record_bc_elim                     false
% 2.36/0.92  
% 2.36/0.92  ------ Preprocessing Options
% 2.36/0.92  
% 2.36/0.92  --preprocessing_flag                    true
% 2.36/0.92  --time_out_prep_mult                    0.1
% 2.36/0.92  --splitting_mode                        input
% 2.36/0.92  --splitting_grd                         true
% 2.36/0.92  --splitting_cvd                         false
% 2.36/0.92  --splitting_cvd_svl                     false
% 2.36/0.92  --splitting_nvd                         32
% 2.36/0.92  --sub_typing                            true
% 2.36/0.92  --prep_gs_sim                           true
% 2.36/0.92  --prep_unflatten                        true
% 2.36/0.92  --prep_res_sim                          true
% 2.36/0.92  --prep_upred                            true
% 2.36/0.92  --prep_sem_filter                       exhaustive
% 2.36/0.92  --prep_sem_filter_out                   false
% 2.36/0.92  --pred_elim                             true
% 2.36/0.92  --res_sim_input                         true
% 2.36/0.92  --eq_ax_congr_red                       true
% 2.36/0.92  --pure_diseq_elim                       true
% 2.36/0.92  --brand_transform                       false
% 2.36/0.92  --non_eq_to_eq                          false
% 2.36/0.92  --prep_def_merge                        true
% 2.36/0.92  --prep_def_merge_prop_impl              false
% 2.36/0.92  --prep_def_merge_mbd                    true
% 2.36/0.92  --prep_def_merge_tr_red                 false
% 2.36/0.92  --prep_def_merge_tr_cl                  false
% 2.36/0.92  --smt_preprocessing                     true
% 2.36/0.92  --smt_ac_axioms                         fast
% 2.36/0.92  --preprocessed_out                      false
% 2.36/0.92  --preprocessed_stats                    false
% 2.36/0.92  
% 2.36/0.92  ------ Abstraction refinement Options
% 2.36/0.92  
% 2.36/0.92  --abstr_ref                             []
% 2.36/0.92  --abstr_ref_prep                        false
% 2.36/0.92  --abstr_ref_until_sat                   false
% 2.36/0.92  --abstr_ref_sig_restrict                funpre
% 2.36/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 2.36/0.92  --abstr_ref_under                       []
% 2.36/0.92  
% 2.36/0.92  ------ SAT Options
% 2.36/0.92  
% 2.36/0.92  --sat_mode                              false
% 2.36/0.92  --sat_fm_restart_options                ""
% 2.36/0.92  --sat_gr_def                            false
% 2.36/0.92  --sat_epr_types                         true
% 2.36/0.92  --sat_non_cyclic_types                  false
% 2.36/0.92  --sat_finite_models                     false
% 2.36/0.92  --sat_fm_lemmas                         false
% 2.36/0.92  --sat_fm_prep                           false
% 2.36/0.92  --sat_fm_uc_incr                        true
% 2.36/0.92  --sat_out_model                         small
% 2.36/0.92  --sat_out_clauses                       false
% 2.36/0.92  
% 2.36/0.92  ------ QBF Options
% 2.36/0.92  
% 2.36/0.92  --qbf_mode                              false
% 2.36/0.92  --qbf_elim_univ                         false
% 2.36/0.92  --qbf_dom_inst                          none
% 2.36/0.92  --qbf_dom_pre_inst                      false
% 2.36/0.92  --qbf_sk_in                             false
% 2.36/0.92  --qbf_pred_elim                         true
% 2.36/0.92  --qbf_split                             512
% 2.36/0.92  
% 2.36/0.92  ------ BMC1 Options
% 2.36/0.92  
% 2.36/0.92  --bmc1_incremental                      false
% 2.36/0.92  --bmc1_axioms                           reachable_all
% 2.36/0.92  --bmc1_min_bound                        0
% 2.36/0.92  --bmc1_max_bound                        -1
% 2.36/0.92  --bmc1_max_bound_default                -1
% 2.36/0.92  --bmc1_symbol_reachability              true
% 2.36/0.92  --bmc1_property_lemmas                  false
% 2.36/0.92  --bmc1_k_induction                      false
% 2.36/0.92  --bmc1_non_equiv_states                 false
% 2.36/0.92  --bmc1_deadlock                         false
% 2.36/0.92  --bmc1_ucm                              false
% 2.36/0.92  --bmc1_add_unsat_core                   none
% 2.36/0.92  --bmc1_unsat_core_children              false
% 2.36/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 2.36/0.92  --bmc1_out_stat                         full
% 2.36/0.92  --bmc1_ground_init                      false
% 2.36/0.92  --bmc1_pre_inst_next_state              false
% 2.36/0.92  --bmc1_pre_inst_state                   false
% 2.36/0.92  --bmc1_pre_inst_reach_state             false
% 2.36/0.92  --bmc1_out_unsat_core                   false
% 2.36/0.92  --bmc1_aig_witness_out                  false
% 2.36/0.92  --bmc1_verbose                          false
% 2.36/0.92  --bmc1_dump_clauses_tptp                false
% 2.36/0.92  --bmc1_dump_unsat_core_tptp             false
% 2.36/0.92  --bmc1_dump_file                        -
% 2.36/0.92  --bmc1_ucm_expand_uc_limit              128
% 2.36/0.92  --bmc1_ucm_n_expand_iterations          6
% 2.36/0.92  --bmc1_ucm_extend_mode                  1
% 2.36/0.92  --bmc1_ucm_init_mode                    2
% 2.36/0.92  --bmc1_ucm_cone_mode                    none
% 2.36/0.92  --bmc1_ucm_reduced_relation_type        0
% 2.36/0.92  --bmc1_ucm_relax_model                  4
% 2.36/0.92  --bmc1_ucm_full_tr_after_sat            true
% 2.36/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 2.36/0.92  --bmc1_ucm_layered_model                none
% 2.36/0.92  --bmc1_ucm_max_lemma_size               10
% 2.36/0.92  
% 2.36/0.92  ------ AIG Options
% 2.36/0.92  
% 2.36/0.92  --aig_mode                              false
% 2.36/0.92  
% 2.36/0.92  ------ Instantiation Options
% 2.36/0.92  
% 2.36/0.92  --instantiation_flag                    true
% 2.36/0.92  --inst_sos_flag                         false
% 2.36/0.92  --inst_sos_phase                        true
% 2.36/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.36/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.36/0.92  --inst_lit_sel_side                     num_symb
% 2.36/0.92  --inst_solver_per_active                1400
% 2.36/0.92  --inst_solver_calls_frac                1.
% 2.36/0.92  --inst_passive_queue_type               priority_queues
% 2.36/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.36/0.92  --inst_passive_queues_freq              [25;2]
% 2.36/0.92  --inst_dismatching                      true
% 2.36/0.92  --inst_eager_unprocessed_to_passive     true
% 2.36/0.92  --inst_prop_sim_given                   true
% 2.36/0.92  --inst_prop_sim_new                     false
% 2.36/0.92  --inst_subs_new                         false
% 2.36/0.92  --inst_eq_res_simp                      false
% 2.36/0.92  --inst_subs_given                       false
% 2.36/0.92  --inst_orphan_elimination               true
% 2.36/0.92  --inst_learning_loop_flag               true
% 2.36/0.92  --inst_learning_start                   3000
% 2.36/0.92  --inst_learning_factor                  2
% 2.36/0.92  --inst_start_prop_sim_after_learn       3
% 2.36/0.92  --inst_sel_renew                        solver
% 2.36/0.92  --inst_lit_activity_flag                true
% 2.36/0.92  --inst_restr_to_given                   false
% 2.36/0.92  --inst_activity_threshold               500
% 2.36/0.92  --inst_out_proof                        true
% 2.36/0.92  
% 2.36/0.92  ------ Resolution Options
% 2.36/0.92  
% 2.36/0.92  --resolution_flag                       true
% 2.36/0.92  --res_lit_sel                           adaptive
% 2.36/0.92  --res_lit_sel_side                      none
% 2.36/0.92  --res_ordering                          kbo
% 2.36/0.92  --res_to_prop_solver                    active
% 2.36/0.92  --res_prop_simpl_new                    false
% 2.36/0.92  --res_prop_simpl_given                  true
% 2.36/0.92  --res_passive_queue_type                priority_queues
% 2.36/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.36/0.92  --res_passive_queues_freq               [15;5]
% 2.36/0.92  --res_forward_subs                      full
% 2.36/0.92  --res_backward_subs                     full
% 2.36/0.92  --res_forward_subs_resolution           true
% 2.36/0.92  --res_backward_subs_resolution          true
% 2.36/0.92  --res_orphan_elimination                true
% 2.36/0.92  --res_time_limit                        2.
% 2.36/0.92  --res_out_proof                         true
% 2.36/0.92  
% 2.36/0.92  ------ Superposition Options
% 2.36/0.92  
% 2.36/0.92  --superposition_flag                    true
% 2.36/0.92  --sup_passive_queue_type                priority_queues
% 2.36/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.36/0.92  --sup_passive_queues_freq               [8;1;4]
% 2.36/0.92  --demod_completeness_check              fast
% 2.36/0.92  --demod_use_ground                      true
% 2.36/0.92  --sup_to_prop_solver                    passive
% 2.36/0.92  --sup_prop_simpl_new                    true
% 2.36/0.92  --sup_prop_simpl_given                  true
% 2.36/0.92  --sup_fun_splitting                     false
% 2.36/0.92  --sup_smt_interval                      50000
% 2.36/0.92  
% 2.36/0.92  ------ Superposition Simplification Setup
% 2.36/0.92  
% 2.36/0.92  --sup_indices_passive                   []
% 2.36/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 2.36/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/0.92  --sup_full_bw                           [BwDemod]
% 2.36/0.92  --sup_immed_triv                        [TrivRules]
% 2.36/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.36/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/0.92  --sup_immed_bw_main                     []
% 2.36/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 2.36/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/0.92  
% 2.36/0.92  ------ Combination Options
% 2.36/0.92  
% 2.36/0.92  --comb_res_mult                         3
% 2.36/0.92  --comb_sup_mult                         2
% 2.36/0.92  --comb_inst_mult                        10
% 2.36/0.92  
% 2.36/0.92  ------ Debug Options
% 2.36/0.92  
% 2.36/0.92  --dbg_backtrace                         false
% 2.36/0.92  --dbg_dump_prop_clauses                 false
% 2.36/0.92  --dbg_dump_prop_clauses_file            -
% 2.36/0.92  --dbg_out_stat                          false
% 2.36/0.92  ------ Parsing...
% 2.36/0.92  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.36/0.92  
% 2.36/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.36/0.92  
% 2.36/0.92  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.36/0.92  
% 2.36/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.36/0.92  ------ Proving...
% 2.36/0.92  ------ Problem Properties 
% 2.36/0.92  
% 2.36/0.92  
% 2.36/0.92  clauses                                 21
% 2.36/0.92  conjectures                             4
% 2.36/0.92  EPR                                     9
% 2.36/0.92  Horn                                    16
% 2.36/0.92  unary                                   7
% 2.36/0.92  binary                                  3
% 2.36/0.92  lits                                    58
% 2.36/0.92  lits eq                                 10
% 2.36/0.92  fd_pure                                 0
% 2.36/0.92  fd_pseudo                               0
% 2.36/0.92  fd_cond                                 0
% 2.36/0.92  fd_pseudo_cond                          2
% 2.36/0.92  AC symbols                              0
% 2.36/0.92  
% 2.36/0.92  ------ Schedule dynamic 5 is on 
% 2.36/0.92  
% 2.36/0.92  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.36/0.92  
% 2.36/0.92  
% 2.36/0.92  ------ 
% 2.36/0.92  Current options:
% 2.36/0.92  ------ 
% 2.36/0.92  
% 2.36/0.92  ------ Input Options
% 2.36/0.92  
% 2.36/0.92  --out_options                           all
% 2.36/0.92  --tptp_safe_out                         true
% 2.36/0.92  --problem_path                          ""
% 2.36/0.92  --include_path                          ""
% 2.36/0.92  --clausifier                            res/vclausify_rel
% 2.36/0.92  --clausifier_options                    --mode clausify
% 2.36/0.92  --stdin                                 false
% 2.36/0.92  --stats_out                             all
% 2.36/0.92  
% 2.36/0.92  ------ General Options
% 2.36/0.92  
% 2.36/0.92  --fof                                   false
% 2.36/0.92  --time_out_real                         305.
% 2.36/0.92  --time_out_virtual                      -1.
% 2.36/0.92  --symbol_type_check                     false
% 2.36/0.92  --clausify_out                          false
% 2.36/0.92  --sig_cnt_out                           false
% 2.36/0.92  --trig_cnt_out                          false
% 2.36/0.92  --trig_cnt_out_tolerance                1.
% 2.36/0.92  --trig_cnt_out_sk_spl                   false
% 2.36/0.92  --abstr_cl_out                          false
% 2.36/0.92  
% 2.36/0.92  ------ Global Options
% 2.36/0.92  
% 2.36/0.92  --schedule                              default
% 2.36/0.92  --add_important_lit                     false
% 2.36/0.92  --prop_solver_per_cl                    1000
% 2.36/0.92  --min_unsat_core                        false
% 2.36/0.92  --soft_assumptions                      false
% 2.36/0.92  --soft_lemma_size                       3
% 2.36/0.92  --prop_impl_unit_size                   0
% 2.36/0.92  --prop_impl_unit                        []
% 2.36/0.92  --share_sel_clauses                     true
% 2.36/0.92  --reset_solvers                         false
% 2.36/0.92  --bc_imp_inh                            [conj_cone]
% 2.36/0.92  --conj_cone_tolerance                   3.
% 2.36/0.92  --extra_neg_conj                        none
% 2.36/0.92  --large_theory_mode                     true
% 2.36/0.92  --prolific_symb_bound                   200
% 2.36/0.92  --lt_threshold                          2000
% 2.36/0.92  --clause_weak_htbl                      true
% 2.36/0.92  --gc_record_bc_elim                     false
% 2.36/0.92  
% 2.36/0.92  ------ Preprocessing Options
% 2.36/0.92  
% 2.36/0.92  --preprocessing_flag                    true
% 2.36/0.92  --time_out_prep_mult                    0.1
% 2.36/0.92  --splitting_mode                        input
% 2.36/0.92  --splitting_grd                         true
% 2.36/0.92  --splitting_cvd                         false
% 2.36/0.92  --splitting_cvd_svl                     false
% 2.36/0.92  --splitting_nvd                         32
% 2.36/0.92  --sub_typing                            true
% 2.36/0.92  --prep_gs_sim                           true
% 2.36/0.92  --prep_unflatten                        true
% 2.36/0.92  --prep_res_sim                          true
% 2.36/0.92  --prep_upred                            true
% 2.36/0.92  --prep_sem_filter                       exhaustive
% 2.36/0.92  --prep_sem_filter_out                   false
% 2.36/0.92  --pred_elim                             true
% 2.36/0.92  --res_sim_input                         true
% 2.36/0.92  --eq_ax_congr_red                       true
% 2.36/0.92  --pure_diseq_elim                       true
% 2.36/0.92  --brand_transform                       false
% 2.36/0.92  --non_eq_to_eq                          false
% 2.36/0.92  --prep_def_merge                        true
% 2.36/0.92  --prep_def_merge_prop_impl              false
% 2.36/0.92  --prep_def_merge_mbd                    true
% 2.36/0.92  --prep_def_merge_tr_red                 false
% 2.36/0.92  --prep_def_merge_tr_cl                  false
% 2.36/0.92  --smt_preprocessing                     true
% 2.36/0.92  --smt_ac_axioms                         fast
% 2.36/0.92  --preprocessed_out                      false
% 2.36/0.92  --preprocessed_stats                    false
% 2.36/0.92  
% 2.36/0.92  ------ Abstraction refinement Options
% 2.36/0.92  
% 2.36/0.92  --abstr_ref                             []
% 2.36/0.92  --abstr_ref_prep                        false
% 2.36/0.92  --abstr_ref_until_sat                   false
% 2.36/0.92  --abstr_ref_sig_restrict                funpre
% 2.36/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 2.36/0.92  --abstr_ref_under                       []
% 2.36/0.92  
% 2.36/0.92  ------ SAT Options
% 2.36/0.92  
% 2.36/0.92  --sat_mode                              false
% 2.36/0.92  --sat_fm_restart_options                ""
% 2.36/0.92  --sat_gr_def                            false
% 2.36/0.92  --sat_epr_types                         true
% 2.36/0.92  --sat_non_cyclic_types                  false
% 2.36/0.92  --sat_finite_models                     false
% 2.36/0.92  --sat_fm_lemmas                         false
% 2.36/0.92  --sat_fm_prep                           false
% 2.36/0.92  --sat_fm_uc_incr                        true
% 2.36/0.92  --sat_out_model                         small
% 2.36/0.92  --sat_out_clauses                       false
% 2.36/0.92  
% 2.36/0.92  ------ QBF Options
% 2.36/0.92  
% 2.36/0.92  --qbf_mode                              false
% 2.36/0.92  --qbf_elim_univ                         false
% 2.36/0.92  --qbf_dom_inst                          none
% 2.36/0.92  --qbf_dom_pre_inst                      false
% 2.36/0.92  --qbf_sk_in                             false
% 2.36/0.92  --qbf_pred_elim                         true
% 2.36/0.92  --qbf_split                             512
% 2.36/0.92  
% 2.36/0.92  ------ BMC1 Options
% 2.36/0.92  
% 2.36/0.92  --bmc1_incremental                      false
% 2.36/0.92  --bmc1_axioms                           reachable_all
% 2.36/0.92  --bmc1_min_bound                        0
% 2.36/0.92  --bmc1_max_bound                        -1
% 2.36/0.92  --bmc1_max_bound_default                -1
% 2.36/0.92  --bmc1_symbol_reachability              true
% 2.36/0.92  --bmc1_property_lemmas                  false
% 2.36/0.92  --bmc1_k_induction                      false
% 2.36/0.92  --bmc1_non_equiv_states                 false
% 2.36/0.92  --bmc1_deadlock                         false
% 2.36/0.92  --bmc1_ucm                              false
% 2.36/0.92  --bmc1_add_unsat_core                   none
% 2.36/0.92  --bmc1_unsat_core_children              false
% 2.36/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 2.36/0.92  --bmc1_out_stat                         full
% 2.36/0.92  --bmc1_ground_init                      false
% 2.36/0.92  --bmc1_pre_inst_next_state              false
% 2.36/0.92  --bmc1_pre_inst_state                   false
% 2.36/0.92  --bmc1_pre_inst_reach_state             false
% 2.36/0.92  --bmc1_out_unsat_core                   false
% 2.36/0.92  --bmc1_aig_witness_out                  false
% 2.36/0.92  --bmc1_verbose                          false
% 2.36/0.92  --bmc1_dump_clauses_tptp                false
% 2.36/0.92  --bmc1_dump_unsat_core_tptp             false
% 2.36/0.92  --bmc1_dump_file                        -
% 2.36/0.92  --bmc1_ucm_expand_uc_limit              128
% 2.36/0.92  --bmc1_ucm_n_expand_iterations          6
% 2.36/0.92  --bmc1_ucm_extend_mode                  1
% 2.36/0.92  --bmc1_ucm_init_mode                    2
% 2.36/0.92  --bmc1_ucm_cone_mode                    none
% 2.36/0.92  --bmc1_ucm_reduced_relation_type        0
% 2.36/0.92  --bmc1_ucm_relax_model                  4
% 2.36/0.92  --bmc1_ucm_full_tr_after_sat            true
% 2.36/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 2.36/0.92  --bmc1_ucm_layered_model                none
% 2.36/0.92  --bmc1_ucm_max_lemma_size               10
% 2.36/0.92  
% 2.36/0.92  ------ AIG Options
% 2.36/0.92  
% 2.36/0.92  --aig_mode                              false
% 2.36/0.92  
% 2.36/0.92  ------ Instantiation Options
% 2.36/0.92  
% 2.36/0.92  --instantiation_flag                    true
% 2.36/0.92  --inst_sos_flag                         false
% 2.36/0.92  --inst_sos_phase                        true
% 2.36/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.36/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.36/0.92  --inst_lit_sel_side                     none
% 2.36/0.92  --inst_solver_per_active                1400
% 2.36/0.92  --inst_solver_calls_frac                1.
% 2.36/0.92  --inst_passive_queue_type               priority_queues
% 2.36/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.36/0.92  --inst_passive_queues_freq              [25;2]
% 2.36/0.92  --inst_dismatching                      true
% 2.36/0.92  --inst_eager_unprocessed_to_passive     true
% 2.36/0.92  --inst_prop_sim_given                   true
% 2.36/0.92  --inst_prop_sim_new                     false
% 2.36/0.92  --inst_subs_new                         false
% 2.36/0.92  --inst_eq_res_simp                      false
% 2.36/0.92  --inst_subs_given                       false
% 2.36/0.92  --inst_orphan_elimination               true
% 2.36/0.92  --inst_learning_loop_flag               true
% 2.36/0.92  --inst_learning_start                   3000
% 2.36/0.92  --inst_learning_factor                  2
% 2.36/0.92  --inst_start_prop_sim_after_learn       3
% 2.36/0.92  --inst_sel_renew                        solver
% 2.36/0.92  --inst_lit_activity_flag                true
% 2.36/0.92  --inst_restr_to_given                   false
% 2.36/0.92  --inst_activity_threshold               500
% 2.36/0.92  --inst_out_proof                        true
% 2.36/0.92  
% 2.36/0.92  ------ Resolution Options
% 2.36/0.92  
% 2.36/0.92  --resolution_flag                       false
% 2.36/0.92  --res_lit_sel                           adaptive
% 2.36/0.92  --res_lit_sel_side                      none
% 2.36/0.92  --res_ordering                          kbo
% 2.36/0.92  --res_to_prop_solver                    active
% 2.36/0.92  --res_prop_simpl_new                    false
% 2.36/0.92  --res_prop_simpl_given                  true
% 2.36/0.92  --res_passive_queue_type                priority_queues
% 2.36/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.36/0.92  --res_passive_queues_freq               [15;5]
% 2.36/0.92  --res_forward_subs                      full
% 2.36/0.92  --res_backward_subs                     full
% 2.36/0.92  --res_forward_subs_resolution           true
% 2.36/0.92  --res_backward_subs_resolution          true
% 2.36/0.92  --res_orphan_elimination                true
% 2.36/0.92  --res_time_limit                        2.
% 2.36/0.92  --res_out_proof                         true
% 2.36/0.92  
% 2.36/0.92  ------ Superposition Options
% 2.36/0.92  
% 2.36/0.92  --superposition_flag                    true
% 2.36/0.92  --sup_passive_queue_type                priority_queues
% 2.36/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.36/0.92  --sup_passive_queues_freq               [8;1;4]
% 2.36/0.92  --demod_completeness_check              fast
% 2.36/0.92  --demod_use_ground                      true
% 2.36/0.92  --sup_to_prop_solver                    passive
% 2.36/0.92  --sup_prop_simpl_new                    true
% 2.36/0.92  --sup_prop_simpl_given                  true
% 2.36/0.92  --sup_fun_splitting                     false
% 2.36/0.92  --sup_smt_interval                      50000
% 2.36/0.92  
% 2.36/0.92  ------ Superposition Simplification Setup
% 2.36/0.92  
% 2.36/0.92  --sup_indices_passive                   []
% 2.36/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 2.36/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/0.92  --sup_full_bw                           [BwDemod]
% 2.36/0.92  --sup_immed_triv                        [TrivRules]
% 2.36/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.36/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/0.92  --sup_immed_bw_main                     []
% 2.36/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 2.36/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/0.92  
% 2.36/0.92  ------ Combination Options
% 2.36/0.92  
% 2.36/0.92  --comb_res_mult                         3
% 2.36/0.92  --comb_sup_mult                         2
% 2.36/0.92  --comb_inst_mult                        10
% 2.36/0.92  
% 2.36/0.92  ------ Debug Options
% 2.36/0.92  
% 2.36/0.92  --dbg_backtrace                         false
% 2.36/0.92  --dbg_dump_prop_clauses                 false
% 2.36/0.92  --dbg_dump_prop_clauses_file            -
% 2.36/0.92  --dbg_out_stat                          false
% 2.36/0.92  
% 2.36/0.92  
% 2.36/0.92  
% 2.36/0.92  
% 2.36/0.92  ------ Proving...
% 2.36/0.92  
% 2.36/0.92  
% 2.36/0.92  % SZS status Theorem for theBenchmark.p
% 2.36/0.92  
% 2.36/0.92  % SZS output start CNFRefutation for theBenchmark.p
% 2.36/0.92  
% 2.36/0.92  fof(f2,axiom,(
% 2.36/0.92    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 2.36/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.92  
% 2.36/0.92  fof(f16,plain,(
% 2.36/0.92    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.36/0.92    inference(ennf_transformation,[],[f2])).
% 2.36/0.92  
% 2.36/0.92  fof(f17,plain,(
% 2.36/0.92    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.36/0.92    inference(flattening,[],[f16])).
% 2.36/0.92  
% 2.36/0.92  fof(f43,plain,(
% 2.36/0.92    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.36/0.92    inference(cnf_transformation,[],[f17])).
% 2.36/0.92  
% 2.36/0.92  fof(f3,axiom,(
% 2.36/0.92    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1))))),
% 2.36/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.92  
% 2.36/0.92  fof(f18,plain,(
% 2.36/0.92    ! [X0] : (! [X1] : ((r2_xboole_0(X1,X0) | X0 = X1 | r2_xboole_0(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.36/0.92    inference(ennf_transformation,[],[f3])).
% 2.36/0.92  
% 2.36/0.92  fof(f19,plain,(
% 2.36/0.92    ! [X0] : (! [X1] : (r2_xboole_0(X1,X0) | X0 = X1 | r2_xboole_0(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.36/0.92    inference(flattening,[],[f18])).
% 2.36/0.92  
% 2.36/0.92  fof(f44,plain,(
% 2.36/0.92    ( ! [X0,X1] : (r2_xboole_0(X1,X0) | X0 = X1 | r2_xboole_0(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.36/0.92    inference(cnf_transformation,[],[f19])).
% 2.36/0.92  
% 2.36/0.92  fof(f1,axiom,(
% 2.36/0.92    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 2.36/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.92  
% 2.36/0.92  fof(f14,plain,(
% 2.36/0.92    ! [X0,X1] : (r2_xboole_0(X0,X1) => (X0 != X1 & r1_tarski(X0,X1)))),
% 2.36/0.92    inference(unused_predicate_definition_removal,[],[f1])).
% 2.36/0.92  
% 2.36/0.92  fof(f15,plain,(
% 2.36/0.92    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1))),
% 2.36/0.92    inference(ennf_transformation,[],[f14])).
% 2.36/0.92  
% 2.36/0.92  fof(f41,plain,(
% 2.36/0.92    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 2.36/0.92    inference(cnf_transformation,[],[f15])).
% 2.36/0.92  
% 2.36/0.92  fof(f4,axiom,(
% 2.36/0.92    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.36/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.92  
% 2.36/0.92  fof(f20,plain,(
% 2.36/0.92    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.36/0.92    inference(ennf_transformation,[],[f4])).
% 2.36/0.92  
% 2.36/0.92  fof(f45,plain,(
% 2.36/0.92    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.36/0.92    inference(cnf_transformation,[],[f20])).
% 2.36/0.92  
% 2.36/0.92  fof(f12,conjecture,(
% 2.36/0.92    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 2.36/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.92  
% 2.36/0.92  fof(f13,negated_conjecture,(
% 2.36/0.92    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 2.36/0.92    inference(negated_conjecture,[],[f12])).
% 2.36/0.92  
% 2.36/0.92  fof(f31,plain,(
% 2.36/0.92    ? [X0] : (? [X1] : ((X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.36/0.92    inference(ennf_transformation,[],[f13])).
% 2.36/0.92  
% 2.36/0.92  fof(f32,plain,(
% 2.36/0.92    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.36/0.92    inference(flattening,[],[f31])).
% 2.36/0.92  
% 2.36/0.92  fof(f39,plain,(
% 2.36/0.92    ( ! [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) => (sK3 != X0 & r4_wellord1(k1_wellord2(X0),k1_wellord2(sK3)) & v3_ordinal1(sK3))) )),
% 2.36/0.92    introduced(choice_axiom,[])).
% 2.36/0.92  
% 2.36/0.92  fof(f38,plain,(
% 2.36/0.92    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : (sK2 != X1 & r4_wellord1(k1_wellord2(sK2),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK2))),
% 2.36/0.92    introduced(choice_axiom,[])).
% 2.36/0.92  
% 2.36/0.92  fof(f40,plain,(
% 2.36/0.92    (sK2 != sK3 & r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) & v3_ordinal1(sK3)) & v3_ordinal1(sK2)),
% 2.36/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f32,f39,f38])).
% 2.36/0.92  
% 2.36/0.92  fof(f59,plain,(
% 2.36/0.92    v3_ordinal1(sK2)),
% 2.36/0.92    inference(cnf_transformation,[],[f40])).
% 2.36/0.92  
% 2.36/0.92  fof(f60,plain,(
% 2.36/0.92    v3_ordinal1(sK3)),
% 2.36/0.92    inference(cnf_transformation,[],[f40])).
% 2.36/0.92  
% 2.36/0.92  fof(f9,axiom,(
% 2.36/0.92    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => k1_wellord1(k1_wellord2(X1),X0) = X0)))),
% 2.36/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.92  
% 2.36/0.92  fof(f27,plain,(
% 2.36/0.92    ! [X0] : (! [X1] : ((k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.36/0.92    inference(ennf_transformation,[],[f9])).
% 2.36/0.92  
% 2.36/0.92  fof(f28,plain,(
% 2.36/0.92    ! [X0] : (! [X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.36/0.92    inference(flattening,[],[f27])).
% 2.36/0.92  
% 2.36/0.92  fof(f56,plain,(
% 2.36/0.92    ( ! [X0,X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.36/0.92    inference(cnf_transformation,[],[f28])).
% 2.36/0.92  
% 2.36/0.92  fof(f11,axiom,(
% 2.36/0.92    ! [X0,X1] : (r1_tarski(X0,X1) => k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0))),
% 2.36/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.92  
% 2.36/0.92  fof(f30,plain,(
% 2.36/0.92    ! [X0,X1] : (k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) | ~r1_tarski(X0,X1))),
% 2.36/0.92    inference(ennf_transformation,[],[f11])).
% 2.36/0.92  
% 2.36/0.92  fof(f58,plain,(
% 2.36/0.92    ( ! [X0,X1] : (k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) | ~r1_tarski(X0,X1)) )),
% 2.36/0.92    inference(cnf_transformation,[],[f30])).
% 2.36/0.92  
% 2.36/0.92  fof(f62,plain,(
% 2.36/0.92    sK2 != sK3),
% 2.36/0.92    inference(cnf_transformation,[],[f40])).
% 2.36/0.92  
% 2.36/0.92  fof(f42,plain,(
% 2.36/0.92    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 2.36/0.92    inference(cnf_transformation,[],[f15])).
% 2.36/0.92  
% 2.36/0.92  fof(f63,plain,(
% 2.36/0.92    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 2.36/0.92    inference(equality_resolution,[],[f42])).
% 2.36/0.92  
% 2.36/0.92  fof(f61,plain,(
% 2.36/0.92    r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))),
% 2.36/0.92    inference(cnf_transformation,[],[f40])).
% 2.36/0.92  
% 2.36/0.92  fof(f5,axiom,(
% 2.36/0.92    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 2.36/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.92  
% 2.36/0.92  fof(f21,plain,(
% 2.36/0.92    ! [X0] : (! [X1] : ((r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.36/0.92    inference(ennf_transformation,[],[f5])).
% 2.36/0.92  
% 2.36/0.92  fof(f22,plain,(
% 2.36/0.92    ! [X0] : (! [X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.36/0.92    inference(flattening,[],[f21])).
% 2.36/0.92  
% 2.36/0.92  fof(f46,plain,(
% 2.36/0.92    ( ! [X0,X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.36/0.92    inference(cnf_transformation,[],[f22])).
% 2.36/0.92  
% 2.36/0.92  fof(f8,axiom,(
% 2.36/0.92    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 2.36/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.92  
% 2.36/0.92  fof(f55,plain,(
% 2.36/0.92    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 2.36/0.92    inference(cnf_transformation,[],[f8])).
% 2.36/0.92  
% 2.36/0.92  fof(f6,axiom,(
% 2.36/0.92    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 2.36/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.92  
% 2.36/0.92  fof(f23,plain,(
% 2.36/0.92    ! [X0] : ((! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 2.36/0.92    inference(ennf_transformation,[],[f6])).
% 2.36/0.92  
% 2.36/0.92  fof(f24,plain,(
% 2.36/0.92    ! [X0] : (! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 2.36/0.92    inference(flattening,[],[f23])).
% 2.36/0.92  
% 2.36/0.92  fof(f47,plain,(
% 2.36/0.92    ( ! [X0,X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0)) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 2.36/0.92    inference(cnf_transformation,[],[f24])).
% 2.36/0.92  
% 2.36/0.92  fof(f10,axiom,(
% 2.36/0.92    ! [X0] : (v3_ordinal1(X0) => v2_wellord1(k1_wellord2(X0)))),
% 2.36/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.92  
% 2.36/0.92  fof(f29,plain,(
% 2.36/0.92    ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0))),
% 2.36/0.92    inference(ennf_transformation,[],[f10])).
% 2.36/0.92  
% 2.36/0.92  fof(f57,plain,(
% 2.36/0.92    ( ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 2.36/0.92    inference(cnf_transformation,[],[f29])).
% 2.36/0.92  
% 2.36/0.92  fof(f7,axiom,(
% 2.36/0.92    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 2.36/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/0.92  
% 2.36/0.92  fof(f25,plain,(
% 2.36/0.92    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 2.36/0.92    inference(ennf_transformation,[],[f7])).
% 2.36/0.92  
% 2.36/0.92  fof(f26,plain,(
% 2.36/0.92    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 2.36/0.92    inference(flattening,[],[f25])).
% 2.36/0.92  
% 2.36/0.92  fof(f33,plain,(
% 2.36/0.92    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 2.36/0.92    inference(nnf_transformation,[],[f26])).
% 2.36/0.92  
% 2.36/0.92  fof(f34,plain,(
% 2.36/0.92    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 2.36/0.92    inference(flattening,[],[f33])).
% 2.36/0.92  
% 2.36/0.92  fof(f35,plain,(
% 2.36/0.92    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 2.36/0.92    inference(rectify,[],[f34])).
% 2.36/0.92  
% 2.36/0.92  fof(f36,plain,(
% 2.36/0.92    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK0(X0,X1),sK1(X0,X1)) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & (r1_tarski(sK0(X0,X1),sK1(X0,X1)) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & r2_hidden(sK1(X0,X1),X0) & r2_hidden(sK0(X0,X1),X0)))),
% 2.36/0.92    introduced(choice_axiom,[])).
% 2.36/0.92  
% 2.36/0.92  fof(f37,plain,(
% 2.36/0.92    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK0(X0,X1),sK1(X0,X1)) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & (r1_tarski(sK0(X0,X1),sK1(X0,X1)) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & r2_hidden(sK1(X0,X1),X0) & r2_hidden(sK0(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 2.36/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f36])).
% 2.36/0.92  
% 2.36/0.92  fof(f48,plain,(
% 2.36/0.92    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 2.36/0.92    inference(cnf_transformation,[],[f37])).
% 2.36/0.92  
% 2.36/0.92  fof(f70,plain,(
% 2.36/0.92    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 2.36/0.92    inference(equality_resolution,[],[f48])).
% 2.36/0.92  
% 2.36/0.92  cnf(c_2,plain,
% 2.36/0.92      ( r2_hidden(X0,X1)
% 2.36/0.92      | r2_hidden(X1,X0)
% 2.36/0.92      | ~ v3_ordinal1(X1)
% 2.36/0.92      | ~ v3_ordinal1(X0)
% 2.36/0.92      | X0 = X1 ),
% 2.36/0.92      inference(cnf_transformation,[],[f43]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_1298,plain,
% 2.36/0.92      ( X0 = X1
% 2.36/0.92      | r2_hidden(X0,X1) = iProver_top
% 2.36/0.92      | r2_hidden(X1,X0) = iProver_top
% 2.36/0.92      | v3_ordinal1(X0) != iProver_top
% 2.36/0.92      | v3_ordinal1(X1) != iProver_top ),
% 2.36/0.92      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_3,plain,
% 2.36/0.92      ( r2_xboole_0(X0,X1)
% 2.36/0.92      | r2_xboole_0(X1,X0)
% 2.36/0.92      | ~ v3_ordinal1(X1)
% 2.36/0.92      | ~ v3_ordinal1(X0)
% 2.36/0.92      | X0 = X1 ),
% 2.36/0.92      inference(cnf_transformation,[],[f44]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_1297,plain,
% 2.36/0.92      ( X0 = X1
% 2.36/0.92      | r2_xboole_0(X0,X1) = iProver_top
% 2.36/0.92      | r2_xboole_0(X1,X0) = iProver_top
% 2.36/0.92      | v3_ordinal1(X0) != iProver_top
% 2.36/0.92      | v3_ordinal1(X1) != iProver_top ),
% 2.36/0.92      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_1,plain,
% 2.36/0.92      ( r1_tarski(X0,X1) | ~ r2_xboole_0(X0,X1) ),
% 2.36/0.92      inference(cnf_transformation,[],[f41]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_1299,plain,
% 2.36/0.92      ( r1_tarski(X0,X1) = iProver_top
% 2.36/0.92      | r2_xboole_0(X0,X1) != iProver_top ),
% 2.36/0.92      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_2270,plain,
% 2.36/0.92      ( X0 = X1
% 2.36/0.92      | r1_tarski(X0,X1) = iProver_top
% 2.36/0.92      | r2_xboole_0(X1,X0) = iProver_top
% 2.36/0.92      | v3_ordinal1(X1) != iProver_top
% 2.36/0.92      | v3_ordinal1(X0) != iProver_top ),
% 2.36/0.92      inference(superposition,[status(thm)],[c_1297,c_1299]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_4,plain,
% 2.36/0.92      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 2.36/0.92      inference(cnf_transformation,[],[f45]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_1296,plain,
% 2.36/0.92      ( r2_hidden(X0,X1) != iProver_top
% 2.36/0.92      | r1_tarski(X1,X0) != iProver_top ),
% 2.36/0.92      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_2449,plain,
% 2.36/0.92      ( X0 = X1
% 2.36/0.92      | r2_hidden(X0,X1) != iProver_top
% 2.36/0.92      | r2_xboole_0(X0,X1) = iProver_top
% 2.36/0.92      | v3_ordinal1(X1) != iProver_top
% 2.36/0.92      | v3_ordinal1(X0) != iProver_top ),
% 2.36/0.92      inference(superposition,[status(thm)],[c_2270,c_1296]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_2746,plain,
% 2.36/0.92      ( X0 = X1
% 2.36/0.92      | r2_hidden(X0,X1) = iProver_top
% 2.36/0.92      | r2_xboole_0(X1,X0) = iProver_top
% 2.36/0.92      | v3_ordinal1(X1) != iProver_top
% 2.36/0.92      | v3_ordinal1(X0) != iProver_top ),
% 2.36/0.92      inference(superposition,[status(thm)],[c_1298,c_2449]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_21,negated_conjecture,
% 2.36/0.92      ( v3_ordinal1(sK2) ),
% 2.36/0.92      inference(cnf_transformation,[],[f59]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_1283,plain,
% 2.36/0.92      ( v3_ordinal1(sK2) = iProver_top ),
% 2.36/0.92      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_20,negated_conjecture,
% 2.36/0.92      ( v3_ordinal1(sK3) ),
% 2.36/0.92      inference(cnf_transformation,[],[f60]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_1284,plain,
% 2.36/0.92      ( v3_ordinal1(sK3) = iProver_top ),
% 2.36/0.92      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_15,plain,
% 2.36/0.92      ( ~ r2_hidden(X0,X1)
% 2.36/0.92      | ~ v3_ordinal1(X1)
% 2.36/0.92      | ~ v3_ordinal1(X0)
% 2.36/0.92      | k1_wellord1(k1_wellord2(X1),X0) = X0 ),
% 2.36/0.92      inference(cnf_transformation,[],[f56]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_1287,plain,
% 2.36/0.92      ( k1_wellord1(k1_wellord2(X0),X1) = X1
% 2.36/0.92      | r2_hidden(X1,X0) != iProver_top
% 2.36/0.92      | v3_ordinal1(X1) != iProver_top
% 2.36/0.92      | v3_ordinal1(X0) != iProver_top ),
% 2.36/0.92      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_2378,plain,
% 2.36/0.92      ( X0 = X1
% 2.36/0.92      | k1_wellord1(k1_wellord2(X1),X0) = X0
% 2.36/0.92      | r2_hidden(X1,X0) = iProver_top
% 2.36/0.92      | v3_ordinal1(X1) != iProver_top
% 2.36/0.92      | v3_ordinal1(X0) != iProver_top ),
% 2.36/0.92      inference(superposition,[status(thm)],[c_1298,c_1287]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_2743,plain,
% 2.36/0.92      ( X0 = X1
% 2.36/0.92      | k1_wellord1(k1_wellord2(X0),X1) = X1
% 2.36/0.92      | r2_xboole_0(X0,X1) = iProver_top
% 2.36/0.92      | v3_ordinal1(X1) != iProver_top
% 2.36/0.92      | v3_ordinal1(X0) != iProver_top ),
% 2.36/0.92      inference(superposition,[status(thm)],[c_2378,c_2449]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_3126,plain,
% 2.36/0.92      ( X0 = X1
% 2.36/0.92      | k1_wellord1(k1_wellord2(X1),X0) = X0
% 2.36/0.92      | r1_tarski(X1,X0) = iProver_top
% 2.36/0.92      | v3_ordinal1(X1) != iProver_top
% 2.36/0.92      | v3_ordinal1(X0) != iProver_top ),
% 2.36/0.92      inference(superposition,[status(thm)],[c_2743,c_1299]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_17,plain,
% 2.36/0.92      ( ~ r1_tarski(X0,X1)
% 2.36/0.92      | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ),
% 2.36/0.92      inference(cnf_transformation,[],[f58]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_1286,plain,
% 2.36/0.92      ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 2.36/0.92      | r1_tarski(X1,X0) != iProver_top ),
% 2.36/0.92      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_3223,plain,
% 2.36/0.92      ( X0 = X1
% 2.36/0.92      | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
% 2.36/0.92      | k1_wellord1(k1_wellord2(X0),X1) = X1
% 2.36/0.92      | v3_ordinal1(X1) != iProver_top
% 2.36/0.92      | v3_ordinal1(X0) != iProver_top ),
% 2.36/0.92      inference(superposition,[status(thm)],[c_3126,c_1286]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_4036,plain,
% 2.36/0.92      ( k2_wellord1(k1_wellord2(X0),sK3) = k1_wellord2(sK3)
% 2.36/0.92      | k1_wellord1(k1_wellord2(sK3),X0) = X0
% 2.36/0.92      | sK3 = X0
% 2.36/0.92      | v3_ordinal1(X0) != iProver_top ),
% 2.36/0.92      inference(superposition,[status(thm)],[c_1284,c_3223]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_4117,plain,
% 2.36/0.92      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 2.36/0.92      | k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 2.36/0.92      | sK3 = sK2 ),
% 2.36/0.92      inference(superposition,[status(thm)],[c_1283,c_4036]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_18,negated_conjecture,
% 2.36/0.92      ( sK2 != sK3 ),
% 2.36/0.92      inference(cnf_transformation,[],[f62]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_66,plain,
% 2.36/0.92      ( r2_xboole_0(sK2,sK2) | ~ v3_ordinal1(sK2) | sK2 = sK2 ),
% 2.36/0.92      inference(instantiation,[status(thm)],[c_3]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_0,plain,
% 2.36/0.92      ( ~ r2_xboole_0(X0,X0) ),
% 2.36/0.92      inference(cnf_transformation,[],[f63]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_75,plain,
% 2.36/0.92      ( ~ r2_xboole_0(sK2,sK2) ),
% 2.36/0.92      inference(instantiation,[status(thm)],[c_0]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_918,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_1481,plain,
% 2.36/0.92      ( sK3 != X0 | sK2 != X0 | sK2 = sK3 ),
% 2.36/0.92      inference(instantiation,[status(thm)],[c_918]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_1482,plain,
% 2.36/0.92      ( sK3 != sK2 | sK2 = sK3 | sK2 != sK2 ),
% 2.36/0.92      inference(instantiation,[status(thm)],[c_1481]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_4210,plain,
% 2.36/0.92      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 2.36/0.92      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
% 2.36/0.92      inference(global_propositional_subsumption,
% 2.36/0.92                [status(thm)],
% 2.36/0.92                [c_4117,c_21,c_18,c_66,c_75,c_1482]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_4211,plain,
% 2.36/0.92      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 2.36/0.92      | k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
% 2.36/0.92      inference(renaming,[status(thm)],[c_4210]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_4037,plain,
% 2.36/0.92      ( k2_wellord1(k1_wellord2(X0),sK2) = k1_wellord2(sK2)
% 2.36/0.92      | k1_wellord1(k1_wellord2(sK2),X0) = X0
% 2.36/0.92      | sK2 = X0
% 2.36/0.92      | v3_ordinal1(X0) != iProver_top ),
% 2.36/0.92      inference(superposition,[status(thm)],[c_1283,c_3223]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_4219,plain,
% 2.36/0.92      ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
% 2.36/0.92      | k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 2.36/0.92      | sK3 = sK2 ),
% 2.36/0.92      inference(superposition,[status(thm)],[c_1284,c_4037]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_917,plain,( X0 = X0 ),theory(equality) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_1567,plain,
% 2.36/0.92      ( k1_wellord2(sK3) = k1_wellord2(sK3) ),
% 2.36/0.92      inference(instantiation,[status(thm)],[c_917]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_19,negated_conjecture,
% 2.36/0.92      ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) ),
% 2.36/0.92      inference(cnf_transformation,[],[f61]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_1285,plain,
% 2.36/0.92      ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) = iProver_top ),
% 2.36/0.92      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_5,plain,
% 2.36/0.92      ( ~ r4_wellord1(X0,X1)
% 2.36/0.92      | r4_wellord1(X1,X0)
% 2.36/0.92      | ~ v1_relat_1(X1)
% 2.36/0.92      | ~ v1_relat_1(X0) ),
% 2.36/0.92      inference(cnf_transformation,[],[f46]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_1295,plain,
% 2.36/0.92      ( r4_wellord1(X0,X1) != iProver_top
% 2.36/0.92      | r4_wellord1(X1,X0) = iProver_top
% 2.36/0.92      | v1_relat_1(X0) != iProver_top
% 2.36/0.92      | v1_relat_1(X1) != iProver_top ),
% 2.36/0.92      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_1836,plain,
% 2.36/0.92      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top
% 2.36/0.92      | v1_relat_1(k1_wellord2(sK3)) != iProver_top
% 2.36/0.92      | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
% 2.36/0.92      inference(superposition,[status(thm)],[c_1285,c_1295]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_14,plain,
% 2.36/0.92      ( v1_relat_1(k1_wellord2(X0)) ),
% 2.36/0.92      inference(cnf_transformation,[],[f55]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_34,plain,
% 2.36/0.92      ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
% 2.36/0.92      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_36,plain,
% 2.36/0.92      ( v1_relat_1(k1_wellord2(sK2)) = iProver_top ),
% 2.36/0.92      inference(instantiation,[status(thm)],[c_34]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_1943,plain,
% 2.36/0.92      ( v1_relat_1(k1_wellord2(sK3)) != iProver_top
% 2.36/0.92      | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top ),
% 2.36/0.92      inference(global_propositional_subsumption,
% 2.36/0.92                [status(thm)],
% 2.36/0.92                [c_1836,c_36]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_1944,plain,
% 2.36/0.92      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top
% 2.36/0.92      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 2.36/0.92      inference(renaming,[status(thm)],[c_1943]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_1288,plain,
% 2.36/0.92      ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
% 2.36/0.92      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_1949,plain,
% 2.36/0.92      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top ),
% 2.36/0.92      inference(forward_subsumption_resolution,
% 2.36/0.92                [status(thm)],
% 2.36/0.92                [c_1944,c_1288]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_2556,plain,
% 2.36/0.92      ( X0 = X1
% 2.36/0.92      | k1_wellord1(k1_wellord2(X1),X0) = X0
% 2.36/0.92      | k1_wellord1(k1_wellord2(X0),X1) = X1
% 2.36/0.92      | v3_ordinal1(X1) != iProver_top
% 2.36/0.92      | v3_ordinal1(X0) != iProver_top ),
% 2.36/0.92      inference(superposition,[status(thm)],[c_2378,c_1287]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_3603,plain,
% 2.36/0.92      ( k1_wellord1(k1_wellord2(X0),sK3) = sK3
% 2.36/0.92      | k1_wellord1(k1_wellord2(sK3),X0) = X0
% 2.36/0.92      | sK3 = X0
% 2.36/0.92      | v3_ordinal1(X0) != iProver_top ),
% 2.36/0.92      inference(superposition,[status(thm)],[c_1284,c_2556]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_3631,plain,
% 2.36/0.92      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 2.36/0.92      | k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 2.36/0.92      | sK3 = sK2 ),
% 2.36/0.92      inference(superposition,[status(thm)],[c_1283,c_3603]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_3816,plain,
% 2.36/0.92      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 2.36/0.92      | k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
% 2.36/0.92      inference(global_propositional_subsumption,
% 2.36/0.92                [status(thm)],
% 2.36/0.92                [c_3631,c_21,c_18,c_66,c_75,c_1482]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_3817,plain,
% 2.36/0.92      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 2.36/0.92      | k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
% 2.36/0.92      inference(renaming,[status(thm)],[c_3816]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_6,plain,
% 2.36/0.92      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
% 2.36/0.92      | ~ r2_hidden(X1,k3_relat_1(X0))
% 2.36/0.92      | ~ v2_wellord1(X0)
% 2.36/0.92      | ~ v1_relat_1(X0) ),
% 2.36/0.92      inference(cnf_transformation,[],[f47]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_16,plain,
% 2.36/0.92      ( v2_wellord1(k1_wellord2(X0)) | ~ v3_ordinal1(X0) ),
% 2.36/0.92      inference(cnf_transformation,[],[f57]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_243,plain,
% 2.36/0.92      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
% 2.36/0.92      | ~ r2_hidden(X1,k3_relat_1(X0))
% 2.36/0.92      | ~ v1_relat_1(X0)
% 2.36/0.92      | ~ v3_ordinal1(X2)
% 2.36/0.92      | k1_wellord2(X2) != X0 ),
% 2.36/0.92      inference(resolution_lifted,[status(thm)],[c_6,c_16]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_244,plain,
% 2.36/0.92      ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
% 2.36/0.92      | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
% 2.36/0.92      | ~ v1_relat_1(k1_wellord2(X0))
% 2.36/0.92      | ~ v3_ordinal1(X0) ),
% 2.36/0.92      inference(unflattening,[status(thm)],[c_243]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_248,plain,
% 2.36/0.92      ( ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
% 2.36/0.92      | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
% 2.36/0.92      | ~ v3_ordinal1(X0) ),
% 2.36/0.92      inference(global_propositional_subsumption,
% 2.36/0.92                [status(thm)],
% 2.36/0.92                [c_244,c_14]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_249,plain,
% 2.36/0.92      ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
% 2.36/0.92      | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
% 2.36/0.92      | ~ v3_ordinal1(X0) ),
% 2.36/0.92      inference(renaming,[status(thm)],[c_248]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_1282,plain,
% 2.36/0.92      ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
% 2.36/0.92      | r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) != iProver_top
% 2.36/0.92      | v3_ordinal1(X0) != iProver_top ),
% 2.36/0.92      inference(predicate_to_equality,[status(thm)],[c_249]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_13,plain,
% 2.36/0.92      ( ~ v1_relat_1(k1_wellord2(X0))
% 2.36/0.92      | k3_relat_1(k1_wellord2(X0)) = X0 ),
% 2.36/0.92      inference(cnf_transformation,[],[f70]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_127,plain,
% 2.36/0.92      ( k3_relat_1(k1_wellord2(X0)) = X0 ),
% 2.36/0.92      inference(global_propositional_subsumption,
% 2.36/0.92                [status(thm)],
% 2.36/0.92                [c_13,c_14]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_1375,plain,
% 2.36/0.92      ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
% 2.36/0.92      | r2_hidden(X1,X0) != iProver_top
% 2.36/0.92      | v3_ordinal1(X0) != iProver_top ),
% 2.36/0.92      inference(light_normalisation,[status(thm)],[c_1282,c_127]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_3820,plain,
% 2.36/0.92      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 2.36/0.92      | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top
% 2.36/0.92      | r2_hidden(sK2,sK3) != iProver_top
% 2.36/0.92      | v3_ordinal1(sK3) != iProver_top ),
% 2.36/0.92      inference(superposition,[status(thm)],[c_3817,c_1375]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_22,plain,
% 2.36/0.92      ( v3_ordinal1(sK2) = iProver_top ),
% 2.36/0.92      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_23,plain,
% 2.36/0.92      ( v3_ordinal1(sK3) = iProver_top ),
% 2.36/0.92      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_1487,plain,
% 2.36/0.92      ( r2_hidden(sK3,sK2)
% 2.36/0.92      | r2_hidden(sK2,sK3)
% 2.36/0.92      | ~ v3_ordinal1(sK3)
% 2.36/0.92      | ~ v3_ordinal1(sK2)
% 2.36/0.92      | sK2 = sK3 ),
% 2.36/0.92      inference(instantiation,[status(thm)],[c_2]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_1488,plain,
% 2.36/0.92      ( sK2 = sK3
% 2.36/0.92      | r2_hidden(sK3,sK2) = iProver_top
% 2.36/0.92      | r2_hidden(sK2,sK3) = iProver_top
% 2.36/0.92      | v3_ordinal1(sK3) != iProver_top
% 2.36/0.92      | v3_ordinal1(sK2) != iProver_top ),
% 2.36/0.92      inference(predicate_to_equality,[status(thm)],[c_1487]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_1520,plain,
% 2.36/0.92      ( ~ r2_hidden(sK3,sK2)
% 2.36/0.92      | ~ v3_ordinal1(sK3)
% 2.36/0.92      | ~ v3_ordinal1(sK2)
% 2.36/0.92      | k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
% 2.36/0.92      inference(instantiation,[status(thm)],[c_15]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_1521,plain,
% 2.36/0.92      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 2.36/0.92      | r2_hidden(sK3,sK2) != iProver_top
% 2.36/0.92      | v3_ordinal1(sK3) != iProver_top
% 2.36/0.92      | v3_ordinal1(sK2) != iProver_top ),
% 2.36/0.92      inference(predicate_to_equality,[status(thm)],[c_1520]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_3894,plain,
% 2.36/0.92      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 2.36/0.92      | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top ),
% 2.36/0.92      inference(global_propositional_subsumption,
% 2.36/0.92                [status(thm)],
% 2.36/0.92                [c_3820,c_22,c_23,c_18,c_1488,c_1521]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_922,plain,
% 2.36/0.92      ( ~ r4_wellord1(X0,X1) | r4_wellord1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.36/0.92      theory(equality) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_1968,plain,
% 2.36/0.92      ( r4_wellord1(X0,X1)
% 2.36/0.92      | ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2))
% 2.36/0.92      | X0 != k1_wellord2(sK3)
% 2.36/0.92      | X1 != k1_wellord2(sK2) ),
% 2.36/0.92      inference(instantiation,[status(thm)],[c_922]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_2205,plain,
% 2.36/0.92      ( r4_wellord1(k1_wellord2(sK3),X0)
% 2.36/0.92      | ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2))
% 2.36/0.92      | X0 != k1_wellord2(sK2)
% 2.36/0.92      | k1_wellord2(sK3) != k1_wellord2(sK3) ),
% 2.36/0.92      inference(instantiation,[status(thm)],[c_1968]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_4326,plain,
% 2.36/0.92      ( r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2))
% 2.36/0.92      | ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2))
% 2.36/0.92      | k2_wellord1(k1_wellord2(sK3),sK2) != k1_wellord2(sK2)
% 2.36/0.92      | k1_wellord2(sK3) != k1_wellord2(sK3) ),
% 2.36/0.92      inference(instantiation,[status(thm)],[c_2205]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_4327,plain,
% 2.36/0.92      ( k2_wellord1(k1_wellord2(sK3),sK2) != k1_wellord2(sK2)
% 2.36/0.92      | k1_wellord2(sK3) != k1_wellord2(sK3)
% 2.36/0.92      | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) = iProver_top
% 2.36/0.92      | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) != iProver_top ),
% 2.36/0.92      inference(predicate_to_equality,[status(thm)],[c_4326]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_4331,plain,
% 2.36/0.92      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
% 2.36/0.92      inference(global_propositional_subsumption,
% 2.36/0.92                [status(thm)],
% 2.36/0.92                [c_4219,c_21,c_18,c_66,c_75,c_1482,c_1567,c_1949,c_3894,
% 2.36/0.92                 c_4327]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_4334,plain,
% 2.36/0.92      ( r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top
% 2.36/0.92      | r2_hidden(sK3,sK2) != iProver_top
% 2.36/0.92      | v3_ordinal1(sK2) != iProver_top ),
% 2.36/0.92      inference(superposition,[status(thm)],[c_4331,c_1375]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_4504,plain,
% 2.36/0.92      ( r2_hidden(sK3,sK2) != iProver_top
% 2.36/0.92      | r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top ),
% 2.36/0.92      inference(global_propositional_subsumption,
% 2.36/0.92                [status(thm)],
% 2.36/0.92                [c_4334,c_22]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_4505,plain,
% 2.36/0.92      ( r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top
% 2.36/0.92      | r2_hidden(sK3,sK2) != iProver_top ),
% 2.36/0.92      inference(renaming,[status(thm)],[c_4504]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_4510,plain,
% 2.36/0.92      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 2.36/0.92      | r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) != iProver_top
% 2.36/0.92      | r2_hidden(sK3,sK2) != iProver_top ),
% 2.36/0.92      inference(superposition,[status(thm)],[c_4211,c_4505]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_1627,plain,
% 2.36/0.92      ( ~ r2_hidden(sK2,sK3)
% 2.36/0.92      | ~ v3_ordinal1(sK3)
% 2.36/0.92      | ~ v3_ordinal1(sK2)
% 2.36/0.92      | k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
% 2.36/0.92      inference(instantiation,[status(thm)],[c_15]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_4511,plain,
% 2.36/0.92      ( ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
% 2.36/0.92      | ~ r2_hidden(sK3,sK2)
% 2.36/0.92      | k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
% 2.36/0.92      inference(predicate_to_equality_rev,[status(thm)],[c_4510]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_4513,plain,
% 2.36/0.92      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
% 2.36/0.92      inference(global_propositional_subsumption,
% 2.36/0.92                [status(thm)],
% 2.36/0.92                [c_4510,c_21,c_20,c_19,c_18,c_1487,c_1627,c_4511]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_4516,plain,
% 2.36/0.92      ( r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top
% 2.36/0.92      | r2_hidden(sK2,sK3) != iProver_top
% 2.36/0.92      | v3_ordinal1(sK3) != iProver_top ),
% 2.36/0.92      inference(superposition,[status(thm)],[c_4513,c_1375]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_1490,plain,
% 2.36/0.92      ( r2_xboole_0(sK3,sK2)
% 2.36/0.92      | r2_xboole_0(sK2,sK3)
% 2.36/0.92      | ~ v3_ordinal1(sK3)
% 2.36/0.92      | ~ v3_ordinal1(sK2)
% 2.36/0.92      | sK2 = sK3 ),
% 2.36/0.92      inference(instantiation,[status(thm)],[c_3]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_1491,plain,
% 2.36/0.92      ( sK2 = sK3
% 2.36/0.92      | r2_xboole_0(sK3,sK2) = iProver_top
% 2.36/0.92      | r2_xboole_0(sK2,sK3) = iProver_top
% 2.36/0.92      | v3_ordinal1(sK3) != iProver_top
% 2.36/0.92      | v3_ordinal1(sK2) != iProver_top ),
% 2.36/0.92      inference(predicate_to_equality,[status(thm)],[c_1490]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_1535,plain,
% 2.36/0.92      ( r1_tarski(sK3,sK2) | ~ r2_xboole_0(sK3,sK2) ),
% 2.36/0.92      inference(instantiation,[status(thm)],[c_1]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_1536,plain,
% 2.36/0.92      ( r1_tarski(sK3,sK2) = iProver_top
% 2.36/0.92      | r2_xboole_0(sK3,sK2) != iProver_top ),
% 2.36/0.92      inference(predicate_to_equality,[status(thm)],[c_1535]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_1623,plain,
% 2.36/0.92      ( ~ r2_hidden(sK2,sK3) | ~ r1_tarski(sK3,sK2) ),
% 2.36/0.92      inference(instantiation,[status(thm)],[c_4]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_1640,plain,
% 2.36/0.92      ( r2_hidden(sK2,sK3) != iProver_top
% 2.36/0.92      | r1_tarski(sK3,sK2) != iProver_top ),
% 2.36/0.92      inference(predicate_to_equality,[status(thm)],[c_1623]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_1655,plain,
% 2.36/0.92      ( r1_tarski(sK2,sK3) | ~ r2_xboole_0(sK2,sK3) ),
% 2.36/0.92      inference(instantiation,[status(thm)],[c_1]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_1656,plain,
% 2.36/0.92      ( r1_tarski(sK2,sK3) = iProver_top
% 2.36/0.92      | r2_xboole_0(sK2,sK3) != iProver_top ),
% 2.36/0.92      inference(predicate_to_equality,[status(thm)],[c_1655]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_1958,plain,
% 2.36/0.92      ( ~ r1_tarski(sK2,sK3)
% 2.36/0.92      | k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2) ),
% 2.36/0.92      inference(instantiation,[status(thm)],[c_17]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_1959,plain,
% 2.36/0.92      ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
% 2.36/0.92      | r1_tarski(sK2,sK3) != iProver_top ),
% 2.36/0.92      inference(predicate_to_equality,[status(thm)],[c_1958]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_4544,plain,
% 2.36/0.92      ( r2_hidden(sK2,sK3) != iProver_top ),
% 2.36/0.92      inference(global_propositional_subsumption,
% 2.36/0.92                [status(thm)],
% 2.36/0.92                [c_4516,c_22,c_23,c_18,c_1491,c_1536,c_1567,c_1640,
% 2.36/0.92                 c_1656,c_1949,c_1959,c_4327]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_4552,plain,
% 2.36/0.92      ( sK3 = sK2
% 2.36/0.92      | r2_xboole_0(sK3,sK2) = iProver_top
% 2.36/0.92      | v3_ordinal1(sK3) != iProver_top
% 2.36/0.92      | v3_ordinal1(sK2) != iProver_top ),
% 2.36/0.92      inference(superposition,[status(thm)],[c_2746,c_4544]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_1516,plain,
% 2.36/0.92      ( ~ r2_hidden(sK3,sK2) | ~ r1_tarski(sK2,sK3) ),
% 2.36/0.92      inference(instantiation,[status(thm)],[c_4]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_1533,plain,
% 2.36/0.92      ( r2_hidden(sK3,sK2) != iProver_top
% 2.36/0.92      | r1_tarski(sK2,sK3) != iProver_top ),
% 2.36/0.92      inference(predicate_to_equality,[status(thm)],[c_1516]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_4574,plain,
% 2.36/0.92      ( r2_xboole_0(sK3,sK2) = iProver_top ),
% 2.36/0.92      inference(global_propositional_subsumption,
% 2.36/0.92                [status(thm)],
% 2.36/0.92                [c_4552,c_22,c_23,c_18,c_1488,c_1491,c_1533,c_1536,
% 2.36/0.92                 c_1567,c_1640,c_1656,c_1949,c_1959,c_4327,c_4516]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_4579,plain,
% 2.36/0.92      ( r1_tarski(sK3,sK2) = iProver_top ),
% 2.36/0.92      inference(superposition,[status(thm)],[c_4574,c_1299]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_4672,plain,
% 2.36/0.92      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
% 2.36/0.92      inference(superposition,[status(thm)],[c_4579,c_1286]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_4786,plain,
% 2.36/0.92      ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) != iProver_top
% 2.36/0.92      | r2_hidden(sK3,sK2) != iProver_top ),
% 2.36/0.92      inference(demodulation,[status(thm)],[c_4672,c_4505]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(c_24,plain,
% 2.36/0.92      ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) = iProver_top ),
% 2.36/0.92      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.36/0.92  
% 2.36/0.92  cnf(contradiction,plain,
% 2.36/0.92      ( $false ),
% 2.36/0.92      inference(minisat,
% 2.36/0.92                [status(thm)],
% 2.36/0.92                [c_4786,c_4544,c_1488,c_18,c_24,c_23,c_22]) ).
% 2.36/0.92  
% 2.36/0.92  
% 2.36/0.92  % SZS output end CNFRefutation for theBenchmark.p
% 2.36/0.92  
% 2.36/0.92  ------                               Statistics
% 2.36/0.92  
% 2.36/0.92  ------ General
% 2.36/0.92  
% 2.36/0.92  abstr_ref_over_cycles:                  0
% 2.36/0.92  abstr_ref_under_cycles:                 0
% 2.36/0.92  gc_basic_clause_elim:                   0
% 2.36/0.92  forced_gc_time:                         0
% 2.36/0.92  parsing_time:                           0.009
% 2.36/0.92  unif_index_cands_time:                  0.
% 2.36/0.92  unif_index_add_time:                    0.
% 2.36/0.92  orderings_time:                         0.
% 2.36/0.92  out_proof_time:                         0.011
% 2.36/0.92  total_time:                             0.166
% 2.36/0.92  num_of_symbols:                         47
% 2.36/0.92  num_of_terms:                           3608
% 2.36/0.92  
% 2.36/0.92  ------ Preprocessing
% 2.36/0.92  
% 2.36/0.92  num_of_splits:                          0
% 2.36/0.92  num_of_split_atoms:                     0
% 2.36/0.92  num_of_reused_defs:                     0
% 2.36/0.92  num_eq_ax_congr_red:                    15
% 2.36/0.92  num_of_sem_filtered_clauses:            1
% 2.36/0.92  num_of_subtypes:                        0
% 2.36/0.92  monotx_restored_types:                  0
% 2.36/0.92  sat_num_of_epr_types:                   0
% 2.36/0.92  sat_num_of_non_cyclic_types:            0
% 2.36/0.92  sat_guarded_non_collapsed_types:        0
% 2.36/0.92  num_pure_diseq_elim:                    0
% 2.36/0.92  simp_replaced_by:                       0
% 2.36/0.92  res_preprocessed:                       114
% 2.36/0.92  prep_upred:                             0
% 2.36/0.92  prep_unflattend:                        37
% 2.36/0.92  smt_new_axioms:                         0
% 2.36/0.92  pred_elim_cands:                        6
% 2.36/0.92  pred_elim:                              1
% 2.36/0.92  pred_elim_cl:                           1
% 2.36/0.92  pred_elim_cycles:                       3
% 2.36/0.92  merged_defs:                            0
% 2.36/0.92  merged_defs_ncl:                        0
% 2.36/0.92  bin_hyper_res:                          0
% 2.36/0.92  prep_cycles:                            4
% 2.36/0.92  pred_elim_time:                         0.011
% 2.36/0.92  splitting_time:                         0.
% 2.36/0.92  sem_filter_time:                        0.
% 2.36/0.92  monotx_time:                            0.001
% 2.36/0.92  subtype_inf_time:                       0.
% 2.36/0.92  
% 2.36/0.92  ------ Problem properties
% 2.36/0.92  
% 2.36/0.92  clauses:                                21
% 2.36/0.92  conjectures:                            4
% 2.36/0.92  epr:                                    9
% 2.36/0.92  horn:                                   16
% 2.36/0.92  ground:                                 4
% 2.36/0.92  unary:                                  7
% 2.36/0.92  binary:                                 3
% 2.36/0.92  lits:                                   58
% 2.36/0.92  lits_eq:                                10
% 2.36/0.92  fd_pure:                                0
% 2.36/0.92  fd_pseudo:                              0
% 2.36/0.92  fd_cond:                                0
% 2.36/0.92  fd_pseudo_cond:                         2
% 2.36/0.92  ac_symbols:                             0
% 2.36/0.92  
% 2.36/0.92  ------ Propositional Solver
% 2.36/0.92  
% 2.36/0.92  prop_solver_calls:                      27
% 2.36/0.92  prop_fast_solver_calls:                 1017
% 2.36/0.92  smt_solver_calls:                       0
% 2.36/0.92  smt_fast_solver_calls:                  0
% 2.36/0.92  prop_num_of_clauses:                    1428
% 2.36/0.92  prop_preprocess_simplified:             5037
% 2.36/0.92  prop_fo_subsumed:                       27
% 2.36/0.92  prop_solver_time:                       0.
% 2.36/0.92  smt_solver_time:                        0.
% 2.36/0.92  smt_fast_solver_time:                   0.
% 2.36/0.92  prop_fast_solver_time:                  0.
% 2.36/0.92  prop_unsat_core_time:                   0.
% 2.36/0.92  
% 2.36/0.92  ------ QBF
% 2.36/0.92  
% 2.36/0.92  qbf_q_res:                              0
% 2.36/0.92  qbf_num_tautologies:                    0
% 2.36/0.92  qbf_prep_cycles:                        0
% 2.36/0.92  
% 2.36/0.92  ------ BMC1
% 2.36/0.92  
% 2.36/0.92  bmc1_current_bound:                     -1
% 2.36/0.92  bmc1_last_solved_bound:                 -1
% 2.36/0.92  bmc1_unsat_core_size:                   -1
% 2.36/0.92  bmc1_unsat_core_parents_size:           -1
% 2.36/0.92  bmc1_merge_next_fun:                    0
% 2.36/0.92  bmc1_unsat_core_clauses_time:           0.
% 2.36/0.92  
% 2.36/0.92  ------ Instantiation
% 2.36/0.92  
% 2.36/0.92  inst_num_of_clauses:                    445
% 2.36/0.92  inst_num_in_passive:                    94
% 2.36/0.92  inst_num_in_active:                     235
% 2.36/0.92  inst_num_in_unprocessed:                116
% 2.36/0.92  inst_num_of_loops:                      310
% 2.36/0.92  inst_num_of_learning_restarts:          0
% 2.36/0.92  inst_num_moves_active_passive:          71
% 2.36/0.92  inst_lit_activity:                      0
% 2.36/0.92  inst_lit_activity_moves:                0
% 2.36/0.92  inst_num_tautologies:                   0
% 2.36/0.92  inst_num_prop_implied:                  0
% 2.36/0.92  inst_num_existing_simplified:           0
% 2.36/0.92  inst_num_eq_res_simplified:             0
% 2.36/0.92  inst_num_child_elim:                    0
% 2.36/0.92  inst_num_of_dismatching_blockings:      224
% 2.36/0.92  inst_num_of_non_proper_insts:           417
% 2.36/0.92  inst_num_of_duplicates:                 0
% 2.36/0.92  inst_inst_num_from_inst_to_res:         0
% 2.36/0.92  inst_dismatching_checking_time:         0.
% 2.36/0.92  
% 2.36/0.92  ------ Resolution
% 2.36/0.92  
% 2.36/0.92  res_num_of_clauses:                     0
% 2.36/0.92  res_num_in_passive:                     0
% 2.36/0.92  res_num_in_active:                      0
% 2.36/0.92  res_num_of_loops:                       118
% 2.36/0.92  res_forward_subset_subsumed:            39
% 2.36/0.92  res_backward_subset_subsumed:           0
% 2.36/0.92  res_forward_subsumed:                   0
% 2.36/0.92  res_backward_subsumed:                  0
% 2.36/0.92  res_forward_subsumption_resolution:     7
% 2.36/0.92  res_backward_subsumption_resolution:    0
% 2.36/0.92  res_clause_to_clause_subsumption:       290
% 2.36/0.92  res_orphan_elimination:                 0
% 2.36/0.92  res_tautology_del:                      24
% 2.36/0.92  res_num_eq_res_simplified:              0
% 2.36/0.92  res_num_sel_changes:                    0
% 2.36/0.92  res_moves_from_active_to_pass:          0
% 2.36/0.92  
% 2.36/0.92  ------ Superposition
% 2.36/0.92  
% 2.36/0.92  sup_time_total:                         0.
% 2.36/0.92  sup_time_generating:                    0.
% 2.36/0.92  sup_time_sim_full:                      0.
% 2.36/0.92  sup_time_sim_immed:                     0.
% 2.36/0.92  
% 2.36/0.92  sup_num_of_clauses:                     74
% 2.36/0.92  sup_num_in_active:                      57
% 2.36/0.92  sup_num_in_passive:                     17
% 2.36/0.92  sup_num_of_loops:                       61
% 2.36/0.92  sup_fw_superposition:                   57
% 2.36/0.92  sup_bw_superposition:                   61
% 2.36/0.92  sup_immediate_simplified:               16
% 2.36/0.92  sup_given_eliminated:                   0
% 2.36/0.92  comparisons_done:                       0
% 2.36/0.92  comparisons_avoided:                    57
% 2.36/0.92  
% 2.36/0.92  ------ Simplifications
% 2.36/0.92  
% 2.36/0.92  
% 2.36/0.92  sim_fw_subset_subsumed:                 4
% 2.36/0.92  sim_bw_subset_subsumed:                 3
% 2.36/0.92  sim_fw_subsumed:                        3
% 2.36/0.92  sim_bw_subsumed:                        0
% 2.36/0.92  sim_fw_subsumption_res:                 3
% 2.36/0.92  sim_bw_subsumption_res:                 0
% 2.36/0.92  sim_tautology_del:                      2
% 2.36/0.92  sim_eq_tautology_del:                   23
% 2.36/0.92  sim_eq_res_simp:                        0
% 2.36/0.92  sim_fw_demodulated:                     0
% 2.36/0.92  sim_bw_demodulated:                     1
% 2.36/0.92  sim_light_normalised:                   10
% 2.36/0.92  sim_joinable_taut:                      0
% 2.36/0.92  sim_joinable_simp:                      0
% 2.36/0.92  sim_ac_normalised:                      0
% 2.36/0.92  sim_smt_subsumption:                    0
% 2.36/0.92  
%------------------------------------------------------------------------------
