%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:42 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :  163 (2058 expanded)
%              Number of clauses        :  106 ( 737 expanded)
%              Number of leaves         :   18 ( 430 expanded)
%              Depth                    :   25
%              Number of atoms          :  575 (7940 expanded)
%              Number of equality atoms :  261 (2196 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   17 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
           => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_wellord1(k1_wellord2(X1),X0) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
     => ( sK3 != X0
        & r4_wellord1(k1_wellord2(X0),k1_wellord2(sK3))
        & v3_ordinal1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
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

fof(f41,plain,
    ( sK2 != sK3
    & r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
    & v3_ordinal1(sK3)
    & v3_ordinal1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f32,f40,f39])).

fof(f61,plain,(
    v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f60,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f63,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f41])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f48,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f58,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f8])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f26])).

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
    inference(flattening,[],[f34])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f37,plain,(
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

fof(f38,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f37])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f70,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f62,plain,(
    r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) ),
    inference(cnf_transformation,[],[f41])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f47,plain,(
    ! [X0,X1] :
      ( r4_wellord1(X1,X0)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_3,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1488,plain,
    ( X0 = X1
    | r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | k1_wellord1(k1_wellord2(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1478,plain,
    ( k1_wellord1(k1_wellord2(X0),X1) = X1
    | r2_hidden(X1,X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2612,plain,
    ( X0 = X1
    | k1_wellord1(k1_wellord2(X0),X1) = X1
    | r2_hidden(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1488,c_1478])).

cnf(c_20,negated_conjecture,
    ( v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1475,plain,
    ( v3_ordinal1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_21,negated_conjecture,
    ( v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1474,plain,
    ( v3_ordinal1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2610,plain,
    ( X0 = X1
    | k1_wellord1(k1_wellord2(X1),X0) = X0
    | r2_hidden(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1488,c_1478])).

cnf(c_0,plain,
    ( r1_ordinal1(X0,X1)
    | r1_ordinal1(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1491,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r1_ordinal1(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_ordinal1(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1489,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_ordinal1(X0,X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2212,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_ordinal1(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1491,c_1489])).

cnf(c_17,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1477,plain,
    ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2723,plain,
    ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | r1_ordinal1(X0,X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2212,c_1477])).

cnf(c_3462,plain,
    ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2723,c_1489])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1487,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3584,plain,
    ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | r2_hidden(X1,X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3462,c_1487])).

cnf(c_4183,plain,
    ( X0 = X1
    | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
    | k1_wellord1(k1_wellord2(X0),X1) = X1
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2610,c_3584])).

cnf(c_6096,plain,
    ( k2_wellord1(k1_wellord2(X0),sK2) = k1_wellord2(sK2)
    | k1_wellord1(k1_wellord2(sK2),X0) = X0
    | sK2 = X0
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1474,c_4183])).

cnf(c_6612,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
    | k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_1475,c_6096])).

cnf(c_18,negated_conjecture,
    ( sK2 != sK3 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_63,plain,
    ( ~ r2_hidden(sK2,sK2)
    | ~ r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_66,plain,
    ( r2_hidden(sK2,sK2)
    | ~ v3_ordinal1(sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_69,plain,
    ( r1_tarski(sK2,sK2)
    | ~ r1_ordinal1(sK2,sK2)
    | ~ v3_ordinal1(sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_75,plain,
    ( r1_ordinal1(sK2,sK2)
    | ~ v3_ordinal1(sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1111,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1680,plain,
    ( sK3 != X0
    | sK2 != X0
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_1111])).

cnf(c_1681,plain,
    ( sK3 != sK2
    | sK2 = sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1680])).

cnf(c_6620,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6612,c_21,c_18,c_63,c_66,c_69,c_75,c_1681])).

cnf(c_6621,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
    | k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
    inference(renaming,[status(thm)],[c_6620])).

cnf(c_4184,plain,
    ( X0 = X1
    | k1_wellord1(k1_wellord2(X1),X0) = X0
    | k1_wellord1(k1_wellord2(X0),X1) = X1
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2610,c_1478])).

cnf(c_4912,plain,
    ( k1_wellord1(k1_wellord2(X0),sK3) = sK3
    | k1_wellord1(k1_wellord2(sK3),X0) = X0
    | sK3 = X0
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1475,c_4184])).

cnf(c_4940,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_1474,c_4912])).

cnf(c_5123,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4940,c_21,c_18,c_63,c_66,c_69,c_75,c_1681])).

cnf(c_5124,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
    inference(renaming,[status(thm)],[c_5123])).

cnf(c_6,plain,
    ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
    | ~ r2_hidden(X1,k3_relat_1(X0))
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_16,plain,
    ( v2_wellord1(k1_wellord2(X0))
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_242,plain,
    ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
    | ~ r2_hidden(X1,k3_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v3_ordinal1(X2)
    | k1_wellord2(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_16])).

cnf(c_243,plain,
    ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
    | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
    | ~ v1_relat_1(k1_wellord2(X0))
    | ~ v3_ordinal1(X0) ),
    inference(unflattening,[status(thm)],[c_242])).

cnf(c_14,plain,
    ( v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_247,plain,
    ( ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
    | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
    | ~ v3_ordinal1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_243,c_14])).

cnf(c_248,plain,
    ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
    | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
    | ~ v3_ordinal1(X0) ),
    inference(renaming,[status(thm)],[c_247])).

cnf(c_1473,plain,
    ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
    | r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_248])).

cnf(c_13,plain,
    ( ~ v1_relat_1(k1_wellord2(X0))
    | k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_127,plain,
    ( k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_14])).

cnf(c_1574,plain,
    ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1473,c_127])).

cnf(c_5127,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5124,c_1574])).

cnf(c_22,plain,
    ( v3_ordinal1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_23,plain,
    ( v3_ordinal1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1686,plain,
    ( r2_hidden(sK3,sK2)
    | r2_hidden(sK2,sK3)
    | ~ v3_ordinal1(sK3)
    | ~ v3_ordinal1(sK2)
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1687,plain,
    ( sK2 = sK3
    | r2_hidden(sK3,sK2) = iProver_top
    | r2_hidden(sK2,sK3) = iProver_top
    | v3_ordinal1(sK3) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1686])).

cnf(c_1715,plain,
    ( ~ r2_hidden(sK3,sK2)
    | ~ v3_ordinal1(sK3)
    | ~ v3_ordinal1(sK2)
    | k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1716,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | r2_hidden(sK3,sK2) != iProver_top
    | v3_ordinal1(sK3) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1715])).

cnf(c_5268,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5127,c_22,c_23,c_18,c_1687,c_1716])).

cnf(c_6624,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6621,c_5268])).

cnf(c_19,negated_conjecture,
    ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1476,plain,
    ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5,plain,
    ( ~ r4_wellord1(X0,X1)
    | r4_wellord1(X1,X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1486,plain,
    ( r4_wellord1(X0,X1) != iProver_top
    | r4_wellord1(X1,X0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2079,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1476,c_1486])).

cnf(c_34,plain,
    ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_36,plain,
    ( v1_relat_1(k1_wellord2(sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_2082,plain,
    ( v1_relat_1(k1_wellord2(sK3)) != iProver_top
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2079,c_36])).

cnf(c_2083,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2082])).

cnf(c_1479,plain,
    ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2088,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2083,c_1479])).

cnf(c_6786,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6624,c_2088])).

cnf(c_6789,plain,
    ( r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top
    | r2_hidden(sK3,sK2) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6786,c_1574])).

cnf(c_24,plain,
    ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1120,plain,
    ( X0 != X1
    | k1_wellord2(X0) = k1_wellord2(X1) ),
    theory(equality)).

cnf(c_1132,plain,
    ( k1_wellord2(sK2) = k1_wellord2(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1120])).

cnf(c_1714,plain,
    ( ~ r2_hidden(sK3,sK2)
    | ~ r1_tarski(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1718,plain,
    ( r2_hidden(sK3,sK2) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1714])).

cnf(c_1743,plain,
    ( ~ r1_tarski(sK3,X0)
    | k2_wellord1(k1_wellord2(X0),sK3) = k1_wellord2(sK3) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1748,plain,
    ( k2_wellord1(k1_wellord2(X0),sK3) = k1_wellord2(sK3)
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1743])).

cnf(c_1750,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | r1_tarski(sK3,sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1748])).

cnf(c_1871,plain,
    ( r1_tarski(sK2,sK3)
    | ~ r1_ordinal1(sK2,sK3)
    | ~ v3_ordinal1(sK3)
    | ~ v3_ordinal1(sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1872,plain,
    ( r1_tarski(sK2,sK3) = iProver_top
    | r1_ordinal1(sK2,sK3) != iProver_top
    | v3_ordinal1(sK3) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1871])).

cnf(c_1886,plain,
    ( r1_tarski(sK3,X0)
    | ~ r1_ordinal1(sK3,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1887,plain,
    ( r1_tarski(sK3,X0) = iProver_top
    | r1_ordinal1(sK3,X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1886])).

cnf(c_1889,plain,
    ( r1_tarski(sK3,sK2) = iProver_top
    | r1_ordinal1(sK3,sK2) != iProver_top
    | v3_ordinal1(sK3) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1887])).

cnf(c_1115,plain,
    ( ~ r4_wellord1(X0,X1)
    | r4_wellord1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1694,plain,
    ( r4_wellord1(X0,X1)
    | ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
    | X1 != k1_wellord2(sK3)
    | X0 != k1_wellord2(sK2) ),
    inference(instantiation,[status(thm)],[c_1115])).

cnf(c_1742,plain,
    ( r4_wellord1(X0,k2_wellord1(k1_wellord2(X1),sK3))
    | ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
    | X0 != k1_wellord2(sK2)
    | k2_wellord1(k1_wellord2(X1),sK3) != k1_wellord2(sK3) ),
    inference(instantiation,[status(thm)],[c_1694])).

cnf(c_2017,plain,
    ( r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(X0),sK3))
    | ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
    | k2_wellord1(k1_wellord2(X0),sK3) != k1_wellord2(sK3)
    | k1_wellord2(sK2) != k1_wellord2(sK2) ),
    inference(instantiation,[status(thm)],[c_1742])).

cnf(c_2019,plain,
    ( k2_wellord1(k1_wellord2(X0),sK3) != k1_wellord2(sK3)
    | k1_wellord2(sK2) != k1_wellord2(sK2)
    | r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(X0),sK3)) = iProver_top
    | r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2017])).

cnf(c_2021,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) != k1_wellord2(sK3)
    | k1_wellord2(sK2) != k1_wellord2(sK2)
    | r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) = iProver_top
    | r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2019])).

cnf(c_2266,plain,
    ( r1_ordinal1(sK3,sK2)
    | r1_ordinal1(sK2,sK3)
    | ~ v3_ordinal1(sK3)
    | ~ v3_ordinal1(sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2267,plain,
    ( r1_ordinal1(sK3,sK2) = iProver_top
    | r1_ordinal1(sK2,sK3) = iProver_top
    | v3_ordinal1(sK3) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2266])).

cnf(c_7351,plain,
    ( r2_hidden(sK3,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6789,c_21,c_22,c_23,c_24,c_63,c_66,c_69,c_75,c_1132,c_1718,c_1750,c_1872,c_1889,c_2021,c_2267])).

cnf(c_7361,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | sK3 = sK2
    | v3_ordinal1(sK3) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2612,c_7351])).

cnf(c_1813,plain,
    ( ~ r2_hidden(sK2,sK3)
    | ~ v3_ordinal1(sK3)
    | ~ v3_ordinal1(sK2)
    | k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1814,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | r2_hidden(sK2,sK3) != iProver_top
    | v3_ordinal1(sK3) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1813])).

cnf(c_7577,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7361,c_21,c_22,c_23,c_24,c_18,c_63,c_66,c_69,c_75,c_1132,c_1687,c_1718,c_1750,c_1814,c_1872,c_1889,c_2021,c_2267,c_6789])).

cnf(c_7580,plain,
    ( r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7577,c_1574])).

cnf(c_7969,plain,
    ( r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7580,c_21,c_22,c_23,c_24,c_18,c_63,c_66,c_69,c_75,c_1132,c_1687,c_1718,c_1750,c_1872,c_1889,c_2021,c_2267,c_6789])).

cnf(c_3610,plain,
    ( X0 = X1
    | k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | r2_hidden(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1488,c_3584])).

cnf(c_7360,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
    | sK3 = sK2
    | v3_ordinal1(sK3) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3610,c_7351])).

cnf(c_7649,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7360,c_21,c_22,c_23,c_18,c_63,c_66,c_69,c_75,c_1681])).

cnf(c_7973,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7969,c_7649])).

cnf(c_7975,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7973,c_2088])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:04:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.77/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/0.99  
% 2.77/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.77/0.99  
% 2.77/0.99  ------  iProver source info
% 2.77/0.99  
% 2.77/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.77/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.77/0.99  git: non_committed_changes: false
% 2.77/0.99  git: last_make_outside_of_git: false
% 2.77/0.99  
% 2.77/0.99  ------ 
% 2.77/0.99  
% 2.77/0.99  ------ Input Options
% 2.77/0.99  
% 2.77/0.99  --out_options                           all
% 2.77/0.99  --tptp_safe_out                         true
% 2.77/0.99  --problem_path                          ""
% 2.77/0.99  --include_path                          ""
% 2.77/0.99  --clausifier                            res/vclausify_rel
% 2.77/0.99  --clausifier_options                    --mode clausify
% 2.77/0.99  --stdin                                 false
% 2.77/0.99  --stats_out                             all
% 2.77/0.99  
% 2.77/0.99  ------ General Options
% 2.77/0.99  
% 2.77/0.99  --fof                                   false
% 2.77/0.99  --time_out_real                         305.
% 2.77/0.99  --time_out_virtual                      -1.
% 2.77/0.99  --symbol_type_check                     false
% 2.77/0.99  --clausify_out                          false
% 2.77/0.99  --sig_cnt_out                           false
% 2.77/0.99  --trig_cnt_out                          false
% 2.77/0.99  --trig_cnt_out_tolerance                1.
% 2.77/0.99  --trig_cnt_out_sk_spl                   false
% 2.77/0.99  --abstr_cl_out                          false
% 2.77/0.99  
% 2.77/0.99  ------ Global Options
% 2.77/0.99  
% 2.77/0.99  --schedule                              default
% 2.77/0.99  --add_important_lit                     false
% 2.77/0.99  --prop_solver_per_cl                    1000
% 2.77/0.99  --min_unsat_core                        false
% 2.77/0.99  --soft_assumptions                      false
% 2.77/0.99  --soft_lemma_size                       3
% 2.77/0.99  --prop_impl_unit_size                   0
% 2.77/0.99  --prop_impl_unit                        []
% 2.77/0.99  --share_sel_clauses                     true
% 2.77/0.99  --reset_solvers                         false
% 2.77/0.99  --bc_imp_inh                            [conj_cone]
% 2.77/0.99  --conj_cone_tolerance                   3.
% 2.77/0.99  --extra_neg_conj                        none
% 2.77/0.99  --large_theory_mode                     true
% 2.77/0.99  --prolific_symb_bound                   200
% 2.77/0.99  --lt_threshold                          2000
% 2.77/0.99  --clause_weak_htbl                      true
% 2.77/0.99  --gc_record_bc_elim                     false
% 2.77/0.99  
% 2.77/0.99  ------ Preprocessing Options
% 2.77/0.99  
% 2.77/0.99  --preprocessing_flag                    true
% 2.77/0.99  --time_out_prep_mult                    0.1
% 2.77/0.99  --splitting_mode                        input
% 2.77/0.99  --splitting_grd                         true
% 2.77/0.99  --splitting_cvd                         false
% 2.77/0.99  --splitting_cvd_svl                     false
% 2.77/0.99  --splitting_nvd                         32
% 2.77/0.99  --sub_typing                            true
% 2.77/0.99  --prep_gs_sim                           true
% 2.77/0.99  --prep_unflatten                        true
% 2.77/0.99  --prep_res_sim                          true
% 2.77/0.99  --prep_upred                            true
% 2.77/0.99  --prep_sem_filter                       exhaustive
% 2.77/0.99  --prep_sem_filter_out                   false
% 2.77/0.99  --pred_elim                             true
% 2.77/0.99  --res_sim_input                         true
% 2.77/0.99  --eq_ax_congr_red                       true
% 2.77/0.99  --pure_diseq_elim                       true
% 2.77/0.99  --brand_transform                       false
% 2.77/0.99  --non_eq_to_eq                          false
% 2.77/0.99  --prep_def_merge                        true
% 2.77/0.99  --prep_def_merge_prop_impl              false
% 2.77/0.99  --prep_def_merge_mbd                    true
% 2.77/0.99  --prep_def_merge_tr_red                 false
% 2.77/0.99  --prep_def_merge_tr_cl                  false
% 2.77/0.99  --smt_preprocessing                     true
% 2.77/0.99  --smt_ac_axioms                         fast
% 2.77/0.99  --preprocessed_out                      false
% 2.77/0.99  --preprocessed_stats                    false
% 2.77/0.99  
% 2.77/0.99  ------ Abstraction refinement Options
% 2.77/0.99  
% 2.77/0.99  --abstr_ref                             []
% 2.77/0.99  --abstr_ref_prep                        false
% 2.77/0.99  --abstr_ref_until_sat                   false
% 2.77/0.99  --abstr_ref_sig_restrict                funpre
% 2.77/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.77/0.99  --abstr_ref_under                       []
% 2.77/0.99  
% 2.77/0.99  ------ SAT Options
% 2.77/0.99  
% 2.77/0.99  --sat_mode                              false
% 2.77/0.99  --sat_fm_restart_options                ""
% 2.77/0.99  --sat_gr_def                            false
% 2.77/0.99  --sat_epr_types                         true
% 2.77/0.99  --sat_non_cyclic_types                  false
% 2.77/0.99  --sat_finite_models                     false
% 2.77/0.99  --sat_fm_lemmas                         false
% 2.77/0.99  --sat_fm_prep                           false
% 2.77/1.00  --sat_fm_uc_incr                        true
% 2.77/1.00  --sat_out_model                         small
% 2.77/1.00  --sat_out_clauses                       false
% 2.77/1.00  
% 2.77/1.00  ------ QBF Options
% 2.77/1.00  
% 2.77/1.00  --qbf_mode                              false
% 2.77/1.00  --qbf_elim_univ                         false
% 2.77/1.00  --qbf_dom_inst                          none
% 2.77/1.00  --qbf_dom_pre_inst                      false
% 2.77/1.00  --qbf_sk_in                             false
% 2.77/1.00  --qbf_pred_elim                         true
% 2.77/1.00  --qbf_split                             512
% 2.77/1.00  
% 2.77/1.00  ------ BMC1 Options
% 2.77/1.00  
% 2.77/1.00  --bmc1_incremental                      false
% 2.77/1.00  --bmc1_axioms                           reachable_all
% 2.77/1.00  --bmc1_min_bound                        0
% 2.77/1.00  --bmc1_max_bound                        -1
% 2.77/1.00  --bmc1_max_bound_default                -1
% 2.77/1.00  --bmc1_symbol_reachability              true
% 2.77/1.00  --bmc1_property_lemmas                  false
% 2.77/1.00  --bmc1_k_induction                      false
% 2.77/1.00  --bmc1_non_equiv_states                 false
% 2.77/1.00  --bmc1_deadlock                         false
% 2.77/1.00  --bmc1_ucm                              false
% 2.77/1.00  --bmc1_add_unsat_core                   none
% 2.77/1.00  --bmc1_unsat_core_children              false
% 2.77/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.77/1.00  --bmc1_out_stat                         full
% 2.77/1.00  --bmc1_ground_init                      false
% 2.77/1.00  --bmc1_pre_inst_next_state              false
% 2.77/1.00  --bmc1_pre_inst_state                   false
% 2.77/1.00  --bmc1_pre_inst_reach_state             false
% 2.77/1.00  --bmc1_out_unsat_core                   false
% 2.77/1.00  --bmc1_aig_witness_out                  false
% 2.77/1.00  --bmc1_verbose                          false
% 2.77/1.00  --bmc1_dump_clauses_tptp                false
% 2.77/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.77/1.00  --bmc1_dump_file                        -
% 2.77/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.77/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.77/1.00  --bmc1_ucm_extend_mode                  1
% 2.77/1.00  --bmc1_ucm_init_mode                    2
% 2.77/1.00  --bmc1_ucm_cone_mode                    none
% 2.77/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.77/1.00  --bmc1_ucm_relax_model                  4
% 2.77/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.77/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.77/1.00  --bmc1_ucm_layered_model                none
% 2.77/1.00  --bmc1_ucm_max_lemma_size               10
% 2.77/1.00  
% 2.77/1.00  ------ AIG Options
% 2.77/1.00  
% 2.77/1.00  --aig_mode                              false
% 2.77/1.00  
% 2.77/1.00  ------ Instantiation Options
% 2.77/1.00  
% 2.77/1.00  --instantiation_flag                    true
% 2.77/1.00  --inst_sos_flag                         false
% 2.77/1.00  --inst_sos_phase                        true
% 2.77/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.77/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.77/1.00  --inst_lit_sel_side                     num_symb
% 2.77/1.00  --inst_solver_per_active                1400
% 2.77/1.00  --inst_solver_calls_frac                1.
% 2.77/1.00  --inst_passive_queue_type               priority_queues
% 2.77/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.77/1.00  --inst_passive_queues_freq              [25;2]
% 2.77/1.00  --inst_dismatching                      true
% 2.77/1.00  --inst_eager_unprocessed_to_passive     true
% 2.77/1.00  --inst_prop_sim_given                   true
% 2.77/1.00  --inst_prop_sim_new                     false
% 2.77/1.00  --inst_subs_new                         false
% 2.77/1.00  --inst_eq_res_simp                      false
% 2.77/1.00  --inst_subs_given                       false
% 2.77/1.00  --inst_orphan_elimination               true
% 2.77/1.00  --inst_learning_loop_flag               true
% 2.77/1.00  --inst_learning_start                   3000
% 2.77/1.00  --inst_learning_factor                  2
% 2.77/1.00  --inst_start_prop_sim_after_learn       3
% 2.77/1.00  --inst_sel_renew                        solver
% 2.77/1.00  --inst_lit_activity_flag                true
% 2.77/1.00  --inst_restr_to_given                   false
% 2.77/1.00  --inst_activity_threshold               500
% 2.77/1.00  --inst_out_proof                        true
% 2.77/1.00  
% 2.77/1.00  ------ Resolution Options
% 2.77/1.00  
% 2.77/1.00  --resolution_flag                       true
% 2.77/1.00  --res_lit_sel                           adaptive
% 2.77/1.00  --res_lit_sel_side                      none
% 2.77/1.00  --res_ordering                          kbo
% 2.77/1.00  --res_to_prop_solver                    active
% 2.77/1.00  --res_prop_simpl_new                    false
% 2.77/1.00  --res_prop_simpl_given                  true
% 2.77/1.00  --res_passive_queue_type                priority_queues
% 2.77/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.77/1.00  --res_passive_queues_freq               [15;5]
% 2.77/1.00  --res_forward_subs                      full
% 2.77/1.00  --res_backward_subs                     full
% 2.77/1.00  --res_forward_subs_resolution           true
% 2.77/1.00  --res_backward_subs_resolution          true
% 2.77/1.00  --res_orphan_elimination                true
% 2.77/1.00  --res_time_limit                        2.
% 2.77/1.00  --res_out_proof                         true
% 2.77/1.00  
% 2.77/1.00  ------ Superposition Options
% 2.77/1.00  
% 2.77/1.00  --superposition_flag                    true
% 2.77/1.00  --sup_passive_queue_type                priority_queues
% 2.77/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.77/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.77/1.00  --demod_completeness_check              fast
% 2.77/1.00  --demod_use_ground                      true
% 2.77/1.00  --sup_to_prop_solver                    passive
% 2.77/1.00  --sup_prop_simpl_new                    true
% 2.77/1.00  --sup_prop_simpl_given                  true
% 2.77/1.00  --sup_fun_splitting                     false
% 2.77/1.00  --sup_smt_interval                      50000
% 2.77/1.00  
% 2.77/1.00  ------ Superposition Simplification Setup
% 2.77/1.00  
% 2.77/1.00  --sup_indices_passive                   []
% 2.77/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.77/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.00  --sup_full_bw                           [BwDemod]
% 2.77/1.00  --sup_immed_triv                        [TrivRules]
% 2.77/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.77/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.00  --sup_immed_bw_main                     []
% 2.77/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.77/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/1.00  
% 2.77/1.00  ------ Combination Options
% 2.77/1.00  
% 2.77/1.00  --comb_res_mult                         3
% 2.77/1.00  --comb_sup_mult                         2
% 2.77/1.00  --comb_inst_mult                        10
% 2.77/1.00  
% 2.77/1.00  ------ Debug Options
% 2.77/1.00  
% 2.77/1.00  --dbg_backtrace                         false
% 2.77/1.00  --dbg_dump_prop_clauses                 false
% 2.77/1.00  --dbg_dump_prop_clauses_file            -
% 2.77/1.00  --dbg_out_stat                          false
% 2.77/1.00  ------ Parsing...
% 2.77/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.77/1.00  
% 2.77/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.77/1.00  
% 2.77/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.77/1.00  
% 2.77/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.77/1.00  ------ Proving...
% 2.77/1.00  ------ Problem Properties 
% 2.77/1.00  
% 2.77/1.00  
% 2.77/1.00  clauses                                 21
% 2.77/1.00  conjectures                             4
% 2.77/1.00  EPR                                     9
% 2.77/1.00  Horn                                    16
% 2.77/1.00  unary                                   6
% 2.77/1.00  binary                                  2
% 2.77/1.00  lits                                    62
% 2.77/1.00  lits eq                                 9
% 2.77/1.00  fd_pure                                 0
% 2.77/1.00  fd_pseudo                               0
% 2.77/1.00  fd_cond                                 0
% 2.77/1.00  fd_pseudo_cond                          1
% 2.77/1.00  AC symbols                              0
% 2.77/1.00  
% 2.77/1.00  ------ Schedule dynamic 5 is on 
% 2.77/1.00  
% 2.77/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.77/1.00  
% 2.77/1.00  
% 2.77/1.00  ------ 
% 2.77/1.00  Current options:
% 2.77/1.00  ------ 
% 2.77/1.00  
% 2.77/1.00  ------ Input Options
% 2.77/1.00  
% 2.77/1.00  --out_options                           all
% 2.77/1.00  --tptp_safe_out                         true
% 2.77/1.00  --problem_path                          ""
% 2.77/1.00  --include_path                          ""
% 2.77/1.00  --clausifier                            res/vclausify_rel
% 2.77/1.00  --clausifier_options                    --mode clausify
% 2.77/1.00  --stdin                                 false
% 2.77/1.00  --stats_out                             all
% 2.77/1.00  
% 2.77/1.00  ------ General Options
% 2.77/1.00  
% 2.77/1.00  --fof                                   false
% 2.77/1.00  --time_out_real                         305.
% 2.77/1.00  --time_out_virtual                      -1.
% 2.77/1.00  --symbol_type_check                     false
% 2.77/1.00  --clausify_out                          false
% 2.77/1.00  --sig_cnt_out                           false
% 2.77/1.00  --trig_cnt_out                          false
% 2.77/1.00  --trig_cnt_out_tolerance                1.
% 2.77/1.00  --trig_cnt_out_sk_spl                   false
% 2.77/1.00  --abstr_cl_out                          false
% 2.77/1.00  
% 2.77/1.00  ------ Global Options
% 2.77/1.00  
% 2.77/1.00  --schedule                              default
% 2.77/1.00  --add_important_lit                     false
% 2.77/1.00  --prop_solver_per_cl                    1000
% 2.77/1.00  --min_unsat_core                        false
% 2.77/1.00  --soft_assumptions                      false
% 2.77/1.00  --soft_lemma_size                       3
% 2.77/1.00  --prop_impl_unit_size                   0
% 2.77/1.00  --prop_impl_unit                        []
% 2.77/1.00  --share_sel_clauses                     true
% 2.77/1.00  --reset_solvers                         false
% 2.77/1.00  --bc_imp_inh                            [conj_cone]
% 2.77/1.00  --conj_cone_tolerance                   3.
% 2.77/1.00  --extra_neg_conj                        none
% 2.77/1.00  --large_theory_mode                     true
% 2.77/1.00  --prolific_symb_bound                   200
% 2.77/1.00  --lt_threshold                          2000
% 2.77/1.00  --clause_weak_htbl                      true
% 2.77/1.00  --gc_record_bc_elim                     false
% 2.77/1.00  
% 2.77/1.00  ------ Preprocessing Options
% 2.77/1.00  
% 2.77/1.00  --preprocessing_flag                    true
% 2.77/1.00  --time_out_prep_mult                    0.1
% 2.77/1.00  --splitting_mode                        input
% 2.77/1.00  --splitting_grd                         true
% 2.77/1.00  --splitting_cvd                         false
% 2.77/1.00  --splitting_cvd_svl                     false
% 2.77/1.00  --splitting_nvd                         32
% 2.77/1.00  --sub_typing                            true
% 2.77/1.00  --prep_gs_sim                           true
% 2.77/1.00  --prep_unflatten                        true
% 2.77/1.00  --prep_res_sim                          true
% 2.77/1.00  --prep_upred                            true
% 2.77/1.00  --prep_sem_filter                       exhaustive
% 2.77/1.00  --prep_sem_filter_out                   false
% 2.77/1.00  --pred_elim                             true
% 2.77/1.00  --res_sim_input                         true
% 2.77/1.00  --eq_ax_congr_red                       true
% 2.77/1.00  --pure_diseq_elim                       true
% 2.77/1.00  --brand_transform                       false
% 2.77/1.00  --non_eq_to_eq                          false
% 2.77/1.00  --prep_def_merge                        true
% 2.77/1.00  --prep_def_merge_prop_impl              false
% 2.77/1.00  --prep_def_merge_mbd                    true
% 2.77/1.00  --prep_def_merge_tr_red                 false
% 2.77/1.00  --prep_def_merge_tr_cl                  false
% 2.77/1.00  --smt_preprocessing                     true
% 2.77/1.00  --smt_ac_axioms                         fast
% 2.77/1.00  --preprocessed_out                      false
% 2.77/1.00  --preprocessed_stats                    false
% 2.77/1.00  
% 2.77/1.00  ------ Abstraction refinement Options
% 2.77/1.00  
% 2.77/1.00  --abstr_ref                             []
% 2.77/1.00  --abstr_ref_prep                        false
% 2.77/1.00  --abstr_ref_until_sat                   false
% 2.77/1.00  --abstr_ref_sig_restrict                funpre
% 2.77/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.77/1.00  --abstr_ref_under                       []
% 2.77/1.00  
% 2.77/1.00  ------ SAT Options
% 2.77/1.00  
% 2.77/1.00  --sat_mode                              false
% 2.77/1.00  --sat_fm_restart_options                ""
% 2.77/1.00  --sat_gr_def                            false
% 2.77/1.00  --sat_epr_types                         true
% 2.77/1.00  --sat_non_cyclic_types                  false
% 2.77/1.00  --sat_finite_models                     false
% 2.77/1.00  --sat_fm_lemmas                         false
% 2.77/1.00  --sat_fm_prep                           false
% 2.77/1.00  --sat_fm_uc_incr                        true
% 2.77/1.00  --sat_out_model                         small
% 2.77/1.00  --sat_out_clauses                       false
% 2.77/1.00  
% 2.77/1.00  ------ QBF Options
% 2.77/1.00  
% 2.77/1.00  --qbf_mode                              false
% 2.77/1.00  --qbf_elim_univ                         false
% 2.77/1.00  --qbf_dom_inst                          none
% 2.77/1.00  --qbf_dom_pre_inst                      false
% 2.77/1.00  --qbf_sk_in                             false
% 2.77/1.00  --qbf_pred_elim                         true
% 2.77/1.00  --qbf_split                             512
% 2.77/1.00  
% 2.77/1.00  ------ BMC1 Options
% 2.77/1.00  
% 2.77/1.00  --bmc1_incremental                      false
% 2.77/1.00  --bmc1_axioms                           reachable_all
% 2.77/1.00  --bmc1_min_bound                        0
% 2.77/1.00  --bmc1_max_bound                        -1
% 2.77/1.00  --bmc1_max_bound_default                -1
% 2.77/1.00  --bmc1_symbol_reachability              true
% 2.77/1.00  --bmc1_property_lemmas                  false
% 2.77/1.00  --bmc1_k_induction                      false
% 2.77/1.00  --bmc1_non_equiv_states                 false
% 2.77/1.00  --bmc1_deadlock                         false
% 2.77/1.00  --bmc1_ucm                              false
% 2.77/1.00  --bmc1_add_unsat_core                   none
% 2.77/1.00  --bmc1_unsat_core_children              false
% 2.77/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.77/1.00  --bmc1_out_stat                         full
% 2.77/1.00  --bmc1_ground_init                      false
% 2.77/1.00  --bmc1_pre_inst_next_state              false
% 2.77/1.00  --bmc1_pre_inst_state                   false
% 2.77/1.00  --bmc1_pre_inst_reach_state             false
% 2.77/1.00  --bmc1_out_unsat_core                   false
% 2.77/1.00  --bmc1_aig_witness_out                  false
% 2.77/1.00  --bmc1_verbose                          false
% 2.77/1.00  --bmc1_dump_clauses_tptp                false
% 2.77/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.77/1.00  --bmc1_dump_file                        -
% 2.77/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.77/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.77/1.00  --bmc1_ucm_extend_mode                  1
% 2.77/1.00  --bmc1_ucm_init_mode                    2
% 2.77/1.00  --bmc1_ucm_cone_mode                    none
% 2.77/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.77/1.00  --bmc1_ucm_relax_model                  4
% 2.77/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.77/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.77/1.00  --bmc1_ucm_layered_model                none
% 2.77/1.00  --bmc1_ucm_max_lemma_size               10
% 2.77/1.00  
% 2.77/1.00  ------ AIG Options
% 2.77/1.00  
% 2.77/1.00  --aig_mode                              false
% 2.77/1.00  
% 2.77/1.00  ------ Instantiation Options
% 2.77/1.00  
% 2.77/1.00  --instantiation_flag                    true
% 2.77/1.00  --inst_sos_flag                         false
% 2.77/1.00  --inst_sos_phase                        true
% 2.77/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.77/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.77/1.00  --inst_lit_sel_side                     none
% 2.77/1.00  --inst_solver_per_active                1400
% 2.77/1.00  --inst_solver_calls_frac                1.
% 2.77/1.00  --inst_passive_queue_type               priority_queues
% 2.77/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.77/1.00  --inst_passive_queues_freq              [25;2]
% 2.77/1.00  --inst_dismatching                      true
% 2.77/1.00  --inst_eager_unprocessed_to_passive     true
% 2.77/1.00  --inst_prop_sim_given                   true
% 2.77/1.00  --inst_prop_sim_new                     false
% 2.77/1.00  --inst_subs_new                         false
% 2.77/1.00  --inst_eq_res_simp                      false
% 2.77/1.00  --inst_subs_given                       false
% 2.77/1.00  --inst_orphan_elimination               true
% 2.77/1.00  --inst_learning_loop_flag               true
% 2.77/1.00  --inst_learning_start                   3000
% 2.77/1.00  --inst_learning_factor                  2
% 2.77/1.00  --inst_start_prop_sim_after_learn       3
% 2.77/1.00  --inst_sel_renew                        solver
% 2.77/1.00  --inst_lit_activity_flag                true
% 2.77/1.00  --inst_restr_to_given                   false
% 2.77/1.00  --inst_activity_threshold               500
% 2.77/1.00  --inst_out_proof                        true
% 2.77/1.00  
% 2.77/1.00  ------ Resolution Options
% 2.77/1.00  
% 2.77/1.00  --resolution_flag                       false
% 2.77/1.00  --res_lit_sel                           adaptive
% 2.77/1.00  --res_lit_sel_side                      none
% 2.77/1.00  --res_ordering                          kbo
% 2.77/1.00  --res_to_prop_solver                    active
% 2.77/1.00  --res_prop_simpl_new                    false
% 2.77/1.00  --res_prop_simpl_given                  true
% 2.77/1.00  --res_passive_queue_type                priority_queues
% 2.77/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.77/1.00  --res_passive_queues_freq               [15;5]
% 2.77/1.00  --res_forward_subs                      full
% 2.77/1.00  --res_backward_subs                     full
% 2.77/1.00  --res_forward_subs_resolution           true
% 2.77/1.00  --res_backward_subs_resolution          true
% 2.77/1.00  --res_orphan_elimination                true
% 2.77/1.00  --res_time_limit                        2.
% 2.77/1.00  --res_out_proof                         true
% 2.77/1.00  
% 2.77/1.00  ------ Superposition Options
% 2.77/1.00  
% 2.77/1.00  --superposition_flag                    true
% 2.77/1.00  --sup_passive_queue_type                priority_queues
% 2.77/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.77/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.77/1.00  --demod_completeness_check              fast
% 2.77/1.00  --demod_use_ground                      true
% 2.77/1.00  --sup_to_prop_solver                    passive
% 2.77/1.00  --sup_prop_simpl_new                    true
% 2.77/1.00  --sup_prop_simpl_given                  true
% 2.77/1.00  --sup_fun_splitting                     false
% 2.77/1.00  --sup_smt_interval                      50000
% 2.77/1.00  
% 2.77/1.00  ------ Superposition Simplification Setup
% 2.77/1.00  
% 2.77/1.00  --sup_indices_passive                   []
% 2.77/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.77/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.00  --sup_full_bw                           [BwDemod]
% 2.77/1.00  --sup_immed_triv                        [TrivRules]
% 2.77/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.77/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.00  --sup_immed_bw_main                     []
% 2.77/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.77/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/1.00  
% 2.77/1.00  ------ Combination Options
% 2.77/1.00  
% 2.77/1.00  --comb_res_mult                         3
% 2.77/1.00  --comb_sup_mult                         2
% 2.77/1.00  --comb_inst_mult                        10
% 2.77/1.00  
% 2.77/1.00  ------ Debug Options
% 2.77/1.00  
% 2.77/1.00  --dbg_backtrace                         false
% 2.77/1.00  --dbg_dump_prop_clauses                 false
% 2.77/1.00  --dbg_dump_prop_clauses_file            -
% 2.77/1.00  --dbg_out_stat                          false
% 2.77/1.00  
% 2.77/1.00  
% 2.77/1.00  
% 2.77/1.00  
% 2.77/1.00  ------ Proving...
% 2.77/1.00  
% 2.77/1.00  
% 2.77/1.00  % SZS status Theorem for theBenchmark.p
% 2.77/1.00  
% 2.77/1.00   Resolution empty clause
% 2.77/1.00  
% 2.77/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.77/1.00  
% 2.77/1.00  fof(f3,axiom,(
% 2.77/1.00    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 2.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f18,plain,(
% 2.77/1.00    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.77/1.00    inference(ennf_transformation,[],[f3])).
% 2.77/1.00  
% 2.77/1.00  fof(f19,plain,(
% 2.77/1.00    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.77/1.00    inference(flattening,[],[f18])).
% 2.77/1.00  
% 2.77/1.00  fof(f45,plain,(
% 2.77/1.00    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f19])).
% 2.77/1.00  
% 2.77/1.00  fof(f9,axiom,(
% 2.77/1.00    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => k1_wellord1(k1_wellord2(X1),X0) = X0)))),
% 2.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f27,plain,(
% 2.77/1.00    ! [X0] : (! [X1] : ((k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.77/1.00    inference(ennf_transformation,[],[f9])).
% 2.77/1.00  
% 2.77/1.00  fof(f28,plain,(
% 2.77/1.00    ! [X0] : (! [X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.77/1.00    inference(flattening,[],[f27])).
% 2.77/1.00  
% 2.77/1.00  fof(f57,plain,(
% 2.77/1.00    ( ! [X0,X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f28])).
% 2.77/1.00  
% 2.77/1.00  fof(f12,conjecture,(
% 2.77/1.00    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 2.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f13,negated_conjecture,(
% 2.77/1.00    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 2.77/1.00    inference(negated_conjecture,[],[f12])).
% 2.77/1.00  
% 2.77/1.00  fof(f31,plain,(
% 2.77/1.00    ? [X0] : (? [X1] : ((X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.77/1.00    inference(ennf_transformation,[],[f13])).
% 2.77/1.00  
% 2.77/1.00  fof(f32,plain,(
% 2.77/1.00    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.77/1.00    inference(flattening,[],[f31])).
% 2.77/1.00  
% 2.77/1.00  fof(f40,plain,(
% 2.77/1.00    ( ! [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) => (sK3 != X0 & r4_wellord1(k1_wellord2(X0),k1_wellord2(sK3)) & v3_ordinal1(sK3))) )),
% 2.77/1.00    introduced(choice_axiom,[])).
% 2.77/1.00  
% 2.77/1.00  fof(f39,plain,(
% 2.77/1.00    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : (sK2 != X1 & r4_wellord1(k1_wellord2(sK2),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK2))),
% 2.77/1.00    introduced(choice_axiom,[])).
% 2.77/1.00  
% 2.77/1.00  fof(f41,plain,(
% 2.77/1.00    (sK2 != sK3 & r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) & v3_ordinal1(sK3)) & v3_ordinal1(sK2)),
% 2.77/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f32,f40,f39])).
% 2.77/1.00  
% 2.77/1.00  fof(f61,plain,(
% 2.77/1.00    v3_ordinal1(sK3)),
% 2.77/1.00    inference(cnf_transformation,[],[f41])).
% 2.77/1.00  
% 2.77/1.00  fof(f60,plain,(
% 2.77/1.00    v3_ordinal1(sK2)),
% 2.77/1.00    inference(cnf_transformation,[],[f41])).
% 2.77/1.00  
% 2.77/1.00  fof(f1,axiom,(
% 2.77/1.00    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 2.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f14,plain,(
% 2.77/1.00    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 2.77/1.00    inference(ennf_transformation,[],[f1])).
% 2.77/1.00  
% 2.77/1.00  fof(f15,plain,(
% 2.77/1.00    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.77/1.00    inference(flattening,[],[f14])).
% 2.77/1.00  
% 2.77/1.00  fof(f42,plain,(
% 2.77/1.00    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f15])).
% 2.77/1.00  
% 2.77/1.00  fof(f2,axiom,(
% 2.77/1.00    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 2.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f16,plain,(
% 2.77/1.00    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 2.77/1.00    inference(ennf_transformation,[],[f2])).
% 2.77/1.00  
% 2.77/1.00  fof(f17,plain,(
% 2.77/1.00    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.77/1.00    inference(flattening,[],[f16])).
% 2.77/1.00  
% 2.77/1.00  fof(f33,plain,(
% 2.77/1.00    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.77/1.00    inference(nnf_transformation,[],[f17])).
% 2.77/1.00  
% 2.77/1.00  fof(f43,plain,(
% 2.77/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f33])).
% 2.77/1.00  
% 2.77/1.00  fof(f11,axiom,(
% 2.77/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0))),
% 2.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f30,plain,(
% 2.77/1.00    ! [X0,X1] : (k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) | ~r1_tarski(X0,X1))),
% 2.77/1.00    inference(ennf_transformation,[],[f11])).
% 2.77/1.00  
% 2.77/1.00  fof(f59,plain,(
% 2.77/1.00    ( ! [X0,X1] : (k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) | ~r1_tarski(X0,X1)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f30])).
% 2.77/1.00  
% 2.77/1.00  fof(f4,axiom,(
% 2.77/1.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f20,plain,(
% 2.77/1.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.77/1.00    inference(ennf_transformation,[],[f4])).
% 2.77/1.00  
% 2.77/1.00  fof(f46,plain,(
% 2.77/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f20])).
% 2.77/1.00  
% 2.77/1.00  fof(f63,plain,(
% 2.77/1.00    sK2 != sK3),
% 2.77/1.00    inference(cnf_transformation,[],[f41])).
% 2.77/1.00  
% 2.77/1.00  fof(f6,axiom,(
% 2.77/1.00    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 2.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f23,plain,(
% 2.77/1.00    ! [X0] : ((! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 2.77/1.00    inference(ennf_transformation,[],[f6])).
% 2.77/1.00  
% 2.77/1.00  fof(f24,plain,(
% 2.77/1.00    ! [X0] : (! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 2.77/1.00    inference(flattening,[],[f23])).
% 2.77/1.00  
% 2.77/1.00  fof(f48,plain,(
% 2.77/1.00    ( ! [X0,X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0)) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f24])).
% 2.77/1.00  
% 2.77/1.00  fof(f10,axiom,(
% 2.77/1.00    ! [X0] : (v3_ordinal1(X0) => v2_wellord1(k1_wellord2(X0)))),
% 2.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f29,plain,(
% 2.77/1.00    ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0))),
% 2.77/1.00    inference(ennf_transformation,[],[f10])).
% 2.77/1.00  
% 2.77/1.00  fof(f58,plain,(
% 2.77/1.00    ( ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f29])).
% 2.77/1.00  
% 2.77/1.00  fof(f8,axiom,(
% 2.77/1.00    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 2.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f56,plain,(
% 2.77/1.00    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 2.77/1.00    inference(cnf_transformation,[],[f8])).
% 2.77/1.00  
% 2.77/1.00  fof(f7,axiom,(
% 2.77/1.00    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 2.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f25,plain,(
% 2.77/1.00    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 2.77/1.00    inference(ennf_transformation,[],[f7])).
% 2.77/1.00  
% 2.77/1.00  fof(f26,plain,(
% 2.77/1.00    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 2.77/1.00    inference(flattening,[],[f25])).
% 2.77/1.00  
% 2.77/1.00  fof(f34,plain,(
% 2.77/1.00    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 2.77/1.00    inference(nnf_transformation,[],[f26])).
% 2.77/1.00  
% 2.77/1.00  fof(f35,plain,(
% 2.77/1.00    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 2.77/1.00    inference(flattening,[],[f34])).
% 2.77/1.00  
% 2.77/1.00  fof(f36,plain,(
% 2.77/1.00    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 2.77/1.00    inference(rectify,[],[f35])).
% 2.77/1.00  
% 2.77/1.00  fof(f37,plain,(
% 2.77/1.00    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK0(X0,X1),sK1(X0,X1)) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & (r1_tarski(sK0(X0,X1),sK1(X0,X1)) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & r2_hidden(sK1(X0,X1),X0) & r2_hidden(sK0(X0,X1),X0)))),
% 2.77/1.00    introduced(choice_axiom,[])).
% 2.77/1.00  
% 2.77/1.00  fof(f38,plain,(
% 2.77/1.00    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK0(X0,X1),sK1(X0,X1)) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & (r1_tarski(sK0(X0,X1),sK1(X0,X1)) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & r2_hidden(sK1(X0,X1),X0) & r2_hidden(sK0(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 2.77/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f37])).
% 2.77/1.00  
% 2.77/1.00  fof(f49,plain,(
% 2.77/1.00    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f38])).
% 2.77/1.00  
% 2.77/1.00  fof(f70,plain,(
% 2.77/1.00    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 2.77/1.00    inference(equality_resolution,[],[f49])).
% 2.77/1.00  
% 2.77/1.00  fof(f62,plain,(
% 2.77/1.00    r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))),
% 2.77/1.00    inference(cnf_transformation,[],[f41])).
% 2.77/1.00  
% 2.77/1.00  fof(f5,axiom,(
% 2.77/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 2.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.00  
% 2.77/1.00  fof(f21,plain,(
% 2.77/1.00    ! [X0] : (! [X1] : ((r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.77/1.00    inference(ennf_transformation,[],[f5])).
% 2.77/1.00  
% 2.77/1.00  fof(f22,plain,(
% 2.77/1.00    ! [X0] : (! [X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.77/1.00    inference(flattening,[],[f21])).
% 2.77/1.00  
% 2.77/1.00  fof(f47,plain,(
% 2.77/1.00    ( ! [X0,X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.77/1.00    inference(cnf_transformation,[],[f22])).
% 2.77/1.00  
% 2.77/1.00  cnf(c_3,plain,
% 2.77/1.00      ( r2_hidden(X0,X1)
% 2.77/1.00      | r2_hidden(X1,X0)
% 2.77/1.00      | ~ v3_ordinal1(X1)
% 2.77/1.00      | ~ v3_ordinal1(X0)
% 2.77/1.00      | X0 = X1 ),
% 2.77/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1488,plain,
% 2.77/1.00      ( X0 = X1
% 2.77/1.00      | r2_hidden(X0,X1) = iProver_top
% 2.77/1.00      | r2_hidden(X1,X0) = iProver_top
% 2.77/1.00      | v3_ordinal1(X0) != iProver_top
% 2.77/1.00      | v3_ordinal1(X1) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_15,plain,
% 2.77/1.00      ( ~ r2_hidden(X0,X1)
% 2.77/1.00      | ~ v3_ordinal1(X1)
% 2.77/1.00      | ~ v3_ordinal1(X0)
% 2.77/1.00      | k1_wellord1(k1_wellord2(X1),X0) = X0 ),
% 2.77/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1478,plain,
% 2.77/1.00      ( k1_wellord1(k1_wellord2(X0),X1) = X1
% 2.77/1.00      | r2_hidden(X1,X0) != iProver_top
% 2.77/1.00      | v3_ordinal1(X1) != iProver_top
% 2.77/1.00      | v3_ordinal1(X0) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2612,plain,
% 2.77/1.00      ( X0 = X1
% 2.77/1.00      | k1_wellord1(k1_wellord2(X0),X1) = X1
% 2.77/1.00      | r2_hidden(X0,X1) = iProver_top
% 2.77/1.00      | v3_ordinal1(X1) != iProver_top
% 2.77/1.00      | v3_ordinal1(X0) != iProver_top ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_1488,c_1478]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_20,negated_conjecture,
% 2.77/1.00      ( v3_ordinal1(sK3) ),
% 2.77/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1475,plain,
% 2.77/1.00      ( v3_ordinal1(sK3) = iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_21,negated_conjecture,
% 2.77/1.00      ( v3_ordinal1(sK2) ),
% 2.77/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1474,plain,
% 2.77/1.00      ( v3_ordinal1(sK2) = iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2610,plain,
% 2.77/1.00      ( X0 = X1
% 2.77/1.00      | k1_wellord1(k1_wellord2(X1),X0) = X0
% 2.77/1.00      | r2_hidden(X1,X0) = iProver_top
% 2.77/1.00      | v3_ordinal1(X1) != iProver_top
% 2.77/1.00      | v3_ordinal1(X0) != iProver_top ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_1488,c_1478]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_0,plain,
% 2.77/1.00      ( r1_ordinal1(X0,X1)
% 2.77/1.00      | r1_ordinal1(X1,X0)
% 2.77/1.00      | ~ v3_ordinal1(X1)
% 2.77/1.00      | ~ v3_ordinal1(X0) ),
% 2.77/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1491,plain,
% 2.77/1.00      ( r1_ordinal1(X0,X1) = iProver_top
% 2.77/1.00      | r1_ordinal1(X1,X0) = iProver_top
% 2.77/1.00      | v3_ordinal1(X0) != iProver_top
% 2.77/1.00      | v3_ordinal1(X1) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2,plain,
% 2.77/1.00      ( r1_tarski(X0,X1)
% 2.77/1.00      | ~ r1_ordinal1(X0,X1)
% 2.77/1.00      | ~ v3_ordinal1(X1)
% 2.77/1.00      | ~ v3_ordinal1(X0) ),
% 2.77/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1489,plain,
% 2.77/1.00      ( r1_tarski(X0,X1) = iProver_top
% 2.77/1.00      | r1_ordinal1(X0,X1) != iProver_top
% 2.77/1.00      | v3_ordinal1(X0) != iProver_top
% 2.77/1.00      | v3_ordinal1(X1) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2212,plain,
% 2.77/1.00      ( r1_tarski(X0,X1) = iProver_top
% 2.77/1.00      | r1_ordinal1(X1,X0) = iProver_top
% 2.77/1.00      | v3_ordinal1(X1) != iProver_top
% 2.77/1.00      | v3_ordinal1(X0) != iProver_top ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_1491,c_1489]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_17,plain,
% 2.77/1.00      ( ~ r1_tarski(X0,X1)
% 2.77/1.00      | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ),
% 2.77/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1477,plain,
% 2.77/1.00      ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 2.77/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2723,plain,
% 2.77/1.00      ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 2.77/1.00      | r1_ordinal1(X0,X1) = iProver_top
% 2.77/1.00      | v3_ordinal1(X0) != iProver_top
% 2.77/1.00      | v3_ordinal1(X1) != iProver_top ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_2212,c_1477]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_3462,plain,
% 2.77/1.00      ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 2.77/1.00      | r1_tarski(X0,X1) = iProver_top
% 2.77/1.00      | v3_ordinal1(X0) != iProver_top
% 2.77/1.00      | v3_ordinal1(X1) != iProver_top ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_2723,c_1489]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_4,plain,
% 2.77/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 2.77/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1487,plain,
% 2.77/1.00      ( r2_hidden(X0,X1) != iProver_top | r1_tarski(X1,X0) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_3584,plain,
% 2.77/1.00      ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 2.77/1.00      | r2_hidden(X1,X0) != iProver_top
% 2.77/1.00      | v3_ordinal1(X0) != iProver_top
% 2.77/1.00      | v3_ordinal1(X1) != iProver_top ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_3462,c_1487]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_4183,plain,
% 2.77/1.00      ( X0 = X1
% 2.77/1.00      | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
% 2.77/1.00      | k1_wellord1(k1_wellord2(X0),X1) = X1
% 2.77/1.00      | v3_ordinal1(X1) != iProver_top
% 2.77/1.00      | v3_ordinal1(X0) != iProver_top ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_2610,c_3584]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_6096,plain,
% 2.77/1.00      ( k2_wellord1(k1_wellord2(X0),sK2) = k1_wellord2(sK2)
% 2.77/1.00      | k1_wellord1(k1_wellord2(sK2),X0) = X0
% 2.77/1.00      | sK2 = X0
% 2.77/1.00      | v3_ordinal1(X0) != iProver_top ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_1474,c_4183]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_6612,plain,
% 2.77/1.00      ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
% 2.77/1.00      | k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 2.77/1.00      | sK3 = sK2 ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_1475,c_6096]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_18,negated_conjecture,
% 2.77/1.00      ( sK2 != sK3 ),
% 2.77/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_63,plain,
% 2.77/1.00      ( ~ r2_hidden(sK2,sK2) | ~ r1_tarski(sK2,sK2) ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_66,plain,
% 2.77/1.00      ( r2_hidden(sK2,sK2) | ~ v3_ordinal1(sK2) | sK2 = sK2 ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_69,plain,
% 2.77/1.00      ( r1_tarski(sK2,sK2) | ~ r1_ordinal1(sK2,sK2) | ~ v3_ordinal1(sK2) ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_75,plain,
% 2.77/1.00      ( r1_ordinal1(sK2,sK2) | ~ v3_ordinal1(sK2) ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1111,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1680,plain,
% 2.77/1.00      ( sK3 != X0 | sK2 != X0 | sK2 = sK3 ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_1111]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1681,plain,
% 2.77/1.00      ( sK3 != sK2 | sK2 = sK3 | sK2 != sK2 ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_1680]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_6620,plain,
% 2.77/1.00      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 2.77/1.00      | k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2) ),
% 2.77/1.00      inference(global_propositional_subsumption,
% 2.77/1.00                [status(thm)],
% 2.77/1.00                [c_6612,c_21,c_18,c_63,c_66,c_69,c_75,c_1681]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_6621,plain,
% 2.77/1.00      ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
% 2.77/1.00      | k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
% 2.77/1.00      inference(renaming,[status(thm)],[c_6620]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_4184,plain,
% 2.77/1.00      ( X0 = X1
% 2.77/1.00      | k1_wellord1(k1_wellord2(X1),X0) = X0
% 2.77/1.00      | k1_wellord1(k1_wellord2(X0),X1) = X1
% 2.77/1.00      | v3_ordinal1(X1) != iProver_top
% 2.77/1.00      | v3_ordinal1(X0) != iProver_top ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_2610,c_1478]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_4912,plain,
% 2.77/1.00      ( k1_wellord1(k1_wellord2(X0),sK3) = sK3
% 2.77/1.00      | k1_wellord1(k1_wellord2(sK3),X0) = X0
% 2.77/1.00      | sK3 = X0
% 2.77/1.00      | v3_ordinal1(X0) != iProver_top ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_1475,c_4184]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_4940,plain,
% 2.77/1.00      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 2.77/1.00      | k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 2.77/1.00      | sK3 = sK2 ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_1474,c_4912]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_5123,plain,
% 2.77/1.00      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 2.77/1.00      | k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
% 2.77/1.00      inference(global_propositional_subsumption,
% 2.77/1.00                [status(thm)],
% 2.77/1.00                [c_4940,c_21,c_18,c_63,c_66,c_69,c_75,c_1681]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_5124,plain,
% 2.77/1.00      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 2.77/1.00      | k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
% 2.77/1.00      inference(renaming,[status(thm)],[c_5123]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_6,plain,
% 2.77/1.00      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
% 2.77/1.00      | ~ r2_hidden(X1,k3_relat_1(X0))
% 2.77/1.00      | ~ v2_wellord1(X0)
% 2.77/1.00      | ~ v1_relat_1(X0) ),
% 2.77/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_16,plain,
% 2.77/1.00      ( v2_wellord1(k1_wellord2(X0)) | ~ v3_ordinal1(X0) ),
% 2.77/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_242,plain,
% 2.77/1.00      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
% 2.77/1.00      | ~ r2_hidden(X1,k3_relat_1(X0))
% 2.77/1.00      | ~ v1_relat_1(X0)
% 2.77/1.00      | ~ v3_ordinal1(X2)
% 2.77/1.00      | k1_wellord2(X2) != X0 ),
% 2.77/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_16]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_243,plain,
% 2.77/1.00      ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
% 2.77/1.00      | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
% 2.77/1.00      | ~ v1_relat_1(k1_wellord2(X0))
% 2.77/1.00      | ~ v3_ordinal1(X0) ),
% 2.77/1.00      inference(unflattening,[status(thm)],[c_242]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_14,plain,
% 2.77/1.00      ( v1_relat_1(k1_wellord2(X0)) ),
% 2.77/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_247,plain,
% 2.77/1.00      ( ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
% 2.77/1.00      | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
% 2.77/1.00      | ~ v3_ordinal1(X0) ),
% 2.77/1.00      inference(global_propositional_subsumption,[status(thm)],[c_243,c_14]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_248,plain,
% 2.77/1.00      ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
% 2.77/1.00      | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
% 2.77/1.00      | ~ v3_ordinal1(X0) ),
% 2.77/1.00      inference(renaming,[status(thm)],[c_247]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1473,plain,
% 2.77/1.00      ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
% 2.77/1.00      | r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) != iProver_top
% 2.77/1.00      | v3_ordinal1(X0) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_248]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_13,plain,
% 2.77/1.00      ( ~ v1_relat_1(k1_wellord2(X0)) | k3_relat_1(k1_wellord2(X0)) = X0 ),
% 2.77/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_127,plain,
% 2.77/1.00      ( k3_relat_1(k1_wellord2(X0)) = X0 ),
% 2.77/1.00      inference(global_propositional_subsumption,[status(thm)],[c_13,c_14]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1574,plain,
% 2.77/1.00      ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
% 2.77/1.00      | r2_hidden(X1,X0) != iProver_top
% 2.77/1.00      | v3_ordinal1(X0) != iProver_top ),
% 2.77/1.00      inference(light_normalisation,[status(thm)],[c_1473,c_127]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_5127,plain,
% 2.77/1.00      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 2.77/1.00      | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top
% 2.77/1.00      | r2_hidden(sK2,sK3) != iProver_top
% 2.77/1.00      | v3_ordinal1(sK3) != iProver_top ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_5124,c_1574]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_22,plain,
% 2.77/1.00      ( v3_ordinal1(sK2) = iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_23,plain,
% 2.77/1.00      ( v3_ordinal1(sK3) = iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1686,plain,
% 2.77/1.00      ( r2_hidden(sK3,sK2)
% 2.77/1.00      | r2_hidden(sK2,sK3)
% 2.77/1.00      | ~ v3_ordinal1(sK3)
% 2.77/1.00      | ~ v3_ordinal1(sK2)
% 2.77/1.00      | sK2 = sK3 ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1687,plain,
% 2.77/1.00      ( sK2 = sK3
% 2.77/1.00      | r2_hidden(sK3,sK2) = iProver_top
% 2.77/1.00      | r2_hidden(sK2,sK3) = iProver_top
% 2.77/1.00      | v3_ordinal1(sK3) != iProver_top
% 2.77/1.00      | v3_ordinal1(sK2) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_1686]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1715,plain,
% 2.77/1.00      ( ~ r2_hidden(sK3,sK2)
% 2.77/1.00      | ~ v3_ordinal1(sK3)
% 2.77/1.00      | ~ v3_ordinal1(sK2)
% 2.77/1.00      | k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1716,plain,
% 2.77/1.00      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 2.77/1.00      | r2_hidden(sK3,sK2) != iProver_top
% 2.77/1.00      | v3_ordinal1(sK3) != iProver_top
% 2.77/1.00      | v3_ordinal1(sK2) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_1715]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_5268,plain,
% 2.77/1.00      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 2.77/1.00      | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top ),
% 2.77/1.00      inference(global_propositional_subsumption,
% 2.77/1.00                [status(thm)],
% 2.77/1.00                [c_5127,c_22,c_23,c_18,c_1687,c_1716]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_6624,plain,
% 2.77/1.00      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 2.77/1.00      | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) != iProver_top ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_6621,c_5268]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_19,negated_conjecture,
% 2.77/1.00      ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) ),
% 2.77/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1476,plain,
% 2.77/1.00      ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) = iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_5,plain,
% 2.77/1.00      ( ~ r4_wellord1(X0,X1)
% 2.77/1.00      | r4_wellord1(X1,X0)
% 2.77/1.00      | ~ v1_relat_1(X1)
% 2.77/1.00      | ~ v1_relat_1(X0) ),
% 2.77/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1486,plain,
% 2.77/1.00      ( r4_wellord1(X0,X1) != iProver_top
% 2.77/1.00      | r4_wellord1(X1,X0) = iProver_top
% 2.77/1.00      | v1_relat_1(X0) != iProver_top
% 2.77/1.00      | v1_relat_1(X1) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2079,plain,
% 2.77/1.00      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top
% 2.77/1.00      | v1_relat_1(k1_wellord2(sK3)) != iProver_top
% 2.77/1.00      | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_1476,c_1486]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_34,plain,
% 2.77/1.00      ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_36,plain,
% 2.77/1.00      ( v1_relat_1(k1_wellord2(sK2)) = iProver_top ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_34]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2082,plain,
% 2.77/1.00      ( v1_relat_1(k1_wellord2(sK3)) != iProver_top
% 2.77/1.00      | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top ),
% 2.77/1.00      inference(global_propositional_subsumption,[status(thm)],[c_2079,c_36]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2083,plain,
% 2.77/1.00      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top
% 2.77/1.00      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 2.77/1.00      inference(renaming,[status(thm)],[c_2082]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1479,plain,
% 2.77/1.00      ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2088,plain,
% 2.77/1.00      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top ),
% 2.77/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_2083,c_1479]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_6786,plain,
% 2.77/1.00      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
% 2.77/1.00      inference(global_propositional_subsumption,[status(thm)],[c_6624,c_2088]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_6789,plain,
% 2.77/1.00      ( r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top
% 2.77/1.00      | r2_hidden(sK3,sK2) != iProver_top
% 2.77/1.00      | v3_ordinal1(sK2) != iProver_top ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_6786,c_1574]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_24,plain,
% 2.77/1.00      ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) = iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1120,plain,
% 2.77/1.00      ( X0 != X1 | k1_wellord2(X0) = k1_wellord2(X1) ),
% 2.77/1.00      theory(equality) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1132,plain,
% 2.77/1.00      ( k1_wellord2(sK2) = k1_wellord2(sK2) | sK2 != sK2 ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_1120]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1714,plain,
% 2.77/1.00      ( ~ r2_hidden(sK3,sK2) | ~ r1_tarski(sK2,sK3) ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1718,plain,
% 2.77/1.00      ( r2_hidden(sK3,sK2) != iProver_top | r1_tarski(sK2,sK3) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_1714]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1743,plain,
% 2.77/1.00      ( ~ r1_tarski(sK3,X0)
% 2.77/1.00      | k2_wellord1(k1_wellord2(X0),sK3) = k1_wellord2(sK3) ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1748,plain,
% 2.77/1.00      ( k2_wellord1(k1_wellord2(X0),sK3) = k1_wellord2(sK3)
% 2.77/1.00      | r1_tarski(sK3,X0) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_1743]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1750,plain,
% 2.77/1.00      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 2.77/1.00      | r1_tarski(sK3,sK2) != iProver_top ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_1748]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1871,plain,
% 2.77/1.00      ( r1_tarski(sK2,sK3)
% 2.77/1.00      | ~ r1_ordinal1(sK2,sK3)
% 2.77/1.00      | ~ v3_ordinal1(sK3)
% 2.77/1.00      | ~ v3_ordinal1(sK2) ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1872,plain,
% 2.77/1.00      ( r1_tarski(sK2,sK3) = iProver_top
% 2.77/1.00      | r1_ordinal1(sK2,sK3) != iProver_top
% 2.77/1.00      | v3_ordinal1(sK3) != iProver_top
% 2.77/1.00      | v3_ordinal1(sK2) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_1871]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1886,plain,
% 2.77/1.00      ( r1_tarski(sK3,X0)
% 2.77/1.00      | ~ r1_ordinal1(sK3,X0)
% 2.77/1.00      | ~ v3_ordinal1(X0)
% 2.77/1.00      | ~ v3_ordinal1(sK3) ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1887,plain,
% 2.77/1.00      ( r1_tarski(sK3,X0) = iProver_top
% 2.77/1.00      | r1_ordinal1(sK3,X0) != iProver_top
% 2.77/1.00      | v3_ordinal1(X0) != iProver_top
% 2.77/1.00      | v3_ordinal1(sK3) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_1886]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1889,plain,
% 2.77/1.00      ( r1_tarski(sK3,sK2) = iProver_top
% 2.77/1.00      | r1_ordinal1(sK3,sK2) != iProver_top
% 2.77/1.00      | v3_ordinal1(sK3) != iProver_top
% 2.77/1.00      | v3_ordinal1(sK2) != iProver_top ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_1887]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1115,plain,
% 2.77/1.00      ( ~ r4_wellord1(X0,X1) | r4_wellord1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.77/1.00      theory(equality) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1694,plain,
% 2.77/1.00      ( r4_wellord1(X0,X1)
% 2.77/1.00      | ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
% 2.77/1.00      | X1 != k1_wellord2(sK3)
% 2.77/1.00      | X0 != k1_wellord2(sK2) ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_1115]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1742,plain,
% 2.77/1.00      ( r4_wellord1(X0,k2_wellord1(k1_wellord2(X1),sK3))
% 2.77/1.00      | ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
% 2.77/1.00      | X0 != k1_wellord2(sK2)
% 2.77/1.00      | k2_wellord1(k1_wellord2(X1),sK3) != k1_wellord2(sK3) ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_1694]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2017,plain,
% 2.77/1.00      ( r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(X0),sK3))
% 2.77/1.00      | ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
% 2.77/1.00      | k2_wellord1(k1_wellord2(X0),sK3) != k1_wellord2(sK3)
% 2.77/1.00      | k1_wellord2(sK2) != k1_wellord2(sK2) ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_1742]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2019,plain,
% 2.77/1.00      ( k2_wellord1(k1_wellord2(X0),sK3) != k1_wellord2(sK3)
% 2.77/1.00      | k1_wellord2(sK2) != k1_wellord2(sK2)
% 2.77/1.00      | r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(X0),sK3)) = iProver_top
% 2.77/1.00      | r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_2017]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2021,plain,
% 2.77/1.00      ( k2_wellord1(k1_wellord2(sK2),sK3) != k1_wellord2(sK3)
% 2.77/1.00      | k1_wellord2(sK2) != k1_wellord2(sK2)
% 2.77/1.00      | r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) = iProver_top
% 2.77/1.00      | r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) != iProver_top ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_2019]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2266,plain,
% 2.77/1.00      ( r1_ordinal1(sK3,sK2)
% 2.77/1.00      | r1_ordinal1(sK2,sK3)
% 2.77/1.00      | ~ v3_ordinal1(sK3)
% 2.77/1.00      | ~ v3_ordinal1(sK2) ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_2267,plain,
% 2.77/1.00      ( r1_ordinal1(sK3,sK2) = iProver_top
% 2.77/1.00      | r1_ordinal1(sK2,sK3) = iProver_top
% 2.77/1.00      | v3_ordinal1(sK3) != iProver_top
% 2.77/1.00      | v3_ordinal1(sK2) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_2266]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_7351,plain,
% 2.77/1.00      ( r2_hidden(sK3,sK2) != iProver_top ),
% 2.77/1.00      inference(global_propositional_subsumption,
% 2.77/1.00                [status(thm)],
% 2.77/1.00                [c_6789,c_21,c_22,c_23,c_24,c_63,c_66,c_69,c_75,c_1132,
% 2.77/1.00                 c_1718,c_1750,c_1872,c_1889,c_2021,c_2267]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_7361,plain,
% 2.77/1.00      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 2.77/1.00      | sK3 = sK2
% 2.77/1.00      | v3_ordinal1(sK3) != iProver_top
% 2.77/1.00      | v3_ordinal1(sK2) != iProver_top ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_2612,c_7351]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1813,plain,
% 2.77/1.00      ( ~ r2_hidden(sK2,sK3)
% 2.77/1.00      | ~ v3_ordinal1(sK3)
% 2.77/1.00      | ~ v3_ordinal1(sK2)
% 2.77/1.00      | k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
% 2.77/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_1814,plain,
% 2.77/1.00      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 2.77/1.00      | r2_hidden(sK2,sK3) != iProver_top
% 2.77/1.00      | v3_ordinal1(sK3) != iProver_top
% 2.77/1.00      | v3_ordinal1(sK2) != iProver_top ),
% 2.77/1.00      inference(predicate_to_equality,[status(thm)],[c_1813]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_7577,plain,
% 2.77/1.00      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
% 2.77/1.00      inference(global_propositional_subsumption,
% 2.77/1.00                [status(thm)],
% 2.77/1.00                [c_7361,c_21,c_22,c_23,c_24,c_18,c_63,c_66,c_69,c_75,c_1132,
% 2.77/1.00                 c_1687,c_1718,c_1750,c_1814,c_1872,c_1889,c_2021,c_2267,
% 2.77/1.00                 c_6789]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_7580,plain,
% 2.77/1.00      ( r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top
% 2.77/1.00      | r2_hidden(sK2,sK3) != iProver_top
% 2.77/1.00      | v3_ordinal1(sK3) != iProver_top ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_7577,c_1574]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_7969,plain,
% 2.77/1.00      ( r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top ),
% 2.77/1.00      inference(global_propositional_subsumption,
% 2.77/1.00                [status(thm)],
% 2.77/1.00                [c_7580,c_21,c_22,c_23,c_24,c_18,c_63,c_66,c_69,c_75,c_1132,
% 2.77/1.00                 c_1687,c_1718,c_1750,c_1872,c_1889,c_2021,c_2267,c_6789]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_3610,plain,
% 2.77/1.00      ( X0 = X1
% 2.77/1.00      | k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 2.77/1.00      | r2_hidden(X0,X1) = iProver_top
% 2.77/1.00      | v3_ordinal1(X1) != iProver_top
% 2.77/1.00      | v3_ordinal1(X0) != iProver_top ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_1488,c_3584]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_7360,plain,
% 2.77/1.00      ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
% 2.77/1.00      | sK3 = sK2
% 2.77/1.00      | v3_ordinal1(sK3) != iProver_top
% 2.77/1.00      | v3_ordinal1(sK2) != iProver_top ),
% 2.77/1.00      inference(superposition,[status(thm)],[c_3610,c_7351]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_7649,plain,
% 2.77/1.00      ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2) ),
% 2.77/1.00      inference(global_propositional_subsumption,
% 2.77/1.00                [status(thm)],
% 2.77/1.00                [c_7360,c_21,c_22,c_23,c_18,c_63,c_66,c_69,c_75,c_1681]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_7973,plain,
% 2.77/1.00      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) != iProver_top ),
% 2.77/1.00      inference(light_normalisation,[status(thm)],[c_7969,c_7649]) ).
% 2.77/1.00  
% 2.77/1.00  cnf(c_7975,plain,
% 2.77/1.00      ( $false ),
% 2.77/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_7973,c_2088]) ).
% 2.77/1.00  
% 2.77/1.00  
% 2.77/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.77/1.00  
% 2.77/1.00  ------                               Statistics
% 2.77/1.00  
% 2.77/1.00  ------ General
% 2.77/1.00  
% 2.77/1.00  abstr_ref_over_cycles:                  0
% 2.77/1.00  abstr_ref_under_cycles:                 0
% 2.77/1.00  gc_basic_clause_elim:                   0
% 2.77/1.00  forced_gc_time:                         0
% 2.77/1.00  parsing_time:                           0.011
% 2.77/1.00  unif_index_cands_time:                  0.
% 2.77/1.00  unif_index_add_time:                    0.
% 2.77/1.00  orderings_time:                         0.
% 2.77/1.00  out_proof_time:                         0.012
% 2.77/1.00  total_time:                             0.231
% 2.77/1.00  num_of_symbols:                         47
% 2.77/1.00  num_of_terms:                           6360
% 2.77/1.00  
% 2.77/1.00  ------ Preprocessing
% 2.77/1.00  
% 2.77/1.00  num_of_splits:                          0
% 2.77/1.00  num_of_split_atoms:                     0
% 2.77/1.00  num_of_reused_defs:                     0
% 2.77/1.00  num_eq_ax_congr_red:                    15
% 2.77/1.00  num_of_sem_filtered_clauses:            1
% 2.77/1.00  num_of_subtypes:                        0
% 2.77/1.00  monotx_restored_types:                  0
% 2.77/1.00  sat_num_of_epr_types:                   0
% 2.77/1.00  sat_num_of_non_cyclic_types:            0
% 2.77/1.00  sat_guarded_non_collapsed_types:        0
% 2.77/1.00  num_pure_diseq_elim:                    0
% 2.77/1.00  simp_replaced_by:                       0
% 2.77/1.00  res_preprocessed:                       114
% 2.77/1.00  prep_upred:                             0
% 2.77/1.00  prep_unflattend:                        45
% 2.77/1.00  smt_new_axioms:                         0
% 2.77/1.00  pred_elim_cands:                        6
% 2.77/1.00  pred_elim:                              1
% 2.77/1.00  pred_elim_cl:                           1
% 2.77/1.00  pred_elim_cycles:                       3
% 2.77/1.00  merged_defs:                            0
% 2.77/1.00  merged_defs_ncl:                        0
% 2.77/1.00  bin_hyper_res:                          0
% 2.77/1.00  prep_cycles:                            4
% 2.77/1.00  pred_elim_time:                         0.015
% 2.77/1.00  splitting_time:                         0.
% 2.77/1.00  sem_filter_time:                        0.
% 2.77/1.00  monotx_time:                            0.
% 2.77/1.00  subtype_inf_time:                       0.
% 2.77/1.00  
% 2.77/1.00  ------ Problem properties
% 2.77/1.00  
% 2.77/1.00  clauses:                                21
% 2.77/1.00  conjectures:                            4
% 2.77/1.00  epr:                                    9
% 2.77/1.00  horn:                                   16
% 2.77/1.00  ground:                                 4
% 2.77/1.00  unary:                                  6
% 2.77/1.00  binary:                                 2
% 2.77/1.00  lits:                                   62
% 2.77/1.00  lits_eq:                                9
% 2.77/1.00  fd_pure:                                0
% 2.77/1.00  fd_pseudo:                              0
% 2.77/1.00  fd_cond:                                0
% 2.77/1.00  fd_pseudo_cond:                         1
% 2.77/1.00  ac_symbols:                             0
% 2.77/1.00  
% 2.77/1.00  ------ Propositional Solver
% 2.77/1.00  
% 2.77/1.00  prop_solver_calls:                      29
% 2.77/1.00  prop_fast_solver_calls:                 1234
% 2.77/1.00  smt_solver_calls:                       0
% 2.77/1.00  smt_fast_solver_calls:                  0
% 2.77/1.00  prop_num_of_clauses:                    2550
% 2.77/1.00  prop_preprocess_simplified:             7457
% 2.77/1.00  prop_fo_subsumed:                       36
% 2.77/1.00  prop_solver_time:                       0.
% 2.77/1.00  smt_solver_time:                        0.
% 2.77/1.00  smt_fast_solver_time:                   0.
% 2.77/1.00  prop_fast_solver_time:                  0.
% 2.77/1.00  prop_unsat_core_time:                   0.
% 2.77/1.00  
% 2.77/1.00  ------ QBF
% 2.77/1.00  
% 2.77/1.00  qbf_q_res:                              0
% 2.77/1.00  qbf_num_tautologies:                    0
% 2.77/1.00  qbf_prep_cycles:                        0
% 2.77/1.00  
% 2.77/1.00  ------ BMC1
% 2.77/1.00  
% 2.77/1.00  bmc1_current_bound:                     -1
% 2.77/1.00  bmc1_last_solved_bound:                 -1
% 2.77/1.00  bmc1_unsat_core_size:                   -1
% 2.77/1.00  bmc1_unsat_core_parents_size:           -1
% 2.77/1.00  bmc1_merge_next_fun:                    0
% 2.77/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.77/1.00  
% 2.77/1.00  ------ Instantiation
% 2.77/1.00  
% 2.77/1.00  inst_num_of_clauses:                    799
% 2.77/1.00  inst_num_in_passive:                    250
% 2.77/1.00  inst_num_in_active:                     352
% 2.77/1.00  inst_num_in_unprocessed:                197
% 2.77/1.00  inst_num_of_loops:                      450
% 2.77/1.00  inst_num_of_learning_restarts:          0
% 2.77/1.00  inst_num_moves_active_passive:          94
% 2.77/1.00  inst_lit_activity:                      0
% 2.77/1.00  inst_lit_activity_moves:                0
% 2.77/1.00  inst_num_tautologies:                   0
% 2.77/1.00  inst_num_prop_implied:                  0
% 2.77/1.00  inst_num_existing_simplified:           0
% 2.77/1.00  inst_num_eq_res_simplified:             0
% 2.77/1.00  inst_num_child_elim:                    0
% 2.77/1.00  inst_num_of_dismatching_blockings:      520
% 2.77/1.00  inst_num_of_non_proper_insts:           955
% 2.77/1.00  inst_num_of_duplicates:                 0
% 2.77/1.00  inst_inst_num_from_inst_to_res:         0
% 2.77/1.00  inst_dismatching_checking_time:         0.
% 2.77/1.00  
% 2.77/1.00  ------ Resolution
% 2.77/1.00  
% 2.77/1.00  res_num_of_clauses:                     0
% 2.77/1.00  res_num_in_passive:                     0
% 2.77/1.00  res_num_in_active:                      0
% 2.77/1.00  res_num_of_loops:                       118
% 2.77/1.00  res_forward_subset_subsumed:            55
% 2.77/1.00  res_backward_subset_subsumed:           0
% 2.77/1.00  res_forward_subsumed:                   0
% 2.77/1.00  res_backward_subsumed:                  0
% 2.77/1.00  res_forward_subsumption_resolution:     8
% 2.77/1.00  res_backward_subsumption_resolution:    0
% 2.77/1.00  res_clause_to_clause_subsumption:       808
% 2.77/1.00  res_orphan_elimination:                 0
% 2.77/1.00  res_tautology_del:                      59
% 2.77/1.00  res_num_eq_res_simplified:              0
% 2.77/1.00  res_num_sel_changes:                    0
% 2.77/1.00  res_moves_from_active_to_pass:          0
% 2.77/1.00  
% 2.77/1.00  ------ Superposition
% 2.77/1.00  
% 2.77/1.00  sup_time_total:                         0.
% 2.77/1.00  sup_time_generating:                    0.
% 2.77/1.00  sup_time_sim_full:                      0.
% 2.77/1.00  sup_time_sim_immed:                     0.
% 2.77/1.00  
% 2.77/1.00  sup_num_of_clauses:                     94
% 2.77/1.00  sup_num_in_active:                      85
% 2.77/1.00  sup_num_in_passive:                     9
% 2.77/1.00  sup_num_of_loops:                       89
% 2.77/1.00  sup_fw_superposition:                   119
% 2.77/1.00  sup_bw_superposition:                   110
% 2.77/1.00  sup_immediate_simplified:               56
% 2.77/1.00  sup_given_eliminated:                   0
% 2.77/1.00  comparisons_done:                       0
% 2.77/1.00  comparisons_avoided:                    66
% 2.77/1.00  
% 2.77/1.00  ------ Simplifications
% 2.77/1.00  
% 2.77/1.00  
% 2.77/1.00  sim_fw_subset_subsumed:                 16
% 2.77/1.00  sim_bw_subset_subsumed:                 6
% 2.77/1.00  sim_fw_subsumed:                        14
% 2.77/1.00  sim_bw_subsumed:                        0
% 2.77/1.00  sim_fw_subsumption_res:                 4
% 2.77/1.00  sim_bw_subsumption_res:                 0
% 2.77/1.00  sim_tautology_del:                      4
% 2.77/1.00  sim_eq_tautology_del:                   39
% 2.77/1.00  sim_eq_res_simp:                        1
% 2.77/1.00  sim_fw_demodulated:                     0
% 2.77/1.00  sim_bw_demodulated:                     0
% 2.77/1.00  sim_light_normalised:                   28
% 2.77/1.00  sim_joinable_taut:                      0
% 2.77/1.00  sim_joinable_simp:                      0
% 2.77/1.00  sim_ac_normalised:                      0
% 2.77/1.00  sim_smt_subsumption:                    0
% 2.77/1.00  
%------------------------------------------------------------------------------
