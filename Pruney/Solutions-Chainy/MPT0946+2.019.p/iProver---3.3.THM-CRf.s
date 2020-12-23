%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:44 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 721 expanded)
%              Number of clauses        :  108 ( 273 expanded)
%              Number of leaves         :   23 ( 155 expanded)
%              Depth                    :   18
%              Number of atoms          :  686 (2858 expanded)
%              Number of equality atoms :  295 ( 945 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   17 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
     => ( sK4 != X0
        & r4_wellord1(k1_wellord2(X0),k1_wellord2(sK4))
        & v3_ordinal1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
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

fof(f52,plain,
    ( sK3 != sK4
    & r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4))
    & v3_ordinal1(sK4)
    & v3_ordinal1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f38,f51,f50])).

fof(f79,plain,(
    v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f80,plain,(
    v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
           => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_wellord1(k1_wellord2(X1),X0) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f82,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f52])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f77,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
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

fof(f31,plain,(
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

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f48,plain,(
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

fof(f49,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f47,f48])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f93,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f68])).

fof(f81,plain,(
    r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) ),
    inference(cnf_transformation,[],[f52])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r4_wellord1(X1,X0)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
       => ( r2_hidden(X0,X1)
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0)
          | sK0(X0,X1,X2) = X1
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0)
            & sK0(X0,X1,X2) != X1 )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ( ( ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0)
                | sK0(X0,X1,X2) = X1
                | ~ r2_hidden(sK0(X0,X1,X2),X2) )
              & ( ( r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0)
                  & sK0(X0,X1,X2) != X1 )
                | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 != X4
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f85,plain,(
    ! [X4,X2,X0] :
      ( ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X4) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f86,plain,(
    ! [X4,X0] :
      ( ~ r2_hidden(X4,k1_wellord1(X0,X4))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f85])).

cnf(c_29,negated_conjecture,
    ( v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1474,plain,
    ( v3_ordinal1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1475,plain,
    ( v3_ordinal1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_ordinal1(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_3,plain,
    ( r2_hidden(X0,X1)
    | r1_ordinal1(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_375,plain,
    ( r2_hidden(X0,X1)
    | r1_tarski(X2,X3)
    | ~ v3_ordinal1(X3)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X1 != X2
    | X0 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_3])).

cnf(c_376,plain,
    ( r2_hidden(X0,X1)
    | r1_tarski(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_1471,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_376])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | k1_wellord1(k1_wellord2(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1478,plain,
    ( k1_wellord1(k1_wellord2(X0),X1) = X1
    | r2_hidden(X1,X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2868,plain,
    ( k1_wellord1(k1_wellord2(X0),X1) = X1
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1471,c_1478])).

cnf(c_25,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1477,plain,
    ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5490,plain,
    ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | k1_wellord1(k1_wellord2(X1),X0) = X0
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2868,c_1477])).

cnf(c_5499,plain,
    ( k2_wellord1(k1_wellord2(sK4),X0) = k1_wellord2(X0)
    | k1_wellord1(k1_wellord2(X0),sK4) = sK4
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1475,c_5490])).

cnf(c_5569,plain,
    ( k2_wellord1(k1_wellord2(sK4),sK3) = k1_wellord2(sK3)
    | k1_wellord1(k1_wellord2(sK3),sK4) = sK4 ),
    inference(superposition,[status(thm)],[c_1474,c_5499])).

cnf(c_2,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1495,plain,
    ( X0 = X1
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3193,plain,
    ( X0 = X1
    | k1_wellord1(k1_wellord2(X0),X1) = X1
    | r2_hidden(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1495,c_1478])).

cnf(c_6889,plain,
    ( X0 = X1
    | k1_wellord1(k1_wellord2(X0),X1) = X1
    | k1_wellord1(k1_wellord2(X1),X0) = X0
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3193,c_1478])).

cnf(c_8536,plain,
    ( k1_wellord1(k1_wellord2(X0),sK4) = sK4
    | k1_wellord1(k1_wellord2(sK4),X0) = X0
    | sK4 = X0
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1475,c_6889])).

cnf(c_8564,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3
    | k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | sK4 = sK3 ),
    inference(superposition,[status(thm)],[c_1474,c_8536])).

cnf(c_26,negated_conjecture,
    ( sK3 != sK4 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1022,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1049,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1022])).

cnf(c_1023,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1745,plain,
    ( sK4 != X0
    | sK3 != X0
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_1023])).

cnf(c_1746,plain,
    ( sK4 != sK3
    | sK3 = sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1745])).

cnf(c_8785,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | k1_wellord1(k1_wellord2(sK4),sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8564,c_26,c_1049,c_1746])).

cnf(c_8786,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3
    | k1_wellord1(k1_wellord2(sK3),sK4) = sK4 ),
    inference(renaming,[status(thm)],[c_8785])).

cnf(c_14,plain,
    ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
    | ~ r2_hidden(X1,k3_relat_1(X0))
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_24,plain,
    ( v2_wellord1(k1_wellord2(X0))
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_328,plain,
    ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
    | ~ r2_hidden(X1,k3_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v3_ordinal1(X2)
    | k1_wellord2(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_24])).

cnf(c_329,plain,
    ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
    | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
    | ~ v1_relat_1(k1_wellord2(X0))
    | ~ v3_ordinal1(X0) ),
    inference(unflattening,[status(thm)],[c_328])).

cnf(c_22,plain,
    ( v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_333,plain,
    ( ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
    | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
    | ~ v3_ordinal1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_329,c_22])).

cnf(c_334,plain,
    ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
    | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
    | ~ v3_ordinal1(X0) ),
    inference(renaming,[status(thm)],[c_333])).

cnf(c_1473,plain,
    ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
    | r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_334])).

cnf(c_21,plain,
    ( ~ v1_relat_1(k1_wellord2(X0))
    | k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_173,plain,
    ( k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_21,c_22])).

cnf(c_1592,plain,
    ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1473,c_173])).

cnf(c_8792,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) != iProver_top
    | r2_hidden(sK3,sK4) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8786,c_1592])).

cnf(c_30,plain,
    ( v3_ordinal1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_31,plain,
    ( v3_ordinal1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1985,plain,
    ( ~ r2_hidden(sK4,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK4)
    | k1_wellord1(k1_wellord2(X0),sK4) = sK4 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1987,plain,
    ( k1_wellord1(k1_wellord2(X0),sK4) = sK4
    | r2_hidden(sK4,X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1985])).

cnf(c_1989,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | r2_hidden(sK4,sK3) != iProver_top
    | v3_ordinal1(sK4) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1987])).

cnf(c_2003,plain,
    ( r2_hidden(sK4,sK3)
    | r2_hidden(sK3,sK4)
    | ~ v3_ordinal1(sK4)
    | ~ v3_ordinal1(sK3)
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2004,plain,
    ( sK3 = sK4
    | r2_hidden(sK4,sK3) = iProver_top
    | r2_hidden(sK3,sK4) = iProver_top
    | v3_ordinal1(sK4) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2003])).

cnf(c_9220,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8792,c_30,c_31,c_26,c_1989,c_2004])).

cnf(c_9226,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5569,c_9220])).

cnf(c_27,negated_conjecture,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1476,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_13,plain,
    ( ~ r4_wellord1(X0,X1)
    | r4_wellord1(X1,X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1486,plain,
    ( r4_wellord1(X0,X1) != iProver_top
    | r4_wellord1(X1,X0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3126,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1476,c_1486])).

cnf(c_42,plain,
    ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_44,plain,
    ( v1_relat_1(k1_wellord2(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_3392,plain,
    ( v1_relat_1(k1_wellord2(sK4)) != iProver_top
    | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3126,c_44])).

cnf(c_3393,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3392])).

cnf(c_1479,plain,
    ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3398,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3393,c_1479])).

cnf(c_9426,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9226,c_3398])).

cnf(c_12,plain,
    ( ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0)
    | k3_relat_1(k2_wellord1(X0,k1_wellord1(X0,X1))) = k1_wellord1(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_349,plain,
    ( ~ v1_relat_1(X0)
    | ~ v3_ordinal1(X1)
    | k1_wellord2(X1) != X0
    | k3_relat_1(k2_wellord1(X0,k1_wellord1(X0,X2))) = k1_wellord1(X0,X2) ),
    inference(resolution_lifted,[status(thm)],[c_12,c_24])).

cnf(c_350,plain,
    ( ~ v1_relat_1(k1_wellord2(X0))
    | ~ v3_ordinal1(X0)
    | k3_relat_1(k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) = k1_wellord1(k1_wellord2(X0),X1) ),
    inference(unflattening,[status(thm)],[c_349])).

cnf(c_354,plain,
    ( ~ v3_ordinal1(X0)
    | k3_relat_1(k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) = k1_wellord1(k1_wellord2(X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_350,c_22])).

cnf(c_1472,plain,
    ( k3_relat_1(k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) = k1_wellord1(k1_wellord2(X0),X1)
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_354])).

cnf(c_2358,plain,
    ( k3_relat_1(k2_wellord1(k1_wellord2(sK3),k1_wellord1(k1_wellord2(sK3),X0))) = k1_wellord1(k1_wellord2(sK3),X0) ),
    inference(superposition,[status(thm)],[c_1474,c_1472])).

cnf(c_11,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1487,plain,
    ( r2_hidden(X0,k3_relat_1(X1)) = iProver_top
    | r2_hidden(X0,k3_relat_1(k2_wellord1(X1,X2))) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2463,plain,
    ( r2_hidden(X0,k1_wellord1(k1_wellord2(sK3),X1)) != iProver_top
    | r2_hidden(X0,k3_relat_1(k1_wellord2(sK3))) = iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2358,c_1487])).

cnf(c_2485,plain,
    ( r2_hidden(X0,k1_wellord1(k1_wellord2(sK3),X1)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2463,c_173])).

cnf(c_3402,plain,
    ( r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X0,k1_wellord1(k1_wellord2(sK3),X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2485,c_44])).

cnf(c_3403,plain,
    ( r2_hidden(X0,k1_wellord1(k1_wellord2(sK3),X1)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_3402])).

cnf(c_9481,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_9426,c_3403])).

cnf(c_9652,plain,
    ( r2_hidden(sK3,sK4) != iProver_top
    | r2_hidden(sK3,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_9481])).

cnf(c_9432,plain,
    ( r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK4)) != iProver_top
    | r2_hidden(sK4,sK3) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_9426,c_1592])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X0))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1489,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8791,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | r2_hidden(sK3,sK3) != iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8786,c_1489])).

cnf(c_39,plain,
    ( k1_wellord1(k1_wellord2(X0),X1) = X1
    | r2_hidden(X1,X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_41,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK3) = sK3
    | r2_hidden(sK3,sK3) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_1759,plain,
    ( ~ r2_hidden(X0,k1_wellord1(k1_wellord2(X1),X0))
    | ~ v1_relat_1(k1_wellord2(X1)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1760,plain,
    ( r2_hidden(X0,k1_wellord1(k1_wellord2(X1),X0)) != iProver_top
    | v1_relat_1(k1_wellord2(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1759])).

cnf(c_1762,plain,
    ( r2_hidden(sK3,k1_wellord1(k1_wellord2(sK3),sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1760])).

cnf(c_1026,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3344,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k1_wellord1(k1_wellord2(X3),X2))
    | X2 != X0
    | k1_wellord1(k1_wellord2(X3),X2) != X1 ),
    inference(instantiation,[status(thm)],[c_1026])).

cnf(c_3345,plain,
    ( X0 != X1
    | k1_wellord1(k1_wellord2(X2),X0) != X3
    | r2_hidden(X1,X3) != iProver_top
    | r2_hidden(X0,k1_wellord1(k1_wellord2(X2),X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3344])).

cnf(c_3347,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK3) != sK3
    | sK3 != sK3
    | r2_hidden(sK3,k1_wellord1(k1_wellord2(sK3),sK3)) = iProver_top
    | r2_hidden(sK3,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3345])).

cnf(c_9047,plain,
    ( r2_hidden(sK3,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8791,c_30,c_41,c_44,c_1049,c_1762,c_3347])).

cnf(c_5436,plain,
    ( r2_hidden(X0,sK4)
    | r1_tarski(sK4,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK4) ),
    inference(instantiation,[status(thm)],[c_376])).

cnf(c_5437,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5436])).

cnf(c_5439,plain,
    ( r2_hidden(sK3,sK4) = iProver_top
    | r1_tarski(sK4,sK3) = iProver_top
    | v3_ordinal1(sK4) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5437])).

cnf(c_1032,plain,
    ( ~ r4_wellord1(X0,X1)
    | r4_wellord1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1777,plain,
    ( r4_wellord1(X0,X1)
    | ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4))
    | X1 != k1_wellord2(sK4)
    | X0 != k1_wellord2(sK3) ),
    inference(instantiation,[status(thm)],[c_1032])).

cnf(c_2266,plain,
    ( r4_wellord1(X0,k2_wellord1(k1_wellord2(X1),sK4))
    | ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4))
    | X0 != k1_wellord2(sK3)
    | k2_wellord1(k1_wellord2(X1),sK4) != k1_wellord2(sK4) ),
    inference(instantiation,[status(thm)],[c_1777])).

cnf(c_2757,plain,
    ( r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(X0),sK4))
    | ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4))
    | k2_wellord1(k1_wellord2(X0),sK4) != k1_wellord2(sK4)
    | k1_wellord2(sK3) != k1_wellord2(sK3) ),
    inference(instantiation,[status(thm)],[c_2266])).

cnf(c_2770,plain,
    ( k2_wellord1(k1_wellord2(X0),sK4) != k1_wellord2(sK4)
    | k1_wellord2(sK3) != k1_wellord2(sK3)
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(X0),sK4)) = iProver_top
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2757])).

cnf(c_2772,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK4) != k1_wellord2(sK4)
    | k1_wellord2(sK3) != k1_wellord2(sK3)
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK4)) = iProver_top
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2770])).

cnf(c_2265,plain,
    ( ~ r1_tarski(sK4,X0)
    | k2_wellord1(k1_wellord2(X0),sK4) = k1_wellord2(sK4) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2267,plain,
    ( k2_wellord1(k1_wellord2(X0),sK4) = k1_wellord2(sK4)
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2265])).

cnf(c_2269,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
    | r1_tarski(sK4,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2267])).

cnf(c_1033,plain,
    ( X0 != X1
    | k1_wellord2(X0) = k1_wellord2(X1) ),
    theory(equality)).

cnf(c_1045,plain,
    ( k1_wellord2(sK3) = k1_wellord2(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1033])).

cnf(c_32,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9652,c_9432,c_9047,c_5439,c_2772,c_2269,c_2004,c_1049,c_1045,c_26,c_32,c_31,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:48:52 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 3.70/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/0.99  
% 3.70/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.70/0.99  
% 3.70/0.99  ------  iProver source info
% 3.70/0.99  
% 3.70/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.70/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.70/0.99  git: non_committed_changes: false
% 3.70/0.99  git: last_make_outside_of_git: false
% 3.70/0.99  
% 3.70/0.99  ------ 
% 3.70/0.99  
% 3.70/0.99  ------ Input Options
% 3.70/0.99  
% 3.70/0.99  --out_options                           all
% 3.70/0.99  --tptp_safe_out                         true
% 3.70/0.99  --problem_path                          ""
% 3.70/0.99  --include_path                          ""
% 3.70/0.99  --clausifier                            res/vclausify_rel
% 3.70/0.99  --clausifier_options                    --mode clausify
% 3.70/0.99  --stdin                                 false
% 3.70/0.99  --stats_out                             all
% 3.70/0.99  
% 3.70/0.99  ------ General Options
% 3.70/0.99  
% 3.70/0.99  --fof                                   false
% 3.70/0.99  --time_out_real                         305.
% 3.70/0.99  --time_out_virtual                      -1.
% 3.70/0.99  --symbol_type_check                     false
% 3.70/0.99  --clausify_out                          false
% 3.70/0.99  --sig_cnt_out                           false
% 3.70/0.99  --trig_cnt_out                          false
% 3.70/0.99  --trig_cnt_out_tolerance                1.
% 3.70/0.99  --trig_cnt_out_sk_spl                   false
% 3.70/0.99  --abstr_cl_out                          false
% 3.70/0.99  
% 3.70/0.99  ------ Global Options
% 3.70/0.99  
% 3.70/0.99  --schedule                              default
% 3.70/0.99  --add_important_lit                     false
% 3.70/0.99  --prop_solver_per_cl                    1000
% 3.70/0.99  --min_unsat_core                        false
% 3.70/0.99  --soft_assumptions                      false
% 3.70/0.99  --soft_lemma_size                       3
% 3.70/0.99  --prop_impl_unit_size                   0
% 3.70/0.99  --prop_impl_unit                        []
% 3.70/0.99  --share_sel_clauses                     true
% 3.70/0.99  --reset_solvers                         false
% 3.70/0.99  --bc_imp_inh                            [conj_cone]
% 3.70/0.99  --conj_cone_tolerance                   3.
% 3.70/0.99  --extra_neg_conj                        none
% 3.70/0.99  --large_theory_mode                     true
% 3.70/0.99  --prolific_symb_bound                   200
% 3.70/0.99  --lt_threshold                          2000
% 3.70/0.99  --clause_weak_htbl                      true
% 3.70/0.99  --gc_record_bc_elim                     false
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing Options
% 3.70/0.99  
% 3.70/0.99  --preprocessing_flag                    true
% 3.70/0.99  --time_out_prep_mult                    0.1
% 3.70/0.99  --splitting_mode                        input
% 3.70/0.99  --splitting_grd                         true
% 3.70/0.99  --splitting_cvd                         false
% 3.70/0.99  --splitting_cvd_svl                     false
% 3.70/0.99  --splitting_nvd                         32
% 3.70/0.99  --sub_typing                            true
% 3.70/0.99  --prep_gs_sim                           true
% 3.70/0.99  --prep_unflatten                        true
% 3.70/0.99  --prep_res_sim                          true
% 3.70/0.99  --prep_upred                            true
% 3.70/0.99  --prep_sem_filter                       exhaustive
% 3.70/0.99  --prep_sem_filter_out                   false
% 3.70/0.99  --pred_elim                             true
% 3.70/0.99  --res_sim_input                         true
% 3.70/0.99  --eq_ax_congr_red                       true
% 3.70/0.99  --pure_diseq_elim                       true
% 3.70/0.99  --brand_transform                       false
% 3.70/0.99  --non_eq_to_eq                          false
% 3.70/0.99  --prep_def_merge                        true
% 3.70/0.99  --prep_def_merge_prop_impl              false
% 3.70/0.99  --prep_def_merge_mbd                    true
% 3.70/0.99  --prep_def_merge_tr_red                 false
% 3.70/0.99  --prep_def_merge_tr_cl                  false
% 3.70/0.99  --smt_preprocessing                     true
% 3.70/0.99  --smt_ac_axioms                         fast
% 3.70/0.99  --preprocessed_out                      false
% 3.70/0.99  --preprocessed_stats                    false
% 3.70/0.99  
% 3.70/0.99  ------ Abstraction refinement Options
% 3.70/0.99  
% 3.70/0.99  --abstr_ref                             []
% 3.70/0.99  --abstr_ref_prep                        false
% 3.70/0.99  --abstr_ref_until_sat                   false
% 3.70/0.99  --abstr_ref_sig_restrict                funpre
% 3.70/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.70/0.99  --abstr_ref_under                       []
% 3.70/0.99  
% 3.70/0.99  ------ SAT Options
% 3.70/0.99  
% 3.70/0.99  --sat_mode                              false
% 3.70/0.99  --sat_fm_restart_options                ""
% 3.70/0.99  --sat_gr_def                            false
% 3.70/0.99  --sat_epr_types                         true
% 3.70/0.99  --sat_non_cyclic_types                  false
% 3.70/0.99  --sat_finite_models                     false
% 3.70/0.99  --sat_fm_lemmas                         false
% 3.70/0.99  --sat_fm_prep                           false
% 3.70/0.99  --sat_fm_uc_incr                        true
% 3.70/0.99  --sat_out_model                         small
% 3.70/0.99  --sat_out_clauses                       false
% 3.70/0.99  
% 3.70/0.99  ------ QBF Options
% 3.70/0.99  
% 3.70/0.99  --qbf_mode                              false
% 3.70/0.99  --qbf_elim_univ                         false
% 3.70/0.99  --qbf_dom_inst                          none
% 3.70/0.99  --qbf_dom_pre_inst                      false
% 3.70/0.99  --qbf_sk_in                             false
% 3.70/0.99  --qbf_pred_elim                         true
% 3.70/0.99  --qbf_split                             512
% 3.70/0.99  
% 3.70/0.99  ------ BMC1 Options
% 3.70/0.99  
% 3.70/0.99  --bmc1_incremental                      false
% 3.70/0.99  --bmc1_axioms                           reachable_all
% 3.70/0.99  --bmc1_min_bound                        0
% 3.70/0.99  --bmc1_max_bound                        -1
% 3.70/0.99  --bmc1_max_bound_default                -1
% 3.70/0.99  --bmc1_symbol_reachability              true
% 3.70/0.99  --bmc1_property_lemmas                  false
% 3.70/0.99  --bmc1_k_induction                      false
% 3.70/0.99  --bmc1_non_equiv_states                 false
% 3.70/0.99  --bmc1_deadlock                         false
% 3.70/0.99  --bmc1_ucm                              false
% 3.70/0.99  --bmc1_add_unsat_core                   none
% 3.70/0.99  --bmc1_unsat_core_children              false
% 3.70/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.70/0.99  --bmc1_out_stat                         full
% 3.70/0.99  --bmc1_ground_init                      false
% 3.70/0.99  --bmc1_pre_inst_next_state              false
% 3.70/0.99  --bmc1_pre_inst_state                   false
% 3.70/0.99  --bmc1_pre_inst_reach_state             false
% 3.70/0.99  --bmc1_out_unsat_core                   false
% 3.70/0.99  --bmc1_aig_witness_out                  false
% 3.70/0.99  --bmc1_verbose                          false
% 3.70/0.99  --bmc1_dump_clauses_tptp                false
% 3.70/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.70/0.99  --bmc1_dump_file                        -
% 3.70/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.70/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.70/0.99  --bmc1_ucm_extend_mode                  1
% 3.70/0.99  --bmc1_ucm_init_mode                    2
% 3.70/0.99  --bmc1_ucm_cone_mode                    none
% 3.70/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.70/0.99  --bmc1_ucm_relax_model                  4
% 3.70/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.70/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.70/0.99  --bmc1_ucm_layered_model                none
% 3.70/0.99  --bmc1_ucm_max_lemma_size               10
% 3.70/0.99  
% 3.70/0.99  ------ AIG Options
% 3.70/0.99  
% 3.70/0.99  --aig_mode                              false
% 3.70/0.99  
% 3.70/0.99  ------ Instantiation Options
% 3.70/0.99  
% 3.70/0.99  --instantiation_flag                    true
% 3.70/0.99  --inst_sos_flag                         false
% 3.70/0.99  --inst_sos_phase                        true
% 3.70/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.70/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.70/0.99  --inst_lit_sel_side                     num_symb
% 3.70/0.99  --inst_solver_per_active                1400
% 3.70/0.99  --inst_solver_calls_frac                1.
% 3.70/0.99  --inst_passive_queue_type               priority_queues
% 3.70/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.70/0.99  --inst_passive_queues_freq              [25;2]
% 3.70/0.99  --inst_dismatching                      true
% 3.70/0.99  --inst_eager_unprocessed_to_passive     true
% 3.70/0.99  --inst_prop_sim_given                   true
% 3.70/0.99  --inst_prop_sim_new                     false
% 3.70/0.99  --inst_subs_new                         false
% 3.70/0.99  --inst_eq_res_simp                      false
% 3.70/0.99  --inst_subs_given                       false
% 3.70/0.99  --inst_orphan_elimination               true
% 3.70/0.99  --inst_learning_loop_flag               true
% 3.70/0.99  --inst_learning_start                   3000
% 3.70/0.99  --inst_learning_factor                  2
% 3.70/0.99  --inst_start_prop_sim_after_learn       3
% 3.70/0.99  --inst_sel_renew                        solver
% 3.70/0.99  --inst_lit_activity_flag                true
% 3.70/0.99  --inst_restr_to_given                   false
% 3.70/0.99  --inst_activity_threshold               500
% 3.70/0.99  --inst_out_proof                        true
% 3.70/0.99  
% 3.70/0.99  ------ Resolution Options
% 3.70/0.99  
% 3.70/0.99  --resolution_flag                       true
% 3.70/0.99  --res_lit_sel                           adaptive
% 3.70/0.99  --res_lit_sel_side                      none
% 3.70/0.99  --res_ordering                          kbo
% 3.70/0.99  --res_to_prop_solver                    active
% 3.70/0.99  --res_prop_simpl_new                    false
% 3.70/0.99  --res_prop_simpl_given                  true
% 3.70/0.99  --res_passive_queue_type                priority_queues
% 3.70/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.70/0.99  --res_passive_queues_freq               [15;5]
% 3.70/0.99  --res_forward_subs                      full
% 3.70/0.99  --res_backward_subs                     full
% 3.70/0.99  --res_forward_subs_resolution           true
% 3.70/0.99  --res_backward_subs_resolution          true
% 3.70/0.99  --res_orphan_elimination                true
% 3.70/0.99  --res_time_limit                        2.
% 3.70/0.99  --res_out_proof                         true
% 3.70/0.99  
% 3.70/0.99  ------ Superposition Options
% 3.70/0.99  
% 3.70/0.99  --superposition_flag                    true
% 3.70/0.99  --sup_passive_queue_type                priority_queues
% 3.70/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.70/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.70/0.99  --demod_completeness_check              fast
% 3.70/0.99  --demod_use_ground                      true
% 3.70/0.99  --sup_to_prop_solver                    passive
% 3.70/0.99  --sup_prop_simpl_new                    true
% 3.70/0.99  --sup_prop_simpl_given                  true
% 3.70/0.99  --sup_fun_splitting                     false
% 3.70/0.99  --sup_smt_interval                      50000
% 3.70/0.99  
% 3.70/0.99  ------ Superposition Simplification Setup
% 3.70/0.99  
% 3.70/0.99  --sup_indices_passive                   []
% 3.70/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.70/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/0.99  --sup_full_bw                           [BwDemod]
% 3.70/0.99  --sup_immed_triv                        [TrivRules]
% 3.70/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/0.99  --sup_immed_bw_main                     []
% 3.70/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.70/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.70/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.70/0.99  
% 3.70/0.99  ------ Combination Options
% 3.70/0.99  
% 3.70/0.99  --comb_res_mult                         3
% 3.70/0.99  --comb_sup_mult                         2
% 3.70/0.99  --comb_inst_mult                        10
% 3.70/0.99  
% 3.70/0.99  ------ Debug Options
% 3.70/0.99  
% 3.70/0.99  --dbg_backtrace                         false
% 3.70/0.99  --dbg_dump_prop_clauses                 false
% 3.70/0.99  --dbg_dump_prop_clauses_file            -
% 3.70/0.99  --dbg_out_stat                          false
% 3.70/0.99  ------ Parsing...
% 3.70/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.99  ------ Proving...
% 3.70/0.99  ------ Problem Properties 
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  clauses                                 27
% 3.70/0.99  conjectures                             4
% 3.70/0.99  EPR                                     6
% 3.70/0.99  Horn                                    18
% 3.70/0.99  unary                                   6
% 3.70/0.99  binary                                  3
% 3.70/0.99  lits                                    82
% 3.70/0.99  lits eq                                 16
% 3.70/0.99  fd_pure                                 0
% 3.70/0.99  fd_pseudo                               0
% 3.70/0.99  fd_cond                                 0
% 3.70/0.99  fd_pseudo_cond                          4
% 3.70/0.99  AC symbols                              0
% 3.70/0.99  
% 3.70/0.99  ------ Schedule dynamic 5 is on 
% 3.70/0.99  
% 3.70/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  ------ 
% 3.70/0.99  Current options:
% 3.70/0.99  ------ 
% 3.70/0.99  
% 3.70/0.99  ------ Input Options
% 3.70/0.99  
% 3.70/0.99  --out_options                           all
% 3.70/0.99  --tptp_safe_out                         true
% 3.70/0.99  --problem_path                          ""
% 3.70/0.99  --include_path                          ""
% 3.70/0.99  --clausifier                            res/vclausify_rel
% 3.70/0.99  --clausifier_options                    --mode clausify
% 3.70/0.99  --stdin                                 false
% 3.70/0.99  --stats_out                             all
% 3.70/0.99  
% 3.70/0.99  ------ General Options
% 3.70/0.99  
% 3.70/0.99  --fof                                   false
% 3.70/0.99  --time_out_real                         305.
% 3.70/0.99  --time_out_virtual                      -1.
% 3.70/0.99  --symbol_type_check                     false
% 3.70/0.99  --clausify_out                          false
% 3.70/0.99  --sig_cnt_out                           false
% 3.70/0.99  --trig_cnt_out                          false
% 3.70/0.99  --trig_cnt_out_tolerance                1.
% 3.70/0.99  --trig_cnt_out_sk_spl                   false
% 3.70/0.99  --abstr_cl_out                          false
% 3.70/0.99  
% 3.70/0.99  ------ Global Options
% 3.70/0.99  
% 3.70/0.99  --schedule                              default
% 3.70/0.99  --add_important_lit                     false
% 3.70/0.99  --prop_solver_per_cl                    1000
% 3.70/0.99  --min_unsat_core                        false
% 3.70/0.99  --soft_assumptions                      false
% 3.70/0.99  --soft_lemma_size                       3
% 3.70/0.99  --prop_impl_unit_size                   0
% 3.70/0.99  --prop_impl_unit                        []
% 3.70/0.99  --share_sel_clauses                     true
% 3.70/0.99  --reset_solvers                         false
% 3.70/0.99  --bc_imp_inh                            [conj_cone]
% 3.70/0.99  --conj_cone_tolerance                   3.
% 3.70/0.99  --extra_neg_conj                        none
% 3.70/0.99  --large_theory_mode                     true
% 3.70/0.99  --prolific_symb_bound                   200
% 3.70/0.99  --lt_threshold                          2000
% 3.70/0.99  --clause_weak_htbl                      true
% 3.70/0.99  --gc_record_bc_elim                     false
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing Options
% 3.70/0.99  
% 3.70/0.99  --preprocessing_flag                    true
% 3.70/0.99  --time_out_prep_mult                    0.1
% 3.70/0.99  --splitting_mode                        input
% 3.70/0.99  --splitting_grd                         true
% 3.70/0.99  --splitting_cvd                         false
% 3.70/0.99  --splitting_cvd_svl                     false
% 3.70/0.99  --splitting_nvd                         32
% 3.70/0.99  --sub_typing                            true
% 3.70/0.99  --prep_gs_sim                           true
% 3.70/0.99  --prep_unflatten                        true
% 3.70/0.99  --prep_res_sim                          true
% 3.70/0.99  --prep_upred                            true
% 3.70/0.99  --prep_sem_filter                       exhaustive
% 3.70/0.99  --prep_sem_filter_out                   false
% 3.70/0.99  --pred_elim                             true
% 3.70/0.99  --res_sim_input                         true
% 3.70/0.99  --eq_ax_congr_red                       true
% 3.70/0.99  --pure_diseq_elim                       true
% 3.70/0.99  --brand_transform                       false
% 3.70/0.99  --non_eq_to_eq                          false
% 3.70/0.99  --prep_def_merge                        true
% 3.70/0.99  --prep_def_merge_prop_impl              false
% 3.70/0.99  --prep_def_merge_mbd                    true
% 3.70/0.99  --prep_def_merge_tr_red                 false
% 3.70/0.99  --prep_def_merge_tr_cl                  false
% 3.70/0.99  --smt_preprocessing                     true
% 3.70/0.99  --smt_ac_axioms                         fast
% 3.70/0.99  --preprocessed_out                      false
% 3.70/0.99  --preprocessed_stats                    false
% 3.70/0.99  
% 3.70/0.99  ------ Abstraction refinement Options
% 3.70/0.99  
% 3.70/0.99  --abstr_ref                             []
% 3.70/0.99  --abstr_ref_prep                        false
% 3.70/0.99  --abstr_ref_until_sat                   false
% 3.70/0.99  --abstr_ref_sig_restrict                funpre
% 3.70/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.70/0.99  --abstr_ref_under                       []
% 3.70/0.99  
% 3.70/0.99  ------ SAT Options
% 3.70/0.99  
% 3.70/0.99  --sat_mode                              false
% 3.70/0.99  --sat_fm_restart_options                ""
% 3.70/0.99  --sat_gr_def                            false
% 3.70/0.99  --sat_epr_types                         true
% 3.70/0.99  --sat_non_cyclic_types                  false
% 3.70/0.99  --sat_finite_models                     false
% 3.70/0.99  --sat_fm_lemmas                         false
% 3.70/0.99  --sat_fm_prep                           false
% 3.70/0.99  --sat_fm_uc_incr                        true
% 3.70/0.99  --sat_out_model                         small
% 3.70/0.99  --sat_out_clauses                       false
% 3.70/0.99  
% 3.70/0.99  ------ QBF Options
% 3.70/0.99  
% 3.70/0.99  --qbf_mode                              false
% 3.70/0.99  --qbf_elim_univ                         false
% 3.70/0.99  --qbf_dom_inst                          none
% 3.70/0.99  --qbf_dom_pre_inst                      false
% 3.70/0.99  --qbf_sk_in                             false
% 3.70/0.99  --qbf_pred_elim                         true
% 3.70/0.99  --qbf_split                             512
% 3.70/0.99  
% 3.70/0.99  ------ BMC1 Options
% 3.70/0.99  
% 3.70/0.99  --bmc1_incremental                      false
% 3.70/0.99  --bmc1_axioms                           reachable_all
% 3.70/0.99  --bmc1_min_bound                        0
% 3.70/0.99  --bmc1_max_bound                        -1
% 3.70/0.99  --bmc1_max_bound_default                -1
% 3.70/0.99  --bmc1_symbol_reachability              true
% 3.70/0.99  --bmc1_property_lemmas                  false
% 3.70/0.99  --bmc1_k_induction                      false
% 3.70/0.99  --bmc1_non_equiv_states                 false
% 3.70/0.99  --bmc1_deadlock                         false
% 3.70/0.99  --bmc1_ucm                              false
% 3.70/0.99  --bmc1_add_unsat_core                   none
% 3.70/0.99  --bmc1_unsat_core_children              false
% 3.70/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.70/0.99  --bmc1_out_stat                         full
% 3.70/0.99  --bmc1_ground_init                      false
% 3.70/0.99  --bmc1_pre_inst_next_state              false
% 3.70/0.99  --bmc1_pre_inst_state                   false
% 3.70/0.99  --bmc1_pre_inst_reach_state             false
% 3.70/0.99  --bmc1_out_unsat_core                   false
% 3.70/0.99  --bmc1_aig_witness_out                  false
% 3.70/0.99  --bmc1_verbose                          false
% 3.70/0.99  --bmc1_dump_clauses_tptp                false
% 3.70/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.70/0.99  --bmc1_dump_file                        -
% 3.70/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.70/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.70/0.99  --bmc1_ucm_extend_mode                  1
% 3.70/0.99  --bmc1_ucm_init_mode                    2
% 3.70/0.99  --bmc1_ucm_cone_mode                    none
% 3.70/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.70/0.99  --bmc1_ucm_relax_model                  4
% 3.70/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.70/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.70/0.99  --bmc1_ucm_layered_model                none
% 3.70/0.99  --bmc1_ucm_max_lemma_size               10
% 3.70/0.99  
% 3.70/0.99  ------ AIG Options
% 3.70/0.99  
% 3.70/0.99  --aig_mode                              false
% 3.70/0.99  
% 3.70/0.99  ------ Instantiation Options
% 3.70/0.99  
% 3.70/0.99  --instantiation_flag                    true
% 3.70/0.99  --inst_sos_flag                         false
% 3.70/0.99  --inst_sos_phase                        true
% 3.70/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.70/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.70/0.99  --inst_lit_sel_side                     none
% 3.70/0.99  --inst_solver_per_active                1400
% 3.70/0.99  --inst_solver_calls_frac                1.
% 3.70/0.99  --inst_passive_queue_type               priority_queues
% 3.70/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.70/0.99  --inst_passive_queues_freq              [25;2]
% 3.70/0.99  --inst_dismatching                      true
% 3.70/0.99  --inst_eager_unprocessed_to_passive     true
% 3.70/0.99  --inst_prop_sim_given                   true
% 3.70/0.99  --inst_prop_sim_new                     false
% 3.70/0.99  --inst_subs_new                         false
% 3.70/0.99  --inst_eq_res_simp                      false
% 3.70/0.99  --inst_subs_given                       false
% 3.70/0.99  --inst_orphan_elimination               true
% 3.70/0.99  --inst_learning_loop_flag               true
% 3.70/0.99  --inst_learning_start                   3000
% 3.70/0.99  --inst_learning_factor                  2
% 3.70/0.99  --inst_start_prop_sim_after_learn       3
% 3.70/0.99  --inst_sel_renew                        solver
% 3.70/0.99  --inst_lit_activity_flag                true
% 3.70/0.99  --inst_restr_to_given                   false
% 3.70/0.99  --inst_activity_threshold               500
% 3.70/0.99  --inst_out_proof                        true
% 3.70/0.99  
% 3.70/0.99  ------ Resolution Options
% 3.70/0.99  
% 3.70/0.99  --resolution_flag                       false
% 3.70/0.99  --res_lit_sel                           adaptive
% 3.70/0.99  --res_lit_sel_side                      none
% 3.70/0.99  --res_ordering                          kbo
% 3.70/0.99  --res_to_prop_solver                    active
% 3.70/0.99  --res_prop_simpl_new                    false
% 3.70/0.99  --res_prop_simpl_given                  true
% 3.70/0.99  --res_passive_queue_type                priority_queues
% 3.70/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.70/0.99  --res_passive_queues_freq               [15;5]
% 3.70/0.99  --res_forward_subs                      full
% 3.70/0.99  --res_backward_subs                     full
% 3.70/0.99  --res_forward_subs_resolution           true
% 3.70/0.99  --res_backward_subs_resolution          true
% 3.70/0.99  --res_orphan_elimination                true
% 3.70/0.99  --res_time_limit                        2.
% 3.70/0.99  --res_out_proof                         true
% 3.70/0.99  
% 3.70/0.99  ------ Superposition Options
% 3.70/0.99  
% 3.70/0.99  --superposition_flag                    true
% 3.70/0.99  --sup_passive_queue_type                priority_queues
% 3.70/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.70/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.70/0.99  --demod_completeness_check              fast
% 3.70/0.99  --demod_use_ground                      true
% 3.70/0.99  --sup_to_prop_solver                    passive
% 3.70/0.99  --sup_prop_simpl_new                    true
% 3.70/0.99  --sup_prop_simpl_given                  true
% 3.70/0.99  --sup_fun_splitting                     false
% 3.70/0.99  --sup_smt_interval                      50000
% 3.70/0.99  
% 3.70/0.99  ------ Superposition Simplification Setup
% 3.70/0.99  
% 3.70/0.99  --sup_indices_passive                   []
% 3.70/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.70/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/0.99  --sup_full_bw                           [BwDemod]
% 3.70/0.99  --sup_immed_triv                        [TrivRules]
% 3.70/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/0.99  --sup_immed_bw_main                     []
% 3.70/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.70/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.70/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.70/0.99  
% 3.70/0.99  ------ Combination Options
% 3.70/0.99  
% 3.70/0.99  --comb_res_mult                         3
% 3.70/0.99  --comb_sup_mult                         2
% 3.70/0.99  --comb_inst_mult                        10
% 3.70/0.99  
% 3.70/0.99  ------ Debug Options
% 3.70/0.99  
% 3.70/0.99  --dbg_backtrace                         false
% 3.70/0.99  --dbg_dump_prop_clauses                 false
% 3.70/0.99  --dbg_dump_prop_clauses_file            -
% 3.70/0.99  --dbg_out_stat                          false
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  ------ Proving...
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  % SZS status Theorem for theBenchmark.p
% 3.70/0.99  
% 3.70/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.70/0.99  
% 3.70/0.99  fof(f14,conjecture,(
% 3.70/0.99    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 3.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f15,negated_conjecture,(
% 3.70/0.99    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 3.70/0.99    inference(negated_conjecture,[],[f14])).
% 3.70/0.99  
% 3.70/0.99  fof(f37,plain,(
% 3.70/0.99    ? [X0] : (? [X1] : ((X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.70/0.99    inference(ennf_transformation,[],[f15])).
% 3.70/0.99  
% 3.70/0.99  fof(f38,plain,(
% 3.70/0.99    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.70/0.99    inference(flattening,[],[f37])).
% 3.70/0.99  
% 3.70/0.99  fof(f51,plain,(
% 3.70/0.99    ( ! [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) => (sK4 != X0 & r4_wellord1(k1_wellord2(X0),k1_wellord2(sK4)) & v3_ordinal1(sK4))) )),
% 3.70/0.99    introduced(choice_axiom,[])).
% 3.70/0.99  
% 3.70/0.99  fof(f50,plain,(
% 3.70/0.99    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : (sK3 != X1 & r4_wellord1(k1_wellord2(sK3),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK3))),
% 3.70/0.99    introduced(choice_axiom,[])).
% 3.70/0.99  
% 3.70/0.99  fof(f52,plain,(
% 3.70/0.99    (sK3 != sK4 & r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) & v3_ordinal1(sK4)) & v3_ordinal1(sK3)),
% 3.70/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f38,f51,f50])).
% 3.70/0.99  
% 3.70/0.99  fof(f79,plain,(
% 3.70/0.99    v3_ordinal1(sK3)),
% 3.70/0.99    inference(cnf_transformation,[],[f52])).
% 3.70/0.99  
% 3.70/0.99  fof(f80,plain,(
% 3.70/0.99    v3_ordinal1(sK4)),
% 3.70/0.99    inference(cnf_transformation,[],[f52])).
% 3.70/0.99  
% 3.70/0.99  fof(f1,axiom,(
% 3.70/0.99    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 3.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f16,plain,(
% 3.70/0.99    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 3.70/0.99    inference(ennf_transformation,[],[f1])).
% 3.70/0.99  
% 3.70/0.99  fof(f17,plain,(
% 3.70/0.99    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.70/0.99    inference(flattening,[],[f16])).
% 3.70/0.99  
% 3.70/0.99  fof(f39,plain,(
% 3.70/0.99    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.70/0.99    inference(nnf_transformation,[],[f17])).
% 3.70/0.99  
% 3.70/0.99  fof(f53,plain,(
% 3.70/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f39])).
% 3.70/0.99  
% 3.70/0.99  fof(f3,axiom,(
% 3.70/0.99    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 3.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f20,plain,(
% 3.70/0.99    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.70/0.99    inference(ennf_transformation,[],[f3])).
% 3.70/0.99  
% 3.70/0.99  fof(f21,plain,(
% 3.70/0.99    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.70/0.99    inference(flattening,[],[f20])).
% 3.70/0.99  
% 3.70/0.99  fof(f56,plain,(
% 3.70/0.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f21])).
% 3.70/0.99  
% 3.70/0.99  fof(f11,axiom,(
% 3.70/0.99    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => k1_wellord1(k1_wellord2(X1),X0) = X0)))),
% 3.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f33,plain,(
% 3.70/0.99    ! [X0] : (! [X1] : ((k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.70/0.99    inference(ennf_transformation,[],[f11])).
% 3.70/0.99  
% 3.70/0.99  fof(f34,plain,(
% 3.70/0.99    ! [X0] : (! [X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.70/0.99    inference(flattening,[],[f33])).
% 3.70/0.99  
% 3.70/0.99  fof(f76,plain,(
% 3.70/0.99    ( ! [X0,X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f34])).
% 3.70/0.99  
% 3.70/0.99  fof(f13,axiom,(
% 3.70/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0))),
% 3.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f36,plain,(
% 3.70/0.99    ! [X0,X1] : (k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) | ~r1_tarski(X0,X1))),
% 3.70/0.99    inference(ennf_transformation,[],[f13])).
% 3.70/0.99  
% 3.70/0.99  fof(f78,plain,(
% 3.70/0.99    ( ! [X0,X1] : (k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) | ~r1_tarski(X0,X1)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f36])).
% 3.70/0.99  
% 3.70/0.99  fof(f2,axiom,(
% 3.70/0.99    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 3.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f18,plain,(
% 3.70/0.99    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.70/0.99    inference(ennf_transformation,[],[f2])).
% 3.70/0.99  
% 3.70/0.99  fof(f19,plain,(
% 3.70/0.99    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.70/0.99    inference(flattening,[],[f18])).
% 3.70/0.99  
% 3.70/0.99  fof(f55,plain,(
% 3.70/0.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f19])).
% 3.70/0.99  
% 3.70/0.99  fof(f82,plain,(
% 3.70/0.99    sK3 != sK4),
% 3.70/0.99    inference(cnf_transformation,[],[f52])).
% 3.70/0.99  
% 3.70/0.99  fof(f8,axiom,(
% 3.70/0.99    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 3.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f29,plain,(
% 3.70/0.99    ! [X0] : ((! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 3.70/0.99    inference(ennf_transformation,[],[f8])).
% 3.70/0.99  
% 3.70/0.99  fof(f30,plain,(
% 3.70/0.99    ! [X0] : (! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 3.70/0.99    inference(flattening,[],[f29])).
% 3.70/0.99  
% 3.70/0.99  fof(f67,plain,(
% 3.70/0.99    ( ! [X0,X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0)) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f30])).
% 3.70/0.99  
% 3.70/0.99  fof(f12,axiom,(
% 3.70/0.99    ! [X0] : (v3_ordinal1(X0) => v2_wellord1(k1_wellord2(X0)))),
% 3.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f35,plain,(
% 3.70/0.99    ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0))),
% 3.70/0.99    inference(ennf_transformation,[],[f12])).
% 3.70/0.99  
% 3.70/0.99  fof(f77,plain,(
% 3.70/0.99    ( ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f35])).
% 3.70/0.99  
% 3.70/0.99  fof(f10,axiom,(
% 3.70/0.99    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 3.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f75,plain,(
% 3.70/0.99    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 3.70/0.99    inference(cnf_transformation,[],[f10])).
% 3.70/0.99  
% 3.70/0.99  fof(f9,axiom,(
% 3.70/0.99    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 3.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f31,plain,(
% 3.70/0.99    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 3.70/0.99    inference(ennf_transformation,[],[f9])).
% 3.70/0.99  
% 3.70/0.99  fof(f32,plain,(
% 3.70/0.99    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 3.70/0.99    inference(flattening,[],[f31])).
% 3.70/0.99  
% 3.70/0.99  fof(f45,plain,(
% 3.70/0.99    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 3.70/0.99    inference(nnf_transformation,[],[f32])).
% 3.70/0.99  
% 3.70/0.99  fof(f46,plain,(
% 3.70/0.99    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 3.70/0.99    inference(flattening,[],[f45])).
% 3.70/0.99  
% 3.70/0.99  fof(f47,plain,(
% 3.70/0.99    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 3.70/0.99    inference(rectify,[],[f46])).
% 3.70/0.99  
% 3.70/0.99  fof(f48,plain,(
% 3.70/0.99    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK1(X0,X1),sK2(X0,X1)) | ~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)) & (r1_tarski(sK1(X0,X1),sK2(X0,X1)) | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)) & r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),X0)))),
% 3.70/0.99    introduced(choice_axiom,[])).
% 3.70/0.99  
% 3.70/0.99  fof(f49,plain,(
% 3.70/0.99    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK1(X0,X1),sK2(X0,X1)) | ~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)) & (r1_tarski(sK1(X0,X1),sK2(X0,X1)) | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)) & r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 3.70/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f47,f48])).
% 3.70/0.99  
% 3.70/0.99  fof(f68,plain,(
% 3.70/0.99    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f49])).
% 3.70/0.99  
% 3.70/0.99  fof(f93,plain,(
% 3.70/0.99    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 3.70/0.99    inference(equality_resolution,[],[f68])).
% 3.70/0.99  
% 3.70/0.99  fof(f81,plain,(
% 3.70/0.99    r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4))),
% 3.70/0.99    inference(cnf_transformation,[],[f52])).
% 3.70/0.99  
% 3.70/0.99  fof(f7,axiom,(
% 3.70/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 3.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f27,plain,(
% 3.70/0.99    ! [X0] : (! [X1] : ((r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.70/0.99    inference(ennf_transformation,[],[f7])).
% 3.70/0.99  
% 3.70/0.99  fof(f28,plain,(
% 3.70/0.99    ! [X0] : (! [X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.70/0.99    inference(flattening,[],[f27])).
% 3.70/0.99  
% 3.70/0.99  fof(f66,plain,(
% 3.70/0.99    ( ! [X0,X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f28])).
% 3.70/0.99  
% 3.70/0.99  fof(f6,axiom,(
% 3.70/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v2_wellord1(X1) => k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))))),
% 3.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f25,plain,(
% 3.70/0.99    ! [X0,X1] : ((k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) | ~v2_wellord1(X1)) | ~v1_relat_1(X1))),
% 3.70/0.99    inference(ennf_transformation,[],[f6])).
% 3.70/0.99  
% 3.70/0.99  fof(f26,plain,(
% 3.70/0.99    ! [X0,X1] : (k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 3.70/0.99    inference(flattening,[],[f25])).
% 3.70/0.99  
% 3.70/0.99  fof(f65,plain,(
% 3.70/0.99    ( ! [X0,X1] : (k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) | ~v2_wellord1(X1) | ~v1_relat_1(X1)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f26])).
% 3.70/0.99  
% 3.70/0.99  fof(f5,axiom,(
% 3.70/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) => (r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2)))))),
% 3.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f23,plain,(
% 3.70/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.70/0.99    inference(ennf_transformation,[],[f5])).
% 3.70/0.99  
% 3.70/0.99  fof(f24,plain,(
% 3.70/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | ~v1_relat_1(X2))),
% 3.70/0.99    inference(flattening,[],[f23])).
% 3.70/0.99  
% 3.70/0.99  fof(f63,plain,(
% 3.70/0.99    ( ! [X2,X0,X1] : (r2_hidden(X0,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | ~v1_relat_1(X2)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f24])).
% 3.70/0.99  
% 3.70/0.99  fof(f4,axiom,(
% 3.70/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 3.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f22,plain,(
% 3.70/0.99    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 3.70/0.99    inference(ennf_transformation,[],[f4])).
% 3.70/0.99  
% 3.70/0.99  fof(f40,plain,(
% 3.70/0.99    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.70/0.99    inference(nnf_transformation,[],[f22])).
% 3.70/0.99  
% 3.70/0.99  fof(f41,plain,(
% 3.70/0.99    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.70/0.99    inference(flattening,[],[f40])).
% 3.70/0.99  
% 3.70/0.99  fof(f42,plain,(
% 3.70/0.99    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.70/0.99    inference(rectify,[],[f41])).
% 3.70/0.99  
% 3.70/0.99  fof(f43,plain,(
% 3.70/0.99    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2))) => ((~r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0) | sK0(X0,X1,X2) = X1 | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0) & sK0(X0,X1,X2) != X1) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.70/0.99    introduced(choice_axiom,[])).
% 3.70/0.99  
% 3.70/0.99  fof(f44,plain,(
% 3.70/0.99    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0) | sK0(X0,X1,X2) = X1 | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0) & sK0(X0,X1,X2) != X1) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.70/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).
% 3.70/0.99  
% 3.70/0.99  fof(f57,plain,(
% 3.70/0.99    ( ! [X4,X2,X0,X1] : (X1 != X4 | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f44])).
% 3.70/0.99  
% 3.70/0.99  fof(f85,plain,(
% 3.70/0.99    ( ! [X4,X2,X0] : (~r2_hidden(X4,X2) | k1_wellord1(X0,X4) != X2 | ~v1_relat_1(X0)) )),
% 3.70/0.99    inference(equality_resolution,[],[f57])).
% 3.70/0.99  
% 3.70/0.99  fof(f86,plain,(
% 3.70/0.99    ( ! [X4,X0] : (~r2_hidden(X4,k1_wellord1(X0,X4)) | ~v1_relat_1(X0)) )),
% 3.70/0.99    inference(equality_resolution,[],[f85])).
% 3.70/0.99  
% 3.70/0.99  cnf(c_29,negated_conjecture,
% 3.70/0.99      ( v3_ordinal1(sK3) ),
% 3.70/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1474,plain,
% 3.70/0.99      ( v3_ordinal1(sK3) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_28,negated_conjecture,
% 3.70/0.99      ( v3_ordinal1(sK4) ),
% 3.70/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1475,plain,
% 3.70/0.99      ( v3_ordinal1(sK4) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1,plain,
% 3.70/0.99      ( r1_tarski(X0,X1)
% 3.70/0.99      | ~ r1_ordinal1(X0,X1)
% 3.70/0.99      | ~ v3_ordinal1(X1)
% 3.70/0.99      | ~ v3_ordinal1(X0) ),
% 3.70/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3,plain,
% 3.70/0.99      ( r2_hidden(X0,X1)
% 3.70/0.99      | r1_ordinal1(X1,X0)
% 3.70/0.99      | ~ v3_ordinal1(X0)
% 3.70/0.99      | ~ v3_ordinal1(X1) ),
% 3.70/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_375,plain,
% 3.70/0.99      ( r2_hidden(X0,X1)
% 3.70/0.99      | r1_tarski(X2,X3)
% 3.70/0.99      | ~ v3_ordinal1(X3)
% 3.70/0.99      | ~ v3_ordinal1(X2)
% 3.70/0.99      | ~ v3_ordinal1(X1)
% 3.70/0.99      | ~ v3_ordinal1(X0)
% 3.70/0.99      | X1 != X2
% 3.70/0.99      | X0 != X3 ),
% 3.70/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_3]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_376,plain,
% 3.70/0.99      ( r2_hidden(X0,X1)
% 3.70/0.99      | r1_tarski(X1,X0)
% 3.70/0.99      | ~ v3_ordinal1(X1)
% 3.70/0.99      | ~ v3_ordinal1(X0) ),
% 3.70/0.99      inference(unflattening,[status(thm)],[c_375]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1471,plain,
% 3.70/0.99      ( r2_hidden(X0,X1) = iProver_top
% 3.70/0.99      | r1_tarski(X1,X0) = iProver_top
% 3.70/0.99      | v3_ordinal1(X0) != iProver_top
% 3.70/0.99      | v3_ordinal1(X1) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_376]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_23,plain,
% 3.70/0.99      ( ~ r2_hidden(X0,X1)
% 3.70/0.99      | ~ v3_ordinal1(X1)
% 3.70/0.99      | ~ v3_ordinal1(X0)
% 3.70/0.99      | k1_wellord1(k1_wellord2(X1),X0) = X0 ),
% 3.70/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1478,plain,
% 3.70/0.99      ( k1_wellord1(k1_wellord2(X0),X1) = X1
% 3.70/0.99      | r2_hidden(X1,X0) != iProver_top
% 3.70/0.99      | v3_ordinal1(X1) != iProver_top
% 3.70/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_2868,plain,
% 3.70/0.99      ( k1_wellord1(k1_wellord2(X0),X1) = X1
% 3.70/0.99      | r1_tarski(X0,X1) = iProver_top
% 3.70/0.99      | v3_ordinal1(X0) != iProver_top
% 3.70/0.99      | v3_ordinal1(X1) != iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_1471,c_1478]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_25,plain,
% 3.70/0.99      ( ~ r1_tarski(X0,X1)
% 3.70/0.99      | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ),
% 3.70/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1477,plain,
% 3.70/0.99      ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 3.70/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_5490,plain,
% 3.70/0.99      ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 3.70/0.99      | k1_wellord1(k1_wellord2(X1),X0) = X0
% 3.70/0.99      | v3_ordinal1(X1) != iProver_top
% 3.70/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_2868,c_1477]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_5499,plain,
% 3.70/0.99      ( k2_wellord1(k1_wellord2(sK4),X0) = k1_wellord2(X0)
% 3.70/0.99      | k1_wellord1(k1_wellord2(X0),sK4) = sK4
% 3.70/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_1475,c_5490]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_5569,plain,
% 3.70/0.99      ( k2_wellord1(k1_wellord2(sK4),sK3) = k1_wellord2(sK3)
% 3.70/0.99      | k1_wellord1(k1_wellord2(sK3),sK4) = sK4 ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_1474,c_5499]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_2,plain,
% 3.70/0.99      ( r2_hidden(X0,X1)
% 3.70/0.99      | r2_hidden(X1,X0)
% 3.70/0.99      | ~ v3_ordinal1(X1)
% 3.70/0.99      | ~ v3_ordinal1(X0)
% 3.70/0.99      | X1 = X0 ),
% 3.70/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1495,plain,
% 3.70/0.99      ( X0 = X1
% 3.70/0.99      | r2_hidden(X1,X0) = iProver_top
% 3.70/0.99      | r2_hidden(X0,X1) = iProver_top
% 3.70/0.99      | v3_ordinal1(X1) != iProver_top
% 3.70/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3193,plain,
% 3.70/0.99      ( X0 = X1
% 3.70/0.99      | k1_wellord1(k1_wellord2(X0),X1) = X1
% 3.70/0.99      | r2_hidden(X0,X1) = iProver_top
% 3.70/0.99      | v3_ordinal1(X1) != iProver_top
% 3.70/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_1495,c_1478]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_6889,plain,
% 3.70/0.99      ( X0 = X1
% 3.70/0.99      | k1_wellord1(k1_wellord2(X0),X1) = X1
% 3.70/0.99      | k1_wellord1(k1_wellord2(X1),X0) = X0
% 3.70/0.99      | v3_ordinal1(X1) != iProver_top
% 3.70/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_3193,c_1478]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_8536,plain,
% 3.70/0.99      ( k1_wellord1(k1_wellord2(X0),sK4) = sK4
% 3.70/0.99      | k1_wellord1(k1_wellord2(sK4),X0) = X0
% 3.70/0.99      | sK4 = X0
% 3.70/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_1475,c_6889]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_8564,plain,
% 3.70/0.99      ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3
% 3.70/0.99      | k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 3.70/0.99      | sK4 = sK3 ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_1474,c_8536]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_26,negated_conjecture,
% 3.70/0.99      ( sK3 != sK4 ),
% 3.70/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1022,plain,( X0 = X0 ),theory(equality) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1049,plain,
% 3.70/0.99      ( sK3 = sK3 ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_1022]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1023,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1745,plain,
% 3.70/0.99      ( sK4 != X0 | sK3 != X0 | sK3 = sK4 ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_1023]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1746,plain,
% 3.70/0.99      ( sK4 != sK3 | sK3 = sK4 | sK3 != sK3 ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_1745]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_8785,plain,
% 3.70/0.99      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 3.70/0.99      | k1_wellord1(k1_wellord2(sK4),sK3) = sK3 ),
% 3.70/0.99      inference(global_propositional_subsumption,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_8564,c_26,c_1049,c_1746]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_8786,plain,
% 3.70/0.99      ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3
% 3.70/0.99      | k1_wellord1(k1_wellord2(sK3),sK4) = sK4 ),
% 3.70/0.99      inference(renaming,[status(thm)],[c_8785]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_14,plain,
% 3.70/0.99      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
% 3.70/0.99      | ~ r2_hidden(X1,k3_relat_1(X0))
% 3.70/0.99      | ~ v2_wellord1(X0)
% 3.70/0.99      | ~ v1_relat_1(X0) ),
% 3.70/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_24,plain,
% 3.70/0.99      ( v2_wellord1(k1_wellord2(X0)) | ~ v3_ordinal1(X0) ),
% 3.70/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_328,plain,
% 3.70/0.99      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
% 3.70/0.99      | ~ r2_hidden(X1,k3_relat_1(X0))
% 3.70/0.99      | ~ v1_relat_1(X0)
% 3.70/0.99      | ~ v3_ordinal1(X2)
% 3.70/0.99      | k1_wellord2(X2) != X0 ),
% 3.70/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_24]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_329,plain,
% 3.70/0.99      ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
% 3.70/0.99      | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
% 3.70/0.99      | ~ v1_relat_1(k1_wellord2(X0))
% 3.70/0.99      | ~ v3_ordinal1(X0) ),
% 3.70/0.99      inference(unflattening,[status(thm)],[c_328]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_22,plain,
% 3.70/0.99      ( v1_relat_1(k1_wellord2(X0)) ),
% 3.70/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_333,plain,
% 3.70/0.99      ( ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
% 3.70/0.99      | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
% 3.70/0.99      | ~ v3_ordinal1(X0) ),
% 3.70/0.99      inference(global_propositional_subsumption,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_329,c_22]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_334,plain,
% 3.70/0.99      ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
% 3.70/0.99      | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
% 3.70/0.99      | ~ v3_ordinal1(X0) ),
% 3.70/0.99      inference(renaming,[status(thm)],[c_333]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1473,plain,
% 3.70/0.99      ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
% 3.70/0.99      | r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) != iProver_top
% 3.70/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_334]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_21,plain,
% 3.70/0.99      ( ~ v1_relat_1(k1_wellord2(X0))
% 3.70/0.99      | k3_relat_1(k1_wellord2(X0)) = X0 ),
% 3.70/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_173,plain,
% 3.70/0.99      ( k3_relat_1(k1_wellord2(X0)) = X0 ),
% 3.70/0.99      inference(global_propositional_subsumption,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_21,c_22]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1592,plain,
% 3.70/0.99      ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
% 3.70/0.99      | r2_hidden(X1,X0) != iProver_top
% 3.70/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.70/0.99      inference(light_normalisation,[status(thm)],[c_1473,c_173]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_8792,plain,
% 3.70/0.99      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 3.70/0.99      | r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) != iProver_top
% 3.70/0.99      | r2_hidden(sK3,sK4) != iProver_top
% 3.70/0.99      | v3_ordinal1(sK4) != iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_8786,c_1592]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_30,plain,
% 3.70/0.99      ( v3_ordinal1(sK3) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_31,plain,
% 3.70/0.99      ( v3_ordinal1(sK4) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1985,plain,
% 3.70/0.99      ( ~ r2_hidden(sK4,X0)
% 3.70/0.99      | ~ v3_ordinal1(X0)
% 3.70/0.99      | ~ v3_ordinal1(sK4)
% 3.70/0.99      | k1_wellord1(k1_wellord2(X0),sK4) = sK4 ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_23]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1987,plain,
% 3.70/0.99      ( k1_wellord1(k1_wellord2(X0),sK4) = sK4
% 3.70/0.99      | r2_hidden(sK4,X0) != iProver_top
% 3.70/0.99      | v3_ordinal1(X0) != iProver_top
% 3.70/0.99      | v3_ordinal1(sK4) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_1985]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1989,plain,
% 3.70/0.99      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 3.70/0.99      | r2_hidden(sK4,sK3) != iProver_top
% 3.70/0.99      | v3_ordinal1(sK4) != iProver_top
% 3.70/0.99      | v3_ordinal1(sK3) != iProver_top ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_1987]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_2003,plain,
% 3.70/0.99      ( r2_hidden(sK4,sK3)
% 3.70/0.99      | r2_hidden(sK3,sK4)
% 3.70/0.99      | ~ v3_ordinal1(sK4)
% 3.70/0.99      | ~ v3_ordinal1(sK3)
% 3.70/0.99      | sK3 = sK4 ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_2004,plain,
% 3.70/0.99      ( sK3 = sK4
% 3.70/0.99      | r2_hidden(sK4,sK3) = iProver_top
% 3.70/0.99      | r2_hidden(sK3,sK4) = iProver_top
% 3.70/0.99      | v3_ordinal1(sK4) != iProver_top
% 3.70/0.99      | v3_ordinal1(sK3) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_2003]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_9220,plain,
% 3.70/0.99      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 3.70/0.99      | r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) != iProver_top ),
% 3.70/0.99      inference(global_propositional_subsumption,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_8792,c_30,c_31,c_26,c_1989,c_2004]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_9226,plain,
% 3.70/0.99      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 3.70/0.99      | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) != iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_5569,c_9220]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_27,negated_conjecture,
% 3.70/0.99      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) ),
% 3.70/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1476,plain,
% 3.70/0.99      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_13,plain,
% 3.70/0.99      ( ~ r4_wellord1(X0,X1)
% 3.70/0.99      | r4_wellord1(X1,X0)
% 3.70/0.99      | ~ v1_relat_1(X0)
% 3.70/0.99      | ~ v1_relat_1(X1) ),
% 3.70/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1486,plain,
% 3.70/0.99      ( r4_wellord1(X0,X1) != iProver_top
% 3.70/0.99      | r4_wellord1(X1,X0) = iProver_top
% 3.70/0.99      | v1_relat_1(X0) != iProver_top
% 3.70/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3126,plain,
% 3.70/0.99      ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
% 3.70/0.99      | v1_relat_1(k1_wellord2(sK4)) != iProver_top
% 3.70/0.99      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_1476,c_1486]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_42,plain,
% 3.70/0.99      ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_44,plain,
% 3.70/0.99      ( v1_relat_1(k1_wellord2(sK3)) = iProver_top ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_42]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3392,plain,
% 3.70/0.99      ( v1_relat_1(k1_wellord2(sK4)) != iProver_top
% 3.70/0.99      | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top ),
% 3.70/0.99      inference(global_propositional_subsumption,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_3126,c_44]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3393,plain,
% 3.70/0.99      ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
% 3.70/0.99      | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
% 3.70/0.99      inference(renaming,[status(thm)],[c_3392]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1479,plain,
% 3.70/0.99      ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3398,plain,
% 3.70/0.99      ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top ),
% 3.70/0.99      inference(forward_subsumption_resolution,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_3393,c_1479]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_9426,plain,
% 3.70/0.99      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4 ),
% 3.70/0.99      inference(global_propositional_subsumption,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_9226,c_3398]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_12,plain,
% 3.70/0.99      ( ~ v2_wellord1(X0)
% 3.70/0.99      | ~ v1_relat_1(X0)
% 3.70/0.99      | k3_relat_1(k2_wellord1(X0,k1_wellord1(X0,X1))) = k1_wellord1(X0,X1) ),
% 3.70/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_349,plain,
% 3.70/0.99      ( ~ v1_relat_1(X0)
% 3.70/0.99      | ~ v3_ordinal1(X1)
% 3.70/0.99      | k1_wellord2(X1) != X0
% 3.70/0.99      | k3_relat_1(k2_wellord1(X0,k1_wellord1(X0,X2))) = k1_wellord1(X0,X2) ),
% 3.70/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_24]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_350,plain,
% 3.70/0.99      ( ~ v1_relat_1(k1_wellord2(X0))
% 3.70/0.99      | ~ v3_ordinal1(X0)
% 3.70/0.99      | k3_relat_1(k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) = k1_wellord1(k1_wellord2(X0),X1) ),
% 3.70/0.99      inference(unflattening,[status(thm)],[c_349]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_354,plain,
% 3.70/0.99      ( ~ v3_ordinal1(X0)
% 3.70/0.99      | k3_relat_1(k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) = k1_wellord1(k1_wellord2(X0),X1) ),
% 3.70/0.99      inference(global_propositional_subsumption,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_350,c_22]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1472,plain,
% 3.70/0.99      ( k3_relat_1(k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) = k1_wellord1(k1_wellord2(X0),X1)
% 3.70/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_354]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_2358,plain,
% 3.70/0.99      ( k3_relat_1(k2_wellord1(k1_wellord2(sK3),k1_wellord1(k1_wellord2(sK3),X0))) = k1_wellord1(k1_wellord2(sK3),X0) ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_1474,c_1472]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_11,plain,
% 3.70/0.99      ( r2_hidden(X0,k3_relat_1(X1))
% 3.70/0.99      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X1,X2)))
% 3.70/0.99      | ~ v1_relat_1(X1) ),
% 3.70/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1487,plain,
% 3.70/0.99      ( r2_hidden(X0,k3_relat_1(X1)) = iProver_top
% 3.70/0.99      | r2_hidden(X0,k3_relat_1(k2_wellord1(X1,X2))) != iProver_top
% 3.70/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_2463,plain,
% 3.70/0.99      ( r2_hidden(X0,k1_wellord1(k1_wellord2(sK3),X1)) != iProver_top
% 3.70/0.99      | r2_hidden(X0,k3_relat_1(k1_wellord2(sK3))) = iProver_top
% 3.70/0.99      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_2358,c_1487]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_2485,plain,
% 3.70/0.99      ( r2_hidden(X0,k1_wellord1(k1_wellord2(sK3),X1)) != iProver_top
% 3.70/0.99      | r2_hidden(X0,sK3) = iProver_top
% 3.70/0.99      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 3.70/0.99      inference(demodulation,[status(thm)],[c_2463,c_173]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3402,plain,
% 3.70/0.99      ( r2_hidden(X0,sK3) = iProver_top
% 3.70/0.99      | r2_hidden(X0,k1_wellord1(k1_wellord2(sK3),X1)) != iProver_top ),
% 3.70/0.99      inference(global_propositional_subsumption,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_2485,c_44]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3403,plain,
% 3.70/0.99      ( r2_hidden(X0,k1_wellord1(k1_wellord2(sK3),X1)) != iProver_top
% 3.70/0.99      | r2_hidden(X0,sK3) = iProver_top ),
% 3.70/0.99      inference(renaming,[status(thm)],[c_3402]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_9481,plain,
% 3.70/0.99      ( r2_hidden(X0,sK4) != iProver_top
% 3.70/0.99      | r2_hidden(X0,sK3) = iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_9426,c_3403]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_9652,plain,
% 3.70/0.99      ( r2_hidden(sK3,sK4) != iProver_top
% 3.70/0.99      | r2_hidden(sK3,sK3) = iProver_top ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_9481]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_9432,plain,
% 3.70/0.99      ( r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK4)) != iProver_top
% 3.70/0.99      | r2_hidden(sK4,sK3) != iProver_top
% 3.70/0.99      | v3_ordinal1(sK3) != iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_9426,c_1592]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_9,plain,
% 3.70/0.99      ( ~ r2_hidden(X0,k1_wellord1(X1,X0)) | ~ v1_relat_1(X1) ),
% 3.70/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1489,plain,
% 3.70/0.99      ( r2_hidden(X0,k1_wellord1(X1,X0)) != iProver_top
% 3.70/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_8791,plain,
% 3.70/0.99      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 3.70/0.99      | r2_hidden(sK3,sK3) != iProver_top
% 3.70/0.99      | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_8786,c_1489]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_39,plain,
% 3.70/0.99      ( k1_wellord1(k1_wellord2(X0),X1) = X1
% 3.70/0.99      | r2_hidden(X1,X0) != iProver_top
% 3.70/0.99      | v3_ordinal1(X1) != iProver_top
% 3.70/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_41,plain,
% 3.70/0.99      ( k1_wellord1(k1_wellord2(sK3),sK3) = sK3
% 3.70/0.99      | r2_hidden(sK3,sK3) != iProver_top
% 3.70/0.99      | v3_ordinal1(sK3) != iProver_top ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_39]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1759,plain,
% 3.70/0.99      ( ~ r2_hidden(X0,k1_wellord1(k1_wellord2(X1),X0))
% 3.70/0.99      | ~ v1_relat_1(k1_wellord2(X1)) ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1760,plain,
% 3.70/0.99      ( r2_hidden(X0,k1_wellord1(k1_wellord2(X1),X0)) != iProver_top
% 3.70/0.99      | v1_relat_1(k1_wellord2(X1)) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_1759]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1762,plain,
% 3.70/0.99      ( r2_hidden(sK3,k1_wellord1(k1_wellord2(sK3),sK3)) != iProver_top
% 3.70/0.99      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_1760]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1026,plain,
% 3.70/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.70/0.99      theory(equality) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3344,plain,
% 3.70/0.99      ( ~ r2_hidden(X0,X1)
% 3.70/0.99      | r2_hidden(X2,k1_wellord1(k1_wellord2(X3),X2))
% 3.70/0.99      | X2 != X0
% 3.70/0.99      | k1_wellord1(k1_wellord2(X3),X2) != X1 ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_1026]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3345,plain,
% 3.70/0.99      ( X0 != X1
% 3.70/0.99      | k1_wellord1(k1_wellord2(X2),X0) != X3
% 3.70/0.99      | r2_hidden(X1,X3) != iProver_top
% 3.70/0.99      | r2_hidden(X0,k1_wellord1(k1_wellord2(X2),X0)) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_3344]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3347,plain,
% 3.70/0.99      ( k1_wellord1(k1_wellord2(sK3),sK3) != sK3
% 3.70/0.99      | sK3 != sK3
% 3.70/0.99      | r2_hidden(sK3,k1_wellord1(k1_wellord2(sK3),sK3)) = iProver_top
% 3.70/0.99      | r2_hidden(sK3,sK3) != iProver_top ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_3345]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_9047,plain,
% 3.70/0.99      ( r2_hidden(sK3,sK3) != iProver_top ),
% 3.70/0.99      inference(global_propositional_subsumption,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_8791,c_30,c_41,c_44,c_1049,c_1762,c_3347]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_5436,plain,
% 3.70/0.99      ( r2_hidden(X0,sK4)
% 3.70/0.99      | r1_tarski(sK4,X0)
% 3.70/0.99      | ~ v3_ordinal1(X0)
% 3.70/0.99      | ~ v3_ordinal1(sK4) ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_376]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_5437,plain,
% 3.70/0.99      ( r2_hidden(X0,sK4) = iProver_top
% 3.70/0.99      | r1_tarski(sK4,X0) = iProver_top
% 3.70/0.99      | v3_ordinal1(X0) != iProver_top
% 3.70/0.99      | v3_ordinal1(sK4) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_5436]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_5439,plain,
% 3.70/0.99      ( r2_hidden(sK3,sK4) = iProver_top
% 3.70/0.99      | r1_tarski(sK4,sK3) = iProver_top
% 3.70/0.99      | v3_ordinal1(sK4) != iProver_top
% 3.70/0.99      | v3_ordinal1(sK3) != iProver_top ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_5437]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1032,plain,
% 3.70/0.99      ( ~ r4_wellord1(X0,X1) | r4_wellord1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.70/0.99      theory(equality) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1777,plain,
% 3.70/0.99      ( r4_wellord1(X0,X1)
% 3.70/0.99      | ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4))
% 3.70/0.99      | X1 != k1_wellord2(sK4)
% 3.70/0.99      | X0 != k1_wellord2(sK3) ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_1032]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_2266,plain,
% 3.70/0.99      ( r4_wellord1(X0,k2_wellord1(k1_wellord2(X1),sK4))
% 3.70/0.99      | ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4))
% 3.70/0.99      | X0 != k1_wellord2(sK3)
% 3.70/0.99      | k2_wellord1(k1_wellord2(X1),sK4) != k1_wellord2(sK4) ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_1777]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_2757,plain,
% 3.70/0.99      ( r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(X0),sK4))
% 3.70/0.99      | ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4))
% 3.70/0.99      | k2_wellord1(k1_wellord2(X0),sK4) != k1_wellord2(sK4)
% 3.70/0.99      | k1_wellord2(sK3) != k1_wellord2(sK3) ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_2266]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_2770,plain,
% 3.70/0.99      ( k2_wellord1(k1_wellord2(X0),sK4) != k1_wellord2(sK4)
% 3.70/0.99      | k1_wellord2(sK3) != k1_wellord2(sK3)
% 3.70/0.99      | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(X0),sK4)) = iProver_top
% 3.70/0.99      | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_2757]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_2772,plain,
% 3.70/0.99      ( k2_wellord1(k1_wellord2(sK3),sK4) != k1_wellord2(sK4)
% 3.70/0.99      | k1_wellord2(sK3) != k1_wellord2(sK3)
% 3.70/0.99      | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK4)) = iProver_top
% 3.70/0.99      | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) != iProver_top ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_2770]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_2265,plain,
% 3.70/0.99      ( ~ r1_tarski(sK4,X0)
% 3.70/0.99      | k2_wellord1(k1_wellord2(X0),sK4) = k1_wellord2(sK4) ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_25]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_2267,plain,
% 3.70/0.99      ( k2_wellord1(k1_wellord2(X0),sK4) = k1_wellord2(sK4)
% 3.70/0.99      | r1_tarski(sK4,X0) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_2265]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_2269,plain,
% 3.70/0.99      ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
% 3.70/0.99      | r1_tarski(sK4,sK3) != iProver_top ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_2267]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1033,plain,
% 3.70/0.99      ( X0 != X1 | k1_wellord2(X0) = k1_wellord2(X1) ),
% 3.70/0.99      theory(equality) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1045,plain,
% 3.70/0.99      ( k1_wellord2(sK3) = k1_wellord2(sK3) | sK3 != sK3 ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_1033]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_32,plain,
% 3.70/0.99      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(contradiction,plain,
% 3.70/0.99      ( $false ),
% 3.70/0.99      inference(minisat,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_9652,c_9432,c_9047,c_5439,c_2772,c_2269,c_2004,c_1049,
% 3.70/0.99                 c_1045,c_26,c_32,c_31,c_30]) ).
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.70/0.99  
% 3.70/0.99  ------                               Statistics
% 3.70/0.99  
% 3.70/0.99  ------ General
% 3.70/0.99  
% 3.70/0.99  abstr_ref_over_cycles:                  0
% 3.70/0.99  abstr_ref_under_cycles:                 0
% 3.70/0.99  gc_basic_clause_elim:                   0
% 3.70/0.99  forced_gc_time:                         0
% 3.70/0.99  parsing_time:                           0.012
% 3.70/0.99  unif_index_cands_time:                  0.
% 3.70/0.99  unif_index_add_time:                    0.
% 3.70/0.99  orderings_time:                         0.
% 3.70/0.99  out_proof_time:                         0.014
% 3.70/0.99  total_time:                             0.326
% 3.70/0.99  num_of_symbols:                         48
% 3.70/0.99  num_of_terms:                           10727
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing
% 3.70/0.99  
% 3.70/0.99  num_of_splits:                          0
% 3.70/0.99  num_of_split_atoms:                     0
% 3.70/0.99  num_of_reused_defs:                     0
% 3.70/0.99  num_eq_ax_congr_red:                    20
% 3.70/0.99  num_of_sem_filtered_clauses:            1
% 3.70/0.99  num_of_subtypes:                        0
% 3.70/0.99  monotx_restored_types:                  0
% 3.70/0.99  sat_num_of_epr_types:                   0
% 3.70/0.99  sat_num_of_non_cyclic_types:            0
% 3.70/0.99  sat_guarded_non_collapsed_types:        0
% 3.70/0.99  num_pure_diseq_elim:                    0
% 3.70/0.99  simp_replaced_by:                       0
% 3.70/0.99  res_preprocessed:                       140
% 3.70/0.99  prep_upred:                             0
% 3.70/0.99  prep_unflattend:                        32
% 3.70/0.99  smt_new_axioms:                         0
% 3.70/0.99  pred_elim_cands:                        5
% 3.70/0.99  pred_elim:                              2
% 3.70/0.99  pred_elim_cl:                           3
% 3.70/0.99  pred_elim_cycles:                       4
% 3.70/0.99  merged_defs:                            0
% 3.70/0.99  merged_defs_ncl:                        0
% 3.70/0.99  bin_hyper_res:                          0
% 3.70/0.99  prep_cycles:                            4
% 3.70/0.99  pred_elim_time:                         0.012
% 3.70/0.99  splitting_time:                         0.
% 3.70/0.99  sem_filter_time:                        0.
% 3.70/0.99  monotx_time:                            0.001
% 3.70/0.99  subtype_inf_time:                       0.
% 3.70/0.99  
% 3.70/0.99  ------ Problem properties
% 3.70/0.99  
% 3.70/0.99  clauses:                                27
% 3.70/0.99  conjectures:                            4
% 3.70/0.99  epr:                                    6
% 3.70/0.99  horn:                                   18
% 3.70/0.99  ground:                                 4
% 3.70/0.99  unary:                                  6
% 3.70/0.99  binary:                                 3
% 3.70/0.99  lits:                                   82
% 3.70/0.99  lits_eq:                                16
% 3.70/0.99  fd_pure:                                0
% 3.70/0.99  fd_pseudo:                              0
% 3.70/0.99  fd_cond:                                0
% 3.70/0.99  fd_pseudo_cond:                         4
% 3.70/0.99  ac_symbols:                             0
% 3.70/0.99  
% 3.70/0.99  ------ Propositional Solver
% 3.70/0.99  
% 3.70/0.99  prop_solver_calls:                      27
% 3.70/0.99  prop_fast_solver_calls:                 1297
% 3.70/0.99  smt_solver_calls:                       0
% 3.70/0.99  smt_fast_solver_calls:                  0
% 3.70/0.99  prop_num_of_clauses:                    3333
% 3.70/0.99  prop_preprocess_simplified:             9360
% 3.70/0.99  prop_fo_subsumed:                       22
% 3.70/0.99  prop_solver_time:                       0.
% 3.70/0.99  smt_solver_time:                        0.
% 3.70/0.99  smt_fast_solver_time:                   0.
% 3.70/0.99  prop_fast_solver_time:                  0.
% 3.70/0.99  prop_unsat_core_time:                   0.
% 3.70/0.99  
% 3.70/0.99  ------ QBF
% 3.70/0.99  
% 3.70/0.99  qbf_q_res:                              0
% 3.70/0.99  qbf_num_tautologies:                    0
% 3.70/0.99  qbf_prep_cycles:                        0
% 3.70/0.99  
% 3.70/0.99  ------ BMC1
% 3.70/0.99  
% 3.70/0.99  bmc1_current_bound:                     -1
% 3.70/0.99  bmc1_last_solved_bound:                 -1
% 3.70/0.99  bmc1_unsat_core_size:                   -1
% 3.70/0.99  bmc1_unsat_core_parents_size:           -1
% 3.70/0.99  bmc1_merge_next_fun:                    0
% 3.70/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.70/0.99  
% 3.70/0.99  ------ Instantiation
% 3.70/0.99  
% 3.70/0.99  inst_num_of_clauses:                    808
% 3.70/0.99  inst_num_in_passive:                    353
% 3.70/0.99  inst_num_in_active:                     345
% 3.70/0.99  inst_num_in_unprocessed:                110
% 3.70/0.99  inst_num_of_loops:                      410
% 3.70/0.99  inst_num_of_learning_restarts:          0
% 3.70/0.99  inst_num_moves_active_passive:          64
% 3.70/0.99  inst_lit_activity:                      0
% 3.70/0.99  inst_lit_activity_moves:                0
% 3.70/0.99  inst_num_tautologies:                   0
% 3.70/0.99  inst_num_prop_implied:                  0
% 3.70/0.99  inst_num_existing_simplified:           0
% 3.70/0.99  inst_num_eq_res_simplified:             0
% 3.70/0.99  inst_num_child_elim:                    0
% 3.70/0.99  inst_num_of_dismatching_blockings:      542
% 3.70/0.99  inst_num_of_non_proper_insts:           888
% 3.70/0.99  inst_num_of_duplicates:                 0
% 3.70/0.99  inst_inst_num_from_inst_to_res:         0
% 3.70/0.99  inst_dismatching_checking_time:         0.
% 3.70/0.99  
% 3.70/0.99  ------ Resolution
% 3.70/0.99  
% 3.70/0.99  res_num_of_clauses:                     0
% 3.70/0.99  res_num_in_passive:                     0
% 3.70/0.99  res_num_in_active:                      0
% 3.70/0.99  res_num_of_loops:                       144
% 3.70/0.99  res_forward_subset_subsumed:            31
% 3.70/0.99  res_backward_subset_subsumed:           0
% 3.70/0.99  res_forward_subsumed:                   0
% 3.70/0.99  res_backward_subsumed:                  0
% 3.70/0.99  res_forward_subsumption_resolution:     6
% 3.70/0.99  res_backward_subsumption_resolution:    0
% 3.70/0.99  res_clause_to_clause_subsumption:       643
% 3.70/0.99  res_orphan_elimination:                 0
% 3.70/0.99  res_tautology_del:                      34
% 3.70/0.99  res_num_eq_res_simplified:              0
% 3.70/0.99  res_num_sel_changes:                    0
% 3.70/0.99  res_moves_from_active_to_pass:          0
% 3.70/0.99  
% 3.70/0.99  ------ Superposition
% 3.70/0.99  
% 3.70/0.99  sup_time_total:                         0.
% 3.70/0.99  sup_time_generating:                    0.
% 3.70/0.99  sup_time_sim_full:                      0.
% 3.70/0.99  sup_time_sim_immed:                     0.
% 3.70/0.99  
% 3.70/0.99  sup_num_of_clauses:                     191
% 3.70/0.99  sup_num_in_active:                      79
% 3.70/0.99  sup_num_in_passive:                     112
% 3.70/0.99  sup_num_of_loops:                       80
% 3.70/0.99  sup_fw_superposition:                   109
% 3.70/0.99  sup_bw_superposition:                   226
% 3.70/0.99  sup_immediate_simplified:               52
% 3.70/0.99  sup_given_eliminated:                   0
% 3.70/0.99  comparisons_done:                       0
% 3.70/0.99  comparisons_avoided:                    54
% 3.70/0.99  
% 3.70/0.99  ------ Simplifications
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  sim_fw_subset_subsumed:                 7
% 3.70/0.99  sim_bw_subset_subsumed:                 10
% 3.70/0.99  sim_fw_subsumed:                        4
% 3.70/0.99  sim_bw_subsumed:                        0
% 3.70/0.99  sim_fw_subsumption_res:                 6
% 3.70/0.99  sim_bw_subsumption_res:                 0
% 3.70/0.99  sim_tautology_del:                      13
% 3.70/0.99  sim_eq_tautology_del:                   13
% 3.70/0.99  sim_eq_res_simp:                        0
% 3.70/0.99  sim_fw_demodulated:                     14
% 3.70/0.99  sim_bw_demodulated:                     0
% 3.70/0.99  sim_light_normalised:                   32
% 3.70/0.99  sim_joinable_taut:                      0
% 3.70/0.99  sim_joinable_simp:                      0
% 3.70/0.99  sim_ac_normalised:                      0
% 3.70/0.99  sim_smt_subsumption:                    0
% 3.70/0.99  
%------------------------------------------------------------------------------
