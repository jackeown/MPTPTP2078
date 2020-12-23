%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:41 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :  229 (151903 expanded)
%              Number of clauses        :  161 (56363 expanded)
%              Number of leaves         :   18 (30468 expanded)
%              Depth                    :   86
%              Number of atoms          :  873 (604220 expanded)
%              Number of equality atoms :  504 (203124 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   17 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
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

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_wellord1(k1_wellord2(X1),X0) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f70,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

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

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
     => ( sK3 != X0
        & r4_wellord1(k1_wellord2(X0),k1_wellord2(sK3))
        & v3_ordinal1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
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

fof(f48,plain,
    ( sK2 != sK3
    & r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
    & v3_ordinal1(sK3)
    & v3_ordinal1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f37,f47,f46])).

fof(f72,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f73,plain,(
    v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
       => ( r2_hidden(X0,X1)
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f30,plain,(
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
    inference(flattening,[],[f30])).

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
    inference(nnf_transformation,[],[f31])).

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
    inference(flattening,[],[f41])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f44,plain,(
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

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f43,f44])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f84,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f61])).

fof(f10,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f75,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f48])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f77,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f74,plain,(
    r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) ),
    inference(cnf_transformation,[],[f48])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

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

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( ( r4_wellord1(X1,X2)
                  & r4_wellord1(X0,X1) )
               => r4_wellord1(X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_wellord1(X0,X2)
              | ~ r4_wellord1(X1,X2)
              | ~ r4_wellord1(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_wellord1(X0,X2)
              | ~ r4_wellord1(X1,X2)
              | ~ r4_wellord1(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r4_wellord1(X0,X2)
      | ~ r4_wellord1(X1,X2)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_792,plain,
    ( X0 = X1
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | k1_wellord1(k1_wellord2(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_779,plain,
    ( k1_wellord1(k1_wellord2(X0),X1) = X1
    | r2_hidden(X1,X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2282,plain,
    ( X0 = X1
    | k1_wellord1(k1_wellord2(X1),X0) = X0
    | r2_hidden(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_792,c_779])).

cnf(c_21,plain,
    ( v2_wellord1(k1_wellord2(X0))
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_778,plain,
    ( v2_wellord1(k1_wellord2(X0)) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_26,negated_conjecture,
    ( v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_774,plain,
    ( v3_ordinal1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_775,plain,
    ( v3_ordinal1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3,plain,
    ( r1_ordinal1(X0,X1)
    | r1_ordinal1(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_795,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r1_ordinal1(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_793,plain,
    ( r1_ordinal1(X0,X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2151,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r1_tarski(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_795,c_793])).

cnf(c_3300,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2151,c_793])).

cnf(c_22,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_777,plain,
    ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3310,plain,
    ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3300,c_777])).

cnf(c_3459,plain,
    ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3310,c_777])).

cnf(c_3640,plain,
    ( k2_wellord1(k1_wellord2(X0),sK3) = k1_wellord2(sK3)
    | k2_wellord1(k1_wellord2(sK3),X0) = k1_wellord2(X0)
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_775,c_3459])).

cnf(c_3789,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
    inference(superposition,[status(thm)],[c_774,c_3640])).

cnf(c_8,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_790,plain,
    ( r2_hidden(X0,k3_relat_1(X1)) = iProver_top
    | r2_hidden(X0,k3_relat_1(k2_wellord1(X1,X2))) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3798,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | r2_hidden(X0,k3_relat_1(k1_wellord2(sK3))) = iProver_top
    | r2_hidden(X0,k3_relat_1(k1_wellord2(sK2))) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3789,c_790])).

cnf(c_18,plain,
    ( ~ v1_relat_1(k1_wellord2(X0))
    | k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_19,plain,
    ( v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_186,plain,
    ( k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_19])).

cnf(c_3816,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3798,c_186])).

cnf(c_2071,plain,
    ( v1_relat_1(k1_wellord2(sK3)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2072,plain,
    ( v1_relat_1(k1_wellord2(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2071])).

cnf(c_3957,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3816,c_2072])).

cnf(c_3958,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3957])).

cnf(c_3966,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | sK2 = X0
    | r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(sK2,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_792,c_3958])).

cnf(c_27,plain,
    ( v3_ordinal1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4354,plain,
    ( v3_ordinal1(X0) != iProver_top
    | r2_hidden(sK2,X0) = iProver_top
    | r2_hidden(X0,sK3) = iProver_top
    | sK2 = X0
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3966,c_27])).

cnf(c_4355,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | sK2 = X0
    | r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(sK2,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4354])).

cnf(c_4363,plain,
    ( k1_wellord1(k1_wellord2(X0),sK2) = sK2
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | sK2 = X0
    | r2_hidden(X0,sK3) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4355,c_779])).

cnf(c_6337,plain,
    ( v3_ordinal1(X0) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top
    | sK2 = X0
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | k1_wellord1(k1_wellord2(X0),sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4363,c_27])).

cnf(c_6338,plain,
    ( k1_wellord1(k1_wellord2(X0),sK2) = sK2
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | sK2 = X0
    | r2_hidden(X0,sK3) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6337])).

cnf(c_6346,plain,
    ( k1_wellord1(k1_wellord2(X0),sK2) = sK2
    | k1_wellord1(k1_wellord2(sK3),X0) = X0
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | sK2 = X0
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6338,c_779])).

cnf(c_4367,plain,
    ( k1_wellord1(k1_wellord2(sK3),X0) = X0
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | sK2 = X0
    | r2_hidden(sK2,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4355,c_779])).

cnf(c_28,plain,
    ( v3_ordinal1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_6377,plain,
    ( v3_ordinal1(X0) != iProver_top
    | r2_hidden(sK2,X0) = iProver_top
    | sK2 = X0
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | k1_wellord1(k1_wellord2(sK3),X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4367,c_28])).

cnf(c_6378,plain,
    ( k1_wellord1(k1_wellord2(sK3),X0) = X0
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | sK2 = X0
    | r2_hidden(sK2,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6377])).

cnf(c_6386,plain,
    ( k1_wellord1(k1_wellord2(X0),sK2) = sK2
    | k1_wellord1(k1_wellord2(sK3),X0) = X0
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | sK2 = X0
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6378,c_779])).

cnf(c_6672,plain,
    ( v3_ordinal1(X0) != iProver_top
    | sK2 = X0
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | k1_wellord1(k1_wellord2(sK3),X0) = X0
    | k1_wellord1(k1_wellord2(X0),sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6346,c_27,c_6386])).

cnf(c_6673,plain,
    ( k1_wellord1(k1_wellord2(X0),sK2) = sK2
    | k1_wellord1(k1_wellord2(sK3),X0) = X0
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | sK2 = X0
    | v3_ordinal1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6672])).

cnf(c_6681,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK3) = sK3
    | k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_775,c_6673])).

cnf(c_23,negated_conjecture,
    ( sK2 != sK3 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_78,plain,
    ( ~ r1_ordinal1(sK2,sK2)
    | r1_tarski(sK2,sK2)
    | ~ v3_ordinal1(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_84,plain,
    ( r1_ordinal1(sK2,sK2)
    | ~ v3_ordinal1(sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_91,plain,
    ( ~ r1_tarski(sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_357,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1081,plain,
    ( sK3 != X0
    | sK2 != X0
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_357])).

cnf(c_1082,plain,
    ( sK3 != sK2
    | sK2 = sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1081])).

cnf(c_6852,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k1_wellord1(k1_wellord2(sK3),sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6681,c_26,c_23,c_78,c_84,c_91,c_1082])).

cnf(c_6853,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK3) = sK3
    | k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
    inference(renaming,[status(thm)],[c_6852])).

cnf(c_11,plain,
    ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
    | ~ r2_hidden(X1,k3_relat_1(X0))
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_787,plain,
    ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) != iProver_top
    | r2_hidden(X1,k3_relat_1(X0)) != iProver_top
    | v2_wellord1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6857,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK3)) != iProver_top
    | r2_hidden(sK3,k3_relat_1(k1_wellord2(sK3))) != iProver_top
    | v2_wellord1(k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6853,c_787])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_796,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1277,plain,
    ( k2_wellord1(k1_wellord2(X0),X0) = k1_wellord2(X0) ),
    inference(superposition,[status(thm)],[c_796,c_777])).

cnf(c_6858,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK3)) != iProver_top
    | r2_hidden(sK3,sK3) != iProver_top
    | v2_wellord1(k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6857,c_186,c_1277])).

cnf(c_24,negated_conjecture,
    ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_29,plain,
    ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_39,plain,
    ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_41,plain,
    ( v1_relat_1(k1_wellord2(sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_776,plain,
    ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_9,plain,
    ( ~ r4_wellord1(X0,X1)
    | r4_wellord1(X1,X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_789,plain,
    ( r4_wellord1(X0,X1) != iProver_top
    | r4_wellord1(X1,X0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1684,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_776,c_789])).

cnf(c_1847,plain,
    ( v1_relat_1(k1_wellord2(sK3)) != iProver_top
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1684,c_41])).

cnf(c_1848,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1847])).

cnf(c_780,plain,
    ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1853,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1848,c_780])).

cnf(c_10,plain,
    ( ~ r4_wellord1(X0,X1)
    | ~ r4_wellord1(X1,X2)
    | r4_wellord1(X0,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1126,plain,
    ( ~ r4_wellord1(X0,X1)
    | ~ r4_wellord1(k1_wellord2(X2),X0)
    | r4_wellord1(k1_wellord2(X2),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(k1_wellord2(X2)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1313,plain,
    ( ~ r4_wellord1(k1_wellord2(X0),X1)
    | r4_wellord1(k1_wellord2(X2),X1)
    | ~ r4_wellord1(k1_wellord2(X2),k1_wellord2(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(k1_wellord2(X0))
    | ~ v1_relat_1(k1_wellord2(X2)) ),
    inference(instantiation,[status(thm)],[c_1126])).

cnf(c_1843,plain,
    ( r4_wellord1(k1_wellord2(X0),k1_wellord2(sK3))
    | ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(sK2))
    | ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
    | ~ v1_relat_1(k1_wellord2(X0))
    | ~ v1_relat_1(k1_wellord2(sK3))
    | ~ v1_relat_1(k1_wellord2(sK2)) ),
    inference(instantiation,[status(thm)],[c_1313])).

cnf(c_1909,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK3))
    | ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2))
    | ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
    | ~ v1_relat_1(k1_wellord2(sK3))
    | ~ v1_relat_1(k1_wellord2(sK2)) ),
    inference(instantiation,[status(thm)],[c_1843])).

cnf(c_1910,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK3)) = iProver_top
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) != iProver_top
    | r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1909])).

cnf(c_6861,plain,
    ( v2_wellord1(k1_wellord2(sK3)) != iProver_top
    | r2_hidden(sK3,sK3) != iProver_top
    | k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6858,c_29,c_41,c_1853,c_1910,c_2072])).

cnf(c_6862,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | r2_hidden(sK3,sK3) != iProver_top
    | v2_wellord1(k1_wellord2(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6861])).

cnf(c_6873,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | sK3 = sK2
    | v2_wellord1(k1_wellord2(sK3)) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6338,c_6862])).

cnf(c_7093,plain,
    ( v2_wellord1(k1_wellord2(sK3)) != iProver_top
    | k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6873,c_26,c_28,c_23,c_78,c_84,c_91,c_1082])).

cnf(c_7094,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | v2_wellord1(k1_wellord2(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7093])).

cnf(c_7100,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_778,c_7094])).

cnf(c_7101,plain,
    ( ~ v3_ordinal1(sK3)
    | k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7100])).

cnf(c_7650,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7100,c_25,c_7101])).

cnf(c_7651,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
    inference(renaming,[status(thm)],[c_7650])).

cnf(c_7654,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top
    | r2_hidden(sK2,k3_relat_1(k1_wellord2(sK3))) != iProver_top
    | v2_wellord1(k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7651,c_787])).

cnf(c_7655,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top
    | v2_wellord1(k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7654,c_186])).

cnf(c_7891,plain,
    ( v2_wellord1(k1_wellord2(sK3)) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7655,c_2072])).

cnf(c_7892,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top
    | v2_wellord1(k1_wellord2(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7891])).

cnf(c_7899,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top
    | v2_wellord1(k1_wellord2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3789,c_7892])).

cnf(c_8390,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | r2_hidden(sK2,sK3) != iProver_top
    | v2_wellord1(k1_wellord2(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7899,c_1853])).

cnf(c_8400,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | sK3 = sK2
    | r2_hidden(sK3,sK2) = iProver_top
    | v2_wellord1(k1_wellord2(sK3)) != iProver_top
    | v3_ordinal1(sK3) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_792,c_8390])).

cnf(c_8404,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | sK3 = sK2
    | r2_hidden(sK3,sK3) = iProver_top
    | v2_wellord1(k1_wellord2(sK3)) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4355,c_8390])).

cnf(c_8441,plain,
    ( v2_wellord1(k1_wellord2(sK3)) != iProver_top
    | r2_hidden(sK3,sK3) = iProver_top
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8404,c_26,c_28,c_23,c_78,c_84,c_91,c_1082])).

cnf(c_8442,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | r2_hidden(sK3,sK3) = iProver_top
    | v2_wellord1(k1_wellord2(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8441])).

cnf(c_8448,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | r2_hidden(sK3,sK3) = iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_778,c_8442])).

cnf(c_8403,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK3) = sK3
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | sK3 = sK2
    | v2_wellord1(k1_wellord2(sK3)) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6378,c_8390])).

cnf(c_2450,plain,
    ( ~ r2_hidden(sK3,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK3)
    | k1_wellord1(k1_wellord2(X0),sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_4062,plain,
    ( ~ r2_hidden(sK3,sK3)
    | ~ v3_ordinal1(sK3)
    | k1_wellord1(k1_wellord2(sK3),sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_2450])).

cnf(c_4066,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK3) = sK3
    | r2_hidden(sK3,sK3) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4062])).

cnf(c_8667,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | k1_wellord1(k1_wellord2(sK3),sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8403,c_28,c_4066,c_8448])).

cnf(c_8668,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK3) = sK3
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
    inference(renaming,[status(thm)],[c_8667])).

cnf(c_8671,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK3)) != iProver_top
    | r2_hidden(sK3,k3_relat_1(k1_wellord2(sK3))) != iProver_top
    | v2_wellord1(k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8668,c_787])).

cnf(c_8672,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK3)) != iProver_top
    | r2_hidden(sK3,sK3) != iProver_top
    | v2_wellord1(k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8671,c_186,c_1277])).

cnf(c_8675,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | v2_wellord1(k1_wellord2(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8400,c_28,c_29,c_41,c_1853,c_1910,c_2072,c_8448,c_8672])).

cnf(c_8681,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_778,c_8675])).

cnf(c_8878,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8681,c_28])).

cnf(c_8887,plain,
    ( r2_hidden(X0,k3_relat_1(k1_wellord2(sK3))) != iProver_top
    | r2_hidden(X0,k3_relat_1(k1_wellord2(sK2))) = iProver_top
    | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8878,c_790])).

cnf(c_8923,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK2) = iProver_top
    | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8887,c_186])).

cnf(c_9105,plain,
    ( r2_hidden(X0,sK2) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8923,c_41])).

cnf(c_9106,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_9105])).

cnf(c_9115,plain,
    ( k1_wellord1(k1_wellord2(X0),sK3) = sK3
    | sK3 = X0
    | r2_hidden(X0,sK2) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2282,c_9106])).

cnf(c_10759,plain,
    ( v3_ordinal1(X0) != iProver_top
    | r2_hidden(X0,sK2) = iProver_top
    | sK3 = X0
    | k1_wellord1(k1_wellord2(X0),sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9115,c_28])).

cnf(c_10760,plain,
    ( k1_wellord1(k1_wellord2(X0),sK3) = sK3
    | sK3 = X0
    | r2_hidden(X0,sK2) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10759])).

cnf(c_9116,plain,
    ( sK3 = X0
    | r2_hidden(X0,sK2) = iProver_top
    | r2_hidden(sK3,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_792,c_9106])).

cnf(c_9178,plain,
    ( v3_ordinal1(X0) != iProver_top
    | r2_hidden(sK3,X0) = iProver_top
    | r2_hidden(X0,sK2) = iProver_top
    | sK3 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9116,c_28])).

cnf(c_9179,plain,
    ( sK3 = X0
    | r2_hidden(X0,sK2) = iProver_top
    | r2_hidden(sK3,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_9178])).

cnf(c_9192,plain,
    ( k1_wellord1(k1_wellord2(sK2),X0) = X0
    | sK3 = X0
    | r2_hidden(sK3,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9179,c_779])).

cnf(c_9564,plain,
    ( v3_ordinal1(X0) != iProver_top
    | r2_hidden(sK3,X0) = iProver_top
    | sK3 = X0
    | k1_wellord1(k1_wellord2(sK2),X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9192,c_27])).

cnf(c_9565,plain,
    ( k1_wellord1(k1_wellord2(sK2),X0) = X0
    | sK3 = X0
    | r2_hidden(sK3,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_9564])).

cnf(c_9572,plain,
    ( k1_wellord1(k1_wellord2(X0),sK3) = sK3
    | k1_wellord1(k1_wellord2(sK2),X0) = X0
    | sK3 = X0
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_9565,c_779])).

cnf(c_9616,plain,
    ( v3_ordinal1(X0) != iProver_top
    | sK3 = X0
    | k1_wellord1(k1_wellord2(sK2),X0) = X0
    | k1_wellord1(k1_wellord2(X0),sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9572,c_28])).

cnf(c_9617,plain,
    ( k1_wellord1(k1_wellord2(X0),sK3) = sK3
    | k1_wellord1(k1_wellord2(sK2),X0) = X0
    | sK3 = X0
    | v3_ordinal1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_9616])).

cnf(c_9627,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | k1_wellord1(k1_wellord2(sK2),sK2) = sK2
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_774,c_9617])).

cnf(c_9619,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | k1_wellord1(k1_wellord2(sK2),sK2) = sK2
    | sK3 = sK2
    | v3_ordinal1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9617])).

cnf(c_9950,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK2) = sK2
    | k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9627,c_26,c_27,c_23,c_78,c_84,c_91,c_1082,c_9619])).

cnf(c_9951,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | k1_wellord1(k1_wellord2(sK2),sK2) = sK2 ),
    inference(renaming,[status(thm)],[c_9950])).

cnf(c_9954,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK2) = sK2
    | r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top
    | r2_hidden(sK3,k3_relat_1(k1_wellord2(sK2))) != iProver_top
    | v2_wellord1(k1_wellord2(sK2)) != iProver_top
    | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9951,c_787])).

cnf(c_9955,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK2) = sK2
    | r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) != iProver_top
    | r2_hidden(sK3,k3_relat_1(k1_wellord2(sK2))) != iProver_top
    | v2_wellord1(k1_wellord2(sK2)) != iProver_top
    | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9954,c_8878])).

cnf(c_9956,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK2) = sK2
    | r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) != iProver_top
    | r2_hidden(sK3,sK2) != iProver_top
    | v2_wellord1(k1_wellord2(sK2)) != iProver_top
    | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9955,c_186])).

cnf(c_34,plain,
    ( v2_wellord1(k1_wellord2(sK2))
    | ~ v3_ordinal1(sK2) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_40,plain,
    ( v1_relat_1(k1_wellord2(sK2)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_9242,plain,
    ( r2_hidden(sK3,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK2)
    | k1_wellord1(k1_wellord2(sK2),X0) = X0
    | sK3 = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9192])).

cnf(c_9244,plain,
    ( r2_hidden(sK3,sK2)
    | ~ v3_ordinal1(sK2)
    | k1_wellord1(k1_wellord2(sK2),sK2) = sK2
    | sK3 = sK2 ),
    inference(instantiation,[status(thm)],[c_9242])).

cnf(c_9957,plain,
    ( ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
    | ~ r2_hidden(sK3,sK2)
    | ~ v2_wellord1(k1_wellord2(sK2))
    | ~ v1_relat_1(k1_wellord2(sK2))
    | k1_wellord1(k1_wellord2(sK2),sK2) = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9956])).

cnf(c_9959,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9956,c_26,c_24,c_23,c_34,c_40,c_78,c_84,c_91,c_1082,c_9244,c_9957])).

cnf(c_9962,plain,
    ( r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK2)) != iProver_top
    | r2_hidden(sK2,k3_relat_1(k1_wellord2(sK2))) != iProver_top
    | v2_wellord1(k1_wellord2(sK2)) != iProver_top
    | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9959,c_787])).

cnf(c_9963,plain,
    ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK2)) != iProver_top
    | r2_hidden(sK2,sK2) != iProver_top
    | v2_wellord1(k1_wellord2(sK2)) != iProver_top
    | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9962,c_186,c_1277])).

cnf(c_33,plain,
    ( v2_wellord1(k1_wellord2(X0)) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_35,plain,
    ( v2_wellord1(k1_wellord2(sK2)) = iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_1903,plain,
    ( ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(sK3))
    | r4_wellord1(k1_wellord2(X0),k1_wellord2(sK2))
    | ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2))
    | ~ v1_relat_1(k1_wellord2(X0))
    | ~ v1_relat_1(k1_wellord2(sK3))
    | ~ v1_relat_1(k1_wellord2(sK2)) ),
    inference(instantiation,[status(thm)],[c_1313])).

cnf(c_1904,plain,
    ( r4_wellord1(k1_wellord2(X0),k1_wellord2(sK3)) != iProver_top
    | r4_wellord1(k1_wellord2(X0),k1_wellord2(sK2)) = iProver_top
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) != iProver_top
    | v1_relat_1(k1_wellord2(X0)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1903])).

cnf(c_1906,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) != iProver_top
    | r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) != iProver_top
    | r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK2)) = iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1904])).

cnf(c_10240,plain,
    ( r2_hidden(sK2,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9963,c_27,c_29,c_35,c_41,c_1853,c_1906,c_2072])).

cnf(c_10771,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | sK3 = sK2
    | v3_ordinal1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_10760,c_10240])).

cnf(c_9165,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | sK3 = sK2
    | r2_hidden(sK2,sK2) = iProver_top
    | v3_ordinal1(sK3) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9115])).

cnf(c_10793,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10771,c_26,c_27,c_28,c_29,c_23,c_35,c_41,c_78,c_84,c_91,c_1082,c_1853,c_1906,c_2072,c_9165,c_9963])).

cnf(c_10796,plain,
    ( r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top
    | r2_hidden(sK3,k3_relat_1(k1_wellord2(sK2))) != iProver_top
    | v2_wellord1(k1_wellord2(sK2)) != iProver_top
    | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10793,c_787])).

cnf(c_10797,plain,
    ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) != iProver_top
    | r2_hidden(sK3,k3_relat_1(k1_wellord2(sK2))) != iProver_top
    | v2_wellord1(k1_wellord2(sK2)) != iProver_top
    | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10796,c_8878])).

cnf(c_10798,plain,
    ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) != iProver_top
    | r2_hidden(sK3,sK2) != iProver_top
    | v2_wellord1(k1_wellord2(sK2)) != iProver_top
    | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10797,c_186])).

cnf(c_9181,plain,
    ( sK3 = sK2
    | r2_hidden(sK3,sK2) = iProver_top
    | r2_hidden(sK2,sK2) = iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9179])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10798,c_9963,c_9181,c_2072,c_1906,c_1853,c_1082,c_91,c_84,c_78,c_41,c_35,c_23,c_29,c_27,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:31:35 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.61/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.61/0.99  
% 3.61/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.61/0.99  
% 3.61/0.99  ------  iProver source info
% 3.61/0.99  
% 3.61/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.61/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.61/0.99  git: non_committed_changes: false
% 3.61/0.99  git: last_make_outside_of_git: false
% 3.61/0.99  
% 3.61/0.99  ------ 
% 3.61/0.99  ------ Parsing...
% 3.61/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.61/0.99  
% 3.61/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.61/0.99  
% 3.61/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.61/0.99  
% 3.61/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.61/0.99  ------ Proving...
% 3.61/0.99  ------ Problem Properties 
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  clauses                                 26
% 3.61/0.99  conjectures                             4
% 3.61/0.99  EPR                                     11
% 3.61/0.99  Horn                                    21
% 3.61/0.99  unary                                   7
% 3.61/0.99  binary                                  2
% 3.61/0.99  lits                                    79
% 3.61/0.99  lits eq                                 10
% 3.61/0.99  fd_pure                                 0
% 3.61/0.99  fd_pseudo                               0
% 3.61/0.99  fd_cond                                 0
% 3.61/0.99  fd_pseudo_cond                          2
% 3.61/0.99  AC symbols                              0
% 3.61/0.99  
% 3.61/0.99  ------ Input Options Time Limit: Unbounded
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  ------ 
% 3.61/0.99  Current options:
% 3.61/0.99  ------ 
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  ------ Proving...
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  % SZS status Theorem for theBenchmark.p
% 3.61/0.99  
% 3.61/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.61/0.99  
% 3.61/0.99  fof(f4,axiom,(
% 3.61/0.99    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 3.61/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f20,plain,(
% 3.61/0.99    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.61/0.99    inference(ennf_transformation,[],[f4])).
% 3.61/0.99  
% 3.61/0.99  fof(f21,plain,(
% 3.61/0.99    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.61/0.99    inference(flattening,[],[f20])).
% 3.61/0.99  
% 3.61/0.99  fof(f55,plain,(
% 3.61/0.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f21])).
% 3.61/0.99  
% 3.61/0.99  fof(f11,axiom,(
% 3.61/0.99    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => k1_wellord1(k1_wellord2(X1),X0) = X0)))),
% 3.61/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f32,plain,(
% 3.61/0.99    ! [X0] : (! [X1] : ((k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.61/0.99    inference(ennf_transformation,[],[f11])).
% 3.61/0.99  
% 3.61/0.99  fof(f33,plain,(
% 3.61/0.99    ! [X0] : (! [X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.61/0.99    inference(flattening,[],[f32])).
% 3.61/0.99  
% 3.61/0.99  fof(f69,plain,(
% 3.61/0.99    ( ! [X0,X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f33])).
% 3.61/0.99  
% 3.61/0.99  fof(f12,axiom,(
% 3.61/0.99    ! [X0] : (v3_ordinal1(X0) => v2_wellord1(k1_wellord2(X0)))),
% 3.61/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f34,plain,(
% 3.61/0.99    ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0))),
% 3.61/0.99    inference(ennf_transformation,[],[f12])).
% 3.61/0.99  
% 3.61/0.99  fof(f70,plain,(
% 3.61/0.99    ( ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f34])).
% 3.61/0.99  
% 3.61/0.99  fof(f14,conjecture,(
% 3.61/0.99    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 3.61/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f15,negated_conjecture,(
% 3.61/0.99    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 3.61/0.99    inference(negated_conjecture,[],[f14])).
% 3.61/0.99  
% 3.61/0.99  fof(f36,plain,(
% 3.61/0.99    ? [X0] : (? [X1] : ((X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.61/0.99    inference(ennf_transformation,[],[f15])).
% 3.61/0.99  
% 3.61/0.99  fof(f37,plain,(
% 3.61/0.99    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.61/0.99    inference(flattening,[],[f36])).
% 3.61/0.99  
% 3.61/0.99  fof(f47,plain,(
% 3.61/0.99    ( ! [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) => (sK3 != X0 & r4_wellord1(k1_wellord2(X0),k1_wellord2(sK3)) & v3_ordinal1(sK3))) )),
% 3.61/0.99    introduced(choice_axiom,[])).
% 3.61/0.99  
% 3.61/0.99  fof(f46,plain,(
% 3.61/0.99    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : (sK2 != X1 & r4_wellord1(k1_wellord2(sK2),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK2))),
% 3.61/0.99    introduced(choice_axiom,[])).
% 3.61/0.99  
% 3.61/0.99  fof(f48,plain,(
% 3.61/0.99    (sK2 != sK3 & r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) & v3_ordinal1(sK3)) & v3_ordinal1(sK2)),
% 3.61/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f37,f47,f46])).
% 3.61/0.99  
% 3.61/0.99  fof(f72,plain,(
% 3.61/0.99    v3_ordinal1(sK2)),
% 3.61/0.99    inference(cnf_transformation,[],[f48])).
% 3.61/0.99  
% 3.61/0.99  fof(f73,plain,(
% 3.61/0.99    v3_ordinal1(sK3)),
% 3.61/0.99    inference(cnf_transformation,[],[f48])).
% 3.61/0.99  
% 3.61/0.99  fof(f2,axiom,(
% 3.61/0.99    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 3.61/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f16,plain,(
% 3.61/0.99    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 3.61/0.99    inference(ennf_transformation,[],[f2])).
% 3.61/0.99  
% 3.61/0.99  fof(f17,plain,(
% 3.61/0.99    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.61/0.99    inference(flattening,[],[f16])).
% 3.61/0.99  
% 3.61/0.99  fof(f52,plain,(
% 3.61/0.99    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f17])).
% 3.61/0.99  
% 3.61/0.99  fof(f3,axiom,(
% 3.61/0.99    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 3.61/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f18,plain,(
% 3.61/0.99    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 3.61/0.99    inference(ennf_transformation,[],[f3])).
% 3.61/0.99  
% 3.61/0.99  fof(f19,plain,(
% 3.61/0.99    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.61/0.99    inference(flattening,[],[f18])).
% 3.61/0.99  
% 3.61/0.99  fof(f40,plain,(
% 3.61/0.99    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.61/0.99    inference(nnf_transformation,[],[f19])).
% 3.61/0.99  
% 3.61/0.99  fof(f53,plain,(
% 3.61/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f40])).
% 3.61/0.99  
% 3.61/0.99  fof(f13,axiom,(
% 3.61/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0))),
% 3.61/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f35,plain,(
% 3.61/0.99    ! [X0,X1] : (k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) | ~r1_tarski(X0,X1))),
% 3.61/0.99    inference(ennf_transformation,[],[f13])).
% 3.61/0.99  
% 3.61/0.99  fof(f71,plain,(
% 3.61/0.99    ( ! [X0,X1] : (k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) | ~r1_tarski(X0,X1)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f35])).
% 3.61/0.99  
% 3.61/0.99  fof(f5,axiom,(
% 3.61/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) => (r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2)))))),
% 3.61/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f22,plain,(
% 3.61/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.61/0.99    inference(ennf_transformation,[],[f5])).
% 3.61/0.99  
% 3.61/0.99  fof(f23,plain,(
% 3.61/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | ~v1_relat_1(X2))),
% 3.61/0.99    inference(flattening,[],[f22])).
% 3.61/0.99  
% 3.61/0.99  fof(f56,plain,(
% 3.61/0.99    ( ! [X2,X0,X1] : (r2_hidden(X0,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | ~v1_relat_1(X2)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f23])).
% 3.61/0.99  
% 3.61/0.99  fof(f9,axiom,(
% 3.61/0.99    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 3.61/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f30,plain,(
% 3.61/0.99    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 3.61/0.99    inference(ennf_transformation,[],[f9])).
% 3.61/0.99  
% 3.61/0.99  fof(f31,plain,(
% 3.61/0.99    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 3.61/0.99    inference(flattening,[],[f30])).
% 3.61/0.99  
% 3.61/0.99  fof(f41,plain,(
% 3.61/0.99    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 3.61/0.99    inference(nnf_transformation,[],[f31])).
% 3.61/0.99  
% 3.61/0.99  fof(f42,plain,(
% 3.61/0.99    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 3.61/0.99    inference(flattening,[],[f41])).
% 3.61/0.99  
% 3.61/0.99  fof(f43,plain,(
% 3.61/0.99    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 3.61/0.99    inference(rectify,[],[f42])).
% 3.61/0.99  
% 3.61/0.99  fof(f44,plain,(
% 3.61/0.99    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK0(X0,X1),sK1(X0,X1)) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & (r1_tarski(sK0(X0,X1),sK1(X0,X1)) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & r2_hidden(sK1(X0,X1),X0) & r2_hidden(sK0(X0,X1),X0)))),
% 3.61/0.99    introduced(choice_axiom,[])).
% 3.61/0.99  
% 3.61/0.99  fof(f45,plain,(
% 3.61/0.99    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK0(X0,X1),sK1(X0,X1)) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & (r1_tarski(sK0(X0,X1),sK1(X0,X1)) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & r2_hidden(sK1(X0,X1),X0) & r2_hidden(sK0(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 3.61/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f43,f44])).
% 3.61/0.99  
% 3.61/0.99  fof(f61,plain,(
% 3.61/0.99    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f45])).
% 3.61/0.99  
% 3.61/0.99  fof(f84,plain,(
% 3.61/0.99    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 3.61/0.99    inference(equality_resolution,[],[f61])).
% 3.61/0.99  
% 3.61/0.99  fof(f10,axiom,(
% 3.61/0.99    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 3.61/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f68,plain,(
% 3.61/0.99    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 3.61/0.99    inference(cnf_transformation,[],[f10])).
% 3.61/0.99  
% 3.61/0.99  fof(f75,plain,(
% 3.61/0.99    sK2 != sK3),
% 3.61/0.99    inference(cnf_transformation,[],[f48])).
% 3.61/0.99  
% 3.61/0.99  fof(f1,axiom,(
% 3.61/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.61/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f38,plain,(
% 3.61/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.61/0.99    inference(nnf_transformation,[],[f1])).
% 3.61/0.99  
% 3.61/0.99  fof(f39,plain,(
% 3.61/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.61/0.99    inference(flattening,[],[f38])).
% 3.61/0.99  
% 3.61/0.99  fof(f51,plain,(
% 3.61/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f39])).
% 3.61/0.99  
% 3.61/0.99  fof(f8,axiom,(
% 3.61/0.99    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 3.61/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f28,plain,(
% 3.61/0.99    ! [X0] : ((! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 3.61/0.99    inference(ennf_transformation,[],[f8])).
% 3.61/0.99  
% 3.61/0.99  fof(f29,plain,(
% 3.61/0.99    ! [X0] : (! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 3.61/0.99    inference(flattening,[],[f28])).
% 3.61/0.99  
% 3.61/0.99  fof(f60,plain,(
% 3.61/0.99    ( ! [X0,X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0)) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f29])).
% 3.61/0.99  
% 3.61/0.99  fof(f49,plain,(
% 3.61/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.61/0.99    inference(cnf_transformation,[],[f39])).
% 3.61/0.99  
% 3.61/0.99  fof(f77,plain,(
% 3.61/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.61/0.99    inference(equality_resolution,[],[f49])).
% 3.61/0.99  
% 3.61/0.99  fof(f74,plain,(
% 3.61/0.99    r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))),
% 3.61/0.99    inference(cnf_transformation,[],[f48])).
% 3.61/0.99  
% 3.61/0.99  fof(f6,axiom,(
% 3.61/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 3.61/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f24,plain,(
% 3.61/0.99    ! [X0] : (! [X1] : ((r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.61/0.99    inference(ennf_transformation,[],[f6])).
% 3.61/0.99  
% 3.61/0.99  fof(f25,plain,(
% 3.61/0.99    ! [X0] : (! [X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.61/0.99    inference(flattening,[],[f24])).
% 3.61/0.99  
% 3.61/0.99  fof(f58,plain,(
% 3.61/0.99    ( ! [X0,X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f25])).
% 3.61/0.99  
% 3.61/0.99  fof(f7,axiom,(
% 3.61/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ((r4_wellord1(X1,X2) & r4_wellord1(X0,X1)) => r4_wellord1(X0,X2)))))),
% 3.61/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f26,plain,(
% 3.61/0.99    ! [X0] : (! [X1] : (! [X2] : ((r4_wellord1(X0,X2) | (~r4_wellord1(X1,X2) | ~r4_wellord1(X0,X1))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.61/0.99    inference(ennf_transformation,[],[f7])).
% 3.61/0.99  
% 3.61/0.99  fof(f27,plain,(
% 3.61/0.99    ! [X0] : (! [X1] : (! [X2] : (r4_wellord1(X0,X2) | ~r4_wellord1(X1,X2) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.61/0.99    inference(flattening,[],[f26])).
% 3.61/0.99  
% 3.61/0.99  fof(f59,plain,(
% 3.61/0.99    ( ! [X2,X0,X1] : (r4_wellord1(X0,X2) | ~r4_wellord1(X1,X2) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f27])).
% 3.61/0.99  
% 3.61/0.99  cnf(c_6,plain,
% 3.61/0.99      ( r2_hidden(X0,X1)
% 3.61/0.99      | r2_hidden(X1,X0)
% 3.61/0.99      | ~ v3_ordinal1(X1)
% 3.61/0.99      | ~ v3_ordinal1(X0)
% 3.61/0.99      | X1 = X0 ),
% 3.61/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_792,plain,
% 3.61/0.99      ( X0 = X1
% 3.61/0.99      | r2_hidden(X1,X0) = iProver_top
% 3.61/0.99      | r2_hidden(X0,X1) = iProver_top
% 3.61/0.99      | v3_ordinal1(X1) != iProver_top
% 3.61/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_20,plain,
% 3.61/0.99      ( ~ r2_hidden(X0,X1)
% 3.61/0.99      | ~ v3_ordinal1(X1)
% 3.61/0.99      | ~ v3_ordinal1(X0)
% 3.61/0.99      | k1_wellord1(k1_wellord2(X1),X0) = X0 ),
% 3.61/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_779,plain,
% 3.61/0.99      ( k1_wellord1(k1_wellord2(X0),X1) = X1
% 3.61/0.99      | r2_hidden(X1,X0) != iProver_top
% 3.61/0.99      | v3_ordinal1(X1) != iProver_top
% 3.61/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2282,plain,
% 3.61/0.99      ( X0 = X1
% 3.61/0.99      | k1_wellord1(k1_wellord2(X1),X0) = X0
% 3.61/0.99      | r2_hidden(X1,X0) = iProver_top
% 3.61/0.99      | v3_ordinal1(X1) != iProver_top
% 3.61/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_792,c_779]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_21,plain,
% 3.61/0.99      ( v2_wellord1(k1_wellord2(X0)) | ~ v3_ordinal1(X0) ),
% 3.61/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_778,plain,
% 3.61/0.99      ( v2_wellord1(k1_wellord2(X0)) = iProver_top
% 3.61/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_26,negated_conjecture,
% 3.61/0.99      ( v3_ordinal1(sK2) ),
% 3.61/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_774,plain,
% 3.61/0.99      ( v3_ordinal1(sK2) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_25,negated_conjecture,
% 3.61/0.99      ( v3_ordinal1(sK3) ),
% 3.61/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_775,plain,
% 3.61/0.99      ( v3_ordinal1(sK3) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3,plain,
% 3.61/0.99      ( r1_ordinal1(X0,X1)
% 3.61/0.99      | r1_ordinal1(X1,X0)
% 3.61/0.99      | ~ v3_ordinal1(X1)
% 3.61/0.99      | ~ v3_ordinal1(X0) ),
% 3.61/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_795,plain,
% 3.61/0.99      ( r1_ordinal1(X0,X1) = iProver_top
% 3.61/0.99      | r1_ordinal1(X1,X0) = iProver_top
% 3.61/0.99      | v3_ordinal1(X0) != iProver_top
% 3.61/0.99      | v3_ordinal1(X1) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_5,plain,
% 3.61/0.99      ( ~ r1_ordinal1(X0,X1)
% 3.61/0.99      | r1_tarski(X0,X1)
% 3.61/0.99      | ~ v3_ordinal1(X1)
% 3.61/0.99      | ~ v3_ordinal1(X0) ),
% 3.61/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_793,plain,
% 3.61/0.99      ( r1_ordinal1(X0,X1) != iProver_top
% 3.61/0.99      | r1_tarski(X0,X1) = iProver_top
% 3.61/0.99      | v3_ordinal1(X0) != iProver_top
% 3.61/0.99      | v3_ordinal1(X1) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2151,plain,
% 3.61/0.99      ( r1_ordinal1(X0,X1) = iProver_top
% 3.61/0.99      | r1_tarski(X1,X0) = iProver_top
% 3.61/0.99      | v3_ordinal1(X0) != iProver_top
% 3.61/0.99      | v3_ordinal1(X1) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_795,c_793]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3300,plain,
% 3.61/0.99      ( r1_tarski(X0,X1) = iProver_top
% 3.61/0.99      | r1_tarski(X1,X0) = iProver_top
% 3.61/0.99      | v3_ordinal1(X0) != iProver_top
% 3.61/0.99      | v3_ordinal1(X1) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_2151,c_793]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_22,plain,
% 3.61/0.99      ( ~ r1_tarski(X0,X1)
% 3.61/0.99      | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ),
% 3.61/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_777,plain,
% 3.61/0.99      ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 3.61/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3310,plain,
% 3.61/0.99      ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 3.61/0.99      | r1_tarski(X0,X1) = iProver_top
% 3.61/0.99      | v3_ordinal1(X0) != iProver_top
% 3.61/0.99      | v3_ordinal1(X1) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_3300,c_777]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3459,plain,
% 3.61/0.99      ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 3.61/0.99      | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
% 3.61/0.99      | v3_ordinal1(X1) != iProver_top
% 3.61/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_3310,c_777]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3640,plain,
% 3.61/0.99      ( k2_wellord1(k1_wellord2(X0),sK3) = k1_wellord2(sK3)
% 3.61/0.99      | k2_wellord1(k1_wellord2(sK3),X0) = k1_wellord2(X0)
% 3.61/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_775,c_3459]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3789,plain,
% 3.61/0.99      ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
% 3.61/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_774,c_3640]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_8,plain,
% 3.61/0.99      ( r2_hidden(X0,k3_relat_1(X1))
% 3.61/0.99      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X1,X2)))
% 3.61/0.99      | ~ v1_relat_1(X1) ),
% 3.61/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_790,plain,
% 3.61/0.99      ( r2_hidden(X0,k3_relat_1(X1)) = iProver_top
% 3.61/0.99      | r2_hidden(X0,k3_relat_1(k2_wellord1(X1,X2))) != iProver_top
% 3.61/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3798,plain,
% 3.61/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.61/0.99      | r2_hidden(X0,k3_relat_1(k1_wellord2(sK3))) = iProver_top
% 3.61/0.99      | r2_hidden(X0,k3_relat_1(k1_wellord2(sK2))) != iProver_top
% 3.61/0.99      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_3789,c_790]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_18,plain,
% 3.61/0.99      ( ~ v1_relat_1(k1_wellord2(X0))
% 3.61/0.99      | k3_relat_1(k1_wellord2(X0)) = X0 ),
% 3.61/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_19,plain,
% 3.61/0.99      ( v1_relat_1(k1_wellord2(X0)) ),
% 3.61/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_186,plain,
% 3.61/0.99      ( k3_relat_1(k1_wellord2(X0)) = X0 ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_18,c_19]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3816,plain,
% 3.61/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.61/0.99      | r2_hidden(X0,sK3) = iProver_top
% 3.61/0.99      | r2_hidden(X0,sK2) != iProver_top
% 3.61/0.99      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_3798,c_186]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2071,plain,
% 3.61/0.99      ( v1_relat_1(k1_wellord2(sK3)) ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2072,plain,
% 3.61/0.99      ( v1_relat_1(k1_wellord2(sK3)) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_2071]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3957,plain,
% 3.61/0.99      ( r2_hidden(X0,sK2) != iProver_top
% 3.61/0.99      | r2_hidden(X0,sK3) = iProver_top
% 3.61/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_3816,c_2072]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3958,plain,
% 3.61/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.61/0.99      | r2_hidden(X0,sK3) = iProver_top
% 3.61/0.99      | r2_hidden(X0,sK2) != iProver_top ),
% 3.61/0.99      inference(renaming,[status(thm)],[c_3957]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3966,plain,
% 3.61/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.61/0.99      | sK2 = X0
% 3.61/0.99      | r2_hidden(X0,sK3) = iProver_top
% 3.61/0.99      | r2_hidden(sK2,X0) = iProver_top
% 3.61/0.99      | v3_ordinal1(X0) != iProver_top
% 3.61/0.99      | v3_ordinal1(sK2) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_792,c_3958]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_27,plain,
% 3.61/0.99      ( v3_ordinal1(sK2) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4354,plain,
% 3.61/0.99      ( v3_ordinal1(X0) != iProver_top
% 3.61/0.99      | r2_hidden(sK2,X0) = iProver_top
% 3.61/0.99      | r2_hidden(X0,sK3) = iProver_top
% 3.61/0.99      | sK2 = X0
% 3.61/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_3966,c_27]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4355,plain,
% 3.61/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.61/0.99      | sK2 = X0
% 3.61/0.99      | r2_hidden(X0,sK3) = iProver_top
% 3.61/0.99      | r2_hidden(sK2,X0) = iProver_top
% 3.61/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.61/0.99      inference(renaming,[status(thm)],[c_4354]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4363,plain,
% 3.61/0.99      ( k1_wellord1(k1_wellord2(X0),sK2) = sK2
% 3.61/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.61/0.99      | sK2 = X0
% 3.61/0.99      | r2_hidden(X0,sK3) = iProver_top
% 3.61/0.99      | v3_ordinal1(X0) != iProver_top
% 3.61/0.99      | v3_ordinal1(sK2) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_4355,c_779]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_6337,plain,
% 3.61/0.99      ( v3_ordinal1(X0) != iProver_top
% 3.61/0.99      | r2_hidden(X0,sK3) = iProver_top
% 3.61/0.99      | sK2 = X0
% 3.61/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.61/0.99      | k1_wellord1(k1_wellord2(X0),sK2) = sK2 ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_4363,c_27]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_6338,plain,
% 3.61/0.99      ( k1_wellord1(k1_wellord2(X0),sK2) = sK2
% 3.61/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.61/0.99      | sK2 = X0
% 3.61/0.99      | r2_hidden(X0,sK3) = iProver_top
% 3.61/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.61/0.99      inference(renaming,[status(thm)],[c_6337]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_6346,plain,
% 3.61/0.99      ( k1_wellord1(k1_wellord2(X0),sK2) = sK2
% 3.61/0.99      | k1_wellord1(k1_wellord2(sK3),X0) = X0
% 3.61/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.61/0.99      | sK2 = X0
% 3.61/0.99      | v3_ordinal1(X0) != iProver_top
% 3.61/0.99      | v3_ordinal1(sK3) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_6338,c_779]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4367,plain,
% 3.61/0.99      ( k1_wellord1(k1_wellord2(sK3),X0) = X0
% 3.61/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.61/0.99      | sK2 = X0
% 3.61/0.99      | r2_hidden(sK2,X0) = iProver_top
% 3.61/0.99      | v3_ordinal1(X0) != iProver_top
% 3.61/0.99      | v3_ordinal1(sK3) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_4355,c_779]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_28,plain,
% 3.61/0.99      ( v3_ordinal1(sK3) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_6377,plain,
% 3.61/0.99      ( v3_ordinal1(X0) != iProver_top
% 3.61/0.99      | r2_hidden(sK2,X0) = iProver_top
% 3.61/0.99      | sK2 = X0
% 3.61/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.61/0.99      | k1_wellord1(k1_wellord2(sK3),X0) = X0 ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_4367,c_28]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_6378,plain,
% 3.61/0.99      ( k1_wellord1(k1_wellord2(sK3),X0) = X0
% 3.61/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.61/0.99      | sK2 = X0
% 3.61/0.99      | r2_hidden(sK2,X0) = iProver_top
% 3.61/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.61/0.99      inference(renaming,[status(thm)],[c_6377]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_6386,plain,
% 3.61/0.99      ( k1_wellord1(k1_wellord2(X0),sK2) = sK2
% 3.61/0.99      | k1_wellord1(k1_wellord2(sK3),X0) = X0
% 3.61/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.61/0.99      | sK2 = X0
% 3.61/0.99      | v3_ordinal1(X0) != iProver_top
% 3.61/0.99      | v3_ordinal1(sK2) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_6378,c_779]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_6672,plain,
% 3.61/0.99      ( v3_ordinal1(X0) != iProver_top
% 3.61/0.99      | sK2 = X0
% 3.61/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.61/0.99      | k1_wellord1(k1_wellord2(sK3),X0) = X0
% 3.61/0.99      | k1_wellord1(k1_wellord2(X0),sK2) = sK2 ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_6346,c_27,c_6386]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_6673,plain,
% 3.61/0.99      ( k1_wellord1(k1_wellord2(X0),sK2) = sK2
% 3.61/0.99      | k1_wellord1(k1_wellord2(sK3),X0) = X0
% 3.61/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.61/0.99      | sK2 = X0
% 3.61/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.61/0.99      inference(renaming,[status(thm)],[c_6672]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_6681,plain,
% 3.61/0.99      ( k1_wellord1(k1_wellord2(sK3),sK3) = sK3
% 3.61/0.99      | k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.61/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.61/0.99      | sK3 = sK2 ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_775,c_6673]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_23,negated_conjecture,
% 3.61/0.99      ( sK2 != sK3 ),
% 3.61/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_78,plain,
% 3.61/0.99      ( ~ r1_ordinal1(sK2,sK2)
% 3.61/0.99      | r1_tarski(sK2,sK2)
% 3.61/0.99      | ~ v3_ordinal1(sK2) ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_84,plain,
% 3.61/0.99      ( r1_ordinal1(sK2,sK2) | ~ v3_ordinal1(sK2) ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_0,plain,
% 3.61/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.61/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_91,plain,
% 3.61/0.99      ( ~ r1_tarski(sK2,sK2) | sK2 = sK2 ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_357,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1081,plain,
% 3.61/0.99      ( sK3 != X0 | sK2 != X0 | sK2 = sK3 ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_357]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1082,plain,
% 3.61/0.99      ( sK3 != sK2 | sK2 = sK3 | sK2 != sK2 ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_1081]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_6852,plain,
% 3.61/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.61/0.99      | k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.61/0.99      | k1_wellord1(k1_wellord2(sK3),sK3) = sK3 ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_6681,c_26,c_23,c_78,c_84,c_91,c_1082]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_6853,plain,
% 3.61/0.99      ( k1_wellord1(k1_wellord2(sK3),sK3) = sK3
% 3.61/0.99      | k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.61/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
% 3.61/0.99      inference(renaming,[status(thm)],[c_6852]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_11,plain,
% 3.61/0.99      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
% 3.61/0.99      | ~ r2_hidden(X1,k3_relat_1(X0))
% 3.61/0.99      | ~ v2_wellord1(X0)
% 3.61/0.99      | ~ v1_relat_1(X0) ),
% 3.61/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_787,plain,
% 3.61/0.99      ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) != iProver_top
% 3.61/0.99      | r2_hidden(X1,k3_relat_1(X0)) != iProver_top
% 3.61/0.99      | v2_wellord1(X0) != iProver_top
% 3.61/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_6857,plain,
% 3.61/0.99      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.61/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.61/0.99      | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK3)) != iProver_top
% 3.61/0.99      | r2_hidden(sK3,k3_relat_1(k1_wellord2(sK3))) != iProver_top
% 3.61/0.99      | v2_wellord1(k1_wellord2(sK3)) != iProver_top
% 3.61/0.99      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_6853,c_787]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2,plain,
% 3.61/0.99      ( r1_tarski(X0,X0) ),
% 3.61/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_796,plain,
% 3.61/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1277,plain,
% 3.61/0.99      ( k2_wellord1(k1_wellord2(X0),X0) = k1_wellord2(X0) ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_796,c_777]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_6858,plain,
% 3.61/0.99      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.61/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.61/0.99      | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK3)) != iProver_top
% 3.61/0.99      | r2_hidden(sK3,sK3) != iProver_top
% 3.61/0.99      | v2_wellord1(k1_wellord2(sK3)) != iProver_top
% 3.61/0.99      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_6857,c_186,c_1277]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_24,negated_conjecture,
% 3.61/0.99      ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) ),
% 3.61/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_29,plain,
% 3.61/0.99      ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_39,plain,
% 3.61/0.99      ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_41,plain,
% 3.61/0.99      ( v1_relat_1(k1_wellord2(sK2)) = iProver_top ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_39]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_776,plain,
% 3.61/0.99      ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9,plain,
% 3.61/0.99      ( ~ r4_wellord1(X0,X1)
% 3.61/0.99      | r4_wellord1(X1,X0)
% 3.61/0.99      | ~ v1_relat_1(X1)
% 3.61/0.99      | ~ v1_relat_1(X0) ),
% 3.61/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_789,plain,
% 3.61/0.99      ( r4_wellord1(X0,X1) != iProver_top
% 3.61/0.99      | r4_wellord1(X1,X0) = iProver_top
% 3.61/0.99      | v1_relat_1(X0) != iProver_top
% 3.61/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1684,plain,
% 3.61/0.99      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top
% 3.61/0.99      | v1_relat_1(k1_wellord2(sK3)) != iProver_top
% 3.61/0.99      | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_776,c_789]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1847,plain,
% 3.61/0.99      ( v1_relat_1(k1_wellord2(sK3)) != iProver_top
% 3.61/0.99      | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_1684,c_41]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1848,plain,
% 3.61/0.99      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top
% 3.61/0.99      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 3.61/0.99      inference(renaming,[status(thm)],[c_1847]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_780,plain,
% 3.61/0.99      ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1853,plain,
% 3.61/0.99      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top ),
% 3.61/0.99      inference(forward_subsumption_resolution,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_1848,c_780]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_10,plain,
% 3.61/0.99      ( ~ r4_wellord1(X0,X1)
% 3.61/0.99      | ~ r4_wellord1(X1,X2)
% 3.61/0.99      | r4_wellord1(X0,X2)
% 3.61/0.99      | ~ v1_relat_1(X2)
% 3.61/0.99      | ~ v1_relat_1(X1)
% 3.61/0.99      | ~ v1_relat_1(X0) ),
% 3.61/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1126,plain,
% 3.61/0.99      ( ~ r4_wellord1(X0,X1)
% 3.61/0.99      | ~ r4_wellord1(k1_wellord2(X2),X0)
% 3.61/0.99      | r4_wellord1(k1_wellord2(X2),X1)
% 3.61/0.99      | ~ v1_relat_1(X1)
% 3.61/0.99      | ~ v1_relat_1(X0)
% 3.61/0.99      | ~ v1_relat_1(k1_wellord2(X2)) ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1313,plain,
% 3.61/0.99      ( ~ r4_wellord1(k1_wellord2(X0),X1)
% 3.61/0.99      | r4_wellord1(k1_wellord2(X2),X1)
% 3.61/0.99      | ~ r4_wellord1(k1_wellord2(X2),k1_wellord2(X0))
% 3.61/0.99      | ~ v1_relat_1(X1)
% 3.61/0.99      | ~ v1_relat_1(k1_wellord2(X0))
% 3.61/0.99      | ~ v1_relat_1(k1_wellord2(X2)) ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_1126]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1843,plain,
% 3.61/0.99      ( r4_wellord1(k1_wellord2(X0),k1_wellord2(sK3))
% 3.61/0.99      | ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(sK2))
% 3.61/0.99      | ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
% 3.61/0.99      | ~ v1_relat_1(k1_wellord2(X0))
% 3.61/0.99      | ~ v1_relat_1(k1_wellord2(sK3))
% 3.61/0.99      | ~ v1_relat_1(k1_wellord2(sK2)) ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_1313]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1909,plain,
% 3.61/0.99      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK3))
% 3.61/0.99      | ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2))
% 3.61/0.99      | ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
% 3.61/0.99      | ~ v1_relat_1(k1_wellord2(sK3))
% 3.61/0.99      | ~ v1_relat_1(k1_wellord2(sK2)) ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_1843]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1910,plain,
% 3.61/0.99      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK3)) = iProver_top
% 3.61/0.99      | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) != iProver_top
% 3.61/0.99      | r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) != iProver_top
% 3.61/0.99      | v1_relat_1(k1_wellord2(sK3)) != iProver_top
% 3.61/0.99      | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_1909]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_6861,plain,
% 3.61/0.99      ( v2_wellord1(k1_wellord2(sK3)) != iProver_top
% 3.61/0.99      | r2_hidden(sK3,sK3) != iProver_top
% 3.61/0.99      | k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.61/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_6858,c_29,c_41,c_1853,c_1910,c_2072]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_6862,plain,
% 3.61/0.99      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.61/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.61/0.99      | r2_hidden(sK3,sK3) != iProver_top
% 3.61/0.99      | v2_wellord1(k1_wellord2(sK3)) != iProver_top ),
% 3.61/0.99      inference(renaming,[status(thm)],[c_6861]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_6873,plain,
% 3.61/0.99      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.61/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.61/0.99      | sK3 = sK2
% 3.61/0.99      | v2_wellord1(k1_wellord2(sK3)) != iProver_top
% 3.61/0.99      | v3_ordinal1(sK3) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_6338,c_6862]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_7093,plain,
% 3.61/0.99      ( v2_wellord1(k1_wellord2(sK3)) != iProver_top
% 3.61/0.99      | k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.61/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_6873,c_26,c_28,c_23,c_78,c_84,c_91,c_1082]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_7094,plain,
% 3.61/0.99      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.61/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.61/0.99      | v2_wellord1(k1_wellord2(sK3)) != iProver_top ),
% 3.61/0.99      inference(renaming,[status(thm)],[c_7093]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_7100,plain,
% 3.61/0.99      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.61/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.61/0.99      | v3_ordinal1(sK3) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_778,c_7094]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_7101,plain,
% 3.61/0.99      ( ~ v3_ordinal1(sK3)
% 3.61/0.99      | k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.61/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
% 3.61/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_7100]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_7650,plain,
% 3.61/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.61/0.99      | k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_7100,c_25,c_7101]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_7651,plain,
% 3.61/0.99      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.61/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
% 3.61/0.99      inference(renaming,[status(thm)],[c_7650]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_7654,plain,
% 3.61/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.61/0.99      | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top
% 3.61/0.99      | r2_hidden(sK2,k3_relat_1(k1_wellord2(sK3))) != iProver_top
% 3.61/0.99      | v2_wellord1(k1_wellord2(sK3)) != iProver_top
% 3.61/0.99      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_7651,c_787]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_7655,plain,
% 3.61/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.61/0.99      | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top
% 3.61/0.99      | r2_hidden(sK2,sK3) != iProver_top
% 3.61/0.99      | v2_wellord1(k1_wellord2(sK3)) != iProver_top
% 3.61/0.99      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_7654,c_186]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_7891,plain,
% 3.61/0.99      ( v2_wellord1(k1_wellord2(sK3)) != iProver_top
% 3.61/0.99      | r2_hidden(sK2,sK3) != iProver_top
% 3.61/0.99      | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top
% 3.61/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_7655,c_2072]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_7892,plain,
% 3.61/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.61/0.99      | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top
% 3.61/0.99      | r2_hidden(sK2,sK3) != iProver_top
% 3.61/0.99      | v2_wellord1(k1_wellord2(sK3)) != iProver_top ),
% 3.61/0.99      inference(renaming,[status(thm)],[c_7891]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_7899,plain,
% 3.61/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.61/0.99      | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) != iProver_top
% 3.61/0.99      | r2_hidden(sK2,sK3) != iProver_top
% 3.61/0.99      | v2_wellord1(k1_wellord2(sK3)) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_3789,c_7892]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_8390,plain,
% 3.61/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.61/0.99      | r2_hidden(sK2,sK3) != iProver_top
% 3.61/0.99      | v2_wellord1(k1_wellord2(sK3)) != iProver_top ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_7899,c_1853]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_8400,plain,
% 3.61/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.61/0.99      | sK3 = sK2
% 3.61/0.99      | r2_hidden(sK3,sK2) = iProver_top
% 3.61/0.99      | v2_wellord1(k1_wellord2(sK3)) != iProver_top
% 3.61/0.99      | v3_ordinal1(sK3) != iProver_top
% 3.61/0.99      | v3_ordinal1(sK2) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_792,c_8390]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_8404,plain,
% 3.61/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.61/0.99      | sK3 = sK2
% 3.61/0.99      | r2_hidden(sK3,sK3) = iProver_top
% 3.61/0.99      | v2_wellord1(k1_wellord2(sK3)) != iProver_top
% 3.61/0.99      | v3_ordinal1(sK3) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_4355,c_8390]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_8441,plain,
% 3.61/0.99      ( v2_wellord1(k1_wellord2(sK3)) != iProver_top
% 3.61/0.99      | r2_hidden(sK3,sK3) = iProver_top
% 3.61/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_8404,c_26,c_28,c_23,c_78,c_84,c_91,c_1082]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_8442,plain,
% 3.61/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.61/0.99      | r2_hidden(sK3,sK3) = iProver_top
% 3.61/0.99      | v2_wellord1(k1_wellord2(sK3)) != iProver_top ),
% 3.61/0.99      inference(renaming,[status(thm)],[c_8441]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_8448,plain,
% 3.61/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.61/0.99      | r2_hidden(sK3,sK3) = iProver_top
% 3.61/0.99      | v3_ordinal1(sK3) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_778,c_8442]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_8403,plain,
% 3.61/0.99      ( k1_wellord1(k1_wellord2(sK3),sK3) = sK3
% 3.61/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.61/0.99      | sK3 = sK2
% 3.61/0.99      | v2_wellord1(k1_wellord2(sK3)) != iProver_top
% 3.61/0.99      | v3_ordinal1(sK3) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_6378,c_8390]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2450,plain,
% 3.61/0.99      ( ~ r2_hidden(sK3,X0)
% 3.61/0.99      | ~ v3_ordinal1(X0)
% 3.61/0.99      | ~ v3_ordinal1(sK3)
% 3.61/0.99      | k1_wellord1(k1_wellord2(X0),sK3) = sK3 ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_20]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4062,plain,
% 3.61/0.99      ( ~ r2_hidden(sK3,sK3)
% 3.61/0.99      | ~ v3_ordinal1(sK3)
% 3.61/0.99      | k1_wellord1(k1_wellord2(sK3),sK3) = sK3 ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_2450]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4066,plain,
% 3.61/0.99      ( k1_wellord1(k1_wellord2(sK3),sK3) = sK3
% 3.61/0.99      | r2_hidden(sK3,sK3) != iProver_top
% 3.61/0.99      | v3_ordinal1(sK3) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_4062]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_8667,plain,
% 3.61/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.61/0.99      | k1_wellord1(k1_wellord2(sK3),sK3) = sK3 ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_8403,c_28,c_4066,c_8448]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_8668,plain,
% 3.61/0.99      ( k1_wellord1(k1_wellord2(sK3),sK3) = sK3
% 3.61/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
% 3.61/0.99      inference(renaming,[status(thm)],[c_8667]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_8671,plain,
% 3.61/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.61/0.99      | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK3)) != iProver_top
% 3.61/0.99      | r2_hidden(sK3,k3_relat_1(k1_wellord2(sK3))) != iProver_top
% 3.61/0.99      | v2_wellord1(k1_wellord2(sK3)) != iProver_top
% 3.61/0.99      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_8668,c_787]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_8672,plain,
% 3.61/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.61/0.99      | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK3)) != iProver_top
% 3.61/0.99      | r2_hidden(sK3,sK3) != iProver_top
% 3.61/0.99      | v2_wellord1(k1_wellord2(sK3)) != iProver_top
% 3.61/0.99      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_8671,c_186,c_1277]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_8675,plain,
% 3.61/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.61/0.99      | v2_wellord1(k1_wellord2(sK3)) != iProver_top ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_8400,c_28,c_29,c_41,c_1853,c_1910,c_2072,c_8448,
% 3.61/0.99                 c_8672]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_8681,plain,
% 3.61/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.61/0.99      | v3_ordinal1(sK3) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_778,c_8675]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_8878,plain,
% 3.61/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_8681,c_28]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_8887,plain,
% 3.61/0.99      ( r2_hidden(X0,k3_relat_1(k1_wellord2(sK3))) != iProver_top
% 3.61/0.99      | r2_hidden(X0,k3_relat_1(k1_wellord2(sK2))) = iProver_top
% 3.61/0.99      | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_8878,c_790]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_8923,plain,
% 3.61/0.99      ( r2_hidden(X0,sK3) != iProver_top
% 3.61/0.99      | r2_hidden(X0,sK2) = iProver_top
% 3.61/0.99      | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_8887,c_186]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9105,plain,
% 3.61/0.99      ( r2_hidden(X0,sK2) = iProver_top
% 3.61/0.99      | r2_hidden(X0,sK3) != iProver_top ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_8923,c_41]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9106,plain,
% 3.61/0.99      ( r2_hidden(X0,sK3) != iProver_top
% 3.61/0.99      | r2_hidden(X0,sK2) = iProver_top ),
% 3.61/0.99      inference(renaming,[status(thm)],[c_9105]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9115,plain,
% 3.61/0.99      ( k1_wellord1(k1_wellord2(X0),sK3) = sK3
% 3.61/0.99      | sK3 = X0
% 3.61/0.99      | r2_hidden(X0,sK2) = iProver_top
% 3.61/0.99      | v3_ordinal1(X0) != iProver_top
% 3.61/0.99      | v3_ordinal1(sK3) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_2282,c_9106]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_10759,plain,
% 3.61/0.99      ( v3_ordinal1(X0) != iProver_top
% 3.61/0.99      | r2_hidden(X0,sK2) = iProver_top
% 3.61/0.99      | sK3 = X0
% 3.61/0.99      | k1_wellord1(k1_wellord2(X0),sK3) = sK3 ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_9115,c_28]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_10760,plain,
% 3.61/0.99      ( k1_wellord1(k1_wellord2(X0),sK3) = sK3
% 3.61/0.99      | sK3 = X0
% 3.61/0.99      | r2_hidden(X0,sK2) = iProver_top
% 3.61/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.61/0.99      inference(renaming,[status(thm)],[c_10759]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9116,plain,
% 3.61/0.99      ( sK3 = X0
% 3.61/0.99      | r2_hidden(X0,sK2) = iProver_top
% 3.61/0.99      | r2_hidden(sK3,X0) = iProver_top
% 3.61/0.99      | v3_ordinal1(X0) != iProver_top
% 3.61/0.99      | v3_ordinal1(sK3) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_792,c_9106]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9178,plain,
% 3.61/0.99      ( v3_ordinal1(X0) != iProver_top
% 3.61/0.99      | r2_hidden(sK3,X0) = iProver_top
% 3.61/0.99      | r2_hidden(X0,sK2) = iProver_top
% 3.61/0.99      | sK3 = X0 ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_9116,c_28]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9179,plain,
% 3.61/0.99      ( sK3 = X0
% 3.61/0.99      | r2_hidden(X0,sK2) = iProver_top
% 3.61/0.99      | r2_hidden(sK3,X0) = iProver_top
% 3.61/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.61/0.99      inference(renaming,[status(thm)],[c_9178]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9192,plain,
% 3.61/0.99      ( k1_wellord1(k1_wellord2(sK2),X0) = X0
% 3.61/0.99      | sK3 = X0
% 3.61/0.99      | r2_hidden(sK3,X0) = iProver_top
% 3.61/0.99      | v3_ordinal1(X0) != iProver_top
% 3.61/0.99      | v3_ordinal1(sK2) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_9179,c_779]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9564,plain,
% 3.61/0.99      ( v3_ordinal1(X0) != iProver_top
% 3.61/0.99      | r2_hidden(sK3,X0) = iProver_top
% 3.61/0.99      | sK3 = X0
% 3.61/0.99      | k1_wellord1(k1_wellord2(sK2),X0) = X0 ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_9192,c_27]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9565,plain,
% 3.61/0.99      ( k1_wellord1(k1_wellord2(sK2),X0) = X0
% 3.61/0.99      | sK3 = X0
% 3.61/0.99      | r2_hidden(sK3,X0) = iProver_top
% 3.61/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.61/0.99      inference(renaming,[status(thm)],[c_9564]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9572,plain,
% 3.61/0.99      ( k1_wellord1(k1_wellord2(X0),sK3) = sK3
% 3.61/0.99      | k1_wellord1(k1_wellord2(sK2),X0) = X0
% 3.61/0.99      | sK3 = X0
% 3.61/0.99      | v3_ordinal1(X0) != iProver_top
% 3.61/0.99      | v3_ordinal1(sK3) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_9565,c_779]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9616,plain,
% 3.61/0.99      ( v3_ordinal1(X0) != iProver_top
% 3.61/0.99      | sK3 = X0
% 3.61/0.99      | k1_wellord1(k1_wellord2(sK2),X0) = X0
% 3.61/0.99      | k1_wellord1(k1_wellord2(X0),sK3) = sK3 ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_9572,c_28]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9617,plain,
% 3.61/0.99      ( k1_wellord1(k1_wellord2(X0),sK3) = sK3
% 3.61/0.99      | k1_wellord1(k1_wellord2(sK2),X0) = X0
% 3.61/0.99      | sK3 = X0
% 3.61/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.61/0.99      inference(renaming,[status(thm)],[c_9616]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9627,plain,
% 3.61/0.99      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.61/0.99      | k1_wellord1(k1_wellord2(sK2),sK2) = sK2
% 3.61/0.99      | sK3 = sK2 ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_774,c_9617]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9619,plain,
% 3.61/0.99      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.61/0.99      | k1_wellord1(k1_wellord2(sK2),sK2) = sK2
% 3.61/0.99      | sK3 = sK2
% 3.61/0.99      | v3_ordinal1(sK2) != iProver_top ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_9617]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9950,plain,
% 3.61/0.99      ( k1_wellord1(k1_wellord2(sK2),sK2) = sK2
% 3.61/0.99      | k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_9627,c_26,c_27,c_23,c_78,c_84,c_91,c_1082,c_9619]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9951,plain,
% 3.61/0.99      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.61/0.99      | k1_wellord1(k1_wellord2(sK2),sK2) = sK2 ),
% 3.61/0.99      inference(renaming,[status(thm)],[c_9950]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9954,plain,
% 3.61/0.99      ( k1_wellord1(k1_wellord2(sK2),sK2) = sK2
% 3.61/0.99      | r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top
% 3.61/0.99      | r2_hidden(sK3,k3_relat_1(k1_wellord2(sK2))) != iProver_top
% 3.61/0.99      | v2_wellord1(k1_wellord2(sK2)) != iProver_top
% 3.61/0.99      | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_9951,c_787]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9955,plain,
% 3.61/0.99      ( k1_wellord1(k1_wellord2(sK2),sK2) = sK2
% 3.61/0.99      | r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) != iProver_top
% 3.61/0.99      | r2_hidden(sK3,k3_relat_1(k1_wellord2(sK2))) != iProver_top
% 3.61/0.99      | v2_wellord1(k1_wellord2(sK2)) != iProver_top
% 3.61/0.99      | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
% 3.61/0.99      inference(light_normalisation,[status(thm)],[c_9954,c_8878]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9956,plain,
% 3.61/0.99      ( k1_wellord1(k1_wellord2(sK2),sK2) = sK2
% 3.61/0.99      | r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) != iProver_top
% 3.61/0.99      | r2_hidden(sK3,sK2) != iProver_top
% 3.61/0.99      | v2_wellord1(k1_wellord2(sK2)) != iProver_top
% 3.61/0.99      | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_9955,c_186]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_34,plain,
% 3.61/0.99      ( v2_wellord1(k1_wellord2(sK2)) | ~ v3_ordinal1(sK2) ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_21]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_40,plain,
% 3.61/0.99      ( v1_relat_1(k1_wellord2(sK2)) ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9242,plain,
% 3.61/0.99      ( r2_hidden(sK3,X0)
% 3.61/0.99      | ~ v3_ordinal1(X0)
% 3.61/0.99      | ~ v3_ordinal1(sK2)
% 3.61/0.99      | k1_wellord1(k1_wellord2(sK2),X0) = X0
% 3.61/0.99      | sK3 = X0 ),
% 3.61/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_9192]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9244,plain,
% 3.61/0.99      ( r2_hidden(sK3,sK2)
% 3.61/0.99      | ~ v3_ordinal1(sK2)
% 3.61/0.99      | k1_wellord1(k1_wellord2(sK2),sK2) = sK2
% 3.61/0.99      | sK3 = sK2 ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_9242]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9957,plain,
% 3.61/0.99      ( ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
% 3.61/0.99      | ~ r2_hidden(sK3,sK2)
% 3.61/0.99      | ~ v2_wellord1(k1_wellord2(sK2))
% 3.61/0.99      | ~ v1_relat_1(k1_wellord2(sK2))
% 3.61/0.99      | k1_wellord1(k1_wellord2(sK2),sK2) = sK2 ),
% 3.61/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_9956]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9959,plain,
% 3.61/0.99      ( k1_wellord1(k1_wellord2(sK2),sK2) = sK2 ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_9956,c_26,c_24,c_23,c_34,c_40,c_78,c_84,c_91,c_1082,
% 3.61/0.99                 c_9244,c_9957]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9962,plain,
% 3.61/0.99      ( r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK2)) != iProver_top
% 3.61/0.99      | r2_hidden(sK2,k3_relat_1(k1_wellord2(sK2))) != iProver_top
% 3.61/0.99      | v2_wellord1(k1_wellord2(sK2)) != iProver_top
% 3.61/0.99      | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_9959,c_787]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9963,plain,
% 3.61/0.99      ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK2)) != iProver_top
% 3.61/0.99      | r2_hidden(sK2,sK2) != iProver_top
% 3.61/0.99      | v2_wellord1(k1_wellord2(sK2)) != iProver_top
% 3.61/0.99      | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_9962,c_186,c_1277]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_33,plain,
% 3.61/0.99      ( v2_wellord1(k1_wellord2(X0)) = iProver_top
% 3.61/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_35,plain,
% 3.61/0.99      ( v2_wellord1(k1_wellord2(sK2)) = iProver_top
% 3.61/0.99      | v3_ordinal1(sK2) != iProver_top ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_33]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1903,plain,
% 3.61/0.99      ( ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(sK3))
% 3.61/0.99      | r4_wellord1(k1_wellord2(X0),k1_wellord2(sK2))
% 3.61/0.99      | ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2))
% 3.61/0.99      | ~ v1_relat_1(k1_wellord2(X0))
% 3.61/0.99      | ~ v1_relat_1(k1_wellord2(sK3))
% 3.61/0.99      | ~ v1_relat_1(k1_wellord2(sK2)) ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_1313]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1904,plain,
% 3.61/0.99      ( r4_wellord1(k1_wellord2(X0),k1_wellord2(sK3)) != iProver_top
% 3.61/0.99      | r4_wellord1(k1_wellord2(X0),k1_wellord2(sK2)) = iProver_top
% 3.61/0.99      | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) != iProver_top
% 3.61/0.99      | v1_relat_1(k1_wellord2(X0)) != iProver_top
% 3.61/0.99      | v1_relat_1(k1_wellord2(sK3)) != iProver_top
% 3.61/0.99      | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_1903]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1906,plain,
% 3.61/0.99      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) != iProver_top
% 3.61/0.99      | r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) != iProver_top
% 3.61/0.99      | r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK2)) = iProver_top
% 3.61/0.99      | v1_relat_1(k1_wellord2(sK3)) != iProver_top
% 3.61/0.99      | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_1904]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_10240,plain,
% 3.61/0.99      ( r2_hidden(sK2,sK2) != iProver_top ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_9963,c_27,c_29,c_35,c_41,c_1853,c_1906,c_2072]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_10771,plain,
% 3.61/0.99      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.61/0.99      | sK3 = sK2
% 3.61/0.99      | v3_ordinal1(sK2) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_10760,c_10240]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9165,plain,
% 3.61/0.99      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.61/0.99      | sK3 = sK2
% 3.61/0.99      | r2_hidden(sK2,sK2) = iProver_top
% 3.61/0.99      | v3_ordinal1(sK3) != iProver_top
% 3.61/0.99      | v3_ordinal1(sK2) != iProver_top ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_9115]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_10793,plain,
% 3.61/0.99      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_10771,c_26,c_27,c_28,c_29,c_23,c_35,c_41,c_78,c_84,
% 3.61/0.99                 c_91,c_1082,c_1853,c_1906,c_2072,c_9165,c_9963]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_10796,plain,
% 3.61/0.99      ( r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top
% 3.61/0.99      | r2_hidden(sK3,k3_relat_1(k1_wellord2(sK2))) != iProver_top
% 3.61/0.99      | v2_wellord1(k1_wellord2(sK2)) != iProver_top
% 3.61/0.99      | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_10793,c_787]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_10797,plain,
% 3.61/0.99      ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) != iProver_top
% 3.61/0.99      | r2_hidden(sK3,k3_relat_1(k1_wellord2(sK2))) != iProver_top
% 3.61/0.99      | v2_wellord1(k1_wellord2(sK2)) != iProver_top
% 3.61/0.99      | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
% 3.61/0.99      inference(light_normalisation,[status(thm)],[c_10796,c_8878]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_10798,plain,
% 3.61/0.99      ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) != iProver_top
% 3.61/0.99      | r2_hidden(sK3,sK2) != iProver_top
% 3.61/0.99      | v2_wellord1(k1_wellord2(sK2)) != iProver_top
% 3.61/0.99      | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_10797,c_186]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9181,plain,
% 3.61/0.99      ( sK3 = sK2
% 3.61/0.99      | r2_hidden(sK3,sK2) = iProver_top
% 3.61/0.99      | r2_hidden(sK2,sK2) = iProver_top
% 3.61/0.99      | v3_ordinal1(sK2) != iProver_top ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_9179]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(contradiction,plain,
% 3.61/0.99      ( $false ),
% 3.61/0.99      inference(minisat,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_10798,c_9963,c_9181,c_2072,c_1906,c_1853,c_1082,c_91,
% 3.61/0.99                 c_84,c_78,c_41,c_35,c_23,c_29,c_27,c_26]) ).
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.61/0.99  
% 3.61/0.99  ------                               Statistics
% 3.61/0.99  
% 3.61/0.99  ------ Selected
% 3.61/0.99  
% 3.61/0.99  total_time:                             0.321
% 3.61/0.99  
%------------------------------------------------------------------------------
