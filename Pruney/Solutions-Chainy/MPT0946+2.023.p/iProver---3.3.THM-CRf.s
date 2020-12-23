%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:45 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :  208 (40547 expanded)
%              Number of clauses        :  143 (14757 expanded)
%              Number of leaves         :   21 (8642 expanded)
%              Depth                    :   42
%              Number of atoms          :  693 (144348 expanded)
%              Number of equality atoms :  375 (53620 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   17 (   3 average)
%              Maximal term depth       :    5 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
           => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_wellord1(k1_wellord2(X1),X0) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f14,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
     => ( sK3 != X0
        & r4_wellord1(k1_wellord2(X0),k1_wellord2(sK3))
        & v3_ordinal1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
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

fof(f45,plain,
    ( sK2 != sK3
    & r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
    & v3_ordinal1(sK3)
    & v3_ordinal1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f37,f44,f43])).

fof(f66,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f67,plain,(
    v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_xboole_0(X1,X0)
              & X0 != X1
              & ~ r2_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_xboole_0(X1,X0)
          | X0 = X1
          | r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_xboole_0(X1,X0)
          | X0 = X1
          | r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X1,X0)
      | X0 = X1
      | r2_xboole_0(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f69,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f45])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f70,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f10,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_wellord1(X0,k3_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k2_wellord1(X0,k3_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X0] :
      ( k2_wellord1(X0,k3_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f38,plain,(
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

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

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
    inference(rectify,[],[f39])).

fof(f41,plain,(
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

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f41])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f77,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f64,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f68,plain,(
    r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) ),
    inference(cnf_transformation,[],[f45])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f52,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r4_wellord1(X0,X2)
      | ~ r4_wellord1(X1,X2)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_2,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1251,plain,
    ( X0 = X1
    | r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | k1_wellord1(k1_wellord2(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1238,plain,
    ( k1_wellord1(k1_wellord2(X0),X1) = X1
    | r2_hidden(X1,X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2382,plain,
    ( X0 = X1
    | k1_wellord1(k1_wellord2(X0),X1) = X1
    | r2_hidden(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1251,c_1238])).

cnf(c_23,negated_conjecture,
    ( v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1234,plain,
    ( v3_ordinal1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1235,plain,
    ( v3_ordinal1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3,plain,
    ( r2_xboole_0(X0,X1)
    | r2_xboole_0(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1250,plain,
    ( X0 = X1
    | r2_xboole_0(X0,X1) = iProver_top
    | r2_xboole_0(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1252,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2347,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) = iProver_top
    | r2_xboole_0(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1250,c_1252])).

cnf(c_19,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1237,plain,
    ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2954,plain,
    ( X0 = X1
    | k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | r2_xboole_0(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2347,c_1237])).

cnf(c_3187,plain,
    ( X0 = X1
    | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
    | r1_tarski(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2954,c_1252])).

cnf(c_3595,plain,
    ( X0 = X1
    | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
    | k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3187,c_1237])).

cnf(c_3700,plain,
    ( k2_wellord1(k1_wellord2(X0),sK3) = k1_wellord2(sK3)
    | k2_wellord1(k1_wellord2(sK3),X0) = k1_wellord2(X0)
    | sK3 = X0
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1235,c_3595])).

cnf(c_3797,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_1234,c_3700])).

cnf(c_24,plain,
    ( v3_ordinal1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_20,negated_conjecture,
    ( sK2 != sK3 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_72,plain,
    ( r2_xboole_0(sK2,sK2)
    | ~ v3_ordinal1(sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_81,plain,
    ( ~ r2_xboole_0(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_839,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1463,plain,
    ( sK3 != X0
    | sK2 != X0
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_839])).

cnf(c_1464,plain,
    ( sK3 != sK2
    | sK2 = sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1463])).

cnf(c_3719,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | sK3 = sK2
    | v3_ordinal1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3700])).

cnf(c_3804,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3797,c_23,c_24,c_20,c_72,c_81,c_1464,c_3719])).

cnf(c_3805,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
    inference(renaming,[status(thm)],[c_3804])).

cnf(c_16,plain,
    ( v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1239,plain,
    ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k2_wellord1(X0,k3_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1248,plain,
    ( k2_wellord1(X0,k3_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1530,plain,
    ( k2_wellord1(k1_wellord2(X0),k3_relat_1(k1_wellord2(X0))) = k1_wellord2(X0) ),
    inference(superposition,[status(thm)],[c_1239,c_1248])).

cnf(c_15,plain,
    ( ~ v1_relat_1(k1_wellord2(X0))
    | k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_137,plain,
    ( k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_16])).

cnf(c_1531,plain,
    ( k2_wellord1(k1_wellord2(X0),X0) = k1_wellord2(X0) ),
    inference(light_normalisation,[status(thm)],[c_1530,c_137])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k2_wellord1(k2_wellord1(X0,X1),X2) = k2_wellord1(k2_wellord1(X0,X2),X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1249,plain,
    ( k2_wellord1(k2_wellord1(X0,X1),X2) = k2_wellord1(k2_wellord1(X0,X2),X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1716,plain,
    ( k2_wellord1(k2_wellord1(k1_wellord2(X0),X1),X2) = k2_wellord1(k2_wellord1(k1_wellord2(X0),X2),X1) ),
    inference(superposition,[status(thm)],[c_1239,c_1249])).

cnf(c_2000,plain,
    ( k2_wellord1(k2_wellord1(k1_wellord2(X0),X1),X0) = k2_wellord1(k1_wellord2(X0),X1) ),
    inference(superposition,[status(thm)],[c_1531,c_1716])).

cnf(c_3808,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k2_wellord1(k1_wellord2(sK3),sK2)
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
    inference(superposition,[status(thm)],[c_3805,c_2000])).

cnf(c_3929,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
    inference(superposition,[status(thm)],[c_3808,c_3805])).

cnf(c_3953,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k2_wellord1(k1_wellord2(sK3),sK2)
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
    inference(superposition,[status(thm)],[c_3929,c_2000])).

cnf(c_2380,plain,
    ( X0 = X1
    | k1_wellord1(k1_wellord2(X1),X0) = X0
    | r2_hidden(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1251,c_1238])).

cnf(c_3073,plain,
    ( X0 = X1
    | k1_wellord1(k1_wellord2(X1),X0) = X0
    | k1_wellord1(k1_wellord2(X0),X1) = X1
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2380,c_1238])).

cnf(c_3323,plain,
    ( k1_wellord1(k1_wellord2(X0),sK3) = sK3
    | k1_wellord1(k1_wellord2(sK3),X0) = X0
    | sK3 = X0
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1235,c_3073])).

cnf(c_3406,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_1234,c_3323])).

cnf(c_3413,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3406,c_23,c_20,c_72,c_81,c_1464])).

cnf(c_3414,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
    inference(renaming,[status(thm)],[c_3413])).

cnf(c_8,plain,
    ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
    | ~ r2_hidden(X1,k3_relat_1(X0))
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_18,plain,
    ( v2_wellord1(k1_wellord2(X0))
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_264,plain,
    ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
    | ~ r2_hidden(X1,k3_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v3_ordinal1(X2)
    | k1_wellord2(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_18])).

cnf(c_265,plain,
    ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
    | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
    | ~ v1_relat_1(k1_wellord2(X0))
    | ~ v3_ordinal1(X0) ),
    inference(unflattening,[status(thm)],[c_264])).

cnf(c_269,plain,
    ( ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
    | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
    | ~ v3_ordinal1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_265,c_16])).

cnf(c_270,plain,
    ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
    | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
    | ~ v3_ordinal1(X0) ),
    inference(renaming,[status(thm)],[c_269])).

cnf(c_1233,plain,
    ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
    | r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_270])).

cnf(c_1332,plain,
    ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1233,c_137])).

cnf(c_3417,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3414,c_1332])).

cnf(c_25,plain,
    ( v3_ordinal1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1474,plain,
    ( r2_hidden(sK3,sK2)
    | r2_hidden(sK2,sK3)
    | ~ v3_ordinal1(sK3)
    | ~ v3_ordinal1(sK2)
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1475,plain,
    ( sK2 = sK3
    | r2_hidden(sK3,sK2) = iProver_top
    | r2_hidden(sK2,sK3) = iProver_top
    | v3_ordinal1(sK3) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1474])).

cnf(c_1509,plain,
    ( ~ r2_hidden(sK3,sK2)
    | ~ v3_ordinal1(sK3)
    | ~ v3_ordinal1(sK2)
    | k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1510,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | r2_hidden(sK3,sK2) != iProver_top
    | v3_ordinal1(sK3) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1509])).

cnf(c_3551,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3417,c_24,c_25,c_20,c_1475,c_1510])).

cnf(c_4223,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3953,c_3551])).

cnf(c_5378,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3929,c_4223])).

cnf(c_1661,plain,
    ( v1_relat_1(k1_wellord2(sK3)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1662,plain,
    ( v1_relat_1(k1_wellord2(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1661])).

cnf(c_21,negated_conjecture,
    ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1236,plain,
    ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_6,plain,
    ( ~ r4_wellord1(X0,X1)
    | r4_wellord1(X1,X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1247,plain,
    ( r4_wellord1(X0,X1) != iProver_top
    | r4_wellord1(X1,X0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2046,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1236,c_1247])).

cnf(c_36,plain,
    ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_38,plain,
    ( v1_relat_1(k1_wellord2(sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_2049,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2046,c_38,c_1662])).

cnf(c_7,plain,
    ( ~ r4_wellord1(X0,X1)
    | ~ r4_wellord1(X1,X2)
    | r4_wellord1(X0,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1246,plain,
    ( r4_wellord1(X0,X1) != iProver_top
    | r4_wellord1(X1,X2) != iProver_top
    | r4_wellord1(X0,X2) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2515,plain,
    ( r4_wellord1(k1_wellord2(sK3),X0) = iProver_top
    | r4_wellord1(k1_wellord2(sK2),X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2049,c_1246])).

cnf(c_2690,plain,
    ( r4_wellord1(k1_wellord2(sK3),X0) = iProver_top
    | r4_wellord1(k1_wellord2(sK2),X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2515,c_38,c_1662])).

cnf(c_2699,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK3)) = iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1236,c_2690])).

cnf(c_5871,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
    | k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5378,c_1662,c_2699])).

cnf(c_5872,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
    inference(renaming,[status(thm)],[c_5871])).

cnf(c_5875,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
    | r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top
    | r2_hidden(sK3,sK2) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5872,c_1332])).

cnf(c_26,plain,
    ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_848,plain,
    ( X0 != X1
    | k1_wellord2(X0) = k1_wellord2(X1) ),
    theory(equality)).

cnf(c_860,plain,
    ( k1_wellord2(sK2) = k1_wellord2(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_848])).

cnf(c_846,plain,
    ( ~ r4_wellord1(X0,X1)
    | r4_wellord1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1480,plain,
    ( r4_wellord1(X0,X1)
    | ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
    | X1 != k1_wellord2(sK3)
    | X0 != k1_wellord2(sK2) ),
    inference(instantiation,[status(thm)],[c_846])).

cnf(c_3568,plain,
    ( r4_wellord1(X0,k2_wellord1(k1_wellord2(sK2),sK3))
    | ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
    | X0 != k1_wellord2(sK2)
    | k2_wellord1(k1_wellord2(sK2),sK3) != k1_wellord2(sK3) ),
    inference(instantiation,[status(thm)],[c_1480])).

cnf(c_5837,plain,
    ( r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3))
    | ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
    | k2_wellord1(k1_wellord2(sK2),sK3) != k1_wellord2(sK3)
    | k1_wellord2(sK2) != k1_wellord2(sK2) ),
    inference(instantiation,[status(thm)],[c_3568])).

cnf(c_5838,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) != k1_wellord2(sK3)
    | k1_wellord2(sK2) != k1_wellord2(sK2)
    | r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) = iProver_top
    | r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5837])).

cnf(c_5878,plain,
    ( r2_hidden(sK3,sK2) != iProver_top
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5875,c_23,c_24,c_26,c_72,c_81,c_860,c_3929,c_5838])).

cnf(c_5879,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
    | r2_hidden(sK3,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5878])).

cnf(c_5887,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
    | sK3 = sK2
    | r2_hidden(sK2,sK3) = iProver_top
    | v3_ordinal1(sK3) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1251,c_5879])).

cnf(c_6358,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5887,c_23,c_24,c_25,c_20,c_72,c_81,c_1464])).

cnf(c_6364,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
    | v3_ordinal1(sK3) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6358,c_1238])).

cnf(c_6365,plain,
    ( ~ v3_ordinal1(sK3)
    | ~ v3_ordinal1(sK2)
    | k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6364])).

cnf(c_6556,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6364,c_23,c_22,c_6365])).

cnf(c_6560,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6556,c_1332])).

cnf(c_6994,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6560,c_23,c_24,c_25,c_20,c_72,c_81,c_1464,c_5887])).

cnf(c_7001,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3953,c_6994])).

cnf(c_4219,plain,
    ( k2_wellord1(k2_wellord1(k1_wellord2(sK2),sK3),sK3) = k2_wellord1(k1_wellord2(sK3),sK2)
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
    inference(superposition,[status(thm)],[c_3953,c_2000])).

cnf(c_3954,plain,
    ( k2_wellord1(k2_wellord1(k1_wellord2(sK2),X0),sK3) = k2_wellord1(k1_wellord2(sK3),X0)
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
    inference(superposition,[status(thm)],[c_3929,c_1716])).

cnf(c_4410,plain,
    ( k2_wellord1(k2_wellord1(k1_wellord2(sK2),sK3),X0) = k2_wellord1(k1_wellord2(sK3),X0)
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
    inference(superposition,[status(thm)],[c_3954,c_1716])).

cnf(c_6094,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK3) = k2_wellord1(k1_wellord2(sK3),sK2)
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
    inference(superposition,[status(thm)],[c_4219,c_4410])).

cnf(c_6098,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK3)
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
    inference(demodulation,[status(thm)],[c_6094,c_1531])).

cnf(c_7000,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6098,c_6994])).

cnf(c_7015,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7001,c_1662,c_2699,c_7000])).

cnf(c_3811,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3805,c_3551])).

cnf(c_4080,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3811,c_38,c_1662,c_2046])).

cnf(c_4081,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
    inference(renaming,[status(thm)],[c_4080])).

cnf(c_4084,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top
    | r2_hidden(sK3,sK2) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4081,c_1332])).

cnf(c_4208,plain,
    ( r2_hidden(sK3,sK2) != iProver_top
    | r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4084,c_24])).

cnf(c_4209,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top
    | r2_hidden(sK3,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4208])).

cnf(c_7029,plain,
    ( k1_wellord2(sK3) = k1_wellord2(sK2)
    | r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK2)) != iProver_top
    | r2_hidden(sK3,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7015,c_4209])).

cnf(c_2514,plain,
    ( r4_wellord1(k1_wellord2(sK3),X0) != iProver_top
    | r4_wellord1(k1_wellord2(sK2),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1236,c_1246])).

cnf(c_2593,plain,
    ( r4_wellord1(k1_wellord2(sK3),X0) != iProver_top
    | r4_wellord1(k1_wellord2(sK2),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2514,c_38,c_1662])).

cnf(c_2602,plain,
    ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK2)) = iProver_top
    | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2049,c_2593])).

cnf(c_7530,plain,
    ( k1_wellord2(sK3) = k1_wellord2(sK2)
    | r2_hidden(sK3,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7029,c_38,c_2602])).

cnf(c_7538,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k1_wellord2(sK3) = k1_wellord2(sK2)
    | sK3 = sK2
    | v3_ordinal1(sK3) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2382,c_7530])).

cnf(c_7539,plain,
    ( k1_wellord2(sK3) = k1_wellord2(sK2)
    | sK3 = sK2
    | r2_hidden(sK2,sK3) = iProver_top
    | v3_ordinal1(sK3) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1251,c_7530])).

cnf(c_7668,plain,
    ( k1_wellord2(sK3) = k1_wellord2(sK2)
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7539,c_23,c_24,c_25,c_20,c_72,c_81,c_1464])).

cnf(c_7674,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k1_wellord2(sK3) = k1_wellord2(sK2)
    | v3_ordinal1(sK3) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7668,c_1238])).

cnf(c_7675,plain,
    ( ~ v3_ordinal1(sK3)
    | ~ v3_ordinal1(sK2)
    | k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k1_wellord2(sK3) = k1_wellord2(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7674])).

cnf(c_7677,plain,
    ( k1_wellord2(sK3) = k1_wellord2(sK2)
    | k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7538,c_23,c_24,c_25,c_20,c_72,c_81,c_1464])).

cnf(c_7678,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k1_wellord2(sK3) = k1_wellord2(sK2) ),
    inference(renaming,[status(thm)],[c_7677])).

cnf(c_7681,plain,
    ( k1_wellord2(sK3) = k1_wellord2(sK2)
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7678,c_1332])).

cnf(c_838,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1562,plain,
    ( k1_wellord2(sK3) = k1_wellord2(sK3) ),
    inference(instantiation,[status(thm)],[c_838])).

cnf(c_7033,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
    | k1_wellord2(sK3) = k1_wellord2(sK2) ),
    inference(demodulation,[status(thm)],[c_7015,c_3808])).

cnf(c_3146,plain,
    ( r4_wellord1(X0,X1)
    | ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2))
    | X0 != k1_wellord2(sK3)
    | X1 != k1_wellord2(sK2) ),
    inference(instantiation,[status(thm)],[c_846])).

cnf(c_3515,plain,
    ( r4_wellord1(k1_wellord2(sK3),X0)
    | ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2))
    | X0 != k1_wellord2(sK2)
    | k1_wellord2(sK3) != k1_wellord2(sK3) ),
    inference(instantiation,[status(thm)],[c_3146])).

cnf(c_7097,plain,
    ( r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2))
    | ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2))
    | k2_wellord1(k1_wellord2(sK3),sK2) != k1_wellord2(sK2)
    | k1_wellord2(sK3) != k1_wellord2(sK3) ),
    inference(instantiation,[status(thm)],[c_3515])).

cnf(c_7128,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK2) != k1_wellord2(sK2)
    | k1_wellord2(sK3) != k1_wellord2(sK3)
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) = iProver_top
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7097])).

cnf(c_7807,plain,
    ( k1_wellord2(sK3) = k1_wellord2(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7681,c_25,c_38,c_1562,c_1662,c_2046,c_7033,c_7128,c_7668])).

cnf(c_7866,plain,
    ( k3_relat_1(k1_wellord2(sK2)) = sK3 ),
    inference(superposition,[status(thm)],[c_7807,c_137])).

cnf(c_7884,plain,
    ( sK3 = sK2 ),
    inference(demodulation,[status(thm)],[c_7866,c_137])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7884,c_1464,c_81,c_72,c_20,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:42:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.01/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/0.99  
% 3.01/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.01/0.99  
% 3.01/0.99  ------  iProver source info
% 3.01/0.99  
% 3.01/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.01/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.01/0.99  git: non_committed_changes: false
% 3.01/0.99  git: last_make_outside_of_git: false
% 3.01/0.99  
% 3.01/0.99  ------ 
% 3.01/0.99  
% 3.01/0.99  ------ Input Options
% 3.01/0.99  
% 3.01/0.99  --out_options                           all
% 3.01/0.99  --tptp_safe_out                         true
% 3.01/0.99  --problem_path                          ""
% 3.01/0.99  --include_path                          ""
% 3.01/0.99  --clausifier                            res/vclausify_rel
% 3.01/0.99  --clausifier_options                    --mode clausify
% 3.01/0.99  --stdin                                 false
% 3.01/0.99  --stats_out                             all
% 3.01/0.99  
% 3.01/0.99  ------ General Options
% 3.01/0.99  
% 3.01/0.99  --fof                                   false
% 3.01/0.99  --time_out_real                         305.
% 3.01/0.99  --time_out_virtual                      -1.
% 3.01/0.99  --symbol_type_check                     false
% 3.01/0.99  --clausify_out                          false
% 3.01/0.99  --sig_cnt_out                           false
% 3.01/0.99  --trig_cnt_out                          false
% 3.01/0.99  --trig_cnt_out_tolerance                1.
% 3.01/0.99  --trig_cnt_out_sk_spl                   false
% 3.01/0.99  --abstr_cl_out                          false
% 3.01/0.99  
% 3.01/0.99  ------ Global Options
% 3.01/0.99  
% 3.01/0.99  --schedule                              default
% 3.01/0.99  --add_important_lit                     false
% 3.01/0.99  --prop_solver_per_cl                    1000
% 3.01/0.99  --min_unsat_core                        false
% 3.01/0.99  --soft_assumptions                      false
% 3.01/0.99  --soft_lemma_size                       3
% 3.01/0.99  --prop_impl_unit_size                   0
% 3.01/0.99  --prop_impl_unit                        []
% 3.01/0.99  --share_sel_clauses                     true
% 3.01/0.99  --reset_solvers                         false
% 3.01/0.99  --bc_imp_inh                            [conj_cone]
% 3.01/0.99  --conj_cone_tolerance                   3.
% 3.01/0.99  --extra_neg_conj                        none
% 3.01/0.99  --large_theory_mode                     true
% 3.01/0.99  --prolific_symb_bound                   200
% 3.01/0.99  --lt_threshold                          2000
% 3.01/0.99  --clause_weak_htbl                      true
% 3.01/0.99  --gc_record_bc_elim                     false
% 3.01/0.99  
% 3.01/0.99  ------ Preprocessing Options
% 3.01/0.99  
% 3.01/0.99  --preprocessing_flag                    true
% 3.01/0.99  --time_out_prep_mult                    0.1
% 3.01/0.99  --splitting_mode                        input
% 3.01/0.99  --splitting_grd                         true
% 3.01/0.99  --splitting_cvd                         false
% 3.01/0.99  --splitting_cvd_svl                     false
% 3.01/0.99  --splitting_nvd                         32
% 3.01/0.99  --sub_typing                            true
% 3.01/0.99  --prep_gs_sim                           true
% 3.01/0.99  --prep_unflatten                        true
% 3.01/0.99  --prep_res_sim                          true
% 3.01/0.99  --prep_upred                            true
% 3.01/0.99  --prep_sem_filter                       exhaustive
% 3.01/0.99  --prep_sem_filter_out                   false
% 3.01/0.99  --pred_elim                             true
% 3.01/0.99  --res_sim_input                         true
% 3.01/0.99  --eq_ax_congr_red                       true
% 3.01/0.99  --pure_diseq_elim                       true
% 3.01/0.99  --brand_transform                       false
% 3.01/0.99  --non_eq_to_eq                          false
% 3.01/0.99  --prep_def_merge                        true
% 3.01/0.99  --prep_def_merge_prop_impl              false
% 3.01/0.99  --prep_def_merge_mbd                    true
% 3.01/0.99  --prep_def_merge_tr_red                 false
% 3.01/0.99  --prep_def_merge_tr_cl                  false
% 3.01/0.99  --smt_preprocessing                     true
% 3.01/0.99  --smt_ac_axioms                         fast
% 3.01/0.99  --preprocessed_out                      false
% 3.01/0.99  --preprocessed_stats                    false
% 3.01/0.99  
% 3.01/0.99  ------ Abstraction refinement Options
% 3.01/0.99  
% 3.01/0.99  --abstr_ref                             []
% 3.01/0.99  --abstr_ref_prep                        false
% 3.01/0.99  --abstr_ref_until_sat                   false
% 3.01/0.99  --abstr_ref_sig_restrict                funpre
% 3.01/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.01/0.99  --abstr_ref_under                       []
% 3.01/0.99  
% 3.01/0.99  ------ SAT Options
% 3.01/0.99  
% 3.01/0.99  --sat_mode                              false
% 3.01/0.99  --sat_fm_restart_options                ""
% 3.01/0.99  --sat_gr_def                            false
% 3.01/0.99  --sat_epr_types                         true
% 3.01/0.99  --sat_non_cyclic_types                  false
% 3.01/0.99  --sat_finite_models                     false
% 3.01/0.99  --sat_fm_lemmas                         false
% 3.01/0.99  --sat_fm_prep                           false
% 3.01/0.99  --sat_fm_uc_incr                        true
% 3.01/0.99  --sat_out_model                         small
% 3.01/0.99  --sat_out_clauses                       false
% 3.01/0.99  
% 3.01/0.99  ------ QBF Options
% 3.01/0.99  
% 3.01/0.99  --qbf_mode                              false
% 3.01/0.99  --qbf_elim_univ                         false
% 3.01/0.99  --qbf_dom_inst                          none
% 3.01/0.99  --qbf_dom_pre_inst                      false
% 3.01/0.99  --qbf_sk_in                             false
% 3.01/0.99  --qbf_pred_elim                         true
% 3.01/0.99  --qbf_split                             512
% 3.01/0.99  
% 3.01/0.99  ------ BMC1 Options
% 3.01/0.99  
% 3.01/0.99  --bmc1_incremental                      false
% 3.01/0.99  --bmc1_axioms                           reachable_all
% 3.01/0.99  --bmc1_min_bound                        0
% 3.01/0.99  --bmc1_max_bound                        -1
% 3.01/0.99  --bmc1_max_bound_default                -1
% 3.01/0.99  --bmc1_symbol_reachability              true
% 3.01/0.99  --bmc1_property_lemmas                  false
% 3.01/0.99  --bmc1_k_induction                      false
% 3.01/0.99  --bmc1_non_equiv_states                 false
% 3.01/0.99  --bmc1_deadlock                         false
% 3.01/0.99  --bmc1_ucm                              false
% 3.01/0.99  --bmc1_add_unsat_core                   none
% 3.01/0.99  --bmc1_unsat_core_children              false
% 3.01/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.01/0.99  --bmc1_out_stat                         full
% 3.01/0.99  --bmc1_ground_init                      false
% 3.01/0.99  --bmc1_pre_inst_next_state              false
% 3.01/0.99  --bmc1_pre_inst_state                   false
% 3.01/0.99  --bmc1_pre_inst_reach_state             false
% 3.01/0.99  --bmc1_out_unsat_core                   false
% 3.01/0.99  --bmc1_aig_witness_out                  false
% 3.01/0.99  --bmc1_verbose                          false
% 3.01/0.99  --bmc1_dump_clauses_tptp                false
% 3.01/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.01/0.99  --bmc1_dump_file                        -
% 3.01/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.01/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.01/0.99  --bmc1_ucm_extend_mode                  1
% 3.01/0.99  --bmc1_ucm_init_mode                    2
% 3.01/0.99  --bmc1_ucm_cone_mode                    none
% 3.01/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.01/0.99  --bmc1_ucm_relax_model                  4
% 3.01/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.01/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.01/0.99  --bmc1_ucm_layered_model                none
% 3.01/0.99  --bmc1_ucm_max_lemma_size               10
% 3.01/0.99  
% 3.01/0.99  ------ AIG Options
% 3.01/0.99  
% 3.01/0.99  --aig_mode                              false
% 3.01/0.99  
% 3.01/0.99  ------ Instantiation Options
% 3.01/0.99  
% 3.01/0.99  --instantiation_flag                    true
% 3.01/0.99  --inst_sos_flag                         false
% 3.01/0.99  --inst_sos_phase                        true
% 3.01/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.01/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.01/0.99  --inst_lit_sel_side                     num_symb
% 3.01/0.99  --inst_solver_per_active                1400
% 3.01/0.99  --inst_solver_calls_frac                1.
% 3.01/0.99  --inst_passive_queue_type               priority_queues
% 3.01/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.01/0.99  --inst_passive_queues_freq              [25;2]
% 3.01/0.99  --inst_dismatching                      true
% 3.01/0.99  --inst_eager_unprocessed_to_passive     true
% 3.01/0.99  --inst_prop_sim_given                   true
% 3.01/0.99  --inst_prop_sim_new                     false
% 3.01/0.99  --inst_subs_new                         false
% 3.01/0.99  --inst_eq_res_simp                      false
% 3.01/0.99  --inst_subs_given                       false
% 3.01/0.99  --inst_orphan_elimination               true
% 3.01/0.99  --inst_learning_loop_flag               true
% 3.01/0.99  --inst_learning_start                   3000
% 3.01/0.99  --inst_learning_factor                  2
% 3.01/0.99  --inst_start_prop_sim_after_learn       3
% 3.01/0.99  --inst_sel_renew                        solver
% 3.01/0.99  --inst_lit_activity_flag                true
% 3.01/0.99  --inst_restr_to_given                   false
% 3.01/0.99  --inst_activity_threshold               500
% 3.01/0.99  --inst_out_proof                        true
% 3.01/0.99  
% 3.01/0.99  ------ Resolution Options
% 3.01/0.99  
% 3.01/0.99  --resolution_flag                       true
% 3.01/0.99  --res_lit_sel                           adaptive
% 3.01/0.99  --res_lit_sel_side                      none
% 3.01/0.99  --res_ordering                          kbo
% 3.01/0.99  --res_to_prop_solver                    active
% 3.01/0.99  --res_prop_simpl_new                    false
% 3.01/0.99  --res_prop_simpl_given                  true
% 3.01/0.99  --res_passive_queue_type                priority_queues
% 3.01/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.01/1.00  --res_passive_queues_freq               [15;5]
% 3.01/1.00  --res_forward_subs                      full
% 3.01/1.00  --res_backward_subs                     full
% 3.01/1.00  --res_forward_subs_resolution           true
% 3.01/1.00  --res_backward_subs_resolution          true
% 3.01/1.00  --res_orphan_elimination                true
% 3.01/1.00  --res_time_limit                        2.
% 3.01/1.00  --res_out_proof                         true
% 3.01/1.00  
% 3.01/1.00  ------ Superposition Options
% 3.01/1.00  
% 3.01/1.00  --superposition_flag                    true
% 3.01/1.00  --sup_passive_queue_type                priority_queues
% 3.01/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.01/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.01/1.00  --demod_completeness_check              fast
% 3.01/1.00  --demod_use_ground                      true
% 3.01/1.00  --sup_to_prop_solver                    passive
% 3.01/1.00  --sup_prop_simpl_new                    true
% 3.01/1.00  --sup_prop_simpl_given                  true
% 3.01/1.00  --sup_fun_splitting                     false
% 3.01/1.00  --sup_smt_interval                      50000
% 3.01/1.00  
% 3.01/1.00  ------ Superposition Simplification Setup
% 3.01/1.00  
% 3.01/1.00  --sup_indices_passive                   []
% 3.01/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.01/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.00  --sup_full_bw                           [BwDemod]
% 3.01/1.00  --sup_immed_triv                        [TrivRules]
% 3.01/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.01/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.00  --sup_immed_bw_main                     []
% 3.01/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.01/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/1.00  
% 3.01/1.00  ------ Combination Options
% 3.01/1.00  
% 3.01/1.00  --comb_res_mult                         3
% 3.01/1.00  --comb_sup_mult                         2
% 3.01/1.00  --comb_inst_mult                        10
% 3.01/1.00  
% 3.01/1.00  ------ Debug Options
% 3.01/1.00  
% 3.01/1.00  --dbg_backtrace                         false
% 3.01/1.00  --dbg_dump_prop_clauses                 false
% 3.01/1.00  --dbg_dump_prop_clauses_file            -
% 3.01/1.00  --dbg_out_stat                          false
% 3.01/1.00  ------ Parsing...
% 3.01/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.01/1.00  
% 3.01/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.01/1.00  
% 3.01/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.01/1.00  
% 3.01/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.01/1.00  ------ Proving...
% 3.01/1.00  ------ Problem Properties 
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  clauses                                 23
% 3.01/1.00  conjectures                             4
% 3.01/1.00  EPR                                     9
% 3.01/1.00  Horn                                    18
% 3.01/1.00  unary                                   7
% 3.01/1.00  binary                                  4
% 3.01/1.00  lits                                    66
% 3.01/1.00  lits eq                                 12
% 3.01/1.00  fd_pure                                 0
% 3.01/1.00  fd_pseudo                               0
% 3.01/1.00  fd_cond                                 0
% 3.01/1.00  fd_pseudo_cond                          2
% 3.01/1.00  AC symbols                              0
% 3.01/1.00  
% 3.01/1.00  ------ Schedule dynamic 5 is on 
% 3.01/1.00  
% 3.01/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  ------ 
% 3.01/1.00  Current options:
% 3.01/1.00  ------ 
% 3.01/1.00  
% 3.01/1.00  ------ Input Options
% 3.01/1.00  
% 3.01/1.00  --out_options                           all
% 3.01/1.00  --tptp_safe_out                         true
% 3.01/1.00  --problem_path                          ""
% 3.01/1.00  --include_path                          ""
% 3.01/1.00  --clausifier                            res/vclausify_rel
% 3.01/1.00  --clausifier_options                    --mode clausify
% 3.01/1.00  --stdin                                 false
% 3.01/1.00  --stats_out                             all
% 3.01/1.00  
% 3.01/1.00  ------ General Options
% 3.01/1.00  
% 3.01/1.00  --fof                                   false
% 3.01/1.00  --time_out_real                         305.
% 3.01/1.00  --time_out_virtual                      -1.
% 3.01/1.00  --symbol_type_check                     false
% 3.01/1.00  --clausify_out                          false
% 3.01/1.00  --sig_cnt_out                           false
% 3.01/1.00  --trig_cnt_out                          false
% 3.01/1.00  --trig_cnt_out_tolerance                1.
% 3.01/1.00  --trig_cnt_out_sk_spl                   false
% 3.01/1.00  --abstr_cl_out                          false
% 3.01/1.00  
% 3.01/1.00  ------ Global Options
% 3.01/1.00  
% 3.01/1.00  --schedule                              default
% 3.01/1.00  --add_important_lit                     false
% 3.01/1.00  --prop_solver_per_cl                    1000
% 3.01/1.00  --min_unsat_core                        false
% 3.01/1.00  --soft_assumptions                      false
% 3.01/1.00  --soft_lemma_size                       3
% 3.01/1.00  --prop_impl_unit_size                   0
% 3.01/1.00  --prop_impl_unit                        []
% 3.01/1.00  --share_sel_clauses                     true
% 3.01/1.00  --reset_solvers                         false
% 3.01/1.00  --bc_imp_inh                            [conj_cone]
% 3.01/1.00  --conj_cone_tolerance                   3.
% 3.01/1.00  --extra_neg_conj                        none
% 3.01/1.00  --large_theory_mode                     true
% 3.01/1.00  --prolific_symb_bound                   200
% 3.01/1.00  --lt_threshold                          2000
% 3.01/1.00  --clause_weak_htbl                      true
% 3.01/1.00  --gc_record_bc_elim                     false
% 3.01/1.00  
% 3.01/1.00  ------ Preprocessing Options
% 3.01/1.00  
% 3.01/1.00  --preprocessing_flag                    true
% 3.01/1.00  --time_out_prep_mult                    0.1
% 3.01/1.00  --splitting_mode                        input
% 3.01/1.00  --splitting_grd                         true
% 3.01/1.00  --splitting_cvd                         false
% 3.01/1.00  --splitting_cvd_svl                     false
% 3.01/1.00  --splitting_nvd                         32
% 3.01/1.00  --sub_typing                            true
% 3.01/1.00  --prep_gs_sim                           true
% 3.01/1.00  --prep_unflatten                        true
% 3.01/1.00  --prep_res_sim                          true
% 3.01/1.00  --prep_upred                            true
% 3.01/1.00  --prep_sem_filter                       exhaustive
% 3.01/1.00  --prep_sem_filter_out                   false
% 3.01/1.00  --pred_elim                             true
% 3.01/1.00  --res_sim_input                         true
% 3.01/1.00  --eq_ax_congr_red                       true
% 3.01/1.00  --pure_diseq_elim                       true
% 3.01/1.00  --brand_transform                       false
% 3.01/1.00  --non_eq_to_eq                          false
% 3.01/1.00  --prep_def_merge                        true
% 3.01/1.00  --prep_def_merge_prop_impl              false
% 3.01/1.00  --prep_def_merge_mbd                    true
% 3.01/1.00  --prep_def_merge_tr_red                 false
% 3.01/1.00  --prep_def_merge_tr_cl                  false
% 3.01/1.00  --smt_preprocessing                     true
% 3.01/1.00  --smt_ac_axioms                         fast
% 3.01/1.00  --preprocessed_out                      false
% 3.01/1.00  --preprocessed_stats                    false
% 3.01/1.00  
% 3.01/1.00  ------ Abstraction refinement Options
% 3.01/1.00  
% 3.01/1.00  --abstr_ref                             []
% 3.01/1.00  --abstr_ref_prep                        false
% 3.01/1.00  --abstr_ref_until_sat                   false
% 3.01/1.00  --abstr_ref_sig_restrict                funpre
% 3.01/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.01/1.00  --abstr_ref_under                       []
% 3.01/1.00  
% 3.01/1.00  ------ SAT Options
% 3.01/1.00  
% 3.01/1.00  --sat_mode                              false
% 3.01/1.00  --sat_fm_restart_options                ""
% 3.01/1.00  --sat_gr_def                            false
% 3.01/1.00  --sat_epr_types                         true
% 3.01/1.00  --sat_non_cyclic_types                  false
% 3.01/1.00  --sat_finite_models                     false
% 3.01/1.00  --sat_fm_lemmas                         false
% 3.01/1.00  --sat_fm_prep                           false
% 3.01/1.00  --sat_fm_uc_incr                        true
% 3.01/1.00  --sat_out_model                         small
% 3.01/1.00  --sat_out_clauses                       false
% 3.01/1.00  
% 3.01/1.00  ------ QBF Options
% 3.01/1.00  
% 3.01/1.00  --qbf_mode                              false
% 3.01/1.00  --qbf_elim_univ                         false
% 3.01/1.00  --qbf_dom_inst                          none
% 3.01/1.00  --qbf_dom_pre_inst                      false
% 3.01/1.00  --qbf_sk_in                             false
% 3.01/1.00  --qbf_pred_elim                         true
% 3.01/1.00  --qbf_split                             512
% 3.01/1.00  
% 3.01/1.00  ------ BMC1 Options
% 3.01/1.00  
% 3.01/1.00  --bmc1_incremental                      false
% 3.01/1.00  --bmc1_axioms                           reachable_all
% 3.01/1.00  --bmc1_min_bound                        0
% 3.01/1.00  --bmc1_max_bound                        -1
% 3.01/1.00  --bmc1_max_bound_default                -1
% 3.01/1.00  --bmc1_symbol_reachability              true
% 3.01/1.00  --bmc1_property_lemmas                  false
% 3.01/1.00  --bmc1_k_induction                      false
% 3.01/1.00  --bmc1_non_equiv_states                 false
% 3.01/1.00  --bmc1_deadlock                         false
% 3.01/1.00  --bmc1_ucm                              false
% 3.01/1.00  --bmc1_add_unsat_core                   none
% 3.01/1.00  --bmc1_unsat_core_children              false
% 3.01/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.01/1.00  --bmc1_out_stat                         full
% 3.01/1.00  --bmc1_ground_init                      false
% 3.01/1.00  --bmc1_pre_inst_next_state              false
% 3.01/1.00  --bmc1_pre_inst_state                   false
% 3.01/1.00  --bmc1_pre_inst_reach_state             false
% 3.01/1.00  --bmc1_out_unsat_core                   false
% 3.01/1.00  --bmc1_aig_witness_out                  false
% 3.01/1.00  --bmc1_verbose                          false
% 3.01/1.00  --bmc1_dump_clauses_tptp                false
% 3.01/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.01/1.00  --bmc1_dump_file                        -
% 3.01/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.01/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.01/1.00  --bmc1_ucm_extend_mode                  1
% 3.01/1.00  --bmc1_ucm_init_mode                    2
% 3.01/1.00  --bmc1_ucm_cone_mode                    none
% 3.01/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.01/1.00  --bmc1_ucm_relax_model                  4
% 3.01/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.01/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.01/1.00  --bmc1_ucm_layered_model                none
% 3.01/1.00  --bmc1_ucm_max_lemma_size               10
% 3.01/1.00  
% 3.01/1.00  ------ AIG Options
% 3.01/1.00  
% 3.01/1.00  --aig_mode                              false
% 3.01/1.00  
% 3.01/1.00  ------ Instantiation Options
% 3.01/1.00  
% 3.01/1.00  --instantiation_flag                    true
% 3.01/1.00  --inst_sos_flag                         false
% 3.01/1.00  --inst_sos_phase                        true
% 3.01/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.01/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.01/1.00  --inst_lit_sel_side                     none
% 3.01/1.00  --inst_solver_per_active                1400
% 3.01/1.00  --inst_solver_calls_frac                1.
% 3.01/1.00  --inst_passive_queue_type               priority_queues
% 3.01/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.01/1.00  --inst_passive_queues_freq              [25;2]
% 3.01/1.00  --inst_dismatching                      true
% 3.01/1.00  --inst_eager_unprocessed_to_passive     true
% 3.01/1.00  --inst_prop_sim_given                   true
% 3.01/1.00  --inst_prop_sim_new                     false
% 3.01/1.00  --inst_subs_new                         false
% 3.01/1.00  --inst_eq_res_simp                      false
% 3.01/1.00  --inst_subs_given                       false
% 3.01/1.00  --inst_orphan_elimination               true
% 3.01/1.00  --inst_learning_loop_flag               true
% 3.01/1.00  --inst_learning_start                   3000
% 3.01/1.00  --inst_learning_factor                  2
% 3.01/1.00  --inst_start_prop_sim_after_learn       3
% 3.01/1.00  --inst_sel_renew                        solver
% 3.01/1.00  --inst_lit_activity_flag                true
% 3.01/1.00  --inst_restr_to_given                   false
% 3.01/1.00  --inst_activity_threshold               500
% 3.01/1.00  --inst_out_proof                        true
% 3.01/1.00  
% 3.01/1.00  ------ Resolution Options
% 3.01/1.00  
% 3.01/1.00  --resolution_flag                       false
% 3.01/1.00  --res_lit_sel                           adaptive
% 3.01/1.00  --res_lit_sel_side                      none
% 3.01/1.00  --res_ordering                          kbo
% 3.01/1.00  --res_to_prop_solver                    active
% 3.01/1.00  --res_prop_simpl_new                    false
% 3.01/1.00  --res_prop_simpl_given                  true
% 3.01/1.00  --res_passive_queue_type                priority_queues
% 3.01/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.01/1.00  --res_passive_queues_freq               [15;5]
% 3.01/1.00  --res_forward_subs                      full
% 3.01/1.00  --res_backward_subs                     full
% 3.01/1.00  --res_forward_subs_resolution           true
% 3.01/1.00  --res_backward_subs_resolution          true
% 3.01/1.00  --res_orphan_elimination                true
% 3.01/1.00  --res_time_limit                        2.
% 3.01/1.00  --res_out_proof                         true
% 3.01/1.00  
% 3.01/1.00  ------ Superposition Options
% 3.01/1.00  
% 3.01/1.00  --superposition_flag                    true
% 3.01/1.00  --sup_passive_queue_type                priority_queues
% 3.01/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.01/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.01/1.00  --demod_completeness_check              fast
% 3.01/1.00  --demod_use_ground                      true
% 3.01/1.00  --sup_to_prop_solver                    passive
% 3.01/1.00  --sup_prop_simpl_new                    true
% 3.01/1.00  --sup_prop_simpl_given                  true
% 3.01/1.00  --sup_fun_splitting                     false
% 3.01/1.00  --sup_smt_interval                      50000
% 3.01/1.00  
% 3.01/1.00  ------ Superposition Simplification Setup
% 3.01/1.00  
% 3.01/1.00  --sup_indices_passive                   []
% 3.01/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.01/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.00  --sup_full_bw                           [BwDemod]
% 3.01/1.00  --sup_immed_triv                        [TrivRules]
% 3.01/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.01/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.00  --sup_immed_bw_main                     []
% 3.01/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.01/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/1.00  
% 3.01/1.00  ------ Combination Options
% 3.01/1.00  
% 3.01/1.00  --comb_res_mult                         3
% 3.01/1.00  --comb_sup_mult                         2
% 3.01/1.00  --comb_inst_mult                        10
% 3.01/1.00  
% 3.01/1.00  ------ Debug Options
% 3.01/1.00  
% 3.01/1.00  --dbg_backtrace                         false
% 3.01/1.00  --dbg_dump_prop_clauses                 false
% 3.01/1.00  --dbg_dump_prop_clauses_file            -
% 3.01/1.00  --dbg_out_stat                          false
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  ------ Proving...
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  % SZS status Theorem for theBenchmark.p
% 3.01/1.00  
% 3.01/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.01/1.00  
% 3.01/1.00  fof(f2,axiom,(
% 3.01/1.00    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f18,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.01/1.00    inference(ennf_transformation,[],[f2])).
% 3.01/1.00  
% 3.01/1.00  fof(f19,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.01/1.00    inference(flattening,[],[f18])).
% 3.01/1.00  
% 3.01/1.00  fof(f48,plain,(
% 3.01/1.00    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f19])).
% 3.01/1.00  
% 3.01/1.00  fof(f11,axiom,(
% 3.01/1.00    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => k1_wellord1(k1_wellord2(X1),X0) = X0)))),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f32,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : ((k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.01/1.00    inference(ennf_transformation,[],[f11])).
% 3.01/1.00  
% 3.01/1.00  fof(f33,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.01/1.00    inference(flattening,[],[f32])).
% 3.01/1.00  
% 3.01/1.00  fof(f63,plain,(
% 3.01/1.00    ( ! [X0,X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f33])).
% 3.01/1.00  
% 3.01/1.00  fof(f14,conjecture,(
% 3.01/1.00    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f15,negated_conjecture,(
% 3.01/1.00    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 3.01/1.00    inference(negated_conjecture,[],[f14])).
% 3.01/1.00  
% 3.01/1.00  fof(f36,plain,(
% 3.01/1.00    ? [X0] : (? [X1] : ((X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.01/1.00    inference(ennf_transformation,[],[f15])).
% 3.01/1.00  
% 3.01/1.00  fof(f37,plain,(
% 3.01/1.00    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.01/1.00    inference(flattening,[],[f36])).
% 3.01/1.00  
% 3.01/1.00  fof(f44,plain,(
% 3.01/1.00    ( ! [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) => (sK3 != X0 & r4_wellord1(k1_wellord2(X0),k1_wellord2(sK3)) & v3_ordinal1(sK3))) )),
% 3.01/1.00    introduced(choice_axiom,[])).
% 3.01/1.00  
% 3.01/1.00  fof(f43,plain,(
% 3.01/1.00    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : (sK2 != X1 & r4_wellord1(k1_wellord2(sK2),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK2))),
% 3.01/1.00    introduced(choice_axiom,[])).
% 3.01/1.00  
% 3.01/1.00  fof(f45,plain,(
% 3.01/1.00    (sK2 != sK3 & r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) & v3_ordinal1(sK3)) & v3_ordinal1(sK2)),
% 3.01/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f37,f44,f43])).
% 3.01/1.00  
% 3.01/1.00  fof(f66,plain,(
% 3.01/1.00    v3_ordinal1(sK2)),
% 3.01/1.00    inference(cnf_transformation,[],[f45])).
% 3.01/1.00  
% 3.01/1.00  fof(f67,plain,(
% 3.01/1.00    v3_ordinal1(sK3)),
% 3.01/1.00    inference(cnf_transformation,[],[f45])).
% 3.01/1.00  
% 3.01/1.00  fof(f3,axiom,(
% 3.01/1.00    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1))))),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f20,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : ((r2_xboole_0(X1,X0) | X0 = X1 | r2_xboole_0(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.01/1.00    inference(ennf_transformation,[],[f3])).
% 3.01/1.00  
% 3.01/1.00  fof(f21,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (r2_xboole_0(X1,X0) | X0 = X1 | r2_xboole_0(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.01/1.00    inference(flattening,[],[f20])).
% 3.01/1.00  
% 3.01/1.00  fof(f49,plain,(
% 3.01/1.00    ( ! [X0,X1] : (r2_xboole_0(X1,X0) | X0 = X1 | r2_xboole_0(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f21])).
% 3.01/1.00  
% 3.01/1.00  fof(f1,axiom,(
% 3.01/1.00    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f16,plain,(
% 3.01/1.00    ! [X0,X1] : (r2_xboole_0(X0,X1) => (X0 != X1 & r1_tarski(X0,X1)))),
% 3.01/1.00    inference(unused_predicate_definition_removal,[],[f1])).
% 3.01/1.00  
% 3.01/1.00  fof(f17,plain,(
% 3.01/1.00    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1))),
% 3.01/1.00    inference(ennf_transformation,[],[f16])).
% 3.01/1.00  
% 3.01/1.00  fof(f46,plain,(
% 3.01/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f17])).
% 3.01/1.00  
% 3.01/1.00  fof(f13,axiom,(
% 3.01/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0))),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f35,plain,(
% 3.01/1.00    ! [X0,X1] : (k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) | ~r1_tarski(X0,X1))),
% 3.01/1.00    inference(ennf_transformation,[],[f13])).
% 3.01/1.00  
% 3.01/1.00  fof(f65,plain,(
% 3.01/1.00    ( ! [X0,X1] : (k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) | ~r1_tarski(X0,X1)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f35])).
% 3.01/1.00  
% 3.01/1.00  fof(f69,plain,(
% 3.01/1.00    sK2 != sK3),
% 3.01/1.00    inference(cnf_transformation,[],[f45])).
% 3.01/1.00  
% 3.01/1.00  fof(f47,plain,(
% 3.01/1.00    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f17])).
% 3.01/1.00  
% 3.01/1.00  fof(f70,plain,(
% 3.01/1.00    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 3.01/1.00    inference(equality_resolution,[],[f47])).
% 3.01/1.00  
% 3.01/1.00  fof(f10,axiom,(
% 3.01/1.00    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f62,plain,(
% 3.01/1.00    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 3.01/1.00    inference(cnf_transformation,[],[f10])).
% 3.01/1.00  
% 3.01/1.00  fof(f5,axiom,(
% 3.01/1.00    ! [X0] : (v1_relat_1(X0) => k2_wellord1(X0,k3_relat_1(X0)) = X0)),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f23,plain,(
% 3.01/1.00    ! [X0] : (k2_wellord1(X0,k3_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 3.01/1.00    inference(ennf_transformation,[],[f5])).
% 3.01/1.00  
% 3.01/1.00  fof(f51,plain,(
% 3.01/1.00    ( ! [X0] : (k2_wellord1(X0,k3_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f23])).
% 3.01/1.00  
% 3.01/1.00  fof(f9,axiom,(
% 3.01/1.00    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f30,plain,(
% 3.01/1.00    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 3.01/1.00    inference(ennf_transformation,[],[f9])).
% 3.01/1.00  
% 3.01/1.00  fof(f31,plain,(
% 3.01/1.00    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 3.01/1.00    inference(flattening,[],[f30])).
% 3.01/1.00  
% 3.01/1.00  fof(f38,plain,(
% 3.01/1.00    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 3.01/1.00    inference(nnf_transformation,[],[f31])).
% 3.01/1.00  
% 3.01/1.00  fof(f39,plain,(
% 3.01/1.00    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 3.01/1.00    inference(flattening,[],[f38])).
% 3.01/1.00  
% 3.01/1.00  fof(f40,plain,(
% 3.01/1.00    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 3.01/1.00    inference(rectify,[],[f39])).
% 3.01/1.00  
% 3.01/1.00  fof(f41,plain,(
% 3.01/1.00    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK0(X0,X1),sK1(X0,X1)) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & (r1_tarski(sK0(X0,X1),sK1(X0,X1)) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & r2_hidden(sK1(X0,X1),X0) & r2_hidden(sK0(X0,X1),X0)))),
% 3.01/1.00    introduced(choice_axiom,[])).
% 3.01/1.00  
% 3.01/1.00  fof(f42,plain,(
% 3.01/1.00    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK0(X0,X1),sK1(X0,X1)) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & (r1_tarski(sK0(X0,X1),sK1(X0,X1)) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & r2_hidden(sK1(X0,X1),X0) & r2_hidden(sK0(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 3.01/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f41])).
% 3.01/1.00  
% 3.01/1.00  fof(f55,plain,(
% 3.01/1.00    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f42])).
% 3.01/1.00  
% 3.01/1.00  fof(f77,plain,(
% 3.01/1.00    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 3.01/1.00    inference(equality_resolution,[],[f55])).
% 3.01/1.00  
% 3.01/1.00  fof(f4,axiom,(
% 3.01/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0))),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f22,plain,(
% 3.01/1.00    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2))),
% 3.01/1.00    inference(ennf_transformation,[],[f4])).
% 3.01/1.00  
% 3.01/1.00  fof(f50,plain,(
% 3.01/1.00    ( ! [X2,X0,X1] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f22])).
% 3.01/1.00  
% 3.01/1.00  fof(f8,axiom,(
% 3.01/1.00    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f28,plain,(
% 3.01/1.00    ! [X0] : ((! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 3.01/1.00    inference(ennf_transformation,[],[f8])).
% 3.01/1.00  
% 3.01/1.00  fof(f29,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 3.01/1.00    inference(flattening,[],[f28])).
% 3.01/1.00  
% 3.01/1.00  fof(f54,plain,(
% 3.01/1.00    ( ! [X0,X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0)) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f29])).
% 3.01/1.00  
% 3.01/1.00  fof(f12,axiom,(
% 3.01/1.00    ! [X0] : (v3_ordinal1(X0) => v2_wellord1(k1_wellord2(X0)))),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f34,plain,(
% 3.01/1.00    ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0))),
% 3.01/1.00    inference(ennf_transformation,[],[f12])).
% 3.01/1.00  
% 3.01/1.00  fof(f64,plain,(
% 3.01/1.00    ( ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f34])).
% 3.01/1.00  
% 3.01/1.00  fof(f68,plain,(
% 3.01/1.00    r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))),
% 3.01/1.00    inference(cnf_transformation,[],[f45])).
% 3.01/1.00  
% 3.01/1.00  fof(f6,axiom,(
% 3.01/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f24,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : ((r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.01/1.00    inference(ennf_transformation,[],[f6])).
% 3.01/1.00  
% 3.01/1.00  fof(f25,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.01/1.00    inference(flattening,[],[f24])).
% 3.01/1.00  
% 3.01/1.00  fof(f52,plain,(
% 3.01/1.00    ( ! [X0,X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f25])).
% 3.01/1.00  
% 3.01/1.00  fof(f7,axiom,(
% 3.01/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ((r4_wellord1(X1,X2) & r4_wellord1(X0,X1)) => r4_wellord1(X0,X2)))))),
% 3.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f26,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (! [X2] : ((r4_wellord1(X0,X2) | (~r4_wellord1(X1,X2) | ~r4_wellord1(X0,X1))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.01/1.00    inference(ennf_transformation,[],[f7])).
% 3.01/1.00  
% 3.01/1.00  fof(f27,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (! [X2] : (r4_wellord1(X0,X2) | ~r4_wellord1(X1,X2) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.01/1.00    inference(flattening,[],[f26])).
% 3.01/1.00  
% 3.01/1.00  fof(f53,plain,(
% 3.01/1.00    ( ! [X2,X0,X1] : (r4_wellord1(X0,X2) | ~r4_wellord1(X1,X2) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f27])).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2,plain,
% 3.01/1.00      ( r2_hidden(X0,X1)
% 3.01/1.00      | r2_hidden(X1,X0)
% 3.01/1.00      | ~ v3_ordinal1(X1)
% 3.01/1.00      | ~ v3_ordinal1(X0)
% 3.01/1.00      | X0 = X1 ),
% 3.01/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1251,plain,
% 3.01/1.00      ( X0 = X1
% 3.01/1.00      | r2_hidden(X0,X1) = iProver_top
% 3.01/1.00      | r2_hidden(X1,X0) = iProver_top
% 3.01/1.00      | v3_ordinal1(X0) != iProver_top
% 3.01/1.00      | v3_ordinal1(X1) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_17,plain,
% 3.01/1.00      ( ~ r2_hidden(X0,X1)
% 3.01/1.00      | ~ v3_ordinal1(X1)
% 3.01/1.00      | ~ v3_ordinal1(X0)
% 3.01/1.00      | k1_wellord1(k1_wellord2(X1),X0) = X0 ),
% 3.01/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1238,plain,
% 3.01/1.00      ( k1_wellord1(k1_wellord2(X0),X1) = X1
% 3.01/1.00      | r2_hidden(X1,X0) != iProver_top
% 3.01/1.00      | v3_ordinal1(X1) != iProver_top
% 3.01/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2382,plain,
% 3.01/1.00      ( X0 = X1
% 3.01/1.00      | k1_wellord1(k1_wellord2(X0),X1) = X1
% 3.01/1.00      | r2_hidden(X0,X1) = iProver_top
% 3.01/1.00      | v3_ordinal1(X1) != iProver_top
% 3.01/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_1251,c_1238]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_23,negated_conjecture,
% 3.01/1.00      ( v3_ordinal1(sK2) ),
% 3.01/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1234,plain,
% 3.01/1.00      ( v3_ordinal1(sK2) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_22,negated_conjecture,
% 3.01/1.00      ( v3_ordinal1(sK3) ),
% 3.01/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1235,plain,
% 3.01/1.00      ( v3_ordinal1(sK3) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3,plain,
% 3.01/1.00      ( r2_xboole_0(X0,X1)
% 3.01/1.00      | r2_xboole_0(X1,X0)
% 3.01/1.00      | ~ v3_ordinal1(X1)
% 3.01/1.00      | ~ v3_ordinal1(X0)
% 3.01/1.00      | X0 = X1 ),
% 3.01/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1250,plain,
% 3.01/1.00      ( X0 = X1
% 3.01/1.00      | r2_xboole_0(X0,X1) = iProver_top
% 3.01/1.00      | r2_xboole_0(X1,X0) = iProver_top
% 3.01/1.00      | v3_ordinal1(X0) != iProver_top
% 3.01/1.00      | v3_ordinal1(X1) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1,plain,
% 3.01/1.00      ( r1_tarski(X0,X1) | ~ r2_xboole_0(X0,X1) ),
% 3.01/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1252,plain,
% 3.01/1.00      ( r1_tarski(X0,X1) = iProver_top
% 3.01/1.00      | r2_xboole_0(X0,X1) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2347,plain,
% 3.01/1.00      ( X0 = X1
% 3.01/1.00      | r1_tarski(X0,X1) = iProver_top
% 3.01/1.00      | r2_xboole_0(X1,X0) = iProver_top
% 3.01/1.00      | v3_ordinal1(X1) != iProver_top
% 3.01/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_1250,c_1252]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_19,plain,
% 3.01/1.00      ( ~ r1_tarski(X0,X1)
% 3.01/1.00      | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ),
% 3.01/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1237,plain,
% 3.01/1.00      ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 3.01/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2954,plain,
% 3.01/1.00      ( X0 = X1
% 3.01/1.00      | k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 3.01/1.00      | r2_xboole_0(X0,X1) = iProver_top
% 3.01/1.00      | v3_ordinal1(X1) != iProver_top
% 3.01/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_2347,c_1237]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3187,plain,
% 3.01/1.00      ( X0 = X1
% 3.01/1.00      | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
% 3.01/1.00      | r1_tarski(X1,X0) = iProver_top
% 3.01/1.00      | v3_ordinal1(X1) != iProver_top
% 3.01/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_2954,c_1252]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3595,plain,
% 3.01/1.00      ( X0 = X1
% 3.01/1.00      | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
% 3.01/1.00      | k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 3.01/1.00      | v3_ordinal1(X1) != iProver_top
% 3.01/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_3187,c_1237]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3700,plain,
% 3.01/1.00      ( k2_wellord1(k1_wellord2(X0),sK3) = k1_wellord2(sK3)
% 3.01/1.00      | k2_wellord1(k1_wellord2(sK3),X0) = k1_wellord2(X0)
% 3.01/1.00      | sK3 = X0
% 3.01/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_1235,c_3595]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3797,plain,
% 3.01/1.00      ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
% 3.01/1.00      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.01/1.00      | sK3 = sK2 ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_1234,c_3700]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_24,plain,
% 3.01/1.00      ( v3_ordinal1(sK2) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_20,negated_conjecture,
% 3.01/1.00      ( sK2 != sK3 ),
% 3.01/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_72,plain,
% 3.01/1.00      ( r2_xboole_0(sK2,sK2) | ~ v3_ordinal1(sK2) | sK2 = sK2 ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_0,plain,
% 3.01/1.00      ( ~ r2_xboole_0(X0,X0) ),
% 3.01/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_81,plain,
% 3.01/1.00      ( ~ r2_xboole_0(sK2,sK2) ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_839,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1463,plain,
% 3.01/1.00      ( sK3 != X0 | sK2 != X0 | sK2 = sK3 ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_839]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1464,plain,
% 3.01/1.00      ( sK3 != sK2 | sK2 = sK3 | sK2 != sK2 ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_1463]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3719,plain,
% 3.01/1.00      ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
% 3.01/1.00      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.01/1.00      | sK3 = sK2
% 3.01/1.00      | v3_ordinal1(sK2) != iProver_top ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_3700]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3804,plain,
% 3.01/1.00      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.01/1.00      | k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_3797,c_23,c_24,c_20,c_72,c_81,c_1464,c_3719]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3805,plain,
% 3.01/1.00      ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
% 3.01/1.00      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
% 3.01/1.00      inference(renaming,[status(thm)],[c_3804]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_16,plain,
% 3.01/1.00      ( v1_relat_1(k1_wellord2(X0)) ),
% 3.01/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1239,plain,
% 3.01/1.00      ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_5,plain,
% 3.01/1.00      ( ~ v1_relat_1(X0) | k2_wellord1(X0,k3_relat_1(X0)) = X0 ),
% 3.01/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1248,plain,
% 3.01/1.00      ( k2_wellord1(X0,k3_relat_1(X0)) = X0
% 3.01/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1530,plain,
% 3.01/1.00      ( k2_wellord1(k1_wellord2(X0),k3_relat_1(k1_wellord2(X0))) = k1_wellord2(X0) ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_1239,c_1248]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_15,plain,
% 3.01/1.00      ( ~ v1_relat_1(k1_wellord2(X0))
% 3.01/1.00      | k3_relat_1(k1_wellord2(X0)) = X0 ),
% 3.01/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_137,plain,
% 3.01/1.00      ( k3_relat_1(k1_wellord2(X0)) = X0 ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_15,c_16]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1531,plain,
% 3.01/1.00      ( k2_wellord1(k1_wellord2(X0),X0) = k1_wellord2(X0) ),
% 3.01/1.00      inference(light_normalisation,[status(thm)],[c_1530,c_137]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4,plain,
% 3.01/1.00      ( ~ v1_relat_1(X0)
% 3.01/1.00      | k2_wellord1(k2_wellord1(X0,X1),X2) = k2_wellord1(k2_wellord1(X0,X2),X1) ),
% 3.01/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1249,plain,
% 3.01/1.00      ( k2_wellord1(k2_wellord1(X0,X1),X2) = k2_wellord1(k2_wellord1(X0,X2),X1)
% 3.01/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1716,plain,
% 3.01/1.00      ( k2_wellord1(k2_wellord1(k1_wellord2(X0),X1),X2) = k2_wellord1(k2_wellord1(k1_wellord2(X0),X2),X1) ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_1239,c_1249]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2000,plain,
% 3.01/1.00      ( k2_wellord1(k2_wellord1(k1_wellord2(X0),X1),X0) = k2_wellord1(k1_wellord2(X0),X1) ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_1531,c_1716]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3808,plain,
% 3.01/1.00      ( k2_wellord1(k1_wellord2(sK2),sK3) = k2_wellord1(k1_wellord2(sK3),sK2)
% 3.01/1.00      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_3805,c_2000]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3929,plain,
% 3.01/1.00      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.01/1.00      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_3808,c_3805]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3953,plain,
% 3.01/1.00      ( k2_wellord1(k1_wellord2(sK2),sK3) = k2_wellord1(k1_wellord2(sK3),sK2)
% 3.01/1.00      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_3929,c_2000]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2380,plain,
% 3.01/1.00      ( X0 = X1
% 3.01/1.00      | k1_wellord1(k1_wellord2(X1),X0) = X0
% 3.01/1.00      | r2_hidden(X1,X0) = iProver_top
% 3.01/1.00      | v3_ordinal1(X1) != iProver_top
% 3.01/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_1251,c_1238]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3073,plain,
% 3.01/1.00      ( X0 = X1
% 3.01/1.00      | k1_wellord1(k1_wellord2(X1),X0) = X0
% 3.01/1.00      | k1_wellord1(k1_wellord2(X0),X1) = X1
% 3.01/1.00      | v3_ordinal1(X1) != iProver_top
% 3.01/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_2380,c_1238]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3323,plain,
% 3.01/1.00      ( k1_wellord1(k1_wellord2(X0),sK3) = sK3
% 3.01/1.00      | k1_wellord1(k1_wellord2(sK3),X0) = X0
% 3.01/1.00      | sK3 = X0
% 3.01/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_1235,c_3073]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3406,plain,
% 3.01/1.00      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.01/1.00      | k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.01/1.00      | sK3 = sK2 ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_1234,c_3323]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3413,plain,
% 3.01/1.00      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.01/1.00      | k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_3406,c_23,c_20,c_72,c_81,c_1464]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3414,plain,
% 3.01/1.00      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.01/1.00      | k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
% 3.01/1.00      inference(renaming,[status(thm)],[c_3413]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_8,plain,
% 3.01/1.00      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
% 3.01/1.00      | ~ r2_hidden(X1,k3_relat_1(X0))
% 3.01/1.00      | ~ v2_wellord1(X0)
% 3.01/1.00      | ~ v1_relat_1(X0) ),
% 3.01/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_18,plain,
% 3.01/1.00      ( v2_wellord1(k1_wellord2(X0)) | ~ v3_ordinal1(X0) ),
% 3.01/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_264,plain,
% 3.01/1.00      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
% 3.01/1.00      | ~ r2_hidden(X1,k3_relat_1(X0))
% 3.01/1.00      | ~ v1_relat_1(X0)
% 3.01/1.00      | ~ v3_ordinal1(X2)
% 3.01/1.00      | k1_wellord2(X2) != X0 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_18]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_265,plain,
% 3.01/1.00      ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
% 3.01/1.00      | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
% 3.01/1.00      | ~ v1_relat_1(k1_wellord2(X0))
% 3.01/1.00      | ~ v3_ordinal1(X0) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_264]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_269,plain,
% 3.01/1.00      ( ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
% 3.01/1.00      | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
% 3.01/1.00      | ~ v3_ordinal1(X0) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_265,c_16]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_270,plain,
% 3.01/1.00      ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
% 3.01/1.00      | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
% 3.01/1.00      | ~ v3_ordinal1(X0) ),
% 3.01/1.00      inference(renaming,[status(thm)],[c_269]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1233,plain,
% 3.01/1.00      ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
% 3.01/1.00      | r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) != iProver_top
% 3.01/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_270]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1332,plain,
% 3.01/1.00      ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
% 3.01/1.00      | r2_hidden(X1,X0) != iProver_top
% 3.01/1.00      | v3_ordinal1(X0) != iProver_top ),
% 3.01/1.00      inference(light_normalisation,[status(thm)],[c_1233,c_137]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3417,plain,
% 3.01/1.00      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.01/1.00      | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top
% 3.01/1.00      | r2_hidden(sK2,sK3) != iProver_top
% 3.01/1.00      | v3_ordinal1(sK3) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_3414,c_1332]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_25,plain,
% 3.01/1.00      ( v3_ordinal1(sK3) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1474,plain,
% 3.01/1.00      ( r2_hidden(sK3,sK2)
% 3.01/1.00      | r2_hidden(sK2,sK3)
% 3.01/1.00      | ~ v3_ordinal1(sK3)
% 3.01/1.00      | ~ v3_ordinal1(sK2)
% 3.01/1.00      | sK2 = sK3 ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1475,plain,
% 3.01/1.00      ( sK2 = sK3
% 3.01/1.00      | r2_hidden(sK3,sK2) = iProver_top
% 3.01/1.00      | r2_hidden(sK2,sK3) = iProver_top
% 3.01/1.00      | v3_ordinal1(sK3) != iProver_top
% 3.01/1.00      | v3_ordinal1(sK2) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_1474]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1509,plain,
% 3.01/1.00      ( ~ r2_hidden(sK3,sK2)
% 3.01/1.00      | ~ v3_ordinal1(sK3)
% 3.01/1.00      | ~ v3_ordinal1(sK2)
% 3.01/1.00      | k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1510,plain,
% 3.01/1.00      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.01/1.00      | r2_hidden(sK3,sK2) != iProver_top
% 3.01/1.00      | v3_ordinal1(sK3) != iProver_top
% 3.01/1.00      | v3_ordinal1(sK2) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_1509]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3551,plain,
% 3.01/1.00      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.01/1.00      | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_3417,c_24,c_25,c_20,c_1475,c_1510]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4223,plain,
% 3.01/1.00      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.01/1.00      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
% 3.01/1.00      | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_3953,c_3551]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_5378,plain,
% 3.01/1.00      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.01/1.00      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
% 3.01/1.00      | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK3)) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_3929,c_4223]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1661,plain,
% 3.01/1.00      ( v1_relat_1(k1_wellord2(sK3)) ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1662,plain,
% 3.01/1.00      ( v1_relat_1(k1_wellord2(sK3)) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_1661]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_21,negated_conjecture,
% 3.01/1.00      ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) ),
% 3.01/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1236,plain,
% 3.01/1.00      ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_6,plain,
% 3.01/1.00      ( ~ r4_wellord1(X0,X1)
% 3.01/1.00      | r4_wellord1(X1,X0)
% 3.01/1.00      | ~ v1_relat_1(X1)
% 3.01/1.00      | ~ v1_relat_1(X0) ),
% 3.01/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1247,plain,
% 3.01/1.00      ( r4_wellord1(X0,X1) != iProver_top
% 3.01/1.00      | r4_wellord1(X1,X0) = iProver_top
% 3.01/1.00      | v1_relat_1(X0) != iProver_top
% 3.01/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2046,plain,
% 3.01/1.00      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top
% 3.01/1.00      | v1_relat_1(k1_wellord2(sK3)) != iProver_top
% 3.01/1.00      | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_1236,c_1247]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_36,plain,
% 3.01/1.00      ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_38,plain,
% 3.01/1.00      ( v1_relat_1(k1_wellord2(sK2)) = iProver_top ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_36]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2049,plain,
% 3.01/1.00      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_2046,c_38,c_1662]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_7,plain,
% 3.01/1.00      ( ~ r4_wellord1(X0,X1)
% 3.01/1.00      | ~ r4_wellord1(X1,X2)
% 3.01/1.00      | r4_wellord1(X0,X2)
% 3.01/1.00      | ~ v1_relat_1(X2)
% 3.01/1.00      | ~ v1_relat_1(X1)
% 3.01/1.00      | ~ v1_relat_1(X0) ),
% 3.01/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1246,plain,
% 3.01/1.00      ( r4_wellord1(X0,X1) != iProver_top
% 3.01/1.00      | r4_wellord1(X1,X2) != iProver_top
% 3.01/1.00      | r4_wellord1(X0,X2) = iProver_top
% 3.01/1.00      | v1_relat_1(X0) != iProver_top
% 3.01/1.00      | v1_relat_1(X2) != iProver_top
% 3.01/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2515,plain,
% 3.01/1.00      ( r4_wellord1(k1_wellord2(sK3),X0) = iProver_top
% 3.01/1.00      | r4_wellord1(k1_wellord2(sK2),X0) != iProver_top
% 3.01/1.00      | v1_relat_1(X0) != iProver_top
% 3.01/1.00      | v1_relat_1(k1_wellord2(sK3)) != iProver_top
% 3.01/1.00      | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_2049,c_1246]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2690,plain,
% 3.01/1.00      ( r4_wellord1(k1_wellord2(sK3),X0) = iProver_top
% 3.01/1.00      | r4_wellord1(k1_wellord2(sK2),X0) != iProver_top
% 3.01/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_2515,c_38,c_1662]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2699,plain,
% 3.01/1.00      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK3)) = iProver_top
% 3.01/1.00      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_1236,c_2690]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_5871,plain,
% 3.01/1.00      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
% 3.01/1.00      | k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_5378,c_1662,c_2699]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_5872,plain,
% 3.01/1.00      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.01/1.00      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
% 3.01/1.00      inference(renaming,[status(thm)],[c_5871]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_5875,plain,
% 3.01/1.00      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
% 3.01/1.00      | r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top
% 3.01/1.00      | r2_hidden(sK3,sK2) != iProver_top
% 3.01/1.00      | v3_ordinal1(sK2) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_5872,c_1332]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_26,plain,
% 3.01/1.00      ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_848,plain,
% 3.01/1.00      ( X0 != X1 | k1_wellord2(X0) = k1_wellord2(X1) ),
% 3.01/1.00      theory(equality) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_860,plain,
% 3.01/1.00      ( k1_wellord2(sK2) = k1_wellord2(sK2) | sK2 != sK2 ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_848]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_846,plain,
% 3.01/1.00      ( ~ r4_wellord1(X0,X1) | r4_wellord1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.01/1.00      theory(equality) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1480,plain,
% 3.01/1.00      ( r4_wellord1(X0,X1)
% 3.01/1.00      | ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
% 3.01/1.00      | X1 != k1_wellord2(sK3)
% 3.01/1.00      | X0 != k1_wellord2(sK2) ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_846]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3568,plain,
% 3.01/1.00      ( r4_wellord1(X0,k2_wellord1(k1_wellord2(sK2),sK3))
% 3.01/1.00      | ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
% 3.01/1.00      | X0 != k1_wellord2(sK2)
% 3.01/1.00      | k2_wellord1(k1_wellord2(sK2),sK3) != k1_wellord2(sK3) ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_1480]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_5837,plain,
% 3.01/1.00      ( r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3))
% 3.01/1.00      | ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
% 3.01/1.00      | k2_wellord1(k1_wellord2(sK2),sK3) != k1_wellord2(sK3)
% 3.01/1.00      | k1_wellord2(sK2) != k1_wellord2(sK2) ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_3568]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_5838,plain,
% 3.01/1.00      ( k2_wellord1(k1_wellord2(sK2),sK3) != k1_wellord2(sK3)
% 3.01/1.00      | k1_wellord2(sK2) != k1_wellord2(sK2)
% 3.01/1.00      | r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) = iProver_top
% 3.01/1.00      | r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_5837]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_5878,plain,
% 3.01/1.00      ( r2_hidden(sK3,sK2) != iProver_top
% 3.01/1.00      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_5875,c_23,c_24,c_26,c_72,c_81,c_860,c_3929,c_5838]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_5879,plain,
% 3.01/1.00      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
% 3.01/1.00      | r2_hidden(sK3,sK2) != iProver_top ),
% 3.01/1.00      inference(renaming,[status(thm)],[c_5878]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_5887,plain,
% 3.01/1.00      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
% 3.01/1.00      | sK3 = sK2
% 3.01/1.00      | r2_hidden(sK2,sK3) = iProver_top
% 3.01/1.00      | v3_ordinal1(sK3) != iProver_top
% 3.01/1.00      | v3_ordinal1(sK2) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_1251,c_5879]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_6358,plain,
% 3.01/1.00      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
% 3.01/1.00      | r2_hidden(sK2,sK3) = iProver_top ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_5887,c_23,c_24,c_25,c_20,c_72,c_81,c_1464]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_6364,plain,
% 3.01/1.00      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.01/1.00      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
% 3.01/1.00      | v3_ordinal1(sK3) != iProver_top
% 3.01/1.00      | v3_ordinal1(sK2) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_6358,c_1238]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_6365,plain,
% 3.01/1.00      ( ~ v3_ordinal1(sK3)
% 3.01/1.00      | ~ v3_ordinal1(sK2)
% 3.01/1.00      | k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.01/1.00      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
% 3.01/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_6364]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_6556,plain,
% 3.01/1.00      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.01/1.00      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_6364,c_23,c_22,c_6365]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_6560,plain,
% 3.01/1.00      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
% 3.01/1.00      | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top
% 3.01/1.00      | r2_hidden(sK2,sK3) != iProver_top
% 3.01/1.00      | v3_ordinal1(sK3) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_6556,c_1332]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_6994,plain,
% 3.01/1.00      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
% 3.01/1.00      | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_6560,c_23,c_24,c_25,c_20,c_72,c_81,c_1464,c_5887]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_7001,plain,
% 3.01/1.00      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
% 3.01/1.00      | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_3953,c_6994]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4219,plain,
% 3.01/1.00      ( k2_wellord1(k2_wellord1(k1_wellord2(sK2),sK3),sK3) = k2_wellord1(k1_wellord2(sK3),sK2)
% 3.01/1.00      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_3953,c_2000]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3954,plain,
% 3.01/1.00      ( k2_wellord1(k2_wellord1(k1_wellord2(sK2),X0),sK3) = k2_wellord1(k1_wellord2(sK3),X0)
% 3.01/1.00      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_3929,c_1716]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4410,plain,
% 3.01/1.00      ( k2_wellord1(k2_wellord1(k1_wellord2(sK2),sK3),X0) = k2_wellord1(k1_wellord2(sK3),X0)
% 3.01/1.00      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_3954,c_1716]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_6094,plain,
% 3.01/1.00      ( k2_wellord1(k1_wellord2(sK3),sK3) = k2_wellord1(k1_wellord2(sK3),sK2)
% 3.01/1.00      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_4219,c_4410]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_6098,plain,
% 3.01/1.00      ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK3)
% 3.01/1.00      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
% 3.01/1.00      inference(demodulation,[status(thm)],[c_6094,c_1531]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_7000,plain,
% 3.01/1.00      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
% 3.01/1.00      | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK3)) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_6098,c_6994]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_7015,plain,
% 3.01/1.00      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_7001,c_1662,c_2699,c_7000]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3811,plain,
% 3.01/1.00      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.01/1.00      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.01/1.00      | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_3805,c_3551]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4080,plain,
% 3.01/1.00      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.01/1.00      | k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_3811,c_38,c_1662,c_2046]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4081,plain,
% 3.01/1.00      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.01/1.00      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
% 3.01/1.00      inference(renaming,[status(thm)],[c_4080]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4084,plain,
% 3.01/1.00      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.01/1.00      | r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top
% 3.01/1.00      | r2_hidden(sK3,sK2) != iProver_top
% 3.01/1.00      | v3_ordinal1(sK2) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_4081,c_1332]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4208,plain,
% 3.01/1.00      ( r2_hidden(sK3,sK2) != iProver_top
% 3.01/1.00      | r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top
% 3.01/1.00      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_4084,c_24]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4209,plain,
% 3.01/1.00      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.01/1.00      | r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top
% 3.01/1.00      | r2_hidden(sK3,sK2) != iProver_top ),
% 3.01/1.00      inference(renaming,[status(thm)],[c_4208]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_7029,plain,
% 3.01/1.00      ( k1_wellord2(sK3) = k1_wellord2(sK2)
% 3.01/1.00      | r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK2)) != iProver_top
% 3.01/1.00      | r2_hidden(sK3,sK2) != iProver_top ),
% 3.01/1.00      inference(demodulation,[status(thm)],[c_7015,c_4209]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2514,plain,
% 3.01/1.00      ( r4_wellord1(k1_wellord2(sK3),X0) != iProver_top
% 3.01/1.00      | r4_wellord1(k1_wellord2(sK2),X0) = iProver_top
% 3.01/1.00      | v1_relat_1(X0) != iProver_top
% 3.01/1.00      | v1_relat_1(k1_wellord2(sK3)) != iProver_top
% 3.01/1.00      | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_1236,c_1246]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2593,plain,
% 3.01/1.00      ( r4_wellord1(k1_wellord2(sK3),X0) != iProver_top
% 3.01/1.00      | r4_wellord1(k1_wellord2(sK2),X0) = iProver_top
% 3.01/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_2514,c_38,c_1662]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_2602,plain,
% 3.01/1.00      ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK2)) = iProver_top
% 3.01/1.00      | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_2049,c_2593]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_7530,plain,
% 3.01/1.00      ( k1_wellord2(sK3) = k1_wellord2(sK2)
% 3.01/1.00      | r2_hidden(sK3,sK2) != iProver_top ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_7029,c_38,c_2602]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_7538,plain,
% 3.01/1.00      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.01/1.00      | k1_wellord2(sK3) = k1_wellord2(sK2)
% 3.01/1.00      | sK3 = sK2
% 3.01/1.00      | v3_ordinal1(sK3) != iProver_top
% 3.01/1.00      | v3_ordinal1(sK2) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_2382,c_7530]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_7539,plain,
% 3.01/1.00      ( k1_wellord2(sK3) = k1_wellord2(sK2)
% 3.01/1.00      | sK3 = sK2
% 3.01/1.00      | r2_hidden(sK2,sK3) = iProver_top
% 3.01/1.00      | v3_ordinal1(sK3) != iProver_top
% 3.01/1.00      | v3_ordinal1(sK2) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_1251,c_7530]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_7668,plain,
% 3.01/1.00      ( k1_wellord2(sK3) = k1_wellord2(sK2)
% 3.01/1.00      | r2_hidden(sK2,sK3) = iProver_top ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_7539,c_23,c_24,c_25,c_20,c_72,c_81,c_1464]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_7674,plain,
% 3.01/1.00      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.01/1.00      | k1_wellord2(sK3) = k1_wellord2(sK2)
% 3.01/1.00      | v3_ordinal1(sK3) != iProver_top
% 3.01/1.00      | v3_ordinal1(sK2) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_7668,c_1238]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_7675,plain,
% 3.01/1.00      ( ~ v3_ordinal1(sK3)
% 3.01/1.00      | ~ v3_ordinal1(sK2)
% 3.01/1.00      | k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.01/1.00      | k1_wellord2(sK3) = k1_wellord2(sK2) ),
% 3.01/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_7674]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_7677,plain,
% 3.01/1.00      ( k1_wellord2(sK3) = k1_wellord2(sK2)
% 3.01/1.00      | k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_7538,c_23,c_24,c_25,c_20,c_72,c_81,c_1464]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_7678,plain,
% 3.01/1.00      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.01/1.00      | k1_wellord2(sK3) = k1_wellord2(sK2) ),
% 3.01/1.00      inference(renaming,[status(thm)],[c_7677]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_7681,plain,
% 3.01/1.00      ( k1_wellord2(sK3) = k1_wellord2(sK2)
% 3.01/1.00      | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top
% 3.01/1.00      | r2_hidden(sK2,sK3) != iProver_top
% 3.01/1.00      | v3_ordinal1(sK3) != iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_7678,c_1332]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_838,plain,( X0 = X0 ),theory(equality) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1562,plain,
% 3.01/1.00      ( k1_wellord2(sK3) = k1_wellord2(sK3) ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_838]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_7033,plain,
% 3.01/1.00      ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
% 3.01/1.00      | k1_wellord2(sK3) = k1_wellord2(sK2) ),
% 3.01/1.00      inference(demodulation,[status(thm)],[c_7015,c_3808]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3146,plain,
% 3.01/1.00      ( r4_wellord1(X0,X1)
% 3.01/1.00      | ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2))
% 3.01/1.00      | X0 != k1_wellord2(sK3)
% 3.01/1.00      | X1 != k1_wellord2(sK2) ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_846]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3515,plain,
% 3.01/1.00      ( r4_wellord1(k1_wellord2(sK3),X0)
% 3.01/1.00      | ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2))
% 3.01/1.00      | X0 != k1_wellord2(sK2)
% 3.01/1.00      | k1_wellord2(sK3) != k1_wellord2(sK3) ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_3146]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_7097,plain,
% 3.01/1.00      ( r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2))
% 3.01/1.00      | ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2))
% 3.01/1.00      | k2_wellord1(k1_wellord2(sK3),sK2) != k1_wellord2(sK2)
% 3.01/1.00      | k1_wellord2(sK3) != k1_wellord2(sK3) ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_3515]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_7128,plain,
% 3.01/1.00      ( k2_wellord1(k1_wellord2(sK3),sK2) != k1_wellord2(sK2)
% 3.01/1.00      | k1_wellord2(sK3) != k1_wellord2(sK3)
% 3.01/1.00      | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) = iProver_top
% 3.01/1.00      | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_7097]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_7807,plain,
% 3.01/1.00      ( k1_wellord2(sK3) = k1_wellord2(sK2) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_7681,c_25,c_38,c_1562,c_1662,c_2046,c_7033,c_7128,
% 3.01/1.00                 c_7668]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_7866,plain,
% 3.01/1.00      ( k3_relat_1(k1_wellord2(sK2)) = sK3 ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_7807,c_137]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_7884,plain,
% 3.01/1.00      ( sK3 = sK2 ),
% 3.01/1.00      inference(demodulation,[status(thm)],[c_7866,c_137]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(contradiction,plain,
% 3.01/1.00      ( $false ),
% 3.01/1.00      inference(minisat,[status(thm)],[c_7884,c_1464,c_81,c_72,c_20,c_23]) ).
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.01/1.00  
% 3.01/1.00  ------                               Statistics
% 3.01/1.00  
% 3.01/1.00  ------ General
% 3.01/1.00  
% 3.01/1.00  abstr_ref_over_cycles:                  0
% 3.01/1.00  abstr_ref_under_cycles:                 0
% 3.01/1.00  gc_basic_clause_elim:                   0
% 3.01/1.00  forced_gc_time:                         0
% 3.01/1.00  parsing_time:                           0.008
% 3.01/1.00  unif_index_cands_time:                  0.
% 3.01/1.00  unif_index_add_time:                    0.
% 3.01/1.00  orderings_time:                         0.
% 3.01/1.00  out_proof_time:                         0.033
% 3.01/1.00  total_time:                             0.276
% 3.01/1.00  num_of_symbols:                         47
% 3.01/1.00  num_of_terms:                           6104
% 3.01/1.00  
% 3.01/1.00  ------ Preprocessing
% 3.01/1.00  
% 3.01/1.00  num_of_splits:                          0
% 3.01/1.00  num_of_split_atoms:                     0
% 3.01/1.00  num_of_reused_defs:                     0
% 3.01/1.00  num_eq_ax_congr_red:                    15
% 3.01/1.00  num_of_sem_filtered_clauses:            1
% 3.01/1.00  num_of_subtypes:                        0
% 3.01/1.00  monotx_restored_types:                  0
% 3.01/1.00  sat_num_of_epr_types:                   0
% 3.01/1.00  sat_num_of_non_cyclic_types:            0
% 3.01/1.00  sat_guarded_non_collapsed_types:        0
% 3.01/1.00  num_pure_diseq_elim:                    0
% 3.01/1.00  simp_replaced_by:                       0
% 3.01/1.00  res_preprocessed:                       122
% 3.01/1.00  prep_upred:                             0
% 3.01/1.00  prep_unflattend:                        25
% 3.01/1.00  smt_new_axioms:                         0
% 3.01/1.00  pred_elim_cands:                        6
% 3.01/1.00  pred_elim:                              1
% 3.01/1.00  pred_elim_cl:                           1
% 3.01/1.00  pred_elim_cycles:                       3
% 3.01/1.00  merged_defs:                            0
% 3.01/1.00  merged_defs_ncl:                        0
% 3.01/1.00  bin_hyper_res:                          0
% 3.01/1.00  prep_cycles:                            4
% 3.01/1.00  pred_elim_time:                         0.01
% 3.01/1.00  splitting_time:                         0.
% 3.01/1.00  sem_filter_time:                        0.
% 3.01/1.00  monotx_time:                            0.
% 3.01/1.00  subtype_inf_time:                       0.
% 3.01/1.00  
% 3.01/1.00  ------ Problem properties
% 3.01/1.00  
% 3.01/1.00  clauses:                                23
% 3.01/1.00  conjectures:                            4
% 3.01/1.00  epr:                                    9
% 3.01/1.00  horn:                                   18
% 3.01/1.00  ground:                                 4
% 3.01/1.00  unary:                                  7
% 3.01/1.00  binary:                                 4
% 3.01/1.00  lits:                                   66
% 3.01/1.00  lits_eq:                                12
% 3.01/1.00  fd_pure:                                0
% 3.01/1.00  fd_pseudo:                              0
% 3.01/1.00  fd_cond:                                0
% 3.01/1.00  fd_pseudo_cond:                         2
% 3.01/1.00  ac_symbols:                             0
% 3.01/1.00  
% 3.01/1.00  ------ Propositional Solver
% 3.01/1.00  
% 3.01/1.00  prop_solver_calls:                      29
% 3.01/1.00  prop_fast_solver_calls:                 1150
% 3.01/1.00  smt_solver_calls:                       0
% 3.01/1.00  smt_fast_solver_calls:                  0
% 3.01/1.00  prop_num_of_clauses:                    2694
% 3.01/1.00  prop_preprocess_simplified:             7809
% 3.01/1.00  prop_fo_subsumed:                       44
% 3.01/1.00  prop_solver_time:                       0.
% 3.01/1.00  smt_solver_time:                        0.
% 3.01/1.00  smt_fast_solver_time:                   0.
% 3.01/1.00  prop_fast_solver_time:                  0.
% 3.01/1.00  prop_unsat_core_time:                   0.
% 3.01/1.00  
% 3.01/1.00  ------ QBF
% 3.01/1.00  
% 3.01/1.00  qbf_q_res:                              0
% 3.01/1.00  qbf_num_tautologies:                    0
% 3.01/1.00  qbf_prep_cycles:                        0
% 3.01/1.00  
% 3.01/1.00  ------ BMC1
% 3.01/1.00  
% 3.01/1.00  bmc1_current_bound:                     -1
% 3.01/1.00  bmc1_last_solved_bound:                 -1
% 3.01/1.00  bmc1_unsat_core_size:                   -1
% 3.01/1.00  bmc1_unsat_core_parents_size:           -1
% 3.01/1.00  bmc1_merge_next_fun:                    0
% 3.01/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.01/1.00  
% 3.01/1.00  ------ Instantiation
% 3.01/1.00  
% 3.01/1.00  inst_num_of_clauses:                    890
% 3.01/1.00  inst_num_in_passive:                    284
% 3.01/1.00  inst_num_in_active:                     359
% 3.01/1.00  inst_num_in_unprocessed:                247
% 3.01/1.00  inst_num_of_loops:                      460
% 3.01/1.00  inst_num_of_learning_restarts:          0
% 3.01/1.00  inst_num_moves_active_passive:          98
% 3.01/1.00  inst_lit_activity:                      0
% 3.01/1.00  inst_lit_activity_moves:                0
% 3.01/1.00  inst_num_tautologies:                   0
% 3.01/1.00  inst_num_prop_implied:                  0
% 3.01/1.00  inst_num_existing_simplified:           0
% 3.01/1.00  inst_num_eq_res_simplified:             0
% 3.01/1.00  inst_num_child_elim:                    0
% 3.01/1.00  inst_num_of_dismatching_blockings:      558
% 3.01/1.00  inst_num_of_non_proper_insts:           881
% 3.01/1.00  inst_num_of_duplicates:                 0
% 3.01/1.00  inst_inst_num_from_inst_to_res:         0
% 3.01/1.00  inst_dismatching_checking_time:         0.
% 3.01/1.00  
% 3.01/1.00  ------ Resolution
% 3.01/1.00  
% 3.01/1.00  res_num_of_clauses:                     0
% 3.01/1.00  res_num_in_passive:                     0
% 3.01/1.00  res_num_in_active:                      0
% 3.01/1.00  res_num_of_loops:                       126
% 3.01/1.00  res_forward_subset_subsumed:            76
% 3.01/1.00  res_backward_subset_subsumed:           0
% 3.01/1.00  res_forward_subsumed:                   0
% 3.01/1.00  res_backward_subsumed:                  0
% 3.01/1.00  res_forward_subsumption_resolution:     6
% 3.01/1.00  res_backward_subsumption_resolution:    0
% 3.01/1.00  res_clause_to_clause_subsumption:       442
% 3.01/1.00  res_orphan_elimination:                 0
% 3.01/1.00  res_tautology_del:                      56
% 3.01/1.00  res_num_eq_res_simplified:              0
% 3.01/1.00  res_num_sel_changes:                    0
% 3.01/1.00  res_moves_from_active_to_pass:          0
% 3.01/1.00  
% 3.01/1.00  ------ Superposition
% 3.01/1.00  
% 3.01/1.00  sup_time_total:                         0.
% 3.01/1.00  sup_time_generating:                    0.
% 3.01/1.00  sup_time_sim_full:                      0.
% 3.01/1.00  sup_time_sim_immed:                     0.
% 3.01/1.00  
% 3.01/1.00  sup_num_of_clauses:                     56
% 3.01/1.00  sup_num_in_active:                      51
% 3.01/1.00  sup_num_in_passive:                     5
% 3.01/1.00  sup_num_of_loops:                       90
% 3.01/1.00  sup_fw_superposition:                   153
% 3.01/1.00  sup_bw_superposition:                   158
% 3.01/1.00  sup_immediate_simplified:               49
% 3.01/1.00  sup_given_eliminated:                   1
% 3.01/1.00  comparisons_done:                       0
% 3.01/1.00  comparisons_avoided:                    109
% 3.01/1.00  
% 3.01/1.00  ------ Simplifications
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  sim_fw_subset_subsumed:                 26
% 3.01/1.00  sim_bw_subset_subsumed:                 11
% 3.01/1.00  sim_fw_subsumed:                        1
% 3.01/1.00  sim_bw_subsumed:                        0
% 3.01/1.00  sim_fw_subsumption_res:                 2
% 3.01/1.00  sim_bw_subsumption_res:                 0
% 3.01/1.00  sim_tautology_del:                      5
% 3.01/1.00  sim_eq_tautology_del:                   35
% 3.01/1.00  sim_eq_res_simp:                        0
% 3.01/1.00  sim_fw_demodulated:                     6
% 3.01/1.00  sim_bw_demodulated:                     36
% 3.01/1.00  sim_light_normalised:                   19
% 3.01/1.00  sim_joinable_taut:                      0
% 3.01/1.00  sim_joinable_simp:                      0
% 3.01/1.00  sim_ac_normalised:                      0
% 3.01/1.00  sim_smt_subsumption:                    0
% 3.01/1.00  
%------------------------------------------------------------------------------
