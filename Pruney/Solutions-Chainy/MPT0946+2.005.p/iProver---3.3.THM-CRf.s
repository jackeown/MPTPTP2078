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
% DateTime   : Thu Dec  3 11:59:42 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :  207 (24821 expanded)
%              Number of clauses        :  140 (9300 expanded)
%              Number of leaves         :   20 (5017 expanded)
%              Depth                    :   43
%              Number of atoms          :  706 (86969 expanded)
%              Number of equality atoms :  353 (27604 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   17 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f35])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f36,f46,f45])).

fof(f70,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f71,plain,(
    v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f51,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f75,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f10,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f54,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_wellord1(k1_wellord2(X1),X0) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f73,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f47])).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f68,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

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
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f29])).

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
    inference(nnf_transformation,[],[f30])).

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

fof(f59,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f82,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f59])).

fof(f72,plain,(
    r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) ),
    inference(cnf_transformation,[],[f47])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r4_wellord1(X1,X0)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

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

fof(f25,plain,(
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
    inference(flattening,[],[f25])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r4_wellord1(X0,X2)
      | ~ r4_wellord1(X1,X2)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_25,negated_conjecture,
    ( v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_859,plain,
    ( v3_ordinal1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_860,plain,
    ( v3_ordinal1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3,plain,
    ( r1_ordinal1(X0,X1)
    | r1_ordinal1(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_877,plain,
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
    inference(cnf_transformation,[],[f52])).

cnf(c_875,plain,
    ( r1_ordinal1(X0,X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2065,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r1_tarski(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_877,c_875])).

cnf(c_2895,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2065,c_875])).

cnf(c_21,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_862,plain,
    ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2905,plain,
    ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2895,c_862])).

cnf(c_2963,plain,
    ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2905,c_862])).

cnf(c_3178,plain,
    ( k2_wellord1(k1_wellord2(X0),sK3) = k1_wellord2(sK3)
    | k2_wellord1(k1_wellord2(sK3),X0) = k1_wellord2(X0)
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_860,c_2963])).

cnf(c_3347,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
    inference(superposition,[status(thm)],[c_859,c_3178])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_878,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1157,plain,
    ( k2_wellord1(k1_wellord2(X0),X0) = k1_wellord2(X0) ),
    inference(superposition,[status(thm)],[c_878,c_862])).

cnf(c_18,plain,
    ( v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_864,plain,
    ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k2_wellord1(k2_wellord1(X0,X1),X2) = k2_wellord1(k2_wellord1(X0,X2),X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_873,plain,
    ( k2_wellord1(k2_wellord1(X0,X1),X2) = k2_wellord1(k2_wellord1(X0,X2),X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1303,plain,
    ( k2_wellord1(k2_wellord1(k1_wellord2(X0),X1),X2) = k2_wellord1(k2_wellord1(k1_wellord2(X0),X2),X1) ),
    inference(superposition,[status(thm)],[c_864,c_873])).

cnf(c_1796,plain,
    ( k2_wellord1(k2_wellord1(k1_wellord2(X0),X1),X0) = k2_wellord1(k1_wellord2(X0),X1) ),
    inference(superposition,[status(thm)],[c_1157,c_1303])).

cnf(c_3355,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK2) = k2_wellord1(k1_wellord2(sK2),sK3)
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
    inference(superposition,[status(thm)],[c_3347,c_1796])).

cnf(c_3537,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
    inference(superposition,[status(thm)],[c_3355,c_3347])).

cnf(c_3629,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK2) = k2_wellord1(k1_wellord2(sK2),sK3)
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
    inference(superposition,[status(thm)],[c_3537,c_1796])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_874,plain,
    ( X0 = X1
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | k1_wellord1(k1_wellord2(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_863,plain,
    ( k1_wellord1(k1_wellord2(X0),X1) = X1
    | r2_hidden(X1,X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2158,plain,
    ( X0 = X1
    | k1_wellord1(k1_wellord2(X0),X1) = X1
    | r2_hidden(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_874,c_863])).

cnf(c_3815,plain,
    ( X0 = X1
    | k1_wellord1(k1_wellord2(X0),X1) = X1
    | k1_wellord1(k1_wellord2(X1),X0) = X0
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2158,c_863])).

cnf(c_3968,plain,
    ( k1_wellord1(k1_wellord2(X0),sK3) = sK3
    | k1_wellord1(k1_wellord2(sK3),X0) = X0
    | sK3 = X0
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_860,c_3815])).

cnf(c_4085,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_859,c_3968])).

cnf(c_22,negated_conjecture,
    ( sK2 != sK3 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_74,plain,
    ( ~ r1_ordinal1(sK2,sK2)
    | r1_tarski(sK2,sK2)
    | ~ v3_ordinal1(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_80,plain,
    ( r1_ordinal1(sK2,sK2)
    | ~ v3_ordinal1(sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_87,plain,
    ( ~ r1_tarski(sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_454,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1104,plain,
    ( sK3 != X0
    | sK2 != X0
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_454])).

cnf(c_1105,plain,
    ( sK3 != sK2
    | sK2 = sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1104])).

cnf(c_4092,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4085,c_25,c_22,c_74,c_80,c_87,c_1105])).

cnf(c_4093,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
    inference(renaming,[status(thm)],[c_4092])).

cnf(c_10,plain,
    ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
    | ~ r2_hidden(X1,k3_relat_1(X0))
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_20,plain,
    ( v2_wellord1(k1_wellord2(X0))
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_278,plain,
    ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
    | ~ r2_hidden(X1,k3_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v3_ordinal1(X2)
    | k1_wellord2(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_279,plain,
    ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
    | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
    | ~ v1_relat_1(k1_wellord2(X0))
    | ~ v3_ordinal1(X0) ),
    inference(unflattening,[status(thm)],[c_278])).

cnf(c_283,plain,
    ( ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
    | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
    | ~ v3_ordinal1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_279,c_18])).

cnf(c_284,plain,
    ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
    | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
    | ~ v3_ordinal1(X0) ),
    inference(renaming,[status(thm)],[c_283])).

cnf(c_858,plain,
    ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
    | r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_284])).

cnf(c_17,plain,
    ( ~ v1_relat_1(k1_wellord2(X0))
    | k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_147,plain,
    ( k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_18])).

cnf(c_970,plain,
    ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_858,c_147])).

cnf(c_4096,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4093,c_970])).

cnf(c_26,plain,
    ( v3_ordinal1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_27,plain,
    ( v3_ordinal1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1115,plain,
    ( r2_hidden(sK3,sK2)
    | r2_hidden(sK2,sK3)
    | ~ v3_ordinal1(sK3)
    | ~ v3_ordinal1(sK2)
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1116,plain,
    ( sK2 = sK3
    | r2_hidden(sK3,sK2) = iProver_top
    | r2_hidden(sK2,sK3) = iProver_top
    | v3_ordinal1(sK3) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1115])).

cnf(c_1161,plain,
    ( ~ r2_hidden(sK3,sK2)
    | ~ v3_ordinal1(sK3)
    | ~ v3_ordinal1(sK2)
    | k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1162,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | r2_hidden(sK3,sK2) != iProver_top
    | v3_ordinal1(sK3) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1161])).

cnf(c_4244,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4096,c_26,c_27,c_22,c_1116,c_1162])).

cnf(c_4499,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3629,c_4244])).

cnf(c_5825,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3537,c_4499])).

cnf(c_1791,plain,
    ( v1_relat_1(k1_wellord2(sK3)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1792,plain,
    ( v1_relat_1(k1_wellord2(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1791])).

cnf(c_23,negated_conjecture,
    ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_861,plain,
    ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_8,plain,
    ( ~ r4_wellord1(X0,X1)
    | r4_wellord1(X1,X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_872,plain,
    ( r4_wellord1(X0,X1) != iProver_top
    | r4_wellord1(X1,X0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1868,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_861,c_872])).

cnf(c_28,plain,
    ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_38,plain,
    ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_40,plain,
    ( v1_relat_1(k1_wellord2(sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_38])).

cnf(c_1089,plain,
    ( r4_wellord1(X0,k1_wellord2(X1))
    | ~ r4_wellord1(k1_wellord2(X1),X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(k1_wellord2(X1)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1250,plain,
    ( ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
    | r4_wellord1(k1_wellord2(X1),k1_wellord2(X0))
    | ~ v1_relat_1(k1_wellord2(X1))
    | ~ v1_relat_1(k1_wellord2(X0)) ),
    inference(instantiation,[status(thm)],[c_1089])).

cnf(c_1699,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2))
    | ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
    | ~ v1_relat_1(k1_wellord2(sK3))
    | ~ v1_relat_1(k1_wellord2(sK2)) ),
    inference(instantiation,[status(thm)],[c_1250])).

cnf(c_1700,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top
    | r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1699])).

cnf(c_1871,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1868,c_28,c_40,c_1700,c_1792])).

cnf(c_9,plain,
    ( ~ r4_wellord1(X0,X1)
    | ~ r4_wellord1(X1,X2)
    | r4_wellord1(X0,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_871,plain,
    ( r4_wellord1(X0,X1) != iProver_top
    | r4_wellord1(X1,X2) != iProver_top
    | r4_wellord1(X0,X2) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2192,plain,
    ( r4_wellord1(k1_wellord2(sK3),X0) = iProver_top
    | r4_wellord1(k1_wellord2(sK2),X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1871,c_871])).

cnf(c_2391,plain,
    ( r4_wellord1(k1_wellord2(sK3),X0) = iProver_top
    | r4_wellord1(k1_wellord2(sK2),X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2192,c_40,c_1792])).

cnf(c_2400,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK3)) = iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_861,c_2391])).

cnf(c_5828,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
    | k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5825,c_1792,c_2400])).

cnf(c_5829,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
    inference(renaming,[status(thm)],[c_5828])).

cnf(c_5832,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
    | r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top
    | r2_hidden(sK3,sK2) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5829,c_970])).

cnf(c_463,plain,
    ( X0 != X1
    | k1_wellord2(X0) = k1_wellord2(X1) ),
    theory(equality)).

cnf(c_475,plain,
    ( k1_wellord2(sK2) = k1_wellord2(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_463])).

cnf(c_460,plain,
    ( ~ r4_wellord1(X0,X1)
    | r4_wellord1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1121,plain,
    ( r4_wellord1(X0,X1)
    | ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
    | X1 != k1_wellord2(sK3)
    | X0 != k1_wellord2(sK2) ),
    inference(instantiation,[status(thm)],[c_460])).

cnf(c_1198,plain,
    ( r4_wellord1(X0,k2_wellord1(k1_wellord2(X1),sK3))
    | ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
    | X0 != k1_wellord2(sK2)
    | k2_wellord1(k1_wellord2(X1),sK3) != k1_wellord2(sK3) ),
    inference(instantiation,[status(thm)],[c_1121])).

cnf(c_1884,plain,
    ( r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(X0),sK3))
    | ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
    | k2_wellord1(k1_wellord2(X0),sK3) != k1_wellord2(sK3)
    | k1_wellord2(sK2) != k1_wellord2(sK2) ),
    inference(instantiation,[status(thm)],[c_1198])).

cnf(c_1887,plain,
    ( k2_wellord1(k1_wellord2(X0),sK3) != k1_wellord2(sK3)
    | k1_wellord2(sK2) != k1_wellord2(sK2)
    | r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(X0),sK3)) = iProver_top
    | r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1884])).

cnf(c_1889,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) != k1_wellord2(sK3)
    | k1_wellord2(sK2) != k1_wellord2(sK2)
    | r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) = iProver_top
    | r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1887])).

cnf(c_5971,plain,
    ( r2_hidden(sK3,sK2) != iProver_top
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5832,c_25,c_26,c_28,c_74,c_80,c_87,c_475,c_1889,c_3537])).

cnf(c_5972,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
    | r2_hidden(sK3,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5971])).

cnf(c_5980,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
    | sK3 = sK2
    | r2_hidden(sK2,sK3) = iProver_top
    | v3_ordinal1(sK3) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_874,c_5972])).

cnf(c_6388,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5980,c_25,c_26,c_27,c_22,c_74,c_80,c_87,c_1105])).

cnf(c_6394,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
    | v3_ordinal1(sK3) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6388,c_863])).

cnf(c_6395,plain,
    ( ~ v3_ordinal1(sK3)
    | ~ v3_ordinal1(sK2)
    | k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6394])).

cnf(c_6397,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6394,c_25,c_24,c_6395])).

cnf(c_6401,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6397,c_970])).

cnf(c_6993,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6401,c_25,c_26,c_27,c_22,c_74,c_80,c_87,c_1105,c_5980])).

cnf(c_7000,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3629,c_6993])).

cnf(c_4495,plain,
    ( k2_wellord1(k2_wellord1(k1_wellord2(sK2),sK3),sK3) = k2_wellord1(k1_wellord2(sK3),sK2)
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
    inference(superposition,[status(thm)],[c_3629,c_1796])).

cnf(c_3630,plain,
    ( k2_wellord1(k2_wellord1(k1_wellord2(sK2),X0),sK3) = k2_wellord1(k1_wellord2(sK3),X0)
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
    inference(superposition,[status(thm)],[c_3537,c_1303])).

cnf(c_6009,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK2) = k2_wellord1(k1_wellord2(sK3),sK3)
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
    inference(superposition,[status(thm)],[c_4495,c_3630])).

cnf(c_6012,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK3)
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
    inference(demodulation,[status(thm)],[c_6009,c_1157])).

cnf(c_6999,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6012,c_6993])).

cnf(c_7014,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7000,c_1792,c_2400,c_6999])).

cnf(c_7032,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
    | k1_wellord2(sK3) = k1_wellord2(sK2) ),
    inference(demodulation,[status(thm)],[c_7014,c_3355])).

cnf(c_2159,plain,
    ( X0 = X1
    | k1_wellord1(k1_wellord2(X1),X0) = X0
    | r2_hidden(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_874,c_863])).

cnf(c_4251,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3347,c_4244])).

cnf(c_4324,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4251,c_28,c_40,c_1700,c_1792])).

cnf(c_4325,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
    inference(renaming,[status(thm)],[c_4324])).

cnf(c_4328,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top
    | r2_hidden(sK3,sK2) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4325,c_970])).

cnf(c_4331,plain,
    ( r2_hidden(sK3,sK2) != iProver_top
    | r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4328,c_26])).

cnf(c_4332,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top
    | r2_hidden(sK3,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4331])).

cnf(c_7028,plain,
    ( k1_wellord2(sK3) = k1_wellord2(sK2)
    | r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK2)) != iProver_top
    | r2_hidden(sK3,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7014,c_4332])).

cnf(c_2191,plain,
    ( r4_wellord1(k1_wellord2(sK3),X0) != iProver_top
    | r4_wellord1(k1_wellord2(sK2),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_861,c_871])).

cnf(c_2300,plain,
    ( r4_wellord1(k1_wellord2(sK3),X0) != iProver_top
    | r4_wellord1(k1_wellord2(sK2),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2191,c_40,c_1792])).

cnf(c_2309,plain,
    ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK2)) = iProver_top
    | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1871,c_2300])).

cnf(c_7417,plain,
    ( k1_wellord2(sK3) = k1_wellord2(sK2)
    | r2_hidden(sK3,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7028,c_40,c_2309])).

cnf(c_7425,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k1_wellord2(sK3) = k1_wellord2(sK2)
    | sK3 = sK2
    | v3_ordinal1(sK3) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2159,c_7417])).

cnf(c_7426,plain,
    ( k1_wellord2(sK3) = k1_wellord2(sK2)
    | sK3 = sK2
    | r2_hidden(sK2,sK3) = iProver_top
    | v3_ordinal1(sK3) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_874,c_7417])).

cnf(c_7582,plain,
    ( k1_wellord2(sK3) = k1_wellord2(sK2)
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7426,c_25,c_26,c_27,c_22,c_74,c_80,c_87,c_1105])).

cnf(c_7588,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k1_wellord2(sK3) = k1_wellord2(sK2)
    | v3_ordinal1(sK3) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7582,c_863])).

cnf(c_7589,plain,
    ( ~ v3_ordinal1(sK3)
    | ~ v3_ordinal1(sK2)
    | k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k1_wellord2(sK3) = k1_wellord2(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7588])).

cnf(c_7591,plain,
    ( k1_wellord2(sK3) = k1_wellord2(sK2)
    | k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7425,c_25,c_26,c_27,c_22,c_74,c_80,c_87,c_1105])).

cnf(c_7592,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k1_wellord2(sK3) = k1_wellord2(sK2) ),
    inference(renaming,[status(thm)],[c_7591])).

cnf(c_7595,plain,
    ( k1_wellord2(sK3) = k1_wellord2(sK2)
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7592,c_970])).

cnf(c_7655,plain,
    ( k1_wellord2(sK3) = k1_wellord2(sK2)
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7595,c_25,c_26,c_27,c_22,c_74,c_80,c_87,c_1105,c_7426])).

cnf(c_7661,plain,
    ( k1_wellord2(sK3) = k1_wellord2(sK2)
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7032,c_7655])).

cnf(c_7669,plain,
    ( k1_wellord2(sK3) = k1_wellord2(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7661,c_28,c_40,c_1700,c_1792])).

cnf(c_7724,plain,
    ( k3_relat_1(k1_wellord2(sK2)) = sK3 ),
    inference(superposition,[status(thm)],[c_7669,c_147])).

cnf(c_7760,plain,
    ( sK3 = sK2 ),
    inference(demodulation,[status(thm)],[c_7724,c_147])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7760,c_1105,c_87,c_80,c_74,c_22,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:53:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.12/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/0.99  
% 3.12/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.12/0.99  
% 3.12/0.99  ------  iProver source info
% 3.12/0.99  
% 3.12/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.12/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.12/0.99  git: non_committed_changes: false
% 3.12/0.99  git: last_make_outside_of_git: false
% 3.12/0.99  
% 3.12/0.99  ------ 
% 3.12/0.99  
% 3.12/0.99  ------ Input Options
% 3.12/0.99  
% 3.12/0.99  --out_options                           all
% 3.12/0.99  --tptp_safe_out                         true
% 3.12/0.99  --problem_path                          ""
% 3.12/0.99  --include_path                          ""
% 3.12/0.99  --clausifier                            res/vclausify_rel
% 3.12/0.99  --clausifier_options                    --mode clausify
% 3.12/0.99  --stdin                                 false
% 3.12/0.99  --stats_out                             all
% 3.12/0.99  
% 3.12/0.99  ------ General Options
% 3.12/0.99  
% 3.12/0.99  --fof                                   false
% 3.12/0.99  --time_out_real                         305.
% 3.12/0.99  --time_out_virtual                      -1.
% 3.12/0.99  --symbol_type_check                     false
% 3.12/0.99  --clausify_out                          false
% 3.12/0.99  --sig_cnt_out                           false
% 3.12/0.99  --trig_cnt_out                          false
% 3.12/0.99  --trig_cnt_out_tolerance                1.
% 3.12/0.99  --trig_cnt_out_sk_spl                   false
% 3.12/0.99  --abstr_cl_out                          false
% 3.12/0.99  
% 3.12/0.99  ------ Global Options
% 3.12/0.99  
% 3.12/0.99  --schedule                              default
% 3.12/0.99  --add_important_lit                     false
% 3.12/0.99  --prop_solver_per_cl                    1000
% 3.12/0.99  --min_unsat_core                        false
% 3.12/0.99  --soft_assumptions                      false
% 3.12/0.99  --soft_lemma_size                       3
% 3.12/0.99  --prop_impl_unit_size                   0
% 3.12/0.99  --prop_impl_unit                        []
% 3.12/0.99  --share_sel_clauses                     true
% 3.12/0.99  --reset_solvers                         false
% 3.12/0.99  --bc_imp_inh                            [conj_cone]
% 3.12/0.99  --conj_cone_tolerance                   3.
% 3.12/0.99  --extra_neg_conj                        none
% 3.12/0.99  --large_theory_mode                     true
% 3.12/0.99  --prolific_symb_bound                   200
% 3.12/0.99  --lt_threshold                          2000
% 3.12/0.99  --clause_weak_htbl                      true
% 3.12/0.99  --gc_record_bc_elim                     false
% 3.12/0.99  
% 3.12/0.99  ------ Preprocessing Options
% 3.12/0.99  
% 3.12/0.99  --preprocessing_flag                    true
% 3.12/0.99  --time_out_prep_mult                    0.1
% 3.12/0.99  --splitting_mode                        input
% 3.12/0.99  --splitting_grd                         true
% 3.12/0.99  --splitting_cvd                         false
% 3.12/0.99  --splitting_cvd_svl                     false
% 3.12/0.99  --splitting_nvd                         32
% 3.12/0.99  --sub_typing                            true
% 3.12/0.99  --prep_gs_sim                           true
% 3.12/0.99  --prep_unflatten                        true
% 3.12/0.99  --prep_res_sim                          true
% 3.12/0.99  --prep_upred                            true
% 3.12/0.99  --prep_sem_filter                       exhaustive
% 3.12/0.99  --prep_sem_filter_out                   false
% 3.12/0.99  --pred_elim                             true
% 3.12/0.99  --res_sim_input                         true
% 3.12/0.99  --eq_ax_congr_red                       true
% 3.12/0.99  --pure_diseq_elim                       true
% 3.12/0.99  --brand_transform                       false
% 3.12/0.99  --non_eq_to_eq                          false
% 3.12/0.99  --prep_def_merge                        true
% 3.12/0.99  --prep_def_merge_prop_impl              false
% 3.12/0.99  --prep_def_merge_mbd                    true
% 3.12/0.99  --prep_def_merge_tr_red                 false
% 3.12/0.99  --prep_def_merge_tr_cl                  false
% 3.12/0.99  --smt_preprocessing                     true
% 3.12/0.99  --smt_ac_axioms                         fast
% 3.12/0.99  --preprocessed_out                      false
% 3.12/0.99  --preprocessed_stats                    false
% 3.12/0.99  
% 3.12/0.99  ------ Abstraction refinement Options
% 3.12/0.99  
% 3.12/0.99  --abstr_ref                             []
% 3.12/0.99  --abstr_ref_prep                        false
% 3.12/0.99  --abstr_ref_until_sat                   false
% 3.12/0.99  --abstr_ref_sig_restrict                funpre
% 3.12/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.12/0.99  --abstr_ref_under                       []
% 3.12/0.99  
% 3.12/0.99  ------ SAT Options
% 3.12/0.99  
% 3.12/0.99  --sat_mode                              false
% 3.12/0.99  --sat_fm_restart_options                ""
% 3.12/0.99  --sat_gr_def                            false
% 3.12/0.99  --sat_epr_types                         true
% 3.12/0.99  --sat_non_cyclic_types                  false
% 3.12/0.99  --sat_finite_models                     false
% 3.12/0.99  --sat_fm_lemmas                         false
% 3.12/0.99  --sat_fm_prep                           false
% 3.12/0.99  --sat_fm_uc_incr                        true
% 3.12/0.99  --sat_out_model                         small
% 3.12/0.99  --sat_out_clauses                       false
% 3.12/0.99  
% 3.12/0.99  ------ QBF Options
% 3.12/0.99  
% 3.12/0.99  --qbf_mode                              false
% 3.12/0.99  --qbf_elim_univ                         false
% 3.12/0.99  --qbf_dom_inst                          none
% 3.12/0.99  --qbf_dom_pre_inst                      false
% 3.12/0.99  --qbf_sk_in                             false
% 3.12/0.99  --qbf_pred_elim                         true
% 3.12/0.99  --qbf_split                             512
% 3.12/0.99  
% 3.12/0.99  ------ BMC1 Options
% 3.12/0.99  
% 3.12/0.99  --bmc1_incremental                      false
% 3.12/0.99  --bmc1_axioms                           reachable_all
% 3.12/0.99  --bmc1_min_bound                        0
% 3.12/0.99  --bmc1_max_bound                        -1
% 3.12/0.99  --bmc1_max_bound_default                -1
% 3.12/0.99  --bmc1_symbol_reachability              true
% 3.12/0.99  --bmc1_property_lemmas                  false
% 3.12/0.99  --bmc1_k_induction                      false
% 3.12/0.99  --bmc1_non_equiv_states                 false
% 3.12/0.99  --bmc1_deadlock                         false
% 3.12/0.99  --bmc1_ucm                              false
% 3.12/0.99  --bmc1_add_unsat_core                   none
% 3.12/0.99  --bmc1_unsat_core_children              false
% 3.12/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.12/0.99  --bmc1_out_stat                         full
% 3.12/0.99  --bmc1_ground_init                      false
% 3.12/0.99  --bmc1_pre_inst_next_state              false
% 3.12/0.99  --bmc1_pre_inst_state                   false
% 3.12/0.99  --bmc1_pre_inst_reach_state             false
% 3.12/0.99  --bmc1_out_unsat_core                   false
% 3.12/0.99  --bmc1_aig_witness_out                  false
% 3.12/0.99  --bmc1_verbose                          false
% 3.12/0.99  --bmc1_dump_clauses_tptp                false
% 3.12/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.12/0.99  --bmc1_dump_file                        -
% 3.12/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.12/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.12/0.99  --bmc1_ucm_extend_mode                  1
% 3.12/0.99  --bmc1_ucm_init_mode                    2
% 3.12/0.99  --bmc1_ucm_cone_mode                    none
% 3.12/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.12/0.99  --bmc1_ucm_relax_model                  4
% 3.12/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.12/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.12/0.99  --bmc1_ucm_layered_model                none
% 3.12/0.99  --bmc1_ucm_max_lemma_size               10
% 3.12/0.99  
% 3.12/0.99  ------ AIG Options
% 3.12/0.99  
% 3.12/0.99  --aig_mode                              false
% 3.12/0.99  
% 3.12/0.99  ------ Instantiation Options
% 3.12/0.99  
% 3.12/0.99  --instantiation_flag                    true
% 3.12/0.99  --inst_sos_flag                         false
% 3.12/0.99  --inst_sos_phase                        true
% 3.12/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.12/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.12/0.99  --inst_lit_sel_side                     num_symb
% 3.12/0.99  --inst_solver_per_active                1400
% 3.12/0.99  --inst_solver_calls_frac                1.
% 3.12/0.99  --inst_passive_queue_type               priority_queues
% 3.12/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.12/0.99  --inst_passive_queues_freq              [25;2]
% 3.12/0.99  --inst_dismatching                      true
% 3.12/0.99  --inst_eager_unprocessed_to_passive     true
% 3.12/0.99  --inst_prop_sim_given                   true
% 3.12/0.99  --inst_prop_sim_new                     false
% 3.12/0.99  --inst_subs_new                         false
% 3.12/0.99  --inst_eq_res_simp                      false
% 3.12/0.99  --inst_subs_given                       false
% 3.12/0.99  --inst_orphan_elimination               true
% 3.12/0.99  --inst_learning_loop_flag               true
% 3.12/0.99  --inst_learning_start                   3000
% 3.12/0.99  --inst_learning_factor                  2
% 3.12/0.99  --inst_start_prop_sim_after_learn       3
% 3.12/0.99  --inst_sel_renew                        solver
% 3.12/0.99  --inst_lit_activity_flag                true
% 3.12/0.99  --inst_restr_to_given                   false
% 3.12/0.99  --inst_activity_threshold               500
% 3.12/0.99  --inst_out_proof                        true
% 3.12/0.99  
% 3.12/0.99  ------ Resolution Options
% 3.12/0.99  
% 3.12/0.99  --resolution_flag                       true
% 3.12/0.99  --res_lit_sel                           adaptive
% 3.12/0.99  --res_lit_sel_side                      none
% 3.12/0.99  --res_ordering                          kbo
% 3.12/0.99  --res_to_prop_solver                    active
% 3.12/0.99  --res_prop_simpl_new                    false
% 3.12/0.99  --res_prop_simpl_given                  true
% 3.12/0.99  --res_passive_queue_type                priority_queues
% 3.12/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.12/0.99  --res_passive_queues_freq               [15;5]
% 3.12/0.99  --res_forward_subs                      full
% 3.12/0.99  --res_backward_subs                     full
% 3.12/0.99  --res_forward_subs_resolution           true
% 3.12/0.99  --res_backward_subs_resolution          true
% 3.12/0.99  --res_orphan_elimination                true
% 3.12/0.99  --res_time_limit                        2.
% 3.12/0.99  --res_out_proof                         true
% 3.12/0.99  
% 3.12/0.99  ------ Superposition Options
% 3.12/0.99  
% 3.12/0.99  --superposition_flag                    true
% 3.12/0.99  --sup_passive_queue_type                priority_queues
% 3.12/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.12/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.12/0.99  --demod_completeness_check              fast
% 3.12/0.99  --demod_use_ground                      true
% 3.12/0.99  --sup_to_prop_solver                    passive
% 3.12/0.99  --sup_prop_simpl_new                    true
% 3.12/0.99  --sup_prop_simpl_given                  true
% 3.12/0.99  --sup_fun_splitting                     false
% 3.12/0.99  --sup_smt_interval                      50000
% 3.12/0.99  
% 3.12/0.99  ------ Superposition Simplification Setup
% 3.12/0.99  
% 3.12/0.99  --sup_indices_passive                   []
% 3.12/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.12/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/0.99  --sup_full_bw                           [BwDemod]
% 3.12/0.99  --sup_immed_triv                        [TrivRules]
% 3.12/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.12/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/0.99  --sup_immed_bw_main                     []
% 3.12/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.12/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.12/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.12/0.99  
% 3.12/0.99  ------ Combination Options
% 3.12/0.99  
% 3.12/0.99  --comb_res_mult                         3
% 3.12/0.99  --comb_sup_mult                         2
% 3.12/0.99  --comb_inst_mult                        10
% 3.12/0.99  
% 3.12/0.99  ------ Debug Options
% 3.12/0.99  
% 3.12/0.99  --dbg_backtrace                         false
% 3.12/0.99  --dbg_dump_prop_clauses                 false
% 3.12/0.99  --dbg_dump_prop_clauses_file            -
% 3.12/0.99  --dbg_out_stat                          false
% 3.12/0.99  ------ Parsing...
% 3.12/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.12/0.99  
% 3.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.12/0.99  
% 3.12/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.12/0.99  
% 3.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.12/0.99  ------ Proving...
% 3.12/0.99  ------ Problem Properties 
% 3.12/0.99  
% 3.12/0.99  
% 3.12/0.99  clauses                                 24
% 3.12/0.99  conjectures                             4
% 3.12/0.99  EPR                                     11
% 3.12/0.99  Horn                                    19
% 3.12/0.99  unary                                   7
% 3.12/0.99  binary                                  2
% 3.12/0.99  lits                                    72
% 3.12/0.99  lits eq                                 11
% 3.12/0.99  fd_pure                                 0
% 3.12/0.99  fd_pseudo                               0
% 3.12/0.99  fd_cond                                 0
% 3.12/0.99  fd_pseudo_cond                          2
% 3.12/0.99  AC symbols                              0
% 3.12/0.99  
% 3.12/0.99  ------ Schedule dynamic 5 is on 
% 3.12/0.99  
% 3.12/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.12/0.99  
% 3.12/0.99  
% 3.12/0.99  ------ 
% 3.12/0.99  Current options:
% 3.12/0.99  ------ 
% 3.12/0.99  
% 3.12/0.99  ------ Input Options
% 3.12/0.99  
% 3.12/0.99  --out_options                           all
% 3.12/0.99  --tptp_safe_out                         true
% 3.12/0.99  --problem_path                          ""
% 3.12/0.99  --include_path                          ""
% 3.12/0.99  --clausifier                            res/vclausify_rel
% 3.12/0.99  --clausifier_options                    --mode clausify
% 3.12/0.99  --stdin                                 false
% 3.12/0.99  --stats_out                             all
% 3.12/0.99  
% 3.12/0.99  ------ General Options
% 3.12/0.99  
% 3.12/0.99  --fof                                   false
% 3.12/0.99  --time_out_real                         305.
% 3.12/0.99  --time_out_virtual                      -1.
% 3.12/0.99  --symbol_type_check                     false
% 3.12/0.99  --clausify_out                          false
% 3.12/0.99  --sig_cnt_out                           false
% 3.12/0.99  --trig_cnt_out                          false
% 3.12/0.99  --trig_cnt_out_tolerance                1.
% 3.12/0.99  --trig_cnt_out_sk_spl                   false
% 3.12/0.99  --abstr_cl_out                          false
% 3.12/0.99  
% 3.12/0.99  ------ Global Options
% 3.12/0.99  
% 3.12/0.99  --schedule                              default
% 3.12/0.99  --add_important_lit                     false
% 3.12/0.99  --prop_solver_per_cl                    1000
% 3.12/0.99  --min_unsat_core                        false
% 3.12/0.99  --soft_assumptions                      false
% 3.12/0.99  --soft_lemma_size                       3
% 3.12/0.99  --prop_impl_unit_size                   0
% 3.12/0.99  --prop_impl_unit                        []
% 3.12/0.99  --share_sel_clauses                     true
% 3.12/0.99  --reset_solvers                         false
% 3.12/0.99  --bc_imp_inh                            [conj_cone]
% 3.12/0.99  --conj_cone_tolerance                   3.
% 3.12/0.99  --extra_neg_conj                        none
% 3.12/0.99  --large_theory_mode                     true
% 3.12/0.99  --prolific_symb_bound                   200
% 3.12/0.99  --lt_threshold                          2000
% 3.12/0.99  --clause_weak_htbl                      true
% 3.12/0.99  --gc_record_bc_elim                     false
% 3.12/0.99  
% 3.12/0.99  ------ Preprocessing Options
% 3.12/0.99  
% 3.12/0.99  --preprocessing_flag                    true
% 3.12/0.99  --time_out_prep_mult                    0.1
% 3.12/0.99  --splitting_mode                        input
% 3.12/0.99  --splitting_grd                         true
% 3.12/0.99  --splitting_cvd                         false
% 3.12/0.99  --splitting_cvd_svl                     false
% 3.12/0.99  --splitting_nvd                         32
% 3.12/0.99  --sub_typing                            true
% 3.12/0.99  --prep_gs_sim                           true
% 3.12/0.99  --prep_unflatten                        true
% 3.12/0.99  --prep_res_sim                          true
% 3.12/0.99  --prep_upred                            true
% 3.12/0.99  --prep_sem_filter                       exhaustive
% 3.12/0.99  --prep_sem_filter_out                   false
% 3.12/0.99  --pred_elim                             true
% 3.12/0.99  --res_sim_input                         true
% 3.12/0.99  --eq_ax_congr_red                       true
% 3.12/0.99  --pure_diseq_elim                       true
% 3.12/0.99  --brand_transform                       false
% 3.12/0.99  --non_eq_to_eq                          false
% 3.12/0.99  --prep_def_merge                        true
% 3.12/0.99  --prep_def_merge_prop_impl              false
% 3.12/0.99  --prep_def_merge_mbd                    true
% 3.12/0.99  --prep_def_merge_tr_red                 false
% 3.12/0.99  --prep_def_merge_tr_cl                  false
% 3.12/0.99  --smt_preprocessing                     true
% 3.12/0.99  --smt_ac_axioms                         fast
% 3.12/0.99  --preprocessed_out                      false
% 3.12/0.99  --preprocessed_stats                    false
% 3.12/0.99  
% 3.12/0.99  ------ Abstraction refinement Options
% 3.12/0.99  
% 3.12/0.99  --abstr_ref                             []
% 3.12/0.99  --abstr_ref_prep                        false
% 3.12/0.99  --abstr_ref_until_sat                   false
% 3.12/0.99  --abstr_ref_sig_restrict                funpre
% 3.12/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.12/0.99  --abstr_ref_under                       []
% 3.12/0.99  
% 3.12/0.99  ------ SAT Options
% 3.12/0.99  
% 3.12/0.99  --sat_mode                              false
% 3.12/0.99  --sat_fm_restart_options                ""
% 3.12/0.99  --sat_gr_def                            false
% 3.12/0.99  --sat_epr_types                         true
% 3.12/0.99  --sat_non_cyclic_types                  false
% 3.12/0.99  --sat_finite_models                     false
% 3.12/0.99  --sat_fm_lemmas                         false
% 3.12/0.99  --sat_fm_prep                           false
% 3.12/0.99  --sat_fm_uc_incr                        true
% 3.12/0.99  --sat_out_model                         small
% 3.12/0.99  --sat_out_clauses                       false
% 3.12/0.99  
% 3.12/0.99  ------ QBF Options
% 3.12/0.99  
% 3.12/0.99  --qbf_mode                              false
% 3.12/0.99  --qbf_elim_univ                         false
% 3.12/0.99  --qbf_dom_inst                          none
% 3.12/0.99  --qbf_dom_pre_inst                      false
% 3.12/0.99  --qbf_sk_in                             false
% 3.12/0.99  --qbf_pred_elim                         true
% 3.12/0.99  --qbf_split                             512
% 3.12/0.99  
% 3.12/0.99  ------ BMC1 Options
% 3.12/0.99  
% 3.12/0.99  --bmc1_incremental                      false
% 3.12/0.99  --bmc1_axioms                           reachable_all
% 3.12/0.99  --bmc1_min_bound                        0
% 3.12/0.99  --bmc1_max_bound                        -1
% 3.12/0.99  --bmc1_max_bound_default                -1
% 3.12/0.99  --bmc1_symbol_reachability              true
% 3.12/0.99  --bmc1_property_lemmas                  false
% 3.12/0.99  --bmc1_k_induction                      false
% 3.12/0.99  --bmc1_non_equiv_states                 false
% 3.12/0.99  --bmc1_deadlock                         false
% 3.12/0.99  --bmc1_ucm                              false
% 3.12/0.99  --bmc1_add_unsat_core                   none
% 3.12/0.99  --bmc1_unsat_core_children              false
% 3.12/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.12/0.99  --bmc1_out_stat                         full
% 3.12/0.99  --bmc1_ground_init                      false
% 3.12/0.99  --bmc1_pre_inst_next_state              false
% 3.12/0.99  --bmc1_pre_inst_state                   false
% 3.12/0.99  --bmc1_pre_inst_reach_state             false
% 3.12/0.99  --bmc1_out_unsat_core                   false
% 3.12/0.99  --bmc1_aig_witness_out                  false
% 3.12/0.99  --bmc1_verbose                          false
% 3.12/0.99  --bmc1_dump_clauses_tptp                false
% 3.12/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.12/0.99  --bmc1_dump_file                        -
% 3.12/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.12/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.12/0.99  --bmc1_ucm_extend_mode                  1
% 3.12/0.99  --bmc1_ucm_init_mode                    2
% 3.12/0.99  --bmc1_ucm_cone_mode                    none
% 3.12/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.12/0.99  --bmc1_ucm_relax_model                  4
% 3.12/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.12/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.12/0.99  --bmc1_ucm_layered_model                none
% 3.12/0.99  --bmc1_ucm_max_lemma_size               10
% 3.12/0.99  
% 3.12/0.99  ------ AIG Options
% 3.12/0.99  
% 3.12/0.99  --aig_mode                              false
% 3.12/0.99  
% 3.12/0.99  ------ Instantiation Options
% 3.12/0.99  
% 3.12/0.99  --instantiation_flag                    true
% 3.12/0.99  --inst_sos_flag                         false
% 3.12/0.99  --inst_sos_phase                        true
% 3.12/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.12/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.12/0.99  --inst_lit_sel_side                     none
% 3.12/0.99  --inst_solver_per_active                1400
% 3.12/0.99  --inst_solver_calls_frac                1.
% 3.12/0.99  --inst_passive_queue_type               priority_queues
% 3.12/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.12/0.99  --inst_passive_queues_freq              [25;2]
% 3.12/0.99  --inst_dismatching                      true
% 3.12/0.99  --inst_eager_unprocessed_to_passive     true
% 3.12/0.99  --inst_prop_sim_given                   true
% 3.12/0.99  --inst_prop_sim_new                     false
% 3.12/0.99  --inst_subs_new                         false
% 3.12/0.99  --inst_eq_res_simp                      false
% 3.12/0.99  --inst_subs_given                       false
% 3.12/0.99  --inst_orphan_elimination               true
% 3.12/0.99  --inst_learning_loop_flag               true
% 3.12/0.99  --inst_learning_start                   3000
% 3.12/0.99  --inst_learning_factor                  2
% 3.12/0.99  --inst_start_prop_sim_after_learn       3
% 3.12/0.99  --inst_sel_renew                        solver
% 3.12/0.99  --inst_lit_activity_flag                true
% 3.12/0.99  --inst_restr_to_given                   false
% 3.12/0.99  --inst_activity_threshold               500
% 3.12/0.99  --inst_out_proof                        true
% 3.12/0.99  
% 3.12/0.99  ------ Resolution Options
% 3.12/0.99  
% 3.12/0.99  --resolution_flag                       false
% 3.12/0.99  --res_lit_sel                           adaptive
% 3.12/0.99  --res_lit_sel_side                      none
% 3.12/0.99  --res_ordering                          kbo
% 3.12/0.99  --res_to_prop_solver                    active
% 3.12/0.99  --res_prop_simpl_new                    false
% 3.12/0.99  --res_prop_simpl_given                  true
% 3.12/0.99  --res_passive_queue_type                priority_queues
% 3.12/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.12/0.99  --res_passive_queues_freq               [15;5]
% 3.12/0.99  --res_forward_subs                      full
% 3.12/0.99  --res_backward_subs                     full
% 3.12/0.99  --res_forward_subs_resolution           true
% 3.12/0.99  --res_backward_subs_resolution          true
% 3.12/0.99  --res_orphan_elimination                true
% 3.12/0.99  --res_time_limit                        2.
% 3.12/0.99  --res_out_proof                         true
% 3.12/0.99  
% 3.12/0.99  ------ Superposition Options
% 3.12/0.99  
% 3.12/0.99  --superposition_flag                    true
% 3.12/0.99  --sup_passive_queue_type                priority_queues
% 3.12/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.12/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.12/0.99  --demod_completeness_check              fast
% 3.12/0.99  --demod_use_ground                      true
% 3.12/0.99  --sup_to_prop_solver                    passive
% 3.12/0.99  --sup_prop_simpl_new                    true
% 3.12/0.99  --sup_prop_simpl_given                  true
% 3.12/0.99  --sup_fun_splitting                     false
% 3.12/0.99  --sup_smt_interval                      50000
% 3.12/0.99  
% 3.12/0.99  ------ Superposition Simplification Setup
% 3.12/0.99  
% 3.12/0.99  --sup_indices_passive                   []
% 3.12/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.12/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/0.99  --sup_full_bw                           [BwDemod]
% 3.12/0.99  --sup_immed_triv                        [TrivRules]
% 3.12/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.12/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/0.99  --sup_immed_bw_main                     []
% 3.12/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.12/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.12/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.12/0.99  
% 3.12/0.99  ------ Combination Options
% 3.12/0.99  
% 3.12/0.99  --comb_res_mult                         3
% 3.12/0.99  --comb_sup_mult                         2
% 3.12/0.99  --comb_inst_mult                        10
% 3.12/0.99  
% 3.12/0.99  ------ Debug Options
% 3.12/0.99  
% 3.12/0.99  --dbg_backtrace                         false
% 3.12/0.99  --dbg_dump_prop_clauses                 false
% 3.12/0.99  --dbg_dump_prop_clauses_file            -
% 3.12/0.99  --dbg_out_stat                          false
% 3.12/0.99  
% 3.12/0.99  
% 3.12/0.99  
% 3.12/0.99  
% 3.12/0.99  ------ Proving...
% 3.12/0.99  
% 3.12/0.99  
% 3.12/0.99  % SZS status Theorem for theBenchmark.p
% 3.12/0.99  
% 3.12/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.12/0.99  
% 3.12/0.99  fof(f14,conjecture,(
% 3.12/0.99    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 3.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f15,negated_conjecture,(
% 3.12/0.99    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 3.12/0.99    inference(negated_conjecture,[],[f14])).
% 3.12/0.99  
% 3.12/0.99  fof(f35,plain,(
% 3.12/0.99    ? [X0] : (? [X1] : ((X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.12/0.99    inference(ennf_transformation,[],[f15])).
% 3.12/0.99  
% 3.12/0.99  fof(f36,plain,(
% 3.12/0.99    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.12/0.99    inference(flattening,[],[f35])).
% 3.12/0.99  
% 3.12/0.99  fof(f46,plain,(
% 3.12/0.99    ( ! [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) => (sK3 != X0 & r4_wellord1(k1_wellord2(X0),k1_wellord2(sK3)) & v3_ordinal1(sK3))) )),
% 3.12/0.99    introduced(choice_axiom,[])).
% 3.12/0.99  
% 3.12/0.99  fof(f45,plain,(
% 3.12/0.99    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : (sK2 != X1 & r4_wellord1(k1_wellord2(sK2),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK2))),
% 3.12/0.99    introduced(choice_axiom,[])).
% 3.12/0.99  
% 3.12/0.99  fof(f47,plain,(
% 3.12/0.99    (sK2 != sK3 & r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) & v3_ordinal1(sK3)) & v3_ordinal1(sK2)),
% 3.12/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f36,f46,f45])).
% 3.12/0.99  
% 3.12/0.99  fof(f70,plain,(
% 3.12/0.99    v3_ordinal1(sK2)),
% 3.12/0.99    inference(cnf_transformation,[],[f47])).
% 3.12/0.99  
% 3.12/0.99  fof(f71,plain,(
% 3.12/0.99    v3_ordinal1(sK3)),
% 3.12/0.99    inference(cnf_transformation,[],[f47])).
% 3.12/0.99  
% 3.12/0.99  fof(f2,axiom,(
% 3.12/0.99    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 3.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f16,plain,(
% 3.12/0.99    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 3.12/0.99    inference(ennf_transformation,[],[f2])).
% 3.12/0.99  
% 3.12/0.99  fof(f17,plain,(
% 3.12/0.99    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.12/0.99    inference(flattening,[],[f16])).
% 3.12/0.99  
% 3.12/0.99  fof(f51,plain,(
% 3.12/0.99    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.12/0.99    inference(cnf_transformation,[],[f17])).
% 3.12/0.99  
% 3.12/0.99  fof(f3,axiom,(
% 3.12/0.99    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 3.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f18,plain,(
% 3.12/0.99    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 3.12/0.99    inference(ennf_transformation,[],[f3])).
% 3.12/0.99  
% 3.12/0.99  fof(f19,plain,(
% 3.12/0.99    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.12/0.99    inference(flattening,[],[f18])).
% 3.12/0.99  
% 3.12/0.99  fof(f39,plain,(
% 3.12/0.99    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.12/0.99    inference(nnf_transformation,[],[f19])).
% 3.12/0.99  
% 3.12/0.99  fof(f52,plain,(
% 3.12/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.12/0.99    inference(cnf_transformation,[],[f39])).
% 3.12/0.99  
% 3.12/0.99  fof(f13,axiom,(
% 3.12/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0))),
% 3.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f34,plain,(
% 3.12/0.99    ! [X0,X1] : (k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) | ~r1_tarski(X0,X1))),
% 3.12/0.99    inference(ennf_transformation,[],[f13])).
% 3.12/0.99  
% 3.12/0.99  fof(f69,plain,(
% 3.12/0.99    ( ! [X0,X1] : (k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) | ~r1_tarski(X0,X1)) )),
% 3.12/0.99    inference(cnf_transformation,[],[f34])).
% 3.12/0.99  
% 3.12/0.99  fof(f1,axiom,(
% 3.12/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f37,plain,(
% 3.12/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.12/0.99    inference(nnf_transformation,[],[f1])).
% 3.12/0.99  
% 3.12/0.99  fof(f38,plain,(
% 3.12/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.12/0.99    inference(flattening,[],[f37])).
% 3.12/0.99  
% 3.12/0.99  fof(f48,plain,(
% 3.12/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.12/0.99    inference(cnf_transformation,[],[f38])).
% 3.12/0.99  
% 3.12/0.99  fof(f75,plain,(
% 3.12/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.12/0.99    inference(equality_resolution,[],[f48])).
% 3.12/0.99  
% 3.12/0.99  fof(f10,axiom,(
% 3.12/0.99    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 3.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f66,plain,(
% 3.12/0.99    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 3.12/0.99    inference(cnf_transformation,[],[f10])).
% 3.12/0.99  
% 3.12/0.99  fof(f5,axiom,(
% 3.12/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0))),
% 3.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f22,plain,(
% 3.12/0.99    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2))),
% 3.12/0.99    inference(ennf_transformation,[],[f5])).
% 3.12/0.99  
% 3.12/0.99  fof(f55,plain,(
% 3.12/0.99    ( ! [X2,X0,X1] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2)) )),
% 3.12/0.99    inference(cnf_transformation,[],[f22])).
% 3.12/0.99  
% 3.12/0.99  fof(f4,axiom,(
% 3.12/0.99    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 3.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f20,plain,(
% 3.12/0.99    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.12/0.99    inference(ennf_transformation,[],[f4])).
% 3.12/0.99  
% 3.12/0.99  fof(f21,plain,(
% 3.12/0.99    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.12/0.99    inference(flattening,[],[f20])).
% 3.12/0.99  
% 3.12/0.99  fof(f54,plain,(
% 3.12/0.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.12/0.99    inference(cnf_transformation,[],[f21])).
% 3.12/0.99  
% 3.12/0.99  fof(f11,axiom,(
% 3.12/0.99    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => k1_wellord1(k1_wellord2(X1),X0) = X0)))),
% 3.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f31,plain,(
% 3.12/0.99    ! [X0] : (! [X1] : ((k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.12/0.99    inference(ennf_transformation,[],[f11])).
% 3.12/0.99  
% 3.12/0.99  fof(f32,plain,(
% 3.12/0.99    ! [X0] : (! [X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.12/0.99    inference(flattening,[],[f31])).
% 3.12/0.99  
% 3.12/0.99  fof(f67,plain,(
% 3.12/0.99    ( ! [X0,X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.12/0.99    inference(cnf_transformation,[],[f32])).
% 3.12/0.99  
% 3.12/0.99  fof(f73,plain,(
% 3.12/0.99    sK2 != sK3),
% 3.12/0.99    inference(cnf_transformation,[],[f47])).
% 3.12/0.99  
% 3.12/0.99  fof(f50,plain,(
% 3.12/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.12/0.99    inference(cnf_transformation,[],[f38])).
% 3.12/0.99  
% 3.12/0.99  fof(f8,axiom,(
% 3.12/0.99    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 3.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f27,plain,(
% 3.12/0.99    ! [X0] : ((! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 3.12/0.99    inference(ennf_transformation,[],[f8])).
% 3.12/0.99  
% 3.12/0.99  fof(f28,plain,(
% 3.12/0.99    ! [X0] : (! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 3.12/0.99    inference(flattening,[],[f27])).
% 3.12/0.99  
% 3.12/0.99  fof(f58,plain,(
% 3.12/0.99    ( ! [X0,X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0)) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 3.12/0.99    inference(cnf_transformation,[],[f28])).
% 3.12/0.99  
% 3.12/0.99  fof(f12,axiom,(
% 3.12/0.99    ! [X0] : (v3_ordinal1(X0) => v2_wellord1(k1_wellord2(X0)))),
% 3.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f33,plain,(
% 3.12/0.99    ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0))),
% 3.12/0.99    inference(ennf_transformation,[],[f12])).
% 3.12/0.99  
% 3.12/0.99  fof(f68,plain,(
% 3.12/0.99    ( ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 3.12/0.99    inference(cnf_transformation,[],[f33])).
% 3.12/0.99  
% 3.12/0.99  fof(f9,axiom,(
% 3.12/0.99    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 3.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f29,plain,(
% 3.12/0.99    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 3.12/0.99    inference(ennf_transformation,[],[f9])).
% 3.12/0.99  
% 3.12/0.99  fof(f30,plain,(
% 3.12/0.99    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 3.12/0.99    inference(flattening,[],[f29])).
% 3.12/0.99  
% 3.12/0.99  fof(f40,plain,(
% 3.12/0.99    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 3.12/0.99    inference(nnf_transformation,[],[f30])).
% 3.12/0.99  
% 3.12/0.99  fof(f41,plain,(
% 3.12/0.99    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 3.12/0.99    inference(flattening,[],[f40])).
% 3.12/0.99  
% 3.12/0.99  fof(f42,plain,(
% 3.12/0.99    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 3.12/0.99    inference(rectify,[],[f41])).
% 3.12/0.99  
% 3.12/0.99  fof(f43,plain,(
% 3.12/0.99    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK0(X0,X1),sK1(X0,X1)) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & (r1_tarski(sK0(X0,X1),sK1(X0,X1)) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & r2_hidden(sK1(X0,X1),X0) & r2_hidden(sK0(X0,X1),X0)))),
% 3.12/0.99    introduced(choice_axiom,[])).
% 3.12/0.99  
% 3.12/0.99  fof(f44,plain,(
% 3.12/0.99    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK0(X0,X1),sK1(X0,X1)) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & (r1_tarski(sK0(X0,X1),sK1(X0,X1)) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & r2_hidden(sK1(X0,X1),X0) & r2_hidden(sK0(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 3.12/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f43])).
% 3.12/0.99  
% 3.12/0.99  fof(f59,plain,(
% 3.12/0.99    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 3.12/0.99    inference(cnf_transformation,[],[f44])).
% 3.12/0.99  
% 3.12/0.99  fof(f82,plain,(
% 3.12/0.99    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 3.12/0.99    inference(equality_resolution,[],[f59])).
% 3.12/0.99  
% 3.12/0.99  fof(f72,plain,(
% 3.12/0.99    r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))),
% 3.12/0.99    inference(cnf_transformation,[],[f47])).
% 3.12/0.99  
% 3.12/0.99  fof(f6,axiom,(
% 3.12/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 3.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f23,plain,(
% 3.12/0.99    ! [X0] : (! [X1] : ((r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.12/0.99    inference(ennf_transformation,[],[f6])).
% 3.12/0.99  
% 3.12/0.99  fof(f24,plain,(
% 3.12/0.99    ! [X0] : (! [X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.12/0.99    inference(flattening,[],[f23])).
% 3.12/0.99  
% 3.12/0.99  fof(f56,plain,(
% 3.12/0.99    ( ! [X0,X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.12/0.99    inference(cnf_transformation,[],[f24])).
% 3.12/0.99  
% 3.12/0.99  fof(f7,axiom,(
% 3.12/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ((r4_wellord1(X1,X2) & r4_wellord1(X0,X1)) => r4_wellord1(X0,X2)))))),
% 3.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f25,plain,(
% 3.12/0.99    ! [X0] : (! [X1] : (! [X2] : ((r4_wellord1(X0,X2) | (~r4_wellord1(X1,X2) | ~r4_wellord1(X0,X1))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.12/0.99    inference(ennf_transformation,[],[f7])).
% 3.12/0.99  
% 3.12/0.99  fof(f26,plain,(
% 3.12/0.99    ! [X0] : (! [X1] : (! [X2] : (r4_wellord1(X0,X2) | ~r4_wellord1(X1,X2) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.12/0.99    inference(flattening,[],[f25])).
% 3.12/0.99  
% 3.12/0.99  fof(f57,plain,(
% 3.12/0.99    ( ! [X2,X0,X1] : (r4_wellord1(X0,X2) | ~r4_wellord1(X1,X2) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.12/0.99    inference(cnf_transformation,[],[f26])).
% 3.12/0.99  
% 3.12/0.99  cnf(c_25,negated_conjecture,
% 3.12/0.99      ( v3_ordinal1(sK2) ),
% 3.12/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_859,plain,
% 3.12/0.99      ( v3_ordinal1(sK2) = iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_24,negated_conjecture,
% 3.12/0.99      ( v3_ordinal1(sK3) ),
% 3.12/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_860,plain,
% 3.12/0.99      ( v3_ordinal1(sK3) = iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3,plain,
% 3.12/0.99      ( r1_ordinal1(X0,X1)
% 3.12/0.99      | r1_ordinal1(X1,X0)
% 3.12/0.99      | ~ v3_ordinal1(X1)
% 3.12/0.99      | ~ v3_ordinal1(X0) ),
% 3.12/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_877,plain,
% 3.12/0.99      ( r1_ordinal1(X0,X1) = iProver_top
% 3.12/0.99      | r1_ordinal1(X1,X0) = iProver_top
% 3.12/0.99      | v3_ordinal1(X0) != iProver_top
% 3.12/0.99      | v3_ordinal1(X1) != iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_5,plain,
% 3.12/0.99      ( ~ r1_ordinal1(X0,X1)
% 3.12/0.99      | r1_tarski(X0,X1)
% 3.12/0.99      | ~ v3_ordinal1(X1)
% 3.12/0.99      | ~ v3_ordinal1(X0) ),
% 3.12/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_875,plain,
% 3.12/0.99      ( r1_ordinal1(X0,X1) != iProver_top
% 3.12/0.99      | r1_tarski(X0,X1) = iProver_top
% 3.12/0.99      | v3_ordinal1(X0) != iProver_top
% 3.12/0.99      | v3_ordinal1(X1) != iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2065,plain,
% 3.12/0.99      ( r1_ordinal1(X0,X1) = iProver_top
% 3.12/0.99      | r1_tarski(X1,X0) = iProver_top
% 3.12/0.99      | v3_ordinal1(X0) != iProver_top
% 3.12/0.99      | v3_ordinal1(X1) != iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_877,c_875]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2895,plain,
% 3.12/0.99      ( r1_tarski(X0,X1) = iProver_top
% 3.12/0.99      | r1_tarski(X1,X0) = iProver_top
% 3.12/0.99      | v3_ordinal1(X0) != iProver_top
% 3.12/0.99      | v3_ordinal1(X1) != iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_2065,c_875]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_21,plain,
% 3.12/0.99      ( ~ r1_tarski(X0,X1)
% 3.12/0.99      | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ),
% 3.12/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_862,plain,
% 3.12/0.99      ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 3.12/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2905,plain,
% 3.12/0.99      ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 3.12/0.99      | r1_tarski(X0,X1) = iProver_top
% 3.12/0.99      | v3_ordinal1(X0) != iProver_top
% 3.12/0.99      | v3_ordinal1(X1) != iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_2895,c_862]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2963,plain,
% 3.12/0.99      ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 3.12/0.99      | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
% 3.12/0.99      | v3_ordinal1(X1) != iProver_top
% 3.12/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_2905,c_862]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3178,plain,
% 3.12/0.99      ( k2_wellord1(k1_wellord2(X0),sK3) = k1_wellord2(sK3)
% 3.12/0.99      | k2_wellord1(k1_wellord2(sK3),X0) = k1_wellord2(X0)
% 3.12/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_860,c_2963]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3347,plain,
% 3.12/0.99      ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
% 3.12/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_859,c_3178]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2,plain,
% 3.12/0.99      ( r1_tarski(X0,X0) ),
% 3.12/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_878,plain,
% 3.12/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1157,plain,
% 3.12/0.99      ( k2_wellord1(k1_wellord2(X0),X0) = k1_wellord2(X0) ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_878,c_862]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_18,plain,
% 3.12/0.99      ( v1_relat_1(k1_wellord2(X0)) ),
% 3.12/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_864,plain,
% 3.12/0.99      ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_7,plain,
% 3.12/0.99      ( ~ v1_relat_1(X0)
% 3.12/0.99      | k2_wellord1(k2_wellord1(X0,X1),X2) = k2_wellord1(k2_wellord1(X0,X2),X1) ),
% 3.12/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_873,plain,
% 3.12/0.99      ( k2_wellord1(k2_wellord1(X0,X1),X2) = k2_wellord1(k2_wellord1(X0,X2),X1)
% 3.12/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1303,plain,
% 3.12/0.99      ( k2_wellord1(k2_wellord1(k1_wellord2(X0),X1),X2) = k2_wellord1(k2_wellord1(k1_wellord2(X0),X2),X1) ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_864,c_873]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1796,plain,
% 3.12/0.99      ( k2_wellord1(k2_wellord1(k1_wellord2(X0),X1),X0) = k2_wellord1(k1_wellord2(X0),X1) ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_1157,c_1303]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3355,plain,
% 3.12/0.99      ( k2_wellord1(k1_wellord2(sK3),sK2) = k2_wellord1(k1_wellord2(sK2),sK3)
% 3.12/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_3347,c_1796]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3537,plain,
% 3.12/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.12/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_3355,c_3347]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3629,plain,
% 3.12/0.99      ( k2_wellord1(k1_wellord2(sK3),sK2) = k2_wellord1(k1_wellord2(sK2),sK3)
% 3.12/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_3537,c_1796]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_6,plain,
% 3.12/0.99      ( r2_hidden(X0,X1)
% 3.12/0.99      | r2_hidden(X1,X0)
% 3.12/0.99      | ~ v3_ordinal1(X1)
% 3.12/0.99      | ~ v3_ordinal1(X0)
% 3.12/0.99      | X1 = X0 ),
% 3.12/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_874,plain,
% 3.12/0.99      ( X0 = X1
% 3.12/0.99      | r2_hidden(X1,X0) = iProver_top
% 3.12/0.99      | r2_hidden(X0,X1) = iProver_top
% 3.12/0.99      | v3_ordinal1(X1) != iProver_top
% 3.12/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_19,plain,
% 3.12/0.99      ( ~ r2_hidden(X0,X1)
% 3.12/0.99      | ~ v3_ordinal1(X1)
% 3.12/0.99      | ~ v3_ordinal1(X0)
% 3.12/0.99      | k1_wellord1(k1_wellord2(X1),X0) = X0 ),
% 3.12/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_863,plain,
% 3.12/0.99      ( k1_wellord1(k1_wellord2(X0),X1) = X1
% 3.12/0.99      | r2_hidden(X1,X0) != iProver_top
% 3.12/0.99      | v3_ordinal1(X1) != iProver_top
% 3.12/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2158,plain,
% 3.12/0.99      ( X0 = X1
% 3.12/0.99      | k1_wellord1(k1_wellord2(X0),X1) = X1
% 3.12/0.99      | r2_hidden(X0,X1) = iProver_top
% 3.12/0.99      | v3_ordinal1(X1) != iProver_top
% 3.12/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_874,c_863]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3815,plain,
% 3.12/0.99      ( X0 = X1
% 3.12/0.99      | k1_wellord1(k1_wellord2(X0),X1) = X1
% 3.12/0.99      | k1_wellord1(k1_wellord2(X1),X0) = X0
% 3.12/0.99      | v3_ordinal1(X1) != iProver_top
% 3.12/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_2158,c_863]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3968,plain,
% 3.12/0.99      ( k1_wellord1(k1_wellord2(X0),sK3) = sK3
% 3.12/0.99      | k1_wellord1(k1_wellord2(sK3),X0) = X0
% 3.12/0.99      | sK3 = X0
% 3.12/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_860,c_3815]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_4085,plain,
% 3.12/0.99      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.12/0.99      | k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.12/0.99      | sK3 = sK2 ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_859,c_3968]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_22,negated_conjecture,
% 3.12/0.99      ( sK2 != sK3 ),
% 3.12/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_74,plain,
% 3.12/0.99      ( ~ r1_ordinal1(sK2,sK2)
% 3.12/0.99      | r1_tarski(sK2,sK2)
% 3.12/0.99      | ~ v3_ordinal1(sK2) ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_80,plain,
% 3.12/0.99      ( r1_ordinal1(sK2,sK2) | ~ v3_ordinal1(sK2) ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_0,plain,
% 3.12/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.12/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_87,plain,
% 3.12/0.99      ( ~ r1_tarski(sK2,sK2) | sK2 = sK2 ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_454,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1104,plain,
% 3.12/0.99      ( sK3 != X0 | sK2 != X0 | sK2 = sK3 ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_454]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1105,plain,
% 3.12/0.99      ( sK3 != sK2 | sK2 = sK3 | sK2 != sK2 ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_1104]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_4092,plain,
% 3.12/0.99      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.12/0.99      | k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
% 3.12/0.99      inference(global_propositional_subsumption,
% 3.12/0.99                [status(thm)],
% 3.12/0.99                [c_4085,c_25,c_22,c_74,c_80,c_87,c_1105]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_4093,plain,
% 3.12/0.99      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.12/0.99      | k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
% 3.12/0.99      inference(renaming,[status(thm)],[c_4092]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_10,plain,
% 3.12/0.99      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
% 3.12/0.99      | ~ r2_hidden(X1,k3_relat_1(X0))
% 3.12/0.99      | ~ v2_wellord1(X0)
% 3.12/0.99      | ~ v1_relat_1(X0) ),
% 3.12/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_20,plain,
% 3.12/0.99      ( v2_wellord1(k1_wellord2(X0)) | ~ v3_ordinal1(X0) ),
% 3.12/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_278,plain,
% 3.12/0.99      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
% 3.12/0.99      | ~ r2_hidden(X1,k3_relat_1(X0))
% 3.12/0.99      | ~ v1_relat_1(X0)
% 3.12/0.99      | ~ v3_ordinal1(X2)
% 3.12/0.99      | k1_wellord2(X2) != X0 ),
% 3.12/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_279,plain,
% 3.12/0.99      ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
% 3.12/0.99      | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
% 3.12/0.99      | ~ v1_relat_1(k1_wellord2(X0))
% 3.12/0.99      | ~ v3_ordinal1(X0) ),
% 3.12/0.99      inference(unflattening,[status(thm)],[c_278]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_283,plain,
% 3.12/0.99      ( ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
% 3.12/0.99      | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
% 3.12/0.99      | ~ v3_ordinal1(X0) ),
% 3.12/0.99      inference(global_propositional_subsumption,
% 3.12/0.99                [status(thm)],
% 3.12/0.99                [c_279,c_18]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_284,plain,
% 3.12/0.99      ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
% 3.12/0.99      | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
% 3.12/0.99      | ~ v3_ordinal1(X0) ),
% 3.12/0.99      inference(renaming,[status(thm)],[c_283]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_858,plain,
% 3.12/0.99      ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
% 3.12/0.99      | r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) != iProver_top
% 3.12/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_284]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_17,plain,
% 3.12/0.99      ( ~ v1_relat_1(k1_wellord2(X0))
% 3.12/0.99      | k3_relat_1(k1_wellord2(X0)) = X0 ),
% 3.12/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_147,plain,
% 3.12/0.99      ( k3_relat_1(k1_wellord2(X0)) = X0 ),
% 3.12/0.99      inference(global_propositional_subsumption,
% 3.12/0.99                [status(thm)],
% 3.12/0.99                [c_17,c_18]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_970,plain,
% 3.12/0.99      ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
% 3.12/0.99      | r2_hidden(X1,X0) != iProver_top
% 3.12/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.12/0.99      inference(light_normalisation,[status(thm)],[c_858,c_147]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_4096,plain,
% 3.12/0.99      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.12/0.99      | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top
% 3.12/0.99      | r2_hidden(sK2,sK3) != iProver_top
% 3.12/0.99      | v3_ordinal1(sK3) != iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_4093,c_970]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_26,plain,
% 3.12/0.99      ( v3_ordinal1(sK2) = iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_27,plain,
% 3.12/0.99      ( v3_ordinal1(sK3) = iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1115,plain,
% 3.12/0.99      ( r2_hidden(sK3,sK2)
% 3.12/0.99      | r2_hidden(sK2,sK3)
% 3.12/0.99      | ~ v3_ordinal1(sK3)
% 3.12/0.99      | ~ v3_ordinal1(sK2)
% 3.12/0.99      | sK2 = sK3 ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1116,plain,
% 3.12/0.99      ( sK2 = sK3
% 3.12/0.99      | r2_hidden(sK3,sK2) = iProver_top
% 3.12/0.99      | r2_hidden(sK2,sK3) = iProver_top
% 3.12/0.99      | v3_ordinal1(sK3) != iProver_top
% 3.12/0.99      | v3_ordinal1(sK2) != iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_1115]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1161,plain,
% 3.12/0.99      ( ~ r2_hidden(sK3,sK2)
% 3.12/0.99      | ~ v3_ordinal1(sK3)
% 3.12/0.99      | ~ v3_ordinal1(sK2)
% 3.12/0.99      | k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1162,plain,
% 3.12/0.99      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.12/0.99      | r2_hidden(sK3,sK2) != iProver_top
% 3.12/0.99      | v3_ordinal1(sK3) != iProver_top
% 3.12/0.99      | v3_ordinal1(sK2) != iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_1161]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_4244,plain,
% 3.12/0.99      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.12/0.99      | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top ),
% 3.12/0.99      inference(global_propositional_subsumption,
% 3.12/0.99                [status(thm)],
% 3.12/0.99                [c_4096,c_26,c_27,c_22,c_1116,c_1162]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_4499,plain,
% 3.12/0.99      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.12/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
% 3.12/0.99      | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_3629,c_4244]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_5825,plain,
% 3.12/0.99      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.12/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
% 3.12/0.99      | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK3)) != iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_3537,c_4499]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1791,plain,
% 3.12/0.99      ( v1_relat_1(k1_wellord2(sK3)) ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1792,plain,
% 3.12/0.99      ( v1_relat_1(k1_wellord2(sK3)) = iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_1791]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_23,negated_conjecture,
% 3.12/0.99      ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) ),
% 3.12/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_861,plain,
% 3.12/0.99      ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) = iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_8,plain,
% 3.12/0.99      ( ~ r4_wellord1(X0,X1)
% 3.12/0.99      | r4_wellord1(X1,X0)
% 3.12/0.99      | ~ v1_relat_1(X0)
% 3.12/0.99      | ~ v1_relat_1(X1) ),
% 3.12/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_872,plain,
% 3.12/0.99      ( r4_wellord1(X0,X1) != iProver_top
% 3.12/0.99      | r4_wellord1(X1,X0) = iProver_top
% 3.12/0.99      | v1_relat_1(X0) != iProver_top
% 3.12/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1868,plain,
% 3.12/0.99      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top
% 3.12/0.99      | v1_relat_1(k1_wellord2(sK3)) != iProver_top
% 3.12/0.99      | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_861,c_872]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_28,plain,
% 3.12/0.99      ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) = iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_38,plain,
% 3.12/0.99      ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_40,plain,
% 3.12/0.99      ( v1_relat_1(k1_wellord2(sK2)) = iProver_top ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_38]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1089,plain,
% 3.12/0.99      ( r4_wellord1(X0,k1_wellord2(X1))
% 3.12/0.99      | ~ r4_wellord1(k1_wellord2(X1),X0)
% 3.12/0.99      | ~ v1_relat_1(X0)
% 3.12/0.99      | ~ v1_relat_1(k1_wellord2(X1)) ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1250,plain,
% 3.12/0.99      ( ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
% 3.12/0.99      | r4_wellord1(k1_wellord2(X1),k1_wellord2(X0))
% 3.12/0.99      | ~ v1_relat_1(k1_wellord2(X1))
% 3.12/0.99      | ~ v1_relat_1(k1_wellord2(X0)) ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_1089]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1699,plain,
% 3.12/0.99      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2))
% 3.12/0.99      | ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
% 3.12/0.99      | ~ v1_relat_1(k1_wellord2(sK3))
% 3.12/0.99      | ~ v1_relat_1(k1_wellord2(sK2)) ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_1250]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1700,plain,
% 3.12/0.99      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top
% 3.12/0.99      | r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) != iProver_top
% 3.12/0.99      | v1_relat_1(k1_wellord2(sK3)) != iProver_top
% 3.12/0.99      | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_1699]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1871,plain,
% 3.12/0.99      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top ),
% 3.12/0.99      inference(global_propositional_subsumption,
% 3.12/0.99                [status(thm)],
% 3.12/0.99                [c_1868,c_28,c_40,c_1700,c_1792]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_9,plain,
% 3.12/0.99      ( ~ r4_wellord1(X0,X1)
% 3.12/0.99      | ~ r4_wellord1(X1,X2)
% 3.12/0.99      | r4_wellord1(X0,X2)
% 3.12/0.99      | ~ v1_relat_1(X2)
% 3.12/0.99      | ~ v1_relat_1(X0)
% 3.12/0.99      | ~ v1_relat_1(X1) ),
% 3.12/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_871,plain,
% 3.12/0.99      ( r4_wellord1(X0,X1) != iProver_top
% 3.12/0.99      | r4_wellord1(X1,X2) != iProver_top
% 3.12/0.99      | r4_wellord1(X0,X2) = iProver_top
% 3.12/0.99      | v1_relat_1(X0) != iProver_top
% 3.12/0.99      | v1_relat_1(X2) != iProver_top
% 3.12/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2192,plain,
% 3.12/0.99      ( r4_wellord1(k1_wellord2(sK3),X0) = iProver_top
% 3.12/0.99      | r4_wellord1(k1_wellord2(sK2),X0) != iProver_top
% 3.12/0.99      | v1_relat_1(X0) != iProver_top
% 3.12/0.99      | v1_relat_1(k1_wellord2(sK3)) != iProver_top
% 3.12/0.99      | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_1871,c_871]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2391,plain,
% 3.12/0.99      ( r4_wellord1(k1_wellord2(sK3),X0) = iProver_top
% 3.12/0.99      | r4_wellord1(k1_wellord2(sK2),X0) != iProver_top
% 3.12/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.12/0.99      inference(global_propositional_subsumption,
% 3.12/0.99                [status(thm)],
% 3.12/0.99                [c_2192,c_40,c_1792]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2400,plain,
% 3.12/0.99      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK3)) = iProver_top
% 3.12/0.99      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_861,c_2391]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_5828,plain,
% 3.12/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
% 3.12/0.99      | k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
% 3.12/0.99      inference(global_propositional_subsumption,
% 3.12/0.99                [status(thm)],
% 3.12/0.99                [c_5825,c_1792,c_2400]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_5829,plain,
% 3.12/0.99      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.12/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
% 3.12/0.99      inference(renaming,[status(thm)],[c_5828]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_5832,plain,
% 3.12/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
% 3.12/0.99      | r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top
% 3.12/0.99      | r2_hidden(sK3,sK2) != iProver_top
% 3.12/0.99      | v3_ordinal1(sK2) != iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_5829,c_970]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_463,plain,
% 3.12/0.99      ( X0 != X1 | k1_wellord2(X0) = k1_wellord2(X1) ),
% 3.12/0.99      theory(equality) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_475,plain,
% 3.12/0.99      ( k1_wellord2(sK2) = k1_wellord2(sK2) | sK2 != sK2 ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_463]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_460,plain,
% 3.12/0.99      ( ~ r4_wellord1(X0,X1) | r4_wellord1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.12/0.99      theory(equality) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1121,plain,
% 3.12/0.99      ( r4_wellord1(X0,X1)
% 3.12/0.99      | ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
% 3.12/0.99      | X1 != k1_wellord2(sK3)
% 3.12/0.99      | X0 != k1_wellord2(sK2) ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_460]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1198,plain,
% 3.12/0.99      ( r4_wellord1(X0,k2_wellord1(k1_wellord2(X1),sK3))
% 3.12/0.99      | ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
% 3.12/0.99      | X0 != k1_wellord2(sK2)
% 3.12/0.99      | k2_wellord1(k1_wellord2(X1),sK3) != k1_wellord2(sK3) ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_1121]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1884,plain,
% 3.12/0.99      ( r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(X0),sK3))
% 3.12/0.99      | ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
% 3.12/0.99      | k2_wellord1(k1_wellord2(X0),sK3) != k1_wellord2(sK3)
% 3.12/0.99      | k1_wellord2(sK2) != k1_wellord2(sK2) ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_1198]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1887,plain,
% 3.12/0.99      ( k2_wellord1(k1_wellord2(X0),sK3) != k1_wellord2(sK3)
% 3.12/0.99      | k1_wellord2(sK2) != k1_wellord2(sK2)
% 3.12/0.99      | r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(X0),sK3)) = iProver_top
% 3.12/0.99      | r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) != iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_1884]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1889,plain,
% 3.12/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) != k1_wellord2(sK3)
% 3.12/0.99      | k1_wellord2(sK2) != k1_wellord2(sK2)
% 3.12/0.99      | r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) = iProver_top
% 3.12/0.99      | r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) != iProver_top ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_1887]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_5971,plain,
% 3.12/0.99      ( r2_hidden(sK3,sK2) != iProver_top
% 3.12/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
% 3.12/0.99      inference(global_propositional_subsumption,
% 3.12/0.99                [status(thm)],
% 3.12/0.99                [c_5832,c_25,c_26,c_28,c_74,c_80,c_87,c_475,c_1889,
% 3.12/0.99                 c_3537]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_5972,plain,
% 3.12/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
% 3.12/0.99      | r2_hidden(sK3,sK2) != iProver_top ),
% 3.12/0.99      inference(renaming,[status(thm)],[c_5971]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_5980,plain,
% 3.12/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
% 3.12/0.99      | sK3 = sK2
% 3.12/0.99      | r2_hidden(sK2,sK3) = iProver_top
% 3.12/0.99      | v3_ordinal1(sK3) != iProver_top
% 3.12/0.99      | v3_ordinal1(sK2) != iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_874,c_5972]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_6388,plain,
% 3.12/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
% 3.12/0.99      | r2_hidden(sK2,sK3) = iProver_top ),
% 3.12/0.99      inference(global_propositional_subsumption,
% 3.12/0.99                [status(thm)],
% 3.12/0.99                [c_5980,c_25,c_26,c_27,c_22,c_74,c_80,c_87,c_1105]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_6394,plain,
% 3.12/0.99      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.12/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
% 3.12/0.99      | v3_ordinal1(sK3) != iProver_top
% 3.12/0.99      | v3_ordinal1(sK2) != iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_6388,c_863]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_6395,plain,
% 3.12/0.99      ( ~ v3_ordinal1(sK3)
% 3.12/0.99      | ~ v3_ordinal1(sK2)
% 3.12/0.99      | k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.12/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
% 3.12/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_6394]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_6397,plain,
% 3.12/0.99      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.12/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
% 3.12/0.99      inference(global_propositional_subsumption,
% 3.12/0.99                [status(thm)],
% 3.12/0.99                [c_6394,c_25,c_24,c_6395]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_6401,plain,
% 3.12/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
% 3.12/0.99      | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top
% 3.12/0.99      | r2_hidden(sK2,sK3) != iProver_top
% 3.12/0.99      | v3_ordinal1(sK3) != iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_6397,c_970]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_6993,plain,
% 3.12/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
% 3.12/0.99      | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top ),
% 3.12/0.99      inference(global_propositional_subsumption,
% 3.12/0.99                [status(thm)],
% 3.12/0.99                [c_6401,c_25,c_26,c_27,c_22,c_74,c_80,c_87,c_1105,c_5980]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_7000,plain,
% 3.12/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
% 3.12/0.99      | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_3629,c_6993]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_4495,plain,
% 3.12/0.99      ( k2_wellord1(k2_wellord1(k1_wellord2(sK2),sK3),sK3) = k2_wellord1(k1_wellord2(sK3),sK2)
% 3.12/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_3629,c_1796]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3630,plain,
% 3.12/0.99      ( k2_wellord1(k2_wellord1(k1_wellord2(sK2),X0),sK3) = k2_wellord1(k1_wellord2(sK3),X0)
% 3.12/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_3537,c_1303]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_6009,plain,
% 3.12/0.99      ( k2_wellord1(k1_wellord2(sK3),sK2) = k2_wellord1(k1_wellord2(sK3),sK3)
% 3.12/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_4495,c_3630]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_6012,plain,
% 3.12/0.99      ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK3)
% 3.12/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
% 3.12/0.99      inference(demodulation,[status(thm)],[c_6009,c_1157]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_6999,plain,
% 3.12/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2)
% 3.12/0.99      | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK3)) != iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_6012,c_6993]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_7014,plain,
% 3.12/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK2) ),
% 3.12/0.99      inference(global_propositional_subsumption,
% 3.12/0.99                [status(thm)],
% 3.12/0.99                [c_7000,c_1792,c_2400,c_6999]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_7032,plain,
% 3.12/0.99      ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
% 3.12/0.99      | k1_wellord2(sK3) = k1_wellord2(sK2) ),
% 3.12/0.99      inference(demodulation,[status(thm)],[c_7014,c_3355]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2159,plain,
% 3.12/0.99      ( X0 = X1
% 3.12/0.99      | k1_wellord1(k1_wellord2(X1),X0) = X0
% 3.12/0.99      | r2_hidden(X1,X0) = iProver_top
% 3.12/0.99      | v3_ordinal1(X1) != iProver_top
% 3.12/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_874,c_863]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_4251,plain,
% 3.12/0.99      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.12/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.12/0.99      | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) != iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_3347,c_4244]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_4324,plain,
% 3.12/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.12/0.99      | k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
% 3.12/0.99      inference(global_propositional_subsumption,
% 3.12/0.99                [status(thm)],
% 3.12/0.99                [c_4251,c_28,c_40,c_1700,c_1792]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_4325,plain,
% 3.12/0.99      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.12/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
% 3.12/0.99      inference(renaming,[status(thm)],[c_4324]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_4328,plain,
% 3.12/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.12/0.99      | r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top
% 3.12/0.99      | r2_hidden(sK3,sK2) != iProver_top
% 3.12/0.99      | v3_ordinal1(sK2) != iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_4325,c_970]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_4331,plain,
% 3.12/0.99      ( r2_hidden(sK3,sK2) != iProver_top
% 3.12/0.99      | r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top
% 3.12/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
% 3.12/0.99      inference(global_propositional_subsumption,
% 3.12/0.99                [status(thm)],
% 3.12/0.99                [c_4328,c_26]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_4332,plain,
% 3.12/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.12/0.99      | r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top
% 3.12/0.99      | r2_hidden(sK3,sK2) != iProver_top ),
% 3.12/0.99      inference(renaming,[status(thm)],[c_4331]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_7028,plain,
% 3.12/0.99      ( k1_wellord2(sK3) = k1_wellord2(sK2)
% 3.12/0.99      | r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK2)) != iProver_top
% 3.12/0.99      | r2_hidden(sK3,sK2) != iProver_top ),
% 3.12/0.99      inference(demodulation,[status(thm)],[c_7014,c_4332]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2191,plain,
% 3.12/0.99      ( r4_wellord1(k1_wellord2(sK3),X0) != iProver_top
% 3.12/0.99      | r4_wellord1(k1_wellord2(sK2),X0) = iProver_top
% 3.12/0.99      | v1_relat_1(X0) != iProver_top
% 3.12/0.99      | v1_relat_1(k1_wellord2(sK3)) != iProver_top
% 3.12/0.99      | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_861,c_871]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2300,plain,
% 3.12/0.99      ( r4_wellord1(k1_wellord2(sK3),X0) != iProver_top
% 3.12/0.99      | r4_wellord1(k1_wellord2(sK2),X0) = iProver_top
% 3.12/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.12/0.99      inference(global_propositional_subsumption,
% 3.12/0.99                [status(thm)],
% 3.12/0.99                [c_2191,c_40,c_1792]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2309,plain,
% 3.12/0.99      ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK2)) = iProver_top
% 3.12/0.99      | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_1871,c_2300]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_7417,plain,
% 3.12/0.99      ( k1_wellord2(sK3) = k1_wellord2(sK2)
% 3.12/0.99      | r2_hidden(sK3,sK2) != iProver_top ),
% 3.12/0.99      inference(global_propositional_subsumption,
% 3.12/0.99                [status(thm)],
% 3.12/0.99                [c_7028,c_40,c_2309]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_7425,plain,
% 3.12/0.99      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.12/0.99      | k1_wellord2(sK3) = k1_wellord2(sK2)
% 3.12/0.99      | sK3 = sK2
% 3.12/0.99      | v3_ordinal1(sK3) != iProver_top
% 3.12/0.99      | v3_ordinal1(sK2) != iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_2159,c_7417]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_7426,plain,
% 3.12/0.99      ( k1_wellord2(sK3) = k1_wellord2(sK2)
% 3.12/0.99      | sK3 = sK2
% 3.12/0.99      | r2_hidden(sK2,sK3) = iProver_top
% 3.12/0.99      | v3_ordinal1(sK3) != iProver_top
% 3.12/0.99      | v3_ordinal1(sK2) != iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_874,c_7417]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_7582,plain,
% 3.12/0.99      ( k1_wellord2(sK3) = k1_wellord2(sK2)
% 3.12/0.99      | r2_hidden(sK2,sK3) = iProver_top ),
% 3.12/0.99      inference(global_propositional_subsumption,
% 3.12/0.99                [status(thm)],
% 3.12/0.99                [c_7426,c_25,c_26,c_27,c_22,c_74,c_80,c_87,c_1105]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_7588,plain,
% 3.12/0.99      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.12/0.99      | k1_wellord2(sK3) = k1_wellord2(sK2)
% 3.12/0.99      | v3_ordinal1(sK3) != iProver_top
% 3.12/0.99      | v3_ordinal1(sK2) != iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_7582,c_863]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_7589,plain,
% 3.12/0.99      ( ~ v3_ordinal1(sK3)
% 3.12/0.99      | ~ v3_ordinal1(sK2)
% 3.12/0.99      | k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.12/0.99      | k1_wellord2(sK3) = k1_wellord2(sK2) ),
% 3.12/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_7588]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_7591,plain,
% 3.12/0.99      ( k1_wellord2(sK3) = k1_wellord2(sK2)
% 3.12/0.99      | k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
% 3.12/0.99      inference(global_propositional_subsumption,
% 3.12/0.99                [status(thm)],
% 3.12/0.99                [c_7425,c_25,c_26,c_27,c_22,c_74,c_80,c_87,c_1105]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_7592,plain,
% 3.12/0.99      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.12/0.99      | k1_wellord2(sK3) = k1_wellord2(sK2) ),
% 3.12/0.99      inference(renaming,[status(thm)],[c_7591]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_7595,plain,
% 3.12/0.99      ( k1_wellord2(sK3) = k1_wellord2(sK2)
% 3.12/0.99      | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top
% 3.12/0.99      | r2_hidden(sK2,sK3) != iProver_top
% 3.12/0.99      | v3_ordinal1(sK3) != iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_7592,c_970]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_7655,plain,
% 3.12/0.99      ( k1_wellord2(sK3) = k1_wellord2(sK2)
% 3.12/0.99      | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top ),
% 3.12/0.99      inference(global_propositional_subsumption,
% 3.12/0.99                [status(thm)],
% 3.12/0.99                [c_7595,c_25,c_26,c_27,c_22,c_74,c_80,c_87,c_1105,c_7426]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_7661,plain,
% 3.12/0.99      ( k1_wellord2(sK3) = k1_wellord2(sK2)
% 3.12/0.99      | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) != iProver_top ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_7032,c_7655]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_7669,plain,
% 3.12/0.99      ( k1_wellord2(sK3) = k1_wellord2(sK2) ),
% 3.12/0.99      inference(global_propositional_subsumption,
% 3.12/0.99                [status(thm)],
% 3.12/0.99                [c_7661,c_28,c_40,c_1700,c_1792]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_7724,plain,
% 3.12/0.99      ( k3_relat_1(k1_wellord2(sK2)) = sK3 ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_7669,c_147]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_7760,plain,
% 3.12/0.99      ( sK3 = sK2 ),
% 3.12/0.99      inference(demodulation,[status(thm)],[c_7724,c_147]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(contradiction,plain,
% 3.12/0.99      ( $false ),
% 3.12/0.99      inference(minisat,
% 3.12/0.99                [status(thm)],
% 3.12/0.99                [c_7760,c_1105,c_87,c_80,c_74,c_22,c_25]) ).
% 3.12/0.99  
% 3.12/0.99  
% 3.12/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.12/0.99  
% 3.12/0.99  ------                               Statistics
% 3.12/0.99  
% 3.12/0.99  ------ General
% 3.12/0.99  
% 3.12/0.99  abstr_ref_over_cycles:                  0
% 3.12/0.99  abstr_ref_under_cycles:                 0
% 3.12/0.99  gc_basic_clause_elim:                   0
% 3.12/0.99  forced_gc_time:                         0
% 3.12/0.99  parsing_time:                           0.01
% 3.12/0.99  unif_index_cands_time:                  0.
% 3.12/0.99  unif_index_add_time:                    0.
% 3.12/0.99  orderings_time:                         0.
% 3.12/0.99  out_proof_time:                         0.013
% 3.12/0.99  total_time:                             0.245
% 3.12/0.99  num_of_symbols:                         47
% 3.12/0.99  num_of_terms:                           7128
% 3.12/0.99  
% 3.12/0.99  ------ Preprocessing
% 3.12/0.99  
% 3.12/0.99  num_of_splits:                          0
% 3.12/0.99  num_of_split_atoms:                     0
% 3.12/0.99  num_of_reused_defs:                     0
% 3.12/0.99  num_eq_ax_congr_red:                    15
% 3.12/0.99  num_of_sem_filtered_clauses:            1
% 3.12/0.99  num_of_subtypes:                        0
% 3.12/0.99  monotx_restored_types:                  0
% 3.12/0.99  sat_num_of_epr_types:                   0
% 3.12/0.99  sat_num_of_non_cyclic_types:            0
% 3.12/0.99  sat_guarded_non_collapsed_types:        0
% 3.12/0.99  num_pure_diseq_elim:                    0
% 3.12/0.99  simp_replaced_by:                       0
% 3.12/0.99  res_preprocessed:                       126
% 3.12/0.99  prep_upred:                             0
% 3.12/0.99  prep_unflattend:                        1
% 3.12/0.99  smt_new_axioms:                         0
% 3.12/0.99  pred_elim_cands:                        6
% 3.12/0.99  pred_elim:                              1
% 3.12/0.99  pred_elim_cl:                           1
% 3.12/0.99  pred_elim_cycles:                       3
% 3.12/0.99  merged_defs:                            0
% 3.12/0.99  merged_defs_ncl:                        0
% 3.12/0.99  bin_hyper_res:                          0
% 3.12/0.99  prep_cycles:                            4
% 3.12/0.99  pred_elim_time:                         0.001
% 3.12/0.99  splitting_time:                         0.
% 3.12/0.99  sem_filter_time:                        0.
% 3.12/0.99  monotx_time:                            0.001
% 3.12/0.99  subtype_inf_time:                       0.
% 3.12/0.99  
% 3.12/0.99  ------ Problem properties
% 3.12/0.99  
% 3.12/0.99  clauses:                                24
% 3.12/0.99  conjectures:                            4
% 3.12/0.99  epr:                                    11
% 3.12/0.99  horn:                                   19
% 3.12/0.99  ground:                                 4
% 3.12/0.99  unary:                                  7
% 3.12/0.99  binary:                                 2
% 3.12/0.99  lits:                                   72
% 3.12/0.99  lits_eq:                                11
% 3.12/0.99  fd_pure:                                0
% 3.12/0.99  fd_pseudo:                              0
% 3.12/0.99  fd_cond:                                0
% 3.12/0.99  fd_pseudo_cond:                         2
% 3.12/0.99  ac_symbols:                             0
% 3.12/0.99  
% 3.12/0.99  ------ Propositional Solver
% 3.12/0.99  
% 3.12/0.99  prop_solver_calls:                      28
% 3.12/0.99  prop_fast_solver_calls:                 1081
% 3.12/0.99  smt_solver_calls:                       0
% 3.12/0.99  smt_fast_solver_calls:                  0
% 3.12/0.99  prop_num_of_clauses:                    2644
% 3.12/0.99  prop_preprocess_simplified:             8086
% 3.12/0.99  prop_fo_subsumed:                       37
% 3.12/0.99  prop_solver_time:                       0.
% 3.12/0.99  smt_solver_time:                        0.
% 3.12/0.99  smt_fast_solver_time:                   0.
% 3.12/0.99  prop_fast_solver_time:                  0.
% 3.12/0.99  prop_unsat_core_time:                   0.
% 3.12/0.99  
% 3.12/0.99  ------ QBF
% 3.12/0.99  
% 3.12/0.99  qbf_q_res:                              0
% 3.12/0.99  qbf_num_tautologies:                    0
% 3.12/0.99  qbf_prep_cycles:                        0
% 3.12/0.99  
% 3.12/0.99  ------ BMC1
% 3.12/0.99  
% 3.12/0.99  bmc1_current_bound:                     -1
% 3.12/0.99  bmc1_last_solved_bound:                 -1
% 3.12/0.99  bmc1_unsat_core_size:                   -1
% 3.12/0.99  bmc1_unsat_core_parents_size:           -1
% 3.12/0.99  bmc1_merge_next_fun:                    0
% 3.12/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.12/0.99  
% 3.12/0.99  ------ Instantiation
% 3.12/0.99  
% 3.12/0.99  inst_num_of_clauses:                    855
% 3.12/0.99  inst_num_in_passive:                    267
% 3.12/0.99  inst_num_in_active:                     389
% 3.12/0.99  inst_num_in_unprocessed:                199
% 3.12/0.99  inst_num_of_loops:                      460
% 3.12/0.99  inst_num_of_learning_restarts:          0
% 3.12/0.99  inst_num_moves_active_passive:          69
% 3.12/0.99  inst_lit_activity:                      0
% 3.12/0.99  inst_lit_activity_moves:                0
% 3.12/0.99  inst_num_tautologies:                   0
% 3.12/0.99  inst_num_prop_implied:                  0
% 3.12/0.99  inst_num_existing_simplified:           0
% 3.12/0.99  inst_num_eq_res_simplified:             0
% 3.12/0.99  inst_num_child_elim:                    0
% 3.12/0.99  inst_num_of_dismatching_blockings:      633
% 3.12/0.99  inst_num_of_non_proper_insts:           1121
% 3.12/0.99  inst_num_of_duplicates:                 0
% 3.12/0.99  inst_inst_num_from_inst_to_res:         0
% 3.12/0.99  inst_dismatching_checking_time:         0.
% 3.12/0.99  
% 3.12/0.99  ------ Resolution
% 3.12/0.99  
% 3.12/0.99  res_num_of_clauses:                     0
% 3.12/0.99  res_num_in_passive:                     0
% 3.12/0.99  res_num_in_active:                      0
% 3.12/0.99  res_num_of_loops:                       130
% 3.12/0.99  res_forward_subset_subsumed:            132
% 3.12/0.99  res_backward_subset_subsumed:           0
% 3.12/0.99  res_forward_subsumed:                   0
% 3.12/0.99  res_backward_subsumed:                  0
% 3.12/0.99  res_forward_subsumption_resolution:     0
% 3.12/0.99  res_backward_subsumption_resolution:    0
% 3.12/0.99  res_clause_to_clause_subsumption:       472
% 3.12/0.99  res_orphan_elimination:                 0
% 3.12/0.99  res_tautology_del:                      58
% 3.12/0.99  res_num_eq_res_simplified:              0
% 3.12/0.99  res_num_sel_changes:                    0
% 3.12/0.99  res_moves_from_active_to_pass:          0
% 3.12/0.99  
% 3.12/0.99  ------ Superposition
% 3.12/0.99  
% 3.12/0.99  sup_time_total:                         0.
% 3.12/0.99  sup_time_generating:                    0.
% 3.12/0.99  sup_time_sim_full:                      0.
% 3.12/0.99  sup_time_sim_immed:                     0.
% 3.12/0.99  
% 3.12/0.99  sup_num_of_clauses:                     57
% 3.12/0.99  sup_num_in_active:                      51
% 3.12/0.99  sup_num_in_passive:                     6
% 3.12/0.99  sup_num_of_loops:                       91
% 3.12/0.99  sup_fw_superposition:                   161
% 3.12/0.99  sup_bw_superposition:                   156
% 3.12/0.99  sup_immediate_simplified:               56
% 3.12/0.99  sup_given_eliminated:                   1
% 3.12/0.99  comparisons_done:                       0
% 3.12/0.99  comparisons_avoided:                    96
% 3.12/0.99  
% 3.12/0.99  ------ Simplifications
% 3.12/0.99  
% 3.12/0.99  
% 3.12/0.99  sim_fw_subset_subsumed:                 30
% 3.12/0.99  sim_bw_subset_subsumed:                 12
% 3.12/0.99  sim_fw_subsumed:                        5
% 3.12/0.99  sim_bw_subsumed:                        0
% 3.12/0.99  sim_fw_subsumption_res:                 2
% 3.12/0.99  sim_bw_subsumption_res:                 0
% 3.12/0.99  sim_tautology_del:                      7
% 3.12/0.99  sim_eq_tautology_del:                   29
% 3.12/0.99  sim_eq_res_simp:                        2
% 3.12/0.99  sim_fw_demodulated:                     6
% 3.12/0.99  sim_bw_demodulated:                     38
% 3.12/0.99  sim_light_normalised:                   18
% 3.12/0.99  sim_joinable_taut:                      0
% 3.12/0.99  sim_joinable_simp:                      0
% 3.12/0.99  sim_ac_normalised:                      0
% 3.12/0.99  sim_smt_subsumption:                    0
% 3.12/0.99  
%------------------------------------------------------------------------------
