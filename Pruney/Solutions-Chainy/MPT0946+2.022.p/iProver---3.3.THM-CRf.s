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
% DateTime   : Thu Dec  3 11:59:45 EST 2020

% Result     : Theorem 7.76s
% Output     : CNFRefutation 7.76s
% Verified   : 
% Statistics : Number of formulae       :  185 (1250 expanded)
%              Number of clauses        :  124 ( 533 expanded)
%              Number of leaves         :   21 ( 265 expanded)
%              Depth                    :   24
%              Number of atoms          :  611 (4773 expanded)
%              Number of equality atoms :  298 (1568 expanded)
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

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

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

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
     => ( sK4 != X0
        & r4_wellord1(k1_wellord2(X0),k1_wellord2(sK4))
        & v3_ordinal1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
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

fof(f44,plain,
    ( sK3 != sK4
    & r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4))
    & v3_ordinal1(sK4)
    & v3_ordinal1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f32,f43,f42])).

fof(f65,plain,(
    v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f66,plain,(
    v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f44])).

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

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_wellord1(k1_wellord2(X1),X0) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f68,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f44])).

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

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

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

fof(f37,plain,(
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
    inference(flattening,[],[f37])).

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
    inference(rectify,[],[f38])).

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f39,f40])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f75,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f8,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f67,plain,(
    r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) ),
    inference(cnf_transformation,[],[f44])).

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

fof(f52,plain,(
    ! [X0,X1] :
      ( r4_wellord1(X1,X0)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

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

fof(f63,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) = k1_wellord1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) = k1_wellord1(X1,X0)
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) = k1_wellord1(X1,X0)
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) = k1_wellord1(X1,X0)
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
       => ( r2_hidden(X0,X1)
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f36])).

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

fof(f64,plain,(
    ! [X0,X1] :
      ( k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_3,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_636,plain,
    ( X0 = X1
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_23,negated_conjecture,
    ( v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_618,plain,
    ( v3_ordinal1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_619,plain,
    ( v3_ordinal1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | k1_wellord1(k1_wellord2(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_623,plain,
    ( k1_wellord1(k1_wellord2(X0),X1) = X1
    | r2_hidden(X1,X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1957,plain,
    ( X0 = X1
    | k1_wellord1(k1_wellord2(X0),X1) = X1
    | r2_hidden(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_636,c_623])).

cnf(c_8707,plain,
    ( X0 = X1
    | k1_wellord1(k1_wellord2(X0),X1) = X1
    | k1_wellord1(k1_wellord2(X1),X0) = X0
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1957,c_623])).

cnf(c_10219,plain,
    ( k1_wellord1(k1_wellord2(X0),sK4) = sK4
    | k1_wellord1(k1_wellord2(sK4),X0) = X0
    | sK4 = X0
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_619,c_8707])).

cnf(c_10552,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3
    | k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | sK4 = sK3 ),
    inference(superposition,[status(thm)],[c_618,c_10219])).

cnf(c_20,negated_conjecture,
    ( sK3 != sK4 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_222,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_251,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_222])).

cnf(c_223,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_879,plain,
    ( sK4 != X0
    | sK3 != X0
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_223])).

cnf(c_880,plain,
    ( sK4 != sK3
    | sK3 = sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_879])).

cnf(c_10559,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | k1_wellord1(k1_wellord2(sK4),sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10552,c_20,c_251,c_880])).

cnf(c_10560,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3
    | k1_wellord1(k1_wellord2(sK3),sK4) = sK4 ),
    inference(renaming,[status(thm)],[c_10559])).

cnf(c_8,plain,
    ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
    | ~ r2_hidden(X1,k3_relat_1(X0))
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_631,plain,
    ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) != iProver_top
    | r2_hidden(X1,k3_relat_1(X0)) != iProver_top
    | v2_wellord1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_10563,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) != iProver_top
    | r2_hidden(sK3,k3_relat_1(k1_wellord2(sK4))) != iProver_top
    | v2_wellord1(k1_wellord2(sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10560,c_631])).

cnf(c_15,plain,
    ( ~ v1_relat_1(k1_wellord2(X0))
    | k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_16,plain,
    ( v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_172,plain,
    ( k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_16])).

cnf(c_10609,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) != iProver_top
    | r2_hidden(sK3,sK4) != iProver_top
    | v2_wellord1(k1_wellord2(sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10563,c_172])).

cnf(c_24,plain,
    ( v3_ordinal1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_25,plain,
    ( v3_ordinal1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_26,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_36,plain,
    ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_38,plain,
    ( v1_relat_1(k1_wellord2(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_233,plain,
    ( X0 != X1
    | k1_wellord2(X0) = k1_wellord2(X1) ),
    theory(equality)).

cnf(c_246,plain,
    ( k1_wellord2(sK3) = k1_wellord2(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_233])).

cnf(c_1256,plain,
    ( k1_wellord2(sK4) = k1_wellord2(sK4) ),
    inference(instantiation,[status(thm)],[c_222])).

cnf(c_7,plain,
    ( ~ r4_wellord1(X0,X1)
    | r4_wellord1(X1,X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_864,plain,
    ( r4_wellord1(X0,k1_wellord2(X1))
    | ~ r4_wellord1(k1_wellord2(X1),X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(k1_wellord2(X1)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1063,plain,
    ( ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
    | r4_wellord1(k1_wellord2(X1),k1_wellord2(X0))
    | ~ v1_relat_1(k1_wellord2(X1))
    | ~ v1_relat_1(k1_wellord2(X0)) ),
    inference(instantiation,[status(thm)],[c_864])).

cnf(c_1559,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3))
    | ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4))
    | ~ v1_relat_1(k1_wellord2(sK4))
    | ~ v1_relat_1(k1_wellord2(sK3)) ),
    inference(instantiation,[status(thm)],[c_1063])).

cnf(c_1560,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1559])).

cnf(c_1920,plain,
    ( v1_relat_1(k1_wellord2(sK4)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1921,plain,
    ( v1_relat_1(k1_wellord2(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1920])).

cnf(c_1925,plain,
    ( k3_relat_1(k1_wellord2(sK4)) = sK4 ),
    inference(instantiation,[status(thm)],[c_172])).

cnf(c_232,plain,
    ( ~ r4_wellord1(X0,X1)
    | r4_wellord1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1745,plain,
    ( r4_wellord1(X0,X1)
    | ~ r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3))
    | X0 != k1_wellord2(sK4)
    | X1 != k1_wellord2(sK3) ),
    inference(instantiation,[status(thm)],[c_232])).

cnf(c_2179,plain,
    ( r4_wellord1(k1_wellord2(sK4),X0)
    | ~ r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3))
    | X0 != k1_wellord2(sK3)
    | k1_wellord2(sK4) != k1_wellord2(sK4) ),
    inference(instantiation,[status(thm)],[c_1745])).

cnf(c_4017,plain,
    ( r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),X0)))
    | ~ r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3))
    | k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),X0)) != k1_wellord2(sK3)
    | k1_wellord2(sK4) != k1_wellord2(sK4) ),
    inference(instantiation,[status(thm)],[c_2179])).

cnf(c_4019,plain,
    ( k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),X0)) != k1_wellord2(sK3)
    | k1_wellord2(sK4) != k1_wellord2(sK4)
    | r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),X0))) = iProver_top
    | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4017])).

cnf(c_4021,plain,
    ( k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),sK3)) != k1_wellord2(sK3)
    | k1_wellord2(sK4) != k1_wellord2(sK4)
    | r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),sK3))) = iProver_top
    | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4019])).

cnf(c_4018,plain,
    ( ~ r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),X0)))
    | ~ r2_hidden(X0,k3_relat_1(k1_wellord2(sK4)))
    | ~ v2_wellord1(k1_wellord2(sK4))
    | ~ v1_relat_1(k1_wellord2(sK4)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_4023,plain,
    ( r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),X0))) != iProver_top
    | r2_hidden(X0,k3_relat_1(k1_wellord2(sK4))) != iProver_top
    | v2_wellord1(k1_wellord2(sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4018])).

cnf(c_4025,plain,
    ( r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),sK3))) != iProver_top
    | r2_hidden(sK3,k3_relat_1(k1_wellord2(sK4))) != iProver_top
    | v2_wellord1(k1_wellord2(sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4023])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_638,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_18,plain,
    ( v2_wellord1(k1_wellord2(X0))
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_622,plain,
    ( v2_wellord1(k1_wellord2(X0)) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_6,plain,
    ( ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0)
    | k3_relat_1(k2_wellord1(X0,k1_wellord1(X0,X1))) = k1_wellord1(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_633,plain,
    ( k3_relat_1(k2_wellord1(X0,k1_wellord1(X0,X1))) = k1_wellord1(X0,X1)
    | v2_wellord1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1787,plain,
    ( k3_relat_1(k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) = k1_wellord1(k1_wellord2(X0),X1)
    | v1_relat_1(k1_wellord2(X0)) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_622,c_633])).

cnf(c_3809,plain,
    ( k3_relat_1(k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) = k1_wellord1(k1_wellord2(X0),X1)
    | v3_ordinal1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1787,c_36])).

cnf(c_3817,plain,
    ( k3_relat_1(k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),X0))) = k1_wellord1(k1_wellord2(sK4),X0) ),
    inference(superposition,[status(thm)],[c_619,c_3809])).

cnf(c_5,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_634,plain,
    ( r2_hidden(X0,k3_relat_1(X1)) = iProver_top
    | r2_hidden(X0,k3_relat_1(k2_wellord1(X1,X2))) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3827,plain,
    ( r2_hidden(X0,k1_wellord1(k1_wellord2(sK4),X1)) != iProver_top
    | r2_hidden(X0,k3_relat_1(k1_wellord2(sK4))) = iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3817,c_634])).

cnf(c_3889,plain,
    ( r2_hidden(X0,k1_wellord1(k1_wellord2(sK4),X1)) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3827,c_172])).

cnf(c_4377,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,k1_wellord1(k1_wellord2(sK4),X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3889,c_1921])).

cnf(c_4378,plain,
    ( r2_hidden(X0,k1_wellord1(k1_wellord2(sK4),X1)) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_4377])).

cnf(c_4385,plain,
    ( r2_hidden(sK0(k1_wellord1(k1_wellord2(sK4),X0),X1),sK4) = iProver_top
    | r1_tarski(k1_wellord1(k1_wellord2(sK4),X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_638,c_4378])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_639,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4711,plain,
    ( r1_tarski(k1_wellord1(k1_wellord2(sK4),X0),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4385,c_639])).

cnf(c_19,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_621,plain,
    ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4854,plain,
    ( k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),X0)) = k1_wellord2(k1_wellord1(k1_wellord2(sK4),X0)) ),
    inference(superposition,[status(thm)],[c_4711,c_621])).

cnf(c_4855,plain,
    ( k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),sK3)) = k1_wellord2(k1_wellord1(k1_wellord2(sK4),sK3)) ),
    inference(instantiation,[status(thm)],[c_4854])).

cnf(c_1019,plain,
    ( X0 != X1
    | X0 = k1_wellord2(sK3)
    | k1_wellord2(sK3) != X1 ),
    inference(instantiation,[status(thm)],[c_223])).

cnf(c_1285,plain,
    ( X0 != k1_wellord2(X1)
    | X0 = k1_wellord2(sK3)
    | k1_wellord2(sK3) != k1_wellord2(X1) ),
    inference(instantiation,[status(thm)],[c_1019])).

cnf(c_2125,plain,
    ( k2_wellord1(k1_wellord2(X0),X1) != k1_wellord2(X1)
    | k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(sK3)
    | k1_wellord2(sK3) != k1_wellord2(X1) ),
    inference(instantiation,[status(thm)],[c_1285])).

cnf(c_5209,plain,
    ( k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),X0)) != k1_wellord2(k1_wellord1(k1_wellord2(sK4),X0))
    | k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),X0)) = k1_wellord2(sK3)
    | k1_wellord2(sK3) != k1_wellord2(k1_wellord1(k1_wellord2(sK4),X0)) ),
    inference(instantiation,[status(thm)],[c_2125])).

cnf(c_5210,plain,
    ( k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),sK3)) != k1_wellord2(k1_wellord1(k1_wellord2(sK4),sK3))
    | k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),sK3)) = k1_wellord2(sK3)
    | k1_wellord2(sK3) != k1_wellord2(k1_wellord1(k1_wellord2(sK4),sK3)) ),
    inference(instantiation,[status(thm)],[c_5209])).

cnf(c_5211,plain,
    ( v2_wellord1(k1_wellord2(sK4))
    | ~ v3_ordinal1(sK4) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_5212,plain,
    ( v2_wellord1(k1_wellord2(sK4)) = iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5211])).

cnf(c_225,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3680,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK3,sK4)
    | X1 != sK4
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_225])).

cnf(c_8942,plain,
    ( r2_hidden(X0,k3_relat_1(k1_wellord2(sK4)))
    | ~ r2_hidden(sK3,sK4)
    | X0 != sK3
    | k3_relat_1(k1_wellord2(sK4)) != sK4 ),
    inference(instantiation,[status(thm)],[c_3680])).

cnf(c_8943,plain,
    ( X0 != sK3
    | k3_relat_1(k1_wellord2(sK4)) != sK4
    | r2_hidden(X0,k3_relat_1(k1_wellord2(sK4))) = iProver_top
    | r2_hidden(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8942])).

cnf(c_8945,plain,
    ( k3_relat_1(k1_wellord2(sK4)) != sK4
    | sK3 != sK3
    | r2_hidden(sK3,k3_relat_1(k1_wellord2(sK4))) = iProver_top
    | r2_hidden(sK3,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8943])).

cnf(c_1284,plain,
    ( X0 != X1
    | k1_wellord2(sK3) != X1
    | k1_wellord2(sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_223])).

cnf(c_2117,plain,
    ( X0 != k1_wellord2(sK3)
    | k1_wellord2(sK3) = X0
    | k1_wellord2(sK3) != k1_wellord2(sK3) ),
    inference(instantiation,[status(thm)],[c_1284])).

cnf(c_2357,plain,
    ( k1_wellord2(X0) != k1_wellord2(sK3)
    | k1_wellord2(sK3) = k1_wellord2(X0)
    | k1_wellord2(sK3) != k1_wellord2(sK3) ),
    inference(instantiation,[status(thm)],[c_2117])).

cnf(c_15886,plain,
    ( k1_wellord2(k1_wellord1(k1_wellord2(sK4),X0)) != k1_wellord2(sK3)
    | k1_wellord2(sK3) = k1_wellord2(k1_wellord1(k1_wellord2(sK4),X0))
    | k1_wellord2(sK3) != k1_wellord2(sK3) ),
    inference(instantiation,[status(thm)],[c_2357])).

cnf(c_15889,plain,
    ( k1_wellord2(k1_wellord1(k1_wellord2(sK4),sK3)) != k1_wellord2(sK3)
    | k1_wellord2(sK3) = k1_wellord2(k1_wellord1(k1_wellord2(sK4),sK3))
    | k1_wellord2(sK3) != k1_wellord2(sK3) ),
    inference(instantiation,[status(thm)],[c_15886])).

cnf(c_21413,plain,
    ( ~ r2_hidden(sK3,sK4)
    | ~ v3_ordinal1(sK4)
    | ~ v3_ordinal1(sK3)
    | k1_wellord1(k1_wellord2(sK4),sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_21414,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3
    | r2_hidden(sK3,sK4) != iProver_top
    | v3_ordinal1(sK4) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21413])).

cnf(c_1022,plain,
    ( X0 != sK3
    | k1_wellord2(X0) = k1_wellord2(sK3) ),
    inference(instantiation,[status(thm)],[c_233])).

cnf(c_28573,plain,
    ( k1_wellord1(k1_wellord2(sK4),X0) != sK3
    | k1_wellord2(k1_wellord1(k1_wellord2(sK4),X0)) = k1_wellord2(sK3) ),
    inference(instantiation,[status(thm)],[c_1022])).

cnf(c_28574,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK3) != sK3
    | k1_wellord2(k1_wellord1(k1_wellord2(sK4),sK3)) = k1_wellord2(sK3) ),
    inference(instantiation,[status(thm)],[c_28573])).

cnf(c_32675,plain,
    ( r2_hidden(sK3,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10609,c_24,c_25,c_26,c_38,c_246,c_251,c_1256,c_1560,c_1921,c_1925,c_4021,c_4025,c_4855,c_5210,c_5212,c_8945,c_15889,c_21414,c_28574])).

cnf(c_32683,plain,
    ( sK4 = sK3
    | r2_hidden(sK4,sK3) = iProver_top
    | v3_ordinal1(sK4) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_636,c_32675])).

cnf(c_3639,plain,
    ( r2_hidden(sK4,sK3)
    | r2_hidden(sK3,sK4)
    | ~ v3_ordinal1(sK4)
    | ~ v3_ordinal1(sK3) ),
    inference(resolution,[status(thm)],[c_3,c_20])).

cnf(c_4447,plain,
    ( r2_hidden(sK4,sK3)
    | r2_hidden(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3639,c_23,c_22])).

cnf(c_4449,plain,
    ( r2_hidden(sK4,sK3) = iProver_top
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4447])).

cnf(c_32703,plain,
    ( r2_hidden(sK4,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_32683,c_24,c_25,c_26,c_38,c_246,c_251,c_1256,c_1560,c_1921,c_1925,c_4021,c_4025,c_4449,c_4855,c_5210,c_5212,c_8945,c_15889,c_21414,c_28574])).

cnf(c_32709,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | v3_ordinal1(sK4) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_32703,c_623])).

cnf(c_1927,plain,
    ( ~ r2_hidden(sK4,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK4)
    | k1_wellord1(k1_wellord2(X0),sK4) = sK4 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1929,plain,
    ( k1_wellord1(k1_wellord2(X0),sK4) = sK4
    | r2_hidden(sK4,X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1927])).

cnf(c_1931,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | r2_hidden(sK4,sK3) != iProver_top
    | v3_ordinal1(sK4) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1929])).

cnf(c_32910,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_32709,c_24,c_25,c_26,c_38,c_246,c_251,c_1256,c_1560,c_1921,c_1925,c_1931,c_4021,c_4025,c_4449,c_4855,c_5210,c_5212,c_8945,c_15889,c_21414,c_28574])).

cnf(c_3818,plain,
    ( k3_relat_1(k2_wellord1(k1_wellord2(sK3),k1_wellord1(k1_wellord2(sK3),X0))) = k1_wellord1(k1_wellord2(sK3),X0) ),
    inference(superposition,[status(thm)],[c_618,c_3809])).

cnf(c_4295,plain,
    ( r2_hidden(X0,k1_wellord1(k1_wellord2(sK3),X1)) != iProver_top
    | r2_hidden(X0,k3_relat_1(k1_wellord2(sK3))) = iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3818,c_634])).

cnf(c_4357,plain,
    ( r2_hidden(X0,k1_wellord1(k1_wellord2(sK3),X1)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4295,c_172])).

cnf(c_4987,plain,
    ( r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X0,k1_wellord1(k1_wellord2(sK3),X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4357,c_38])).

cnf(c_4988,plain,
    ( r2_hidden(X0,k1_wellord1(k1_wellord2(sK3),X1)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_4987])).

cnf(c_4995,plain,
    ( r2_hidden(sK0(k1_wellord1(k1_wellord2(sK3),X0),X1),sK3) = iProver_top
    | r1_tarski(k1_wellord1(k1_wellord2(sK3),X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_638,c_4988])).

cnf(c_5224,plain,
    ( r1_tarski(k1_wellord1(k1_wellord2(sK3),X0),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4995,c_639])).

cnf(c_5250,plain,
    ( k2_wellord1(k1_wellord2(sK3),k1_wellord1(k1_wellord2(sK3),X0)) = k1_wellord2(k1_wellord1(k1_wellord2(sK3),X0)) ),
    inference(superposition,[status(thm)],[c_5224,c_621])).

cnf(c_5409,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(k1_wellord1(k1_wellord2(sK3),X0))) != iProver_top
    | r2_hidden(X0,k3_relat_1(k1_wellord2(sK3))) != iProver_top
    | v2_wellord1(k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5250,c_631])).

cnf(c_5440,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(k1_wellord1(k1_wellord2(sK3),X0))) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | v2_wellord1(k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5409,c_172])).

cnf(c_30,plain,
    ( v2_wellord1(k1_wellord2(X0)) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_32,plain,
    ( v2_wellord1(k1_wellord2(sK3)) = iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_12301,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(k1_wellord1(k1_wellord2(sK3),X0))) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5440,c_24,c_32,c_38])).

cnf(c_32916,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) != iProver_top
    | r2_hidden(sK4,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_32910,c_12301])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_32916,c_32675,c_4449,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n025.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 11:24:50 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 7.76/1.47  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.76/1.47  
% 7.76/1.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.76/1.47  
% 7.76/1.47  ------  iProver source info
% 7.76/1.47  
% 7.76/1.47  git: date: 2020-06-30 10:37:57 +0100
% 7.76/1.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.76/1.47  git: non_committed_changes: false
% 7.76/1.47  git: last_make_outside_of_git: false
% 7.76/1.47  
% 7.76/1.47  ------ 
% 7.76/1.47  
% 7.76/1.47  ------ Input Options
% 7.76/1.47  
% 7.76/1.47  --out_options                           all
% 7.76/1.47  --tptp_safe_out                         true
% 7.76/1.47  --problem_path                          ""
% 7.76/1.47  --include_path                          ""
% 7.76/1.47  --clausifier                            res/vclausify_rel
% 7.76/1.47  --clausifier_options                    --mode clausify
% 7.76/1.47  --stdin                                 false
% 7.76/1.47  --stats_out                             sel
% 7.76/1.47  
% 7.76/1.47  ------ General Options
% 7.76/1.47  
% 7.76/1.47  --fof                                   false
% 7.76/1.47  --time_out_real                         604.99
% 7.76/1.47  --time_out_virtual                      -1.
% 7.76/1.47  --symbol_type_check                     false
% 7.76/1.47  --clausify_out                          false
% 7.76/1.47  --sig_cnt_out                           false
% 7.76/1.47  --trig_cnt_out                          false
% 7.76/1.47  --trig_cnt_out_tolerance                1.
% 7.76/1.47  --trig_cnt_out_sk_spl                   false
% 7.76/1.47  --abstr_cl_out                          false
% 7.76/1.47  
% 7.76/1.47  ------ Global Options
% 7.76/1.47  
% 7.76/1.47  --schedule                              none
% 7.76/1.47  --add_important_lit                     false
% 7.76/1.47  --prop_solver_per_cl                    1000
% 7.76/1.47  --min_unsat_core                        false
% 7.76/1.47  --soft_assumptions                      false
% 7.76/1.47  --soft_lemma_size                       3
% 7.76/1.47  --prop_impl_unit_size                   0
% 7.76/1.47  --prop_impl_unit                        []
% 7.76/1.47  --share_sel_clauses                     true
% 7.76/1.47  --reset_solvers                         false
% 7.76/1.47  --bc_imp_inh                            [conj_cone]
% 7.76/1.47  --conj_cone_tolerance                   3.
% 7.76/1.47  --extra_neg_conj                        none
% 7.76/1.47  --large_theory_mode                     true
% 7.76/1.47  --prolific_symb_bound                   200
% 7.76/1.47  --lt_threshold                          2000
% 7.76/1.47  --clause_weak_htbl                      true
% 7.76/1.47  --gc_record_bc_elim                     false
% 7.76/1.47  
% 7.76/1.47  ------ Preprocessing Options
% 7.76/1.47  
% 7.76/1.47  --preprocessing_flag                    true
% 7.76/1.47  --time_out_prep_mult                    0.1
% 7.76/1.47  --splitting_mode                        input
% 7.76/1.47  --splitting_grd                         true
% 7.76/1.47  --splitting_cvd                         false
% 7.76/1.47  --splitting_cvd_svl                     false
% 7.76/1.47  --splitting_nvd                         32
% 7.76/1.47  --sub_typing                            true
% 7.76/1.47  --prep_gs_sim                           false
% 7.76/1.47  --prep_unflatten                        true
% 7.76/1.47  --prep_res_sim                          true
% 7.76/1.47  --prep_upred                            true
% 7.76/1.47  --prep_sem_filter                       exhaustive
% 7.76/1.47  --prep_sem_filter_out                   false
% 7.76/1.47  --pred_elim                             false
% 7.76/1.47  --res_sim_input                         true
% 7.76/1.47  --eq_ax_congr_red                       true
% 7.76/1.47  --pure_diseq_elim                       true
% 7.76/1.47  --brand_transform                       false
% 7.76/1.47  --non_eq_to_eq                          false
% 7.76/1.47  --prep_def_merge                        true
% 7.76/1.47  --prep_def_merge_prop_impl              false
% 7.76/1.47  --prep_def_merge_mbd                    true
% 7.76/1.47  --prep_def_merge_tr_red                 false
% 7.76/1.47  --prep_def_merge_tr_cl                  false
% 7.76/1.47  --smt_preprocessing                     true
% 7.76/1.47  --smt_ac_axioms                         fast
% 7.76/1.47  --preprocessed_out                      false
% 7.76/1.47  --preprocessed_stats                    false
% 7.76/1.47  
% 7.76/1.47  ------ Abstraction refinement Options
% 7.76/1.47  
% 7.76/1.47  --abstr_ref                             []
% 7.76/1.47  --abstr_ref_prep                        false
% 7.76/1.47  --abstr_ref_until_sat                   false
% 7.76/1.47  --abstr_ref_sig_restrict                funpre
% 7.76/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 7.76/1.47  --abstr_ref_under                       []
% 7.76/1.47  
% 7.76/1.47  ------ SAT Options
% 7.76/1.47  
% 7.76/1.47  --sat_mode                              false
% 7.76/1.47  --sat_fm_restart_options                ""
% 7.76/1.47  --sat_gr_def                            false
% 7.76/1.47  --sat_epr_types                         true
% 7.76/1.47  --sat_non_cyclic_types                  false
% 7.76/1.47  --sat_finite_models                     false
% 7.76/1.47  --sat_fm_lemmas                         false
% 7.76/1.47  --sat_fm_prep                           false
% 7.76/1.47  --sat_fm_uc_incr                        true
% 7.76/1.47  --sat_out_model                         small
% 7.76/1.47  --sat_out_clauses                       false
% 7.76/1.47  
% 7.76/1.47  ------ QBF Options
% 7.76/1.47  
% 7.76/1.47  --qbf_mode                              false
% 7.76/1.47  --qbf_elim_univ                         false
% 7.76/1.47  --qbf_dom_inst                          none
% 7.76/1.47  --qbf_dom_pre_inst                      false
% 7.76/1.47  --qbf_sk_in                             false
% 7.76/1.47  --qbf_pred_elim                         true
% 7.76/1.47  --qbf_split                             512
% 7.76/1.47  
% 7.76/1.47  ------ BMC1 Options
% 7.76/1.47  
% 7.76/1.47  --bmc1_incremental                      false
% 7.76/1.47  --bmc1_axioms                           reachable_all
% 7.76/1.47  --bmc1_min_bound                        0
% 7.76/1.47  --bmc1_max_bound                        -1
% 7.76/1.47  --bmc1_max_bound_default                -1
% 7.76/1.47  --bmc1_symbol_reachability              true
% 7.76/1.47  --bmc1_property_lemmas                  false
% 7.76/1.47  --bmc1_k_induction                      false
% 7.76/1.47  --bmc1_non_equiv_states                 false
% 7.76/1.47  --bmc1_deadlock                         false
% 7.76/1.47  --bmc1_ucm                              false
% 7.76/1.47  --bmc1_add_unsat_core                   none
% 7.76/1.47  --bmc1_unsat_core_children              false
% 7.76/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 7.76/1.47  --bmc1_out_stat                         full
% 7.76/1.47  --bmc1_ground_init                      false
% 7.76/1.47  --bmc1_pre_inst_next_state              false
% 7.76/1.47  --bmc1_pre_inst_state                   false
% 7.76/1.47  --bmc1_pre_inst_reach_state             false
% 7.76/1.47  --bmc1_out_unsat_core                   false
% 7.76/1.47  --bmc1_aig_witness_out                  false
% 7.76/1.47  --bmc1_verbose                          false
% 7.76/1.47  --bmc1_dump_clauses_tptp                false
% 7.76/1.47  --bmc1_dump_unsat_core_tptp             false
% 7.76/1.47  --bmc1_dump_file                        -
% 7.76/1.47  --bmc1_ucm_expand_uc_limit              128
% 7.76/1.47  --bmc1_ucm_n_expand_iterations          6
% 7.76/1.47  --bmc1_ucm_extend_mode                  1
% 7.76/1.47  --bmc1_ucm_init_mode                    2
% 7.76/1.47  --bmc1_ucm_cone_mode                    none
% 7.76/1.47  --bmc1_ucm_reduced_relation_type        0
% 7.76/1.47  --bmc1_ucm_relax_model                  4
% 7.76/1.47  --bmc1_ucm_full_tr_after_sat            true
% 7.76/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 7.76/1.47  --bmc1_ucm_layered_model                none
% 7.76/1.47  --bmc1_ucm_max_lemma_size               10
% 7.76/1.47  
% 7.76/1.47  ------ AIG Options
% 7.76/1.47  
% 7.76/1.47  --aig_mode                              false
% 7.76/1.47  
% 7.76/1.47  ------ Instantiation Options
% 7.76/1.47  
% 7.76/1.47  --instantiation_flag                    true
% 7.76/1.47  --inst_sos_flag                         false
% 7.76/1.47  --inst_sos_phase                        true
% 7.76/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.76/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.76/1.47  --inst_lit_sel_side                     num_symb
% 7.76/1.47  --inst_solver_per_active                1400
% 7.76/1.47  --inst_solver_calls_frac                1.
% 7.76/1.47  --inst_passive_queue_type               priority_queues
% 7.76/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.76/1.47  --inst_passive_queues_freq              [25;2]
% 7.76/1.47  --inst_dismatching                      true
% 7.76/1.47  --inst_eager_unprocessed_to_passive     true
% 7.76/1.47  --inst_prop_sim_given                   true
% 7.76/1.47  --inst_prop_sim_new                     false
% 7.76/1.47  --inst_subs_new                         false
% 7.76/1.47  --inst_eq_res_simp                      false
% 7.76/1.47  --inst_subs_given                       false
% 7.76/1.47  --inst_orphan_elimination               true
% 7.76/1.47  --inst_learning_loop_flag               true
% 7.76/1.47  --inst_learning_start                   3000
% 7.76/1.47  --inst_learning_factor                  2
% 7.76/1.47  --inst_start_prop_sim_after_learn       3
% 7.76/1.47  --inst_sel_renew                        solver
% 7.76/1.47  --inst_lit_activity_flag                true
% 7.76/1.47  --inst_restr_to_given                   false
% 7.76/1.47  --inst_activity_threshold               500
% 7.76/1.47  --inst_out_proof                        true
% 7.76/1.47  
% 7.76/1.47  ------ Resolution Options
% 7.76/1.47  
% 7.76/1.47  --resolution_flag                       true
% 7.76/1.47  --res_lit_sel                           adaptive
% 7.76/1.47  --res_lit_sel_side                      none
% 7.76/1.47  --res_ordering                          kbo
% 7.76/1.47  --res_to_prop_solver                    active
% 7.76/1.47  --res_prop_simpl_new                    false
% 7.76/1.47  --res_prop_simpl_given                  true
% 7.76/1.47  --res_passive_queue_type                priority_queues
% 7.76/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.76/1.47  --res_passive_queues_freq               [15;5]
% 7.76/1.47  --res_forward_subs                      full
% 7.76/1.47  --res_backward_subs                     full
% 7.76/1.47  --res_forward_subs_resolution           true
% 7.76/1.47  --res_backward_subs_resolution          true
% 7.76/1.47  --res_orphan_elimination                true
% 7.76/1.47  --res_time_limit                        2.
% 7.76/1.47  --res_out_proof                         true
% 7.76/1.47  
% 7.76/1.47  ------ Superposition Options
% 7.76/1.47  
% 7.76/1.47  --superposition_flag                    true
% 7.76/1.47  --sup_passive_queue_type                priority_queues
% 7.76/1.47  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.76/1.47  --sup_passive_queues_freq               [1;4]
% 7.76/1.47  --demod_completeness_check              fast
% 7.76/1.47  --demod_use_ground                      true
% 7.76/1.47  --sup_to_prop_solver                    passive
% 7.76/1.47  --sup_prop_simpl_new                    true
% 7.76/1.47  --sup_prop_simpl_given                  true
% 7.76/1.47  --sup_fun_splitting                     false
% 7.76/1.47  --sup_smt_interval                      50000
% 7.76/1.47  
% 7.76/1.47  ------ Superposition Simplification Setup
% 7.76/1.47  
% 7.76/1.47  --sup_indices_passive                   []
% 7.76/1.47  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.76/1.47  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.76/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.76/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 7.76/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.76/1.47  --sup_full_bw                           [BwDemod]
% 7.76/1.47  --sup_immed_triv                        [TrivRules]
% 7.76/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.76/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.76/1.47  --sup_immed_bw_main                     []
% 7.76/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.76/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 7.76/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.76/1.47  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.76/1.47  
% 7.76/1.47  ------ Combination Options
% 7.76/1.47  
% 7.76/1.47  --comb_res_mult                         3
% 7.76/1.47  --comb_sup_mult                         2
% 7.76/1.47  --comb_inst_mult                        10
% 7.76/1.47  
% 7.76/1.47  ------ Debug Options
% 7.76/1.47  
% 7.76/1.47  --dbg_backtrace                         false
% 7.76/1.47  --dbg_dump_prop_clauses                 false
% 7.76/1.47  --dbg_dump_prop_clauses_file            -
% 7.76/1.47  --dbg_out_stat                          false
% 7.76/1.47  ------ Parsing...
% 7.76/1.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.76/1.47  
% 7.76/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.76/1.47  
% 7.76/1.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.76/1.47  
% 7.76/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.76/1.47  ------ Proving...
% 7.76/1.47  ------ Problem Properties 
% 7.76/1.47  
% 7.76/1.47  
% 7.76/1.47  clauses                                 24
% 7.76/1.47  conjectures                             4
% 7.76/1.47  EPR                                     6
% 7.76/1.47  Horn                                    19
% 7.76/1.47  unary                                   6
% 7.76/1.47  binary                                  4
% 7.76/1.47  lits                                    67
% 7.76/1.47  lits eq                                 10
% 7.76/1.47  fd_pure                                 0
% 7.76/1.47  fd_pseudo                               0
% 7.76/1.47  fd_cond                                 0
% 7.76/1.47  fd_pseudo_cond                          1
% 7.76/1.47  AC symbols                              0
% 7.76/1.47  
% 7.76/1.47  ------ Input Options Time Limit: Unbounded
% 7.76/1.47  
% 7.76/1.47  
% 7.76/1.47  ------ 
% 7.76/1.47  Current options:
% 7.76/1.47  ------ 
% 7.76/1.47  
% 7.76/1.47  ------ Input Options
% 7.76/1.47  
% 7.76/1.47  --out_options                           all
% 7.76/1.47  --tptp_safe_out                         true
% 7.76/1.47  --problem_path                          ""
% 7.76/1.47  --include_path                          ""
% 7.76/1.47  --clausifier                            res/vclausify_rel
% 7.76/1.47  --clausifier_options                    --mode clausify
% 7.76/1.47  --stdin                                 false
% 7.76/1.47  --stats_out                             sel
% 7.76/1.47  
% 7.76/1.47  ------ General Options
% 7.76/1.47  
% 7.76/1.47  --fof                                   false
% 7.76/1.47  --time_out_real                         604.99
% 7.76/1.47  --time_out_virtual                      -1.
% 7.76/1.47  --symbol_type_check                     false
% 7.76/1.47  --clausify_out                          false
% 7.76/1.47  --sig_cnt_out                           false
% 7.76/1.47  --trig_cnt_out                          false
% 7.76/1.47  --trig_cnt_out_tolerance                1.
% 7.76/1.47  --trig_cnt_out_sk_spl                   false
% 7.76/1.47  --abstr_cl_out                          false
% 7.76/1.47  
% 7.76/1.47  ------ Global Options
% 7.76/1.47  
% 7.76/1.47  --schedule                              none
% 7.76/1.47  --add_important_lit                     false
% 7.76/1.47  --prop_solver_per_cl                    1000
% 7.76/1.47  --min_unsat_core                        false
% 7.76/1.47  --soft_assumptions                      false
% 7.76/1.47  --soft_lemma_size                       3
% 7.76/1.47  --prop_impl_unit_size                   0
% 7.76/1.47  --prop_impl_unit                        []
% 7.76/1.47  --share_sel_clauses                     true
% 7.76/1.47  --reset_solvers                         false
% 7.76/1.47  --bc_imp_inh                            [conj_cone]
% 7.76/1.47  --conj_cone_tolerance                   3.
% 7.76/1.47  --extra_neg_conj                        none
% 7.76/1.47  --large_theory_mode                     true
% 7.76/1.47  --prolific_symb_bound                   200
% 7.76/1.47  --lt_threshold                          2000
% 7.76/1.47  --clause_weak_htbl                      true
% 7.76/1.47  --gc_record_bc_elim                     false
% 7.76/1.47  
% 7.76/1.47  ------ Preprocessing Options
% 7.76/1.47  
% 7.76/1.47  --preprocessing_flag                    true
% 7.76/1.47  --time_out_prep_mult                    0.1
% 7.76/1.47  --splitting_mode                        input
% 7.76/1.47  --splitting_grd                         true
% 7.76/1.47  --splitting_cvd                         false
% 7.76/1.47  --splitting_cvd_svl                     false
% 7.76/1.47  --splitting_nvd                         32
% 7.76/1.47  --sub_typing                            true
% 7.76/1.47  --prep_gs_sim                           false
% 7.76/1.47  --prep_unflatten                        true
% 7.76/1.47  --prep_res_sim                          true
% 7.76/1.47  --prep_upred                            true
% 7.76/1.47  --prep_sem_filter                       exhaustive
% 7.76/1.47  --prep_sem_filter_out                   false
% 7.76/1.47  --pred_elim                             false
% 7.76/1.47  --res_sim_input                         true
% 7.76/1.47  --eq_ax_congr_red                       true
% 7.76/1.47  --pure_diseq_elim                       true
% 7.76/1.47  --brand_transform                       false
% 7.76/1.47  --non_eq_to_eq                          false
% 7.76/1.47  --prep_def_merge                        true
% 7.76/1.47  --prep_def_merge_prop_impl              false
% 7.76/1.47  --prep_def_merge_mbd                    true
% 7.76/1.47  --prep_def_merge_tr_red                 false
% 7.76/1.47  --prep_def_merge_tr_cl                  false
% 7.76/1.47  --smt_preprocessing                     true
% 7.76/1.47  --smt_ac_axioms                         fast
% 7.76/1.47  --preprocessed_out                      false
% 7.76/1.47  --preprocessed_stats                    false
% 7.76/1.47  
% 7.76/1.47  ------ Abstraction refinement Options
% 7.76/1.47  
% 7.76/1.47  --abstr_ref                             []
% 7.76/1.47  --abstr_ref_prep                        false
% 7.76/1.47  --abstr_ref_until_sat                   false
% 7.76/1.47  --abstr_ref_sig_restrict                funpre
% 7.76/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 7.76/1.47  --abstr_ref_under                       []
% 7.76/1.47  
% 7.76/1.47  ------ SAT Options
% 7.76/1.47  
% 7.76/1.47  --sat_mode                              false
% 7.76/1.47  --sat_fm_restart_options                ""
% 7.76/1.47  --sat_gr_def                            false
% 7.76/1.47  --sat_epr_types                         true
% 7.76/1.47  --sat_non_cyclic_types                  false
% 7.76/1.47  --sat_finite_models                     false
% 7.76/1.47  --sat_fm_lemmas                         false
% 7.76/1.47  --sat_fm_prep                           false
% 7.76/1.47  --sat_fm_uc_incr                        true
% 7.76/1.47  --sat_out_model                         small
% 7.76/1.47  --sat_out_clauses                       false
% 7.76/1.47  
% 7.76/1.47  ------ QBF Options
% 7.76/1.47  
% 7.76/1.47  --qbf_mode                              false
% 7.76/1.47  --qbf_elim_univ                         false
% 7.76/1.47  --qbf_dom_inst                          none
% 7.76/1.47  --qbf_dom_pre_inst                      false
% 7.76/1.47  --qbf_sk_in                             false
% 7.76/1.47  --qbf_pred_elim                         true
% 7.76/1.47  --qbf_split                             512
% 7.76/1.47  
% 7.76/1.47  ------ BMC1 Options
% 7.76/1.47  
% 7.76/1.47  --bmc1_incremental                      false
% 7.76/1.47  --bmc1_axioms                           reachable_all
% 7.76/1.47  --bmc1_min_bound                        0
% 7.76/1.47  --bmc1_max_bound                        -1
% 7.76/1.47  --bmc1_max_bound_default                -1
% 7.76/1.47  --bmc1_symbol_reachability              true
% 7.76/1.47  --bmc1_property_lemmas                  false
% 7.76/1.47  --bmc1_k_induction                      false
% 7.76/1.47  --bmc1_non_equiv_states                 false
% 7.76/1.47  --bmc1_deadlock                         false
% 7.76/1.47  --bmc1_ucm                              false
% 7.76/1.47  --bmc1_add_unsat_core                   none
% 7.76/1.47  --bmc1_unsat_core_children              false
% 7.76/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 7.76/1.47  --bmc1_out_stat                         full
% 7.76/1.47  --bmc1_ground_init                      false
% 7.76/1.47  --bmc1_pre_inst_next_state              false
% 7.76/1.47  --bmc1_pre_inst_state                   false
% 7.76/1.47  --bmc1_pre_inst_reach_state             false
% 7.76/1.47  --bmc1_out_unsat_core                   false
% 7.76/1.47  --bmc1_aig_witness_out                  false
% 7.76/1.47  --bmc1_verbose                          false
% 7.76/1.47  --bmc1_dump_clauses_tptp                false
% 7.76/1.47  --bmc1_dump_unsat_core_tptp             false
% 7.76/1.47  --bmc1_dump_file                        -
% 7.76/1.47  --bmc1_ucm_expand_uc_limit              128
% 7.76/1.47  --bmc1_ucm_n_expand_iterations          6
% 7.76/1.47  --bmc1_ucm_extend_mode                  1
% 7.76/1.47  --bmc1_ucm_init_mode                    2
% 7.76/1.47  --bmc1_ucm_cone_mode                    none
% 7.76/1.47  --bmc1_ucm_reduced_relation_type        0
% 7.76/1.47  --bmc1_ucm_relax_model                  4
% 7.76/1.47  --bmc1_ucm_full_tr_after_sat            true
% 7.76/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 7.76/1.47  --bmc1_ucm_layered_model                none
% 7.76/1.47  --bmc1_ucm_max_lemma_size               10
% 7.76/1.47  
% 7.76/1.47  ------ AIG Options
% 7.76/1.47  
% 7.76/1.47  --aig_mode                              false
% 7.76/1.47  
% 7.76/1.47  ------ Instantiation Options
% 7.76/1.47  
% 7.76/1.47  --instantiation_flag                    true
% 7.76/1.47  --inst_sos_flag                         false
% 7.76/1.47  --inst_sos_phase                        true
% 7.76/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.76/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.76/1.47  --inst_lit_sel_side                     num_symb
% 7.76/1.47  --inst_solver_per_active                1400
% 7.76/1.47  --inst_solver_calls_frac                1.
% 7.76/1.47  --inst_passive_queue_type               priority_queues
% 7.76/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.76/1.47  --inst_passive_queues_freq              [25;2]
% 7.76/1.47  --inst_dismatching                      true
% 7.76/1.47  --inst_eager_unprocessed_to_passive     true
% 7.76/1.47  --inst_prop_sim_given                   true
% 7.76/1.47  --inst_prop_sim_new                     false
% 7.76/1.47  --inst_subs_new                         false
% 7.76/1.47  --inst_eq_res_simp                      false
% 7.76/1.47  --inst_subs_given                       false
% 7.76/1.47  --inst_orphan_elimination               true
% 7.76/1.47  --inst_learning_loop_flag               true
% 7.76/1.47  --inst_learning_start                   3000
% 7.76/1.47  --inst_learning_factor                  2
% 7.76/1.47  --inst_start_prop_sim_after_learn       3
% 7.76/1.47  --inst_sel_renew                        solver
% 7.76/1.47  --inst_lit_activity_flag                true
% 7.76/1.47  --inst_restr_to_given                   false
% 7.76/1.47  --inst_activity_threshold               500
% 7.76/1.47  --inst_out_proof                        true
% 7.76/1.47  
% 7.76/1.47  ------ Resolution Options
% 7.76/1.47  
% 7.76/1.47  --resolution_flag                       true
% 7.76/1.47  --res_lit_sel                           adaptive
% 7.76/1.47  --res_lit_sel_side                      none
% 7.76/1.47  --res_ordering                          kbo
% 7.76/1.47  --res_to_prop_solver                    active
% 7.76/1.47  --res_prop_simpl_new                    false
% 7.76/1.47  --res_prop_simpl_given                  true
% 7.76/1.47  --res_passive_queue_type                priority_queues
% 7.76/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.76/1.47  --res_passive_queues_freq               [15;5]
% 7.76/1.47  --res_forward_subs                      full
% 7.76/1.47  --res_backward_subs                     full
% 7.76/1.47  --res_forward_subs_resolution           true
% 7.76/1.47  --res_backward_subs_resolution          true
% 7.76/1.47  --res_orphan_elimination                true
% 7.76/1.47  --res_time_limit                        2.
% 7.76/1.47  --res_out_proof                         true
% 7.76/1.47  
% 7.76/1.47  ------ Superposition Options
% 7.76/1.47  
% 7.76/1.47  --superposition_flag                    true
% 7.76/1.47  --sup_passive_queue_type                priority_queues
% 7.76/1.47  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.76/1.47  --sup_passive_queues_freq               [1;4]
% 7.76/1.47  --demod_completeness_check              fast
% 7.76/1.47  --demod_use_ground                      true
% 7.76/1.47  --sup_to_prop_solver                    passive
% 7.76/1.47  --sup_prop_simpl_new                    true
% 7.76/1.47  --sup_prop_simpl_given                  true
% 7.76/1.47  --sup_fun_splitting                     false
% 7.76/1.47  --sup_smt_interval                      50000
% 7.76/1.47  
% 7.76/1.47  ------ Superposition Simplification Setup
% 7.76/1.47  
% 7.76/1.47  --sup_indices_passive                   []
% 7.76/1.47  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.76/1.47  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.76/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.76/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 7.76/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.76/1.47  --sup_full_bw                           [BwDemod]
% 7.76/1.47  --sup_immed_triv                        [TrivRules]
% 7.76/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.76/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.76/1.47  --sup_immed_bw_main                     []
% 7.76/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.76/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 7.76/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.76/1.47  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.76/1.47  
% 7.76/1.47  ------ Combination Options
% 7.76/1.47  
% 7.76/1.47  --comb_res_mult                         3
% 7.76/1.47  --comb_sup_mult                         2
% 7.76/1.47  --comb_inst_mult                        10
% 7.76/1.47  
% 7.76/1.47  ------ Debug Options
% 7.76/1.47  
% 7.76/1.47  --dbg_backtrace                         false
% 7.76/1.47  --dbg_dump_prop_clauses                 false
% 7.76/1.47  --dbg_dump_prop_clauses_file            -
% 7.76/1.47  --dbg_out_stat                          false
% 7.76/1.47  
% 7.76/1.47  
% 7.76/1.47  
% 7.76/1.47  
% 7.76/1.47  ------ Proving...
% 7.76/1.47  
% 7.76/1.47  
% 7.76/1.47  % SZS status Theorem for theBenchmark.p
% 7.76/1.47  
% 7.76/1.47  % SZS output start CNFRefutation for theBenchmark.p
% 7.76/1.47  
% 7.76/1.47  fof(f2,axiom,(
% 7.76/1.47    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 7.76/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.76/1.47  
% 7.76/1.47  fof(f15,plain,(
% 7.76/1.47    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 7.76/1.47    inference(ennf_transformation,[],[f2])).
% 7.76/1.47  
% 7.76/1.47  fof(f16,plain,(
% 7.76/1.47    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 7.76/1.47    inference(flattening,[],[f15])).
% 7.76/1.47  
% 7.76/1.47  fof(f48,plain,(
% 7.76/1.47    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 7.76/1.47    inference(cnf_transformation,[],[f16])).
% 7.76/1.47  
% 7.76/1.47  fof(f12,conjecture,(
% 7.76/1.47    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 7.76/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.76/1.47  
% 7.76/1.47  fof(f13,negated_conjecture,(
% 7.76/1.47    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 7.76/1.47    inference(negated_conjecture,[],[f12])).
% 7.76/1.47  
% 7.76/1.47  fof(f31,plain,(
% 7.76/1.47    ? [X0] : (? [X1] : ((X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 7.76/1.47    inference(ennf_transformation,[],[f13])).
% 7.76/1.47  
% 7.76/1.47  fof(f32,plain,(
% 7.76/1.47    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 7.76/1.47    inference(flattening,[],[f31])).
% 7.76/1.47  
% 7.76/1.47  fof(f43,plain,(
% 7.76/1.47    ( ! [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) => (sK4 != X0 & r4_wellord1(k1_wellord2(X0),k1_wellord2(sK4)) & v3_ordinal1(sK4))) )),
% 7.76/1.47    introduced(choice_axiom,[])).
% 7.76/1.47  
% 7.76/1.47  fof(f42,plain,(
% 7.76/1.47    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : (sK3 != X1 & r4_wellord1(k1_wellord2(sK3),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK3))),
% 7.76/1.47    introduced(choice_axiom,[])).
% 7.76/1.47  
% 7.76/1.47  fof(f44,plain,(
% 7.76/1.47    (sK3 != sK4 & r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) & v3_ordinal1(sK4)) & v3_ordinal1(sK3)),
% 7.76/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f32,f43,f42])).
% 7.76/1.47  
% 7.76/1.47  fof(f65,plain,(
% 7.76/1.47    v3_ordinal1(sK3)),
% 7.76/1.47    inference(cnf_transformation,[],[f44])).
% 7.76/1.47  
% 7.76/1.47  fof(f66,plain,(
% 7.76/1.47    v3_ordinal1(sK4)),
% 7.76/1.47    inference(cnf_transformation,[],[f44])).
% 7.76/1.47  
% 7.76/1.47  fof(f9,axiom,(
% 7.76/1.47    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => k1_wellord1(k1_wellord2(X1),X0) = X0)))),
% 7.76/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.76/1.47  
% 7.76/1.47  fof(f27,plain,(
% 7.76/1.47    ! [X0] : (! [X1] : ((k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 7.76/1.47    inference(ennf_transformation,[],[f9])).
% 7.76/1.47  
% 7.76/1.47  fof(f28,plain,(
% 7.76/1.47    ! [X0] : (! [X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 7.76/1.47    inference(flattening,[],[f27])).
% 7.76/1.47  
% 7.76/1.47  fof(f62,plain,(
% 7.76/1.47    ( ! [X0,X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 7.76/1.47    inference(cnf_transformation,[],[f28])).
% 7.76/1.47  
% 7.76/1.47  fof(f68,plain,(
% 7.76/1.47    sK3 != sK4),
% 7.76/1.47    inference(cnf_transformation,[],[f44])).
% 7.76/1.47  
% 7.76/1.47  fof(f6,axiom,(
% 7.76/1.47    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 7.76/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.76/1.47  
% 7.76/1.47  fof(f23,plain,(
% 7.76/1.47    ! [X0] : ((! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 7.76/1.47    inference(ennf_transformation,[],[f6])).
% 7.76/1.47  
% 7.76/1.47  fof(f24,plain,(
% 7.76/1.47    ! [X0] : (! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 7.76/1.47    inference(flattening,[],[f23])).
% 7.76/1.47  
% 7.76/1.47  fof(f53,plain,(
% 7.76/1.47    ( ! [X0,X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0)) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 7.76/1.47    inference(cnf_transformation,[],[f24])).
% 7.76/1.47  
% 7.76/1.47  fof(f7,axiom,(
% 7.76/1.47    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 7.76/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.76/1.47  
% 7.76/1.47  fof(f25,plain,(
% 7.76/1.47    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 7.76/1.47    inference(ennf_transformation,[],[f7])).
% 7.76/1.47  
% 7.76/1.47  fof(f26,plain,(
% 7.76/1.47    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 7.76/1.47    inference(flattening,[],[f25])).
% 7.76/1.47  
% 7.76/1.47  fof(f37,plain,(
% 7.76/1.47    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 7.76/1.47    inference(nnf_transformation,[],[f26])).
% 7.76/1.47  
% 7.76/1.47  fof(f38,plain,(
% 7.76/1.47    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 7.76/1.47    inference(flattening,[],[f37])).
% 7.76/1.47  
% 7.76/1.47  fof(f39,plain,(
% 7.76/1.47    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 7.76/1.47    inference(rectify,[],[f38])).
% 7.76/1.47  
% 7.76/1.47  fof(f40,plain,(
% 7.76/1.47    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK1(X0,X1),sK2(X0,X1)) | ~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)) & (r1_tarski(sK1(X0,X1),sK2(X0,X1)) | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)) & r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),X0)))),
% 7.76/1.47    introduced(choice_axiom,[])).
% 7.76/1.47  
% 7.76/1.47  fof(f41,plain,(
% 7.76/1.47    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK1(X0,X1),sK2(X0,X1)) | ~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)) & (r1_tarski(sK1(X0,X1),sK2(X0,X1)) | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)) & r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 7.76/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f39,f40])).
% 7.76/1.47  
% 7.76/1.47  fof(f54,plain,(
% 7.76/1.47    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 7.76/1.47    inference(cnf_transformation,[],[f41])).
% 7.76/1.47  
% 7.76/1.47  fof(f75,plain,(
% 7.76/1.47    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 7.76/1.47    inference(equality_resolution,[],[f54])).
% 7.76/1.47  
% 7.76/1.47  fof(f8,axiom,(
% 7.76/1.47    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 7.76/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.76/1.47  
% 7.76/1.47  fof(f61,plain,(
% 7.76/1.47    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 7.76/1.47    inference(cnf_transformation,[],[f8])).
% 7.76/1.47  
% 7.76/1.47  fof(f67,plain,(
% 7.76/1.47    r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4))),
% 7.76/1.47    inference(cnf_transformation,[],[f44])).
% 7.76/1.47  
% 7.76/1.47  fof(f5,axiom,(
% 7.76/1.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 7.76/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.76/1.47  
% 7.76/1.47  fof(f21,plain,(
% 7.76/1.47    ! [X0] : (! [X1] : ((r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.76/1.47    inference(ennf_transformation,[],[f5])).
% 7.76/1.47  
% 7.76/1.47  fof(f22,plain,(
% 7.76/1.47    ! [X0] : (! [X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.76/1.47    inference(flattening,[],[f21])).
% 7.76/1.47  
% 7.76/1.47  fof(f52,plain,(
% 7.76/1.47    ( ! [X0,X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.76/1.47    inference(cnf_transformation,[],[f22])).
% 7.76/1.47  
% 7.76/1.47  fof(f1,axiom,(
% 7.76/1.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.76/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.76/1.47  
% 7.76/1.47  fof(f14,plain,(
% 7.76/1.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.76/1.47    inference(ennf_transformation,[],[f1])).
% 7.76/1.47  
% 7.76/1.47  fof(f33,plain,(
% 7.76/1.47    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.76/1.47    inference(nnf_transformation,[],[f14])).
% 7.76/1.47  
% 7.76/1.47  fof(f34,plain,(
% 7.76/1.47    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.76/1.47    inference(rectify,[],[f33])).
% 7.76/1.47  
% 7.76/1.47  fof(f35,plain,(
% 7.76/1.47    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.76/1.47    introduced(choice_axiom,[])).
% 7.76/1.47  
% 7.76/1.47  fof(f36,plain,(
% 7.76/1.47    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.76/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 7.76/1.47  
% 7.76/1.47  fof(f46,plain,(
% 7.76/1.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.76/1.47    inference(cnf_transformation,[],[f36])).
% 7.76/1.47  
% 7.76/1.47  fof(f10,axiom,(
% 7.76/1.47    ! [X0] : (v3_ordinal1(X0) => v2_wellord1(k1_wellord2(X0)))),
% 7.76/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.76/1.47  
% 7.76/1.47  fof(f29,plain,(
% 7.76/1.47    ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0))),
% 7.76/1.47    inference(ennf_transformation,[],[f10])).
% 7.76/1.47  
% 7.76/1.47  fof(f63,plain,(
% 7.76/1.47    ( ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 7.76/1.47    inference(cnf_transformation,[],[f29])).
% 7.76/1.47  
% 7.76/1.47  fof(f4,axiom,(
% 7.76/1.47    ! [X0,X1] : (v1_relat_1(X1) => (v2_wellord1(X1) => k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) = k1_wellord1(X1,X0)))),
% 7.76/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.76/1.47  
% 7.76/1.47  fof(f19,plain,(
% 7.76/1.47    ! [X0,X1] : ((k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) = k1_wellord1(X1,X0) | ~v2_wellord1(X1)) | ~v1_relat_1(X1))),
% 7.76/1.47    inference(ennf_transformation,[],[f4])).
% 7.76/1.47  
% 7.76/1.47  fof(f20,plain,(
% 7.76/1.47    ! [X0,X1] : (k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) = k1_wellord1(X1,X0) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 7.76/1.47    inference(flattening,[],[f19])).
% 7.76/1.47  
% 7.76/1.47  fof(f51,plain,(
% 7.76/1.47    ( ! [X0,X1] : (k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) = k1_wellord1(X1,X0) | ~v2_wellord1(X1) | ~v1_relat_1(X1)) )),
% 7.76/1.47    inference(cnf_transformation,[],[f20])).
% 7.76/1.47  
% 7.76/1.47  fof(f3,axiom,(
% 7.76/1.47    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) => (r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2)))))),
% 7.76/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.76/1.47  
% 7.76/1.47  fof(f17,plain,(
% 7.76/1.47    ! [X0,X1,X2] : (((r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.76/1.47    inference(ennf_transformation,[],[f3])).
% 7.76/1.47  
% 7.76/1.47  fof(f18,plain,(
% 7.76/1.47    ! [X0,X1,X2] : ((r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | ~v1_relat_1(X2))),
% 7.76/1.47    inference(flattening,[],[f17])).
% 7.76/1.47  
% 7.76/1.47  fof(f49,plain,(
% 7.76/1.47    ( ! [X2,X0,X1] : (r2_hidden(X0,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | ~v1_relat_1(X2)) )),
% 7.76/1.47    inference(cnf_transformation,[],[f18])).
% 7.76/1.47  
% 7.76/1.47  fof(f47,plain,(
% 7.76/1.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.76/1.47    inference(cnf_transformation,[],[f36])).
% 7.76/1.47  
% 7.76/1.47  fof(f11,axiom,(
% 7.76/1.47    ! [X0,X1] : (r1_tarski(X0,X1) => k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0))),
% 7.76/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.76/1.47  
% 7.76/1.47  fof(f30,plain,(
% 7.76/1.47    ! [X0,X1] : (k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) | ~r1_tarski(X0,X1))),
% 7.76/1.47    inference(ennf_transformation,[],[f11])).
% 7.76/1.47  
% 7.76/1.47  fof(f64,plain,(
% 7.76/1.47    ( ! [X0,X1] : (k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) | ~r1_tarski(X0,X1)) )),
% 7.76/1.47    inference(cnf_transformation,[],[f30])).
% 7.76/1.47  
% 7.76/1.47  cnf(c_3,plain,
% 7.76/1.47      ( r2_hidden(X0,X1)
% 7.76/1.47      | r2_hidden(X1,X0)
% 7.76/1.47      | ~ v3_ordinal1(X1)
% 7.76/1.47      | ~ v3_ordinal1(X0)
% 7.76/1.47      | X1 = X0 ),
% 7.76/1.47      inference(cnf_transformation,[],[f48]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_636,plain,
% 7.76/1.47      ( X0 = X1
% 7.76/1.47      | r2_hidden(X1,X0) = iProver_top
% 7.76/1.47      | r2_hidden(X0,X1) = iProver_top
% 7.76/1.47      | v3_ordinal1(X1) != iProver_top
% 7.76/1.47      | v3_ordinal1(X0) != iProver_top ),
% 7.76/1.47      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_23,negated_conjecture,
% 7.76/1.47      ( v3_ordinal1(sK3) ),
% 7.76/1.47      inference(cnf_transformation,[],[f65]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_618,plain,
% 7.76/1.47      ( v3_ordinal1(sK3) = iProver_top ),
% 7.76/1.47      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_22,negated_conjecture,
% 7.76/1.47      ( v3_ordinal1(sK4) ),
% 7.76/1.47      inference(cnf_transformation,[],[f66]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_619,plain,
% 7.76/1.47      ( v3_ordinal1(sK4) = iProver_top ),
% 7.76/1.47      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_17,plain,
% 7.76/1.47      ( ~ r2_hidden(X0,X1)
% 7.76/1.47      | ~ v3_ordinal1(X1)
% 7.76/1.47      | ~ v3_ordinal1(X0)
% 7.76/1.47      | k1_wellord1(k1_wellord2(X1),X0) = X0 ),
% 7.76/1.47      inference(cnf_transformation,[],[f62]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_623,plain,
% 7.76/1.47      ( k1_wellord1(k1_wellord2(X0),X1) = X1
% 7.76/1.47      | r2_hidden(X1,X0) != iProver_top
% 7.76/1.47      | v3_ordinal1(X1) != iProver_top
% 7.76/1.47      | v3_ordinal1(X0) != iProver_top ),
% 7.76/1.47      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_1957,plain,
% 7.76/1.47      ( X0 = X1
% 7.76/1.47      | k1_wellord1(k1_wellord2(X0),X1) = X1
% 7.76/1.47      | r2_hidden(X0,X1) = iProver_top
% 7.76/1.47      | v3_ordinal1(X1) != iProver_top
% 7.76/1.47      | v3_ordinal1(X0) != iProver_top ),
% 7.76/1.47      inference(superposition,[status(thm)],[c_636,c_623]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_8707,plain,
% 7.76/1.47      ( X0 = X1
% 7.76/1.47      | k1_wellord1(k1_wellord2(X0),X1) = X1
% 7.76/1.47      | k1_wellord1(k1_wellord2(X1),X0) = X0
% 7.76/1.47      | v3_ordinal1(X1) != iProver_top
% 7.76/1.47      | v3_ordinal1(X0) != iProver_top ),
% 7.76/1.47      inference(superposition,[status(thm)],[c_1957,c_623]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_10219,plain,
% 7.76/1.47      ( k1_wellord1(k1_wellord2(X0),sK4) = sK4
% 7.76/1.47      | k1_wellord1(k1_wellord2(sK4),X0) = X0
% 7.76/1.47      | sK4 = X0
% 7.76/1.47      | v3_ordinal1(X0) != iProver_top ),
% 7.76/1.47      inference(superposition,[status(thm)],[c_619,c_8707]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_10552,plain,
% 7.76/1.47      ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3
% 7.76/1.47      | k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 7.76/1.47      | sK4 = sK3 ),
% 7.76/1.47      inference(superposition,[status(thm)],[c_618,c_10219]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_20,negated_conjecture,
% 7.76/1.47      ( sK3 != sK4 ),
% 7.76/1.47      inference(cnf_transformation,[],[f68]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_222,plain,( X0 = X0 ),theory(equality) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_251,plain,
% 7.76/1.47      ( sK3 = sK3 ),
% 7.76/1.47      inference(instantiation,[status(thm)],[c_222]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_223,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_879,plain,
% 7.76/1.47      ( sK4 != X0 | sK3 != X0 | sK3 = sK4 ),
% 7.76/1.47      inference(instantiation,[status(thm)],[c_223]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_880,plain,
% 7.76/1.47      ( sK4 != sK3 | sK3 = sK4 | sK3 != sK3 ),
% 7.76/1.47      inference(instantiation,[status(thm)],[c_879]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_10559,plain,
% 7.76/1.47      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 7.76/1.47      | k1_wellord1(k1_wellord2(sK4),sK3) = sK3 ),
% 7.76/1.47      inference(global_propositional_subsumption,
% 7.76/1.47                [status(thm)],
% 7.76/1.47                [c_10552,c_20,c_251,c_880]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_10560,plain,
% 7.76/1.47      ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3
% 7.76/1.47      | k1_wellord1(k1_wellord2(sK3),sK4) = sK4 ),
% 7.76/1.47      inference(renaming,[status(thm)],[c_10559]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_8,plain,
% 7.76/1.47      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
% 7.76/1.47      | ~ r2_hidden(X1,k3_relat_1(X0))
% 7.76/1.47      | ~ v2_wellord1(X0)
% 7.76/1.47      | ~ v1_relat_1(X0) ),
% 7.76/1.47      inference(cnf_transformation,[],[f53]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_631,plain,
% 7.76/1.47      ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) != iProver_top
% 7.76/1.47      | r2_hidden(X1,k3_relat_1(X0)) != iProver_top
% 7.76/1.47      | v2_wellord1(X0) != iProver_top
% 7.76/1.47      | v1_relat_1(X0) != iProver_top ),
% 7.76/1.47      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_10563,plain,
% 7.76/1.47      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 7.76/1.47      | r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) != iProver_top
% 7.76/1.47      | r2_hidden(sK3,k3_relat_1(k1_wellord2(sK4))) != iProver_top
% 7.76/1.47      | v2_wellord1(k1_wellord2(sK4)) != iProver_top
% 7.76/1.47      | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
% 7.76/1.47      inference(superposition,[status(thm)],[c_10560,c_631]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_15,plain,
% 7.76/1.47      ( ~ v1_relat_1(k1_wellord2(X0))
% 7.76/1.47      | k3_relat_1(k1_wellord2(X0)) = X0 ),
% 7.76/1.47      inference(cnf_transformation,[],[f75]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_16,plain,
% 7.76/1.47      ( v1_relat_1(k1_wellord2(X0)) ),
% 7.76/1.47      inference(cnf_transformation,[],[f61]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_172,plain,
% 7.76/1.47      ( k3_relat_1(k1_wellord2(X0)) = X0 ),
% 7.76/1.47      inference(global_propositional_subsumption,
% 7.76/1.47                [status(thm)],
% 7.76/1.47                [c_15,c_16]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_10609,plain,
% 7.76/1.47      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 7.76/1.47      | r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) != iProver_top
% 7.76/1.47      | r2_hidden(sK3,sK4) != iProver_top
% 7.76/1.47      | v2_wellord1(k1_wellord2(sK4)) != iProver_top
% 7.76/1.47      | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
% 7.76/1.47      inference(demodulation,[status(thm)],[c_10563,c_172]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_24,plain,
% 7.76/1.47      ( v3_ordinal1(sK3) = iProver_top ),
% 7.76/1.47      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_25,plain,
% 7.76/1.47      ( v3_ordinal1(sK4) = iProver_top ),
% 7.76/1.47      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_21,negated_conjecture,
% 7.76/1.47      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) ),
% 7.76/1.47      inference(cnf_transformation,[],[f67]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_26,plain,
% 7.76/1.47      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) = iProver_top ),
% 7.76/1.47      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_36,plain,
% 7.76/1.47      ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
% 7.76/1.47      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_38,plain,
% 7.76/1.47      ( v1_relat_1(k1_wellord2(sK3)) = iProver_top ),
% 7.76/1.47      inference(instantiation,[status(thm)],[c_36]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_233,plain,
% 7.76/1.47      ( X0 != X1 | k1_wellord2(X0) = k1_wellord2(X1) ),
% 7.76/1.47      theory(equality) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_246,plain,
% 7.76/1.47      ( k1_wellord2(sK3) = k1_wellord2(sK3) | sK3 != sK3 ),
% 7.76/1.47      inference(instantiation,[status(thm)],[c_233]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_1256,plain,
% 7.76/1.47      ( k1_wellord2(sK4) = k1_wellord2(sK4) ),
% 7.76/1.47      inference(instantiation,[status(thm)],[c_222]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_7,plain,
% 7.76/1.47      ( ~ r4_wellord1(X0,X1)
% 7.76/1.47      | r4_wellord1(X1,X0)
% 7.76/1.47      | ~ v1_relat_1(X1)
% 7.76/1.47      | ~ v1_relat_1(X0) ),
% 7.76/1.47      inference(cnf_transformation,[],[f52]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_864,plain,
% 7.76/1.47      ( r4_wellord1(X0,k1_wellord2(X1))
% 7.76/1.47      | ~ r4_wellord1(k1_wellord2(X1),X0)
% 7.76/1.47      | ~ v1_relat_1(X0)
% 7.76/1.47      | ~ v1_relat_1(k1_wellord2(X1)) ),
% 7.76/1.47      inference(instantiation,[status(thm)],[c_7]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_1063,plain,
% 7.76/1.47      ( ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
% 7.76/1.47      | r4_wellord1(k1_wellord2(X1),k1_wellord2(X0))
% 7.76/1.47      | ~ v1_relat_1(k1_wellord2(X1))
% 7.76/1.47      | ~ v1_relat_1(k1_wellord2(X0)) ),
% 7.76/1.47      inference(instantiation,[status(thm)],[c_864]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_1559,plain,
% 7.76/1.47      ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3))
% 7.76/1.47      | ~ r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4))
% 7.76/1.47      | ~ v1_relat_1(k1_wellord2(sK4))
% 7.76/1.47      | ~ v1_relat_1(k1_wellord2(sK3)) ),
% 7.76/1.47      inference(instantiation,[status(thm)],[c_1063]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_1560,plain,
% 7.76/1.47      ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
% 7.76/1.47      | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) != iProver_top
% 7.76/1.47      | v1_relat_1(k1_wellord2(sK4)) != iProver_top
% 7.76/1.47      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 7.76/1.47      inference(predicate_to_equality,[status(thm)],[c_1559]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_1920,plain,
% 7.76/1.47      ( v1_relat_1(k1_wellord2(sK4)) ),
% 7.76/1.47      inference(instantiation,[status(thm)],[c_16]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_1921,plain,
% 7.76/1.47      ( v1_relat_1(k1_wellord2(sK4)) = iProver_top ),
% 7.76/1.47      inference(predicate_to_equality,[status(thm)],[c_1920]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_1925,plain,
% 7.76/1.47      ( k3_relat_1(k1_wellord2(sK4)) = sK4 ),
% 7.76/1.47      inference(instantiation,[status(thm)],[c_172]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_232,plain,
% 7.76/1.47      ( ~ r4_wellord1(X0,X1) | r4_wellord1(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.76/1.47      theory(equality) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_1745,plain,
% 7.76/1.47      ( r4_wellord1(X0,X1)
% 7.76/1.47      | ~ r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3))
% 7.76/1.47      | X0 != k1_wellord2(sK4)
% 7.76/1.47      | X1 != k1_wellord2(sK3) ),
% 7.76/1.47      inference(instantiation,[status(thm)],[c_232]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_2179,plain,
% 7.76/1.47      ( r4_wellord1(k1_wellord2(sK4),X0)
% 7.76/1.47      | ~ r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3))
% 7.76/1.47      | X0 != k1_wellord2(sK3)
% 7.76/1.47      | k1_wellord2(sK4) != k1_wellord2(sK4) ),
% 7.76/1.47      inference(instantiation,[status(thm)],[c_1745]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_4017,plain,
% 7.76/1.47      ( r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),X0)))
% 7.76/1.47      | ~ r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3))
% 7.76/1.47      | k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),X0)) != k1_wellord2(sK3)
% 7.76/1.47      | k1_wellord2(sK4) != k1_wellord2(sK4) ),
% 7.76/1.47      inference(instantiation,[status(thm)],[c_2179]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_4019,plain,
% 7.76/1.47      ( k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),X0)) != k1_wellord2(sK3)
% 7.76/1.47      | k1_wellord2(sK4) != k1_wellord2(sK4)
% 7.76/1.47      | r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),X0))) = iProver_top
% 7.76/1.47      | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) != iProver_top ),
% 7.76/1.47      inference(predicate_to_equality,[status(thm)],[c_4017]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_4021,plain,
% 7.76/1.47      ( k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),sK3)) != k1_wellord2(sK3)
% 7.76/1.47      | k1_wellord2(sK4) != k1_wellord2(sK4)
% 7.76/1.47      | r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),sK3))) = iProver_top
% 7.76/1.47      | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) != iProver_top ),
% 7.76/1.47      inference(instantiation,[status(thm)],[c_4019]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_4018,plain,
% 7.76/1.47      ( ~ r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),X0)))
% 7.76/1.47      | ~ r2_hidden(X0,k3_relat_1(k1_wellord2(sK4)))
% 7.76/1.47      | ~ v2_wellord1(k1_wellord2(sK4))
% 7.76/1.47      | ~ v1_relat_1(k1_wellord2(sK4)) ),
% 7.76/1.47      inference(instantiation,[status(thm)],[c_8]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_4023,plain,
% 7.76/1.47      ( r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),X0))) != iProver_top
% 7.76/1.47      | r2_hidden(X0,k3_relat_1(k1_wellord2(sK4))) != iProver_top
% 7.76/1.47      | v2_wellord1(k1_wellord2(sK4)) != iProver_top
% 7.76/1.47      | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
% 7.76/1.47      inference(predicate_to_equality,[status(thm)],[c_4018]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_4025,plain,
% 7.76/1.47      ( r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),sK3))) != iProver_top
% 7.76/1.47      | r2_hidden(sK3,k3_relat_1(k1_wellord2(sK4))) != iProver_top
% 7.76/1.47      | v2_wellord1(k1_wellord2(sK4)) != iProver_top
% 7.76/1.47      | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
% 7.76/1.47      inference(instantiation,[status(thm)],[c_4023]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_1,plain,
% 7.76/1.47      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.76/1.47      inference(cnf_transformation,[],[f46]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_638,plain,
% 7.76/1.47      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 7.76/1.47      | r1_tarski(X0,X1) = iProver_top ),
% 7.76/1.47      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_18,plain,
% 7.76/1.47      ( v2_wellord1(k1_wellord2(X0)) | ~ v3_ordinal1(X0) ),
% 7.76/1.47      inference(cnf_transformation,[],[f63]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_622,plain,
% 7.76/1.47      ( v2_wellord1(k1_wellord2(X0)) = iProver_top
% 7.76/1.47      | v3_ordinal1(X0) != iProver_top ),
% 7.76/1.47      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_6,plain,
% 7.76/1.47      ( ~ v2_wellord1(X0)
% 7.76/1.47      | ~ v1_relat_1(X0)
% 7.76/1.47      | k3_relat_1(k2_wellord1(X0,k1_wellord1(X0,X1))) = k1_wellord1(X0,X1) ),
% 7.76/1.47      inference(cnf_transformation,[],[f51]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_633,plain,
% 7.76/1.47      ( k3_relat_1(k2_wellord1(X0,k1_wellord1(X0,X1))) = k1_wellord1(X0,X1)
% 7.76/1.47      | v2_wellord1(X0) != iProver_top
% 7.76/1.47      | v1_relat_1(X0) != iProver_top ),
% 7.76/1.47      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_1787,plain,
% 7.76/1.47      ( k3_relat_1(k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) = k1_wellord1(k1_wellord2(X0),X1)
% 7.76/1.47      | v1_relat_1(k1_wellord2(X0)) != iProver_top
% 7.76/1.47      | v3_ordinal1(X0) != iProver_top ),
% 7.76/1.47      inference(superposition,[status(thm)],[c_622,c_633]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_3809,plain,
% 7.76/1.47      ( k3_relat_1(k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) = k1_wellord1(k1_wellord2(X0),X1)
% 7.76/1.47      | v3_ordinal1(X0) != iProver_top ),
% 7.76/1.47      inference(global_propositional_subsumption,
% 7.76/1.47                [status(thm)],
% 7.76/1.47                [c_1787,c_36]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_3817,plain,
% 7.76/1.47      ( k3_relat_1(k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),X0))) = k1_wellord1(k1_wellord2(sK4),X0) ),
% 7.76/1.47      inference(superposition,[status(thm)],[c_619,c_3809]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_5,plain,
% 7.76/1.47      ( r2_hidden(X0,k3_relat_1(X1))
% 7.76/1.47      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X1,X2)))
% 7.76/1.47      | ~ v1_relat_1(X1) ),
% 7.76/1.47      inference(cnf_transformation,[],[f49]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_634,plain,
% 7.76/1.47      ( r2_hidden(X0,k3_relat_1(X1)) = iProver_top
% 7.76/1.47      | r2_hidden(X0,k3_relat_1(k2_wellord1(X1,X2))) != iProver_top
% 7.76/1.47      | v1_relat_1(X1) != iProver_top ),
% 7.76/1.47      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_3827,plain,
% 7.76/1.47      ( r2_hidden(X0,k1_wellord1(k1_wellord2(sK4),X1)) != iProver_top
% 7.76/1.47      | r2_hidden(X0,k3_relat_1(k1_wellord2(sK4))) = iProver_top
% 7.76/1.47      | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
% 7.76/1.47      inference(superposition,[status(thm)],[c_3817,c_634]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_3889,plain,
% 7.76/1.47      ( r2_hidden(X0,k1_wellord1(k1_wellord2(sK4),X1)) != iProver_top
% 7.76/1.47      | r2_hidden(X0,sK4) = iProver_top
% 7.76/1.47      | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
% 7.76/1.47      inference(demodulation,[status(thm)],[c_3827,c_172]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_4377,plain,
% 7.76/1.47      ( r2_hidden(X0,sK4) = iProver_top
% 7.76/1.47      | r2_hidden(X0,k1_wellord1(k1_wellord2(sK4),X1)) != iProver_top ),
% 7.76/1.47      inference(global_propositional_subsumption,
% 7.76/1.47                [status(thm)],
% 7.76/1.47                [c_3889,c_1921]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_4378,plain,
% 7.76/1.47      ( r2_hidden(X0,k1_wellord1(k1_wellord2(sK4),X1)) != iProver_top
% 7.76/1.47      | r2_hidden(X0,sK4) = iProver_top ),
% 7.76/1.47      inference(renaming,[status(thm)],[c_4377]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_4385,plain,
% 7.76/1.47      ( r2_hidden(sK0(k1_wellord1(k1_wellord2(sK4),X0),X1),sK4) = iProver_top
% 7.76/1.47      | r1_tarski(k1_wellord1(k1_wellord2(sK4),X0),X1) = iProver_top ),
% 7.76/1.47      inference(superposition,[status(thm)],[c_638,c_4378]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_0,plain,
% 7.76/1.47      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.76/1.47      inference(cnf_transformation,[],[f47]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_639,plain,
% 7.76/1.47      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 7.76/1.47      | r1_tarski(X0,X1) = iProver_top ),
% 7.76/1.47      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_4711,plain,
% 7.76/1.47      ( r1_tarski(k1_wellord1(k1_wellord2(sK4),X0),sK4) = iProver_top ),
% 7.76/1.47      inference(superposition,[status(thm)],[c_4385,c_639]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_19,plain,
% 7.76/1.47      ( ~ r1_tarski(X0,X1)
% 7.76/1.47      | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ),
% 7.76/1.47      inference(cnf_transformation,[],[f64]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_621,plain,
% 7.76/1.47      ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 7.76/1.47      | r1_tarski(X1,X0) != iProver_top ),
% 7.76/1.47      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_4854,plain,
% 7.76/1.47      ( k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),X0)) = k1_wellord2(k1_wellord1(k1_wellord2(sK4),X0)) ),
% 7.76/1.47      inference(superposition,[status(thm)],[c_4711,c_621]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_4855,plain,
% 7.76/1.47      ( k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),sK3)) = k1_wellord2(k1_wellord1(k1_wellord2(sK4),sK3)) ),
% 7.76/1.47      inference(instantiation,[status(thm)],[c_4854]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_1019,plain,
% 7.76/1.47      ( X0 != X1 | X0 = k1_wellord2(sK3) | k1_wellord2(sK3) != X1 ),
% 7.76/1.47      inference(instantiation,[status(thm)],[c_223]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_1285,plain,
% 7.76/1.47      ( X0 != k1_wellord2(X1)
% 7.76/1.47      | X0 = k1_wellord2(sK3)
% 7.76/1.47      | k1_wellord2(sK3) != k1_wellord2(X1) ),
% 7.76/1.47      inference(instantiation,[status(thm)],[c_1019]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_2125,plain,
% 7.76/1.47      ( k2_wellord1(k1_wellord2(X0),X1) != k1_wellord2(X1)
% 7.76/1.47      | k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(sK3)
% 7.76/1.47      | k1_wellord2(sK3) != k1_wellord2(X1) ),
% 7.76/1.47      inference(instantiation,[status(thm)],[c_1285]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_5209,plain,
% 7.76/1.47      ( k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),X0)) != k1_wellord2(k1_wellord1(k1_wellord2(sK4),X0))
% 7.76/1.47      | k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),X0)) = k1_wellord2(sK3)
% 7.76/1.47      | k1_wellord2(sK3) != k1_wellord2(k1_wellord1(k1_wellord2(sK4),X0)) ),
% 7.76/1.47      inference(instantiation,[status(thm)],[c_2125]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_5210,plain,
% 7.76/1.47      ( k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),sK3)) != k1_wellord2(k1_wellord1(k1_wellord2(sK4),sK3))
% 7.76/1.47      | k2_wellord1(k1_wellord2(sK4),k1_wellord1(k1_wellord2(sK4),sK3)) = k1_wellord2(sK3)
% 7.76/1.47      | k1_wellord2(sK3) != k1_wellord2(k1_wellord1(k1_wellord2(sK4),sK3)) ),
% 7.76/1.47      inference(instantiation,[status(thm)],[c_5209]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_5211,plain,
% 7.76/1.47      ( v2_wellord1(k1_wellord2(sK4)) | ~ v3_ordinal1(sK4) ),
% 7.76/1.47      inference(instantiation,[status(thm)],[c_18]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_5212,plain,
% 7.76/1.47      ( v2_wellord1(k1_wellord2(sK4)) = iProver_top
% 7.76/1.47      | v3_ordinal1(sK4) != iProver_top ),
% 7.76/1.47      inference(predicate_to_equality,[status(thm)],[c_5211]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_225,plain,
% 7.76/1.47      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.76/1.47      theory(equality) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_3680,plain,
% 7.76/1.47      ( r2_hidden(X0,X1) | ~ r2_hidden(sK3,sK4) | X1 != sK4 | X0 != sK3 ),
% 7.76/1.47      inference(instantiation,[status(thm)],[c_225]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_8942,plain,
% 7.76/1.47      ( r2_hidden(X0,k3_relat_1(k1_wellord2(sK4)))
% 7.76/1.47      | ~ r2_hidden(sK3,sK4)
% 7.76/1.47      | X0 != sK3
% 7.76/1.47      | k3_relat_1(k1_wellord2(sK4)) != sK4 ),
% 7.76/1.47      inference(instantiation,[status(thm)],[c_3680]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_8943,plain,
% 7.76/1.47      ( X0 != sK3
% 7.76/1.47      | k3_relat_1(k1_wellord2(sK4)) != sK4
% 7.76/1.47      | r2_hidden(X0,k3_relat_1(k1_wellord2(sK4))) = iProver_top
% 7.76/1.47      | r2_hidden(sK3,sK4) != iProver_top ),
% 7.76/1.47      inference(predicate_to_equality,[status(thm)],[c_8942]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_8945,plain,
% 7.76/1.47      ( k3_relat_1(k1_wellord2(sK4)) != sK4
% 7.76/1.47      | sK3 != sK3
% 7.76/1.47      | r2_hidden(sK3,k3_relat_1(k1_wellord2(sK4))) = iProver_top
% 7.76/1.47      | r2_hidden(sK3,sK4) != iProver_top ),
% 7.76/1.47      inference(instantiation,[status(thm)],[c_8943]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_1284,plain,
% 7.76/1.47      ( X0 != X1 | k1_wellord2(sK3) != X1 | k1_wellord2(sK3) = X0 ),
% 7.76/1.47      inference(instantiation,[status(thm)],[c_223]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_2117,plain,
% 7.76/1.47      ( X0 != k1_wellord2(sK3)
% 7.76/1.47      | k1_wellord2(sK3) = X0
% 7.76/1.47      | k1_wellord2(sK3) != k1_wellord2(sK3) ),
% 7.76/1.47      inference(instantiation,[status(thm)],[c_1284]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_2357,plain,
% 7.76/1.47      ( k1_wellord2(X0) != k1_wellord2(sK3)
% 7.76/1.47      | k1_wellord2(sK3) = k1_wellord2(X0)
% 7.76/1.47      | k1_wellord2(sK3) != k1_wellord2(sK3) ),
% 7.76/1.47      inference(instantiation,[status(thm)],[c_2117]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_15886,plain,
% 7.76/1.47      ( k1_wellord2(k1_wellord1(k1_wellord2(sK4),X0)) != k1_wellord2(sK3)
% 7.76/1.47      | k1_wellord2(sK3) = k1_wellord2(k1_wellord1(k1_wellord2(sK4),X0))
% 7.76/1.47      | k1_wellord2(sK3) != k1_wellord2(sK3) ),
% 7.76/1.47      inference(instantiation,[status(thm)],[c_2357]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_15889,plain,
% 7.76/1.47      ( k1_wellord2(k1_wellord1(k1_wellord2(sK4),sK3)) != k1_wellord2(sK3)
% 7.76/1.47      | k1_wellord2(sK3) = k1_wellord2(k1_wellord1(k1_wellord2(sK4),sK3))
% 7.76/1.47      | k1_wellord2(sK3) != k1_wellord2(sK3) ),
% 7.76/1.47      inference(instantiation,[status(thm)],[c_15886]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_21413,plain,
% 7.76/1.47      ( ~ r2_hidden(sK3,sK4)
% 7.76/1.47      | ~ v3_ordinal1(sK4)
% 7.76/1.47      | ~ v3_ordinal1(sK3)
% 7.76/1.47      | k1_wellord1(k1_wellord2(sK4),sK3) = sK3 ),
% 7.76/1.47      inference(instantiation,[status(thm)],[c_17]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_21414,plain,
% 7.76/1.47      ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3
% 7.76/1.47      | r2_hidden(sK3,sK4) != iProver_top
% 7.76/1.47      | v3_ordinal1(sK4) != iProver_top
% 7.76/1.47      | v3_ordinal1(sK3) != iProver_top ),
% 7.76/1.47      inference(predicate_to_equality,[status(thm)],[c_21413]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_1022,plain,
% 7.76/1.47      ( X0 != sK3 | k1_wellord2(X0) = k1_wellord2(sK3) ),
% 7.76/1.47      inference(instantiation,[status(thm)],[c_233]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_28573,plain,
% 7.76/1.47      ( k1_wellord1(k1_wellord2(sK4),X0) != sK3
% 7.76/1.47      | k1_wellord2(k1_wellord1(k1_wellord2(sK4),X0)) = k1_wellord2(sK3) ),
% 7.76/1.47      inference(instantiation,[status(thm)],[c_1022]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_28574,plain,
% 7.76/1.47      ( k1_wellord1(k1_wellord2(sK4),sK3) != sK3
% 7.76/1.47      | k1_wellord2(k1_wellord1(k1_wellord2(sK4),sK3)) = k1_wellord2(sK3) ),
% 7.76/1.47      inference(instantiation,[status(thm)],[c_28573]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_32675,plain,
% 7.76/1.47      ( r2_hidden(sK3,sK4) != iProver_top ),
% 7.76/1.47      inference(global_propositional_subsumption,
% 7.76/1.47                [status(thm)],
% 7.76/1.47                [c_10609,c_24,c_25,c_26,c_38,c_246,c_251,c_1256,c_1560,
% 7.76/1.47                 c_1921,c_1925,c_4021,c_4025,c_4855,c_5210,c_5212,c_8945,
% 7.76/1.47                 c_15889,c_21414,c_28574]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_32683,plain,
% 7.76/1.47      ( sK4 = sK3
% 7.76/1.47      | r2_hidden(sK4,sK3) = iProver_top
% 7.76/1.47      | v3_ordinal1(sK4) != iProver_top
% 7.76/1.47      | v3_ordinal1(sK3) != iProver_top ),
% 7.76/1.47      inference(superposition,[status(thm)],[c_636,c_32675]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_3639,plain,
% 7.76/1.47      ( r2_hidden(sK4,sK3)
% 7.76/1.47      | r2_hidden(sK3,sK4)
% 7.76/1.47      | ~ v3_ordinal1(sK4)
% 7.76/1.47      | ~ v3_ordinal1(sK3) ),
% 7.76/1.47      inference(resolution,[status(thm)],[c_3,c_20]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_4447,plain,
% 7.76/1.47      ( r2_hidden(sK4,sK3) | r2_hidden(sK3,sK4) ),
% 7.76/1.47      inference(global_propositional_subsumption,
% 7.76/1.47                [status(thm)],
% 7.76/1.47                [c_3639,c_23,c_22]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_4449,plain,
% 7.76/1.47      ( r2_hidden(sK4,sK3) = iProver_top
% 7.76/1.47      | r2_hidden(sK3,sK4) = iProver_top ),
% 7.76/1.47      inference(predicate_to_equality,[status(thm)],[c_4447]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_32703,plain,
% 7.76/1.47      ( r2_hidden(sK4,sK3) = iProver_top ),
% 7.76/1.47      inference(global_propositional_subsumption,
% 7.76/1.47                [status(thm)],
% 7.76/1.47                [c_32683,c_24,c_25,c_26,c_38,c_246,c_251,c_1256,c_1560,
% 7.76/1.47                 c_1921,c_1925,c_4021,c_4025,c_4449,c_4855,c_5210,c_5212,
% 7.76/1.47                 c_8945,c_15889,c_21414,c_28574]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_32709,plain,
% 7.76/1.47      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 7.76/1.47      | v3_ordinal1(sK4) != iProver_top
% 7.76/1.47      | v3_ordinal1(sK3) != iProver_top ),
% 7.76/1.47      inference(superposition,[status(thm)],[c_32703,c_623]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_1927,plain,
% 7.76/1.47      ( ~ r2_hidden(sK4,X0)
% 7.76/1.47      | ~ v3_ordinal1(X0)
% 7.76/1.47      | ~ v3_ordinal1(sK4)
% 7.76/1.47      | k1_wellord1(k1_wellord2(X0),sK4) = sK4 ),
% 7.76/1.47      inference(instantiation,[status(thm)],[c_17]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_1929,plain,
% 7.76/1.47      ( k1_wellord1(k1_wellord2(X0),sK4) = sK4
% 7.76/1.47      | r2_hidden(sK4,X0) != iProver_top
% 7.76/1.47      | v3_ordinal1(X0) != iProver_top
% 7.76/1.47      | v3_ordinal1(sK4) != iProver_top ),
% 7.76/1.47      inference(predicate_to_equality,[status(thm)],[c_1927]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_1931,plain,
% 7.76/1.47      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 7.76/1.47      | r2_hidden(sK4,sK3) != iProver_top
% 7.76/1.47      | v3_ordinal1(sK4) != iProver_top
% 7.76/1.47      | v3_ordinal1(sK3) != iProver_top ),
% 7.76/1.47      inference(instantiation,[status(thm)],[c_1929]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_32910,plain,
% 7.76/1.47      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4 ),
% 7.76/1.47      inference(global_propositional_subsumption,
% 7.76/1.47                [status(thm)],
% 7.76/1.47                [c_32709,c_24,c_25,c_26,c_38,c_246,c_251,c_1256,c_1560,
% 7.76/1.47                 c_1921,c_1925,c_1931,c_4021,c_4025,c_4449,c_4855,c_5210,
% 7.76/1.47                 c_5212,c_8945,c_15889,c_21414,c_28574]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_3818,plain,
% 7.76/1.47      ( k3_relat_1(k2_wellord1(k1_wellord2(sK3),k1_wellord1(k1_wellord2(sK3),X0))) = k1_wellord1(k1_wellord2(sK3),X0) ),
% 7.76/1.47      inference(superposition,[status(thm)],[c_618,c_3809]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_4295,plain,
% 7.76/1.47      ( r2_hidden(X0,k1_wellord1(k1_wellord2(sK3),X1)) != iProver_top
% 7.76/1.47      | r2_hidden(X0,k3_relat_1(k1_wellord2(sK3))) = iProver_top
% 7.76/1.47      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 7.76/1.47      inference(superposition,[status(thm)],[c_3818,c_634]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_4357,plain,
% 7.76/1.47      ( r2_hidden(X0,k1_wellord1(k1_wellord2(sK3),X1)) != iProver_top
% 7.76/1.47      | r2_hidden(X0,sK3) = iProver_top
% 7.76/1.47      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 7.76/1.47      inference(demodulation,[status(thm)],[c_4295,c_172]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_4987,plain,
% 7.76/1.47      ( r2_hidden(X0,sK3) = iProver_top
% 7.76/1.47      | r2_hidden(X0,k1_wellord1(k1_wellord2(sK3),X1)) != iProver_top ),
% 7.76/1.47      inference(global_propositional_subsumption,
% 7.76/1.47                [status(thm)],
% 7.76/1.47                [c_4357,c_38]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_4988,plain,
% 7.76/1.47      ( r2_hidden(X0,k1_wellord1(k1_wellord2(sK3),X1)) != iProver_top
% 7.76/1.47      | r2_hidden(X0,sK3) = iProver_top ),
% 7.76/1.47      inference(renaming,[status(thm)],[c_4987]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_4995,plain,
% 7.76/1.47      ( r2_hidden(sK0(k1_wellord1(k1_wellord2(sK3),X0),X1),sK3) = iProver_top
% 7.76/1.47      | r1_tarski(k1_wellord1(k1_wellord2(sK3),X0),X1) = iProver_top ),
% 7.76/1.47      inference(superposition,[status(thm)],[c_638,c_4988]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_5224,plain,
% 7.76/1.47      ( r1_tarski(k1_wellord1(k1_wellord2(sK3),X0),sK3) = iProver_top ),
% 7.76/1.47      inference(superposition,[status(thm)],[c_4995,c_639]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_5250,plain,
% 7.76/1.47      ( k2_wellord1(k1_wellord2(sK3),k1_wellord1(k1_wellord2(sK3),X0)) = k1_wellord2(k1_wellord1(k1_wellord2(sK3),X0)) ),
% 7.76/1.47      inference(superposition,[status(thm)],[c_5224,c_621]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_5409,plain,
% 7.76/1.47      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(k1_wellord1(k1_wellord2(sK3),X0))) != iProver_top
% 7.76/1.47      | r2_hidden(X0,k3_relat_1(k1_wellord2(sK3))) != iProver_top
% 7.76/1.47      | v2_wellord1(k1_wellord2(sK3)) != iProver_top
% 7.76/1.47      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 7.76/1.47      inference(superposition,[status(thm)],[c_5250,c_631]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_5440,plain,
% 7.76/1.47      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(k1_wellord1(k1_wellord2(sK3),X0))) != iProver_top
% 7.76/1.47      | r2_hidden(X0,sK3) != iProver_top
% 7.76/1.47      | v2_wellord1(k1_wellord2(sK3)) != iProver_top
% 7.76/1.47      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 7.76/1.47      inference(demodulation,[status(thm)],[c_5409,c_172]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_30,plain,
% 7.76/1.47      ( v2_wellord1(k1_wellord2(X0)) = iProver_top
% 7.76/1.47      | v3_ordinal1(X0) != iProver_top ),
% 7.76/1.47      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_32,plain,
% 7.76/1.47      ( v2_wellord1(k1_wellord2(sK3)) = iProver_top
% 7.76/1.47      | v3_ordinal1(sK3) != iProver_top ),
% 7.76/1.47      inference(instantiation,[status(thm)],[c_30]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_12301,plain,
% 7.76/1.47      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(k1_wellord1(k1_wellord2(sK3),X0))) != iProver_top
% 7.76/1.47      | r2_hidden(X0,sK3) != iProver_top ),
% 7.76/1.47      inference(global_propositional_subsumption,
% 7.76/1.47                [status(thm)],
% 7.76/1.47                [c_5440,c_24,c_32,c_38]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(c_32916,plain,
% 7.76/1.47      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) != iProver_top
% 7.76/1.47      | r2_hidden(sK4,sK3) != iProver_top ),
% 7.76/1.47      inference(superposition,[status(thm)],[c_32910,c_12301]) ).
% 7.76/1.47  
% 7.76/1.47  cnf(contradiction,plain,
% 7.76/1.47      ( $false ),
% 7.76/1.47      inference(minisat,[status(thm)],[c_32916,c_32675,c_4449,c_26]) ).
% 7.76/1.47  
% 7.76/1.47  
% 7.76/1.47  % SZS output end CNFRefutation for theBenchmark.p
% 7.76/1.47  
% 7.76/1.47  ------                               Statistics
% 7.76/1.47  
% 7.76/1.47  ------ Selected
% 7.76/1.47  
% 7.76/1.47  total_time:                             0.9
% 7.76/1.47  
%------------------------------------------------------------------------------
