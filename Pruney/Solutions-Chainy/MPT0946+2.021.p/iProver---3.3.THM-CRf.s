%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:45 EST 2020

% Result     : Theorem 11.79s
% Output     : CNFRefutation 11.79s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_16846)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
     => ( sK5 != X0
        & r4_wellord1(k1_wellord2(X0),k1_wellord2(sK5))
        & v3_ordinal1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( sK4 != X1
          & r4_wellord1(k1_wellord2(sK4),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( sK4 != sK5
    & r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK5))
    & v3_ordinal1(sK5)
    & v3_ordinal1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f32,f46,f45])).

fof(f72,plain,(
    v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f2,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f73,plain,(
    v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f47])).

fof(f3,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ? [X1] :
          ( v4_ordinal1(X1)
          & r2_hidden(X0,X1)
          & v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ? [X1] :
          ( r2_hidden(X0,X1)
          & v3_ordinal1(X1) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r2_hidden(X0,X1)
          & v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r2_hidden(X0,X1)
          & v3_ordinal1(X1) )
     => ( r2_hidden(X0,sK0(X0))
        & v3_ordinal1(sK0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ( r2_hidden(X0,sK0(X0))
        & v3_ordinal1(sK0(X0)) )
      | ~ v3_ordinal1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f33])).

fof(f52,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK0(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

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

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_wellord1(k1_wellord2(X1),X0) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,(
    ! [X0] :
      ( v3_ordinal1(sK0(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

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

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0)
          | sK1(X0,X1,X2) = X1
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0)
            & sK1(X0,X1,X2) != X1 )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ( ( ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0)
                | sK1(X0,X1,X2) = X1
                | ~ r2_hidden(sK1(X0,X1,X2),X2) )
              & ( ( r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0)
                  & sK1(X0,X1,X2) != X1 )
                | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f77,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f8,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
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
    inference(nnf_transformation,[],[f26])).

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
     => ( ( ~ r1_tarski(sK2(X0,X1),sK3(X0,X1))
          | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
        & ( r1_tarski(sK2(X0,X1),sK3(X0,X1))
          | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
        & r2_hidden(sK3(X0,X1),X0)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK2(X0,X1),sK3(X0,X1))
              | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
            & ( r1_tarski(sK2(X0,X1),sK3(X0,X1))
              | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
            & r2_hidden(sK3(X0,X1),X0)
            & r2_hidden(sK2(X0,X1),X0) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f42,f43])).

fof(f62,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_tarski(X4,X5)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f85,plain,(
    ! [X4,X0,X5] :
      ( r1_tarski(X4,X5)
      | ~ r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f86,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f61])).

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

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f75,plain,(
    sK4 != sK5 ),
    inference(cnf_transformation,[],[f47])).

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

fof(f60,plain,(
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

fof(f70,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f74,plain,(
    r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK5)) ),
    inference(cnf_transformation,[],[f47])).

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

fof(f59,plain,(
    ! [X0,X1] :
      ( r4_wellord1(X1,X0)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 != X4
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f78,plain,(
    ! [X4,X2,X0] :
      ( ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X4) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f79,plain,(
    ! [X4,X0] :
      ( ~ r2_hidden(X4,k1_wellord1(X0,X4))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f78])).

cnf(c_27,negated_conjecture,
    ( v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1243,plain,
    ( v3_ordinal1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1264,plain,
    ( X0 = X1
    | r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_26,negated_conjecture,
    ( v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1244,plain,
    ( v3_ordinal1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3,plain,
    ( r2_hidden(X0,sK0(X0))
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1263,plain,
    ( r2_hidden(X0,sK0(X0)) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | k1_wellord1(k1_wellord2(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1247,plain,
    ( k1_wellord1(k1_wellord2(X0),X1) = X1
    | r2_hidden(X1,X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2237,plain,
    ( k1_wellord1(k1_wellord2(sK0(X0)),X0) = X0
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK0(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1263,c_1247])).

cnf(c_4,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(sK0(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_84,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2384,plain,
    ( v3_ordinal1(X0) != iProver_top
    | k1_wellord1(k1_wellord2(sK0(X0)),X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2237,c_84])).

cnf(c_2385,plain,
    ( k1_wellord1(k1_wellord2(sK0(X0)),X0) = X0
    | v3_ordinal1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2384])).

cnf(c_2393,plain,
    ( k1_wellord1(k1_wellord2(sK0(sK5)),sK5) = sK5 ),
    inference(superposition,[status(thm)],[c_1244,c_2385])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1257,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2407,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(X0,sK5),k1_wellord2(sK0(sK5))) = iProver_top
    | v1_relat_1(k1_wellord2(sK0(sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2393,c_1257])).

cnf(c_20,plain,
    ( v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1248,plain,
    ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3167,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(X0,sK5),k1_wellord2(sK0(sK5))) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2407,c_1248])).

cnf(c_18,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2))
    | ~ v1_relat_1(k1_wellord2(X2)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1249,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2)) != iProver_top
    | v1_relat_1(k1_wellord2(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1387,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1249,c_1248])).

cnf(c_5827,plain,
    ( r1_tarski(X0,sK5) = iProver_top
    | r2_hidden(X0,sK0(sK5)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK5,sK0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3167,c_1387])).

cnf(c_29,plain,
    ( v3_ordinal1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2859,plain,
    ( r2_hidden(sK5,sK0(sK5))
    | ~ v3_ordinal1(sK5) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2862,plain,
    ( r2_hidden(sK5,sK0(sK5)) = iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2859])).

cnf(c_1,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1265,plain,
    ( r2_hidden(X0,k3_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3172,plain,
    ( r2_hidden(X0,k3_relat_1(k1_wellord2(sK0(sK5)))) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | v1_relat_1(k1_wellord2(sK0(sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3167,c_1265])).

cnf(c_19,plain,
    ( ~ v1_relat_1(k1_wellord2(X0))
    | k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_159,plain,
    ( k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_20])).

cnf(c_3191,plain,
    ( r2_hidden(X0,sK0(sK5)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | v1_relat_1(k1_wellord2(sK0(sK5))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3172,c_159])).

cnf(c_6058,plain,
    ( r2_hidden(X0,sK0(sK5)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3191,c_1248])).

cnf(c_6964,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r1_tarski(X0,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5827,c_29,c_2862,c_6058])).

cnf(c_6965,plain,
    ( r1_tarski(X0,sK5) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_6964])).

cnf(c_6972,plain,
    ( sK5 = X0
    | r1_tarski(X0,sK5) = iProver_top
    | r2_hidden(sK5,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_6965])).

cnf(c_16760,plain,
    ( v3_ordinal1(X0) != iProver_top
    | r2_hidden(sK5,X0) = iProver_top
    | r1_tarski(X0,sK5) = iProver_top
    | sK5 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6972,c_29])).

cnf(c_16761,plain,
    ( sK5 = X0
    | r1_tarski(X0,sK5) = iProver_top
    | r2_hidden(sK5,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_16760])).

cnf(c_23,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1246,plain,
    ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_16770,plain,
    ( k2_wellord1(k1_wellord2(sK5),X0) = k1_wellord2(X0)
    | sK5 = X0
    | r2_hidden(sK5,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16761,c_1246])).

cnf(c_16779,plain,
    ( k2_wellord1(k1_wellord2(sK5),X0) = k1_wellord2(X0)
    | k1_wellord1(k1_wellord2(X0),sK5) = sK5
    | sK5 = X0
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_16770,c_1247])).

cnf(c_34513,plain,
    ( v3_ordinal1(X0) != iProver_top
    | sK5 = X0
    | k1_wellord1(k1_wellord2(X0),sK5) = sK5
    | k2_wellord1(k1_wellord2(sK5),X0) = k1_wellord2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16779,c_29])).

cnf(c_34514,plain,
    ( k2_wellord1(k1_wellord2(sK5),X0) = k1_wellord2(X0)
    | k1_wellord1(k1_wellord2(X0),sK5) = sK5
    | sK5 = X0
    | v3_ordinal1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_34513])).

cnf(c_34525,plain,
    ( k2_wellord1(k1_wellord2(sK5),sK4) = k1_wellord2(sK4)
    | k1_wellord1(k1_wellord2(sK4),sK5) = sK5
    | sK5 = sK4 ),
    inference(superposition,[status(thm)],[c_1243,c_34514])).

cnf(c_24,negated_conjecture,
    ( sK4 != sK5 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_791,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_818,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_791])).

cnf(c_792,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1512,plain,
    ( sK5 != X0
    | sK4 != X0
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_792])).

cnf(c_1513,plain,
    ( sK5 != sK4
    | sK4 = sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1512])).

cnf(c_34543,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK5) = sK5
    | k2_wellord1(k1_wellord2(sK5),sK4) = k1_wellord2(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_34525,c_27,c_26,c_24,c_818,c_1513,c_16846])).

cnf(c_34544,plain,
    ( k2_wellord1(k1_wellord2(sK5),sK4) = k1_wellord2(sK4)
    | k1_wellord1(k1_wellord2(sK4),sK5) = sK5 ),
    inference(renaming,[status(thm)],[c_34543])).

cnf(c_2722,plain,
    ( X0 = X1
    | k1_wellord1(k1_wellord2(X1),X0) = X0
    | r2_hidden(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_1247])).

cnf(c_18535,plain,
    ( X0 = X1
    | k1_wellord1(k1_wellord2(X0),X1) = X1
    | k1_wellord1(k1_wellord2(X1),X0) = X0
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2722,c_1247])).

cnf(c_25095,plain,
    ( k1_wellord1(k1_wellord2(X0),sK5) = sK5
    | k1_wellord1(k1_wellord2(sK5),X0) = X0
    | sK5 = X0
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1244,c_18535])).

cnf(c_25311,plain,
    ( k1_wellord1(k1_wellord2(sK5),sK4) = sK4
    | k1_wellord1(k1_wellord2(sK4),sK5) = sK5
    | sK5 = sK4 ),
    inference(superposition,[status(thm)],[c_1243,c_25095])).

cnf(c_25329,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK5) = sK5
    | k1_wellord1(k1_wellord2(sK5),sK4) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_25311,c_24,c_818,c_1513])).

cnf(c_25330,plain,
    ( k1_wellord1(k1_wellord2(sK5),sK4) = sK4
    | k1_wellord1(k1_wellord2(sK4),sK5) = sK5 ),
    inference(renaming,[status(thm)],[c_25329])).

cnf(c_12,plain,
    ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
    | ~ r2_hidden(X1,k3_relat_1(X0))
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_22,plain,
    ( v2_wellord1(k1_wellord2(X0))
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_306,plain,
    ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
    | ~ r2_hidden(X1,k3_relat_1(X0))
    | ~ v3_ordinal1(X2)
    | ~ v1_relat_1(X0)
    | k1_wellord2(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_307,plain,
    ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
    | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
    | ~ v3_ordinal1(X0)
    | ~ v1_relat_1(k1_wellord2(X0)) ),
    inference(unflattening,[status(thm)],[c_306])).

cnf(c_311,plain,
    ( ~ v3_ordinal1(X0)
    | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
    | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_307,c_20])).

cnf(c_312,plain,
    ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
    | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
    | ~ v3_ordinal1(X0) ),
    inference(renaming,[status(thm)],[c_311])).

cnf(c_1242,plain,
    ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
    | r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_312])).

cnf(c_1359,plain,
    ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1242,c_159])).

cnf(c_25339,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK5) = sK5
    | r4_wellord1(k1_wellord2(sK5),k2_wellord1(k1_wellord2(sK5),sK4)) != iProver_top
    | r2_hidden(sK4,sK5) != iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_25330,c_1359])).

cnf(c_28,plain,
    ( v3_ordinal1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1690,plain,
    ( r2_hidden(sK5,sK4)
    | r2_hidden(sK4,sK5)
    | ~ v3_ordinal1(sK5)
    | ~ v3_ordinal1(sK4)
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1691,plain,
    ( sK4 = sK5
    | r2_hidden(sK5,sK4) = iProver_top
    | r2_hidden(sK4,sK5) = iProver_top
    | v3_ordinal1(sK5) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1690])).

cnf(c_1792,plain,
    ( ~ r2_hidden(sK5,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK5)
    | k1_wellord1(k1_wellord2(X0),sK5) = sK5 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1794,plain,
    ( k1_wellord1(k1_wellord2(X0),sK5) = sK5
    | r2_hidden(sK5,X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1792])).

cnf(c_1796,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK5) = sK5
    | r2_hidden(sK5,sK4) != iProver_top
    | v3_ordinal1(sK5) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1794])).

cnf(c_25515,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK5) = sK5
    | r4_wellord1(k1_wellord2(sK5),k2_wellord1(k1_wellord2(sK5),sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25339,c_28,c_29,c_24,c_1691,c_1796])).

cnf(c_34547,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK5) = sK5
    | r4_wellord1(k1_wellord2(sK5),k1_wellord2(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_34544,c_25515])).

cnf(c_25,negated_conjecture,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK5)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1245,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_11,plain,
    ( ~ r4_wellord1(X0,X1)
    | r4_wellord1(X1,X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1255,plain,
    ( r4_wellord1(X0,X1) != iProver_top
    | r4_wellord1(X1,X0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2081,plain,
    ( r4_wellord1(k1_wellord2(sK5),k1_wellord2(sK4)) = iProver_top
    | v1_relat_1(k1_wellord2(sK5)) != iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1245,c_1255])).

cnf(c_30,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_40,plain,
    ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_42,plain,
    ( v1_relat_1(k1_wellord2(sK4)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_1497,plain,
    ( r4_wellord1(X0,k1_wellord2(X1))
    | ~ r4_wellord1(k1_wellord2(X1),X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(k1_wellord2(X1)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1675,plain,
    ( ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
    | r4_wellord1(k1_wellord2(X1),k1_wellord2(X0))
    | ~ v1_relat_1(k1_wellord2(X1))
    | ~ v1_relat_1(k1_wellord2(X0)) ),
    inference(instantiation,[status(thm)],[c_1497])).

cnf(c_2047,plain,
    ( r4_wellord1(k1_wellord2(sK5),k1_wellord2(sK4))
    | ~ r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK5))
    | ~ v1_relat_1(k1_wellord2(sK5))
    | ~ v1_relat_1(k1_wellord2(sK4)) ),
    inference(instantiation,[status(thm)],[c_1675])).

cnf(c_2048,plain,
    ( r4_wellord1(k1_wellord2(sK5),k1_wellord2(sK4)) = iProver_top
    | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK5)) != iProver_top
    | v1_relat_1(k1_wellord2(sK5)) != iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2047])).

cnf(c_2223,plain,
    ( v1_relat_1(k1_wellord2(sK5)) != iProver_top
    | r4_wellord1(k1_wellord2(sK5),k1_wellord2(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2081,c_30,c_42,c_2048])).

cnf(c_2224,plain,
    ( r4_wellord1(k1_wellord2(sK5),k1_wellord2(sK4)) = iProver_top
    | v1_relat_1(k1_wellord2(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2223])).

cnf(c_2229,plain,
    ( r4_wellord1(k1_wellord2(sK5),k1_wellord2(sK4)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2224,c_1248])).

cnf(c_34762,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK5) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_34547,c_2229])).

cnf(c_34776,plain,
    ( r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK5)) != iProver_top
    | r2_hidden(sK5,sK4) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_34762,c_1359])).

cnf(c_2394,plain,
    ( k1_wellord1(k1_wellord2(sK0(sK4)),sK4) = sK4 ),
    inference(superposition,[status(thm)],[c_1243,c_2385])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X0))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1256,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2533,plain,
    ( r2_hidden(sK4,sK4) != iProver_top
    | v1_relat_1(k1_wellord2(sK0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2394,c_1256])).

cnf(c_3085,plain,
    ( r2_hidden(sK4,sK4) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2533,c_1248])).

cnf(c_34774,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(X0,sK5),k1_wellord2(sK4)) = iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_34762,c_1257])).

cnf(c_35589,plain,
    ( r2_hidden(k4_tarski(X0,sK5),k1_wellord2(sK4)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_34774,c_42])).

cnf(c_35590,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(X0,sK5),k1_wellord2(sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_35589])).

cnf(c_35598,plain,
    ( r2_hidden(X0,k3_relat_1(k1_wellord2(sK4))) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_35590,c_1265])).

cnf(c_35630,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_35598,c_159])).

cnf(c_35648,plain,
    ( r2_hidden(sK4,sK5) != iProver_top
    | r2_hidden(sK4,sK4) = iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_35630])).

cnf(c_48682,plain,
    ( r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_34776,c_28,c_29,c_24,c_42,c_1691,c_3085,c_35648])).

cnf(c_2532,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k4_tarski(X0,sK4),k1_wellord2(sK0(sK4))) = iProver_top
    | v1_relat_1(k1_wellord2(sK0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2394,c_1257])).

cnf(c_3215,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k4_tarski(X0,sK4),k1_wellord2(sK0(sK4))) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2532,c_1248])).

cnf(c_5828,plain,
    ( r1_tarski(X0,sK4) = iProver_top
    | r2_hidden(X0,sK0(sK4)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(sK4,sK0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3215,c_1387])).

cnf(c_87,plain,
    ( r2_hidden(X0,sK0(X0)) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_89,plain,
    ( r2_hidden(sK4,sK0(sK4)) = iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_87])).

cnf(c_3218,plain,
    ( r2_hidden(X0,k3_relat_1(k1_wellord2(sK0(sK4)))) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | v1_relat_1(k1_wellord2(sK0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3215,c_1265])).

cnf(c_3237,plain,
    ( r2_hidden(X0,sK0(sK4)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | v1_relat_1(k1_wellord2(sK0(sK4))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3218,c_159])).

cnf(c_6352,plain,
    ( r2_hidden(X0,sK0(sK4)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3237,c_1248])).

cnf(c_7106,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r1_tarski(X0,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5828,c_28,c_89,c_6352])).

cnf(c_7107,plain,
    ( r1_tarski(X0,sK4) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_7106])).

cnf(c_7112,plain,
    ( sK4 = X0
    | r1_tarski(X0,sK4) = iProver_top
    | r2_hidden(sK4,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_7107])).

cnf(c_17020,plain,
    ( v3_ordinal1(X0) != iProver_top
    | r2_hidden(sK4,X0) = iProver_top
    | r1_tarski(X0,sK4) = iProver_top
    | sK4 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7112,c_28])).

cnf(c_17021,plain,
    ( sK4 = X0
    | r1_tarski(X0,sK4) = iProver_top
    | r2_hidden(sK4,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_17020])).

cnf(c_17028,plain,
    ( k2_wellord1(k1_wellord2(sK4),X0) = k1_wellord2(X0)
    | sK4 = X0
    | r2_hidden(sK4,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17021,c_1246])).

cnf(c_17035,plain,
    ( k2_wellord1(k1_wellord2(sK4),X0) = k1_wellord2(X0)
    | k1_wellord1(k1_wellord2(X0),sK4) = sK4
    | sK4 = X0
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_17028,c_1247])).

cnf(c_44984,plain,
    ( v3_ordinal1(X0) != iProver_top
    | sK4 = X0
    | k1_wellord1(k1_wellord2(X0),sK4) = sK4
    | k2_wellord1(k1_wellord2(sK4),X0) = k1_wellord2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17035,c_28])).

cnf(c_44985,plain,
    ( k2_wellord1(k1_wellord2(sK4),X0) = k1_wellord2(X0)
    | k1_wellord1(k1_wellord2(X0),sK4) = sK4
    | sK4 = X0
    | v3_ordinal1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_44984])).

cnf(c_44993,plain,
    ( k2_wellord1(k1_wellord2(sK4),sK5) = k1_wellord2(sK5)
    | k1_wellord1(k1_wellord2(sK5),sK4) = sK4
    | sK5 = sK4 ),
    inference(superposition,[status(thm)],[c_1244,c_44985])).

cnf(c_35782,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_35630,c_42])).

cnf(c_35783,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_35782])).

cnf(c_35809,plain,
    ( k2_wellord1(k1_wellord2(sK4),sK5) = k1_wellord2(sK5)
    | sK5 = sK4
    | r2_hidden(sK4,sK4) = iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_17028,c_35783])).

cnf(c_45010,plain,
    ( k2_wellord1(k1_wellord2(sK4),sK5) = k1_wellord2(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_44993,c_29,c_24,c_818,c_1513,c_3085,c_35809])).

cnf(c_48686,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_48682,c_45010])).

cnf(c_48688,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_48686,c_1245])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:41:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.79/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.79/1.99  
% 11.79/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.79/1.99  
% 11.79/1.99  ------  iProver source info
% 11.79/1.99  
% 11.79/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.79/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.79/1.99  git: non_committed_changes: false
% 11.79/1.99  git: last_make_outside_of_git: false
% 11.79/1.99  
% 11.79/1.99  ------ 
% 11.79/1.99  
% 11.79/1.99  ------ Input Options
% 11.79/1.99  
% 11.79/1.99  --out_options                           all
% 11.79/1.99  --tptp_safe_out                         true
% 11.79/1.99  --problem_path                          ""
% 11.79/1.99  --include_path                          ""
% 11.79/1.99  --clausifier                            res/vclausify_rel
% 11.79/1.99  --clausifier_options                    --mode clausify
% 11.79/1.99  --stdin                                 false
% 11.79/1.99  --stats_out                             all
% 11.79/1.99  
% 11.79/1.99  ------ General Options
% 11.79/1.99  
% 11.79/1.99  --fof                                   false
% 11.79/1.99  --time_out_real                         305.
% 11.79/1.99  --time_out_virtual                      -1.
% 11.79/1.99  --symbol_type_check                     false
% 11.79/1.99  --clausify_out                          false
% 11.79/1.99  --sig_cnt_out                           false
% 11.79/1.99  --trig_cnt_out                          false
% 11.79/1.99  --trig_cnt_out_tolerance                1.
% 11.79/1.99  --trig_cnt_out_sk_spl                   false
% 11.79/1.99  --abstr_cl_out                          false
% 11.79/1.99  
% 11.79/1.99  ------ Global Options
% 11.79/1.99  
% 11.79/1.99  --schedule                              default
% 11.79/1.99  --add_important_lit                     false
% 11.79/1.99  --prop_solver_per_cl                    1000
% 11.79/1.99  --min_unsat_core                        false
% 11.79/1.99  --soft_assumptions                      false
% 11.79/1.99  --soft_lemma_size                       3
% 11.79/1.99  --prop_impl_unit_size                   0
% 11.79/1.99  --prop_impl_unit                        []
% 11.79/1.99  --share_sel_clauses                     true
% 11.79/1.99  --reset_solvers                         false
% 11.79/1.99  --bc_imp_inh                            [conj_cone]
% 11.79/1.99  --conj_cone_tolerance                   3.
% 11.79/1.99  --extra_neg_conj                        none
% 11.79/1.99  --large_theory_mode                     true
% 11.79/1.99  --prolific_symb_bound                   200
% 11.79/1.99  --lt_threshold                          2000
% 11.79/1.99  --clause_weak_htbl                      true
% 11.79/1.99  --gc_record_bc_elim                     false
% 11.79/1.99  
% 11.79/1.99  ------ Preprocessing Options
% 11.79/1.99  
% 11.79/1.99  --preprocessing_flag                    true
% 11.79/1.99  --time_out_prep_mult                    0.1
% 11.79/1.99  --splitting_mode                        input
% 11.79/1.99  --splitting_grd                         true
% 11.79/1.99  --splitting_cvd                         false
% 11.79/1.99  --splitting_cvd_svl                     false
% 11.79/1.99  --splitting_nvd                         32
% 11.79/1.99  --sub_typing                            true
% 11.79/1.99  --prep_gs_sim                           true
% 11.79/1.99  --prep_unflatten                        true
% 11.79/1.99  --prep_res_sim                          true
% 11.79/1.99  --prep_upred                            true
% 11.79/1.99  --prep_sem_filter                       exhaustive
% 11.79/1.99  --prep_sem_filter_out                   false
% 11.79/1.99  --pred_elim                             true
% 11.79/1.99  --res_sim_input                         true
% 11.79/1.99  --eq_ax_congr_red                       true
% 11.79/1.99  --pure_diseq_elim                       true
% 11.79/1.99  --brand_transform                       false
% 11.79/1.99  --non_eq_to_eq                          false
% 11.79/1.99  --prep_def_merge                        true
% 11.79/1.99  --prep_def_merge_prop_impl              false
% 11.79/1.99  --prep_def_merge_mbd                    true
% 11.79/1.99  --prep_def_merge_tr_red                 false
% 11.79/1.99  --prep_def_merge_tr_cl                  false
% 11.79/1.99  --smt_preprocessing                     true
% 11.79/1.99  --smt_ac_axioms                         fast
% 11.79/1.99  --preprocessed_out                      false
% 11.79/1.99  --preprocessed_stats                    false
% 11.79/1.99  
% 11.79/1.99  ------ Abstraction refinement Options
% 11.79/1.99  
% 11.79/1.99  --abstr_ref                             []
% 11.79/1.99  --abstr_ref_prep                        false
% 11.79/1.99  --abstr_ref_until_sat                   false
% 11.79/1.99  --abstr_ref_sig_restrict                funpre
% 11.79/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.79/1.99  --abstr_ref_under                       []
% 11.79/1.99  
% 11.79/1.99  ------ SAT Options
% 11.79/1.99  
% 11.79/1.99  --sat_mode                              false
% 11.79/1.99  --sat_fm_restart_options                ""
% 11.79/1.99  --sat_gr_def                            false
% 11.79/1.99  --sat_epr_types                         true
% 11.79/1.99  --sat_non_cyclic_types                  false
% 11.79/1.99  --sat_finite_models                     false
% 11.79/1.99  --sat_fm_lemmas                         false
% 11.79/1.99  --sat_fm_prep                           false
% 11.79/1.99  --sat_fm_uc_incr                        true
% 11.79/1.99  --sat_out_model                         small
% 11.79/1.99  --sat_out_clauses                       false
% 11.79/1.99  
% 11.79/1.99  ------ QBF Options
% 11.79/1.99  
% 11.79/1.99  --qbf_mode                              false
% 11.79/1.99  --qbf_elim_univ                         false
% 11.79/1.99  --qbf_dom_inst                          none
% 11.79/1.99  --qbf_dom_pre_inst                      false
% 11.79/1.99  --qbf_sk_in                             false
% 11.79/1.99  --qbf_pred_elim                         true
% 11.79/1.99  --qbf_split                             512
% 11.79/1.99  
% 11.79/1.99  ------ BMC1 Options
% 11.79/1.99  
% 11.79/1.99  --bmc1_incremental                      false
% 11.79/1.99  --bmc1_axioms                           reachable_all
% 11.79/1.99  --bmc1_min_bound                        0
% 11.79/1.99  --bmc1_max_bound                        -1
% 11.79/1.99  --bmc1_max_bound_default                -1
% 11.79/1.99  --bmc1_symbol_reachability              true
% 11.79/1.99  --bmc1_property_lemmas                  false
% 11.79/1.99  --bmc1_k_induction                      false
% 11.79/1.99  --bmc1_non_equiv_states                 false
% 11.79/1.99  --bmc1_deadlock                         false
% 11.79/1.99  --bmc1_ucm                              false
% 11.79/1.99  --bmc1_add_unsat_core                   none
% 11.79/1.99  --bmc1_unsat_core_children              false
% 11.79/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.79/1.99  --bmc1_out_stat                         full
% 11.79/1.99  --bmc1_ground_init                      false
% 11.79/1.99  --bmc1_pre_inst_next_state              false
% 11.79/1.99  --bmc1_pre_inst_state                   false
% 11.79/1.99  --bmc1_pre_inst_reach_state             false
% 11.79/1.99  --bmc1_out_unsat_core                   false
% 11.79/1.99  --bmc1_aig_witness_out                  false
% 11.79/1.99  --bmc1_verbose                          false
% 11.79/1.99  --bmc1_dump_clauses_tptp                false
% 11.79/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.79/1.99  --bmc1_dump_file                        -
% 11.79/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.79/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.79/1.99  --bmc1_ucm_extend_mode                  1
% 11.79/1.99  --bmc1_ucm_init_mode                    2
% 11.79/1.99  --bmc1_ucm_cone_mode                    none
% 11.79/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.79/1.99  --bmc1_ucm_relax_model                  4
% 11.79/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.79/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.79/1.99  --bmc1_ucm_layered_model                none
% 11.79/1.99  --bmc1_ucm_max_lemma_size               10
% 11.79/1.99  
% 11.79/1.99  ------ AIG Options
% 11.79/1.99  
% 11.79/1.99  --aig_mode                              false
% 11.79/1.99  
% 11.79/1.99  ------ Instantiation Options
% 11.79/1.99  
% 11.79/1.99  --instantiation_flag                    true
% 11.79/1.99  --inst_sos_flag                         false
% 11.79/1.99  --inst_sos_phase                        true
% 11.79/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.79/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.79/1.99  --inst_lit_sel_side                     num_symb
% 11.79/1.99  --inst_solver_per_active                1400
% 11.79/1.99  --inst_solver_calls_frac                1.
% 11.79/1.99  --inst_passive_queue_type               priority_queues
% 11.79/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.79/1.99  --inst_passive_queues_freq              [25;2]
% 11.79/1.99  --inst_dismatching                      true
% 11.79/1.99  --inst_eager_unprocessed_to_passive     true
% 11.79/1.99  --inst_prop_sim_given                   true
% 11.79/1.99  --inst_prop_sim_new                     false
% 11.79/1.99  --inst_subs_new                         false
% 11.79/1.99  --inst_eq_res_simp                      false
% 11.79/1.99  --inst_subs_given                       false
% 11.79/1.99  --inst_orphan_elimination               true
% 11.79/1.99  --inst_learning_loop_flag               true
% 11.79/1.99  --inst_learning_start                   3000
% 11.79/1.99  --inst_learning_factor                  2
% 11.79/1.99  --inst_start_prop_sim_after_learn       3
% 11.79/1.99  --inst_sel_renew                        solver
% 11.79/1.99  --inst_lit_activity_flag                true
% 11.79/1.99  --inst_restr_to_given                   false
% 11.79/1.99  --inst_activity_threshold               500
% 11.79/1.99  --inst_out_proof                        true
% 11.79/1.99  
% 11.79/1.99  ------ Resolution Options
% 11.79/1.99  
% 11.79/1.99  --resolution_flag                       true
% 11.79/1.99  --res_lit_sel                           adaptive
% 11.79/1.99  --res_lit_sel_side                      none
% 11.79/1.99  --res_ordering                          kbo
% 11.79/1.99  --res_to_prop_solver                    active
% 11.79/1.99  --res_prop_simpl_new                    false
% 11.79/1.99  --res_prop_simpl_given                  true
% 11.79/1.99  --res_passive_queue_type                priority_queues
% 11.79/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.79/1.99  --res_passive_queues_freq               [15;5]
% 11.79/1.99  --res_forward_subs                      full
% 11.79/1.99  --res_backward_subs                     full
% 11.79/1.99  --res_forward_subs_resolution           true
% 11.79/1.99  --res_backward_subs_resolution          true
% 11.79/1.99  --res_orphan_elimination                true
% 11.79/1.99  --res_time_limit                        2.
% 11.79/1.99  --res_out_proof                         true
% 11.79/1.99  
% 11.79/1.99  ------ Superposition Options
% 11.79/1.99  
% 11.79/1.99  --superposition_flag                    true
% 11.79/1.99  --sup_passive_queue_type                priority_queues
% 11.79/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.79/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.79/1.99  --demod_completeness_check              fast
% 11.79/1.99  --demod_use_ground                      true
% 11.79/1.99  --sup_to_prop_solver                    passive
% 11.79/1.99  --sup_prop_simpl_new                    true
% 11.79/1.99  --sup_prop_simpl_given                  true
% 11.79/1.99  --sup_fun_splitting                     false
% 11.79/1.99  --sup_smt_interval                      50000
% 11.79/1.99  
% 11.79/1.99  ------ Superposition Simplification Setup
% 11.79/1.99  
% 11.79/1.99  --sup_indices_passive                   []
% 11.79/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.79/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.79/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.79/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.79/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.79/1.99  --sup_full_bw                           [BwDemod]
% 11.79/1.99  --sup_immed_triv                        [TrivRules]
% 11.79/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.79/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.79/1.99  --sup_immed_bw_main                     []
% 11.79/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.79/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.79/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.79/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.79/1.99  
% 11.79/1.99  ------ Combination Options
% 11.79/1.99  
% 11.79/1.99  --comb_res_mult                         3
% 11.79/1.99  --comb_sup_mult                         2
% 11.79/1.99  --comb_inst_mult                        10
% 11.79/1.99  
% 11.79/1.99  ------ Debug Options
% 11.79/1.99  
% 11.79/1.99  --dbg_backtrace                         false
% 11.79/1.99  --dbg_dump_prop_clauses                 false
% 11.79/1.99  --dbg_dump_prop_clauses_file            -
% 11.79/1.99  --dbg_out_stat                          false
% 11.79/1.99  ------ Parsing...
% 11.79/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.79/1.99  
% 11.79/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.79/1.99  
% 11.79/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.79/1.99  
% 11.79/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.79/1.99  ------ Proving...
% 11.79/1.99  ------ Problem Properties 
% 11.79/1.99  
% 11.79/1.99  
% 11.79/1.99  clauses                                 27
% 11.79/1.99  conjectures                             4
% 11.79/1.99  EPR                                     5
% 11.79/1.99  Horn                                    19
% 11.79/1.99  unary                                   6
% 11.79/1.99  binary                                  4
% 11.79/1.99  lits                                    80
% 11.79/1.99  lits eq                                 15
% 11.79/1.99  fd_pure                                 0
% 11.79/1.99  fd_pseudo                               0
% 11.79/1.99  fd_cond                                 0
% 11.79/1.99  fd_pseudo_cond                          4
% 11.79/1.99  AC symbols                              0
% 11.79/1.99  
% 11.79/1.99  ------ Schedule dynamic 5 is on 
% 11.79/1.99  
% 11.79/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.79/1.99  
% 11.79/1.99  
% 11.79/1.99  ------ 
% 11.79/1.99  Current options:
% 11.79/1.99  ------ 
% 11.79/1.99  
% 11.79/1.99  ------ Input Options
% 11.79/1.99  
% 11.79/1.99  --out_options                           all
% 11.79/1.99  --tptp_safe_out                         true
% 11.79/1.99  --problem_path                          ""
% 11.79/1.99  --include_path                          ""
% 11.79/1.99  --clausifier                            res/vclausify_rel
% 11.79/1.99  --clausifier_options                    --mode clausify
% 11.79/1.99  --stdin                                 false
% 11.79/1.99  --stats_out                             all
% 11.79/1.99  
% 11.79/2.00  ------ General Options
% 11.79/2.00  
% 11.79/2.00  --fof                                   false
% 11.79/2.00  --time_out_real                         305.
% 11.79/2.00  --time_out_virtual                      -1.
% 11.79/2.00  --symbol_type_check                     false
% 11.79/2.00  --clausify_out                          false
% 11.79/2.00  --sig_cnt_out                           false
% 11.79/2.00  --trig_cnt_out                          false
% 11.79/2.00  --trig_cnt_out_tolerance                1.
% 11.79/2.00  --trig_cnt_out_sk_spl                   false
% 11.79/2.00  --abstr_cl_out                          false
% 11.79/2.00  
% 11.79/2.00  ------ Global Options
% 11.79/2.00  
% 11.79/2.00  --schedule                              default
% 11.79/2.00  --add_important_lit                     false
% 11.79/2.00  --prop_solver_per_cl                    1000
% 11.79/2.00  --min_unsat_core                        false
% 11.79/2.00  --soft_assumptions                      false
% 11.79/2.00  --soft_lemma_size                       3
% 11.79/2.00  --prop_impl_unit_size                   0
% 11.79/2.00  --prop_impl_unit                        []
% 11.79/2.00  --share_sel_clauses                     true
% 11.79/2.00  --reset_solvers                         false
% 11.79/2.00  --bc_imp_inh                            [conj_cone]
% 11.79/2.00  --conj_cone_tolerance                   3.
% 11.79/2.00  --extra_neg_conj                        none
% 11.79/2.00  --large_theory_mode                     true
% 11.79/2.00  --prolific_symb_bound                   200
% 11.79/2.00  --lt_threshold                          2000
% 11.79/2.00  --clause_weak_htbl                      true
% 11.79/2.00  --gc_record_bc_elim                     false
% 11.79/2.00  
% 11.79/2.00  ------ Preprocessing Options
% 11.79/2.00  
% 11.79/2.00  --preprocessing_flag                    true
% 11.79/2.00  --time_out_prep_mult                    0.1
% 11.79/2.00  --splitting_mode                        input
% 11.79/2.00  --splitting_grd                         true
% 11.79/2.00  --splitting_cvd                         false
% 11.79/2.00  --splitting_cvd_svl                     false
% 11.79/2.00  --splitting_nvd                         32
% 11.79/2.00  --sub_typing                            true
% 11.79/2.00  --prep_gs_sim                           true
% 11.79/2.00  --prep_unflatten                        true
% 11.79/2.00  --prep_res_sim                          true
% 11.79/2.00  --prep_upred                            true
% 11.79/2.00  --prep_sem_filter                       exhaustive
% 11.79/2.00  --prep_sem_filter_out                   false
% 11.79/2.00  --pred_elim                             true
% 11.79/2.00  --res_sim_input                         true
% 11.79/2.00  --eq_ax_congr_red                       true
% 11.79/2.00  --pure_diseq_elim                       true
% 11.79/2.00  --brand_transform                       false
% 11.79/2.00  --non_eq_to_eq                          false
% 11.79/2.00  --prep_def_merge                        true
% 11.79/2.00  --prep_def_merge_prop_impl              false
% 11.79/2.00  --prep_def_merge_mbd                    true
% 11.79/2.00  --prep_def_merge_tr_red                 false
% 11.79/2.00  --prep_def_merge_tr_cl                  false
% 11.79/2.00  --smt_preprocessing                     true
% 11.79/2.00  --smt_ac_axioms                         fast
% 11.79/2.00  --preprocessed_out                      false
% 11.79/2.00  --preprocessed_stats                    false
% 11.79/2.00  
% 11.79/2.00  ------ Abstraction refinement Options
% 11.79/2.00  
% 11.79/2.00  --abstr_ref                             []
% 11.79/2.00  --abstr_ref_prep                        false
% 11.79/2.00  --abstr_ref_until_sat                   false
% 11.79/2.00  --abstr_ref_sig_restrict                funpre
% 11.79/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.79/2.00  --abstr_ref_under                       []
% 11.79/2.00  
% 11.79/2.00  ------ SAT Options
% 11.79/2.00  
% 11.79/2.00  --sat_mode                              false
% 11.79/2.00  --sat_fm_restart_options                ""
% 11.79/2.00  --sat_gr_def                            false
% 11.79/2.00  --sat_epr_types                         true
% 11.79/2.00  --sat_non_cyclic_types                  false
% 11.79/2.00  --sat_finite_models                     false
% 11.79/2.00  --sat_fm_lemmas                         false
% 11.79/2.00  --sat_fm_prep                           false
% 11.79/2.00  --sat_fm_uc_incr                        true
% 11.79/2.00  --sat_out_model                         small
% 11.79/2.00  --sat_out_clauses                       false
% 11.79/2.00  
% 11.79/2.00  ------ QBF Options
% 11.79/2.00  
% 11.79/2.00  --qbf_mode                              false
% 11.79/2.00  --qbf_elim_univ                         false
% 11.79/2.00  --qbf_dom_inst                          none
% 11.79/2.00  --qbf_dom_pre_inst                      false
% 11.79/2.00  --qbf_sk_in                             false
% 11.79/2.00  --qbf_pred_elim                         true
% 11.79/2.00  --qbf_split                             512
% 11.79/2.00  
% 11.79/2.00  ------ BMC1 Options
% 11.79/2.00  
% 11.79/2.00  --bmc1_incremental                      false
% 11.79/2.00  --bmc1_axioms                           reachable_all
% 11.79/2.00  --bmc1_min_bound                        0
% 11.79/2.00  --bmc1_max_bound                        -1
% 11.79/2.00  --bmc1_max_bound_default                -1
% 11.79/2.00  --bmc1_symbol_reachability              true
% 11.79/2.00  --bmc1_property_lemmas                  false
% 11.79/2.00  --bmc1_k_induction                      false
% 11.79/2.00  --bmc1_non_equiv_states                 false
% 11.79/2.00  --bmc1_deadlock                         false
% 11.79/2.00  --bmc1_ucm                              false
% 11.79/2.00  --bmc1_add_unsat_core                   none
% 11.79/2.00  --bmc1_unsat_core_children              false
% 11.79/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.79/2.00  --bmc1_out_stat                         full
% 11.79/2.00  --bmc1_ground_init                      false
% 11.79/2.00  --bmc1_pre_inst_next_state              false
% 11.79/2.00  --bmc1_pre_inst_state                   false
% 11.79/2.00  --bmc1_pre_inst_reach_state             false
% 11.79/2.00  --bmc1_out_unsat_core                   false
% 11.79/2.00  --bmc1_aig_witness_out                  false
% 11.79/2.00  --bmc1_verbose                          false
% 11.79/2.00  --bmc1_dump_clauses_tptp                false
% 11.79/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.79/2.00  --bmc1_dump_file                        -
% 11.79/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.79/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.79/2.00  --bmc1_ucm_extend_mode                  1
% 11.79/2.00  --bmc1_ucm_init_mode                    2
% 11.79/2.00  --bmc1_ucm_cone_mode                    none
% 11.79/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.79/2.00  --bmc1_ucm_relax_model                  4
% 11.79/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.79/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.79/2.00  --bmc1_ucm_layered_model                none
% 11.79/2.00  --bmc1_ucm_max_lemma_size               10
% 11.79/2.00  
% 11.79/2.00  ------ AIG Options
% 11.79/2.00  
% 11.79/2.00  --aig_mode                              false
% 11.79/2.00  
% 11.79/2.00  ------ Instantiation Options
% 11.79/2.00  
% 11.79/2.00  --instantiation_flag                    true
% 11.79/2.00  --inst_sos_flag                         false
% 11.79/2.00  --inst_sos_phase                        true
% 11.79/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.79/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.79/2.00  --inst_lit_sel_side                     none
% 11.79/2.00  --inst_solver_per_active                1400
% 11.79/2.00  --inst_solver_calls_frac                1.
% 11.79/2.00  --inst_passive_queue_type               priority_queues
% 11.79/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.79/2.00  --inst_passive_queues_freq              [25;2]
% 11.79/2.00  --inst_dismatching                      true
% 11.79/2.00  --inst_eager_unprocessed_to_passive     true
% 11.79/2.00  --inst_prop_sim_given                   true
% 11.79/2.00  --inst_prop_sim_new                     false
% 11.79/2.00  --inst_subs_new                         false
% 11.79/2.00  --inst_eq_res_simp                      false
% 11.79/2.00  --inst_subs_given                       false
% 11.79/2.00  --inst_orphan_elimination               true
% 11.79/2.00  --inst_learning_loop_flag               true
% 11.79/2.00  --inst_learning_start                   3000
% 11.79/2.00  --inst_learning_factor                  2
% 11.79/2.00  --inst_start_prop_sim_after_learn       3
% 11.79/2.00  --inst_sel_renew                        solver
% 11.79/2.00  --inst_lit_activity_flag                true
% 11.79/2.00  --inst_restr_to_given                   false
% 11.79/2.00  --inst_activity_threshold               500
% 11.79/2.00  --inst_out_proof                        true
% 11.79/2.00  
% 11.79/2.00  ------ Resolution Options
% 11.79/2.00  
% 11.79/2.00  --resolution_flag                       false
% 11.79/2.00  --res_lit_sel                           adaptive
% 11.79/2.00  --res_lit_sel_side                      none
% 11.79/2.00  --res_ordering                          kbo
% 11.79/2.00  --res_to_prop_solver                    active
% 11.79/2.00  --res_prop_simpl_new                    false
% 11.79/2.00  --res_prop_simpl_given                  true
% 11.79/2.00  --res_passive_queue_type                priority_queues
% 11.79/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.79/2.00  --res_passive_queues_freq               [15;5]
% 11.79/2.00  --res_forward_subs                      full
% 11.79/2.00  --res_backward_subs                     full
% 11.79/2.00  --res_forward_subs_resolution           true
% 11.79/2.00  --res_backward_subs_resolution          true
% 11.79/2.00  --res_orphan_elimination                true
% 11.79/2.00  --res_time_limit                        2.
% 11.79/2.00  --res_out_proof                         true
% 11.79/2.00  
% 11.79/2.00  ------ Superposition Options
% 11.79/2.00  
% 11.79/2.00  --superposition_flag                    true
% 11.79/2.00  --sup_passive_queue_type                priority_queues
% 11.79/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.79/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.79/2.00  --demod_completeness_check              fast
% 11.79/2.00  --demod_use_ground                      true
% 11.79/2.00  --sup_to_prop_solver                    passive
% 11.79/2.00  --sup_prop_simpl_new                    true
% 11.79/2.00  --sup_prop_simpl_given                  true
% 11.79/2.00  --sup_fun_splitting                     false
% 11.79/2.00  --sup_smt_interval                      50000
% 11.79/2.00  
% 11.79/2.00  ------ Superposition Simplification Setup
% 11.79/2.00  
% 11.79/2.00  --sup_indices_passive                   []
% 11.79/2.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.79/2.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.79/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.79/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.79/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.79/2.00  --sup_full_bw                           [BwDemod]
% 11.79/2.00  --sup_immed_triv                        [TrivRules]
% 11.79/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.79/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.79/2.00  --sup_immed_bw_main                     []
% 11.79/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.79/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.79/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.79/2.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.79/2.00  
% 11.79/2.00  ------ Combination Options
% 11.79/2.00  
% 11.79/2.00  --comb_res_mult                         3
% 11.79/2.00  --comb_sup_mult                         2
% 11.79/2.00  --comb_inst_mult                        10
% 11.79/2.00  
% 11.79/2.00  ------ Debug Options
% 11.79/2.00  
% 11.79/2.00  --dbg_backtrace                         false
% 11.79/2.00  --dbg_dump_prop_clauses                 false
% 11.79/2.00  --dbg_dump_prop_clauses_file            -
% 11.79/2.00  --dbg_out_stat                          false
% 11.79/2.00  
% 11.79/2.00  
% 11.79/2.00  
% 11.79/2.00  
% 11.79/2.00  ------ Proving...
% 11.79/2.00  
% 11.79/2.00  
% 11.79/2.00  % SZS status Theorem for theBenchmark.p
% 11.79/2.00  
% 11.79/2.00   Resolution empty clause
% 11.79/2.00  
% 11.79/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.79/2.00  
% 11.79/2.00  fof(f12,conjecture,(
% 11.79/2.00    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 11.79/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.79/2.00  
% 11.79/2.00  fof(f13,negated_conjecture,(
% 11.79/2.00    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 11.79/2.00    inference(negated_conjecture,[],[f12])).
% 11.79/2.00  
% 11.79/2.00  fof(f31,plain,(
% 11.79/2.00    ? [X0] : (? [X1] : ((X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 11.79/2.00    inference(ennf_transformation,[],[f13])).
% 11.79/2.00  
% 11.79/2.00  fof(f32,plain,(
% 11.79/2.00    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 11.79/2.00    inference(flattening,[],[f31])).
% 11.79/2.00  
% 11.79/2.00  fof(f46,plain,(
% 11.79/2.00    ( ! [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) => (sK5 != X0 & r4_wellord1(k1_wellord2(X0),k1_wellord2(sK5)) & v3_ordinal1(sK5))) )),
% 11.79/2.00    introduced(choice_axiom,[])).
% 11.79/2.00  
% 11.79/2.00  fof(f45,plain,(
% 11.79/2.00    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : (sK4 != X1 & r4_wellord1(k1_wellord2(sK4),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK4))),
% 11.79/2.00    introduced(choice_axiom,[])).
% 11.79/2.00  
% 11.79/2.00  fof(f47,plain,(
% 11.79/2.00    (sK4 != sK5 & r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK5)) & v3_ordinal1(sK5)) & v3_ordinal1(sK4)),
% 11.79/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f32,f46,f45])).
% 11.79/2.00  
% 11.79/2.00  fof(f72,plain,(
% 11.79/2.00    v3_ordinal1(sK4)),
% 11.79/2.00    inference(cnf_transformation,[],[f47])).
% 11.79/2.00  
% 11.79/2.00  fof(f2,axiom,(
% 11.79/2.00    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 11.79/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.79/2.00  
% 11.79/2.00  fof(f17,plain,(
% 11.79/2.00    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 11.79/2.00    inference(ennf_transformation,[],[f2])).
% 11.79/2.00  
% 11.79/2.00  fof(f18,plain,(
% 11.79/2.00    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 11.79/2.00    inference(flattening,[],[f17])).
% 11.79/2.00  
% 11.79/2.00  fof(f50,plain,(
% 11.79/2.00    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 11.79/2.00    inference(cnf_transformation,[],[f18])).
% 11.79/2.00  
% 11.79/2.00  fof(f73,plain,(
% 11.79/2.00    v3_ordinal1(sK5)),
% 11.79/2.00    inference(cnf_transformation,[],[f47])).
% 11.79/2.00  
% 11.79/2.00  fof(f3,axiom,(
% 11.79/2.00    ! [X0] : (v3_ordinal1(X0) => ? [X1] : (v4_ordinal1(X1) & r2_hidden(X0,X1) & v3_ordinal1(X1)))),
% 11.79/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.79/2.00  
% 11.79/2.00  fof(f14,plain,(
% 11.79/2.00    ! [X0] : (v3_ordinal1(X0) => ? [X1] : (r2_hidden(X0,X1) & v3_ordinal1(X1)))),
% 11.79/2.00    inference(pure_predicate_removal,[],[f3])).
% 11.79/2.00  
% 11.79/2.00  fof(f19,plain,(
% 11.79/2.00    ! [X0] : (? [X1] : (r2_hidden(X0,X1) & v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 11.79/2.00    inference(ennf_transformation,[],[f14])).
% 11.79/2.00  
% 11.79/2.00  fof(f33,plain,(
% 11.79/2.00    ! [X0] : (? [X1] : (r2_hidden(X0,X1) & v3_ordinal1(X1)) => (r2_hidden(X0,sK0(X0)) & v3_ordinal1(sK0(X0))))),
% 11.79/2.00    introduced(choice_axiom,[])).
% 11.79/2.00  
% 11.79/2.00  fof(f34,plain,(
% 11.79/2.00    ! [X0] : ((r2_hidden(X0,sK0(X0)) & v3_ordinal1(sK0(X0))) | ~v3_ordinal1(X0))),
% 11.79/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f33])).
% 11.79/2.00  
% 11.79/2.00  fof(f52,plain,(
% 11.79/2.00    ( ! [X0] : (r2_hidden(X0,sK0(X0)) | ~v3_ordinal1(X0)) )),
% 11.79/2.00    inference(cnf_transformation,[],[f34])).
% 11.79/2.00  
% 11.79/2.00  fof(f9,axiom,(
% 11.79/2.00    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => k1_wellord1(k1_wellord2(X1),X0) = X0)))),
% 11.79/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.79/2.00  
% 11.79/2.00  fof(f27,plain,(
% 11.79/2.00    ! [X0] : (! [X1] : ((k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 11.79/2.00    inference(ennf_transformation,[],[f9])).
% 11.79/2.00  
% 11.79/2.00  fof(f28,plain,(
% 11.79/2.00    ! [X0] : (! [X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 11.79/2.00    inference(flattening,[],[f27])).
% 11.79/2.00  
% 11.79/2.00  fof(f69,plain,(
% 11.79/2.00    ( ! [X0,X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 11.79/2.00    inference(cnf_transformation,[],[f28])).
% 11.79/2.00  
% 11.79/2.00  fof(f51,plain,(
% 11.79/2.00    ( ! [X0] : (v3_ordinal1(sK0(X0)) | ~v3_ordinal1(X0)) )),
% 11.79/2.00    inference(cnf_transformation,[],[f34])).
% 11.79/2.00  
% 11.79/2.00  fof(f4,axiom,(
% 11.79/2.00    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 11.79/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.79/2.00  
% 11.79/2.00  fof(f20,plain,(
% 11.79/2.00    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 11.79/2.00    inference(ennf_transformation,[],[f4])).
% 11.79/2.00  
% 11.79/2.00  fof(f35,plain,(
% 11.79/2.00    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 11.79/2.00    inference(nnf_transformation,[],[f20])).
% 11.79/2.00  
% 11.79/2.00  fof(f36,plain,(
% 11.79/2.00    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 11.79/2.00    inference(flattening,[],[f35])).
% 11.79/2.00  
% 11.79/2.00  fof(f37,plain,(
% 11.79/2.00    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 11.79/2.00    inference(rectify,[],[f36])).
% 11.79/2.00  
% 11.79/2.00  fof(f38,plain,(
% 11.79/2.00    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2))) => ((~r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) | sK1(X0,X1,X2) = X1 | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) & sK1(X0,X1,X2) != X1) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 11.79/2.00    introduced(choice_axiom,[])).
% 11.79/2.00  
% 11.79/2.00  fof(f39,plain,(
% 11.79/2.00    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) | sK1(X0,X1,X2) = X1 | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) & sK1(X0,X1,X2) != X1) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 11.79/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).
% 11.79/2.00  
% 11.79/2.00  fof(f54,plain,(
% 11.79/2.00    ( ! [X4,X2,X0,X1] : (r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 11.79/2.00    inference(cnf_transformation,[],[f39])).
% 11.79/2.00  
% 11.79/2.00  fof(f77,plain,(
% 11.79/2.00    ( ! [X4,X0,X1] : (r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(X4,k1_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 11.79/2.00    inference(equality_resolution,[],[f54])).
% 11.79/2.00  
% 11.79/2.00  fof(f8,axiom,(
% 11.79/2.00    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 11.79/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.79/2.00  
% 11.79/2.00  fof(f68,plain,(
% 11.79/2.00    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 11.79/2.00    inference(cnf_transformation,[],[f8])).
% 11.79/2.00  
% 11.79/2.00  fof(f7,axiom,(
% 11.79/2.00    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 11.79/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.79/2.00  
% 11.79/2.00  fof(f25,plain,(
% 11.79/2.00    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 11.79/2.00    inference(ennf_transformation,[],[f7])).
% 11.79/2.00  
% 11.79/2.00  fof(f26,plain,(
% 11.79/2.00    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 11.79/2.00    inference(flattening,[],[f25])).
% 11.79/2.00  
% 11.79/2.00  fof(f40,plain,(
% 11.79/2.00    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 11.79/2.00    inference(nnf_transformation,[],[f26])).
% 11.79/2.00  
% 11.79/2.00  fof(f41,plain,(
% 11.79/2.00    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 11.79/2.00    inference(flattening,[],[f40])).
% 11.79/2.00  
% 11.79/2.00  fof(f42,plain,(
% 11.79/2.00    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 11.79/2.00    inference(rectify,[],[f41])).
% 11.79/2.00  
% 11.79/2.00  fof(f43,plain,(
% 11.79/2.00    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK2(X0,X1),sK3(X0,X1)) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & (r1_tarski(sK2(X0,X1),sK3(X0,X1)) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),X0)))),
% 11.79/2.00    introduced(choice_axiom,[])).
% 11.79/2.00  
% 11.79/2.00  fof(f44,plain,(
% 11.79/2.00    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK2(X0,X1),sK3(X0,X1)) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & (r1_tarski(sK2(X0,X1),sK3(X0,X1)) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 11.79/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f42,f43])).
% 11.79/2.00  
% 11.79/2.00  fof(f62,plain,(
% 11.79/2.00    ( ! [X4,X0,X5,X1] : (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 11.79/2.00    inference(cnf_transformation,[],[f44])).
% 11.79/2.00  
% 11.79/2.00  fof(f85,plain,(
% 11.79/2.00    ( ! [X4,X0,X5] : (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0)) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | ~v1_relat_1(k1_wellord2(X0))) )),
% 11.79/2.00    inference(equality_resolution,[],[f62])).
% 11.79/2.00  
% 11.79/2.00  fof(f1,axiom,(
% 11.79/2.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 11.79/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.79/2.00  
% 11.79/2.00  fof(f15,plain,(
% 11.79/2.00    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 11.79/2.00    inference(ennf_transformation,[],[f1])).
% 11.79/2.00  
% 11.79/2.00  fof(f16,plain,(
% 11.79/2.00    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 11.79/2.00    inference(flattening,[],[f15])).
% 11.79/2.00  
% 11.79/2.00  fof(f48,plain,(
% 11.79/2.00    ( ! [X2,X0,X1] : (r2_hidden(X0,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 11.79/2.00    inference(cnf_transformation,[],[f16])).
% 11.79/2.00  
% 11.79/2.00  fof(f61,plain,(
% 11.79/2.00    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 11.79/2.00    inference(cnf_transformation,[],[f44])).
% 11.79/2.00  
% 11.79/2.00  fof(f86,plain,(
% 11.79/2.00    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 11.79/2.00    inference(equality_resolution,[],[f61])).
% 11.79/2.00  
% 11.79/2.00  fof(f11,axiom,(
% 11.79/2.00    ! [X0,X1] : (r1_tarski(X0,X1) => k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0))),
% 11.79/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.79/2.00  
% 11.79/2.00  fof(f30,plain,(
% 11.79/2.00    ! [X0,X1] : (k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) | ~r1_tarski(X0,X1))),
% 11.79/2.00    inference(ennf_transformation,[],[f11])).
% 11.79/2.00  
% 11.79/2.00  fof(f71,plain,(
% 11.79/2.00    ( ! [X0,X1] : (k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) | ~r1_tarski(X0,X1)) )),
% 11.79/2.00    inference(cnf_transformation,[],[f30])).
% 11.79/2.00  
% 11.79/2.00  fof(f75,plain,(
% 11.79/2.00    sK4 != sK5),
% 11.79/2.00    inference(cnf_transformation,[],[f47])).
% 11.79/2.00  
% 11.79/2.00  fof(f6,axiom,(
% 11.79/2.00    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 11.79/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.79/2.00  
% 11.79/2.00  fof(f23,plain,(
% 11.79/2.00    ! [X0] : ((! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 11.79/2.00    inference(ennf_transformation,[],[f6])).
% 11.79/2.00  
% 11.79/2.00  fof(f24,plain,(
% 11.79/2.00    ! [X0] : (! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 11.79/2.00    inference(flattening,[],[f23])).
% 11.79/2.00  
% 11.79/2.00  fof(f60,plain,(
% 11.79/2.00    ( ! [X0,X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0)) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 11.79/2.00    inference(cnf_transformation,[],[f24])).
% 11.79/2.00  
% 11.79/2.00  fof(f10,axiom,(
% 11.79/2.00    ! [X0] : (v3_ordinal1(X0) => v2_wellord1(k1_wellord2(X0)))),
% 11.79/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.79/2.00  
% 11.79/2.00  fof(f29,plain,(
% 11.79/2.00    ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0))),
% 11.79/2.00    inference(ennf_transformation,[],[f10])).
% 11.79/2.00  
% 11.79/2.00  fof(f70,plain,(
% 11.79/2.00    ( ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 11.79/2.00    inference(cnf_transformation,[],[f29])).
% 11.79/2.00  
% 11.79/2.00  fof(f74,plain,(
% 11.79/2.00    r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK5))),
% 11.79/2.00    inference(cnf_transformation,[],[f47])).
% 11.79/2.00  
% 11.79/2.00  fof(f5,axiom,(
% 11.79/2.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 11.79/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.79/2.00  
% 11.79/2.00  fof(f21,plain,(
% 11.79/2.00    ! [X0] : (! [X1] : ((r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.79/2.00    inference(ennf_transformation,[],[f5])).
% 11.79/2.00  
% 11.79/2.00  fof(f22,plain,(
% 11.79/2.00    ! [X0] : (! [X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.79/2.00    inference(flattening,[],[f21])).
% 11.79/2.00  
% 11.79/2.00  fof(f59,plain,(
% 11.79/2.00    ( ! [X0,X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.79/2.00    inference(cnf_transformation,[],[f22])).
% 11.79/2.00  
% 11.79/2.00  fof(f53,plain,(
% 11.79/2.00    ( ! [X4,X2,X0,X1] : (X1 != X4 | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 11.79/2.00    inference(cnf_transformation,[],[f39])).
% 11.79/2.00  
% 11.79/2.00  fof(f78,plain,(
% 11.79/2.00    ( ! [X4,X2,X0] : (~r2_hidden(X4,X2) | k1_wellord1(X0,X4) != X2 | ~v1_relat_1(X0)) )),
% 11.79/2.00    inference(equality_resolution,[],[f53])).
% 11.79/2.00  
% 11.79/2.00  fof(f79,plain,(
% 11.79/2.00    ( ! [X4,X0] : (~r2_hidden(X4,k1_wellord1(X0,X4)) | ~v1_relat_1(X0)) )),
% 11.79/2.00    inference(equality_resolution,[],[f78])).
% 11.79/2.00  
% 11.79/2.00  cnf(c_27,negated_conjecture,
% 11.79/2.00      ( v3_ordinal1(sK4) ),
% 11.79/2.00      inference(cnf_transformation,[],[f72]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_1243,plain,
% 11.79/2.00      ( v3_ordinal1(sK4) = iProver_top ),
% 11.79/2.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_2,plain,
% 11.79/2.00      ( r2_hidden(X0,X1)
% 11.79/2.00      | r2_hidden(X1,X0)
% 11.79/2.00      | ~ v3_ordinal1(X1)
% 11.79/2.00      | ~ v3_ordinal1(X0)
% 11.79/2.00      | X0 = X1 ),
% 11.79/2.00      inference(cnf_transformation,[],[f50]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_1264,plain,
% 11.79/2.00      ( X0 = X1
% 11.79/2.00      | r2_hidden(X0,X1) = iProver_top
% 11.79/2.00      | r2_hidden(X1,X0) = iProver_top
% 11.79/2.00      | v3_ordinal1(X0) != iProver_top
% 11.79/2.00      | v3_ordinal1(X1) != iProver_top ),
% 11.79/2.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_26,negated_conjecture,
% 11.79/2.00      ( v3_ordinal1(sK5) ),
% 11.79/2.00      inference(cnf_transformation,[],[f73]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_1244,plain,
% 11.79/2.00      ( v3_ordinal1(sK5) = iProver_top ),
% 11.79/2.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_3,plain,
% 11.79/2.00      ( r2_hidden(X0,sK0(X0)) | ~ v3_ordinal1(X0) ),
% 11.79/2.00      inference(cnf_transformation,[],[f52]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_1263,plain,
% 11.79/2.00      ( r2_hidden(X0,sK0(X0)) = iProver_top | v3_ordinal1(X0) != iProver_top ),
% 11.79/2.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_21,plain,
% 11.79/2.00      ( ~ r2_hidden(X0,X1)
% 11.79/2.00      | ~ v3_ordinal1(X1)
% 11.79/2.00      | ~ v3_ordinal1(X0)
% 11.79/2.00      | k1_wellord1(k1_wellord2(X1),X0) = X0 ),
% 11.79/2.00      inference(cnf_transformation,[],[f69]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_1247,plain,
% 11.79/2.00      ( k1_wellord1(k1_wellord2(X0),X1) = X1
% 11.79/2.00      | r2_hidden(X1,X0) != iProver_top
% 11.79/2.00      | v3_ordinal1(X1) != iProver_top
% 11.79/2.00      | v3_ordinal1(X0) != iProver_top ),
% 11.79/2.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_2237,plain,
% 11.79/2.00      ( k1_wellord1(k1_wellord2(sK0(X0)),X0) = X0
% 11.79/2.00      | v3_ordinal1(X0) != iProver_top
% 11.79/2.00      | v3_ordinal1(sK0(X0)) != iProver_top ),
% 11.79/2.00      inference(superposition,[status(thm)],[c_1263,c_1247]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_4,plain,
% 11.79/2.00      ( ~ v3_ordinal1(X0) | v3_ordinal1(sK0(X0)) ),
% 11.79/2.00      inference(cnf_transformation,[],[f51]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_84,plain,
% 11.79/2.00      ( v3_ordinal1(X0) != iProver_top | v3_ordinal1(sK0(X0)) = iProver_top ),
% 11.79/2.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_2384,plain,
% 11.79/2.00      ( v3_ordinal1(X0) != iProver_top
% 11.79/2.00      | k1_wellord1(k1_wellord2(sK0(X0)),X0) = X0 ),
% 11.79/2.00      inference(global_propositional_subsumption,[status(thm)],[c_2237,c_84]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_2385,plain,
% 11.79/2.00      ( k1_wellord1(k1_wellord2(sK0(X0)),X0) = X0
% 11.79/2.00      | v3_ordinal1(X0) != iProver_top ),
% 11.79/2.00      inference(renaming,[status(thm)],[c_2384]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_2393,plain,
% 11.79/2.00      ( k1_wellord1(k1_wellord2(sK0(sK5)),sK5) = sK5 ),
% 11.79/2.00      inference(superposition,[status(thm)],[c_1244,c_2385]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_9,plain,
% 11.79/2.00      ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
% 11.79/2.00      | r2_hidden(k4_tarski(X0,X2),X1)
% 11.79/2.00      | ~ v1_relat_1(X1) ),
% 11.79/2.00      inference(cnf_transformation,[],[f77]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_1257,plain,
% 11.79/2.00      ( r2_hidden(X0,k1_wellord1(X1,X2)) != iProver_top
% 11.79/2.00      | r2_hidden(k4_tarski(X0,X2),X1) = iProver_top
% 11.79/2.00      | v1_relat_1(X1) != iProver_top ),
% 11.79/2.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_2407,plain,
% 11.79/2.00      ( r2_hidden(X0,sK5) != iProver_top
% 11.79/2.00      | r2_hidden(k4_tarski(X0,sK5),k1_wellord2(sK0(sK5))) = iProver_top
% 11.79/2.00      | v1_relat_1(k1_wellord2(sK0(sK5))) != iProver_top ),
% 11.79/2.00      inference(superposition,[status(thm)],[c_2393,c_1257]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_20,plain,
% 11.79/2.00      ( v1_relat_1(k1_wellord2(X0)) ),
% 11.79/2.00      inference(cnf_transformation,[],[f68]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_1248,plain,
% 11.79/2.00      ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
% 11.79/2.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_3167,plain,
% 11.79/2.00      ( r2_hidden(X0,sK5) != iProver_top
% 11.79/2.00      | r2_hidden(k4_tarski(X0,sK5),k1_wellord2(sK0(sK5))) = iProver_top ),
% 11.79/2.00      inference(forward_subsumption_resolution,[status(thm)],[c_2407,c_1248]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_18,plain,
% 11.79/2.00      ( r1_tarski(X0,X1)
% 11.79/2.00      | ~ r2_hidden(X1,X2)
% 11.79/2.00      | ~ r2_hidden(X0,X2)
% 11.79/2.00      | ~ r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2))
% 11.79/2.00      | ~ v1_relat_1(k1_wellord2(X2)) ),
% 11.79/2.00      inference(cnf_transformation,[],[f85]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_1249,plain,
% 11.79/2.00      ( r1_tarski(X0,X1) = iProver_top
% 11.79/2.00      | r2_hidden(X1,X2) != iProver_top
% 11.79/2.00      | r2_hidden(X0,X2) != iProver_top
% 11.79/2.00      | r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2)) != iProver_top
% 11.79/2.00      | v1_relat_1(k1_wellord2(X2)) != iProver_top ),
% 11.79/2.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_1387,plain,
% 11.79/2.00      ( r1_tarski(X0,X1) = iProver_top
% 11.79/2.00      | r2_hidden(X1,X2) != iProver_top
% 11.79/2.00      | r2_hidden(X0,X2) != iProver_top
% 11.79/2.00      | r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2)) != iProver_top ),
% 11.79/2.00      inference(forward_subsumption_resolution,[status(thm)],[c_1249,c_1248]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_5827,plain,
% 11.79/2.00      ( r1_tarski(X0,sK5) = iProver_top
% 11.79/2.00      | r2_hidden(X0,sK0(sK5)) != iProver_top
% 11.79/2.00      | r2_hidden(X0,sK5) != iProver_top
% 11.79/2.00      | r2_hidden(sK5,sK0(sK5)) != iProver_top ),
% 11.79/2.00      inference(superposition,[status(thm)],[c_3167,c_1387]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_29,plain,
% 11.79/2.00      ( v3_ordinal1(sK5) = iProver_top ),
% 11.79/2.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_2859,plain,
% 11.79/2.00      ( r2_hidden(sK5,sK0(sK5)) | ~ v3_ordinal1(sK5) ),
% 11.79/2.00      inference(instantiation,[status(thm)],[c_3]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_2862,plain,
% 11.79/2.00      ( r2_hidden(sK5,sK0(sK5)) = iProver_top
% 11.79/2.00      | v3_ordinal1(sK5) != iProver_top ),
% 11.79/2.00      inference(predicate_to_equality,[status(thm)],[c_2859]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_1,plain,
% 11.79/2.00      ( r2_hidden(X0,k3_relat_1(X1))
% 11.79/2.00      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 11.79/2.00      | ~ v1_relat_1(X1) ),
% 11.79/2.00      inference(cnf_transformation,[],[f48]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_1265,plain,
% 11.79/2.00      ( r2_hidden(X0,k3_relat_1(X1)) = iProver_top
% 11.79/2.00      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top
% 11.79/2.00      | v1_relat_1(X1) != iProver_top ),
% 11.79/2.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_3172,plain,
% 11.79/2.00      ( r2_hidden(X0,k3_relat_1(k1_wellord2(sK0(sK5)))) = iProver_top
% 11.79/2.00      | r2_hidden(X0,sK5) != iProver_top
% 11.79/2.00      | v1_relat_1(k1_wellord2(sK0(sK5))) != iProver_top ),
% 11.79/2.00      inference(superposition,[status(thm)],[c_3167,c_1265]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_19,plain,
% 11.79/2.00      ( ~ v1_relat_1(k1_wellord2(X0)) | k3_relat_1(k1_wellord2(X0)) = X0 ),
% 11.79/2.00      inference(cnf_transformation,[],[f86]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_159,plain,
% 11.79/2.00      ( k3_relat_1(k1_wellord2(X0)) = X0 ),
% 11.79/2.00      inference(global_propositional_subsumption,[status(thm)],[c_19,c_20]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_3191,plain,
% 11.79/2.00      ( r2_hidden(X0,sK0(sK5)) = iProver_top
% 11.79/2.00      | r2_hidden(X0,sK5) != iProver_top
% 11.79/2.00      | v1_relat_1(k1_wellord2(sK0(sK5))) != iProver_top ),
% 11.79/2.00      inference(demodulation,[status(thm)],[c_3172,c_159]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_6058,plain,
% 11.79/2.00      ( r2_hidden(X0,sK0(sK5)) = iProver_top
% 11.79/2.00      | r2_hidden(X0,sK5) != iProver_top ),
% 11.79/2.00      inference(forward_subsumption_resolution,[status(thm)],[c_3191,c_1248]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_6964,plain,
% 11.79/2.00      ( r2_hidden(X0,sK5) != iProver_top | r1_tarski(X0,sK5) = iProver_top ),
% 11.79/2.00      inference(global_propositional_subsumption,
% 11.79/2.00                [status(thm)],
% 11.79/2.00                [c_5827,c_29,c_2862,c_6058]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_6965,plain,
% 11.79/2.00      ( r1_tarski(X0,sK5) = iProver_top | r2_hidden(X0,sK5) != iProver_top ),
% 11.79/2.00      inference(renaming,[status(thm)],[c_6964]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_6972,plain,
% 11.79/2.00      ( sK5 = X0
% 11.79/2.00      | r1_tarski(X0,sK5) = iProver_top
% 11.79/2.00      | r2_hidden(sK5,X0) = iProver_top
% 11.79/2.00      | v3_ordinal1(X0) != iProver_top
% 11.79/2.00      | v3_ordinal1(sK5) != iProver_top ),
% 11.79/2.00      inference(superposition,[status(thm)],[c_1264,c_6965]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_16760,plain,
% 11.79/2.00      ( v3_ordinal1(X0) != iProver_top
% 11.79/2.00      | r2_hidden(sK5,X0) = iProver_top
% 11.79/2.00      | r1_tarski(X0,sK5) = iProver_top
% 11.79/2.00      | sK5 = X0 ),
% 11.79/2.00      inference(global_propositional_subsumption,[status(thm)],[c_6972,c_29]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_16761,plain,
% 11.79/2.00      ( sK5 = X0
% 11.79/2.00      | r1_tarski(X0,sK5) = iProver_top
% 11.79/2.00      | r2_hidden(sK5,X0) = iProver_top
% 11.79/2.00      | v3_ordinal1(X0) != iProver_top ),
% 11.79/2.00      inference(renaming,[status(thm)],[c_16760]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_23,plain,
% 11.79/2.00      ( ~ r1_tarski(X0,X1)
% 11.79/2.00      | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ),
% 11.79/2.00      inference(cnf_transformation,[],[f71]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_1246,plain,
% 11.79/2.00      ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 11.79/2.00      | r1_tarski(X1,X0) != iProver_top ),
% 11.79/2.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_16770,plain,
% 11.79/2.00      ( k2_wellord1(k1_wellord2(sK5),X0) = k1_wellord2(X0)
% 11.79/2.00      | sK5 = X0
% 11.79/2.00      | r2_hidden(sK5,X0) = iProver_top
% 11.79/2.00      | v3_ordinal1(X0) != iProver_top ),
% 11.79/2.00      inference(superposition,[status(thm)],[c_16761,c_1246]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_16779,plain,
% 11.79/2.00      ( k2_wellord1(k1_wellord2(sK5),X0) = k1_wellord2(X0)
% 11.79/2.00      | k1_wellord1(k1_wellord2(X0),sK5) = sK5
% 11.79/2.00      | sK5 = X0
% 11.79/2.00      | v3_ordinal1(X0) != iProver_top
% 11.79/2.00      | v3_ordinal1(sK5) != iProver_top ),
% 11.79/2.00      inference(superposition,[status(thm)],[c_16770,c_1247]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_34513,plain,
% 11.79/2.00      ( v3_ordinal1(X0) != iProver_top
% 11.79/2.00      | sK5 = X0
% 11.79/2.00      | k1_wellord1(k1_wellord2(X0),sK5) = sK5
% 11.79/2.00      | k2_wellord1(k1_wellord2(sK5),X0) = k1_wellord2(X0) ),
% 11.79/2.00      inference(global_propositional_subsumption,[status(thm)],[c_16779,c_29]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_34514,plain,
% 11.79/2.00      ( k2_wellord1(k1_wellord2(sK5),X0) = k1_wellord2(X0)
% 11.79/2.00      | k1_wellord1(k1_wellord2(X0),sK5) = sK5
% 11.79/2.00      | sK5 = X0
% 11.79/2.00      | v3_ordinal1(X0) != iProver_top ),
% 11.79/2.00      inference(renaming,[status(thm)],[c_34513]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_34525,plain,
% 11.79/2.00      ( k2_wellord1(k1_wellord2(sK5),sK4) = k1_wellord2(sK4)
% 11.79/2.00      | k1_wellord1(k1_wellord2(sK4),sK5) = sK5
% 11.79/2.00      | sK5 = sK4 ),
% 11.79/2.00      inference(superposition,[status(thm)],[c_1243,c_34514]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_24,negated_conjecture,
% 11.79/2.00      ( sK4 != sK5 ),
% 11.79/2.00      inference(cnf_transformation,[],[f75]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_791,plain,( X0 = X0 ),theory(equality) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_818,plain,
% 11.79/2.00      ( sK4 = sK4 ),
% 11.79/2.00      inference(instantiation,[status(thm)],[c_791]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_792,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_1512,plain,
% 11.79/2.00      ( sK5 != X0 | sK4 != X0 | sK4 = sK5 ),
% 11.79/2.00      inference(instantiation,[status(thm)],[c_792]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_1513,plain,
% 11.79/2.00      ( sK5 != sK4 | sK4 = sK5 | sK4 != sK4 ),
% 11.79/2.00      inference(instantiation,[status(thm)],[c_1512]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_34543,plain,
% 11.79/2.00      ( k1_wellord1(k1_wellord2(sK4),sK5) = sK5
% 11.79/2.00      | k2_wellord1(k1_wellord2(sK5),sK4) = k1_wellord2(sK4) ),
% 11.79/2.00      inference(global_propositional_subsumption,
% 11.79/2.00                [status(thm)],
% 11.79/2.00                [c_34525,c_27,c_26,c_24,c_818,c_1513,c_16846]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_34544,plain,
% 11.79/2.00      ( k2_wellord1(k1_wellord2(sK5),sK4) = k1_wellord2(sK4)
% 11.79/2.00      | k1_wellord1(k1_wellord2(sK4),sK5) = sK5 ),
% 11.79/2.00      inference(renaming,[status(thm)],[c_34543]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_2722,plain,
% 11.79/2.00      ( X0 = X1
% 11.79/2.00      | k1_wellord1(k1_wellord2(X1),X0) = X0
% 11.79/2.00      | r2_hidden(X1,X0) = iProver_top
% 11.79/2.00      | v3_ordinal1(X1) != iProver_top
% 11.79/2.00      | v3_ordinal1(X0) != iProver_top ),
% 11.79/2.00      inference(superposition,[status(thm)],[c_1264,c_1247]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_18535,plain,
% 11.79/2.00      ( X0 = X1
% 11.79/2.00      | k1_wellord1(k1_wellord2(X0),X1) = X1
% 11.79/2.00      | k1_wellord1(k1_wellord2(X1),X0) = X0
% 11.79/2.00      | v3_ordinal1(X1) != iProver_top
% 11.79/2.00      | v3_ordinal1(X0) != iProver_top ),
% 11.79/2.00      inference(superposition,[status(thm)],[c_2722,c_1247]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_25095,plain,
% 11.79/2.00      ( k1_wellord1(k1_wellord2(X0),sK5) = sK5
% 11.79/2.00      | k1_wellord1(k1_wellord2(sK5),X0) = X0
% 11.79/2.00      | sK5 = X0
% 11.79/2.00      | v3_ordinal1(X0) != iProver_top ),
% 11.79/2.00      inference(superposition,[status(thm)],[c_1244,c_18535]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_25311,plain,
% 11.79/2.00      ( k1_wellord1(k1_wellord2(sK5),sK4) = sK4
% 11.79/2.00      | k1_wellord1(k1_wellord2(sK4),sK5) = sK5
% 11.79/2.00      | sK5 = sK4 ),
% 11.79/2.00      inference(superposition,[status(thm)],[c_1243,c_25095]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_25329,plain,
% 11.79/2.00      ( k1_wellord1(k1_wellord2(sK4),sK5) = sK5
% 11.79/2.00      | k1_wellord1(k1_wellord2(sK5),sK4) = sK4 ),
% 11.79/2.00      inference(global_propositional_subsumption,
% 11.79/2.00                [status(thm)],
% 11.79/2.00                [c_25311,c_24,c_818,c_1513]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_25330,plain,
% 11.79/2.00      ( k1_wellord1(k1_wellord2(sK5),sK4) = sK4
% 11.79/2.00      | k1_wellord1(k1_wellord2(sK4),sK5) = sK5 ),
% 11.79/2.00      inference(renaming,[status(thm)],[c_25329]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_12,plain,
% 11.79/2.00      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
% 11.79/2.00      | ~ r2_hidden(X1,k3_relat_1(X0))
% 11.79/2.00      | ~ v2_wellord1(X0)
% 11.79/2.00      | ~ v1_relat_1(X0) ),
% 11.79/2.00      inference(cnf_transformation,[],[f60]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_22,plain,
% 11.79/2.00      ( v2_wellord1(k1_wellord2(X0)) | ~ v3_ordinal1(X0) ),
% 11.79/2.00      inference(cnf_transformation,[],[f70]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_306,plain,
% 11.79/2.00      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
% 11.79/2.00      | ~ r2_hidden(X1,k3_relat_1(X0))
% 11.79/2.00      | ~ v3_ordinal1(X2)
% 11.79/2.00      | ~ v1_relat_1(X0)
% 11.79/2.00      | k1_wellord2(X2) != X0 ),
% 11.79/2.00      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_307,plain,
% 11.79/2.00      ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
% 11.79/2.00      | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
% 11.79/2.00      | ~ v3_ordinal1(X0)
% 11.79/2.00      | ~ v1_relat_1(k1_wellord2(X0)) ),
% 11.79/2.00      inference(unflattening,[status(thm)],[c_306]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_311,plain,
% 11.79/2.00      ( ~ v3_ordinal1(X0)
% 11.79/2.00      | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
% 11.79/2.00      | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) ),
% 11.79/2.00      inference(global_propositional_subsumption,[status(thm)],[c_307,c_20]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_312,plain,
% 11.79/2.00      ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
% 11.79/2.00      | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
% 11.79/2.00      | ~ v3_ordinal1(X0) ),
% 11.79/2.00      inference(renaming,[status(thm)],[c_311]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_1242,plain,
% 11.79/2.00      ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
% 11.79/2.00      | r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) != iProver_top
% 11.79/2.00      | v3_ordinal1(X0) != iProver_top ),
% 11.79/2.00      inference(predicate_to_equality,[status(thm)],[c_312]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_1359,plain,
% 11.79/2.00      ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
% 11.79/2.00      | r2_hidden(X1,X0) != iProver_top
% 11.79/2.00      | v3_ordinal1(X0) != iProver_top ),
% 11.79/2.00      inference(light_normalisation,[status(thm)],[c_1242,c_159]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_25339,plain,
% 11.79/2.00      ( k1_wellord1(k1_wellord2(sK4),sK5) = sK5
% 11.79/2.00      | r4_wellord1(k1_wellord2(sK5),k2_wellord1(k1_wellord2(sK5),sK4)) != iProver_top
% 11.79/2.00      | r2_hidden(sK4,sK5) != iProver_top
% 11.79/2.00      | v3_ordinal1(sK5) != iProver_top ),
% 11.79/2.00      inference(superposition,[status(thm)],[c_25330,c_1359]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_28,plain,
% 11.79/2.00      ( v3_ordinal1(sK4) = iProver_top ),
% 11.79/2.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_1690,plain,
% 11.79/2.00      ( r2_hidden(sK5,sK4)
% 11.79/2.00      | r2_hidden(sK4,sK5)
% 11.79/2.00      | ~ v3_ordinal1(sK5)
% 11.79/2.00      | ~ v3_ordinal1(sK4)
% 11.79/2.00      | sK4 = sK5 ),
% 11.79/2.00      inference(instantiation,[status(thm)],[c_2]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_1691,plain,
% 11.79/2.00      ( sK4 = sK5
% 11.79/2.00      | r2_hidden(sK5,sK4) = iProver_top
% 11.79/2.00      | r2_hidden(sK4,sK5) = iProver_top
% 11.79/2.00      | v3_ordinal1(sK5) != iProver_top
% 11.79/2.00      | v3_ordinal1(sK4) != iProver_top ),
% 11.79/2.00      inference(predicate_to_equality,[status(thm)],[c_1690]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_1792,plain,
% 11.79/2.00      ( ~ r2_hidden(sK5,X0)
% 11.79/2.00      | ~ v3_ordinal1(X0)
% 11.79/2.00      | ~ v3_ordinal1(sK5)
% 11.79/2.00      | k1_wellord1(k1_wellord2(X0),sK5) = sK5 ),
% 11.79/2.00      inference(instantiation,[status(thm)],[c_21]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_1794,plain,
% 11.79/2.00      ( k1_wellord1(k1_wellord2(X0),sK5) = sK5
% 11.79/2.00      | r2_hidden(sK5,X0) != iProver_top
% 11.79/2.00      | v3_ordinal1(X0) != iProver_top
% 11.79/2.00      | v3_ordinal1(sK5) != iProver_top ),
% 11.79/2.00      inference(predicate_to_equality,[status(thm)],[c_1792]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_1796,plain,
% 11.79/2.00      ( k1_wellord1(k1_wellord2(sK4),sK5) = sK5
% 11.79/2.00      | r2_hidden(sK5,sK4) != iProver_top
% 11.79/2.00      | v3_ordinal1(sK5) != iProver_top
% 11.79/2.00      | v3_ordinal1(sK4) != iProver_top ),
% 11.79/2.00      inference(instantiation,[status(thm)],[c_1794]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_25515,plain,
% 11.79/2.00      ( k1_wellord1(k1_wellord2(sK4),sK5) = sK5
% 11.79/2.00      | r4_wellord1(k1_wellord2(sK5),k2_wellord1(k1_wellord2(sK5),sK4)) != iProver_top ),
% 11.79/2.00      inference(global_propositional_subsumption,
% 11.79/2.00                [status(thm)],
% 11.79/2.00                [c_25339,c_28,c_29,c_24,c_1691,c_1796]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_34547,plain,
% 11.79/2.00      ( k1_wellord1(k1_wellord2(sK4),sK5) = sK5
% 11.79/2.00      | r4_wellord1(k1_wellord2(sK5),k1_wellord2(sK4)) != iProver_top ),
% 11.79/2.00      inference(superposition,[status(thm)],[c_34544,c_25515]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_25,negated_conjecture,
% 11.79/2.00      ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK5)) ),
% 11.79/2.00      inference(cnf_transformation,[],[f74]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_1245,plain,
% 11.79/2.00      ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK5)) = iProver_top ),
% 11.79/2.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_11,plain,
% 11.79/2.00      ( ~ r4_wellord1(X0,X1)
% 11.79/2.00      | r4_wellord1(X1,X0)
% 11.79/2.00      | ~ v1_relat_1(X0)
% 11.79/2.00      | ~ v1_relat_1(X1) ),
% 11.79/2.00      inference(cnf_transformation,[],[f59]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_1255,plain,
% 11.79/2.00      ( r4_wellord1(X0,X1) != iProver_top
% 11.79/2.00      | r4_wellord1(X1,X0) = iProver_top
% 11.79/2.00      | v1_relat_1(X0) != iProver_top
% 11.79/2.00      | v1_relat_1(X1) != iProver_top ),
% 11.79/2.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_2081,plain,
% 11.79/2.00      ( r4_wellord1(k1_wellord2(sK5),k1_wellord2(sK4)) = iProver_top
% 11.79/2.00      | v1_relat_1(k1_wellord2(sK5)) != iProver_top
% 11.79/2.00      | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
% 11.79/2.00      inference(superposition,[status(thm)],[c_1245,c_1255]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_30,plain,
% 11.79/2.00      ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK5)) = iProver_top ),
% 11.79/2.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_40,plain,
% 11.79/2.00      ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
% 11.79/2.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_42,plain,
% 11.79/2.00      ( v1_relat_1(k1_wellord2(sK4)) = iProver_top ),
% 11.79/2.00      inference(instantiation,[status(thm)],[c_40]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_1497,plain,
% 11.79/2.00      ( r4_wellord1(X0,k1_wellord2(X1))
% 11.79/2.00      | ~ r4_wellord1(k1_wellord2(X1),X0)
% 11.79/2.00      | ~ v1_relat_1(X0)
% 11.79/2.00      | ~ v1_relat_1(k1_wellord2(X1)) ),
% 11.79/2.00      inference(instantiation,[status(thm)],[c_11]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_1675,plain,
% 11.79/2.00      ( ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
% 11.79/2.00      | r4_wellord1(k1_wellord2(X1),k1_wellord2(X0))
% 11.79/2.00      | ~ v1_relat_1(k1_wellord2(X1))
% 11.79/2.00      | ~ v1_relat_1(k1_wellord2(X0)) ),
% 11.79/2.00      inference(instantiation,[status(thm)],[c_1497]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_2047,plain,
% 11.79/2.00      ( r4_wellord1(k1_wellord2(sK5),k1_wellord2(sK4))
% 11.79/2.00      | ~ r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK5))
% 11.79/2.00      | ~ v1_relat_1(k1_wellord2(sK5))
% 11.79/2.00      | ~ v1_relat_1(k1_wellord2(sK4)) ),
% 11.79/2.00      inference(instantiation,[status(thm)],[c_1675]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_2048,plain,
% 11.79/2.00      ( r4_wellord1(k1_wellord2(sK5),k1_wellord2(sK4)) = iProver_top
% 11.79/2.00      | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK5)) != iProver_top
% 11.79/2.00      | v1_relat_1(k1_wellord2(sK5)) != iProver_top
% 11.79/2.00      | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
% 11.79/2.00      inference(predicate_to_equality,[status(thm)],[c_2047]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_2223,plain,
% 11.79/2.00      ( v1_relat_1(k1_wellord2(sK5)) != iProver_top
% 11.79/2.00      | r4_wellord1(k1_wellord2(sK5),k1_wellord2(sK4)) = iProver_top ),
% 11.79/2.00      inference(global_propositional_subsumption,
% 11.79/2.00                [status(thm)],
% 11.79/2.00                [c_2081,c_30,c_42,c_2048]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_2224,plain,
% 11.79/2.00      ( r4_wellord1(k1_wellord2(sK5),k1_wellord2(sK4)) = iProver_top
% 11.79/2.00      | v1_relat_1(k1_wellord2(sK5)) != iProver_top ),
% 11.79/2.00      inference(renaming,[status(thm)],[c_2223]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_2229,plain,
% 11.79/2.00      ( r4_wellord1(k1_wellord2(sK5),k1_wellord2(sK4)) = iProver_top ),
% 11.79/2.00      inference(forward_subsumption_resolution,[status(thm)],[c_2224,c_1248]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_34762,plain,
% 11.79/2.00      ( k1_wellord1(k1_wellord2(sK4),sK5) = sK5 ),
% 11.79/2.00      inference(global_propositional_subsumption,
% 11.79/2.00                [status(thm)],
% 11.79/2.00                [c_34547,c_2229]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_34776,plain,
% 11.79/2.00      ( r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK5)) != iProver_top
% 11.79/2.00      | r2_hidden(sK5,sK4) != iProver_top
% 11.79/2.00      | v3_ordinal1(sK4) != iProver_top ),
% 11.79/2.00      inference(superposition,[status(thm)],[c_34762,c_1359]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_2394,plain,
% 11.79/2.00      ( k1_wellord1(k1_wellord2(sK0(sK4)),sK4) = sK4 ),
% 11.79/2.00      inference(superposition,[status(thm)],[c_1243,c_2385]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_10,plain,
% 11.79/2.00      ( ~ r2_hidden(X0,k1_wellord1(X1,X0)) | ~ v1_relat_1(X1) ),
% 11.79/2.00      inference(cnf_transformation,[],[f79]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_1256,plain,
% 11.79/2.00      ( r2_hidden(X0,k1_wellord1(X1,X0)) != iProver_top
% 11.79/2.00      | v1_relat_1(X1) != iProver_top ),
% 11.79/2.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_2533,plain,
% 11.79/2.00      ( r2_hidden(sK4,sK4) != iProver_top
% 11.79/2.00      | v1_relat_1(k1_wellord2(sK0(sK4))) != iProver_top ),
% 11.79/2.00      inference(superposition,[status(thm)],[c_2394,c_1256]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_3085,plain,
% 11.79/2.00      ( r2_hidden(sK4,sK4) != iProver_top ),
% 11.79/2.00      inference(forward_subsumption_resolution,[status(thm)],[c_2533,c_1248]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_34774,plain,
% 11.79/2.00      ( r2_hidden(X0,sK5) != iProver_top
% 11.79/2.00      | r2_hidden(k4_tarski(X0,sK5),k1_wellord2(sK4)) = iProver_top
% 11.79/2.00      | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
% 11.79/2.00      inference(superposition,[status(thm)],[c_34762,c_1257]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_35589,plain,
% 11.79/2.00      ( r2_hidden(k4_tarski(X0,sK5),k1_wellord2(sK4)) = iProver_top
% 11.79/2.00      | r2_hidden(X0,sK5) != iProver_top ),
% 11.79/2.00      inference(global_propositional_subsumption,[status(thm)],[c_34774,c_42]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_35590,plain,
% 11.79/2.00      ( r2_hidden(X0,sK5) != iProver_top
% 11.79/2.00      | r2_hidden(k4_tarski(X0,sK5),k1_wellord2(sK4)) = iProver_top ),
% 11.79/2.00      inference(renaming,[status(thm)],[c_35589]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_35598,plain,
% 11.79/2.00      ( r2_hidden(X0,k3_relat_1(k1_wellord2(sK4))) = iProver_top
% 11.79/2.00      | r2_hidden(X0,sK5) != iProver_top
% 11.79/2.00      | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
% 11.79/2.00      inference(superposition,[status(thm)],[c_35590,c_1265]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_35630,plain,
% 11.79/2.00      ( r2_hidden(X0,sK5) != iProver_top
% 11.79/2.00      | r2_hidden(X0,sK4) = iProver_top
% 11.79/2.00      | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
% 11.79/2.00      inference(demodulation,[status(thm)],[c_35598,c_159]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_35648,plain,
% 11.79/2.00      ( r2_hidden(sK4,sK5) != iProver_top
% 11.79/2.00      | r2_hidden(sK4,sK4) = iProver_top
% 11.79/2.00      | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
% 11.79/2.00      inference(instantiation,[status(thm)],[c_35630]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_48682,plain,
% 11.79/2.00      ( r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK5)) != iProver_top ),
% 11.79/2.00      inference(global_propositional_subsumption,
% 11.79/2.00                [status(thm)],
% 11.79/2.00                [c_34776,c_28,c_29,c_24,c_42,c_1691,c_3085,c_35648]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_2532,plain,
% 11.79/2.00      ( r2_hidden(X0,sK4) != iProver_top
% 11.79/2.00      | r2_hidden(k4_tarski(X0,sK4),k1_wellord2(sK0(sK4))) = iProver_top
% 11.79/2.00      | v1_relat_1(k1_wellord2(sK0(sK4))) != iProver_top ),
% 11.79/2.00      inference(superposition,[status(thm)],[c_2394,c_1257]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_3215,plain,
% 11.79/2.00      ( r2_hidden(X0,sK4) != iProver_top
% 11.79/2.00      | r2_hidden(k4_tarski(X0,sK4),k1_wellord2(sK0(sK4))) = iProver_top ),
% 11.79/2.00      inference(forward_subsumption_resolution,[status(thm)],[c_2532,c_1248]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_5828,plain,
% 11.79/2.00      ( r1_tarski(X0,sK4) = iProver_top
% 11.79/2.00      | r2_hidden(X0,sK0(sK4)) != iProver_top
% 11.79/2.00      | r2_hidden(X0,sK4) != iProver_top
% 11.79/2.00      | r2_hidden(sK4,sK0(sK4)) != iProver_top ),
% 11.79/2.00      inference(superposition,[status(thm)],[c_3215,c_1387]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_87,plain,
% 11.79/2.00      ( r2_hidden(X0,sK0(X0)) = iProver_top | v3_ordinal1(X0) != iProver_top ),
% 11.79/2.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_89,plain,
% 11.79/2.00      ( r2_hidden(sK4,sK0(sK4)) = iProver_top
% 11.79/2.00      | v3_ordinal1(sK4) != iProver_top ),
% 11.79/2.00      inference(instantiation,[status(thm)],[c_87]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_3218,plain,
% 11.79/2.00      ( r2_hidden(X0,k3_relat_1(k1_wellord2(sK0(sK4)))) = iProver_top
% 11.79/2.00      | r2_hidden(X0,sK4) != iProver_top
% 11.79/2.00      | v1_relat_1(k1_wellord2(sK0(sK4))) != iProver_top ),
% 11.79/2.00      inference(superposition,[status(thm)],[c_3215,c_1265]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_3237,plain,
% 11.79/2.00      ( r2_hidden(X0,sK0(sK4)) = iProver_top
% 11.79/2.00      | r2_hidden(X0,sK4) != iProver_top
% 11.79/2.00      | v1_relat_1(k1_wellord2(sK0(sK4))) != iProver_top ),
% 11.79/2.00      inference(demodulation,[status(thm)],[c_3218,c_159]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_6352,plain,
% 11.79/2.00      ( r2_hidden(X0,sK0(sK4)) = iProver_top
% 11.79/2.00      | r2_hidden(X0,sK4) != iProver_top ),
% 11.79/2.00      inference(forward_subsumption_resolution,[status(thm)],[c_3237,c_1248]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_7106,plain,
% 11.79/2.00      ( r2_hidden(X0,sK4) != iProver_top | r1_tarski(X0,sK4) = iProver_top ),
% 11.79/2.00      inference(global_propositional_subsumption,
% 11.79/2.00                [status(thm)],
% 11.79/2.00                [c_5828,c_28,c_89,c_6352]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_7107,plain,
% 11.79/2.00      ( r1_tarski(X0,sK4) = iProver_top | r2_hidden(X0,sK4) != iProver_top ),
% 11.79/2.00      inference(renaming,[status(thm)],[c_7106]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_7112,plain,
% 11.79/2.00      ( sK4 = X0
% 11.79/2.00      | r1_tarski(X0,sK4) = iProver_top
% 11.79/2.00      | r2_hidden(sK4,X0) = iProver_top
% 11.79/2.00      | v3_ordinal1(X0) != iProver_top
% 11.79/2.00      | v3_ordinal1(sK4) != iProver_top ),
% 11.79/2.00      inference(superposition,[status(thm)],[c_1264,c_7107]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_17020,plain,
% 11.79/2.00      ( v3_ordinal1(X0) != iProver_top
% 11.79/2.00      | r2_hidden(sK4,X0) = iProver_top
% 11.79/2.00      | r1_tarski(X0,sK4) = iProver_top
% 11.79/2.00      | sK4 = X0 ),
% 11.79/2.00      inference(global_propositional_subsumption,[status(thm)],[c_7112,c_28]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_17021,plain,
% 11.79/2.00      ( sK4 = X0
% 11.79/2.00      | r1_tarski(X0,sK4) = iProver_top
% 11.79/2.00      | r2_hidden(sK4,X0) = iProver_top
% 11.79/2.00      | v3_ordinal1(X0) != iProver_top ),
% 11.79/2.00      inference(renaming,[status(thm)],[c_17020]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_17028,plain,
% 11.79/2.00      ( k2_wellord1(k1_wellord2(sK4),X0) = k1_wellord2(X0)
% 11.79/2.00      | sK4 = X0
% 11.79/2.00      | r2_hidden(sK4,X0) = iProver_top
% 11.79/2.00      | v3_ordinal1(X0) != iProver_top ),
% 11.79/2.00      inference(superposition,[status(thm)],[c_17021,c_1246]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_17035,plain,
% 11.79/2.00      ( k2_wellord1(k1_wellord2(sK4),X0) = k1_wellord2(X0)
% 11.79/2.00      | k1_wellord1(k1_wellord2(X0),sK4) = sK4
% 11.79/2.00      | sK4 = X0
% 11.79/2.00      | v3_ordinal1(X0) != iProver_top
% 11.79/2.00      | v3_ordinal1(sK4) != iProver_top ),
% 11.79/2.00      inference(superposition,[status(thm)],[c_17028,c_1247]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_44984,plain,
% 11.79/2.00      ( v3_ordinal1(X0) != iProver_top
% 11.79/2.00      | sK4 = X0
% 11.79/2.00      | k1_wellord1(k1_wellord2(X0),sK4) = sK4
% 11.79/2.00      | k2_wellord1(k1_wellord2(sK4),X0) = k1_wellord2(X0) ),
% 11.79/2.00      inference(global_propositional_subsumption,[status(thm)],[c_17035,c_28]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_44985,plain,
% 11.79/2.00      ( k2_wellord1(k1_wellord2(sK4),X0) = k1_wellord2(X0)
% 11.79/2.00      | k1_wellord1(k1_wellord2(X0),sK4) = sK4
% 11.79/2.00      | sK4 = X0
% 11.79/2.00      | v3_ordinal1(X0) != iProver_top ),
% 11.79/2.00      inference(renaming,[status(thm)],[c_44984]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_44993,plain,
% 11.79/2.00      ( k2_wellord1(k1_wellord2(sK4),sK5) = k1_wellord2(sK5)
% 11.79/2.00      | k1_wellord1(k1_wellord2(sK5),sK4) = sK4
% 11.79/2.00      | sK5 = sK4 ),
% 11.79/2.00      inference(superposition,[status(thm)],[c_1244,c_44985]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_35782,plain,
% 11.79/2.00      ( r2_hidden(X0,sK4) = iProver_top | r2_hidden(X0,sK5) != iProver_top ),
% 11.79/2.00      inference(global_propositional_subsumption,[status(thm)],[c_35630,c_42]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_35783,plain,
% 11.79/2.00      ( r2_hidden(X0,sK5) != iProver_top | r2_hidden(X0,sK4) = iProver_top ),
% 11.79/2.00      inference(renaming,[status(thm)],[c_35782]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_35809,plain,
% 11.79/2.00      ( k2_wellord1(k1_wellord2(sK4),sK5) = k1_wellord2(sK5)
% 11.79/2.00      | sK5 = sK4
% 11.79/2.00      | r2_hidden(sK4,sK4) = iProver_top
% 11.79/2.00      | v3_ordinal1(sK5) != iProver_top ),
% 11.79/2.00      inference(superposition,[status(thm)],[c_17028,c_35783]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_45010,plain,
% 11.79/2.00      ( k2_wellord1(k1_wellord2(sK4),sK5) = k1_wellord2(sK5) ),
% 11.79/2.00      inference(global_propositional_subsumption,
% 11.79/2.00                [status(thm)],
% 11.79/2.00                [c_44993,c_29,c_24,c_818,c_1513,c_3085,c_35809]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_48686,plain,
% 11.79/2.00      ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK5)) != iProver_top ),
% 11.79/2.00      inference(light_normalisation,[status(thm)],[c_48682,c_45010]) ).
% 11.79/2.00  
% 11.79/2.00  cnf(c_48688,plain,
% 11.79/2.00      ( $false ),
% 11.79/2.00      inference(forward_subsumption_resolution,[status(thm)],[c_48686,c_1245]) ).
% 11.79/2.00  
% 11.79/2.00  
% 11.79/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.79/2.00  
% 11.79/2.00  ------                               Statistics
% 11.79/2.00  
% 11.79/2.00  ------ General
% 11.79/2.00  
% 11.79/2.00  abstr_ref_over_cycles:                  0
% 11.79/2.00  abstr_ref_under_cycles:                 0
% 11.79/2.00  gc_basic_clause_elim:                   0
% 11.79/2.00  forced_gc_time:                         0
% 11.79/2.00  parsing_time:                           0.014
% 11.79/2.00  unif_index_cands_time:                  0.
% 11.79/2.00  unif_index_add_time:                    0.
% 11.79/2.00  orderings_time:                         0.
% 11.79/2.00  out_proof_time:                         0.022
% 11.79/2.00  total_time:                             1.254
% 11.79/2.00  num_of_symbols:                         48
% 11.79/2.00  num_of_terms:                           40055
% 11.79/2.00  
% 11.79/2.00  ------ Preprocessing
% 11.79/2.00  
% 11.79/2.00  num_of_splits:                          0
% 11.79/2.00  num_of_split_atoms:                     0
% 11.79/2.00  num_of_reused_defs:                     0
% 11.79/2.00  num_eq_ax_congr_red:                    21
% 11.79/2.00  num_of_sem_filtered_clauses:            1
% 11.79/2.00  num_of_subtypes:                        0
% 11.79/2.00  monotx_restored_types:                  0
% 11.79/2.00  sat_num_of_epr_types:                   0
% 11.79/2.00  sat_num_of_non_cyclic_types:            0
% 11.79/2.00  sat_guarded_non_collapsed_types:        0
% 11.79/2.00  num_pure_diseq_elim:                    0
% 11.79/2.00  simp_replaced_by:                       0
% 11.79/2.00  res_preprocessed:                       138
% 11.79/2.00  prep_upred:                             0
% 11.79/2.00  prep_unflattend:                        13
% 11.79/2.00  smt_new_axioms:                         0
% 11.79/2.00  pred_elim_cands:                        5
% 11.79/2.00  pred_elim:                              1
% 11.79/2.00  pred_elim_cl:                           1
% 11.79/2.00  pred_elim_cycles:                       3
% 11.79/2.00  merged_defs:                            0
% 11.79/2.00  merged_defs_ncl:                        0
% 11.79/2.00  bin_hyper_res:                          0
% 11.79/2.00  prep_cycles:                            4
% 11.79/2.00  pred_elim_time:                         0.007
% 11.79/2.00  splitting_time:                         0.
% 11.79/2.00  sem_filter_time:                        0.
% 11.79/2.00  monotx_time:                            0.
% 11.79/2.00  subtype_inf_time:                       0.
% 11.79/2.00  
% 11.79/2.00  ------ Problem properties
% 11.79/2.00  
% 11.79/2.00  clauses:                                27
% 11.79/2.00  conjectures:                            4
% 11.79/2.00  epr:                                    5
% 11.79/2.00  horn:                                   19
% 11.79/2.00  ground:                                 4
% 11.79/2.00  unary:                                  6
% 11.79/2.00  binary:                                 4
% 11.79/2.00  lits:                                   80
% 11.79/2.00  lits_eq:                                15
% 11.79/2.00  fd_pure:                                0
% 11.79/2.00  fd_pseudo:                              0
% 11.79/2.00  fd_cond:                                0
% 11.79/2.00  fd_pseudo_cond:                         4
% 11.79/2.00  ac_symbols:                             0
% 11.79/2.00  
% 11.79/2.00  ------ Propositional Solver
% 11.79/2.00  
% 11.79/2.00  prop_solver_calls:                      29
% 11.79/2.00  prop_fast_solver_calls:                 2657
% 11.79/2.00  smt_solver_calls:                       0
% 11.79/2.00  smt_fast_solver_calls:                  0
% 11.79/2.00  prop_num_of_clauses:                    14318
% 11.79/2.00  prop_preprocess_simplified:             27212
% 11.79/2.00  prop_fo_subsumed:                       82
% 11.79/2.00  prop_solver_time:                       0.
% 11.79/2.00  smt_solver_time:                        0.
% 11.79/2.00  smt_fast_solver_time:                   0.
% 11.79/2.00  prop_fast_solver_time:                  0.
% 11.79/2.00  prop_unsat_core_time:                   0.
% 11.79/2.00  
% 11.79/2.00  ------ QBF
% 11.79/2.00  
% 11.79/2.00  qbf_q_res:                              0
% 11.79/2.00  qbf_num_tautologies:                    0
% 11.79/2.00  qbf_prep_cycles:                        0
% 11.79/2.00  
% 11.79/2.00  ------ BMC1
% 11.79/2.00  
% 11.79/2.00  bmc1_current_bound:                     -1
% 11.79/2.00  bmc1_last_solved_bound:                 -1
% 11.79/2.00  bmc1_unsat_core_size:                   -1
% 11.79/2.00  bmc1_unsat_core_parents_size:           -1
% 11.79/2.00  bmc1_merge_next_fun:                    0
% 11.79/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.79/2.00  
% 11.79/2.00  ------ Instantiation
% 11.79/2.00  
% 11.79/2.00  inst_num_of_clauses:                    3367
% 11.79/2.00  inst_num_in_passive:                    1593
% 11.79/2.00  inst_num_in_active:                     1263
% 11.79/2.00  inst_num_in_unprocessed:                511
% 11.79/2.00  inst_num_of_loops:                      1510
% 11.79/2.00  inst_num_of_learning_restarts:          0
% 11.79/2.00  inst_num_moves_active_passive:          245
% 11.79/2.00  inst_lit_activity:                      0
% 11.79/2.00  inst_lit_activity_moves:                0
% 11.79/2.00  inst_num_tautologies:                   0
% 11.79/2.00  inst_num_prop_implied:                  0
% 11.79/2.00  inst_num_existing_simplified:           0
% 11.79/2.00  inst_num_eq_res_simplified:             0
% 11.79/2.00  inst_num_child_elim:                    0
% 11.79/2.00  inst_num_of_dismatching_blockings:      4366
% 11.79/2.00  inst_num_of_non_proper_insts:           5025
% 11.79/2.00  inst_num_of_duplicates:                 0
% 11.79/2.00  inst_inst_num_from_inst_to_res:         0
% 11.79/2.00  inst_dismatching_checking_time:         0.
% 11.79/2.00  
% 11.79/2.00  ------ Resolution
% 11.79/2.00  
% 11.79/2.00  res_num_of_clauses:                     0
% 11.79/2.00  res_num_in_passive:                     0
% 11.79/2.00  res_num_in_active:                      0
% 11.79/2.00  res_num_of_loops:                       142
% 11.79/2.00  res_forward_subset_subsumed:            212
% 11.79/2.00  res_backward_subset_subsumed:           2
% 11.79/2.00  res_forward_subsumed:                   0
% 11.79/2.00  res_backward_subsumed:                  0
% 11.79/2.00  res_forward_subsumption_resolution:     5
% 11.79/2.00  res_backward_subsumption_resolution:    0
% 11.79/2.00  res_clause_to_clause_subsumption:       7092
% 11.79/2.00  res_orphan_elimination:                 0
% 11.79/2.00  res_tautology_del:                      250
% 11.79/2.00  res_num_eq_res_simplified:              0
% 11.79/2.00  res_num_sel_changes:                    0
% 11.79/2.00  res_moves_from_active_to_pass:          0
% 11.79/2.00  
% 11.79/2.00  ------ Superposition
% 11.79/2.00  
% 11.79/2.00  sup_time_total:                         0.
% 11.79/2.00  sup_time_generating:                    0.
% 11.79/2.00  sup_time_sim_full:                      0.
% 11.79/2.00  sup_time_sim_immed:                     0.
% 11.79/2.00  
% 11.79/2.00  sup_num_of_clauses:                     1191
% 11.79/2.00  sup_num_in_active:                      290
% 11.79/2.00  sup_num_in_passive:                     901
% 11.79/2.00  sup_num_of_loops:                       300
% 11.79/2.00  sup_fw_superposition:                   722
% 11.79/2.00  sup_bw_superposition:                   1141
% 11.79/2.00  sup_immediate_simplified:               439
% 11.79/2.00  sup_given_eliminated:                   1
% 11.79/2.00  comparisons_done:                       0
% 11.79/2.00  comparisons_avoided:                    131
% 11.79/2.00  
% 11.79/2.00  ------ Simplifications
% 11.79/2.00  
% 11.79/2.00  
% 11.79/2.00  sim_fw_subset_subsumed:                 103
% 11.79/2.00  sim_bw_subset_subsumed:                 35
% 11.79/2.00  sim_fw_subsumed:                        133
% 11.79/2.00  sim_bw_subsumed:                        12
% 11.79/2.00  sim_fw_subsumption_res:                 111
% 11.79/2.00  sim_bw_subsumption_res:                 0
% 11.79/2.00  sim_tautology_del:                      19
% 11.79/2.00  sim_eq_tautology_del:                   142
% 11.79/2.00  sim_eq_res_simp:                        1
% 11.79/2.00  sim_fw_demodulated:                     177
% 11.79/2.00  sim_bw_demodulated:                     1
% 11.79/2.00  sim_light_normalised:                   90
% 11.79/2.00  sim_joinable_taut:                      0
% 11.79/2.00  sim_joinable_simp:                      0
% 11.79/2.00  sim_ac_normalised:                      0
% 11.79/2.00  sim_smt_subsumption:                    0
% 11.79/2.00  
%------------------------------------------------------------------------------
