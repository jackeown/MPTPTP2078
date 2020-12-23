%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:44 EST 2020

% Result     : Theorem 4.14s
% Output     : CNFRefutation 4.14s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_8944)

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

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

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

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
     => ( sK4 != X0
        & r4_wellord1(k1_wellord2(X0),k1_wellord2(sK4))
        & v3_ordinal1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
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

fof(f48,plain,
    ( sK3 != sK4
    & r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4))
    & v3_ordinal1(sK4)
    & v3_ordinal1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f33,f47,f46])).

fof(f77,plain,(
    v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f34])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f51])).

fof(f10,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f76,plain,(
    v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f54,f51])).

fof(f84,plain,(
    ! [X1] : r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(equality_resolution,[],[f80])).

fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
           => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_wellord1(k1_wellord2(X1),X0) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f83,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f56,f51])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

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
    inference(nnf_transformation,[],[f21])).

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
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f39,plain,(
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

fof(f40,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f86,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f58])).

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
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

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
    inference(nnf_transformation,[],[f27])).

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
     => ( ( ~ r1_tarski(sK1(X0,X1),sK2(X0,X1))
          | ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) )
        & ( r1_tarski(sK1(X0,X1),sK2(X0,X1))
          | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) )
        & r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f43,f44])).

fof(f66,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_tarski(X4,X5)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f94,plain,(
    ! [X4,X0,X5] :
      ( r1_tarski(X4,X5)
      | ~ r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f66])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f79,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f74,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f95,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f65])).

fof(f78,plain,(
    r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) ),
    inference(cnf_transformation,[],[f48])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r4_wellord1(X1,X0)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 != X4
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f87,plain,(
    ! [X4,X2,X0] :
      ( ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X4) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f88,plain,(
    ! [X4,X0] :
      ( ~ r2_hidden(X4,k1_wellord1(X0,X4))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f87])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1300,plain,
    ( X0 = X1
    | r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_28,negated_conjecture,
    ( v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1281,plain,
    ( v3_ordinal1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1302,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_22,plain,
    ( v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1285,plain,
    ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_29,negated_conjecture,
    ( v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1280,plain,
    ( v3_ordinal1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1303,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | k1_wellord1(k1_wellord2(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1284,plain,
    ( k1_wellord1(k1_wellord2(X0),X1) = X1
    | r2_hidden(X1,X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2728,plain,
    ( k1_wellord1(k1_wellord2(k2_xboole_0(X0,k1_tarski(X0))),X0) = X0
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1303,c_1284])).

cnf(c_6,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_86,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2741,plain,
    ( v3_ordinal1(X0) != iProver_top
    | k1_wellord1(k1_wellord2(k2_xboole_0(X0,k1_tarski(X0))),X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2728,c_86])).

cnf(c_2742,plain,
    ( k1_wellord1(k1_wellord2(k2_xboole_0(X0,k1_tarski(X0))),X0) = X0
    | v3_ordinal1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2741])).

cnf(c_2749,plain,
    ( k1_wellord1(k1_wellord2(k2_xboole_0(sK3,k1_tarski(sK3))),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_1280,c_2742])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1294,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3243,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k4_tarski(X0,sK3),k1_wellord2(k2_xboole_0(sK3,k1_tarski(sK3)))) = iProver_top
    | v1_relat_1(k1_wellord2(k2_xboole_0(sK3,k1_tarski(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2749,c_1294])).

cnf(c_20,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2))
    | ~ v1_relat_1(k1_wellord2(X2)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1286,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2)) != iProver_top
    | v1_relat_1(k1_wellord2(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3503,plain,
    ( r1_tarski(X0,sK3) = iProver_top
    | r2_hidden(X0,k2_xboole_0(sK3,k1_tarski(sK3))) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(sK3,k2_xboole_0(sK3,k1_tarski(sK3))) != iProver_top
    | v1_relat_1(k1_wellord2(k2_xboole_0(sK3,k1_tarski(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3243,c_1286])).

cnf(c_98,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_100,plain,
    ( r2_hidden(sK3,k2_xboole_0(sK3,k1_tarski(sK3))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_98])).

cnf(c_4445,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,k2_xboole_0(sK3,k1_tarski(sK3))) != iProver_top
    | r1_tarski(X0,sK3) = iProver_top
    | v1_relat_1(k1_wellord2(k2_xboole_0(sK3,k1_tarski(sK3)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3503,c_100])).

cnf(c_4446,plain,
    ( r1_tarski(X0,sK3) = iProver_top
    | r2_hidden(X0,k2_xboole_0(sK3,k1_tarski(sK3))) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | v1_relat_1(k1_wellord2(k2_xboole_0(sK3,k1_tarski(sK3)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4445])).

cnf(c_4449,plain,
    ( r1_tarski(X0,sK3) = iProver_top
    | r2_hidden(X0,k2_xboole_0(sK3,k1_tarski(sK3))) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1285,c_4446])).

cnf(c_5693,plain,
    ( r1_tarski(X0,sK3) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1302,c_4449])).

cnf(c_5782,plain,
    ( sK3 = X0
    | r1_tarski(X0,sK3) = iProver_top
    | r2_hidden(sK3,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1300,c_5693])).

cnf(c_30,plain,
    ( v3_ordinal1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_8954,plain,
    ( v3_ordinal1(X0) != iProver_top
    | r2_hidden(sK3,X0) = iProver_top
    | r1_tarski(X0,sK3) = iProver_top
    | sK3 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5782,c_30])).

cnf(c_8955,plain,
    ( sK3 = X0
    | r1_tarski(X0,sK3) = iProver_top
    | r2_hidden(sK3,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8954])).

cnf(c_25,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1283,plain,
    ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_8958,plain,
    ( k2_wellord1(k1_wellord2(sK3),X0) = k1_wellord2(X0)
    | sK3 = X0
    | r2_hidden(sK3,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8955,c_1283])).

cnf(c_9633,plain,
    ( k2_wellord1(k1_wellord2(sK3),X0) = k1_wellord2(X0)
    | k1_wellord1(k1_wellord2(X0),sK3) = sK3
    | sK3 = X0
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8958,c_1284])).

cnf(c_12197,plain,
    ( v3_ordinal1(X0) != iProver_top
    | sK3 = X0
    | k1_wellord1(k1_wellord2(X0),sK3) = sK3
    | k2_wellord1(k1_wellord2(sK3),X0) = k1_wellord2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9633,c_30])).

cnf(c_12198,plain,
    ( k2_wellord1(k1_wellord2(sK3),X0) = k1_wellord2(X0)
    | k1_wellord1(k1_wellord2(X0),sK3) = sK3
    | sK3 = X0
    | v3_ordinal1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_12197])).

cnf(c_12202,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
    | k1_wellord1(k1_wellord2(sK4),sK3) = sK3
    | sK4 = sK3 ),
    inference(superposition,[status(thm)],[c_1281,c_12198])).

cnf(c_26,negated_conjecture,
    ( sK3 != sK4 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_827,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_856,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_827])).

cnf(c_828,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1339,plain,
    ( sK4 != X0
    | sK3 != X0
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_828])).

cnf(c_1340,plain,
    ( sK4 != sK3
    | sK3 = sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1339])).

cnf(c_12233,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3
    | k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12202,c_26,c_856,c_1340])).

cnf(c_12234,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
    | k1_wellord1(k1_wellord2(sK4),sK3) = sK3 ),
    inference(renaming,[status(thm)],[c_12233])).

cnf(c_2748,plain,
    ( k1_wellord1(k1_wellord2(k2_xboole_0(sK4,k1_tarski(sK4))),sK4) = sK4 ),
    inference(superposition,[status(thm)],[c_1281,c_2742])).

cnf(c_2909,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k4_tarski(X0,sK4),k1_wellord2(k2_xboole_0(sK4,k1_tarski(sK4)))) = iProver_top
    | v1_relat_1(k1_wellord2(k2_xboole_0(sK4,k1_tarski(sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2748,c_1294])).

cnf(c_3348,plain,
    ( r1_tarski(X0,sK4) = iProver_top
    | r2_hidden(X0,k2_xboole_0(sK4,k1_tarski(sK4))) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(sK4,k2_xboole_0(sK4,k1_tarski(sK4))) != iProver_top
    | v1_relat_1(k1_wellord2(k2_xboole_0(sK4,k1_tarski(sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2909,c_1286])).

cnf(c_3266,plain,
    ( r2_hidden(X0,k2_xboole_0(sK4,k1_tarski(sK4)))
    | ~ r2_hidden(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3267,plain,
    ( r2_hidden(X0,k2_xboole_0(sK4,k1_tarski(sK4))) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3266])).

cnf(c_3687,plain,
    ( r1_tarski(X0,sK4) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(sK4,k2_xboole_0(sK4,k1_tarski(sK4))) != iProver_top
    | v1_relat_1(k1_wellord2(k2_xboole_0(sK4,k1_tarski(sK4)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3348,c_3267])).

cnf(c_3693,plain,
    ( r1_tarski(X0,sK4) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(sK4,k2_xboole_0(sK4,k1_tarski(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1285,c_3687])).

cnf(c_5094,plain,
    ( r1_tarski(X0,sK4) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1303,c_3693])).

cnf(c_5102,plain,
    ( sK4 = X0
    | r1_tarski(X0,sK4) = iProver_top
    | r2_hidden(sK4,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1300,c_5094])).

cnf(c_31,plain,
    ( v3_ordinal1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_8815,plain,
    ( v3_ordinal1(X0) != iProver_top
    | r2_hidden(sK4,X0) = iProver_top
    | r1_tarski(X0,sK4) = iProver_top
    | sK4 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5102,c_31])).

cnf(c_8816,plain,
    ( sK4 = X0
    | r1_tarski(X0,sK4) = iProver_top
    | r2_hidden(sK4,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8815])).

cnf(c_8821,plain,
    ( k2_wellord1(k1_wellord2(sK4),X0) = k1_wellord2(X0)
    | sK4 = X0
    | r2_hidden(sK4,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8816,c_1283])).

cnf(c_8931,plain,
    ( k2_wellord1(k1_wellord2(sK4),X0) = k1_wellord2(X0)
    | k1_wellord1(k1_wellord2(X0),sK4) = sK4
    | sK4 = X0
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8821,c_1284])).

cnf(c_12117,plain,
    ( v3_ordinal1(X0) != iProver_top
    | sK4 = X0
    | k1_wellord1(k1_wellord2(X0),sK4) = sK4
    | k2_wellord1(k1_wellord2(sK4),X0) = k1_wellord2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8931,c_31])).

cnf(c_12118,plain,
    ( k2_wellord1(k1_wellord2(sK4),X0) = k1_wellord2(X0)
    | k1_wellord1(k1_wellord2(X0),sK4) = sK4
    | sK4 = X0
    | v3_ordinal1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_12117])).

cnf(c_12125,plain,
    ( k2_wellord1(k1_wellord2(sK4),sK3) = k1_wellord2(sK3)
    | k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | sK4 = sK3 ),
    inference(superposition,[status(thm)],[c_1280,c_12118])).

cnf(c_12192,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | k2_wellord1(k1_wellord2(sK4),sK3) = k1_wellord2(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12125,c_29,c_28,c_26,c_856,c_1340,c_8944])).

cnf(c_12193,plain,
    ( k2_wellord1(k1_wellord2(sK4),sK3) = k1_wellord2(sK3)
    | k1_wellord1(k1_wellord2(sK3),sK4) = sK4 ),
    inference(renaming,[status(thm)],[c_12192])).

cnf(c_3077,plain,
    ( X0 = X1
    | k1_wellord1(k1_wellord2(X1),X0) = X0
    | r2_hidden(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1300,c_1284])).

cnf(c_9560,plain,
    ( X0 = X1
    | k1_wellord1(k1_wellord2(X0),X1) = X1
    | k1_wellord1(k1_wellord2(X1),X0) = X0
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3077,c_1284])).

cnf(c_9940,plain,
    ( k1_wellord1(k1_wellord2(X0),sK4) = sK4
    | k1_wellord1(k1_wellord2(sK4),X0) = X0
    | sK4 = X0
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1281,c_9560])).

cnf(c_9950,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3
    | k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | sK4 = sK3 ),
    inference(superposition,[status(thm)],[c_1280,c_9940])).

cnf(c_9944,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3
    | k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | sK4 = sK3
    | v3_ordinal1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9940])).

cnf(c_10113,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | k1_wellord1(k1_wellord2(sK4),sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9950,c_30,c_26,c_856,c_1340,c_9944])).

cnf(c_10114,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3
    | k1_wellord1(k1_wellord2(sK3),sK4) = sK4 ),
    inference(renaming,[status(thm)],[c_10113])).

cnf(c_14,plain,
    ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
    | ~ r2_hidden(X1,k3_relat_1(X0))
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_24,plain,
    ( v2_wellord1(k1_wellord2(X0))
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_329,plain,
    ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
    | ~ r2_hidden(X1,k3_relat_1(X0))
    | ~ v3_ordinal1(X2)
    | ~ v1_relat_1(X0)
    | k1_wellord2(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_24])).

cnf(c_330,plain,
    ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
    | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
    | ~ v3_ordinal1(X0)
    | ~ v1_relat_1(k1_wellord2(X0)) ),
    inference(unflattening,[status(thm)],[c_329])).

cnf(c_334,plain,
    ( ~ v3_ordinal1(X0)
    | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
    | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_330,c_22])).

cnf(c_335,plain,
    ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
    | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
    | ~ v3_ordinal1(X0) ),
    inference(renaming,[status(thm)],[c_334])).

cnf(c_1279,plain,
    ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
    | r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_335])).

cnf(c_21,plain,
    ( ~ v1_relat_1(k1_wellord2(X0))
    | k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_171,plain,
    ( k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_21,c_22])).

cnf(c_1306,plain,
    ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1279,c_171])).

cnf(c_10117,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) != iProver_top
    | r2_hidden(sK3,sK4) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_10114,c_1306])).

cnf(c_1994,plain,
    ( r2_hidden(sK4,sK3)
    | r2_hidden(sK3,sK4)
    | ~ v3_ordinal1(sK4)
    | ~ v3_ordinal1(sK3)
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1995,plain,
    ( sK3 = sK4
    | r2_hidden(sK4,sK3) = iProver_top
    | r2_hidden(sK3,sK4) = iProver_top
    | v3_ordinal1(sK4) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1994])).

cnf(c_6968,plain,
    ( ~ r2_hidden(sK4,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK4)
    | k1_wellord1(k1_wellord2(X0),sK4) = sK4 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_6969,plain,
    ( k1_wellord1(k1_wellord2(X0),sK4) = sK4
    | r2_hidden(sK4,X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6968])).

cnf(c_6971,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | r2_hidden(sK4,sK3) != iProver_top
    | v3_ordinal1(sK4) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6969])).

cnf(c_10192,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10117,c_30,c_31,c_26,c_1995,c_6971])).

cnf(c_12194,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
    | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12193,c_10192])).

cnf(c_42,plain,
    ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_44,plain,
    ( v1_relat_1(k1_wellord2(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_1449,plain,
    ( v1_relat_1(k1_wellord2(sK4)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1450,plain,
    ( v1_relat_1(k1_wellord2(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1449])).

cnf(c_27,negated_conjecture,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1282,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_13,plain,
    ( ~ r4_wellord1(X0,X1)
    | r4_wellord1(X1,X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1292,plain,
    ( r4_wellord1(X0,X1) != iProver_top
    | r4_wellord1(X1,X0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2646,plain,
    ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1282,c_1292])).

cnf(c_12236,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12194,c_44,c_1450,c_2646])).

cnf(c_12240,plain,
    ( r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK4)) != iProver_top
    | r2_hidden(sK4,sK3) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_12236,c_1306])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X0))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1293,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3244,plain,
    ( r2_hidden(sK3,sK3) != iProver_top
    | v1_relat_1(k1_wellord2(k2_xboole_0(sK3,k1_tarski(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2749,c_1293])).

cnf(c_3342,plain,
    ( r2_hidden(sK3,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1285,c_3244])).

cnf(c_12238,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k4_tarski(X0,sK4),k1_wellord2(sK3)) = iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12236,c_1294])).

cnf(c_12314,plain,
    ( r2_hidden(k4_tarski(X0,sK4),k1_wellord2(sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12238,c_44])).

cnf(c_12315,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k4_tarski(X0,sK4),k1_wellord2(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_12314])).

cnf(c_1,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1304,plain,
    ( r2_hidden(X0,k3_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_12323,plain,
    ( r2_hidden(X0,k3_relat_1(k1_wellord2(sK3))) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12315,c_1304])).

cnf(c_12331,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12323,c_171])).

cnf(c_12349,plain,
    ( r2_hidden(sK3,sK4) != iProver_top
    | r2_hidden(sK3,sK3) = iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12331])).

cnf(c_12355,plain,
    ( r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12240,c_30,c_31,c_26,c_44,c_1995,c_3342,c_12349])).

cnf(c_12359,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12234,c_12355])).

cnf(c_32,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_12382,plain,
    ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12359,c_32])).

cnf(c_12386,plain,
    ( r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) != iProver_top
    | r2_hidden(sK3,sK4) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_12382,c_1306])).

cnf(c_12530,plain,
    ( r2_hidden(sK3,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12386,c_44,c_3342,c_12349])).

cnf(c_12537,plain,
    ( sK4 = sK3
    | r2_hidden(sK4,sK3) = iProver_top
    | v3_ordinal1(sK4) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1300,c_12530])).

cnf(c_13296,plain,
    ( r2_hidden(sK4,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12537,c_30,c_31,c_26,c_44,c_1995,c_3342,c_12349])).

cnf(c_12384,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k4_tarski(X0,sK3),k1_wellord2(sK4)) = iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12382,c_1294])).

cnf(c_12390,plain,
    ( r2_hidden(k4_tarski(X0,sK3),k1_wellord2(sK4)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12384,c_1450])).

cnf(c_12391,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k4_tarski(X0,sK3),k1_wellord2(sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_12390])).

cnf(c_12397,plain,
    ( r2_hidden(X0,k3_relat_1(k1_wellord2(sK4))) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12391,c_1304])).

cnf(c_12405,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12397,c_171])).

cnf(c_0,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1305,plain,
    ( r2_hidden(X0,k3_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_12395,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(sK3,k3_relat_1(k1_wellord2(sK4))) = iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12391,c_1305])).

cnf(c_12406,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(sK3,sK4) = iProver_top
    | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12395,c_171])).

cnf(c_12782,plain,
    ( r2_hidden(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12405,c_44,c_1450,c_3342,c_12349,c_12406])).

cnf(c_13302,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_13296,c_12782])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:26:15 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 4.14/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.14/0.98  
% 4.14/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.14/0.98  
% 4.14/0.98  ------  iProver source info
% 4.14/0.98  
% 4.14/0.98  git: date: 2020-06-30 10:37:57 +0100
% 4.14/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.14/0.98  git: non_committed_changes: false
% 4.14/0.98  git: last_make_outside_of_git: false
% 4.14/0.98  
% 4.14/0.98  ------ 
% 4.14/0.98  
% 4.14/0.98  ------ Input Options
% 4.14/0.98  
% 4.14/0.98  --out_options                           all
% 4.14/0.98  --tptp_safe_out                         true
% 4.14/0.98  --problem_path                          ""
% 4.14/0.98  --include_path                          ""
% 4.14/0.98  --clausifier                            res/vclausify_rel
% 4.14/0.98  --clausifier_options                    ""
% 4.14/0.98  --stdin                                 false
% 4.14/0.98  --stats_out                             all
% 4.14/0.98  
% 4.14/0.98  ------ General Options
% 4.14/0.98  
% 4.14/0.98  --fof                                   false
% 4.14/0.98  --time_out_real                         305.
% 4.14/0.98  --time_out_virtual                      -1.
% 4.14/0.98  --symbol_type_check                     false
% 4.14/0.98  --clausify_out                          false
% 4.14/0.98  --sig_cnt_out                           false
% 4.14/0.98  --trig_cnt_out                          false
% 4.14/0.98  --trig_cnt_out_tolerance                1.
% 4.14/0.98  --trig_cnt_out_sk_spl                   false
% 4.14/0.98  --abstr_cl_out                          false
% 4.14/0.98  
% 4.14/0.98  ------ Global Options
% 4.14/0.98  
% 4.14/0.98  --schedule                              default
% 4.14/0.98  --add_important_lit                     false
% 4.14/0.98  --prop_solver_per_cl                    1000
% 4.14/0.98  --min_unsat_core                        false
% 4.14/0.98  --soft_assumptions                      false
% 4.14/0.98  --soft_lemma_size                       3
% 4.14/0.98  --prop_impl_unit_size                   0
% 4.14/0.98  --prop_impl_unit                        []
% 4.14/0.98  --share_sel_clauses                     true
% 4.14/0.98  --reset_solvers                         false
% 4.14/0.98  --bc_imp_inh                            [conj_cone]
% 4.14/0.98  --conj_cone_tolerance                   3.
% 4.14/0.98  --extra_neg_conj                        none
% 4.14/0.98  --large_theory_mode                     true
% 4.14/0.98  --prolific_symb_bound                   200
% 4.14/0.98  --lt_threshold                          2000
% 4.14/0.98  --clause_weak_htbl                      true
% 4.14/0.98  --gc_record_bc_elim                     false
% 4.14/0.98  
% 4.14/0.98  ------ Preprocessing Options
% 4.14/0.98  
% 4.14/0.98  --preprocessing_flag                    true
% 4.14/0.98  --time_out_prep_mult                    0.1
% 4.14/0.98  --splitting_mode                        input
% 4.14/0.98  --splitting_grd                         true
% 4.14/0.98  --splitting_cvd                         false
% 4.14/0.98  --splitting_cvd_svl                     false
% 4.14/0.98  --splitting_nvd                         32
% 4.14/0.98  --sub_typing                            true
% 4.14/0.98  --prep_gs_sim                           true
% 4.14/0.98  --prep_unflatten                        true
% 4.14/0.98  --prep_res_sim                          true
% 4.14/0.98  --prep_upred                            true
% 4.14/0.98  --prep_sem_filter                       exhaustive
% 4.14/0.98  --prep_sem_filter_out                   false
% 4.14/0.98  --pred_elim                             true
% 4.14/0.98  --res_sim_input                         true
% 4.14/0.98  --eq_ax_congr_red                       true
% 4.14/0.98  --pure_diseq_elim                       true
% 4.14/0.98  --brand_transform                       false
% 4.14/0.98  --non_eq_to_eq                          false
% 4.14/0.98  --prep_def_merge                        true
% 4.14/0.98  --prep_def_merge_prop_impl              false
% 4.14/0.98  --prep_def_merge_mbd                    true
% 4.14/0.98  --prep_def_merge_tr_red                 false
% 4.14/0.98  --prep_def_merge_tr_cl                  false
% 4.14/0.98  --smt_preprocessing                     true
% 4.14/0.98  --smt_ac_axioms                         fast
% 4.14/0.98  --preprocessed_out                      false
% 4.14/0.98  --preprocessed_stats                    false
% 4.14/0.98  
% 4.14/0.98  ------ Abstraction refinement Options
% 4.14/0.98  
% 4.14/0.98  --abstr_ref                             []
% 4.14/0.98  --abstr_ref_prep                        false
% 4.14/0.98  --abstr_ref_until_sat                   false
% 4.14/0.98  --abstr_ref_sig_restrict                funpre
% 4.14/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 4.14/0.98  --abstr_ref_under                       []
% 4.14/0.98  
% 4.14/0.98  ------ SAT Options
% 4.14/0.98  
% 4.14/0.98  --sat_mode                              false
% 4.14/0.98  --sat_fm_restart_options                ""
% 4.14/0.98  --sat_gr_def                            false
% 4.14/0.98  --sat_epr_types                         true
% 4.14/0.98  --sat_non_cyclic_types                  false
% 4.14/0.98  --sat_finite_models                     false
% 4.14/0.98  --sat_fm_lemmas                         false
% 4.14/0.98  --sat_fm_prep                           false
% 4.14/0.98  --sat_fm_uc_incr                        true
% 4.14/0.98  --sat_out_model                         small
% 4.14/0.98  --sat_out_clauses                       false
% 4.14/0.98  
% 4.14/0.98  ------ QBF Options
% 4.14/0.98  
% 4.14/0.98  --qbf_mode                              false
% 4.14/0.98  --qbf_elim_univ                         false
% 4.14/0.98  --qbf_dom_inst                          none
% 4.14/0.98  --qbf_dom_pre_inst                      false
% 4.14/0.98  --qbf_sk_in                             false
% 4.14/0.98  --qbf_pred_elim                         true
% 4.14/0.98  --qbf_split                             512
% 4.14/0.98  
% 4.14/0.98  ------ BMC1 Options
% 4.14/0.98  
% 4.14/0.98  --bmc1_incremental                      false
% 4.14/0.98  --bmc1_axioms                           reachable_all
% 4.14/0.98  --bmc1_min_bound                        0
% 4.14/0.98  --bmc1_max_bound                        -1
% 4.14/0.98  --bmc1_max_bound_default                -1
% 4.14/0.98  --bmc1_symbol_reachability              true
% 4.14/0.98  --bmc1_property_lemmas                  false
% 4.14/0.98  --bmc1_k_induction                      false
% 4.14/0.98  --bmc1_non_equiv_states                 false
% 4.14/0.98  --bmc1_deadlock                         false
% 4.14/0.98  --bmc1_ucm                              false
% 4.14/0.98  --bmc1_add_unsat_core                   none
% 4.14/0.98  --bmc1_unsat_core_children              false
% 4.14/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 4.14/0.98  --bmc1_out_stat                         full
% 4.14/0.98  --bmc1_ground_init                      false
% 4.14/0.98  --bmc1_pre_inst_next_state              false
% 4.14/0.98  --bmc1_pre_inst_state                   false
% 4.14/0.98  --bmc1_pre_inst_reach_state             false
% 4.14/0.98  --bmc1_out_unsat_core                   false
% 4.14/0.98  --bmc1_aig_witness_out                  false
% 4.14/0.98  --bmc1_verbose                          false
% 4.14/0.98  --bmc1_dump_clauses_tptp                false
% 4.14/0.98  --bmc1_dump_unsat_core_tptp             false
% 4.14/0.98  --bmc1_dump_file                        -
% 4.14/0.98  --bmc1_ucm_expand_uc_limit              128
% 4.14/0.98  --bmc1_ucm_n_expand_iterations          6
% 4.14/0.98  --bmc1_ucm_extend_mode                  1
% 4.14/0.98  --bmc1_ucm_init_mode                    2
% 4.14/0.98  --bmc1_ucm_cone_mode                    none
% 4.14/0.98  --bmc1_ucm_reduced_relation_type        0
% 4.14/0.98  --bmc1_ucm_relax_model                  4
% 4.14/0.98  --bmc1_ucm_full_tr_after_sat            true
% 4.14/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 4.14/0.98  --bmc1_ucm_layered_model                none
% 4.14/0.98  --bmc1_ucm_max_lemma_size               10
% 4.14/0.98  
% 4.14/0.98  ------ AIG Options
% 4.14/0.98  
% 4.14/0.98  --aig_mode                              false
% 4.14/0.98  
% 4.14/0.98  ------ Instantiation Options
% 4.14/0.98  
% 4.14/0.98  --instantiation_flag                    true
% 4.14/0.98  --inst_sos_flag                         true
% 4.14/0.98  --inst_sos_phase                        true
% 4.14/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.14/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.14/0.98  --inst_lit_sel_side                     num_symb
% 4.14/0.98  --inst_solver_per_active                1400
% 4.14/0.98  --inst_solver_calls_frac                1.
% 4.14/0.98  --inst_passive_queue_type               priority_queues
% 4.14/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.14/0.98  --inst_passive_queues_freq              [25;2]
% 4.14/0.98  --inst_dismatching                      true
% 4.14/0.98  --inst_eager_unprocessed_to_passive     true
% 4.14/0.98  --inst_prop_sim_given                   true
% 4.14/0.98  --inst_prop_sim_new                     false
% 4.14/0.98  --inst_subs_new                         false
% 4.14/0.98  --inst_eq_res_simp                      false
% 4.14/0.98  --inst_subs_given                       false
% 4.14/0.98  --inst_orphan_elimination               true
% 4.14/0.98  --inst_learning_loop_flag               true
% 4.14/0.98  --inst_learning_start                   3000
% 4.14/0.98  --inst_learning_factor                  2
% 4.14/0.98  --inst_start_prop_sim_after_learn       3
% 4.14/0.98  --inst_sel_renew                        solver
% 4.14/0.98  --inst_lit_activity_flag                true
% 4.14/0.98  --inst_restr_to_given                   false
% 4.14/0.98  --inst_activity_threshold               500
% 4.14/0.98  --inst_out_proof                        true
% 4.14/0.98  
% 4.14/0.98  ------ Resolution Options
% 4.14/0.98  
% 4.14/0.98  --resolution_flag                       true
% 4.14/0.98  --res_lit_sel                           adaptive
% 4.14/0.98  --res_lit_sel_side                      none
% 4.14/0.98  --res_ordering                          kbo
% 4.14/0.98  --res_to_prop_solver                    active
% 4.14/0.98  --res_prop_simpl_new                    false
% 4.14/0.98  --res_prop_simpl_given                  true
% 4.14/0.98  --res_passive_queue_type                priority_queues
% 4.14/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.14/0.98  --res_passive_queues_freq               [15;5]
% 4.14/0.98  --res_forward_subs                      full
% 4.14/0.98  --res_backward_subs                     full
% 4.14/0.98  --res_forward_subs_resolution           true
% 4.14/0.98  --res_backward_subs_resolution          true
% 4.14/0.98  --res_orphan_elimination                true
% 4.14/0.98  --res_time_limit                        2.
% 4.14/0.98  --res_out_proof                         true
% 4.14/0.98  
% 4.14/0.98  ------ Superposition Options
% 4.14/0.98  
% 4.14/0.98  --superposition_flag                    true
% 4.14/0.98  --sup_passive_queue_type                priority_queues
% 4.14/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.14/0.98  --sup_passive_queues_freq               [8;1;4]
% 4.14/0.98  --demod_completeness_check              fast
% 4.14/0.98  --demod_use_ground                      true
% 4.14/0.98  --sup_to_prop_solver                    passive
% 4.14/0.98  --sup_prop_simpl_new                    true
% 4.14/0.98  --sup_prop_simpl_given                  true
% 4.14/0.98  --sup_fun_splitting                     true
% 4.14/0.98  --sup_smt_interval                      50000
% 4.14/0.98  
% 4.14/0.98  ------ Superposition Simplification Setup
% 4.14/0.98  
% 4.14/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.14/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.14/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.14/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.14/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 4.14/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.14/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.14/0.98  --sup_immed_triv                        [TrivRules]
% 4.14/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.14/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.14/0.98  --sup_immed_bw_main                     []
% 4.14/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.14/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 4.14/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.14/0.98  --sup_input_bw                          []
% 4.14/0.98  
% 4.14/0.98  ------ Combination Options
% 4.14/0.98  
% 4.14/0.98  --comb_res_mult                         3
% 4.14/0.98  --comb_sup_mult                         2
% 4.14/0.98  --comb_inst_mult                        10
% 4.14/0.98  
% 4.14/0.98  ------ Debug Options
% 4.14/0.98  
% 4.14/0.98  --dbg_backtrace                         false
% 4.14/0.98  --dbg_dump_prop_clauses                 false
% 4.14/0.98  --dbg_dump_prop_clauses_file            -
% 4.14/0.98  --dbg_out_stat                          false
% 4.14/0.98  ------ Parsing...
% 4.14/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.14/0.98  
% 4.14/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 4.14/0.98  
% 4.14/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.14/0.98  
% 4.14/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.14/0.98  ------ Proving...
% 4.14/0.98  ------ Problem Properties 
% 4.14/0.98  
% 4.14/0.98  
% 4.14/0.98  clauses                                 29
% 4.14/0.98  conjectures                             4
% 4.14/0.98  EPR                                     5
% 4.14/0.98  Horn                                    20
% 4.14/0.98  unary                                   7
% 4.14/0.98  binary                                  4
% 4.14/0.98  lits                                    84
% 4.14/0.98  lits eq                                 16
% 4.14/0.98  fd_pure                                 0
% 4.14/0.98  fd_pseudo                               0
% 4.14/0.98  fd_cond                                 0
% 4.14/0.98  fd_pseudo_cond                          5
% 4.14/0.98  AC symbols                              0
% 4.14/0.98  
% 4.14/0.98  ------ Schedule dynamic 5 is on 
% 4.14/0.98  
% 4.14/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.14/0.98  
% 4.14/0.98  
% 4.14/0.98  ------ 
% 4.14/0.98  Current options:
% 4.14/0.98  ------ 
% 4.14/0.98  
% 4.14/0.98  ------ Input Options
% 4.14/0.98  
% 4.14/0.98  --out_options                           all
% 4.14/0.98  --tptp_safe_out                         true
% 4.14/0.98  --problem_path                          ""
% 4.14/0.98  --include_path                          ""
% 4.14/0.98  --clausifier                            res/vclausify_rel
% 4.14/0.98  --clausifier_options                    ""
% 4.14/0.98  --stdin                                 false
% 4.14/0.98  --stats_out                             all
% 4.14/0.98  
% 4.14/0.98  ------ General Options
% 4.14/0.98  
% 4.14/0.98  --fof                                   false
% 4.14/0.98  --time_out_real                         305.
% 4.14/0.98  --time_out_virtual                      -1.
% 4.14/0.98  --symbol_type_check                     false
% 4.14/0.98  --clausify_out                          false
% 4.14/0.98  --sig_cnt_out                           false
% 4.14/0.98  --trig_cnt_out                          false
% 4.14/0.98  --trig_cnt_out_tolerance                1.
% 4.14/0.98  --trig_cnt_out_sk_spl                   false
% 4.14/0.98  --abstr_cl_out                          false
% 4.14/0.98  
% 4.14/0.98  ------ Global Options
% 4.14/0.98  
% 4.14/0.98  --schedule                              default
% 4.14/0.98  --add_important_lit                     false
% 4.14/0.98  --prop_solver_per_cl                    1000
% 4.14/0.98  --min_unsat_core                        false
% 4.14/0.98  --soft_assumptions                      false
% 4.14/0.98  --soft_lemma_size                       3
% 4.14/0.98  --prop_impl_unit_size                   0
% 4.14/0.98  --prop_impl_unit                        []
% 4.14/0.98  --share_sel_clauses                     true
% 4.14/0.98  --reset_solvers                         false
% 4.14/0.98  --bc_imp_inh                            [conj_cone]
% 4.14/0.98  --conj_cone_tolerance                   3.
% 4.14/0.98  --extra_neg_conj                        none
% 4.14/0.98  --large_theory_mode                     true
% 4.14/0.98  --prolific_symb_bound                   200
% 4.14/0.98  --lt_threshold                          2000
% 4.14/0.98  --clause_weak_htbl                      true
% 4.14/0.98  --gc_record_bc_elim                     false
% 4.14/0.98  
% 4.14/0.98  ------ Preprocessing Options
% 4.14/0.98  
% 4.14/0.98  --preprocessing_flag                    true
% 4.14/0.98  --time_out_prep_mult                    0.1
% 4.14/0.98  --splitting_mode                        input
% 4.14/0.98  --splitting_grd                         true
% 4.14/0.98  --splitting_cvd                         false
% 4.14/0.98  --splitting_cvd_svl                     false
% 4.14/0.98  --splitting_nvd                         32
% 4.14/0.98  --sub_typing                            true
% 4.14/0.98  --prep_gs_sim                           true
% 4.14/0.98  --prep_unflatten                        true
% 4.14/0.98  --prep_res_sim                          true
% 4.14/0.98  --prep_upred                            true
% 4.14/0.98  --prep_sem_filter                       exhaustive
% 4.14/0.98  --prep_sem_filter_out                   false
% 4.14/0.98  --pred_elim                             true
% 4.14/0.98  --res_sim_input                         true
% 4.14/0.98  --eq_ax_congr_red                       true
% 4.14/0.98  --pure_diseq_elim                       true
% 4.14/0.98  --brand_transform                       false
% 4.14/0.98  --non_eq_to_eq                          false
% 4.14/0.98  --prep_def_merge                        true
% 4.14/0.98  --prep_def_merge_prop_impl              false
% 4.14/0.98  --prep_def_merge_mbd                    true
% 4.14/0.98  --prep_def_merge_tr_red                 false
% 4.14/0.98  --prep_def_merge_tr_cl                  false
% 4.14/0.98  --smt_preprocessing                     true
% 4.14/0.98  --smt_ac_axioms                         fast
% 4.14/0.98  --preprocessed_out                      false
% 4.14/0.98  --preprocessed_stats                    false
% 4.14/0.98  
% 4.14/0.98  ------ Abstraction refinement Options
% 4.14/0.98  
% 4.14/0.98  --abstr_ref                             []
% 4.14/0.98  --abstr_ref_prep                        false
% 4.14/0.98  --abstr_ref_until_sat                   false
% 4.14/0.98  --abstr_ref_sig_restrict                funpre
% 4.14/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 4.14/0.98  --abstr_ref_under                       []
% 4.14/0.98  
% 4.14/0.98  ------ SAT Options
% 4.14/0.98  
% 4.14/0.98  --sat_mode                              false
% 4.14/0.98  --sat_fm_restart_options                ""
% 4.14/0.98  --sat_gr_def                            false
% 4.14/0.98  --sat_epr_types                         true
% 4.14/0.98  --sat_non_cyclic_types                  false
% 4.14/0.98  --sat_finite_models                     false
% 4.14/0.98  --sat_fm_lemmas                         false
% 4.14/0.98  --sat_fm_prep                           false
% 4.14/0.98  --sat_fm_uc_incr                        true
% 4.14/0.98  --sat_out_model                         small
% 4.14/0.98  --sat_out_clauses                       false
% 4.14/0.98  
% 4.14/0.98  ------ QBF Options
% 4.14/0.98  
% 4.14/0.98  --qbf_mode                              false
% 4.14/0.98  --qbf_elim_univ                         false
% 4.14/0.98  --qbf_dom_inst                          none
% 4.14/0.98  --qbf_dom_pre_inst                      false
% 4.14/0.98  --qbf_sk_in                             false
% 4.14/0.98  --qbf_pred_elim                         true
% 4.14/0.98  --qbf_split                             512
% 4.14/0.98  
% 4.14/0.98  ------ BMC1 Options
% 4.14/0.98  
% 4.14/0.98  --bmc1_incremental                      false
% 4.14/0.98  --bmc1_axioms                           reachable_all
% 4.14/0.98  --bmc1_min_bound                        0
% 4.14/0.98  --bmc1_max_bound                        -1
% 4.14/0.98  --bmc1_max_bound_default                -1
% 4.14/0.98  --bmc1_symbol_reachability              true
% 4.14/0.98  --bmc1_property_lemmas                  false
% 4.14/0.98  --bmc1_k_induction                      false
% 4.14/0.98  --bmc1_non_equiv_states                 false
% 4.14/0.98  --bmc1_deadlock                         false
% 4.14/0.98  --bmc1_ucm                              false
% 4.14/0.98  --bmc1_add_unsat_core                   none
% 4.14/0.98  --bmc1_unsat_core_children              false
% 4.14/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 4.14/0.98  --bmc1_out_stat                         full
% 4.14/0.98  --bmc1_ground_init                      false
% 4.14/0.98  --bmc1_pre_inst_next_state              false
% 4.14/0.98  --bmc1_pre_inst_state                   false
% 4.14/0.98  --bmc1_pre_inst_reach_state             false
% 4.14/0.98  --bmc1_out_unsat_core                   false
% 4.14/0.98  --bmc1_aig_witness_out                  false
% 4.14/0.98  --bmc1_verbose                          false
% 4.14/0.98  --bmc1_dump_clauses_tptp                false
% 4.14/0.98  --bmc1_dump_unsat_core_tptp             false
% 4.14/0.98  --bmc1_dump_file                        -
% 4.14/0.98  --bmc1_ucm_expand_uc_limit              128
% 4.14/0.98  --bmc1_ucm_n_expand_iterations          6
% 4.14/0.98  --bmc1_ucm_extend_mode                  1
% 4.14/0.98  --bmc1_ucm_init_mode                    2
% 4.14/0.98  --bmc1_ucm_cone_mode                    none
% 4.14/0.98  --bmc1_ucm_reduced_relation_type        0
% 4.14/0.98  --bmc1_ucm_relax_model                  4
% 4.14/0.98  --bmc1_ucm_full_tr_after_sat            true
% 4.14/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 4.14/0.98  --bmc1_ucm_layered_model                none
% 4.14/0.98  --bmc1_ucm_max_lemma_size               10
% 4.14/0.98  
% 4.14/0.98  ------ AIG Options
% 4.14/0.98  
% 4.14/0.98  --aig_mode                              false
% 4.14/0.98  
% 4.14/0.98  ------ Instantiation Options
% 4.14/0.98  
% 4.14/0.98  --instantiation_flag                    true
% 4.14/0.98  --inst_sos_flag                         true
% 4.14/0.98  --inst_sos_phase                        true
% 4.14/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.14/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.14/0.98  --inst_lit_sel_side                     none
% 4.14/0.98  --inst_solver_per_active                1400
% 4.14/0.98  --inst_solver_calls_frac                1.
% 4.14/0.98  --inst_passive_queue_type               priority_queues
% 4.14/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.14/0.98  --inst_passive_queues_freq              [25;2]
% 4.14/0.98  --inst_dismatching                      true
% 4.14/0.98  --inst_eager_unprocessed_to_passive     true
% 4.14/0.98  --inst_prop_sim_given                   true
% 4.14/0.98  --inst_prop_sim_new                     false
% 4.14/0.98  --inst_subs_new                         false
% 4.14/0.98  --inst_eq_res_simp                      false
% 4.14/0.98  --inst_subs_given                       false
% 4.14/0.98  --inst_orphan_elimination               true
% 4.14/0.98  --inst_learning_loop_flag               true
% 4.14/0.98  --inst_learning_start                   3000
% 4.14/0.98  --inst_learning_factor                  2
% 4.14/0.98  --inst_start_prop_sim_after_learn       3
% 4.14/0.98  --inst_sel_renew                        solver
% 4.14/0.98  --inst_lit_activity_flag                true
% 4.14/0.98  --inst_restr_to_given                   false
% 4.14/0.98  --inst_activity_threshold               500
% 4.14/0.98  --inst_out_proof                        true
% 4.14/0.98  
% 4.14/0.98  ------ Resolution Options
% 4.14/0.98  
% 4.14/0.98  --resolution_flag                       false
% 4.14/0.98  --res_lit_sel                           adaptive
% 4.14/0.98  --res_lit_sel_side                      none
% 4.14/0.98  --res_ordering                          kbo
% 4.14/0.98  --res_to_prop_solver                    active
% 4.14/0.98  --res_prop_simpl_new                    false
% 4.14/0.98  --res_prop_simpl_given                  true
% 4.14/0.98  --res_passive_queue_type                priority_queues
% 4.14/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.14/0.98  --res_passive_queues_freq               [15;5]
% 4.14/0.98  --res_forward_subs                      full
% 4.14/0.98  --res_backward_subs                     full
% 4.14/0.98  --res_forward_subs_resolution           true
% 4.14/0.98  --res_backward_subs_resolution          true
% 4.14/0.98  --res_orphan_elimination                true
% 4.14/0.98  --res_time_limit                        2.
% 4.14/0.98  --res_out_proof                         true
% 4.14/0.98  
% 4.14/0.98  ------ Superposition Options
% 4.14/0.98  
% 4.14/0.98  --superposition_flag                    true
% 4.14/0.98  --sup_passive_queue_type                priority_queues
% 4.14/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.14/0.98  --sup_passive_queues_freq               [8;1;4]
% 4.14/0.98  --demod_completeness_check              fast
% 4.14/0.98  --demod_use_ground                      true
% 4.14/0.98  --sup_to_prop_solver                    passive
% 4.14/0.98  --sup_prop_simpl_new                    true
% 4.14/0.98  --sup_prop_simpl_given                  true
% 4.14/0.98  --sup_fun_splitting                     true
% 4.14/0.98  --sup_smt_interval                      50000
% 4.14/0.98  
% 4.14/0.98  ------ Superposition Simplification Setup
% 4.14/0.98  
% 4.14/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.14/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.14/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.14/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.14/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 4.14/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.14/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.14/0.98  --sup_immed_triv                        [TrivRules]
% 4.14/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.14/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.14/0.98  --sup_immed_bw_main                     []
% 4.14/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.14/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 4.14/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.14/0.98  --sup_input_bw                          []
% 4.14/0.98  
% 4.14/0.98  ------ Combination Options
% 4.14/0.98  
% 4.14/0.98  --comb_res_mult                         3
% 4.14/0.98  --comb_sup_mult                         2
% 4.14/0.98  --comb_inst_mult                        10
% 4.14/0.98  
% 4.14/0.98  ------ Debug Options
% 4.14/0.98  
% 4.14/0.98  --dbg_backtrace                         false
% 4.14/0.98  --dbg_dump_prop_clauses                 false
% 4.14/0.98  --dbg_dump_prop_clauses_file            -
% 4.14/0.98  --dbg_out_stat                          false
% 4.14/0.98  
% 4.14/0.98  
% 4.14/0.98  
% 4.14/0.98  
% 4.14/0.98  ------ Proving...
% 4.14/0.98  
% 4.14/0.98  
% 4.14/0.98  % SZS status Theorem for theBenchmark.p
% 4.14/0.98  
% 4.14/0.98   Resolution empty clause
% 4.14/0.98  
% 4.14/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 4.14/0.98  
% 4.14/0.98  fof(f4,axiom,(
% 4.14/0.98    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 4.14/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.14/0.98  
% 4.14/0.98  fof(f18,plain,(
% 4.14/0.98    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 4.14/0.98    inference(ennf_transformation,[],[f4])).
% 4.14/0.98  
% 4.14/0.98  fof(f19,plain,(
% 4.14/0.98    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 4.14/0.98    inference(flattening,[],[f18])).
% 4.14/0.98  
% 4.14/0.98  fof(f55,plain,(
% 4.14/0.98    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 4.14/0.98    inference(cnf_transformation,[],[f19])).
% 4.14/0.98  
% 4.14/0.98  fof(f14,conjecture,(
% 4.14/0.98    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 4.14/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.14/0.98  
% 4.14/0.98  fof(f15,negated_conjecture,(
% 4.14/0.98    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 4.14/0.98    inference(negated_conjecture,[],[f14])).
% 4.14/0.98  
% 4.14/0.98  fof(f32,plain,(
% 4.14/0.98    ? [X0] : (? [X1] : ((X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 4.14/0.98    inference(ennf_transformation,[],[f15])).
% 4.14/0.98  
% 4.14/0.98  fof(f33,plain,(
% 4.14/0.98    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 4.14/0.98    inference(flattening,[],[f32])).
% 4.14/0.98  
% 4.14/0.98  fof(f47,plain,(
% 4.14/0.98    ( ! [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) => (sK4 != X0 & r4_wellord1(k1_wellord2(X0),k1_wellord2(sK4)) & v3_ordinal1(sK4))) )),
% 4.14/0.98    introduced(choice_axiom,[])).
% 4.14/0.98  
% 4.14/0.98  fof(f46,plain,(
% 4.14/0.98    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : (sK3 != X1 & r4_wellord1(k1_wellord2(sK3),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK3))),
% 4.14/0.98    introduced(choice_axiom,[])).
% 4.14/0.98  
% 4.14/0.98  fof(f48,plain,(
% 4.14/0.98    (sK3 != sK4 & r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) & v3_ordinal1(sK4)) & v3_ordinal1(sK3)),
% 4.14/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f33,f47,f46])).
% 4.14/0.98  
% 4.14/0.98  fof(f77,plain,(
% 4.14/0.98    v3_ordinal1(sK4)),
% 4.14/0.98    inference(cnf_transformation,[],[f48])).
% 4.14/0.98  
% 4.14/0.98  fof(f3,axiom,(
% 4.14/0.98    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 4.14/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.14/0.98  
% 4.14/0.98  fof(f34,plain,(
% 4.14/0.98    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 4.14/0.98    inference(nnf_transformation,[],[f3])).
% 4.14/0.98  
% 4.14/0.98  fof(f35,plain,(
% 4.14/0.98    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 4.14/0.98    inference(flattening,[],[f34])).
% 4.14/0.98  
% 4.14/0.98  fof(f53,plain,(
% 4.14/0.98    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 4.14/0.98    inference(cnf_transformation,[],[f35])).
% 4.14/0.98  
% 4.14/0.98  fof(f2,axiom,(
% 4.14/0.98    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 4.14/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.14/0.98  
% 4.14/0.98  fof(f51,plain,(
% 4.14/0.98    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 4.14/0.98    inference(cnf_transformation,[],[f2])).
% 4.14/0.98  
% 4.14/0.98  fof(f81,plain,(
% 4.14/0.98    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r2_hidden(X0,X1)) )),
% 4.14/0.98    inference(definition_unfolding,[],[f53,f51])).
% 4.14/0.98  
% 4.14/0.98  fof(f10,axiom,(
% 4.14/0.98    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 4.14/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.14/0.98  
% 4.14/0.98  fof(f72,plain,(
% 4.14/0.98    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 4.14/0.98    inference(cnf_transformation,[],[f10])).
% 4.14/0.98  
% 4.14/0.98  fof(f76,plain,(
% 4.14/0.98    v3_ordinal1(sK3)),
% 4.14/0.98    inference(cnf_transformation,[],[f48])).
% 4.14/0.98  
% 4.14/0.98  fof(f54,plain,(
% 4.14/0.98    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 4.14/0.98    inference(cnf_transformation,[],[f35])).
% 4.14/0.98  
% 4.14/0.98  fof(f80,plain,(
% 4.14/0.98    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | X0 != X1) )),
% 4.14/0.98    inference(definition_unfolding,[],[f54,f51])).
% 4.14/0.98  
% 4.14/0.98  fof(f84,plain,(
% 4.14/0.98    ( ! [X1] : (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 4.14/0.98    inference(equality_resolution,[],[f80])).
% 4.14/0.98  
% 4.14/0.98  fof(f11,axiom,(
% 4.14/0.98    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => k1_wellord1(k1_wellord2(X1),X0) = X0)))),
% 4.14/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.14/0.98  
% 4.14/0.98  fof(f28,plain,(
% 4.14/0.98    ! [X0] : (! [X1] : ((k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 4.14/0.98    inference(ennf_transformation,[],[f11])).
% 4.14/0.98  
% 4.14/0.98  fof(f29,plain,(
% 4.14/0.98    ! [X0] : (! [X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 4.14/0.98    inference(flattening,[],[f28])).
% 4.14/0.98  
% 4.14/0.98  fof(f73,plain,(
% 4.14/0.98    ( ! [X0,X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 4.14/0.98    inference(cnf_transformation,[],[f29])).
% 4.14/0.98  
% 4.14/0.98  fof(f5,axiom,(
% 4.14/0.98    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 4.14/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.14/0.98  
% 4.14/0.98  fof(f20,plain,(
% 4.14/0.98    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 4.14/0.98    inference(ennf_transformation,[],[f5])).
% 4.14/0.98  
% 4.14/0.98  fof(f56,plain,(
% 4.14/0.98    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 4.14/0.98    inference(cnf_transformation,[],[f20])).
% 4.14/0.98  
% 4.14/0.98  fof(f83,plain,(
% 4.14/0.98    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 4.14/0.98    inference(definition_unfolding,[],[f56,f51])).
% 4.14/0.98  
% 4.14/0.98  fof(f6,axiom,(
% 4.14/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 4.14/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.14/0.98  
% 4.14/0.98  fof(f21,plain,(
% 4.14/0.98    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 4.14/0.98    inference(ennf_transformation,[],[f6])).
% 4.14/0.98  
% 4.14/0.98  fof(f36,plain,(
% 4.14/0.98    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 4.14/0.98    inference(nnf_transformation,[],[f21])).
% 4.14/0.98  
% 4.14/0.98  fof(f37,plain,(
% 4.14/0.98    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 4.14/0.98    inference(flattening,[],[f36])).
% 4.14/0.98  
% 4.14/0.98  fof(f38,plain,(
% 4.14/0.98    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 4.14/0.98    inference(rectify,[],[f37])).
% 4.14/0.98  
% 4.14/0.98  fof(f39,plain,(
% 4.14/0.98    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2))) => ((~r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0) | sK0(X0,X1,X2) = X1 | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0) & sK0(X0,X1,X2) != X1) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 4.14/0.98    introduced(choice_axiom,[])).
% 4.14/0.98  
% 4.14/0.98  fof(f40,plain,(
% 4.14/0.98    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0) | sK0(X0,X1,X2) = X1 | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK0(X0,X1,X2),X1),X0) & sK0(X0,X1,X2) != X1) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 4.14/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).
% 4.14/0.98  
% 4.14/0.98  fof(f58,plain,(
% 4.14/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 4.14/0.98    inference(cnf_transformation,[],[f40])).
% 4.14/0.98  
% 4.14/0.98  fof(f86,plain,(
% 4.14/0.98    ( ! [X4,X0,X1] : (r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(X4,k1_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 4.14/0.98    inference(equality_resolution,[],[f58])).
% 4.14/0.98  
% 4.14/0.98  fof(f9,axiom,(
% 4.14/0.98    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 4.14/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.14/0.98  
% 4.14/0.98  fof(f26,plain,(
% 4.14/0.98    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 4.14/0.98    inference(ennf_transformation,[],[f9])).
% 4.14/0.98  
% 4.14/0.98  fof(f27,plain,(
% 4.14/0.98    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 4.14/0.98    inference(flattening,[],[f26])).
% 4.14/0.98  
% 4.14/0.98  fof(f41,plain,(
% 4.14/0.98    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 4.14/0.98    inference(nnf_transformation,[],[f27])).
% 4.14/0.98  
% 4.14/0.98  fof(f42,plain,(
% 4.14/0.98    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 4.14/0.98    inference(flattening,[],[f41])).
% 4.14/0.98  
% 4.14/0.98  fof(f43,plain,(
% 4.14/0.98    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 4.14/0.98    inference(rectify,[],[f42])).
% 4.14/0.98  
% 4.14/0.98  fof(f44,plain,(
% 4.14/0.98    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK1(X0,X1),sK2(X0,X1)) | ~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)) & (r1_tarski(sK1(X0,X1),sK2(X0,X1)) | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)) & r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),X0)))),
% 4.14/0.98    introduced(choice_axiom,[])).
% 4.14/0.98  
% 4.14/0.98  fof(f45,plain,(
% 4.14/0.98    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK1(X0,X1),sK2(X0,X1)) | ~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)) & (r1_tarski(sK1(X0,X1),sK2(X0,X1)) | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)) & r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 4.14/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f43,f44])).
% 4.14/0.98  
% 4.14/0.98  fof(f66,plain,(
% 4.14/0.98    ( ! [X4,X0,X5,X1] : (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 4.14/0.98    inference(cnf_transformation,[],[f45])).
% 4.14/0.98  
% 4.14/0.98  fof(f94,plain,(
% 4.14/0.98    ( ! [X4,X0,X5] : (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0)) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | ~v1_relat_1(k1_wellord2(X0))) )),
% 4.14/0.98    inference(equality_resolution,[],[f66])).
% 4.14/0.98  
% 4.14/0.98  fof(f13,axiom,(
% 4.14/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0))),
% 4.14/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.14/0.98  
% 4.14/0.98  fof(f31,plain,(
% 4.14/0.98    ! [X0,X1] : (k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) | ~r1_tarski(X0,X1))),
% 4.14/0.98    inference(ennf_transformation,[],[f13])).
% 4.14/0.98  
% 4.14/0.98  fof(f75,plain,(
% 4.14/0.98    ( ! [X0,X1] : (k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) | ~r1_tarski(X0,X1)) )),
% 4.14/0.98    inference(cnf_transformation,[],[f31])).
% 4.14/0.98  
% 4.14/0.98  fof(f79,plain,(
% 4.14/0.98    sK3 != sK4),
% 4.14/0.98    inference(cnf_transformation,[],[f48])).
% 4.14/0.98  
% 4.14/0.98  fof(f8,axiom,(
% 4.14/0.98    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 4.14/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.14/0.98  
% 4.14/0.98  fof(f24,plain,(
% 4.14/0.98    ! [X0] : ((! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 4.14/0.98    inference(ennf_transformation,[],[f8])).
% 4.14/0.98  
% 4.14/0.98  fof(f25,plain,(
% 4.14/0.98    ! [X0] : (! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 4.14/0.98    inference(flattening,[],[f24])).
% 4.14/0.98  
% 4.14/0.98  fof(f64,plain,(
% 4.14/0.98    ( ! [X0,X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0)) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 4.14/0.98    inference(cnf_transformation,[],[f25])).
% 4.14/0.98  
% 4.14/0.98  fof(f12,axiom,(
% 4.14/0.98    ! [X0] : (v3_ordinal1(X0) => v2_wellord1(k1_wellord2(X0)))),
% 4.14/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.14/0.98  
% 4.14/0.98  fof(f30,plain,(
% 4.14/0.98    ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0))),
% 4.14/0.98    inference(ennf_transformation,[],[f12])).
% 4.14/0.98  
% 4.14/0.98  fof(f74,plain,(
% 4.14/0.98    ( ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 4.14/0.98    inference(cnf_transformation,[],[f30])).
% 4.14/0.98  
% 4.14/0.98  fof(f65,plain,(
% 4.14/0.98    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 4.14/0.98    inference(cnf_transformation,[],[f45])).
% 4.14/0.98  
% 4.14/0.98  fof(f95,plain,(
% 4.14/0.98    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 4.14/0.98    inference(equality_resolution,[],[f65])).
% 4.14/0.98  
% 4.14/0.98  fof(f78,plain,(
% 4.14/0.98    r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4))),
% 4.14/0.98    inference(cnf_transformation,[],[f48])).
% 4.14/0.98  
% 4.14/0.98  fof(f7,axiom,(
% 4.14/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 4.14/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.14/0.98  
% 4.14/0.98  fof(f22,plain,(
% 4.14/0.98    ! [X0] : (! [X1] : ((r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 4.14/0.98    inference(ennf_transformation,[],[f7])).
% 4.14/0.98  
% 4.14/0.98  fof(f23,plain,(
% 4.14/0.98    ! [X0] : (! [X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 4.14/0.98    inference(flattening,[],[f22])).
% 4.14/0.98  
% 4.14/0.98  fof(f63,plain,(
% 4.14/0.98    ( ! [X0,X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 4.14/0.98    inference(cnf_transformation,[],[f23])).
% 4.14/0.98  
% 4.14/0.98  fof(f57,plain,(
% 4.14/0.98    ( ! [X4,X2,X0,X1] : (X1 != X4 | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 4.14/0.98    inference(cnf_transformation,[],[f40])).
% 4.14/0.98  
% 4.14/0.98  fof(f87,plain,(
% 4.14/0.98    ( ! [X4,X2,X0] : (~r2_hidden(X4,X2) | k1_wellord1(X0,X4) != X2 | ~v1_relat_1(X0)) )),
% 4.14/0.98    inference(equality_resolution,[],[f57])).
% 4.14/0.98  
% 4.14/0.98  fof(f88,plain,(
% 4.14/0.98    ( ! [X4,X0] : (~r2_hidden(X4,k1_wellord1(X0,X4)) | ~v1_relat_1(X0)) )),
% 4.14/0.98    inference(equality_resolution,[],[f87])).
% 4.14/0.98  
% 4.14/0.98  fof(f1,axiom,(
% 4.14/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 4.14/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.14/0.98  
% 4.14/0.98  fof(f16,plain,(
% 4.14/0.98    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 4.14/0.98    inference(ennf_transformation,[],[f1])).
% 4.14/0.98  
% 4.14/0.98  fof(f17,plain,(
% 4.14/0.98    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 4.14/0.98    inference(flattening,[],[f16])).
% 4.14/0.98  
% 4.14/0.98  fof(f49,plain,(
% 4.14/0.98    ( ! [X2,X0,X1] : (r2_hidden(X0,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 4.14/0.98    inference(cnf_transformation,[],[f17])).
% 4.14/0.98  
% 4.14/0.98  fof(f50,plain,(
% 4.14/0.98    ( ! [X2,X0,X1] : (r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 4.14/0.98    inference(cnf_transformation,[],[f17])).
% 4.14/0.98  
% 4.14/0.98  cnf(c_5,plain,
% 4.14/0.98      ( r2_hidden(X0,X1)
% 4.14/0.98      | r2_hidden(X1,X0)
% 4.14/0.98      | ~ v3_ordinal1(X1)
% 4.14/0.98      | ~ v3_ordinal1(X0)
% 4.14/0.98      | X0 = X1 ),
% 4.14/0.98      inference(cnf_transformation,[],[f55]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_1300,plain,
% 4.14/0.98      ( X0 = X1
% 4.14/0.98      | r2_hidden(X0,X1) = iProver_top
% 4.14/0.98      | r2_hidden(X1,X0) = iProver_top
% 4.14/0.98      | v3_ordinal1(X0) != iProver_top
% 4.14/0.98      | v3_ordinal1(X1) != iProver_top ),
% 4.14/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_28,negated_conjecture,
% 4.14/0.98      ( v3_ordinal1(sK4) ),
% 4.14/0.98      inference(cnf_transformation,[],[f77]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_1281,plain,
% 4.14/0.98      ( v3_ordinal1(sK4) = iProver_top ),
% 4.14/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_3,plain,
% 4.14/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ),
% 4.14/0.98      inference(cnf_transformation,[],[f81]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_1302,plain,
% 4.14/0.98      ( r2_hidden(X0,X1) != iProver_top
% 4.14/0.98      | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) = iProver_top ),
% 4.14/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_22,plain,
% 4.14/0.98      ( v1_relat_1(k1_wellord2(X0)) ),
% 4.14/0.98      inference(cnf_transformation,[],[f72]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_1285,plain,
% 4.14/0.98      ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
% 4.14/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_29,negated_conjecture,
% 4.14/0.98      ( v3_ordinal1(sK3) ),
% 4.14/0.98      inference(cnf_transformation,[],[f76]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_1280,plain,
% 4.14/0.98      ( v3_ordinal1(sK3) = iProver_top ),
% 4.14/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_2,plain,
% 4.14/0.98      ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
% 4.14/0.98      inference(cnf_transformation,[],[f84]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_1303,plain,
% 4.14/0.98      ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
% 4.14/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_23,plain,
% 4.14/0.98      ( ~ r2_hidden(X0,X1)
% 4.14/0.98      | ~ v3_ordinal1(X1)
% 4.14/0.98      | ~ v3_ordinal1(X0)
% 4.14/0.98      | k1_wellord1(k1_wellord2(X1),X0) = X0 ),
% 4.14/0.98      inference(cnf_transformation,[],[f73]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_1284,plain,
% 4.14/0.98      ( k1_wellord1(k1_wellord2(X0),X1) = X1
% 4.14/0.98      | r2_hidden(X1,X0) != iProver_top
% 4.14/0.98      | v3_ordinal1(X1) != iProver_top
% 4.14/0.98      | v3_ordinal1(X0) != iProver_top ),
% 4.14/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_2728,plain,
% 4.14/0.98      ( k1_wellord1(k1_wellord2(k2_xboole_0(X0,k1_tarski(X0))),X0) = X0
% 4.14/0.98      | v3_ordinal1(X0) != iProver_top
% 4.14/0.98      | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) != iProver_top ),
% 4.14/0.98      inference(superposition,[status(thm)],[c_1303,c_1284]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_6,plain,
% 4.14/0.98      ( ~ v3_ordinal1(X0) | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
% 4.14/0.98      inference(cnf_transformation,[],[f83]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_86,plain,
% 4.14/0.98      ( v3_ordinal1(X0) != iProver_top
% 4.14/0.98      | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
% 4.14/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_2741,plain,
% 4.14/0.98      ( v3_ordinal1(X0) != iProver_top
% 4.14/0.98      | k1_wellord1(k1_wellord2(k2_xboole_0(X0,k1_tarski(X0))),X0) = X0 ),
% 4.14/0.98      inference(global_propositional_subsumption,[status(thm)],[c_2728,c_86]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_2742,plain,
% 4.14/0.98      ( k1_wellord1(k1_wellord2(k2_xboole_0(X0,k1_tarski(X0))),X0) = X0
% 4.14/0.98      | v3_ordinal1(X0) != iProver_top ),
% 4.14/0.98      inference(renaming,[status(thm)],[c_2741]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_2749,plain,
% 4.14/0.98      ( k1_wellord1(k1_wellord2(k2_xboole_0(sK3,k1_tarski(sK3))),sK3) = sK3 ),
% 4.14/0.98      inference(superposition,[status(thm)],[c_1280,c_2742]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_11,plain,
% 4.14/0.98      ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
% 4.14/0.98      | r2_hidden(k4_tarski(X0,X2),X1)
% 4.14/0.98      | ~ v1_relat_1(X1) ),
% 4.14/0.98      inference(cnf_transformation,[],[f86]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_1294,plain,
% 4.14/0.98      ( r2_hidden(X0,k1_wellord1(X1,X2)) != iProver_top
% 4.14/0.98      | r2_hidden(k4_tarski(X0,X2),X1) = iProver_top
% 4.14/0.98      | v1_relat_1(X1) != iProver_top ),
% 4.14/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_3243,plain,
% 4.14/0.98      ( r2_hidden(X0,sK3) != iProver_top
% 4.14/0.98      | r2_hidden(k4_tarski(X0,sK3),k1_wellord2(k2_xboole_0(sK3,k1_tarski(sK3)))) = iProver_top
% 4.14/0.98      | v1_relat_1(k1_wellord2(k2_xboole_0(sK3,k1_tarski(sK3)))) != iProver_top ),
% 4.14/0.98      inference(superposition,[status(thm)],[c_2749,c_1294]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_20,plain,
% 4.14/0.98      ( r1_tarski(X0,X1)
% 4.14/0.98      | ~ r2_hidden(X1,X2)
% 4.14/0.98      | ~ r2_hidden(X0,X2)
% 4.14/0.98      | ~ r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2))
% 4.14/0.98      | ~ v1_relat_1(k1_wellord2(X2)) ),
% 4.14/0.98      inference(cnf_transformation,[],[f94]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_1286,plain,
% 4.14/0.98      ( r1_tarski(X0,X1) = iProver_top
% 4.14/0.98      | r2_hidden(X1,X2) != iProver_top
% 4.14/0.98      | r2_hidden(X0,X2) != iProver_top
% 4.14/0.98      | r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2)) != iProver_top
% 4.14/0.98      | v1_relat_1(k1_wellord2(X2)) != iProver_top ),
% 4.14/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_3503,plain,
% 4.14/0.98      ( r1_tarski(X0,sK3) = iProver_top
% 4.14/0.98      | r2_hidden(X0,k2_xboole_0(sK3,k1_tarski(sK3))) != iProver_top
% 4.14/0.98      | r2_hidden(X0,sK3) != iProver_top
% 4.14/0.98      | r2_hidden(sK3,k2_xboole_0(sK3,k1_tarski(sK3))) != iProver_top
% 4.14/0.98      | v1_relat_1(k1_wellord2(k2_xboole_0(sK3,k1_tarski(sK3)))) != iProver_top ),
% 4.14/0.98      inference(superposition,[status(thm)],[c_3243,c_1286]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_98,plain,
% 4.14/0.98      ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
% 4.14/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_100,plain,
% 4.14/0.98      ( r2_hidden(sK3,k2_xboole_0(sK3,k1_tarski(sK3))) = iProver_top ),
% 4.14/0.98      inference(instantiation,[status(thm)],[c_98]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_4445,plain,
% 4.14/0.98      ( r2_hidden(X0,sK3) != iProver_top
% 4.14/0.98      | r2_hidden(X0,k2_xboole_0(sK3,k1_tarski(sK3))) != iProver_top
% 4.14/0.98      | r1_tarski(X0,sK3) = iProver_top
% 4.14/0.98      | v1_relat_1(k1_wellord2(k2_xboole_0(sK3,k1_tarski(sK3)))) != iProver_top ),
% 4.14/0.98      inference(global_propositional_subsumption,[status(thm)],[c_3503,c_100]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_4446,plain,
% 4.14/0.98      ( r1_tarski(X0,sK3) = iProver_top
% 4.14/0.98      | r2_hidden(X0,k2_xboole_0(sK3,k1_tarski(sK3))) != iProver_top
% 4.14/0.98      | r2_hidden(X0,sK3) != iProver_top
% 4.14/0.98      | v1_relat_1(k1_wellord2(k2_xboole_0(sK3,k1_tarski(sK3)))) != iProver_top ),
% 4.14/0.98      inference(renaming,[status(thm)],[c_4445]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_4449,plain,
% 4.14/0.98      ( r1_tarski(X0,sK3) = iProver_top
% 4.14/0.98      | r2_hidden(X0,k2_xboole_0(sK3,k1_tarski(sK3))) != iProver_top
% 4.14/0.98      | r2_hidden(X0,sK3) != iProver_top ),
% 4.14/0.98      inference(superposition,[status(thm)],[c_1285,c_4446]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_5693,plain,
% 4.14/0.98      ( r1_tarski(X0,sK3) = iProver_top | r2_hidden(X0,sK3) != iProver_top ),
% 4.14/0.98      inference(superposition,[status(thm)],[c_1302,c_4449]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_5782,plain,
% 4.14/0.98      ( sK3 = X0
% 4.14/0.98      | r1_tarski(X0,sK3) = iProver_top
% 4.14/0.98      | r2_hidden(sK3,X0) = iProver_top
% 4.14/0.98      | v3_ordinal1(X0) != iProver_top
% 4.14/0.98      | v3_ordinal1(sK3) != iProver_top ),
% 4.14/0.98      inference(superposition,[status(thm)],[c_1300,c_5693]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_30,plain,
% 4.14/0.98      ( v3_ordinal1(sK3) = iProver_top ),
% 4.14/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_8954,plain,
% 4.14/0.98      ( v3_ordinal1(X0) != iProver_top
% 4.14/0.98      | r2_hidden(sK3,X0) = iProver_top
% 4.14/0.98      | r1_tarski(X0,sK3) = iProver_top
% 4.14/0.98      | sK3 = X0 ),
% 4.14/0.98      inference(global_propositional_subsumption,[status(thm)],[c_5782,c_30]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_8955,plain,
% 4.14/0.98      ( sK3 = X0
% 4.14/0.98      | r1_tarski(X0,sK3) = iProver_top
% 4.14/0.98      | r2_hidden(sK3,X0) = iProver_top
% 4.14/0.98      | v3_ordinal1(X0) != iProver_top ),
% 4.14/0.98      inference(renaming,[status(thm)],[c_8954]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_25,plain,
% 4.14/0.98      ( ~ r1_tarski(X0,X1)
% 4.14/0.98      | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ),
% 4.14/0.98      inference(cnf_transformation,[],[f75]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_1283,plain,
% 4.14/0.98      ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 4.14/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 4.14/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_8958,plain,
% 4.14/0.98      ( k2_wellord1(k1_wellord2(sK3),X0) = k1_wellord2(X0)
% 4.14/0.98      | sK3 = X0
% 4.14/0.98      | r2_hidden(sK3,X0) = iProver_top
% 4.14/0.98      | v3_ordinal1(X0) != iProver_top ),
% 4.14/0.98      inference(superposition,[status(thm)],[c_8955,c_1283]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_9633,plain,
% 4.14/0.98      ( k2_wellord1(k1_wellord2(sK3),X0) = k1_wellord2(X0)
% 4.14/0.98      | k1_wellord1(k1_wellord2(X0),sK3) = sK3
% 4.14/0.98      | sK3 = X0
% 4.14/0.98      | v3_ordinal1(X0) != iProver_top
% 4.14/0.98      | v3_ordinal1(sK3) != iProver_top ),
% 4.14/0.98      inference(superposition,[status(thm)],[c_8958,c_1284]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_12197,plain,
% 4.14/0.98      ( v3_ordinal1(X0) != iProver_top
% 4.14/0.98      | sK3 = X0
% 4.14/0.98      | k1_wellord1(k1_wellord2(X0),sK3) = sK3
% 4.14/0.98      | k2_wellord1(k1_wellord2(sK3),X0) = k1_wellord2(X0) ),
% 4.14/0.98      inference(global_propositional_subsumption,[status(thm)],[c_9633,c_30]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_12198,plain,
% 4.14/0.98      ( k2_wellord1(k1_wellord2(sK3),X0) = k1_wellord2(X0)
% 4.14/0.98      | k1_wellord1(k1_wellord2(X0),sK3) = sK3
% 4.14/0.98      | sK3 = X0
% 4.14/0.98      | v3_ordinal1(X0) != iProver_top ),
% 4.14/0.98      inference(renaming,[status(thm)],[c_12197]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_12202,plain,
% 4.14/0.98      ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
% 4.14/0.98      | k1_wellord1(k1_wellord2(sK4),sK3) = sK3
% 4.14/0.98      | sK4 = sK3 ),
% 4.14/0.98      inference(superposition,[status(thm)],[c_1281,c_12198]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_26,negated_conjecture,
% 4.14/0.98      ( sK3 != sK4 ),
% 4.14/0.98      inference(cnf_transformation,[],[f79]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_827,plain,( X0 = X0 ),theory(equality) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_856,plain,
% 4.14/0.98      ( sK3 = sK3 ),
% 4.14/0.98      inference(instantiation,[status(thm)],[c_827]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_828,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_1339,plain,
% 4.14/0.98      ( sK4 != X0 | sK3 != X0 | sK3 = sK4 ),
% 4.14/0.98      inference(instantiation,[status(thm)],[c_828]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_1340,plain,
% 4.14/0.98      ( sK4 != sK3 | sK3 = sK4 | sK3 != sK3 ),
% 4.14/0.98      inference(instantiation,[status(thm)],[c_1339]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_12233,plain,
% 4.14/0.98      ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3
% 4.14/0.98      | k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4) ),
% 4.14/0.98      inference(global_propositional_subsumption,
% 4.14/0.98                [status(thm)],
% 4.14/0.98                [c_12202,c_26,c_856,c_1340]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_12234,plain,
% 4.14/0.98      ( k2_wellord1(k1_wellord2(sK3),sK4) = k1_wellord2(sK4)
% 4.14/0.98      | k1_wellord1(k1_wellord2(sK4),sK3) = sK3 ),
% 4.14/0.98      inference(renaming,[status(thm)],[c_12233]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_2748,plain,
% 4.14/0.98      ( k1_wellord1(k1_wellord2(k2_xboole_0(sK4,k1_tarski(sK4))),sK4) = sK4 ),
% 4.14/0.98      inference(superposition,[status(thm)],[c_1281,c_2742]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_2909,plain,
% 4.14/0.98      ( r2_hidden(X0,sK4) != iProver_top
% 4.14/0.98      | r2_hidden(k4_tarski(X0,sK4),k1_wellord2(k2_xboole_0(sK4,k1_tarski(sK4)))) = iProver_top
% 4.14/0.98      | v1_relat_1(k1_wellord2(k2_xboole_0(sK4,k1_tarski(sK4)))) != iProver_top ),
% 4.14/0.98      inference(superposition,[status(thm)],[c_2748,c_1294]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_3348,plain,
% 4.14/0.98      ( r1_tarski(X0,sK4) = iProver_top
% 4.14/0.98      | r2_hidden(X0,k2_xboole_0(sK4,k1_tarski(sK4))) != iProver_top
% 4.14/0.98      | r2_hidden(X0,sK4) != iProver_top
% 4.14/0.98      | r2_hidden(sK4,k2_xboole_0(sK4,k1_tarski(sK4))) != iProver_top
% 4.14/0.98      | v1_relat_1(k1_wellord2(k2_xboole_0(sK4,k1_tarski(sK4)))) != iProver_top ),
% 4.14/0.98      inference(superposition,[status(thm)],[c_2909,c_1286]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_3266,plain,
% 4.14/0.98      ( r2_hidden(X0,k2_xboole_0(sK4,k1_tarski(sK4))) | ~ r2_hidden(X0,sK4) ),
% 4.14/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_3267,plain,
% 4.14/0.98      ( r2_hidden(X0,k2_xboole_0(sK4,k1_tarski(sK4))) = iProver_top
% 4.14/0.98      | r2_hidden(X0,sK4) != iProver_top ),
% 4.14/0.98      inference(predicate_to_equality,[status(thm)],[c_3266]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_3687,plain,
% 4.14/0.98      ( r1_tarski(X0,sK4) = iProver_top
% 4.14/0.98      | r2_hidden(X0,sK4) != iProver_top
% 4.14/0.98      | r2_hidden(sK4,k2_xboole_0(sK4,k1_tarski(sK4))) != iProver_top
% 4.14/0.98      | v1_relat_1(k1_wellord2(k2_xboole_0(sK4,k1_tarski(sK4)))) != iProver_top ),
% 4.14/0.98      inference(global_propositional_subsumption,[status(thm)],[c_3348,c_3267]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_3693,plain,
% 4.14/0.98      ( r1_tarski(X0,sK4) = iProver_top
% 4.14/0.98      | r2_hidden(X0,sK4) != iProver_top
% 4.14/0.98      | r2_hidden(sK4,k2_xboole_0(sK4,k1_tarski(sK4))) != iProver_top ),
% 4.14/0.98      inference(superposition,[status(thm)],[c_1285,c_3687]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_5094,plain,
% 4.14/0.98      ( r1_tarski(X0,sK4) = iProver_top | r2_hidden(X0,sK4) != iProver_top ),
% 4.14/0.98      inference(superposition,[status(thm)],[c_1303,c_3693]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_5102,plain,
% 4.14/0.98      ( sK4 = X0
% 4.14/0.98      | r1_tarski(X0,sK4) = iProver_top
% 4.14/0.98      | r2_hidden(sK4,X0) = iProver_top
% 4.14/0.98      | v3_ordinal1(X0) != iProver_top
% 4.14/0.98      | v3_ordinal1(sK4) != iProver_top ),
% 4.14/0.98      inference(superposition,[status(thm)],[c_1300,c_5094]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_31,plain,
% 4.14/0.98      ( v3_ordinal1(sK4) = iProver_top ),
% 4.14/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_8815,plain,
% 4.14/0.98      ( v3_ordinal1(X0) != iProver_top
% 4.14/0.98      | r2_hidden(sK4,X0) = iProver_top
% 4.14/0.98      | r1_tarski(X0,sK4) = iProver_top
% 4.14/0.98      | sK4 = X0 ),
% 4.14/0.98      inference(global_propositional_subsumption,[status(thm)],[c_5102,c_31]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_8816,plain,
% 4.14/0.98      ( sK4 = X0
% 4.14/0.98      | r1_tarski(X0,sK4) = iProver_top
% 4.14/0.98      | r2_hidden(sK4,X0) = iProver_top
% 4.14/0.98      | v3_ordinal1(X0) != iProver_top ),
% 4.14/0.98      inference(renaming,[status(thm)],[c_8815]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_8821,plain,
% 4.14/0.98      ( k2_wellord1(k1_wellord2(sK4),X0) = k1_wellord2(X0)
% 4.14/0.98      | sK4 = X0
% 4.14/0.98      | r2_hidden(sK4,X0) = iProver_top
% 4.14/0.98      | v3_ordinal1(X0) != iProver_top ),
% 4.14/0.98      inference(superposition,[status(thm)],[c_8816,c_1283]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_8931,plain,
% 4.14/0.98      ( k2_wellord1(k1_wellord2(sK4),X0) = k1_wellord2(X0)
% 4.14/0.98      | k1_wellord1(k1_wellord2(X0),sK4) = sK4
% 4.14/0.98      | sK4 = X0
% 4.14/0.98      | v3_ordinal1(X0) != iProver_top
% 4.14/0.98      | v3_ordinal1(sK4) != iProver_top ),
% 4.14/0.98      inference(superposition,[status(thm)],[c_8821,c_1284]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_12117,plain,
% 4.14/0.98      ( v3_ordinal1(X0) != iProver_top
% 4.14/0.98      | sK4 = X0
% 4.14/0.98      | k1_wellord1(k1_wellord2(X0),sK4) = sK4
% 4.14/0.98      | k2_wellord1(k1_wellord2(sK4),X0) = k1_wellord2(X0) ),
% 4.14/0.98      inference(global_propositional_subsumption,[status(thm)],[c_8931,c_31]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_12118,plain,
% 4.14/0.98      ( k2_wellord1(k1_wellord2(sK4),X0) = k1_wellord2(X0)
% 4.14/0.98      | k1_wellord1(k1_wellord2(X0),sK4) = sK4
% 4.14/0.98      | sK4 = X0
% 4.14/0.98      | v3_ordinal1(X0) != iProver_top ),
% 4.14/0.98      inference(renaming,[status(thm)],[c_12117]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_12125,plain,
% 4.14/0.98      ( k2_wellord1(k1_wellord2(sK4),sK3) = k1_wellord2(sK3)
% 4.14/0.98      | k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 4.14/0.98      | sK4 = sK3 ),
% 4.14/0.98      inference(superposition,[status(thm)],[c_1280,c_12118]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_12192,plain,
% 4.14/0.98      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 4.14/0.98      | k2_wellord1(k1_wellord2(sK4),sK3) = k1_wellord2(sK3) ),
% 4.14/0.98      inference(global_propositional_subsumption,
% 4.14/0.98                [status(thm)],
% 4.14/0.98                [c_12125,c_29,c_28,c_26,c_856,c_1340,c_8944]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_12193,plain,
% 4.14/0.98      ( k2_wellord1(k1_wellord2(sK4),sK3) = k1_wellord2(sK3)
% 4.14/0.98      | k1_wellord1(k1_wellord2(sK3),sK4) = sK4 ),
% 4.14/0.98      inference(renaming,[status(thm)],[c_12192]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_3077,plain,
% 4.14/0.98      ( X0 = X1
% 4.14/0.98      | k1_wellord1(k1_wellord2(X1),X0) = X0
% 4.14/0.98      | r2_hidden(X1,X0) = iProver_top
% 4.14/0.98      | v3_ordinal1(X1) != iProver_top
% 4.14/0.98      | v3_ordinal1(X0) != iProver_top ),
% 4.14/0.98      inference(superposition,[status(thm)],[c_1300,c_1284]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_9560,plain,
% 4.14/0.98      ( X0 = X1
% 4.14/0.98      | k1_wellord1(k1_wellord2(X0),X1) = X1
% 4.14/0.98      | k1_wellord1(k1_wellord2(X1),X0) = X0
% 4.14/0.98      | v3_ordinal1(X1) != iProver_top
% 4.14/0.98      | v3_ordinal1(X0) != iProver_top ),
% 4.14/0.98      inference(superposition,[status(thm)],[c_3077,c_1284]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_9940,plain,
% 4.14/0.98      ( k1_wellord1(k1_wellord2(X0),sK4) = sK4
% 4.14/0.98      | k1_wellord1(k1_wellord2(sK4),X0) = X0
% 4.14/0.98      | sK4 = X0
% 4.14/0.98      | v3_ordinal1(X0) != iProver_top ),
% 4.14/0.98      inference(superposition,[status(thm)],[c_1281,c_9560]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_9950,plain,
% 4.14/0.98      ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3
% 4.14/0.98      | k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 4.14/0.98      | sK4 = sK3 ),
% 4.14/0.98      inference(superposition,[status(thm)],[c_1280,c_9940]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_9944,plain,
% 4.14/0.98      ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3
% 4.14/0.98      | k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 4.14/0.98      | sK4 = sK3
% 4.14/0.98      | v3_ordinal1(sK3) != iProver_top ),
% 4.14/0.98      inference(instantiation,[status(thm)],[c_9940]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_10113,plain,
% 4.14/0.98      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 4.14/0.98      | k1_wellord1(k1_wellord2(sK4),sK3) = sK3 ),
% 4.14/0.98      inference(global_propositional_subsumption,
% 4.14/0.98                [status(thm)],
% 4.14/0.98                [c_9950,c_30,c_26,c_856,c_1340,c_9944]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_10114,plain,
% 4.14/0.98      ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3
% 4.14/0.98      | k1_wellord1(k1_wellord2(sK3),sK4) = sK4 ),
% 4.14/0.98      inference(renaming,[status(thm)],[c_10113]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_14,plain,
% 4.14/0.98      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
% 4.14/0.98      | ~ r2_hidden(X1,k3_relat_1(X0))
% 4.14/0.98      | ~ v2_wellord1(X0)
% 4.14/0.98      | ~ v1_relat_1(X0) ),
% 4.14/0.98      inference(cnf_transformation,[],[f64]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_24,plain,
% 4.14/0.98      ( v2_wellord1(k1_wellord2(X0)) | ~ v3_ordinal1(X0) ),
% 4.14/0.98      inference(cnf_transformation,[],[f74]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_329,plain,
% 4.14/0.98      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
% 4.14/0.98      | ~ r2_hidden(X1,k3_relat_1(X0))
% 4.14/0.98      | ~ v3_ordinal1(X2)
% 4.14/0.98      | ~ v1_relat_1(X0)
% 4.14/0.98      | k1_wellord2(X2) != X0 ),
% 4.14/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_24]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_330,plain,
% 4.14/0.98      ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
% 4.14/0.98      | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
% 4.14/0.98      | ~ v3_ordinal1(X0)
% 4.14/0.98      | ~ v1_relat_1(k1_wellord2(X0)) ),
% 4.14/0.98      inference(unflattening,[status(thm)],[c_329]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_334,plain,
% 4.14/0.98      ( ~ v3_ordinal1(X0)
% 4.14/0.98      | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
% 4.14/0.98      | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) ),
% 4.14/0.98      inference(global_propositional_subsumption,[status(thm)],[c_330,c_22]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_335,plain,
% 4.14/0.98      ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
% 4.14/0.98      | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
% 4.14/0.98      | ~ v3_ordinal1(X0) ),
% 4.14/0.98      inference(renaming,[status(thm)],[c_334]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_1279,plain,
% 4.14/0.98      ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
% 4.14/0.98      | r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) != iProver_top
% 4.14/0.98      | v3_ordinal1(X0) != iProver_top ),
% 4.14/0.98      inference(predicate_to_equality,[status(thm)],[c_335]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_21,plain,
% 4.14/0.98      ( ~ v1_relat_1(k1_wellord2(X0)) | k3_relat_1(k1_wellord2(X0)) = X0 ),
% 4.14/0.98      inference(cnf_transformation,[],[f95]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_171,plain,
% 4.14/0.98      ( k3_relat_1(k1_wellord2(X0)) = X0 ),
% 4.14/0.98      inference(global_propositional_subsumption,[status(thm)],[c_21,c_22]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_1306,plain,
% 4.14/0.98      ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
% 4.14/0.98      | r2_hidden(X1,X0) != iProver_top
% 4.14/0.98      | v3_ordinal1(X0) != iProver_top ),
% 4.14/0.98      inference(light_normalisation,[status(thm)],[c_1279,c_171]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_10117,plain,
% 4.14/0.98      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 4.14/0.98      | r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) != iProver_top
% 4.14/0.98      | r2_hidden(sK3,sK4) != iProver_top
% 4.14/0.98      | v3_ordinal1(sK4) != iProver_top ),
% 4.14/0.98      inference(superposition,[status(thm)],[c_10114,c_1306]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_1994,plain,
% 4.14/0.98      ( r2_hidden(sK4,sK3)
% 4.14/0.98      | r2_hidden(sK3,sK4)
% 4.14/0.98      | ~ v3_ordinal1(sK4)
% 4.14/0.98      | ~ v3_ordinal1(sK3)
% 4.14/0.98      | sK3 = sK4 ),
% 4.14/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_1995,plain,
% 4.14/0.98      ( sK3 = sK4
% 4.14/0.98      | r2_hidden(sK4,sK3) = iProver_top
% 4.14/0.98      | r2_hidden(sK3,sK4) = iProver_top
% 4.14/0.98      | v3_ordinal1(sK4) != iProver_top
% 4.14/0.98      | v3_ordinal1(sK3) != iProver_top ),
% 4.14/0.98      inference(predicate_to_equality,[status(thm)],[c_1994]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_6968,plain,
% 4.14/0.98      ( ~ r2_hidden(sK4,X0)
% 4.14/0.98      | ~ v3_ordinal1(X0)
% 4.14/0.98      | ~ v3_ordinal1(sK4)
% 4.14/0.98      | k1_wellord1(k1_wellord2(X0),sK4) = sK4 ),
% 4.14/0.98      inference(instantiation,[status(thm)],[c_23]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_6969,plain,
% 4.14/0.98      ( k1_wellord1(k1_wellord2(X0),sK4) = sK4
% 4.14/0.98      | r2_hidden(sK4,X0) != iProver_top
% 4.14/0.98      | v3_ordinal1(X0) != iProver_top
% 4.14/0.98      | v3_ordinal1(sK4) != iProver_top ),
% 4.14/0.98      inference(predicate_to_equality,[status(thm)],[c_6968]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_6971,plain,
% 4.14/0.98      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 4.14/0.98      | r2_hidden(sK4,sK3) != iProver_top
% 4.14/0.98      | v3_ordinal1(sK4) != iProver_top
% 4.14/0.98      | v3_ordinal1(sK3) != iProver_top ),
% 4.14/0.98      inference(instantiation,[status(thm)],[c_6969]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_10192,plain,
% 4.14/0.98      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 4.14/0.98      | r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) != iProver_top ),
% 4.14/0.98      inference(global_propositional_subsumption,
% 4.14/0.98                [status(thm)],
% 4.14/0.98                [c_10117,c_30,c_31,c_26,c_1995,c_6971]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_12194,plain,
% 4.14/0.98      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4
% 4.14/0.98      | r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) != iProver_top ),
% 4.14/0.98      inference(superposition,[status(thm)],[c_12193,c_10192]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_42,plain,
% 4.14/0.98      ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
% 4.14/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_44,plain,
% 4.14/0.98      ( v1_relat_1(k1_wellord2(sK3)) = iProver_top ),
% 4.14/0.98      inference(instantiation,[status(thm)],[c_42]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_1449,plain,
% 4.14/0.98      ( v1_relat_1(k1_wellord2(sK4)) ),
% 4.14/0.98      inference(instantiation,[status(thm)],[c_22]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_1450,plain,
% 4.14/0.98      ( v1_relat_1(k1_wellord2(sK4)) = iProver_top ),
% 4.14/0.98      inference(predicate_to_equality,[status(thm)],[c_1449]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_27,negated_conjecture,
% 4.14/0.98      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) ),
% 4.14/0.98      inference(cnf_transformation,[],[f78]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_1282,plain,
% 4.14/0.98      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) = iProver_top ),
% 4.14/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_13,plain,
% 4.14/0.98      ( ~ r4_wellord1(X0,X1)
% 4.14/0.98      | r4_wellord1(X1,X0)
% 4.14/0.98      | ~ v1_relat_1(X0)
% 4.14/0.98      | ~ v1_relat_1(X1) ),
% 4.14/0.98      inference(cnf_transformation,[],[f63]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_1292,plain,
% 4.14/0.98      ( r4_wellord1(X0,X1) != iProver_top
% 4.14/0.98      | r4_wellord1(X1,X0) = iProver_top
% 4.14/0.98      | v1_relat_1(X0) != iProver_top
% 4.14/0.98      | v1_relat_1(X1) != iProver_top ),
% 4.14/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_2646,plain,
% 4.14/0.98      ( r4_wellord1(k1_wellord2(sK4),k1_wellord2(sK3)) = iProver_top
% 4.14/0.98      | v1_relat_1(k1_wellord2(sK4)) != iProver_top
% 4.14/0.98      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 4.14/0.98      inference(superposition,[status(thm)],[c_1282,c_1292]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_12236,plain,
% 4.14/0.98      ( k1_wellord1(k1_wellord2(sK3),sK4) = sK4 ),
% 4.14/0.98      inference(global_propositional_subsumption,
% 4.14/0.98                [status(thm)],
% 4.14/0.98                [c_12194,c_44,c_1450,c_2646]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_12240,plain,
% 4.14/0.98      ( r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK4)) != iProver_top
% 4.14/0.98      | r2_hidden(sK4,sK3) != iProver_top
% 4.14/0.98      | v3_ordinal1(sK3) != iProver_top ),
% 4.14/0.98      inference(superposition,[status(thm)],[c_12236,c_1306]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_12,plain,
% 4.14/0.98      ( ~ r2_hidden(X0,k1_wellord1(X1,X0)) | ~ v1_relat_1(X1) ),
% 4.14/0.98      inference(cnf_transformation,[],[f88]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_1293,plain,
% 4.14/0.98      ( r2_hidden(X0,k1_wellord1(X1,X0)) != iProver_top
% 4.14/0.98      | v1_relat_1(X1) != iProver_top ),
% 4.14/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_3244,plain,
% 4.14/0.98      ( r2_hidden(sK3,sK3) != iProver_top
% 4.14/0.98      | v1_relat_1(k1_wellord2(k2_xboole_0(sK3,k1_tarski(sK3)))) != iProver_top ),
% 4.14/0.98      inference(superposition,[status(thm)],[c_2749,c_1293]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_3342,plain,
% 4.14/0.98      ( r2_hidden(sK3,sK3) != iProver_top ),
% 4.14/0.98      inference(superposition,[status(thm)],[c_1285,c_3244]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_12238,plain,
% 4.14/0.98      ( r2_hidden(X0,sK4) != iProver_top
% 4.14/0.98      | r2_hidden(k4_tarski(X0,sK4),k1_wellord2(sK3)) = iProver_top
% 4.14/0.98      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 4.14/0.98      inference(superposition,[status(thm)],[c_12236,c_1294]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_12314,plain,
% 4.14/0.98      ( r2_hidden(k4_tarski(X0,sK4),k1_wellord2(sK3)) = iProver_top
% 4.14/0.98      | r2_hidden(X0,sK4) != iProver_top ),
% 4.14/0.98      inference(global_propositional_subsumption,[status(thm)],[c_12238,c_44]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_12315,plain,
% 4.14/0.98      ( r2_hidden(X0,sK4) != iProver_top
% 4.14/0.98      | r2_hidden(k4_tarski(X0,sK4),k1_wellord2(sK3)) = iProver_top ),
% 4.14/0.98      inference(renaming,[status(thm)],[c_12314]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_1,plain,
% 4.14/0.98      ( r2_hidden(X0,k3_relat_1(X1))
% 4.14/0.98      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 4.14/0.98      | ~ v1_relat_1(X1) ),
% 4.14/0.98      inference(cnf_transformation,[],[f49]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_1304,plain,
% 4.14/0.98      ( r2_hidden(X0,k3_relat_1(X1)) = iProver_top
% 4.14/0.98      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top
% 4.14/0.98      | v1_relat_1(X1) != iProver_top ),
% 4.14/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_12323,plain,
% 4.14/0.98      ( r2_hidden(X0,k3_relat_1(k1_wellord2(sK3))) = iProver_top
% 4.14/0.98      | r2_hidden(X0,sK4) != iProver_top
% 4.14/0.98      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 4.14/0.98      inference(superposition,[status(thm)],[c_12315,c_1304]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_12331,plain,
% 4.14/0.98      ( r2_hidden(X0,sK4) != iProver_top
% 4.14/0.98      | r2_hidden(X0,sK3) = iProver_top
% 4.14/0.98      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 4.14/0.98      inference(demodulation,[status(thm)],[c_12323,c_171]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_12349,plain,
% 4.14/0.98      ( r2_hidden(sK3,sK4) != iProver_top
% 4.14/0.98      | r2_hidden(sK3,sK3) = iProver_top
% 4.14/0.98      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 4.14/0.98      inference(instantiation,[status(thm)],[c_12331]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_12355,plain,
% 4.14/0.98      ( r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK4)) != iProver_top ),
% 4.14/0.98      inference(global_propositional_subsumption,
% 4.14/0.98                [status(thm)],
% 4.14/0.98                [c_12240,c_30,c_31,c_26,c_44,c_1995,c_3342,c_12349]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_12359,plain,
% 4.14/0.98      ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3
% 4.14/0.98      | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) != iProver_top ),
% 4.14/0.98      inference(superposition,[status(thm)],[c_12234,c_12355]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_32,plain,
% 4.14/0.98      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK4)) = iProver_top ),
% 4.14/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_12382,plain,
% 4.14/0.98      ( k1_wellord1(k1_wellord2(sK4),sK3) = sK3 ),
% 4.14/0.98      inference(global_propositional_subsumption,[status(thm)],[c_12359,c_32]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_12386,plain,
% 4.14/0.98      ( r4_wellord1(k1_wellord2(sK4),k2_wellord1(k1_wellord2(sK4),sK3)) != iProver_top
% 4.14/0.98      | r2_hidden(sK3,sK4) != iProver_top
% 4.14/0.98      | v3_ordinal1(sK4) != iProver_top ),
% 4.14/0.98      inference(superposition,[status(thm)],[c_12382,c_1306]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_12530,plain,
% 4.14/0.98      ( r2_hidden(sK3,sK4) != iProver_top ),
% 4.14/0.98      inference(global_propositional_subsumption,
% 4.14/0.98                [status(thm)],
% 4.14/0.98                [c_12386,c_44,c_3342,c_12349]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_12537,plain,
% 4.14/0.98      ( sK4 = sK3
% 4.14/0.98      | r2_hidden(sK4,sK3) = iProver_top
% 4.14/0.98      | v3_ordinal1(sK4) != iProver_top
% 4.14/0.98      | v3_ordinal1(sK3) != iProver_top ),
% 4.14/0.98      inference(superposition,[status(thm)],[c_1300,c_12530]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_13296,plain,
% 4.14/0.98      ( r2_hidden(sK4,sK3) = iProver_top ),
% 4.14/0.98      inference(global_propositional_subsumption,
% 4.14/0.98                [status(thm)],
% 4.14/0.98                [c_12537,c_30,c_31,c_26,c_44,c_1995,c_3342,c_12349]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_12384,plain,
% 4.14/0.98      ( r2_hidden(X0,sK3) != iProver_top
% 4.14/0.98      | r2_hidden(k4_tarski(X0,sK3),k1_wellord2(sK4)) = iProver_top
% 4.14/0.98      | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
% 4.14/0.98      inference(superposition,[status(thm)],[c_12382,c_1294]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_12390,plain,
% 4.14/0.98      ( r2_hidden(k4_tarski(X0,sK3),k1_wellord2(sK4)) = iProver_top
% 4.14/0.98      | r2_hidden(X0,sK3) != iProver_top ),
% 4.14/0.98      inference(global_propositional_subsumption,
% 4.14/0.98                [status(thm)],
% 4.14/0.98                [c_12384,c_1450]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_12391,plain,
% 4.14/0.98      ( r2_hidden(X0,sK3) != iProver_top
% 4.14/0.98      | r2_hidden(k4_tarski(X0,sK3),k1_wellord2(sK4)) = iProver_top ),
% 4.14/0.98      inference(renaming,[status(thm)],[c_12390]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_12397,plain,
% 4.14/0.98      ( r2_hidden(X0,k3_relat_1(k1_wellord2(sK4))) = iProver_top
% 4.14/0.98      | r2_hidden(X0,sK3) != iProver_top
% 4.14/0.98      | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
% 4.14/0.98      inference(superposition,[status(thm)],[c_12391,c_1304]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_12405,plain,
% 4.14/0.98      ( r2_hidden(X0,sK4) = iProver_top
% 4.14/0.98      | r2_hidden(X0,sK3) != iProver_top
% 4.14/0.98      | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
% 4.14/0.98      inference(demodulation,[status(thm)],[c_12397,c_171]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_0,plain,
% 4.14/0.98      ( r2_hidden(X0,k3_relat_1(X1))
% 4.14/0.98      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 4.14/0.98      | ~ v1_relat_1(X1) ),
% 4.14/0.98      inference(cnf_transformation,[],[f50]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_1305,plain,
% 4.14/0.98      ( r2_hidden(X0,k3_relat_1(X1)) = iProver_top
% 4.14/0.98      | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
% 4.14/0.98      | v1_relat_1(X1) != iProver_top ),
% 4.14/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_12395,plain,
% 4.14/0.98      ( r2_hidden(X0,sK3) != iProver_top
% 4.14/0.98      | r2_hidden(sK3,k3_relat_1(k1_wellord2(sK4))) = iProver_top
% 4.14/0.98      | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
% 4.14/0.98      inference(superposition,[status(thm)],[c_12391,c_1305]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_12406,plain,
% 4.14/0.98      ( r2_hidden(X0,sK3) != iProver_top
% 4.14/0.98      | r2_hidden(sK3,sK4) = iProver_top
% 4.14/0.98      | v1_relat_1(k1_wellord2(sK4)) != iProver_top ),
% 4.14/0.98      inference(demodulation,[status(thm)],[c_12395,c_171]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_12782,plain,
% 4.14/0.98      ( r2_hidden(X0,sK3) != iProver_top ),
% 4.14/0.98      inference(global_propositional_subsumption,
% 4.14/0.98                [status(thm)],
% 4.14/0.98                [c_12405,c_44,c_1450,c_3342,c_12349,c_12406]) ).
% 4.14/0.98  
% 4.14/0.98  cnf(c_13302,plain,
% 4.14/0.98      ( $false ),
% 4.14/0.98      inference(superposition,[status(thm)],[c_13296,c_12782]) ).
% 4.14/0.98  
% 4.14/0.98  
% 4.14/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 4.14/0.98  
% 4.14/0.98  ------                               Statistics
% 4.14/0.98  
% 4.14/0.98  ------ General
% 4.14/0.98  
% 4.14/0.98  abstr_ref_over_cycles:                  0
% 4.14/0.98  abstr_ref_under_cycles:                 0
% 4.14/0.98  gc_basic_clause_elim:                   0
% 4.14/0.98  forced_gc_time:                         0
% 4.14/0.98  parsing_time:                           0.008
% 4.14/0.98  unif_index_cands_time:                  0.
% 4.14/0.98  unif_index_add_time:                    0.
% 4.14/0.98  orderings_time:                         0.
% 4.14/0.98  out_proof_time:                         0.016
% 4.14/0.98  total_time:                             0.464
% 4.14/0.98  num_of_symbols:                         49
% 4.14/0.98  num_of_terms:                           13423
% 4.14/0.98  
% 4.14/0.98  ------ Preprocessing
% 4.14/0.98  
% 4.14/0.98  num_of_splits:                          0
% 4.14/0.98  num_of_split_atoms:                     0
% 4.14/0.98  num_of_reused_defs:                     0
% 4.14/0.98  num_eq_ax_congr_red:                    24
% 4.14/0.98  num_of_sem_filtered_clauses:            1
% 4.14/0.98  num_of_subtypes:                        0
% 4.14/0.98  monotx_restored_types:                  0
% 4.14/0.98  sat_num_of_epr_types:                   0
% 4.14/0.98  sat_num_of_non_cyclic_types:            0
% 4.14/0.98  sat_guarded_non_collapsed_types:        0
% 4.14/0.98  num_pure_diseq_elim:                    0
% 4.14/0.98  simp_replaced_by:                       0
% 4.14/0.98  res_preprocessed:                       148
% 4.14/0.98  prep_upred:                             0
% 4.14/0.98  prep_unflattend:                        13
% 4.14/0.98  smt_new_axioms:                         0
% 4.14/0.98  pred_elim_cands:                        5
% 4.14/0.98  pred_elim:                              1
% 4.14/0.98  pred_elim_cl:                           1
% 4.14/0.98  pred_elim_cycles:                       3
% 4.14/0.98  merged_defs:                            0
% 4.14/0.98  merged_defs_ncl:                        0
% 4.14/0.98  bin_hyper_res:                          0
% 4.14/0.98  prep_cycles:                            4
% 4.14/0.98  pred_elim_time:                         0.008
% 4.14/0.98  splitting_time:                         0.
% 4.14/0.98  sem_filter_time:                        0.
% 4.14/0.98  monotx_time:                            0.
% 4.14/0.98  subtype_inf_time:                       0.
% 4.14/0.98  
% 4.14/0.98  ------ Problem properties
% 4.14/0.98  
% 4.14/0.98  clauses:                                29
% 4.14/0.98  conjectures:                            4
% 4.14/0.98  epr:                                    5
% 4.14/0.98  horn:                                   20
% 4.14/0.98  ground:                                 4
% 4.14/0.98  unary:                                  7
% 4.14/0.98  binary:                                 4
% 4.14/0.98  lits:                                   84
% 4.14/0.98  lits_eq:                                16
% 4.14/0.98  fd_pure:                                0
% 4.14/0.98  fd_pseudo:                              0
% 4.14/0.98  fd_cond:                                0
% 4.14/0.98  fd_pseudo_cond:                         5
% 4.14/0.98  ac_symbols:                             0
% 4.14/0.98  
% 4.14/0.98  ------ Propositional Solver
% 4.14/0.98  
% 4.14/0.98  prop_solver_calls:                      30
% 4.14/0.98  prop_fast_solver_calls:                 1678
% 4.14/0.98  smt_solver_calls:                       0
% 4.14/0.98  smt_fast_solver_calls:                  0
% 4.14/0.98  prop_num_of_clauses:                    5816
% 4.14/0.98  prop_preprocess_simplified:             12598
% 4.14/0.98  prop_fo_subsumed:                       68
% 4.14/0.98  prop_solver_time:                       0.
% 4.14/0.98  smt_solver_time:                        0.
% 4.14/0.98  smt_fast_solver_time:                   0.
% 4.14/0.98  prop_fast_solver_time:                  0.
% 4.14/0.98  prop_unsat_core_time:                   0.
% 4.14/0.98  
% 4.14/0.98  ------ QBF
% 4.14/0.98  
% 4.14/0.98  qbf_q_res:                              0
% 4.14/0.98  qbf_num_tautologies:                    0
% 4.14/0.98  qbf_prep_cycles:                        0
% 4.14/0.98  
% 4.14/0.98  ------ BMC1
% 4.14/0.98  
% 4.14/0.98  bmc1_current_bound:                     -1
% 4.14/0.98  bmc1_last_solved_bound:                 -1
% 4.14/0.98  bmc1_unsat_core_size:                   -1
% 4.14/0.98  bmc1_unsat_core_parents_size:           -1
% 4.14/0.98  bmc1_merge_next_fun:                    0
% 4.14/0.98  bmc1_unsat_core_clauses_time:           0.
% 4.14/0.98  
% 4.14/0.98  ------ Instantiation
% 4.14/0.98  
% 4.14/0.98  inst_num_of_clauses:                    1353
% 4.14/0.98  inst_num_in_passive:                    153
% 4.14/0.98  inst_num_in_active:                     702
% 4.14/0.98  inst_num_in_unprocessed:                498
% 4.14/0.98  inst_num_of_loops:                      770
% 4.14/0.98  inst_num_of_learning_restarts:          0
% 4.14/0.98  inst_num_moves_active_passive:          67
% 4.14/0.98  inst_lit_activity:                      0
% 4.14/0.98  inst_lit_activity_moves:                0
% 4.14/0.98  inst_num_tautologies:                   0
% 4.14/0.98  inst_num_prop_implied:                  0
% 4.14/0.98  inst_num_existing_simplified:           0
% 4.14/0.98  inst_num_eq_res_simplified:             0
% 4.14/0.98  inst_num_child_elim:                    0
% 4.14/0.98  inst_num_of_dismatching_blockings:      886
% 4.14/0.98  inst_num_of_non_proper_insts:           1904
% 4.14/0.98  inst_num_of_duplicates:                 0
% 4.14/0.98  inst_inst_num_from_inst_to_res:         0
% 4.14/0.98  inst_dismatching_checking_time:         0.
% 4.14/0.98  
% 4.14/0.98  ------ Resolution
% 4.14/0.98  
% 4.14/0.98  res_num_of_clauses:                     0
% 4.14/0.98  res_num_in_passive:                     0
% 4.14/0.98  res_num_in_active:                      0
% 4.14/0.98  res_num_of_loops:                       152
% 4.14/0.98  res_forward_subset_subsumed:            219
% 4.14/0.98  res_backward_subset_subsumed:           4
% 4.14/0.98  res_forward_subsumed:                   0
% 4.14/0.98  res_backward_subsumed:                  0
% 4.14/0.98  res_forward_subsumption_resolution:     5
% 4.14/0.98  res_backward_subsumption_resolution:    0
% 4.14/0.98  res_clause_to_clause_subsumption:       1817
% 4.14/0.98  res_orphan_elimination:                 0
% 4.14/0.98  res_tautology_del:                      107
% 4.14/0.98  res_num_eq_res_simplified:              0
% 4.14/0.98  res_num_sel_changes:                    0
% 4.14/0.98  res_moves_from_active_to_pass:          0
% 4.14/0.98  
% 4.14/0.98  ------ Superposition
% 4.14/0.98  
% 4.14/0.98  sup_time_total:                         0.
% 4.14/0.98  sup_time_generating:                    0.
% 4.14/0.98  sup_time_sim_full:                      0.
% 4.14/0.98  sup_time_sim_immed:                     0.
% 4.14/0.98  
% 4.14/0.98  sup_num_of_clauses:                     468
% 4.14/0.98  sup_num_in_active:                      110
% 4.14/0.98  sup_num_in_passive:                     358
% 4.14/0.98  sup_num_of_loops:                       153
% 4.14/0.98  sup_fw_superposition:                   289
% 4.14/0.98  sup_bw_superposition:                   434
% 4.14/0.98  sup_immediate_simplified:               116
% 4.14/0.98  sup_given_eliminated:                   4
% 4.14/0.98  comparisons_done:                       0
% 4.14/0.98  comparisons_avoided:                    64
% 4.14/0.98  
% 4.14/0.98  ------ Simplifications
% 4.14/0.98  
% 4.14/0.98  
% 4.14/0.98  sim_fw_subset_subsumed:                 22
% 4.14/0.98  sim_bw_subset_subsumed:                 38
% 4.14/0.98  sim_fw_subsumed:                        33
% 4.14/0.98  sim_bw_subsumed:                        47
% 4.14/0.98  sim_fw_subsumption_res:                 0
% 4.14/0.98  sim_bw_subsumption_res:                 0
% 4.14/0.98  sim_tautology_del:                      12
% 4.14/0.98  sim_eq_tautology_del:                   59
% 4.14/0.98  sim_eq_res_simp:                        1
% 4.14/0.98  sim_fw_demodulated:                     50
% 4.14/0.98  sim_bw_demodulated:                     0
% 4.14/0.98  sim_light_normalised:                   24
% 4.14/0.98  sim_joinable_taut:                      0
% 4.14/0.98  sim_joinable_simp:                      0
% 4.14/0.98  sim_ac_normalised:                      0
% 4.14/0.98  sim_smt_subsumption:                    0
% 4.14/0.98  
%------------------------------------------------------------------------------
