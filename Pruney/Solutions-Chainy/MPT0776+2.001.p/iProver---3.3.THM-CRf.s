%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:19 EST 2020

% Result     : Theorem 43.45s
% Output     : CNFRefutation 43.45s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 281 expanded)
%              Number of clauses        :   53 (  81 expanded)
%              Number of leaves         :   12 (  54 expanded)
%              Depth                    :   23
%              Number of atoms          :  424 (1287 expanded)
%              Number of equality atoms :  171 ( 378 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   15 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( ( r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f15,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f29,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | ~ r2_hidden(k4_tarski(X2,X1),X0)
              | ~ r2_hidden(k4_tarski(X1,X2),X0) )
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | ~ r2_hidden(k4_tarski(X4,X3),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0) )
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & r2_hidden(k4_tarski(X2,X1),X0)
          & r2_hidden(k4_tarski(X1,X2),X0) )
     => ( sK2(X0) != sK3(X0)
        & r2_hidden(k4_tarski(sK3(X0),sK2(X0)),X0)
        & r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ( sK2(X0) != sK3(X0)
            & r2_hidden(k4_tarski(sK3(X0),sK2(X0)),X0)
            & r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | ~ r2_hidden(k4_tarski(X4,X3),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0) )
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f30,f31])).

fof(f53,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | r2_hidden(k4_tarski(sK3(X0),sK2(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f69,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f54,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | sK2(X0) != sK3(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_2(X1)
       => v4_relat_2(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( v4_relat_2(X1)
         => v4_relat_2(k2_wellord1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ~ v4_relat_2(k2_wellord1(X1,X0))
      & v4_relat_2(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ~ v4_relat_2(k2_wellord1(X1,X0))
      & v4_relat_2(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( ~ v4_relat_2(k2_wellord1(X1,X0))
        & v4_relat_2(X1)
        & v1_relat_1(X1) )
   => ( ~ v4_relat_2(k2_wellord1(sK5,sK4))
      & v4_relat_2(sK5)
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ v4_relat_2(k2_wellord1(sK5,sK4))
    & v4_relat_2(sK5)
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f18,f33])).

fof(f56,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_wellord1(k2_wellord1(X2,X0),X1),k1_wellord1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_wellord1(k2_wellord1(X2,X0),X1),k1_wellord1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_wellord1(k2_wellord1(X2,X0),X1),k1_wellord1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f43])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f19])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f36,f43])).

fof(f67,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(equality_resolution,[],[f63])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f70,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f51,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ v4_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f57,plain,(
    v4_relat_2(sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f52,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f58,plain,(
    ~ v4_relat_2(k2_wellord1(sK5,sK4)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_wellord1(X0,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_780,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_wellord1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_16,plain,
    ( r2_hidden(k4_tarski(sK3(X0),sK2(X0)),X0)
    | v4_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_778,plain,
    ( r2_hidden(k4_tarski(sK3(X0),sK2(X0)),X0) = iProver_top
    | v4_relat_2(X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_11,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X2))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_783,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_wellord1(X2,X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2291,plain,
    ( sK3(X0) = sK2(X0)
    | r2_hidden(sK3(X0),k1_wellord1(X0,sK2(X0))) = iProver_top
    | v4_relat_2(X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_778,c_783])).

cnf(c_15,plain,
    ( v4_relat_2(X0)
    | ~ v1_relat_1(X0)
    | sK3(X0) != sK2(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_34,plain,
    ( sK3(X0) != sK2(X0)
    | v4_relat_2(X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3155,plain,
    ( r2_hidden(sK3(X0),k1_wellord1(X0,sK2(X0))) = iProver_top
    | v4_relat_2(X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2291,c_34])).

cnf(c_22,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_772,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_19,plain,
    ( r1_tarski(k1_wellord1(k2_wellord1(X0,X1),X2),k1_wellord1(X0,X2))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_775,plain,
    ( r1_tarski(k1_wellord1(k2_wellord1(X0,X1),X2),k1_wellord1(X0,X2)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_787,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1345,plain,
    ( k1_setfam_1(k2_tarski(k1_wellord1(k2_wellord1(X0,X1),X2),k1_wellord1(X0,X2))) = k1_wellord1(k2_wellord1(X0,X1),X2)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_775,c_787])).

cnf(c_1653,plain,
    ( k1_setfam_1(k2_tarski(k1_wellord1(k2_wellord1(sK5,X0),X1),k1_wellord1(sK5,X1))) = k1_wellord1(k2_wellord1(sK5,X0),X1) ),
    inference(superposition,[status(thm)],[c_772,c_1345])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_789,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1731,plain,
    ( r2_hidden(X0,k1_wellord1(k2_wellord1(sK5,X1),X2)) != iProver_top
    | r2_hidden(X0,k1_wellord1(sK5,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1653,c_789])).

cnf(c_3160,plain,
    ( r2_hidden(sK3(k2_wellord1(sK5,X0)),k1_wellord1(sK5,sK2(k2_wellord1(sK5,X0)))) = iProver_top
    | v4_relat_2(k2_wellord1(sK5,X0)) = iProver_top
    | v1_relat_1(k2_wellord1(sK5,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3155,c_1731])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_782,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3266,plain,
    ( r2_hidden(k4_tarski(sK3(k2_wellord1(sK5,X0)),sK2(k2_wellord1(sK5,X0))),sK5) = iProver_top
    | v4_relat_2(k2_wellord1(sK5,X0)) = iProver_top
    | v1_relat_1(k2_wellord1(sK5,X0)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3160,c_782])).

cnf(c_23,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3398,plain,
    ( v1_relat_1(k2_wellord1(sK5,X0)) != iProver_top
    | v4_relat_2(k2_wellord1(sK5,X0)) = iProver_top
    | r2_hidden(k4_tarski(sK3(k2_wellord1(sK5,X0)),sK2(k2_wellord1(sK5,X0))),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3266,c_23])).

cnf(c_3399,plain,
    ( r2_hidden(k4_tarski(sK3(k2_wellord1(sK5,X0)),sK2(k2_wellord1(sK5,X0))),sK5) = iProver_top
    | v4_relat_2(k2_wellord1(sK5,X0)) = iProver_top
    | v1_relat_1(k2_wellord1(sK5,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3398])).

cnf(c_18,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X1,X0),X2)
    | ~ v4_relat_2(X2)
    | ~ v1_relat_1(X2)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_776,plain,
    ( X0 = X1
    | r2_hidden(k4_tarski(X1,X0),X2) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
    | v4_relat_2(X2) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3405,plain,
    ( sK3(k2_wellord1(sK5,X0)) = sK2(k2_wellord1(sK5,X0))
    | r2_hidden(k4_tarski(sK2(k2_wellord1(sK5,X0)),sK3(k2_wellord1(sK5,X0))),sK5) != iProver_top
    | v4_relat_2(k2_wellord1(sK5,X0)) = iProver_top
    | v4_relat_2(sK5) != iProver_top
    | v1_relat_1(k2_wellord1(sK5,X0)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3399,c_776])).

cnf(c_21,negated_conjecture,
    ( v4_relat_2(sK5) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_24,plain,
    ( v4_relat_2(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_17,plain,
    ( r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
    | v4_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_777,plain,
    ( r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) = iProver_top
    | v4_relat_2(X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2292,plain,
    ( sK3(X0) = sK2(X0)
    | r2_hidden(sK2(X0),k1_wellord1(X0,sK3(X0))) = iProver_top
    | v4_relat_2(X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_777,c_783])).

cnf(c_3165,plain,
    ( r2_hidden(sK2(X0),k1_wellord1(X0,sK3(X0))) = iProver_top
    | v4_relat_2(X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2292,c_34])).

cnf(c_3170,plain,
    ( r2_hidden(sK2(k2_wellord1(sK5,X0)),k1_wellord1(sK5,sK3(k2_wellord1(sK5,X0)))) = iProver_top
    | v4_relat_2(k2_wellord1(sK5,X0)) = iProver_top
    | v1_relat_1(k2_wellord1(sK5,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3165,c_1731])).

cnf(c_3271,plain,
    ( r2_hidden(k4_tarski(sK2(k2_wellord1(sK5,X0)),sK3(k2_wellord1(sK5,X0))),sK5) = iProver_top
    | v4_relat_2(k2_wellord1(sK5,X0)) = iProver_top
    | v1_relat_1(k2_wellord1(sK5,X0)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3170,c_782])).

cnf(c_3451,plain,
    ( v1_relat_1(k2_wellord1(sK5,X0)) != iProver_top
    | v4_relat_2(k2_wellord1(sK5,X0)) = iProver_top
    | r2_hidden(k4_tarski(sK2(k2_wellord1(sK5,X0)),sK3(k2_wellord1(sK5,X0))),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3271,c_23])).

cnf(c_3452,plain,
    ( r2_hidden(k4_tarski(sK2(k2_wellord1(sK5,X0)),sK3(k2_wellord1(sK5,X0))),sK5) = iProver_top
    | v4_relat_2(k2_wellord1(sK5,X0)) = iProver_top
    | v1_relat_1(k2_wellord1(sK5,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3451])).

cnf(c_129031,plain,
    ( v1_relat_1(k2_wellord1(sK5,X0)) != iProver_top
    | sK3(k2_wellord1(sK5,X0)) = sK2(k2_wellord1(sK5,X0))
    | v4_relat_2(k2_wellord1(sK5,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3405,c_23,c_24,c_3452])).

cnf(c_129032,plain,
    ( sK3(k2_wellord1(sK5,X0)) = sK2(k2_wellord1(sK5,X0))
    | v4_relat_2(k2_wellord1(sK5,X0)) = iProver_top
    | v1_relat_1(k2_wellord1(sK5,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_129031])).

cnf(c_129037,plain,
    ( sK3(k2_wellord1(sK5,X0)) = sK2(k2_wellord1(sK5,X0))
    | v4_relat_2(k2_wellord1(sK5,X0)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_780,c_129032])).

cnf(c_129205,plain,
    ( v4_relat_2(k2_wellord1(sK5,X0)) = iProver_top
    | sK3(k2_wellord1(sK5,X0)) = sK2(k2_wellord1(sK5,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_129037,c_23])).

cnf(c_129206,plain,
    ( sK3(k2_wellord1(sK5,X0)) = sK2(k2_wellord1(sK5,X0))
    | v4_relat_2(k2_wellord1(sK5,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_129205])).

cnf(c_20,negated_conjecture,
    ( ~ v4_relat_2(k2_wellord1(sK5,sK4)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_774,plain,
    ( v4_relat_2(k2_wellord1(sK5,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_129211,plain,
    ( sK3(k2_wellord1(sK5,sK4)) = sK2(k2_wellord1(sK5,sK4)) ),
    inference(superposition,[status(thm)],[c_129206,c_774])).

cnf(c_842,plain,
    ( v1_relat_1(k2_wellord1(sK5,sK4))
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_342,plain,
    ( ~ v1_relat_1(X0)
    | k2_wellord1(sK5,sK4) != X0
    | sK3(X0) != sK2(X0) ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_343,plain,
    ( ~ v1_relat_1(k2_wellord1(sK5,sK4))
    | sK3(k2_wellord1(sK5,sK4)) != sK2(k2_wellord1(sK5,sK4)) ),
    inference(unflattening,[status(thm)],[c_342])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_129211,c_842,c_343,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:34:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 43.45/6.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 43.45/6.01  
% 43.45/6.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 43.45/6.01  
% 43.45/6.01  ------  iProver source info
% 43.45/6.01  
% 43.45/6.01  git: date: 2020-06-30 10:37:57 +0100
% 43.45/6.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 43.45/6.01  git: non_committed_changes: false
% 43.45/6.01  git: last_make_outside_of_git: false
% 43.45/6.01  
% 43.45/6.01  ------ 
% 43.45/6.01  
% 43.45/6.01  ------ Input Options
% 43.45/6.01  
% 43.45/6.01  --out_options                           all
% 43.45/6.01  --tptp_safe_out                         true
% 43.45/6.01  --problem_path                          ""
% 43.45/6.01  --include_path                          ""
% 43.45/6.01  --clausifier                            res/vclausify_rel
% 43.45/6.01  --clausifier_options                    ""
% 43.45/6.01  --stdin                                 false
% 43.45/6.01  --stats_out                             all
% 43.45/6.01  
% 43.45/6.01  ------ General Options
% 43.45/6.01  
% 43.45/6.01  --fof                                   false
% 43.45/6.01  --time_out_real                         305.
% 43.45/6.01  --time_out_virtual                      -1.
% 43.45/6.01  --symbol_type_check                     false
% 43.45/6.01  --clausify_out                          false
% 43.45/6.01  --sig_cnt_out                           false
% 43.45/6.01  --trig_cnt_out                          false
% 43.45/6.01  --trig_cnt_out_tolerance                1.
% 43.45/6.01  --trig_cnt_out_sk_spl                   false
% 43.45/6.01  --abstr_cl_out                          false
% 43.45/6.01  
% 43.45/6.01  ------ Global Options
% 43.45/6.01  
% 43.45/6.01  --schedule                              default
% 43.45/6.01  --add_important_lit                     false
% 43.45/6.01  --prop_solver_per_cl                    1000
% 43.45/6.01  --min_unsat_core                        false
% 43.45/6.01  --soft_assumptions                      false
% 43.45/6.01  --soft_lemma_size                       3
% 43.45/6.01  --prop_impl_unit_size                   0
% 43.45/6.01  --prop_impl_unit                        []
% 43.45/6.01  --share_sel_clauses                     true
% 43.45/6.01  --reset_solvers                         false
% 43.45/6.01  --bc_imp_inh                            [conj_cone]
% 43.45/6.01  --conj_cone_tolerance                   3.
% 43.45/6.01  --extra_neg_conj                        none
% 43.45/6.01  --large_theory_mode                     true
% 43.45/6.01  --prolific_symb_bound                   200
% 43.45/6.01  --lt_threshold                          2000
% 43.45/6.01  --clause_weak_htbl                      true
% 43.45/6.01  --gc_record_bc_elim                     false
% 43.45/6.01  
% 43.45/6.01  ------ Preprocessing Options
% 43.45/6.01  
% 43.45/6.01  --preprocessing_flag                    true
% 43.45/6.01  --time_out_prep_mult                    0.1
% 43.45/6.01  --splitting_mode                        input
% 43.45/6.01  --splitting_grd                         true
% 43.45/6.01  --splitting_cvd                         false
% 43.45/6.01  --splitting_cvd_svl                     false
% 43.45/6.01  --splitting_nvd                         32
% 43.45/6.01  --sub_typing                            true
% 43.45/6.01  --prep_gs_sim                           true
% 43.45/6.01  --prep_unflatten                        true
% 43.45/6.01  --prep_res_sim                          true
% 43.45/6.01  --prep_upred                            true
% 43.45/6.01  --prep_sem_filter                       exhaustive
% 43.45/6.01  --prep_sem_filter_out                   false
% 43.45/6.01  --pred_elim                             true
% 43.45/6.01  --res_sim_input                         true
% 43.45/6.01  --eq_ax_congr_red                       true
% 43.45/6.01  --pure_diseq_elim                       true
% 43.45/6.01  --brand_transform                       false
% 43.45/6.01  --non_eq_to_eq                          false
% 43.45/6.01  --prep_def_merge                        true
% 43.45/6.01  --prep_def_merge_prop_impl              false
% 43.45/6.01  --prep_def_merge_mbd                    true
% 43.45/6.01  --prep_def_merge_tr_red                 false
% 43.45/6.01  --prep_def_merge_tr_cl                  false
% 43.45/6.01  --smt_preprocessing                     true
% 43.45/6.01  --smt_ac_axioms                         fast
% 43.45/6.01  --preprocessed_out                      false
% 43.45/6.01  --preprocessed_stats                    false
% 43.45/6.01  
% 43.45/6.01  ------ Abstraction refinement Options
% 43.45/6.01  
% 43.45/6.01  --abstr_ref                             []
% 43.45/6.01  --abstr_ref_prep                        false
% 43.45/6.01  --abstr_ref_until_sat                   false
% 43.45/6.01  --abstr_ref_sig_restrict                funpre
% 43.45/6.01  --abstr_ref_af_restrict_to_split_sk     false
% 43.45/6.01  --abstr_ref_under                       []
% 43.45/6.01  
% 43.45/6.01  ------ SAT Options
% 43.45/6.01  
% 43.45/6.01  --sat_mode                              false
% 43.45/6.01  --sat_fm_restart_options                ""
% 43.45/6.01  --sat_gr_def                            false
% 43.45/6.01  --sat_epr_types                         true
% 43.45/6.01  --sat_non_cyclic_types                  false
% 43.45/6.01  --sat_finite_models                     false
% 43.45/6.01  --sat_fm_lemmas                         false
% 43.45/6.01  --sat_fm_prep                           false
% 43.45/6.01  --sat_fm_uc_incr                        true
% 43.45/6.01  --sat_out_model                         small
% 43.45/6.01  --sat_out_clauses                       false
% 43.45/6.01  
% 43.45/6.01  ------ QBF Options
% 43.45/6.01  
% 43.45/6.01  --qbf_mode                              false
% 43.45/6.01  --qbf_elim_univ                         false
% 43.45/6.01  --qbf_dom_inst                          none
% 43.45/6.01  --qbf_dom_pre_inst                      false
% 43.45/6.01  --qbf_sk_in                             false
% 43.45/6.01  --qbf_pred_elim                         true
% 43.45/6.01  --qbf_split                             512
% 43.45/6.01  
% 43.45/6.01  ------ BMC1 Options
% 43.45/6.01  
% 43.45/6.01  --bmc1_incremental                      false
% 43.45/6.01  --bmc1_axioms                           reachable_all
% 43.45/6.01  --bmc1_min_bound                        0
% 43.45/6.01  --bmc1_max_bound                        -1
% 43.45/6.01  --bmc1_max_bound_default                -1
% 43.45/6.01  --bmc1_symbol_reachability              true
% 43.45/6.01  --bmc1_property_lemmas                  false
% 43.45/6.01  --bmc1_k_induction                      false
% 43.45/6.01  --bmc1_non_equiv_states                 false
% 43.45/6.01  --bmc1_deadlock                         false
% 43.45/6.01  --bmc1_ucm                              false
% 43.45/6.01  --bmc1_add_unsat_core                   none
% 43.45/6.01  --bmc1_unsat_core_children              false
% 43.45/6.01  --bmc1_unsat_core_extrapolate_axioms    false
% 43.45/6.01  --bmc1_out_stat                         full
% 43.45/6.01  --bmc1_ground_init                      false
% 43.45/6.01  --bmc1_pre_inst_next_state              false
% 43.45/6.01  --bmc1_pre_inst_state                   false
% 43.45/6.01  --bmc1_pre_inst_reach_state             false
% 43.45/6.01  --bmc1_out_unsat_core                   false
% 43.45/6.01  --bmc1_aig_witness_out                  false
% 43.45/6.01  --bmc1_verbose                          false
% 43.45/6.01  --bmc1_dump_clauses_tptp                false
% 43.45/6.01  --bmc1_dump_unsat_core_tptp             false
% 43.45/6.01  --bmc1_dump_file                        -
% 43.45/6.01  --bmc1_ucm_expand_uc_limit              128
% 43.45/6.01  --bmc1_ucm_n_expand_iterations          6
% 43.45/6.01  --bmc1_ucm_extend_mode                  1
% 43.45/6.01  --bmc1_ucm_init_mode                    2
% 43.45/6.01  --bmc1_ucm_cone_mode                    none
% 43.45/6.01  --bmc1_ucm_reduced_relation_type        0
% 43.45/6.01  --bmc1_ucm_relax_model                  4
% 43.45/6.01  --bmc1_ucm_full_tr_after_sat            true
% 43.45/6.01  --bmc1_ucm_expand_neg_assumptions       false
% 43.45/6.01  --bmc1_ucm_layered_model                none
% 43.45/6.01  --bmc1_ucm_max_lemma_size               10
% 43.45/6.01  
% 43.45/6.01  ------ AIG Options
% 43.45/6.01  
% 43.45/6.01  --aig_mode                              false
% 43.45/6.01  
% 43.45/6.01  ------ Instantiation Options
% 43.45/6.01  
% 43.45/6.01  --instantiation_flag                    true
% 43.45/6.01  --inst_sos_flag                         true
% 43.45/6.01  --inst_sos_phase                        true
% 43.45/6.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 43.45/6.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 43.45/6.01  --inst_lit_sel_side                     num_symb
% 43.45/6.01  --inst_solver_per_active                1400
% 43.45/6.01  --inst_solver_calls_frac                1.
% 43.45/6.01  --inst_passive_queue_type               priority_queues
% 43.45/6.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 43.45/6.01  --inst_passive_queues_freq              [25;2]
% 43.45/6.01  --inst_dismatching                      true
% 43.45/6.01  --inst_eager_unprocessed_to_passive     true
% 43.45/6.01  --inst_prop_sim_given                   true
% 43.45/6.01  --inst_prop_sim_new                     false
% 43.45/6.01  --inst_subs_new                         false
% 43.45/6.01  --inst_eq_res_simp                      false
% 43.45/6.01  --inst_subs_given                       false
% 43.45/6.01  --inst_orphan_elimination               true
% 43.45/6.01  --inst_learning_loop_flag               true
% 43.45/6.01  --inst_learning_start                   3000
% 43.45/6.01  --inst_learning_factor                  2
% 43.45/6.01  --inst_start_prop_sim_after_learn       3
% 43.45/6.01  --inst_sel_renew                        solver
% 43.45/6.01  --inst_lit_activity_flag                true
% 43.45/6.01  --inst_restr_to_given                   false
% 43.45/6.01  --inst_activity_threshold               500
% 43.45/6.01  --inst_out_proof                        true
% 43.45/6.01  
% 43.45/6.01  ------ Resolution Options
% 43.45/6.01  
% 43.45/6.01  --resolution_flag                       true
% 43.45/6.01  --res_lit_sel                           adaptive
% 43.45/6.01  --res_lit_sel_side                      none
% 43.45/6.01  --res_ordering                          kbo
% 43.45/6.01  --res_to_prop_solver                    active
% 43.45/6.01  --res_prop_simpl_new                    false
% 43.45/6.01  --res_prop_simpl_given                  true
% 43.45/6.01  --res_passive_queue_type                priority_queues
% 43.45/6.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 43.45/6.01  --res_passive_queues_freq               [15;5]
% 43.45/6.01  --res_forward_subs                      full
% 43.45/6.01  --res_backward_subs                     full
% 43.45/6.01  --res_forward_subs_resolution           true
% 43.45/6.01  --res_backward_subs_resolution          true
% 43.45/6.01  --res_orphan_elimination                true
% 43.45/6.01  --res_time_limit                        2.
% 43.45/6.01  --res_out_proof                         true
% 43.45/6.01  
% 43.45/6.01  ------ Superposition Options
% 43.45/6.01  
% 43.45/6.01  --superposition_flag                    true
% 43.45/6.01  --sup_passive_queue_type                priority_queues
% 43.45/6.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 43.45/6.01  --sup_passive_queues_freq               [8;1;4]
% 43.45/6.01  --demod_completeness_check              fast
% 43.45/6.01  --demod_use_ground                      true
% 43.45/6.01  --sup_to_prop_solver                    passive
% 43.45/6.01  --sup_prop_simpl_new                    true
% 43.45/6.01  --sup_prop_simpl_given                  true
% 43.45/6.01  --sup_fun_splitting                     true
% 43.45/6.01  --sup_smt_interval                      50000
% 43.45/6.01  
% 43.45/6.01  ------ Superposition Simplification Setup
% 43.45/6.01  
% 43.45/6.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 43.45/6.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 43.45/6.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 43.45/6.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 43.45/6.01  --sup_full_triv                         [TrivRules;PropSubs]
% 43.45/6.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 43.45/6.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 43.45/6.01  --sup_immed_triv                        [TrivRules]
% 43.45/6.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 43.45/6.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.45/6.01  --sup_immed_bw_main                     []
% 43.45/6.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 43.45/6.01  --sup_input_triv                        [Unflattening;TrivRules]
% 43.45/6.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.45/6.01  --sup_input_bw                          []
% 43.45/6.01  
% 43.45/6.01  ------ Combination Options
% 43.45/6.01  
% 43.45/6.01  --comb_res_mult                         3
% 43.45/6.01  --comb_sup_mult                         2
% 43.45/6.01  --comb_inst_mult                        10
% 43.45/6.01  
% 43.45/6.01  ------ Debug Options
% 43.45/6.01  
% 43.45/6.01  --dbg_backtrace                         false
% 43.45/6.01  --dbg_dump_prop_clauses                 false
% 43.45/6.01  --dbg_dump_prop_clauses_file            -
% 43.45/6.01  --dbg_out_stat                          false
% 43.45/6.01  ------ Parsing...
% 43.45/6.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 43.45/6.01  
% 43.45/6.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 43.45/6.01  
% 43.45/6.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 43.45/6.01  
% 43.45/6.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.45/6.01  ------ Proving...
% 43.45/6.01  ------ Problem Properties 
% 43.45/6.01  
% 43.45/6.01  
% 43.45/6.01  clauses                                 23
% 43.45/6.01  conjectures                             3
% 43.45/6.01  EPR                                     2
% 43.45/6.01  Horn                                    15
% 43.45/6.01  unary                                   4
% 43.45/6.01  binary                                  6
% 43.45/6.01  lits                                    63
% 43.45/6.01  lits eq                                 13
% 43.45/6.01  fd_pure                                 0
% 43.45/6.01  fd_pseudo                               0
% 43.45/6.01  fd_cond                                 0
% 43.45/6.01  fd_pseudo_cond                          7
% 43.45/6.01  AC symbols                              0
% 43.45/6.01  
% 43.45/6.01  ------ Schedule dynamic 5 is on 
% 43.45/6.01  
% 43.45/6.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 43.45/6.01  
% 43.45/6.01  
% 43.45/6.01  ------ 
% 43.45/6.01  Current options:
% 43.45/6.01  ------ 
% 43.45/6.01  
% 43.45/6.01  ------ Input Options
% 43.45/6.01  
% 43.45/6.01  --out_options                           all
% 43.45/6.01  --tptp_safe_out                         true
% 43.45/6.01  --problem_path                          ""
% 43.45/6.01  --include_path                          ""
% 43.45/6.01  --clausifier                            res/vclausify_rel
% 43.45/6.01  --clausifier_options                    ""
% 43.45/6.01  --stdin                                 false
% 43.45/6.01  --stats_out                             all
% 43.45/6.01  
% 43.45/6.01  ------ General Options
% 43.45/6.01  
% 43.45/6.01  --fof                                   false
% 43.45/6.01  --time_out_real                         305.
% 43.45/6.01  --time_out_virtual                      -1.
% 43.45/6.01  --symbol_type_check                     false
% 43.45/6.01  --clausify_out                          false
% 43.45/6.01  --sig_cnt_out                           false
% 43.45/6.01  --trig_cnt_out                          false
% 43.45/6.01  --trig_cnt_out_tolerance                1.
% 43.45/6.01  --trig_cnt_out_sk_spl                   false
% 43.45/6.01  --abstr_cl_out                          false
% 43.45/6.01  
% 43.45/6.01  ------ Global Options
% 43.45/6.01  
% 43.45/6.01  --schedule                              default
% 43.45/6.01  --add_important_lit                     false
% 43.45/6.01  --prop_solver_per_cl                    1000
% 43.45/6.01  --min_unsat_core                        false
% 43.45/6.01  --soft_assumptions                      false
% 43.45/6.01  --soft_lemma_size                       3
% 43.45/6.01  --prop_impl_unit_size                   0
% 43.45/6.01  --prop_impl_unit                        []
% 43.45/6.01  --share_sel_clauses                     true
% 43.45/6.01  --reset_solvers                         false
% 43.45/6.01  --bc_imp_inh                            [conj_cone]
% 43.45/6.01  --conj_cone_tolerance                   3.
% 43.45/6.01  --extra_neg_conj                        none
% 43.45/6.01  --large_theory_mode                     true
% 43.45/6.01  --prolific_symb_bound                   200
% 43.45/6.01  --lt_threshold                          2000
% 43.45/6.01  --clause_weak_htbl                      true
% 43.45/6.01  --gc_record_bc_elim                     false
% 43.45/6.01  
% 43.45/6.01  ------ Preprocessing Options
% 43.45/6.01  
% 43.45/6.01  --preprocessing_flag                    true
% 43.45/6.01  --time_out_prep_mult                    0.1
% 43.45/6.01  --splitting_mode                        input
% 43.45/6.01  --splitting_grd                         true
% 43.45/6.01  --splitting_cvd                         false
% 43.45/6.01  --splitting_cvd_svl                     false
% 43.45/6.01  --splitting_nvd                         32
% 43.45/6.01  --sub_typing                            true
% 43.45/6.01  --prep_gs_sim                           true
% 43.45/6.01  --prep_unflatten                        true
% 43.45/6.01  --prep_res_sim                          true
% 43.45/6.01  --prep_upred                            true
% 43.45/6.01  --prep_sem_filter                       exhaustive
% 43.45/6.01  --prep_sem_filter_out                   false
% 43.45/6.01  --pred_elim                             true
% 43.45/6.01  --res_sim_input                         true
% 43.45/6.01  --eq_ax_congr_red                       true
% 43.45/6.01  --pure_diseq_elim                       true
% 43.45/6.01  --brand_transform                       false
% 43.45/6.01  --non_eq_to_eq                          false
% 43.45/6.01  --prep_def_merge                        true
% 43.45/6.01  --prep_def_merge_prop_impl              false
% 43.45/6.01  --prep_def_merge_mbd                    true
% 43.45/6.01  --prep_def_merge_tr_red                 false
% 43.45/6.01  --prep_def_merge_tr_cl                  false
% 43.45/6.01  --smt_preprocessing                     true
% 43.45/6.01  --smt_ac_axioms                         fast
% 43.45/6.01  --preprocessed_out                      false
% 43.45/6.01  --preprocessed_stats                    false
% 43.45/6.01  
% 43.45/6.01  ------ Abstraction refinement Options
% 43.45/6.01  
% 43.45/6.01  --abstr_ref                             []
% 43.45/6.01  --abstr_ref_prep                        false
% 43.45/6.01  --abstr_ref_until_sat                   false
% 43.45/6.01  --abstr_ref_sig_restrict                funpre
% 43.45/6.01  --abstr_ref_af_restrict_to_split_sk     false
% 43.45/6.01  --abstr_ref_under                       []
% 43.45/6.01  
% 43.45/6.01  ------ SAT Options
% 43.45/6.01  
% 43.45/6.01  --sat_mode                              false
% 43.45/6.01  --sat_fm_restart_options                ""
% 43.45/6.01  --sat_gr_def                            false
% 43.45/6.01  --sat_epr_types                         true
% 43.45/6.01  --sat_non_cyclic_types                  false
% 43.45/6.01  --sat_finite_models                     false
% 43.45/6.01  --sat_fm_lemmas                         false
% 43.45/6.01  --sat_fm_prep                           false
% 43.45/6.01  --sat_fm_uc_incr                        true
% 43.45/6.01  --sat_out_model                         small
% 43.45/6.01  --sat_out_clauses                       false
% 43.45/6.01  
% 43.45/6.01  ------ QBF Options
% 43.45/6.01  
% 43.45/6.01  --qbf_mode                              false
% 43.45/6.01  --qbf_elim_univ                         false
% 43.45/6.01  --qbf_dom_inst                          none
% 43.45/6.01  --qbf_dom_pre_inst                      false
% 43.45/6.01  --qbf_sk_in                             false
% 43.45/6.01  --qbf_pred_elim                         true
% 43.45/6.01  --qbf_split                             512
% 43.45/6.01  
% 43.45/6.01  ------ BMC1 Options
% 43.45/6.01  
% 43.45/6.01  --bmc1_incremental                      false
% 43.45/6.01  --bmc1_axioms                           reachable_all
% 43.45/6.01  --bmc1_min_bound                        0
% 43.45/6.01  --bmc1_max_bound                        -1
% 43.45/6.01  --bmc1_max_bound_default                -1
% 43.45/6.01  --bmc1_symbol_reachability              true
% 43.45/6.01  --bmc1_property_lemmas                  false
% 43.45/6.01  --bmc1_k_induction                      false
% 43.45/6.01  --bmc1_non_equiv_states                 false
% 43.45/6.01  --bmc1_deadlock                         false
% 43.45/6.01  --bmc1_ucm                              false
% 43.45/6.01  --bmc1_add_unsat_core                   none
% 43.45/6.01  --bmc1_unsat_core_children              false
% 43.45/6.01  --bmc1_unsat_core_extrapolate_axioms    false
% 43.45/6.01  --bmc1_out_stat                         full
% 43.45/6.01  --bmc1_ground_init                      false
% 43.45/6.01  --bmc1_pre_inst_next_state              false
% 43.45/6.01  --bmc1_pre_inst_state                   false
% 43.45/6.01  --bmc1_pre_inst_reach_state             false
% 43.45/6.01  --bmc1_out_unsat_core                   false
% 43.45/6.01  --bmc1_aig_witness_out                  false
% 43.45/6.01  --bmc1_verbose                          false
% 43.45/6.01  --bmc1_dump_clauses_tptp                false
% 43.45/6.01  --bmc1_dump_unsat_core_tptp             false
% 43.45/6.01  --bmc1_dump_file                        -
% 43.45/6.01  --bmc1_ucm_expand_uc_limit              128
% 43.45/6.01  --bmc1_ucm_n_expand_iterations          6
% 43.45/6.01  --bmc1_ucm_extend_mode                  1
% 43.45/6.01  --bmc1_ucm_init_mode                    2
% 43.45/6.01  --bmc1_ucm_cone_mode                    none
% 43.45/6.01  --bmc1_ucm_reduced_relation_type        0
% 43.45/6.01  --bmc1_ucm_relax_model                  4
% 43.45/6.01  --bmc1_ucm_full_tr_after_sat            true
% 43.45/6.01  --bmc1_ucm_expand_neg_assumptions       false
% 43.45/6.01  --bmc1_ucm_layered_model                none
% 43.45/6.01  --bmc1_ucm_max_lemma_size               10
% 43.45/6.01  
% 43.45/6.01  ------ AIG Options
% 43.45/6.01  
% 43.45/6.01  --aig_mode                              false
% 43.45/6.01  
% 43.45/6.01  ------ Instantiation Options
% 43.45/6.01  
% 43.45/6.01  --instantiation_flag                    true
% 43.45/6.01  --inst_sos_flag                         true
% 43.45/6.01  --inst_sos_phase                        true
% 43.45/6.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 43.45/6.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 43.45/6.01  --inst_lit_sel_side                     none
% 43.45/6.01  --inst_solver_per_active                1400
% 43.45/6.01  --inst_solver_calls_frac                1.
% 43.45/6.01  --inst_passive_queue_type               priority_queues
% 43.45/6.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 43.45/6.01  --inst_passive_queues_freq              [25;2]
% 43.45/6.01  --inst_dismatching                      true
% 43.45/6.01  --inst_eager_unprocessed_to_passive     true
% 43.45/6.01  --inst_prop_sim_given                   true
% 43.45/6.01  --inst_prop_sim_new                     false
% 43.45/6.01  --inst_subs_new                         false
% 43.45/6.01  --inst_eq_res_simp                      false
% 43.45/6.01  --inst_subs_given                       false
% 43.45/6.01  --inst_orphan_elimination               true
% 43.45/6.01  --inst_learning_loop_flag               true
% 43.45/6.01  --inst_learning_start                   3000
% 43.45/6.01  --inst_learning_factor                  2
% 43.45/6.01  --inst_start_prop_sim_after_learn       3
% 43.45/6.01  --inst_sel_renew                        solver
% 43.45/6.01  --inst_lit_activity_flag                true
% 43.45/6.01  --inst_restr_to_given                   false
% 43.45/6.01  --inst_activity_threshold               500
% 43.45/6.01  --inst_out_proof                        true
% 43.45/6.01  
% 43.45/6.01  ------ Resolution Options
% 43.45/6.01  
% 43.45/6.01  --resolution_flag                       false
% 43.45/6.01  --res_lit_sel                           adaptive
% 43.45/6.01  --res_lit_sel_side                      none
% 43.45/6.01  --res_ordering                          kbo
% 43.45/6.01  --res_to_prop_solver                    active
% 43.45/6.01  --res_prop_simpl_new                    false
% 43.45/6.01  --res_prop_simpl_given                  true
% 43.45/6.01  --res_passive_queue_type                priority_queues
% 43.45/6.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 43.45/6.01  --res_passive_queues_freq               [15;5]
% 43.45/6.01  --res_forward_subs                      full
% 43.45/6.01  --res_backward_subs                     full
% 43.45/6.01  --res_forward_subs_resolution           true
% 43.45/6.01  --res_backward_subs_resolution          true
% 43.45/6.01  --res_orphan_elimination                true
% 43.45/6.01  --res_time_limit                        2.
% 43.45/6.01  --res_out_proof                         true
% 43.45/6.01  
% 43.45/6.01  ------ Superposition Options
% 43.45/6.01  
% 43.45/6.01  --superposition_flag                    true
% 43.45/6.01  --sup_passive_queue_type                priority_queues
% 43.45/6.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 43.45/6.01  --sup_passive_queues_freq               [8;1;4]
% 43.45/6.01  --demod_completeness_check              fast
% 43.45/6.01  --demod_use_ground                      true
% 43.45/6.01  --sup_to_prop_solver                    passive
% 43.45/6.01  --sup_prop_simpl_new                    true
% 43.45/6.01  --sup_prop_simpl_given                  true
% 43.45/6.01  --sup_fun_splitting                     true
% 43.45/6.01  --sup_smt_interval                      50000
% 43.45/6.01  
% 43.45/6.01  ------ Superposition Simplification Setup
% 43.45/6.01  
% 43.45/6.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 43.45/6.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 43.45/6.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 43.45/6.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 43.45/6.01  --sup_full_triv                         [TrivRules;PropSubs]
% 43.45/6.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 43.45/6.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 43.45/6.01  --sup_immed_triv                        [TrivRules]
% 43.45/6.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 43.45/6.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.45/6.01  --sup_immed_bw_main                     []
% 43.45/6.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 43.45/6.01  --sup_input_triv                        [Unflattening;TrivRules]
% 43.45/6.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.45/6.01  --sup_input_bw                          []
% 43.45/6.01  
% 43.45/6.01  ------ Combination Options
% 43.45/6.01  
% 43.45/6.01  --comb_res_mult                         3
% 43.45/6.01  --comb_sup_mult                         2
% 43.45/6.01  --comb_inst_mult                        10
% 43.45/6.01  
% 43.45/6.01  ------ Debug Options
% 43.45/6.01  
% 43.45/6.01  --dbg_backtrace                         false
% 43.45/6.01  --dbg_dump_prop_clauses                 false
% 43.45/6.01  --dbg_dump_prop_clauses_file            -
% 43.45/6.01  --dbg_out_stat                          false
% 43.45/6.01  
% 43.45/6.01  
% 43.45/6.01  
% 43.45/6.01  
% 43.45/6.01  ------ Proving...
% 43.45/6.01  
% 43.45/6.01  
% 43.45/6.01  % SZS status Theorem for theBenchmark.p
% 43.45/6.01  
% 43.45/6.01  % SZS output start CNFRefutation for theBenchmark.p
% 43.45/6.01  
% 43.45/6.01  fof(f6,axiom,(
% 43.45/6.01    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k2_wellord1(X0,X1)))),
% 43.45/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.45/6.01  
% 43.45/6.01  fof(f13,plain,(
% 43.45/6.01    ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0))),
% 43.45/6.01    inference(ennf_transformation,[],[f6])).
% 43.45/6.01  
% 43.45/6.01  fof(f50,plain,(
% 43.45/6.01    ( ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 43.45/6.01    inference(cnf_transformation,[],[f13])).
% 43.45/6.01  
% 43.45/6.01  fof(f7,axiom,(
% 43.45/6.01    ! [X0] : (v1_relat_1(X0) => (v4_relat_2(X0) <=> ! [X1,X2] : ((r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => X1 = X2)))),
% 43.45/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.45/6.01  
% 43.45/6.01  fof(f14,plain,(
% 43.45/6.01    ! [X0] : ((v4_relat_2(X0) <=> ! [X1,X2] : (X1 = X2 | (~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)))) | ~v1_relat_1(X0))),
% 43.45/6.01    inference(ennf_transformation,[],[f7])).
% 43.45/6.01  
% 43.45/6.01  fof(f15,plain,(
% 43.45/6.01    ! [X0] : ((v4_relat_2(X0) <=> ! [X1,X2] : (X1 = X2 | ~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0))) | ~v1_relat_1(X0))),
% 43.45/6.01    inference(flattening,[],[f14])).
% 43.45/6.01  
% 43.45/6.01  fof(f29,plain,(
% 43.45/6.01    ! [X0] : (((v4_relat_2(X0) | ? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X1,X2] : (X1 = X2 | ~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)) | ~v4_relat_2(X0))) | ~v1_relat_1(X0))),
% 43.45/6.01    inference(nnf_transformation,[],[f15])).
% 43.45/6.01  
% 43.45/6.01  fof(f30,plain,(
% 43.45/6.01    ! [X0] : (((v4_relat_2(X0) | ? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X3,X4] : (X3 = X4 | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~v4_relat_2(X0))) | ~v1_relat_1(X0))),
% 43.45/6.01    inference(rectify,[],[f29])).
% 43.45/6.01  
% 43.45/6.01  fof(f31,plain,(
% 43.45/6.01    ! [X0] : (? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => (sK2(X0) != sK3(X0) & r2_hidden(k4_tarski(sK3(X0),sK2(X0)),X0) & r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)))),
% 43.45/6.01    introduced(choice_axiom,[])).
% 43.45/6.01  
% 43.45/6.01  fof(f32,plain,(
% 43.45/6.01    ! [X0] : (((v4_relat_2(X0) | (sK2(X0) != sK3(X0) & r2_hidden(k4_tarski(sK3(X0),sK2(X0)),X0) & r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0))) & (! [X3,X4] : (X3 = X4 | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~v4_relat_2(X0))) | ~v1_relat_1(X0))),
% 43.45/6.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f30,f31])).
% 43.45/6.01  
% 43.45/6.01  fof(f53,plain,(
% 43.45/6.01    ( ! [X0] : (v4_relat_2(X0) | r2_hidden(k4_tarski(sK3(X0),sK2(X0)),X0) | ~v1_relat_1(X0)) )),
% 43.45/6.01    inference(cnf_transformation,[],[f32])).
% 43.45/6.01  
% 43.45/6.01  fof(f5,axiom,(
% 43.45/6.01    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 43.45/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.45/6.01  
% 43.45/6.01  fof(f12,plain,(
% 43.45/6.01    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 43.45/6.01    inference(ennf_transformation,[],[f5])).
% 43.45/6.01  
% 43.45/6.01  fof(f24,plain,(
% 43.45/6.01    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 43.45/6.01    inference(nnf_transformation,[],[f12])).
% 43.45/6.01  
% 43.45/6.01  fof(f25,plain,(
% 43.45/6.01    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 43.45/6.01    inference(flattening,[],[f24])).
% 43.45/6.01  
% 43.45/6.01  fof(f26,plain,(
% 43.45/6.01    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 43.45/6.01    inference(rectify,[],[f25])).
% 43.45/6.01  
% 43.45/6.01  fof(f27,plain,(
% 43.45/6.01    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2))) => ((~r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) | sK1(X0,X1,X2) = X1 | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) & sK1(X0,X1,X2) != X1) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 43.45/6.01    introduced(choice_axiom,[])).
% 43.45/6.01  
% 43.45/6.01  fof(f28,plain,(
% 43.45/6.01    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) | sK1(X0,X1,X2) = X1 | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK1(X0,X1,X2),X1),X0) & sK1(X0,X1,X2) != X1) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 43.45/6.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).
% 43.45/6.01  
% 43.45/6.01  fof(f46,plain,(
% 43.45/6.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 43.45/6.01    inference(cnf_transformation,[],[f28])).
% 43.45/6.01  
% 43.45/6.01  fof(f69,plain,(
% 43.45/6.01    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_wellord1(X0,X1)) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | ~v1_relat_1(X0)) )),
% 43.45/6.01    inference(equality_resolution,[],[f46])).
% 43.45/6.01  
% 43.45/6.01  fof(f54,plain,(
% 43.45/6.01    ( ! [X0] : (v4_relat_2(X0) | sK2(X0) != sK3(X0) | ~v1_relat_1(X0)) )),
% 43.45/6.01    inference(cnf_transformation,[],[f32])).
% 43.45/6.01  
% 43.45/6.01  fof(f9,conjecture,(
% 43.45/6.01    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_2(X1) => v4_relat_2(k2_wellord1(X1,X0))))),
% 43.45/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.45/6.01  
% 43.45/6.01  fof(f10,negated_conjecture,(
% 43.45/6.01    ~! [X0,X1] : (v1_relat_1(X1) => (v4_relat_2(X1) => v4_relat_2(k2_wellord1(X1,X0))))),
% 43.45/6.01    inference(negated_conjecture,[],[f9])).
% 43.45/6.01  
% 43.45/6.01  fof(f17,plain,(
% 43.45/6.01    ? [X0,X1] : ((~v4_relat_2(k2_wellord1(X1,X0)) & v4_relat_2(X1)) & v1_relat_1(X1))),
% 43.45/6.01    inference(ennf_transformation,[],[f10])).
% 43.45/6.01  
% 43.45/6.01  fof(f18,plain,(
% 43.45/6.01    ? [X0,X1] : (~v4_relat_2(k2_wellord1(X1,X0)) & v4_relat_2(X1) & v1_relat_1(X1))),
% 43.45/6.01    inference(flattening,[],[f17])).
% 43.45/6.01  
% 43.45/6.01  fof(f33,plain,(
% 43.45/6.01    ? [X0,X1] : (~v4_relat_2(k2_wellord1(X1,X0)) & v4_relat_2(X1) & v1_relat_1(X1)) => (~v4_relat_2(k2_wellord1(sK5,sK4)) & v4_relat_2(sK5) & v1_relat_1(sK5))),
% 43.45/6.01    introduced(choice_axiom,[])).
% 43.45/6.01  
% 43.45/6.01  fof(f34,plain,(
% 43.45/6.01    ~v4_relat_2(k2_wellord1(sK5,sK4)) & v4_relat_2(sK5) & v1_relat_1(sK5)),
% 43.45/6.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f18,f33])).
% 43.45/6.01  
% 43.45/6.01  fof(f56,plain,(
% 43.45/6.01    v1_relat_1(sK5)),
% 43.45/6.01    inference(cnf_transformation,[],[f34])).
% 43.45/6.01  
% 43.45/6.01  fof(f8,axiom,(
% 43.45/6.01    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k1_wellord1(k2_wellord1(X2,X0),X1),k1_wellord1(X2,X1)))),
% 43.45/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.45/6.01  
% 43.45/6.01  fof(f16,plain,(
% 43.45/6.01    ! [X0,X1,X2] : (r1_tarski(k1_wellord1(k2_wellord1(X2,X0),X1),k1_wellord1(X2,X1)) | ~v1_relat_1(X2))),
% 43.45/6.01    inference(ennf_transformation,[],[f8])).
% 43.45/6.01  
% 43.45/6.01  fof(f55,plain,(
% 43.45/6.01    ( ! [X2,X0,X1] : (r1_tarski(k1_wellord1(k2_wellord1(X2,X0),X1),k1_wellord1(X2,X1)) | ~v1_relat_1(X2)) )),
% 43.45/6.01    inference(cnf_transformation,[],[f16])).
% 43.45/6.01  
% 43.45/6.01  fof(f2,axiom,(
% 43.45/6.01    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 43.45/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.45/6.01  
% 43.45/6.01  fof(f11,plain,(
% 43.45/6.01    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 43.45/6.01    inference(ennf_transformation,[],[f2])).
% 43.45/6.01  
% 43.45/6.01  fof(f41,plain,(
% 43.45/6.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 43.45/6.01    inference(cnf_transformation,[],[f11])).
% 43.45/6.01  
% 43.45/6.01  fof(f4,axiom,(
% 43.45/6.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 43.45/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.45/6.01  
% 43.45/6.01  fof(f43,plain,(
% 43.45/6.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 43.45/6.01    inference(cnf_transformation,[],[f4])).
% 43.45/6.01  
% 43.45/6.01  fof(f65,plain,(
% 43.45/6.01    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 43.45/6.01    inference(definition_unfolding,[],[f41,f43])).
% 43.45/6.01  
% 43.45/6.01  fof(f1,axiom,(
% 43.45/6.01    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 43.45/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.45/6.01  
% 43.45/6.01  fof(f19,plain,(
% 43.45/6.01    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 43.45/6.01    inference(nnf_transformation,[],[f1])).
% 43.45/6.01  
% 43.45/6.01  fof(f20,plain,(
% 43.45/6.01    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 43.45/6.01    inference(flattening,[],[f19])).
% 43.45/6.01  
% 43.45/6.01  fof(f21,plain,(
% 43.45/6.01    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 43.45/6.01    inference(rectify,[],[f20])).
% 43.45/6.01  
% 43.45/6.01  fof(f22,plain,(
% 43.45/6.01    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 43.45/6.01    introduced(choice_axiom,[])).
% 43.45/6.01  
% 43.45/6.01  fof(f23,plain,(
% 43.45/6.01    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 43.45/6.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 43.45/6.01  
% 43.45/6.01  fof(f36,plain,(
% 43.45/6.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 43.45/6.01    inference(cnf_transformation,[],[f23])).
% 43.45/6.01  
% 43.45/6.01  fof(f63,plain,(
% 43.45/6.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 43.45/6.01    inference(definition_unfolding,[],[f36,f43])).
% 43.45/6.01  
% 43.45/6.01  fof(f67,plain,(
% 43.45/6.01    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 43.45/6.01    inference(equality_resolution,[],[f63])).
% 43.45/6.01  
% 43.45/6.01  fof(f45,plain,(
% 43.45/6.01    ( ! [X4,X2,X0,X1] : (r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 43.45/6.01    inference(cnf_transformation,[],[f28])).
% 43.45/6.01  
% 43.45/6.01  fof(f70,plain,(
% 43.45/6.01    ( ! [X4,X0,X1] : (r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(X4,k1_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 43.45/6.01    inference(equality_resolution,[],[f45])).
% 43.45/6.01  
% 43.45/6.01  fof(f51,plain,(
% 43.45/6.01    ( ! [X4,X0,X3] : (X3 = X4 | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~v4_relat_2(X0) | ~v1_relat_1(X0)) )),
% 43.45/6.01    inference(cnf_transformation,[],[f32])).
% 43.45/6.01  
% 43.45/6.01  fof(f57,plain,(
% 43.45/6.01    v4_relat_2(sK5)),
% 43.45/6.01    inference(cnf_transformation,[],[f34])).
% 43.45/6.01  
% 43.45/6.01  fof(f52,plain,(
% 43.45/6.01    ( ! [X0] : (v4_relat_2(X0) | r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) | ~v1_relat_1(X0)) )),
% 43.45/6.01    inference(cnf_transformation,[],[f32])).
% 43.45/6.01  
% 43.45/6.01  fof(f58,plain,(
% 43.45/6.01    ~v4_relat_2(k2_wellord1(sK5,sK4))),
% 43.45/6.01    inference(cnf_transformation,[],[f34])).
% 43.45/6.01  
% 43.45/6.01  cnf(c_14,plain,
% 43.45/6.01      ( ~ v1_relat_1(X0) | v1_relat_1(k2_wellord1(X0,X1)) ),
% 43.45/6.01      inference(cnf_transformation,[],[f50]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_780,plain,
% 43.45/6.01      ( v1_relat_1(X0) != iProver_top
% 43.45/6.01      | v1_relat_1(k2_wellord1(X0,X1)) = iProver_top ),
% 43.45/6.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_16,plain,
% 43.45/6.01      ( r2_hidden(k4_tarski(sK3(X0),sK2(X0)),X0)
% 43.45/6.01      | v4_relat_2(X0)
% 43.45/6.01      | ~ v1_relat_1(X0) ),
% 43.45/6.01      inference(cnf_transformation,[],[f53]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_778,plain,
% 43.45/6.01      ( r2_hidden(k4_tarski(sK3(X0),sK2(X0)),X0) = iProver_top
% 43.45/6.01      | v4_relat_2(X0) = iProver_top
% 43.45/6.01      | v1_relat_1(X0) != iProver_top ),
% 43.45/6.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_11,plain,
% 43.45/6.01      ( r2_hidden(X0,k1_wellord1(X1,X2))
% 43.45/6.01      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 43.45/6.01      | ~ v1_relat_1(X1)
% 43.45/6.01      | X0 = X2 ),
% 43.45/6.01      inference(cnf_transformation,[],[f69]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_783,plain,
% 43.45/6.01      ( X0 = X1
% 43.45/6.01      | r2_hidden(X0,k1_wellord1(X2,X1)) = iProver_top
% 43.45/6.01      | r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
% 43.45/6.01      | v1_relat_1(X2) != iProver_top ),
% 43.45/6.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_2291,plain,
% 43.45/6.01      ( sK3(X0) = sK2(X0)
% 43.45/6.01      | r2_hidden(sK3(X0),k1_wellord1(X0,sK2(X0))) = iProver_top
% 43.45/6.01      | v4_relat_2(X0) = iProver_top
% 43.45/6.01      | v1_relat_1(X0) != iProver_top ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_778,c_783]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_15,plain,
% 43.45/6.01      ( v4_relat_2(X0) | ~ v1_relat_1(X0) | sK3(X0) != sK2(X0) ),
% 43.45/6.01      inference(cnf_transformation,[],[f54]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_34,plain,
% 43.45/6.01      ( sK3(X0) != sK2(X0)
% 43.45/6.01      | v4_relat_2(X0) = iProver_top
% 43.45/6.01      | v1_relat_1(X0) != iProver_top ),
% 43.45/6.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_3155,plain,
% 43.45/6.01      ( r2_hidden(sK3(X0),k1_wellord1(X0,sK2(X0))) = iProver_top
% 43.45/6.01      | v4_relat_2(X0) = iProver_top
% 43.45/6.01      | v1_relat_1(X0) != iProver_top ),
% 43.45/6.01      inference(global_propositional_subsumption,
% 43.45/6.01                [status(thm)],
% 43.45/6.01                [c_2291,c_34]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_22,negated_conjecture,
% 43.45/6.01      ( v1_relat_1(sK5) ),
% 43.45/6.01      inference(cnf_transformation,[],[f56]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_772,plain,
% 43.45/6.01      ( v1_relat_1(sK5) = iProver_top ),
% 43.45/6.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_19,plain,
% 43.45/6.01      ( r1_tarski(k1_wellord1(k2_wellord1(X0,X1),X2),k1_wellord1(X0,X2))
% 43.45/6.01      | ~ v1_relat_1(X0) ),
% 43.45/6.01      inference(cnf_transformation,[],[f55]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_775,plain,
% 43.45/6.01      ( r1_tarski(k1_wellord1(k2_wellord1(X0,X1),X2),k1_wellord1(X0,X2)) = iProver_top
% 43.45/6.01      | v1_relat_1(X0) != iProver_top ),
% 43.45/6.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_6,plain,
% 43.45/6.01      ( ~ r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
% 43.45/6.01      inference(cnf_transformation,[],[f65]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_787,plain,
% 43.45/6.01      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
% 43.45/6.01      | r1_tarski(X0,X1) != iProver_top ),
% 43.45/6.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_1345,plain,
% 43.45/6.01      ( k1_setfam_1(k2_tarski(k1_wellord1(k2_wellord1(X0,X1),X2),k1_wellord1(X0,X2))) = k1_wellord1(k2_wellord1(X0,X1),X2)
% 43.45/6.01      | v1_relat_1(X0) != iProver_top ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_775,c_787]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_1653,plain,
% 43.45/6.01      ( k1_setfam_1(k2_tarski(k1_wellord1(k2_wellord1(sK5,X0),X1),k1_wellord1(sK5,X1))) = k1_wellord1(k2_wellord1(sK5,X0),X1) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_772,c_1345]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_4,plain,
% 43.45/6.01      ( r2_hidden(X0,X1)
% 43.45/6.01      | ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
% 43.45/6.01      inference(cnf_transformation,[],[f67]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_789,plain,
% 43.45/6.01      ( r2_hidden(X0,X1) = iProver_top
% 43.45/6.01      | r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) != iProver_top ),
% 43.45/6.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_1731,plain,
% 43.45/6.01      ( r2_hidden(X0,k1_wellord1(k2_wellord1(sK5,X1),X2)) != iProver_top
% 43.45/6.01      | r2_hidden(X0,k1_wellord1(sK5,X2)) = iProver_top ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_1653,c_789]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_3160,plain,
% 43.45/6.01      ( r2_hidden(sK3(k2_wellord1(sK5,X0)),k1_wellord1(sK5,sK2(k2_wellord1(sK5,X0)))) = iProver_top
% 43.45/6.01      | v4_relat_2(k2_wellord1(sK5,X0)) = iProver_top
% 43.45/6.01      | v1_relat_1(k2_wellord1(sK5,X0)) != iProver_top ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_3155,c_1731]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_12,plain,
% 43.45/6.01      ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
% 43.45/6.01      | r2_hidden(k4_tarski(X0,X2),X1)
% 43.45/6.01      | ~ v1_relat_1(X1) ),
% 43.45/6.01      inference(cnf_transformation,[],[f70]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_782,plain,
% 43.45/6.01      ( r2_hidden(X0,k1_wellord1(X1,X2)) != iProver_top
% 43.45/6.01      | r2_hidden(k4_tarski(X0,X2),X1) = iProver_top
% 43.45/6.01      | v1_relat_1(X1) != iProver_top ),
% 43.45/6.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_3266,plain,
% 43.45/6.01      ( r2_hidden(k4_tarski(sK3(k2_wellord1(sK5,X0)),sK2(k2_wellord1(sK5,X0))),sK5) = iProver_top
% 43.45/6.01      | v4_relat_2(k2_wellord1(sK5,X0)) = iProver_top
% 43.45/6.01      | v1_relat_1(k2_wellord1(sK5,X0)) != iProver_top
% 43.45/6.01      | v1_relat_1(sK5) != iProver_top ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_3160,c_782]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_23,plain,
% 43.45/6.01      ( v1_relat_1(sK5) = iProver_top ),
% 43.45/6.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_3398,plain,
% 43.45/6.01      ( v1_relat_1(k2_wellord1(sK5,X0)) != iProver_top
% 43.45/6.01      | v4_relat_2(k2_wellord1(sK5,X0)) = iProver_top
% 43.45/6.01      | r2_hidden(k4_tarski(sK3(k2_wellord1(sK5,X0)),sK2(k2_wellord1(sK5,X0))),sK5) = iProver_top ),
% 43.45/6.01      inference(global_propositional_subsumption,
% 43.45/6.01                [status(thm)],
% 43.45/6.01                [c_3266,c_23]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_3399,plain,
% 43.45/6.01      ( r2_hidden(k4_tarski(sK3(k2_wellord1(sK5,X0)),sK2(k2_wellord1(sK5,X0))),sK5) = iProver_top
% 43.45/6.01      | v4_relat_2(k2_wellord1(sK5,X0)) = iProver_top
% 43.45/6.01      | v1_relat_1(k2_wellord1(sK5,X0)) != iProver_top ),
% 43.45/6.01      inference(renaming,[status(thm)],[c_3398]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_18,plain,
% 43.45/6.01      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 43.45/6.01      | ~ r2_hidden(k4_tarski(X1,X0),X2)
% 43.45/6.01      | ~ v4_relat_2(X2)
% 43.45/6.01      | ~ v1_relat_1(X2)
% 43.45/6.01      | X1 = X0 ),
% 43.45/6.01      inference(cnf_transformation,[],[f51]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_776,plain,
% 43.45/6.01      ( X0 = X1
% 43.45/6.01      | r2_hidden(k4_tarski(X1,X0),X2) != iProver_top
% 43.45/6.01      | r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
% 43.45/6.01      | v4_relat_2(X2) != iProver_top
% 43.45/6.01      | v1_relat_1(X2) != iProver_top ),
% 43.45/6.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_3405,plain,
% 43.45/6.01      ( sK3(k2_wellord1(sK5,X0)) = sK2(k2_wellord1(sK5,X0))
% 43.45/6.01      | r2_hidden(k4_tarski(sK2(k2_wellord1(sK5,X0)),sK3(k2_wellord1(sK5,X0))),sK5) != iProver_top
% 43.45/6.01      | v4_relat_2(k2_wellord1(sK5,X0)) = iProver_top
% 43.45/6.01      | v4_relat_2(sK5) != iProver_top
% 43.45/6.01      | v1_relat_1(k2_wellord1(sK5,X0)) != iProver_top
% 43.45/6.01      | v1_relat_1(sK5) != iProver_top ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_3399,c_776]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_21,negated_conjecture,
% 43.45/6.01      ( v4_relat_2(sK5) ),
% 43.45/6.01      inference(cnf_transformation,[],[f57]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_24,plain,
% 43.45/6.01      ( v4_relat_2(sK5) = iProver_top ),
% 43.45/6.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_17,plain,
% 43.45/6.01      ( r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
% 43.45/6.01      | v4_relat_2(X0)
% 43.45/6.01      | ~ v1_relat_1(X0) ),
% 43.45/6.01      inference(cnf_transformation,[],[f52]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_777,plain,
% 43.45/6.01      ( r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) = iProver_top
% 43.45/6.01      | v4_relat_2(X0) = iProver_top
% 43.45/6.01      | v1_relat_1(X0) != iProver_top ),
% 43.45/6.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_2292,plain,
% 43.45/6.01      ( sK3(X0) = sK2(X0)
% 43.45/6.01      | r2_hidden(sK2(X0),k1_wellord1(X0,sK3(X0))) = iProver_top
% 43.45/6.01      | v4_relat_2(X0) = iProver_top
% 43.45/6.01      | v1_relat_1(X0) != iProver_top ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_777,c_783]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_3165,plain,
% 43.45/6.01      ( r2_hidden(sK2(X0),k1_wellord1(X0,sK3(X0))) = iProver_top
% 43.45/6.01      | v4_relat_2(X0) = iProver_top
% 43.45/6.01      | v1_relat_1(X0) != iProver_top ),
% 43.45/6.01      inference(global_propositional_subsumption,
% 43.45/6.01                [status(thm)],
% 43.45/6.01                [c_2292,c_34]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_3170,plain,
% 43.45/6.01      ( r2_hidden(sK2(k2_wellord1(sK5,X0)),k1_wellord1(sK5,sK3(k2_wellord1(sK5,X0)))) = iProver_top
% 43.45/6.01      | v4_relat_2(k2_wellord1(sK5,X0)) = iProver_top
% 43.45/6.01      | v1_relat_1(k2_wellord1(sK5,X0)) != iProver_top ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_3165,c_1731]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_3271,plain,
% 43.45/6.01      ( r2_hidden(k4_tarski(sK2(k2_wellord1(sK5,X0)),sK3(k2_wellord1(sK5,X0))),sK5) = iProver_top
% 43.45/6.01      | v4_relat_2(k2_wellord1(sK5,X0)) = iProver_top
% 43.45/6.01      | v1_relat_1(k2_wellord1(sK5,X0)) != iProver_top
% 43.45/6.01      | v1_relat_1(sK5) != iProver_top ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_3170,c_782]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_3451,plain,
% 43.45/6.01      ( v1_relat_1(k2_wellord1(sK5,X0)) != iProver_top
% 43.45/6.01      | v4_relat_2(k2_wellord1(sK5,X0)) = iProver_top
% 43.45/6.01      | r2_hidden(k4_tarski(sK2(k2_wellord1(sK5,X0)),sK3(k2_wellord1(sK5,X0))),sK5) = iProver_top ),
% 43.45/6.01      inference(global_propositional_subsumption,
% 43.45/6.01                [status(thm)],
% 43.45/6.01                [c_3271,c_23]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_3452,plain,
% 43.45/6.01      ( r2_hidden(k4_tarski(sK2(k2_wellord1(sK5,X0)),sK3(k2_wellord1(sK5,X0))),sK5) = iProver_top
% 43.45/6.01      | v4_relat_2(k2_wellord1(sK5,X0)) = iProver_top
% 43.45/6.01      | v1_relat_1(k2_wellord1(sK5,X0)) != iProver_top ),
% 43.45/6.01      inference(renaming,[status(thm)],[c_3451]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_129031,plain,
% 43.45/6.01      ( v1_relat_1(k2_wellord1(sK5,X0)) != iProver_top
% 43.45/6.01      | sK3(k2_wellord1(sK5,X0)) = sK2(k2_wellord1(sK5,X0))
% 43.45/6.01      | v4_relat_2(k2_wellord1(sK5,X0)) = iProver_top ),
% 43.45/6.01      inference(global_propositional_subsumption,
% 43.45/6.01                [status(thm)],
% 43.45/6.01                [c_3405,c_23,c_24,c_3452]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_129032,plain,
% 43.45/6.01      ( sK3(k2_wellord1(sK5,X0)) = sK2(k2_wellord1(sK5,X0))
% 43.45/6.01      | v4_relat_2(k2_wellord1(sK5,X0)) = iProver_top
% 43.45/6.01      | v1_relat_1(k2_wellord1(sK5,X0)) != iProver_top ),
% 43.45/6.01      inference(renaming,[status(thm)],[c_129031]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_129037,plain,
% 43.45/6.01      ( sK3(k2_wellord1(sK5,X0)) = sK2(k2_wellord1(sK5,X0))
% 43.45/6.01      | v4_relat_2(k2_wellord1(sK5,X0)) = iProver_top
% 43.45/6.01      | v1_relat_1(sK5) != iProver_top ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_780,c_129032]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_129205,plain,
% 43.45/6.01      ( v4_relat_2(k2_wellord1(sK5,X0)) = iProver_top
% 43.45/6.01      | sK3(k2_wellord1(sK5,X0)) = sK2(k2_wellord1(sK5,X0)) ),
% 43.45/6.01      inference(global_propositional_subsumption,
% 43.45/6.01                [status(thm)],
% 43.45/6.01                [c_129037,c_23]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_129206,plain,
% 43.45/6.01      ( sK3(k2_wellord1(sK5,X0)) = sK2(k2_wellord1(sK5,X0))
% 43.45/6.01      | v4_relat_2(k2_wellord1(sK5,X0)) = iProver_top ),
% 43.45/6.01      inference(renaming,[status(thm)],[c_129205]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_20,negated_conjecture,
% 43.45/6.01      ( ~ v4_relat_2(k2_wellord1(sK5,sK4)) ),
% 43.45/6.01      inference(cnf_transformation,[],[f58]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_774,plain,
% 43.45/6.01      ( v4_relat_2(k2_wellord1(sK5,sK4)) != iProver_top ),
% 43.45/6.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_129211,plain,
% 43.45/6.01      ( sK3(k2_wellord1(sK5,sK4)) = sK2(k2_wellord1(sK5,sK4)) ),
% 43.45/6.01      inference(superposition,[status(thm)],[c_129206,c_774]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_842,plain,
% 43.45/6.01      ( v1_relat_1(k2_wellord1(sK5,sK4)) | ~ v1_relat_1(sK5) ),
% 43.45/6.01      inference(instantiation,[status(thm)],[c_14]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_342,plain,
% 43.45/6.01      ( ~ v1_relat_1(X0)
% 43.45/6.01      | k2_wellord1(sK5,sK4) != X0
% 43.45/6.01      | sK3(X0) != sK2(X0) ),
% 43.45/6.01      inference(resolution_lifted,[status(thm)],[c_15,c_20]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(c_343,plain,
% 43.45/6.01      ( ~ v1_relat_1(k2_wellord1(sK5,sK4))
% 43.45/6.01      | sK3(k2_wellord1(sK5,sK4)) != sK2(k2_wellord1(sK5,sK4)) ),
% 43.45/6.01      inference(unflattening,[status(thm)],[c_342]) ).
% 43.45/6.01  
% 43.45/6.01  cnf(contradiction,plain,
% 43.45/6.01      ( $false ),
% 43.45/6.01      inference(minisat,[status(thm)],[c_129211,c_842,c_343,c_22]) ).
% 43.45/6.01  
% 43.45/6.01  
% 43.45/6.01  % SZS output end CNFRefutation for theBenchmark.p
% 43.45/6.01  
% 43.45/6.01  ------                               Statistics
% 43.45/6.01  
% 43.45/6.01  ------ General
% 43.45/6.01  
% 43.45/6.01  abstr_ref_over_cycles:                  0
% 43.45/6.01  abstr_ref_under_cycles:                 0
% 43.45/6.01  gc_basic_clause_elim:                   0
% 43.45/6.01  forced_gc_time:                         0
% 43.45/6.01  parsing_time:                           0.008
% 43.45/6.01  unif_index_cands_time:                  0.
% 43.45/6.01  unif_index_add_time:                    0.
% 43.45/6.01  orderings_time:                         0.
% 43.45/6.01  out_proof_time:                         0.023
% 43.45/6.01  total_time:                             5.109
% 43.45/6.01  num_of_symbols:                         46
% 43.45/6.01  num_of_terms:                           146832
% 43.45/6.01  
% 43.45/6.01  ------ Preprocessing
% 43.45/6.01  
% 43.45/6.01  num_of_splits:                          0
% 43.45/6.01  num_of_split_atoms:                     0
% 43.45/6.01  num_of_reused_defs:                     0
% 43.45/6.01  num_eq_ax_congr_red:                    22
% 43.45/6.01  num_of_sem_filtered_clauses:            1
% 43.45/6.01  num_of_subtypes:                        0
% 43.45/6.01  monotx_restored_types:                  0
% 43.45/6.01  sat_num_of_epr_types:                   0
% 43.45/6.01  sat_num_of_non_cyclic_types:            0
% 43.45/6.01  sat_guarded_non_collapsed_types:        0
% 43.45/6.01  num_pure_diseq_elim:                    0
% 43.45/6.01  simp_replaced_by:                       0
% 43.45/6.01  res_preprocessed:                       90
% 43.45/6.01  prep_upred:                             0
% 43.45/6.01  prep_unflattend:                        9
% 43.45/6.01  smt_new_axioms:                         0
% 43.45/6.01  pred_elim_cands:                        4
% 43.45/6.01  pred_elim:                              0
% 43.45/6.01  pred_elim_cl:                           0
% 43.45/6.01  pred_elim_cycles:                       2
% 43.45/6.01  merged_defs:                            0
% 43.45/6.01  merged_defs_ncl:                        0
% 43.45/6.01  bin_hyper_res:                          0
% 43.45/6.01  prep_cycles:                            3
% 43.45/6.01  pred_elim_time:                         0.002
% 43.45/6.01  splitting_time:                         0.
% 43.45/6.01  sem_filter_time:                        0.
% 43.45/6.01  monotx_time:                            0.
% 43.45/6.01  subtype_inf_time:                       0.
% 43.45/6.01  
% 43.45/6.01  ------ Problem properties
% 43.45/6.01  
% 43.45/6.01  clauses:                                23
% 43.45/6.01  conjectures:                            3
% 43.45/6.01  epr:                                    2
% 43.45/6.01  horn:                                   15
% 43.45/6.01  ground:                                 3
% 43.45/6.01  unary:                                  4
% 43.45/6.01  binary:                                 6
% 43.45/6.01  lits:                                   63
% 43.45/6.01  lits_eq:                                13
% 43.45/6.01  fd_pure:                                0
% 43.45/6.01  fd_pseudo:                              0
% 43.45/6.01  fd_cond:                                0
% 43.45/6.01  fd_pseudo_cond:                         7
% 43.45/6.01  ac_symbols:                             0
% 43.45/6.01  
% 43.45/6.01  ------ Propositional Solver
% 43.45/6.01  
% 43.45/6.01  prop_solver_calls:                      52
% 43.45/6.01  prop_fast_solver_calls:                 3386
% 43.45/6.01  smt_solver_calls:                       0
% 43.45/6.01  smt_fast_solver_calls:                  0
% 43.45/6.01  prop_num_of_clauses:                    51433
% 43.45/6.01  prop_preprocess_simplified:             80660
% 43.45/6.01  prop_fo_subsumed:                       33
% 43.45/6.01  prop_solver_time:                       0.
% 43.45/6.01  smt_solver_time:                        0.
% 43.45/6.01  smt_fast_solver_time:                   0.
% 43.45/6.01  prop_fast_solver_time:                  0.
% 43.45/6.01  prop_unsat_core_time:                   0.004
% 43.45/6.01  
% 43.45/6.01  ------ QBF
% 43.45/6.01  
% 43.45/6.01  qbf_q_res:                              0
% 43.45/6.01  qbf_num_tautologies:                    0
% 43.45/6.01  qbf_prep_cycles:                        0
% 43.45/6.01  
% 43.45/6.01  ------ BMC1
% 43.45/6.01  
% 43.45/6.01  bmc1_current_bound:                     -1
% 43.45/6.01  bmc1_last_solved_bound:                 -1
% 43.45/6.01  bmc1_unsat_core_size:                   -1
% 43.45/6.01  bmc1_unsat_core_parents_size:           -1
% 43.45/6.01  bmc1_merge_next_fun:                    0
% 43.45/6.01  bmc1_unsat_core_clauses_time:           0.
% 43.45/6.01  
% 43.45/6.01  ------ Instantiation
% 43.45/6.01  
% 43.45/6.01  inst_num_of_clauses:                    3291
% 43.45/6.01  inst_num_in_passive:                    1922
% 43.45/6.01  inst_num_in_active:                     3431
% 43.45/6.01  inst_num_in_unprocessed:                300
% 43.45/6.01  inst_num_of_loops:                      4229
% 43.45/6.01  inst_num_of_learning_restarts:          1
% 43.45/6.01  inst_num_moves_active_passive:          795
% 43.45/6.01  inst_lit_activity:                      0
% 43.45/6.01  inst_lit_activity_moves:                2
% 43.45/6.01  inst_num_tautologies:                   0
% 43.45/6.01  inst_num_prop_implied:                  0
% 43.45/6.01  inst_num_existing_simplified:           0
% 43.45/6.01  inst_num_eq_res_simplified:             0
% 43.45/6.01  inst_num_child_elim:                    0
% 43.45/6.01  inst_num_of_dismatching_blockings:      21316
% 43.45/6.01  inst_num_of_non_proper_insts:           15522
% 43.45/6.01  inst_num_of_duplicates:                 0
% 43.45/6.01  inst_inst_num_from_inst_to_res:         0
% 43.45/6.01  inst_dismatching_checking_time:         0.
% 43.45/6.01  
% 43.45/6.01  ------ Resolution
% 43.45/6.01  
% 43.45/6.01  res_num_of_clauses:                     33
% 43.45/6.01  res_num_in_passive:                     33
% 43.45/6.01  res_num_in_active:                      0
% 43.45/6.01  res_num_of_loops:                       93
% 43.45/6.01  res_forward_subset_subsumed:            504
% 43.45/6.01  res_backward_subset_subsumed:           0
% 43.45/6.01  res_forward_subsumed:                   0
% 43.45/6.01  res_backward_subsumed:                  0
% 43.45/6.01  res_forward_subsumption_resolution:     0
% 43.45/6.01  res_backward_subsumption_resolution:    0
% 43.45/6.01  res_clause_to_clause_subsumption:       232257
% 43.45/6.01  res_orphan_elimination:                 0
% 43.45/6.01  res_tautology_del:                      367
% 43.45/6.01  res_num_eq_res_simplified:              0
% 43.45/6.01  res_num_sel_changes:                    0
% 43.45/6.01  res_moves_from_active_to_pass:          0
% 43.45/6.01  
% 43.45/6.01  ------ Superposition
% 43.45/6.01  
% 43.45/6.01  sup_time_total:                         0.
% 43.45/6.01  sup_time_generating:                    0.
% 43.45/6.01  sup_time_sim_full:                      0.
% 43.45/6.01  sup_time_sim_immed:                     0.
% 43.45/6.01  
% 43.45/6.01  sup_num_of_clauses:                     7062
% 43.45/6.01  sup_num_in_active:                      844
% 43.45/6.01  sup_num_in_passive:                     6218
% 43.45/6.01  sup_num_of_loops:                       844
% 43.45/6.01  sup_fw_superposition:                   10046
% 43.45/6.01  sup_bw_superposition:                   7610
% 43.45/6.01  sup_immediate_simplified:               4530
% 43.45/6.01  sup_given_eliminated:                   0
% 43.45/6.01  comparisons_done:                       0
% 43.45/6.01  comparisons_avoided:                    2
% 43.45/6.01  
% 43.45/6.01  ------ Simplifications
% 43.45/6.01  
% 43.45/6.01  
% 43.45/6.01  sim_fw_subset_subsumed:                 288
% 43.45/6.01  sim_bw_subset_subsumed:                 18
% 43.45/6.01  sim_fw_subsumed:                        902
% 43.45/6.01  sim_bw_subsumed:                        5
% 43.45/6.01  sim_fw_subsumption_res:                 0
% 43.45/6.01  sim_bw_subsumption_res:                 0
% 43.45/6.01  sim_tautology_del:                      124
% 43.45/6.01  sim_eq_tautology_del:                   20
% 43.45/6.01  sim_eq_res_simp:                        553
% 43.45/6.01  sim_fw_demodulated:                     3170
% 43.45/6.01  sim_bw_demodulated:                     283
% 43.45/6.01  sim_light_normalised:                   1719
% 43.45/6.01  sim_joinable_taut:                      0
% 43.45/6.01  sim_joinable_simp:                      0
% 43.45/6.01  sim_ac_normalised:                      0
% 43.45/6.01  sim_smt_subsumption:                    0
% 43.45/6.01  
%------------------------------------------------------------------------------
