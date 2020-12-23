%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:14 EST 2020

% Result     : Theorem 4.08s
% Output     : CNFRefutation 4.08s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 646 expanded)
%              Number of clauses        :   55 ( 120 expanded)
%              Number of leaves         :   20 ( 168 expanded)
%              Depth                    :   18
%              Number of atoms          :  417 (1934 expanded)
%              Number of equality atoms :  264 (1184 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f35,plain,
    ( ? [X0,X1] :
        ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
        & k1_tarski(X0) = k1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k1_tarski(k1_funct_1(sK6,sK5)) != k2_relat_1(sK6)
      & k1_tarski(sK5) = k1_relat_1(sK6)
      & v1_funct_1(sK6)
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( k1_tarski(k1_funct_1(sK6,sK5)) != k2_relat_1(sK6)
    & k1_tarski(sK5) = k1_relat_1(sK6)
    & v1_funct_1(sK6)
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f20,f35])).

fof(f60,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK1(X0,X1) != X1
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( sK1(X0,X1) != X1
        & r2_hidden(sK1(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f26])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f63])).

fof(f65,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f64])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | k1_xboole_0 = X0
      | k3_enumset1(X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f47,f65])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f29])).

fof(f33,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X5)) = X5
        & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1)) = X2
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK2(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK2(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK2(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK2(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK3(X0,X1)) = sK2(X0,X1)
                  & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK2(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK4(X0,X5)) = X5
                    & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f30,f33,f32,f31])).

fof(f54,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f84,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f59,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,(
    k1_tarski(sK5) = k1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f36])).

fof(f76,plain,(
    k3_enumset1(sK5,sK5,sK5,sK5,sK5) = k1_relat_1(sK6) ),
    inference(definition_unfolding,[],[f61,f65])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f21])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK0(X0,X1,X2) != X1
            & sK0(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( sK0(X0,X1,X2) = X1
          | sK0(X0,X1,X2) = X0
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK0(X0,X1,X2) != X1
              & sK0(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( sK0(X0,X1,X2) = X1
            | sK0(X0,X1,X2) = X0
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k3_enumset1(X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f38,f64])).

fof(f79,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k3_enumset1(X4,X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f70])).

fof(f80,plain,(
    ! [X4,X1] : r2_hidden(X4,k3_enumset1(X4,X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f79])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k3_enumset1(X1,X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f49,f65])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f62,plain,(
    k1_tarski(k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) ),
    inference(cnf_transformation,[],[f36])).

fof(f75,plain,(
    k3_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) ),
    inference(definition_unfolding,[],[f62,f65])).

fof(f53,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f85,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k3_enumset1(X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f37,f64])).

fof(f81,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k3_enumset1(X0,X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f71])).

fof(f48,plain,(
    ! [X0,X1] :
      ( sK1(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f72,plain,(
    ! [X0,X1] :
      ( sK1(X0,X1) != X1
      | k1_xboole_0 = X0
      | k3_enumset1(X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f48,f65])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_489,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | k3_enumset1(X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_500,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK4(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_491,plain,
    ( k1_funct_1(X0,sK4(X0,X1)) = X1
    | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1988,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(X1)
    | k1_funct_1(X1,sK4(X1,sK1(k2_relat_1(X1),X0))) = sK1(k2_relat_1(X1),X0)
    | k2_relat_1(X1) = k1_xboole_0
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_500,c_491])).

cnf(c_7314,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK6)
    | k1_funct_1(sK6,sK4(sK6,sK1(k2_relat_1(sK6),X0))) = sK1(k2_relat_1(sK6),X0)
    | k2_relat_1(sK6) = k1_xboole_0
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_489,c_1988])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_22,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_19,negated_conjecture,
    ( k3_enumset1(sK5,sK5,sK5,sK5,sK5) = k1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_4,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_502,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_769,plain,
    ( r2_hidden(sK5,k1_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_502])).

cnf(c_488,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k3_enumset1(X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_499,plain,
    ( k9_relat_1(X0,k3_enumset1(X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1185,plain,
    ( k9_relat_1(sK6,k3_enumset1(X0,X0,X0,X0,X0)) = k11_relat_1(sK6,X0) ),
    inference(superposition,[status(thm)],[c_488,c_499])).

cnf(c_1489,plain,
    ( k9_relat_1(sK6,k1_relat_1(sK6)) = k11_relat_1(sK6,sK5) ),
    inference(superposition,[status(thm)],[c_19,c_1185])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_498,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_870,plain,
    ( k9_relat_1(sK6,k1_relat_1(sK6)) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_488,c_498])).

cnf(c_1490,plain,
    ( k11_relat_1(sK6,sK5) = k2_relat_1(sK6) ),
    inference(light_normalisation,[status(thm)],[c_1489,c_870])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k11_relat_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_496,plain,
    ( k11_relat_1(X0,X1) != k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1819,plain,
    ( k2_relat_1(sK6) != k1_xboole_0
    | r2_hidden(sK5,k1_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1490,c_496])).

cnf(c_7315,plain,
    ( ~ v1_relat_1(sK6)
    | k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK6)
    | k1_funct_1(sK6,sK4(sK6,sK1(k2_relat_1(sK6),X0))) = sK1(k2_relat_1(sK6),X0)
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7314])).

cnf(c_8807,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK6)
    | k1_funct_1(sK6,sK4(sK6,sK1(k2_relat_1(sK6),X0))) = sK1(k2_relat_1(sK6),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7314,c_21,c_22,c_769,c_1819,c_7315])).

cnf(c_18,negated_conjecture,
    ( k3_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_8838,plain,
    ( k1_funct_1(sK6,sK4(sK6,sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5)))) = sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5)) ),
    inference(superposition,[status(thm)],[c_8807,c_18])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK4(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_490,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK4(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_501,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1347,plain,
    ( sK5 = X0
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_501])).

cnf(c_1356,plain,
    ( sK4(sK6,X0) = sK5
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_490,c_1347])).

cnf(c_23,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1641,plain,
    ( sK4(sK6,X0) = sK5
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1356,c_22,c_23])).

cnf(c_1990,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK6)
    | sK4(sK6,sK1(k2_relat_1(sK6),X0)) = sK5
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_500,c_1641])).

cnf(c_7513,plain,
    ( sK4(sK6,sK1(k2_relat_1(sK6),X0)) = sK5
    | k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1990,c_22,c_769,c_1819])).

cnf(c_7514,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK6)
    | sK4(sK6,sK1(k2_relat_1(sK6),X0)) = sK5 ),
    inference(renaming,[status(thm)],[c_7513])).

cnf(c_7537,plain,
    ( sK4(sK6,sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5))) = sK5 ),
    inference(superposition,[status(thm)],[c_7514,c_18])).

cnf(c_8847,plain,
    ( sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5)) = k1_funct_1(sK6,sK5) ),
    inference(light_normalisation,[status(thm)],[c_8838,c_7537])).

cnf(c_182,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1002,plain,
    ( X0 != X1
    | k2_relat_1(sK6) != X1
    | k2_relat_1(sK6) = X0 ),
    inference(instantiation,[status(thm)],[c_182])).

cnf(c_1470,plain,
    ( X0 != k2_relat_1(sK6)
    | k2_relat_1(sK6) = X0
    | k2_relat_1(sK6) != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1002])).

cnf(c_3532,plain,
    ( k2_relat_1(sK6) != k2_relat_1(sK6)
    | k2_relat_1(sK6) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1470])).

cnf(c_181,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1435,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_181])).

cnf(c_188,plain,
    ( X0 != X1
    | k2_relat_1(X0) = k2_relat_1(X1) ),
    theory(equality)).

cnf(c_1004,plain,
    ( k2_relat_1(sK6) = k2_relat_1(X0)
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_188])).

cnf(c_1434,plain,
    ( k2_relat_1(sK6) = k2_relat_1(sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1004])).

cnf(c_6,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = X1
    | sK1(X1,X0) != X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_753,plain,
    ( k3_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k2_relat_1(sK6)
    | sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5)) != k1_funct_1(sK6,sK5)
    | k1_xboole_0 = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8847,c_3532,c_1819,c_1435,c_1434,c_769,c_753,c_18,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.32  % Computer   : n019.cluster.edu
% 0.14/0.32  % Model      : x86_64 x86_64
% 0.14/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.32  % Memory     : 8042.1875MB
% 0.14/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.32  % CPULimit   : 60
% 0.14/0.32  % WCLimit    : 600
% 0.14/0.32  % DateTime   : Tue Dec  1 16:17:07 EST 2020
% 0.14/0.32  % CPUTime    : 
% 0.14/0.32  % Running in FOF mode
% 4.08/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.08/1.01  
% 4.08/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.08/1.01  
% 4.08/1.01  ------  iProver source info
% 4.08/1.01  
% 4.08/1.01  git: date: 2020-06-30 10:37:57 +0100
% 4.08/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.08/1.01  git: non_committed_changes: false
% 4.08/1.01  git: last_make_outside_of_git: false
% 4.08/1.01  
% 4.08/1.01  ------ 
% 4.08/1.01  ------ Parsing...
% 4.08/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.08/1.01  
% 4.08/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 4.08/1.01  
% 4.08/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.08/1.01  
% 4.08/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.08/1.01  ------ Proving...
% 4.08/1.01  ------ Problem Properties 
% 4.08/1.01  
% 4.08/1.01  
% 4.08/1.01  clauses                                 22
% 4.08/1.01  conjectures                             4
% 4.08/1.01  EPR                                     2
% 4.08/1.01  Horn                                    15
% 4.08/1.01  unary                                   6
% 4.08/1.01  binary                                  2
% 4.08/1.01  lits                                    63
% 4.08/1.01  lits eq                                 26
% 4.08/1.01  fd_pure                                 0
% 4.08/1.01  fd_pseudo                               0
% 4.08/1.01  fd_cond                                 0
% 4.08/1.01  fd_pseudo_cond                          8
% 4.08/1.01  AC symbols                              0
% 4.08/1.01  
% 4.08/1.01  ------ Input Options Time Limit: Unbounded
% 4.08/1.01  
% 4.08/1.01  
% 4.08/1.01  ------ 
% 4.08/1.01  Current options:
% 4.08/1.01  ------ 
% 4.08/1.01  
% 4.08/1.01  
% 4.08/1.01  
% 4.08/1.01  
% 4.08/1.01  ------ Proving...
% 4.08/1.01  
% 4.08/1.01  
% 4.08/1.01  % SZS status Theorem for theBenchmark.p
% 4.08/1.01  
% 4.08/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 4.08/1.01  
% 4.08/1.01  fof(f11,conjecture,(
% 4.08/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 4.08/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/1.01  
% 4.08/1.01  fof(f12,negated_conjecture,(
% 4.08/1.01    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 4.08/1.01    inference(negated_conjecture,[],[f11])).
% 4.08/1.01  
% 4.08/1.01  fof(f19,plain,(
% 4.08/1.01    ? [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 4.08/1.01    inference(ennf_transformation,[],[f12])).
% 4.08/1.01  
% 4.08/1.01  fof(f20,plain,(
% 4.08/1.01    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 4.08/1.01    inference(flattening,[],[f19])).
% 4.08/1.01  
% 4.08/1.01  fof(f35,plain,(
% 4.08/1.01    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) & k1_tarski(sK5) = k1_relat_1(sK6) & v1_funct_1(sK6) & v1_relat_1(sK6))),
% 4.08/1.01    introduced(choice_axiom,[])).
% 4.08/1.01  
% 4.08/1.01  fof(f36,plain,(
% 4.08/1.01    k1_tarski(k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) & k1_tarski(sK5) = k1_relat_1(sK6) & v1_funct_1(sK6) & v1_relat_1(sK6)),
% 4.08/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f20,f35])).
% 4.08/1.01  
% 4.08/1.01  fof(f60,plain,(
% 4.08/1.01    v1_funct_1(sK6)),
% 4.08/1.01    inference(cnf_transformation,[],[f36])).
% 4.08/1.01  
% 4.08/1.01  fof(f6,axiom,(
% 4.08/1.01    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 4.08/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/1.01  
% 4.08/1.01  fof(f13,plain,(
% 4.08/1.01    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 4.08/1.01    inference(ennf_transformation,[],[f6])).
% 4.08/1.01  
% 4.08/1.01  fof(f26,plain,(
% 4.08/1.01    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK1(X0,X1) != X1 & r2_hidden(sK1(X0,X1),X0)))),
% 4.08/1.01    introduced(choice_axiom,[])).
% 4.08/1.01  
% 4.08/1.01  fof(f27,plain,(
% 4.08/1.01    ! [X0,X1] : ((sK1(X0,X1) != X1 & r2_hidden(sK1(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 4.08/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f26])).
% 4.08/1.01  
% 4.08/1.01  fof(f47,plain,(
% 4.08/1.01    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 4.08/1.01    inference(cnf_transformation,[],[f27])).
% 4.08/1.01  
% 4.08/1.01  fof(f2,axiom,(
% 4.08/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 4.08/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/1.01  
% 4.08/1.01  fof(f43,plain,(
% 4.08/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 4.08/1.01    inference(cnf_transformation,[],[f2])).
% 4.08/1.01  
% 4.08/1.01  fof(f3,axiom,(
% 4.08/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 4.08/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/1.01  
% 4.08/1.01  fof(f44,plain,(
% 4.08/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 4.08/1.01    inference(cnf_transformation,[],[f3])).
% 4.08/1.01  
% 4.08/1.01  fof(f4,axiom,(
% 4.08/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 4.08/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/1.01  
% 4.08/1.01  fof(f45,plain,(
% 4.08/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 4.08/1.01    inference(cnf_transformation,[],[f4])).
% 4.08/1.01  
% 4.08/1.01  fof(f5,axiom,(
% 4.08/1.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 4.08/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/1.01  
% 4.08/1.01  fof(f46,plain,(
% 4.08/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 4.08/1.01    inference(cnf_transformation,[],[f5])).
% 4.08/1.01  
% 4.08/1.01  fof(f63,plain,(
% 4.08/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 4.08/1.01    inference(definition_unfolding,[],[f45,f46])).
% 4.08/1.01  
% 4.08/1.01  fof(f64,plain,(
% 4.08/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 4.08/1.01    inference(definition_unfolding,[],[f44,f63])).
% 4.08/1.01  
% 4.08/1.01  fof(f65,plain,(
% 4.08/1.01    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 4.08/1.01    inference(definition_unfolding,[],[f43,f64])).
% 4.08/1.01  
% 4.08/1.01  fof(f73,plain,(
% 4.08/1.01    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | k1_xboole_0 = X0 | k3_enumset1(X1,X1,X1,X1,X1) = X0) )),
% 4.08/1.01    inference(definition_unfolding,[],[f47,f65])).
% 4.08/1.01  
% 4.08/1.01  fof(f10,axiom,(
% 4.08/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 4.08/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/1.01  
% 4.08/1.01  fof(f17,plain,(
% 4.08/1.01    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.08/1.01    inference(ennf_transformation,[],[f10])).
% 4.08/1.01  
% 4.08/1.01  fof(f18,plain,(
% 4.08/1.01    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.08/1.01    inference(flattening,[],[f17])).
% 4.08/1.01  
% 4.08/1.01  fof(f29,plain,(
% 4.08/1.01    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.08/1.01    inference(nnf_transformation,[],[f18])).
% 4.08/1.01  
% 4.08/1.01  fof(f30,plain,(
% 4.08/1.01    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.08/1.01    inference(rectify,[],[f29])).
% 4.08/1.01  
% 4.08/1.01  fof(f33,plain,(
% 4.08/1.01    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))))),
% 4.08/1.01    introduced(choice_axiom,[])).
% 4.08/1.01  
% 4.08/1.01  fof(f32,plain,(
% 4.08/1.01    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1)) = X2 & r2_hidden(sK3(X0,X1),k1_relat_1(X0))))) )),
% 4.08/1.01    introduced(choice_axiom,[])).
% 4.08/1.01  
% 4.08/1.01  fof(f31,plain,(
% 4.08/1.01    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK2(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1))))),
% 4.08/1.01    introduced(choice_axiom,[])).
% 4.08/1.01  
% 4.08/1.01  fof(f34,plain,(
% 4.08/1.01    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & ((k1_funct_1(X0,sK3(X0,X1)) = sK2(X0,X1) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.08/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f30,f33,f32,f31])).
% 4.08/1.01  
% 4.08/1.01  fof(f54,plain,(
% 4.08/1.01    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK4(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.08/1.01    inference(cnf_transformation,[],[f34])).
% 4.08/1.01  
% 4.08/1.01  fof(f84,plain,(
% 4.08/1.01    ( ! [X0,X5] : (k1_funct_1(X0,sK4(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.08/1.01    inference(equality_resolution,[],[f54])).
% 4.08/1.01  
% 4.08/1.01  fof(f59,plain,(
% 4.08/1.01    v1_relat_1(sK6)),
% 4.08/1.01    inference(cnf_transformation,[],[f36])).
% 4.08/1.01  
% 4.08/1.01  fof(f61,plain,(
% 4.08/1.01    k1_tarski(sK5) = k1_relat_1(sK6)),
% 4.08/1.01    inference(cnf_transformation,[],[f36])).
% 4.08/1.01  
% 4.08/1.01  fof(f76,plain,(
% 4.08/1.01    k3_enumset1(sK5,sK5,sK5,sK5,sK5) = k1_relat_1(sK6)),
% 4.08/1.01    inference(definition_unfolding,[],[f61,f65])).
% 4.08/1.01  
% 4.08/1.01  fof(f1,axiom,(
% 4.08/1.01    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 4.08/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/1.01  
% 4.08/1.01  fof(f21,plain,(
% 4.08/1.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 4.08/1.01    inference(nnf_transformation,[],[f1])).
% 4.08/1.01  
% 4.08/1.01  fof(f22,plain,(
% 4.08/1.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 4.08/1.01    inference(flattening,[],[f21])).
% 4.08/1.01  
% 4.08/1.01  fof(f23,plain,(
% 4.08/1.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 4.08/1.01    inference(rectify,[],[f22])).
% 4.08/1.01  
% 4.08/1.01  fof(f24,plain,(
% 4.08/1.01    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 4.08/1.01    introduced(choice_axiom,[])).
% 4.08/1.01  
% 4.08/1.01  fof(f25,plain,(
% 4.08/1.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 4.08/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 4.08/1.01  
% 4.08/1.01  fof(f38,plain,(
% 4.08/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 4.08/1.01    inference(cnf_transformation,[],[f25])).
% 4.08/1.01  
% 4.08/1.01  fof(f70,plain,(
% 4.08/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k3_enumset1(X0,X0,X0,X0,X1) != X2) )),
% 4.08/1.01    inference(definition_unfolding,[],[f38,f64])).
% 4.08/1.01  
% 4.08/1.01  fof(f79,plain,(
% 4.08/1.01    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k3_enumset1(X4,X4,X4,X4,X1) != X2) )),
% 4.08/1.01    inference(equality_resolution,[],[f70])).
% 4.08/1.01  
% 4.08/1.01  fof(f80,plain,(
% 4.08/1.01    ( ! [X4,X1] : (r2_hidden(X4,k3_enumset1(X4,X4,X4,X4,X1))) )),
% 4.08/1.01    inference(equality_resolution,[],[f79])).
% 4.08/1.01  
% 4.08/1.01  fof(f7,axiom,(
% 4.08/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 4.08/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/1.01  
% 4.08/1.01  fof(f14,plain,(
% 4.08/1.01    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 4.08/1.01    inference(ennf_transformation,[],[f7])).
% 4.08/1.01  
% 4.08/1.01  fof(f49,plain,(
% 4.08/1.01    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 4.08/1.01    inference(cnf_transformation,[],[f14])).
% 4.08/1.01  
% 4.08/1.01  fof(f74,plain,(
% 4.08/1.01    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k3_enumset1(X1,X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 4.08/1.01    inference(definition_unfolding,[],[f49,f65])).
% 4.08/1.01  
% 4.08/1.01  fof(f8,axiom,(
% 4.08/1.01    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 4.08/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/1.01  
% 4.08/1.01  fof(f15,plain,(
% 4.08/1.01    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 4.08/1.01    inference(ennf_transformation,[],[f8])).
% 4.08/1.01  
% 4.08/1.01  fof(f50,plain,(
% 4.08/1.01    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 4.08/1.01    inference(cnf_transformation,[],[f15])).
% 4.08/1.01  
% 4.08/1.01  fof(f9,axiom,(
% 4.08/1.01    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 4.08/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/1.01  
% 4.08/1.01  fof(f16,plain,(
% 4.08/1.01    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 4.08/1.01    inference(ennf_transformation,[],[f9])).
% 4.08/1.01  
% 4.08/1.01  fof(f28,plain,(
% 4.08/1.01    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 4.08/1.01    inference(nnf_transformation,[],[f16])).
% 4.08/1.01  
% 4.08/1.01  fof(f51,plain,(
% 4.08/1.01    ( ! [X0,X1] : (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 4.08/1.01    inference(cnf_transformation,[],[f28])).
% 4.08/1.01  
% 4.08/1.01  fof(f62,plain,(
% 4.08/1.01    k1_tarski(k1_funct_1(sK6,sK5)) != k2_relat_1(sK6)),
% 4.08/1.01    inference(cnf_transformation,[],[f36])).
% 4.08/1.01  
% 4.08/1.01  fof(f75,plain,(
% 4.08/1.01    k3_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k2_relat_1(sK6)),
% 4.08/1.01    inference(definition_unfolding,[],[f62,f65])).
% 4.08/1.01  
% 4.08/1.01  fof(f53,plain,(
% 4.08/1.01    ( ! [X0,X5,X1] : (r2_hidden(sK4(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.08/1.01    inference(cnf_transformation,[],[f34])).
% 4.08/1.01  
% 4.08/1.01  fof(f85,plain,(
% 4.08/1.01    ( ! [X0,X5] : (r2_hidden(sK4(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.08/1.01    inference(equality_resolution,[],[f53])).
% 4.08/1.01  
% 4.08/1.01  fof(f37,plain,(
% 4.08/1.01    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 4.08/1.01    inference(cnf_transformation,[],[f25])).
% 4.08/1.01  
% 4.08/1.01  fof(f71,plain,(
% 4.08/1.01    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k3_enumset1(X0,X0,X0,X0,X1) != X2) )),
% 4.08/1.01    inference(definition_unfolding,[],[f37,f64])).
% 4.08/1.01  
% 4.08/1.01  fof(f81,plain,(
% 4.08/1.01    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k3_enumset1(X0,X0,X0,X0,X1))) )),
% 4.08/1.01    inference(equality_resolution,[],[f71])).
% 4.08/1.01  
% 4.08/1.01  fof(f48,plain,(
% 4.08/1.01    ( ! [X0,X1] : (sK1(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 4.08/1.01    inference(cnf_transformation,[],[f27])).
% 4.08/1.01  
% 4.08/1.01  fof(f72,plain,(
% 4.08/1.01    ( ! [X0,X1] : (sK1(X0,X1) != X1 | k1_xboole_0 = X0 | k3_enumset1(X1,X1,X1,X1,X1) = X0) )),
% 4.08/1.01    inference(definition_unfolding,[],[f48,f65])).
% 4.08/1.01  
% 4.08/1.01  cnf(c_20,negated_conjecture,
% 4.08/1.01      ( v1_funct_1(sK6) ),
% 4.08/1.01      inference(cnf_transformation,[],[f60]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_489,plain,
% 4.08/1.01      ( v1_funct_1(sK6) = iProver_top ),
% 4.08/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_7,plain,
% 4.08/1.01      ( r2_hidden(sK1(X0,X1),X0)
% 4.08/1.01      | k3_enumset1(X1,X1,X1,X1,X1) = X0
% 4.08/1.01      | k1_xboole_0 = X0 ),
% 4.08/1.01      inference(cnf_transformation,[],[f73]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_500,plain,
% 4.08/1.01      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
% 4.08/1.01      | k1_xboole_0 = X1
% 4.08/1.01      | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
% 4.08/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_16,plain,
% 4.08/1.01      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 4.08/1.01      | ~ v1_funct_1(X1)
% 4.08/1.01      | ~ v1_relat_1(X1)
% 4.08/1.01      | k1_funct_1(X1,sK4(X1,X0)) = X0 ),
% 4.08/1.01      inference(cnf_transformation,[],[f84]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_491,plain,
% 4.08/1.01      ( k1_funct_1(X0,sK4(X0,X1)) = X1
% 4.08/1.01      | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
% 4.08/1.01      | v1_funct_1(X0) != iProver_top
% 4.08/1.01      | v1_relat_1(X0) != iProver_top ),
% 4.08/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_1988,plain,
% 4.08/1.01      ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(X1)
% 4.08/1.01      | k1_funct_1(X1,sK4(X1,sK1(k2_relat_1(X1),X0))) = sK1(k2_relat_1(X1),X0)
% 4.08/1.01      | k2_relat_1(X1) = k1_xboole_0
% 4.08/1.01      | v1_funct_1(X1) != iProver_top
% 4.08/1.01      | v1_relat_1(X1) != iProver_top ),
% 4.08/1.01      inference(superposition,[status(thm)],[c_500,c_491]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_7314,plain,
% 4.08/1.01      ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK6)
% 4.08/1.01      | k1_funct_1(sK6,sK4(sK6,sK1(k2_relat_1(sK6),X0))) = sK1(k2_relat_1(sK6),X0)
% 4.08/1.01      | k2_relat_1(sK6) = k1_xboole_0
% 4.08/1.01      | v1_relat_1(sK6) != iProver_top ),
% 4.08/1.01      inference(superposition,[status(thm)],[c_489,c_1988]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_21,negated_conjecture,
% 4.08/1.01      ( v1_relat_1(sK6) ),
% 4.08/1.01      inference(cnf_transformation,[],[f59]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_22,plain,
% 4.08/1.01      ( v1_relat_1(sK6) = iProver_top ),
% 4.08/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_19,negated_conjecture,
% 4.08/1.01      ( k3_enumset1(sK5,sK5,sK5,sK5,sK5) = k1_relat_1(sK6) ),
% 4.08/1.01      inference(cnf_transformation,[],[f76]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_4,plain,
% 4.08/1.01      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X1)) ),
% 4.08/1.01      inference(cnf_transformation,[],[f80]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_502,plain,
% 4.08/1.01      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X1)) = iProver_top ),
% 4.08/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_769,plain,
% 4.08/1.01      ( r2_hidden(sK5,k1_relat_1(sK6)) = iProver_top ),
% 4.08/1.01      inference(superposition,[status(thm)],[c_19,c_502]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_488,plain,
% 4.08/1.01      ( v1_relat_1(sK6) = iProver_top ),
% 4.08/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_8,plain,
% 4.08/1.01      ( ~ v1_relat_1(X0)
% 4.08/1.01      | k9_relat_1(X0,k3_enumset1(X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 4.08/1.01      inference(cnf_transformation,[],[f74]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_499,plain,
% 4.08/1.01      ( k9_relat_1(X0,k3_enumset1(X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1)
% 4.08/1.01      | v1_relat_1(X0) != iProver_top ),
% 4.08/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_1185,plain,
% 4.08/1.01      ( k9_relat_1(sK6,k3_enumset1(X0,X0,X0,X0,X0)) = k11_relat_1(sK6,X0) ),
% 4.08/1.01      inference(superposition,[status(thm)],[c_488,c_499]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_1489,plain,
% 4.08/1.01      ( k9_relat_1(sK6,k1_relat_1(sK6)) = k11_relat_1(sK6,sK5) ),
% 4.08/1.01      inference(superposition,[status(thm)],[c_19,c_1185]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_9,plain,
% 4.08/1.01      ( ~ v1_relat_1(X0)
% 4.08/1.01      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 4.08/1.01      inference(cnf_transformation,[],[f50]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_498,plain,
% 4.08/1.01      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 4.08/1.01      | v1_relat_1(X0) != iProver_top ),
% 4.08/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_870,plain,
% 4.08/1.01      ( k9_relat_1(sK6,k1_relat_1(sK6)) = k2_relat_1(sK6) ),
% 4.08/1.01      inference(superposition,[status(thm)],[c_488,c_498]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_1490,plain,
% 4.08/1.01      ( k11_relat_1(sK6,sK5) = k2_relat_1(sK6) ),
% 4.08/1.01      inference(light_normalisation,[status(thm)],[c_1489,c_870]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_11,plain,
% 4.08/1.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 4.08/1.01      | ~ v1_relat_1(X1)
% 4.08/1.01      | k11_relat_1(X1,X0) != k1_xboole_0 ),
% 4.08/1.01      inference(cnf_transformation,[],[f51]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_496,plain,
% 4.08/1.01      ( k11_relat_1(X0,X1) != k1_xboole_0
% 4.08/1.01      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 4.08/1.01      | v1_relat_1(X0) != iProver_top ),
% 4.08/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_1819,plain,
% 4.08/1.01      ( k2_relat_1(sK6) != k1_xboole_0
% 4.08/1.01      | r2_hidden(sK5,k1_relat_1(sK6)) != iProver_top
% 4.08/1.01      | v1_relat_1(sK6) != iProver_top ),
% 4.08/1.01      inference(superposition,[status(thm)],[c_1490,c_496]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_7315,plain,
% 4.08/1.01      ( ~ v1_relat_1(sK6)
% 4.08/1.01      | k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK6)
% 4.08/1.01      | k1_funct_1(sK6,sK4(sK6,sK1(k2_relat_1(sK6),X0))) = sK1(k2_relat_1(sK6),X0)
% 4.08/1.01      | k2_relat_1(sK6) = k1_xboole_0 ),
% 4.08/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_7314]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_8807,plain,
% 4.08/1.01      ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK6)
% 4.08/1.01      | k1_funct_1(sK6,sK4(sK6,sK1(k2_relat_1(sK6),X0))) = sK1(k2_relat_1(sK6),X0) ),
% 4.08/1.01      inference(global_propositional_subsumption,
% 4.08/1.01                [status(thm)],
% 4.08/1.01                [c_7314,c_21,c_22,c_769,c_1819,c_7315]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_18,negated_conjecture,
% 4.08/1.01      ( k3_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) ),
% 4.08/1.01      inference(cnf_transformation,[],[f75]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_8838,plain,
% 4.08/1.01      ( k1_funct_1(sK6,sK4(sK6,sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5)))) = sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5)) ),
% 4.08/1.01      inference(superposition,[status(thm)],[c_8807,c_18]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_17,plain,
% 4.08/1.01      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 4.08/1.01      | r2_hidden(sK4(X1,X0),k1_relat_1(X1))
% 4.08/1.01      | ~ v1_funct_1(X1)
% 4.08/1.01      | ~ v1_relat_1(X1) ),
% 4.08/1.01      inference(cnf_transformation,[],[f85]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_490,plain,
% 4.08/1.01      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 4.08/1.01      | r2_hidden(sK4(X1,X0),k1_relat_1(X1)) = iProver_top
% 4.08/1.01      | v1_funct_1(X1) != iProver_top
% 4.08/1.01      | v1_relat_1(X1) != iProver_top ),
% 4.08/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_5,plain,
% 4.08/1.01      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 4.08/1.01      inference(cnf_transformation,[],[f81]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_501,plain,
% 4.08/1.01      ( X0 = X1
% 4.08/1.01      | X0 = X2
% 4.08/1.01      | r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X2)) != iProver_top ),
% 4.08/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_1347,plain,
% 4.08/1.01      ( sK5 = X0 | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 4.08/1.01      inference(superposition,[status(thm)],[c_19,c_501]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_1356,plain,
% 4.08/1.01      ( sK4(sK6,X0) = sK5
% 4.08/1.01      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 4.08/1.01      | v1_funct_1(sK6) != iProver_top
% 4.08/1.01      | v1_relat_1(sK6) != iProver_top ),
% 4.08/1.01      inference(superposition,[status(thm)],[c_490,c_1347]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_23,plain,
% 4.08/1.01      ( v1_funct_1(sK6) = iProver_top ),
% 4.08/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_1641,plain,
% 4.08/1.01      ( sK4(sK6,X0) = sK5
% 4.08/1.01      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
% 4.08/1.01      inference(global_propositional_subsumption,
% 4.08/1.01                [status(thm)],
% 4.08/1.01                [c_1356,c_22,c_23]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_1990,plain,
% 4.08/1.01      ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK6)
% 4.08/1.01      | sK4(sK6,sK1(k2_relat_1(sK6),X0)) = sK5
% 4.08/1.01      | k2_relat_1(sK6) = k1_xboole_0 ),
% 4.08/1.01      inference(superposition,[status(thm)],[c_500,c_1641]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_7513,plain,
% 4.08/1.01      ( sK4(sK6,sK1(k2_relat_1(sK6),X0)) = sK5
% 4.08/1.01      | k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK6) ),
% 4.08/1.01      inference(global_propositional_subsumption,
% 4.08/1.01                [status(thm)],
% 4.08/1.01                [c_1990,c_22,c_769,c_1819]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_7514,plain,
% 4.08/1.01      ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK6)
% 4.08/1.01      | sK4(sK6,sK1(k2_relat_1(sK6),X0)) = sK5 ),
% 4.08/1.01      inference(renaming,[status(thm)],[c_7513]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_7537,plain,
% 4.08/1.01      ( sK4(sK6,sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5))) = sK5 ),
% 4.08/1.01      inference(superposition,[status(thm)],[c_7514,c_18]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_8847,plain,
% 4.08/1.01      ( sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5)) = k1_funct_1(sK6,sK5) ),
% 4.08/1.01      inference(light_normalisation,[status(thm)],[c_8838,c_7537]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_182,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_1002,plain,
% 4.08/1.01      ( X0 != X1 | k2_relat_1(sK6) != X1 | k2_relat_1(sK6) = X0 ),
% 4.08/1.01      inference(instantiation,[status(thm)],[c_182]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_1470,plain,
% 4.08/1.01      ( X0 != k2_relat_1(sK6)
% 4.08/1.01      | k2_relat_1(sK6) = X0
% 4.08/1.01      | k2_relat_1(sK6) != k2_relat_1(sK6) ),
% 4.08/1.01      inference(instantiation,[status(thm)],[c_1002]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_3532,plain,
% 4.08/1.01      ( k2_relat_1(sK6) != k2_relat_1(sK6)
% 4.08/1.01      | k2_relat_1(sK6) = k1_xboole_0
% 4.08/1.01      | k1_xboole_0 != k2_relat_1(sK6) ),
% 4.08/1.01      inference(instantiation,[status(thm)],[c_1470]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_181,plain,( X0 = X0 ),theory(equality) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_1435,plain,
% 4.08/1.01      ( sK6 = sK6 ),
% 4.08/1.01      inference(instantiation,[status(thm)],[c_181]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_188,plain,
% 4.08/1.01      ( X0 != X1 | k2_relat_1(X0) = k2_relat_1(X1) ),
% 4.08/1.01      theory(equality) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_1004,plain,
% 4.08/1.01      ( k2_relat_1(sK6) = k2_relat_1(X0) | sK6 != X0 ),
% 4.08/1.01      inference(instantiation,[status(thm)],[c_188]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_1434,plain,
% 4.08/1.01      ( k2_relat_1(sK6) = k2_relat_1(sK6) | sK6 != sK6 ),
% 4.08/1.01      inference(instantiation,[status(thm)],[c_1004]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_6,plain,
% 4.08/1.01      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
% 4.08/1.01      | sK1(X1,X0) != X0
% 4.08/1.01      | k1_xboole_0 = X1 ),
% 4.08/1.01      inference(cnf_transformation,[],[f72]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_753,plain,
% 4.08/1.01      ( k3_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k2_relat_1(sK6)
% 4.08/1.01      | sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5)) != k1_funct_1(sK6,sK5)
% 4.08/1.01      | k1_xboole_0 = k2_relat_1(sK6) ),
% 4.08/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(contradiction,plain,
% 4.08/1.01      ( $false ),
% 4.08/1.01      inference(minisat,
% 4.08/1.01                [status(thm)],
% 4.08/1.01                [c_8847,c_3532,c_1819,c_1435,c_1434,c_769,c_753,c_18,
% 4.08/1.01                 c_22]) ).
% 4.08/1.01  
% 4.08/1.01  
% 4.08/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 4.08/1.01  
% 4.08/1.01  ------                               Statistics
% 4.08/1.01  
% 4.08/1.01  ------ Selected
% 4.08/1.01  
% 4.08/1.01  total_time:                             0.388
% 4.08/1.01  
%------------------------------------------------------------------------------
