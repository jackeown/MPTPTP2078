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
% DateTime   : Thu Dec  3 11:49:19 EST 2020

% Result     : Theorem 6.85s
% Output     : CNFRefutation 6.85s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 626 expanded)
%              Number of clauses        :   65 ( 112 expanded)
%              Number of leaves         :   21 ( 166 expanded)
%              Depth                    :   20
%              Number of atoms          :  543 (2371 expanded)
%              Number of equality atoms :  340 (1359 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f9])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f26])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f46,f81])).

fof(f83,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f45,f82])).

fof(f84,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f83])).

fof(f85,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f84])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | k1_xboole_0 = X0
      | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f53,f85])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f39,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X5)) = X5
        & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) = X2
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
              ( k1_funct_1(X0,X3) != sK3(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK3(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK3(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK3(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK4(X0,X1)) = sK3(X0,X1)
                  & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK3(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK5(X0,X5)) = X5
                    & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f36,f39,f38,f37])).

fof(f72,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK5(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f102,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK5(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f41,plain,
    ( ? [X0,X1] :
        ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
        & k1_tarski(X0) = k1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7)
      & k1_tarski(sK6) = k1_relat_1(sK7)
      & v1_funct_1(sK7)
      & v1_relat_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7)
    & k1_tarski(sK6) = k1_relat_1(sK7)
    & v1_funct_1(sK7)
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f21,f41])).

fof(f78,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f42])).

fof(f77,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f42])).

fof(f79,plain,(
    k1_tarski(sK6) = k1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f42])).

fof(f91,plain,(
    k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k1_relat_1(sK7) ),
    inference(definition_unfolding,[],[f79,f85])).

fof(f80,plain,(
    k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) ),
    inference(cnf_transformation,[],[f42])).

fof(f90,plain,(
    k5_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) ),
    inference(definition_unfolding,[],[f80,f85])).

fof(f54,plain,(
    ! [X0,X1] :
      ( sK1(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f86,plain,(
    ! [X0,X1] :
      ( sK1(X0,X1) != X1
      | k1_xboole_0 = X0
      | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f54,f85])).

fof(f71,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK5(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f103,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK5(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X4 != X6
              & X3 != X6
              & X2 != X6
              & X1 != X6
              & X0 != X6 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X4,X3,X2,X1,X0,X5] :
      ( sP0(X4,X3,X2,X1,X0,X5)
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> sP0(X4,X3,X2,X1,X0,X5) ) ),
    inference(definition_folding,[],[f16,f22])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ~ sP0(X4,X3,X2,X1,X0,X5) )
      & ( sP0(X4,X3,X2,X1,X0,X5)
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP0(X4,X3,X2,X1,X0,X5)
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP0(X4,X3,X2,X1,X0,X5)
      | k5_enumset1(X0,X0,X0,X1,X2,X3,X4) != X5 ) ),
    inference(definition_unfolding,[],[f67,f81])).

fof(f99,plain,(
    ! [X4,X2,X0,X3,X1] : sP0(X4,X3,X2,X1,X0,k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) ),
    inference(equality_resolution,[],[f89])).

fof(f28,plain,(
    ! [X4,X3,X2,X1,X0,X5] :
      ( ( sP0(X4,X3,X2,X1,X0,X5)
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X5) ) )
        | ~ sP0(X4,X3,X2,X1,X0,X5) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f29,plain,(
    ! [X4,X3,X2,X1,X0,X5] :
      ( ( sP0(X4,X3,X2,X1,X0,X5)
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X5) ) )
        | ~ sP0(X4,X3,X2,X1,X0,X5) ) ) ),
    inference(flattening,[],[f28])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP0(X0,X1,X2,X3,X4,X5)
        | ? [X6] :
            ( ( ( X0 != X6
                & X1 != X6
                & X2 != X6
                & X3 != X6
                & X4 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X0 = X6
              | X1 = X6
              | X2 = X6
              | X3 = X6
              | X4 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ( X0 != X7
                & X1 != X7
                & X2 != X7
                & X3 != X7
                & X4 != X7 ) )
            & ( X0 = X7
              | X1 = X7
              | X2 = X7
              | X3 = X7
              | X4 = X7
              | ~ r2_hidden(X7,X5) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ( ( X0 != X6
              & X1 != X6
              & X2 != X6
              & X3 != X6
              & X4 != X6 )
            | ~ r2_hidden(X6,X5) )
          & ( X0 = X6
            | X1 = X6
            | X2 = X6
            | X3 = X6
            | X4 = X6
            | r2_hidden(X6,X5) ) )
     => ( ( ( sK2(X0,X1,X2,X3,X4,X5) != X0
            & sK2(X0,X1,X2,X3,X4,X5) != X1
            & sK2(X0,X1,X2,X3,X4,X5) != X2
            & sK2(X0,X1,X2,X3,X4,X5) != X3
            & sK2(X0,X1,X2,X3,X4,X5) != X4 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3,X4,X5),X5) )
        & ( sK2(X0,X1,X2,X3,X4,X5) = X0
          | sK2(X0,X1,X2,X3,X4,X5) = X1
          | sK2(X0,X1,X2,X3,X4,X5) = X2
          | sK2(X0,X1,X2,X3,X4,X5) = X3
          | sK2(X0,X1,X2,X3,X4,X5) = X4
          | r2_hidden(sK2(X0,X1,X2,X3,X4,X5),X5) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP0(X0,X1,X2,X3,X4,X5)
        | ( ( ( sK2(X0,X1,X2,X3,X4,X5) != X0
              & sK2(X0,X1,X2,X3,X4,X5) != X1
              & sK2(X0,X1,X2,X3,X4,X5) != X2
              & sK2(X0,X1,X2,X3,X4,X5) != X3
              & sK2(X0,X1,X2,X3,X4,X5) != X4 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3,X4,X5),X5) )
          & ( sK2(X0,X1,X2,X3,X4,X5) = X0
            | sK2(X0,X1,X2,X3,X4,X5) = X1
            | sK2(X0,X1,X2,X3,X4,X5) = X2
            | sK2(X0,X1,X2,X3,X4,X5) = X3
            | sK2(X0,X1,X2,X3,X4,X5) = X4
            | r2_hidden(sK2(X0,X1,X2,X3,X4,X5),X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ( X0 != X7
                & X1 != X7
                & X2 != X7
                & X3 != X7
                & X4 != X7 ) )
            & ( X0 = X7
              | X1 = X7
              | X2 = X7
              | X3 = X7
              | X4 = X7
              | ~ r2_hidden(X7,X5) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).

fof(f55,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( X0 = X7
      | X1 = X7
      | X2 = X7
      | X3 = X7
      | X4 = X7
      | ~ r2_hidden(X7,X5)
      | ~ sP0(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f56,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | X4 != X7
      | ~ sP0(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f98,plain,(
    ! [X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | ~ sP0(X0,X1,X2,X3,X7,X5) ) ),
    inference(equality_resolution,[],[f56])).

fof(f73,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f100,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f101,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f100])).

fof(f60,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | X0 != X7
      | ~ sP0(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f94,plain,(
    ! [X4,X2,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | ~ sP0(X7,X1,X2,X3,X4,X5) ) ),
    inference(equality_resolution,[],[f60])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f24])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f92,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f51])).

fof(f8,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_3077,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_26,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK5(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_354,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK5(X1,X0)) = X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_30])).

cnf(c_355,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK7))
    | ~ v1_relat_1(sK7)
    | k1_funct_1(sK7,sK5(sK7,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_354])).

cnf(c_31,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_359,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK7))
    | k1_funct_1(sK7,sK5(sK7,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_355,c_31])).

cnf(c_3059,plain,
    ( k1_funct_1(sK7,sK5(sK7,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_359])).

cnf(c_4768,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(sK7)
    | k1_funct_1(sK7,sK5(sK7,sK1(k2_relat_1(sK7),X0))) = sK1(k2_relat_1(sK7),X0)
    | k2_relat_1(sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3077,c_3059])).

cnf(c_29,negated_conjecture,
    ( k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_20060,plain,
    ( k1_funct_1(sK7,sK5(sK7,sK1(k2_relat_1(sK7),sK6))) = sK1(k2_relat_1(sK7),sK6)
    | k2_relat_1(sK7) = k1_relat_1(sK7)
    | k2_relat_1(sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4768,c_29])).

cnf(c_28,negated_conjecture,
    ( k5_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_4,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = X1
    | sK1(X1,X0) != X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_3110,plain,
    ( k5_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) = k2_relat_1(sK7)
    | sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK6)) != k1_funct_1(sK7,sK6)
    | k1_xboole_0 = k2_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2528,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4212,plain,
    ( k2_relat_1(sK7) = k2_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_2528])).

cnf(c_2529,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3555,plain,
    ( X0 != X1
    | k2_relat_1(sK7) != X1
    | k2_relat_1(sK7) = X0 ),
    inference(instantiation,[status(thm)],[c_2529])).

cnf(c_4148,plain,
    ( X0 != k2_relat_1(sK7)
    | k2_relat_1(sK7) = X0
    | k2_relat_1(sK7) != k2_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_3555])).

cnf(c_6269,plain,
    ( k2_relat_1(sK7) != k2_relat_1(sK7)
    | k2_relat_1(sK7) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_4148])).

cnf(c_27,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK5(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_336,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK5(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_30])).

cnf(c_337,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK7))
    | r2_hidden(sK5(sK7,X0),k1_relat_1(sK7))
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_336])).

cnf(c_341,plain,
    ( r2_hidden(sK5(sK7,X0),k1_relat_1(sK7))
    | ~ r2_hidden(X0,k2_relat_1(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_337,c_31])).

cnf(c_342,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK7))
    | r2_hidden(sK5(sK7,X0),k1_relat_1(sK7)) ),
    inference(renaming,[status(thm)],[c_341])).

cnf(c_3060,plain,
    ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | r2_hidden(sK5(sK7,X0),k1_relat_1(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_342])).

cnf(c_19,plain,
    ( sP0(X0,X1,X2,X3,X4,k5_enumset1(X4,X4,X4,X3,X2,X1,X0)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_3063,plain,
    ( sP0(X0,X1,X2,X3,X4,k5_enumset1(X4,X4,X4,X3,X2,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4059,plain,
    ( sP0(sK6,sK6,sK6,sK6,sK6,k1_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_29,c_3063])).

cnf(c_17,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5)
    | ~ r2_hidden(X6,X5)
    | X6 = X4
    | X6 = X3
    | X6 = X2
    | X6 = X1
    | X6 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3065,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | X0 = X4
    | X0 = X5
    | sP0(X5,X4,X3,X2,X1,X6) != iProver_top
    | r2_hidden(X0,X6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_7767,plain,
    ( sK6 = X0
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4059,c_3065])).

cnf(c_8026,plain,
    ( sK5(sK7,X0) = sK6
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3060,c_7767])).

cnf(c_8036,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(sK7)
    | sK5(sK7,sK1(k2_relat_1(sK7),X0)) = sK6
    | k2_relat_1(sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3077,c_8026])).

cnf(c_13192,plain,
    ( sK5(sK7,sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK6))) = sK6
    | k2_relat_1(sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8036,c_28])).

cnf(c_20059,plain,
    ( k1_funct_1(sK7,sK5(sK7,sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK6)))) = sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK6))
    | k2_relat_1(sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4768,c_28])).

cnf(c_20475,plain,
    ( sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK6)) = k1_funct_1(sK7,sK6)
    | k2_relat_1(sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13192,c_20059])).

cnf(c_20484,plain,
    ( k2_relat_1(sK7) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20060,c_28,c_3110,c_4212,c_6269,c_20475])).

cnf(c_16,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5)
    | r2_hidden(X4,X5) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_3066,plain,
    ( sP0(X0,X1,X2,X3,X4,X5) != iProver_top
    | r2_hidden(X4,X5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4985,plain,
    ( r2_hidden(sK6,k1_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4059,c_3066])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_372,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_30])).

cnf(c_373,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK7))
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7))
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_372])).

cnf(c_377,plain,
    ( r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7))
    | ~ r2_hidden(X0,k1_relat_1(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_373,c_31])).

cnf(c_378,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK7))
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) ),
    inference(renaming,[status(thm)],[c_377])).

cnf(c_3058,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_378])).

cnf(c_3320,plain,
    ( k1_funct_1(sK7,sK5(sK7,k1_funct_1(sK7,X0))) = k1_funct_1(sK7,X0)
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3058,c_3059])).

cnf(c_5173,plain,
    ( k1_funct_1(sK7,sK5(sK7,k1_funct_1(sK7,sK6))) = k1_funct_1(sK7,sK6) ),
    inference(superposition,[status(thm)],[c_4985,c_3320])).

cnf(c_5181,plain,
    ( r2_hidden(sK5(sK7,k1_funct_1(sK7,sK6)),k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,sK6),k2_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5173,c_3058])).

cnf(c_32,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_374,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_373])).

cnf(c_376,plain,
    ( r2_hidden(k1_funct_1(sK7,sK6),k2_relat_1(sK7)) = iProver_top
    | r2_hidden(sK6,k1_relat_1(sK7)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_374])).

cnf(c_12,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5)
    | r2_hidden(X0,X5) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_3167,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,k1_relat_1(sK7))
    | r2_hidden(X0,k1_relat_1(sK7)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_3168,plain,
    ( sP0(X0,X1,X2,X3,X4,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3167])).

cnf(c_3170,plain,
    ( sP0(sK6,sK6,sK6,sK6,sK6,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(sK6,k1_relat_1(sK7)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3168])).

cnf(c_5352,plain,
    ( r2_hidden(k1_funct_1(sK7,sK6),k2_relat_1(sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5181,c_32,c_376,c_3170,c_4059])).

cnf(c_20541,plain,
    ( r2_hidden(k1_funct_1(sK7,sK6),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_20484,c_5352])).

cnf(c_0,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_3078,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4204,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_3078])).

cnf(c_21040,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_20541,c_4204])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:03:24 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 6.85/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.85/1.49  
% 6.85/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.85/1.49  
% 6.85/1.49  ------  iProver source info
% 6.85/1.49  
% 6.85/1.49  git: date: 2020-06-30 10:37:57 +0100
% 6.85/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.85/1.49  git: non_committed_changes: false
% 6.85/1.49  git: last_make_outside_of_git: false
% 6.85/1.49  
% 6.85/1.49  ------ 
% 6.85/1.49  
% 6.85/1.49  ------ Input Options
% 6.85/1.49  
% 6.85/1.49  --out_options                           all
% 6.85/1.49  --tptp_safe_out                         true
% 6.85/1.49  --problem_path                          ""
% 6.85/1.49  --include_path                          ""
% 6.85/1.49  --clausifier                            res/vclausify_rel
% 6.85/1.49  --clausifier_options                    ""
% 6.85/1.49  --stdin                                 false
% 6.85/1.49  --stats_out                             all
% 6.85/1.49  
% 6.85/1.49  ------ General Options
% 6.85/1.49  
% 6.85/1.49  --fof                                   false
% 6.85/1.49  --time_out_real                         305.
% 6.85/1.49  --time_out_virtual                      -1.
% 6.85/1.49  --symbol_type_check                     false
% 6.85/1.49  --clausify_out                          false
% 6.85/1.49  --sig_cnt_out                           false
% 6.85/1.49  --trig_cnt_out                          false
% 6.85/1.49  --trig_cnt_out_tolerance                1.
% 6.85/1.49  --trig_cnt_out_sk_spl                   false
% 6.85/1.49  --abstr_cl_out                          false
% 6.85/1.49  
% 6.85/1.49  ------ Global Options
% 6.85/1.49  
% 6.85/1.49  --schedule                              default
% 6.85/1.49  --add_important_lit                     false
% 6.85/1.49  --prop_solver_per_cl                    1000
% 6.85/1.49  --min_unsat_core                        false
% 6.85/1.49  --soft_assumptions                      false
% 6.85/1.49  --soft_lemma_size                       3
% 6.85/1.49  --prop_impl_unit_size                   0
% 6.85/1.49  --prop_impl_unit                        []
% 6.85/1.49  --share_sel_clauses                     true
% 6.85/1.49  --reset_solvers                         false
% 6.85/1.49  --bc_imp_inh                            [conj_cone]
% 6.85/1.49  --conj_cone_tolerance                   3.
% 6.85/1.49  --extra_neg_conj                        none
% 6.85/1.49  --large_theory_mode                     true
% 6.85/1.49  --prolific_symb_bound                   200
% 6.85/1.49  --lt_threshold                          2000
% 6.85/1.49  --clause_weak_htbl                      true
% 6.85/1.49  --gc_record_bc_elim                     false
% 6.85/1.49  
% 6.85/1.49  ------ Preprocessing Options
% 6.85/1.49  
% 6.85/1.49  --preprocessing_flag                    true
% 6.85/1.49  --time_out_prep_mult                    0.1
% 6.85/1.49  --splitting_mode                        input
% 6.85/1.49  --splitting_grd                         true
% 6.85/1.49  --splitting_cvd                         false
% 6.85/1.49  --splitting_cvd_svl                     false
% 6.85/1.49  --splitting_nvd                         32
% 6.85/1.49  --sub_typing                            true
% 6.85/1.49  --prep_gs_sim                           true
% 6.85/1.49  --prep_unflatten                        true
% 6.85/1.49  --prep_res_sim                          true
% 6.85/1.49  --prep_upred                            true
% 6.85/1.49  --prep_sem_filter                       exhaustive
% 6.85/1.49  --prep_sem_filter_out                   false
% 6.85/1.49  --pred_elim                             true
% 6.85/1.49  --res_sim_input                         true
% 6.85/1.49  --eq_ax_congr_red                       true
% 6.85/1.49  --pure_diseq_elim                       true
% 6.85/1.49  --brand_transform                       false
% 6.85/1.49  --non_eq_to_eq                          false
% 6.85/1.49  --prep_def_merge                        true
% 6.85/1.49  --prep_def_merge_prop_impl              false
% 6.85/1.49  --prep_def_merge_mbd                    true
% 6.85/1.49  --prep_def_merge_tr_red                 false
% 6.85/1.49  --prep_def_merge_tr_cl                  false
% 6.85/1.49  --smt_preprocessing                     true
% 6.85/1.49  --smt_ac_axioms                         fast
% 6.85/1.49  --preprocessed_out                      false
% 6.85/1.49  --preprocessed_stats                    false
% 6.85/1.49  
% 6.85/1.49  ------ Abstraction refinement Options
% 6.85/1.49  
% 6.85/1.49  --abstr_ref                             []
% 6.85/1.49  --abstr_ref_prep                        false
% 6.85/1.49  --abstr_ref_until_sat                   false
% 6.85/1.49  --abstr_ref_sig_restrict                funpre
% 6.85/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 6.85/1.49  --abstr_ref_under                       []
% 6.85/1.49  
% 6.85/1.49  ------ SAT Options
% 6.85/1.49  
% 6.85/1.49  --sat_mode                              false
% 6.85/1.49  --sat_fm_restart_options                ""
% 6.85/1.49  --sat_gr_def                            false
% 6.85/1.49  --sat_epr_types                         true
% 6.85/1.49  --sat_non_cyclic_types                  false
% 6.85/1.49  --sat_finite_models                     false
% 6.85/1.49  --sat_fm_lemmas                         false
% 6.85/1.49  --sat_fm_prep                           false
% 6.85/1.49  --sat_fm_uc_incr                        true
% 6.85/1.49  --sat_out_model                         small
% 6.85/1.49  --sat_out_clauses                       false
% 6.85/1.49  
% 6.85/1.49  ------ QBF Options
% 6.85/1.49  
% 6.85/1.49  --qbf_mode                              false
% 6.85/1.49  --qbf_elim_univ                         false
% 6.85/1.49  --qbf_dom_inst                          none
% 6.85/1.49  --qbf_dom_pre_inst                      false
% 6.85/1.49  --qbf_sk_in                             false
% 6.85/1.49  --qbf_pred_elim                         true
% 6.85/1.49  --qbf_split                             512
% 6.85/1.49  
% 6.85/1.49  ------ BMC1 Options
% 6.85/1.49  
% 6.85/1.49  --bmc1_incremental                      false
% 6.85/1.49  --bmc1_axioms                           reachable_all
% 6.85/1.49  --bmc1_min_bound                        0
% 6.85/1.49  --bmc1_max_bound                        -1
% 6.85/1.49  --bmc1_max_bound_default                -1
% 6.85/1.49  --bmc1_symbol_reachability              true
% 6.85/1.49  --bmc1_property_lemmas                  false
% 6.85/1.49  --bmc1_k_induction                      false
% 6.85/1.49  --bmc1_non_equiv_states                 false
% 6.85/1.49  --bmc1_deadlock                         false
% 6.85/1.49  --bmc1_ucm                              false
% 6.85/1.49  --bmc1_add_unsat_core                   none
% 6.85/1.49  --bmc1_unsat_core_children              false
% 6.85/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 6.85/1.49  --bmc1_out_stat                         full
% 6.85/1.49  --bmc1_ground_init                      false
% 6.85/1.49  --bmc1_pre_inst_next_state              false
% 6.85/1.49  --bmc1_pre_inst_state                   false
% 6.85/1.49  --bmc1_pre_inst_reach_state             false
% 6.85/1.49  --bmc1_out_unsat_core                   false
% 6.85/1.49  --bmc1_aig_witness_out                  false
% 6.85/1.49  --bmc1_verbose                          false
% 6.85/1.49  --bmc1_dump_clauses_tptp                false
% 6.85/1.49  --bmc1_dump_unsat_core_tptp             false
% 6.85/1.49  --bmc1_dump_file                        -
% 6.85/1.49  --bmc1_ucm_expand_uc_limit              128
% 6.85/1.49  --bmc1_ucm_n_expand_iterations          6
% 6.85/1.49  --bmc1_ucm_extend_mode                  1
% 6.85/1.49  --bmc1_ucm_init_mode                    2
% 6.85/1.49  --bmc1_ucm_cone_mode                    none
% 6.85/1.49  --bmc1_ucm_reduced_relation_type        0
% 6.85/1.49  --bmc1_ucm_relax_model                  4
% 6.85/1.49  --bmc1_ucm_full_tr_after_sat            true
% 6.85/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 6.85/1.49  --bmc1_ucm_layered_model                none
% 6.85/1.49  --bmc1_ucm_max_lemma_size               10
% 6.85/1.49  
% 6.85/1.49  ------ AIG Options
% 6.85/1.49  
% 6.85/1.49  --aig_mode                              false
% 6.85/1.49  
% 6.85/1.49  ------ Instantiation Options
% 6.85/1.49  
% 6.85/1.49  --instantiation_flag                    true
% 6.85/1.49  --inst_sos_flag                         true
% 6.85/1.49  --inst_sos_phase                        true
% 6.85/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.85/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.85/1.49  --inst_lit_sel_side                     num_symb
% 6.85/1.49  --inst_solver_per_active                1400
% 6.85/1.49  --inst_solver_calls_frac                1.
% 6.85/1.49  --inst_passive_queue_type               priority_queues
% 6.85/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.85/1.49  --inst_passive_queues_freq              [25;2]
% 6.85/1.49  --inst_dismatching                      true
% 6.85/1.49  --inst_eager_unprocessed_to_passive     true
% 6.85/1.49  --inst_prop_sim_given                   true
% 6.85/1.49  --inst_prop_sim_new                     false
% 6.85/1.49  --inst_subs_new                         false
% 6.85/1.49  --inst_eq_res_simp                      false
% 6.85/1.49  --inst_subs_given                       false
% 6.85/1.49  --inst_orphan_elimination               true
% 6.85/1.49  --inst_learning_loop_flag               true
% 6.85/1.49  --inst_learning_start                   3000
% 6.85/1.49  --inst_learning_factor                  2
% 6.85/1.49  --inst_start_prop_sim_after_learn       3
% 6.85/1.49  --inst_sel_renew                        solver
% 6.85/1.49  --inst_lit_activity_flag                true
% 6.85/1.49  --inst_restr_to_given                   false
% 6.85/1.49  --inst_activity_threshold               500
% 6.85/1.49  --inst_out_proof                        true
% 6.85/1.49  
% 6.85/1.49  ------ Resolution Options
% 6.85/1.49  
% 6.85/1.49  --resolution_flag                       true
% 6.85/1.49  --res_lit_sel                           adaptive
% 6.85/1.49  --res_lit_sel_side                      none
% 6.85/1.49  --res_ordering                          kbo
% 6.85/1.49  --res_to_prop_solver                    active
% 6.85/1.49  --res_prop_simpl_new                    false
% 6.85/1.49  --res_prop_simpl_given                  true
% 6.85/1.49  --res_passive_queue_type                priority_queues
% 6.85/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.85/1.49  --res_passive_queues_freq               [15;5]
% 6.85/1.49  --res_forward_subs                      full
% 6.85/1.49  --res_backward_subs                     full
% 6.85/1.49  --res_forward_subs_resolution           true
% 6.85/1.49  --res_backward_subs_resolution          true
% 6.85/1.49  --res_orphan_elimination                true
% 6.85/1.49  --res_time_limit                        2.
% 6.85/1.49  --res_out_proof                         true
% 6.85/1.49  
% 6.85/1.49  ------ Superposition Options
% 6.85/1.49  
% 6.85/1.49  --superposition_flag                    true
% 6.85/1.49  --sup_passive_queue_type                priority_queues
% 6.85/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.85/1.49  --sup_passive_queues_freq               [8;1;4]
% 6.85/1.49  --demod_completeness_check              fast
% 6.85/1.49  --demod_use_ground                      true
% 6.85/1.49  --sup_to_prop_solver                    passive
% 6.85/1.49  --sup_prop_simpl_new                    true
% 6.85/1.49  --sup_prop_simpl_given                  true
% 6.85/1.49  --sup_fun_splitting                     true
% 6.85/1.49  --sup_smt_interval                      50000
% 6.85/1.49  
% 6.85/1.49  ------ Superposition Simplification Setup
% 6.85/1.49  
% 6.85/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 6.85/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 6.85/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 6.85/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 6.85/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 6.85/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 6.85/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 6.85/1.49  --sup_immed_triv                        [TrivRules]
% 6.85/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.85/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 6.85/1.49  --sup_immed_bw_main                     []
% 6.85/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 6.85/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 6.85/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 6.85/1.49  --sup_input_bw                          []
% 6.85/1.49  
% 6.85/1.49  ------ Combination Options
% 6.85/1.49  
% 6.85/1.49  --comb_res_mult                         3
% 6.85/1.49  --comb_sup_mult                         2
% 6.85/1.49  --comb_inst_mult                        10
% 6.85/1.49  
% 6.85/1.49  ------ Debug Options
% 6.85/1.49  
% 6.85/1.49  --dbg_backtrace                         false
% 6.85/1.49  --dbg_dump_prop_clauses                 false
% 6.85/1.49  --dbg_dump_prop_clauses_file            -
% 6.85/1.49  --dbg_out_stat                          false
% 6.85/1.49  ------ Parsing...
% 6.85/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.85/1.49  
% 6.85/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 6.85/1.49  
% 6.85/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.85/1.49  
% 6.85/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.85/1.49  ------ Proving...
% 6.85/1.49  ------ Problem Properties 
% 6.85/1.49  
% 6.85/1.49  
% 6.85/1.49  clauses                                 30
% 6.85/1.49  conjectures                             2
% 6.85/1.49  EPR                                     6
% 6.85/1.49  Horn                                    23
% 6.85/1.49  unary                                   6
% 6.85/1.49  binary                                  11
% 6.85/1.49  lits                                    76
% 6.85/1.49  lits eq                                 38
% 6.85/1.49  fd_pure                                 0
% 6.85/1.49  fd_pseudo                               0
% 6.85/1.49  fd_cond                                 4
% 6.85/1.49  fd_pseudo_cond                          4
% 6.85/1.49  AC symbols                              0
% 6.85/1.49  
% 6.85/1.49  ------ Schedule dynamic 5 is on 
% 6.85/1.49  
% 6.85/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.85/1.49  
% 6.85/1.49  
% 6.85/1.49  ------ 
% 6.85/1.49  Current options:
% 6.85/1.49  ------ 
% 6.85/1.49  
% 6.85/1.49  ------ Input Options
% 6.85/1.49  
% 6.85/1.49  --out_options                           all
% 6.85/1.49  --tptp_safe_out                         true
% 6.85/1.49  --problem_path                          ""
% 6.85/1.49  --include_path                          ""
% 6.85/1.49  --clausifier                            res/vclausify_rel
% 6.85/1.49  --clausifier_options                    ""
% 6.85/1.49  --stdin                                 false
% 6.85/1.49  --stats_out                             all
% 6.85/1.49  
% 6.85/1.49  ------ General Options
% 6.85/1.49  
% 6.85/1.49  --fof                                   false
% 6.85/1.49  --time_out_real                         305.
% 6.85/1.49  --time_out_virtual                      -1.
% 6.85/1.49  --symbol_type_check                     false
% 6.85/1.49  --clausify_out                          false
% 6.85/1.49  --sig_cnt_out                           false
% 6.85/1.49  --trig_cnt_out                          false
% 6.85/1.49  --trig_cnt_out_tolerance                1.
% 6.85/1.49  --trig_cnt_out_sk_spl                   false
% 6.85/1.49  --abstr_cl_out                          false
% 6.85/1.49  
% 6.85/1.49  ------ Global Options
% 6.85/1.49  
% 6.85/1.49  --schedule                              default
% 6.85/1.49  --add_important_lit                     false
% 6.85/1.49  --prop_solver_per_cl                    1000
% 6.85/1.49  --min_unsat_core                        false
% 6.85/1.49  --soft_assumptions                      false
% 6.85/1.49  --soft_lemma_size                       3
% 6.85/1.49  --prop_impl_unit_size                   0
% 6.85/1.49  --prop_impl_unit                        []
% 6.85/1.49  --share_sel_clauses                     true
% 6.85/1.49  --reset_solvers                         false
% 6.85/1.49  --bc_imp_inh                            [conj_cone]
% 6.85/1.49  --conj_cone_tolerance                   3.
% 6.85/1.49  --extra_neg_conj                        none
% 6.85/1.49  --large_theory_mode                     true
% 6.85/1.49  --prolific_symb_bound                   200
% 6.85/1.49  --lt_threshold                          2000
% 6.85/1.49  --clause_weak_htbl                      true
% 6.85/1.49  --gc_record_bc_elim                     false
% 6.85/1.49  
% 6.85/1.49  ------ Preprocessing Options
% 6.85/1.49  
% 6.85/1.49  --preprocessing_flag                    true
% 6.85/1.49  --time_out_prep_mult                    0.1
% 6.85/1.49  --splitting_mode                        input
% 6.85/1.49  --splitting_grd                         true
% 6.85/1.49  --splitting_cvd                         false
% 6.85/1.49  --splitting_cvd_svl                     false
% 6.85/1.49  --splitting_nvd                         32
% 6.85/1.49  --sub_typing                            true
% 6.85/1.49  --prep_gs_sim                           true
% 6.85/1.49  --prep_unflatten                        true
% 6.85/1.49  --prep_res_sim                          true
% 6.85/1.49  --prep_upred                            true
% 6.85/1.49  --prep_sem_filter                       exhaustive
% 6.85/1.49  --prep_sem_filter_out                   false
% 6.85/1.49  --pred_elim                             true
% 6.85/1.49  --res_sim_input                         true
% 6.85/1.49  --eq_ax_congr_red                       true
% 6.85/1.49  --pure_diseq_elim                       true
% 6.85/1.49  --brand_transform                       false
% 6.85/1.49  --non_eq_to_eq                          false
% 6.85/1.49  --prep_def_merge                        true
% 6.85/1.49  --prep_def_merge_prop_impl              false
% 6.85/1.49  --prep_def_merge_mbd                    true
% 6.85/1.49  --prep_def_merge_tr_red                 false
% 6.85/1.49  --prep_def_merge_tr_cl                  false
% 6.85/1.49  --smt_preprocessing                     true
% 6.85/1.49  --smt_ac_axioms                         fast
% 6.85/1.49  --preprocessed_out                      false
% 6.85/1.49  --preprocessed_stats                    false
% 6.85/1.49  
% 6.85/1.49  ------ Abstraction refinement Options
% 6.85/1.49  
% 6.85/1.49  --abstr_ref                             []
% 6.85/1.49  --abstr_ref_prep                        false
% 6.85/1.49  --abstr_ref_until_sat                   false
% 6.85/1.49  --abstr_ref_sig_restrict                funpre
% 6.85/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 6.85/1.49  --abstr_ref_under                       []
% 6.85/1.49  
% 6.85/1.49  ------ SAT Options
% 6.85/1.49  
% 6.85/1.49  --sat_mode                              false
% 6.85/1.49  --sat_fm_restart_options                ""
% 6.85/1.49  --sat_gr_def                            false
% 6.85/1.49  --sat_epr_types                         true
% 6.85/1.49  --sat_non_cyclic_types                  false
% 6.85/1.49  --sat_finite_models                     false
% 6.85/1.49  --sat_fm_lemmas                         false
% 6.85/1.49  --sat_fm_prep                           false
% 6.85/1.49  --sat_fm_uc_incr                        true
% 6.85/1.49  --sat_out_model                         small
% 6.85/1.49  --sat_out_clauses                       false
% 6.85/1.49  
% 6.85/1.49  ------ QBF Options
% 6.85/1.49  
% 6.85/1.49  --qbf_mode                              false
% 6.85/1.49  --qbf_elim_univ                         false
% 6.85/1.49  --qbf_dom_inst                          none
% 6.85/1.49  --qbf_dom_pre_inst                      false
% 6.85/1.49  --qbf_sk_in                             false
% 6.85/1.49  --qbf_pred_elim                         true
% 6.85/1.49  --qbf_split                             512
% 6.85/1.49  
% 6.85/1.49  ------ BMC1 Options
% 6.85/1.49  
% 6.85/1.49  --bmc1_incremental                      false
% 6.85/1.49  --bmc1_axioms                           reachable_all
% 6.85/1.49  --bmc1_min_bound                        0
% 6.85/1.49  --bmc1_max_bound                        -1
% 6.85/1.49  --bmc1_max_bound_default                -1
% 6.85/1.49  --bmc1_symbol_reachability              true
% 6.85/1.49  --bmc1_property_lemmas                  false
% 6.85/1.49  --bmc1_k_induction                      false
% 6.85/1.49  --bmc1_non_equiv_states                 false
% 6.85/1.49  --bmc1_deadlock                         false
% 6.85/1.49  --bmc1_ucm                              false
% 6.85/1.49  --bmc1_add_unsat_core                   none
% 6.85/1.49  --bmc1_unsat_core_children              false
% 6.85/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 6.85/1.49  --bmc1_out_stat                         full
% 6.85/1.49  --bmc1_ground_init                      false
% 6.85/1.49  --bmc1_pre_inst_next_state              false
% 6.85/1.49  --bmc1_pre_inst_state                   false
% 6.85/1.49  --bmc1_pre_inst_reach_state             false
% 6.85/1.49  --bmc1_out_unsat_core                   false
% 6.85/1.49  --bmc1_aig_witness_out                  false
% 6.85/1.49  --bmc1_verbose                          false
% 6.85/1.49  --bmc1_dump_clauses_tptp                false
% 6.85/1.49  --bmc1_dump_unsat_core_tptp             false
% 6.85/1.49  --bmc1_dump_file                        -
% 6.85/1.49  --bmc1_ucm_expand_uc_limit              128
% 6.85/1.49  --bmc1_ucm_n_expand_iterations          6
% 6.85/1.49  --bmc1_ucm_extend_mode                  1
% 6.85/1.49  --bmc1_ucm_init_mode                    2
% 6.85/1.49  --bmc1_ucm_cone_mode                    none
% 6.85/1.49  --bmc1_ucm_reduced_relation_type        0
% 6.85/1.49  --bmc1_ucm_relax_model                  4
% 6.85/1.49  --bmc1_ucm_full_tr_after_sat            true
% 6.85/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 6.85/1.49  --bmc1_ucm_layered_model                none
% 6.85/1.49  --bmc1_ucm_max_lemma_size               10
% 6.85/1.49  
% 6.85/1.49  ------ AIG Options
% 6.85/1.49  
% 6.85/1.49  --aig_mode                              false
% 6.85/1.49  
% 6.85/1.49  ------ Instantiation Options
% 6.85/1.49  
% 6.85/1.49  --instantiation_flag                    true
% 6.85/1.49  --inst_sos_flag                         true
% 6.85/1.49  --inst_sos_phase                        true
% 6.85/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.85/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.85/1.49  --inst_lit_sel_side                     none
% 6.85/1.49  --inst_solver_per_active                1400
% 6.85/1.49  --inst_solver_calls_frac                1.
% 6.85/1.49  --inst_passive_queue_type               priority_queues
% 6.85/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.85/1.49  --inst_passive_queues_freq              [25;2]
% 6.85/1.49  --inst_dismatching                      true
% 6.85/1.49  --inst_eager_unprocessed_to_passive     true
% 6.85/1.49  --inst_prop_sim_given                   true
% 6.85/1.49  --inst_prop_sim_new                     false
% 6.85/1.49  --inst_subs_new                         false
% 6.85/1.49  --inst_eq_res_simp                      false
% 6.85/1.49  --inst_subs_given                       false
% 6.85/1.49  --inst_orphan_elimination               true
% 6.85/1.49  --inst_learning_loop_flag               true
% 6.85/1.49  --inst_learning_start                   3000
% 6.85/1.49  --inst_learning_factor                  2
% 6.85/1.49  --inst_start_prop_sim_after_learn       3
% 6.85/1.49  --inst_sel_renew                        solver
% 6.85/1.49  --inst_lit_activity_flag                true
% 6.85/1.49  --inst_restr_to_given                   false
% 6.85/1.49  --inst_activity_threshold               500
% 6.85/1.49  --inst_out_proof                        true
% 6.85/1.49  
% 6.85/1.49  ------ Resolution Options
% 6.85/1.49  
% 6.85/1.49  --resolution_flag                       false
% 6.85/1.49  --res_lit_sel                           adaptive
% 6.85/1.49  --res_lit_sel_side                      none
% 6.85/1.49  --res_ordering                          kbo
% 6.85/1.49  --res_to_prop_solver                    active
% 6.85/1.49  --res_prop_simpl_new                    false
% 6.85/1.49  --res_prop_simpl_given                  true
% 6.85/1.49  --res_passive_queue_type                priority_queues
% 6.85/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.85/1.49  --res_passive_queues_freq               [15;5]
% 6.85/1.49  --res_forward_subs                      full
% 6.85/1.49  --res_backward_subs                     full
% 6.85/1.49  --res_forward_subs_resolution           true
% 6.85/1.49  --res_backward_subs_resolution          true
% 6.85/1.49  --res_orphan_elimination                true
% 6.85/1.49  --res_time_limit                        2.
% 6.85/1.49  --res_out_proof                         true
% 6.85/1.49  
% 6.85/1.49  ------ Superposition Options
% 6.85/1.49  
% 6.85/1.49  --superposition_flag                    true
% 6.85/1.49  --sup_passive_queue_type                priority_queues
% 6.85/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.85/1.49  --sup_passive_queues_freq               [8;1;4]
% 6.85/1.49  --demod_completeness_check              fast
% 6.85/1.49  --demod_use_ground                      true
% 6.85/1.49  --sup_to_prop_solver                    passive
% 6.85/1.49  --sup_prop_simpl_new                    true
% 6.85/1.49  --sup_prop_simpl_given                  true
% 6.85/1.49  --sup_fun_splitting                     true
% 6.85/1.49  --sup_smt_interval                      50000
% 6.85/1.49  
% 6.85/1.49  ------ Superposition Simplification Setup
% 6.85/1.49  
% 6.85/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 6.85/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 6.85/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 6.85/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 6.85/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 6.85/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 6.85/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 6.85/1.49  --sup_immed_triv                        [TrivRules]
% 6.85/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.85/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 6.85/1.49  --sup_immed_bw_main                     []
% 6.85/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 6.85/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 6.85/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 6.85/1.49  --sup_input_bw                          []
% 6.85/1.49  
% 6.85/1.49  ------ Combination Options
% 6.85/1.49  
% 6.85/1.49  --comb_res_mult                         3
% 6.85/1.49  --comb_sup_mult                         2
% 6.85/1.49  --comb_inst_mult                        10
% 6.85/1.49  
% 6.85/1.49  ------ Debug Options
% 6.85/1.49  
% 6.85/1.49  --dbg_backtrace                         false
% 6.85/1.49  --dbg_dump_prop_clauses                 false
% 6.85/1.49  --dbg_dump_prop_clauses_file            -
% 6.85/1.49  --dbg_out_stat                          false
% 6.85/1.49  
% 6.85/1.49  
% 6.85/1.49  
% 6.85/1.49  
% 6.85/1.49  ------ Proving...
% 6.85/1.49  
% 6.85/1.49  
% 6.85/1.49  % SZS status Theorem for theBenchmark.p
% 6.85/1.49  
% 6.85/1.49   Resolution empty clause
% 6.85/1.49  
% 6.85/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 6.85/1.49  
% 6.85/1.49  fof(f9,axiom,(
% 6.85/1.49    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 6.85/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.85/1.49  
% 6.85/1.49  fof(f15,plain,(
% 6.85/1.49    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 6.85/1.49    inference(ennf_transformation,[],[f9])).
% 6.85/1.49  
% 6.85/1.49  fof(f26,plain,(
% 6.85/1.49    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK1(X0,X1) != X1 & r2_hidden(sK1(X0,X1),X0)))),
% 6.85/1.49    introduced(choice_axiom,[])).
% 6.85/1.49  
% 6.85/1.49  fof(f27,plain,(
% 6.85/1.49    ! [X0,X1] : ((sK1(X0,X1) != X1 & r2_hidden(sK1(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 6.85/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f26])).
% 6.85/1.49  
% 6.85/1.49  fof(f53,plain,(
% 6.85/1.49    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 6.85/1.49    inference(cnf_transformation,[],[f27])).
% 6.85/1.49  
% 6.85/1.49  fof(f1,axiom,(
% 6.85/1.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 6.85/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.85/1.49  
% 6.85/1.49  fof(f43,plain,(
% 6.85/1.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 6.85/1.49    inference(cnf_transformation,[],[f1])).
% 6.85/1.49  
% 6.85/1.49  fof(f2,axiom,(
% 6.85/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 6.85/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.85/1.49  
% 6.85/1.49  fof(f44,plain,(
% 6.85/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 6.85/1.49    inference(cnf_transformation,[],[f2])).
% 6.85/1.49  
% 6.85/1.49  fof(f3,axiom,(
% 6.85/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 6.85/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.85/1.49  
% 6.85/1.49  fof(f45,plain,(
% 6.85/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 6.85/1.49    inference(cnf_transformation,[],[f3])).
% 6.85/1.49  
% 6.85/1.49  fof(f4,axiom,(
% 6.85/1.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 6.85/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.85/1.49  
% 6.85/1.49  fof(f46,plain,(
% 6.85/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 6.85/1.49    inference(cnf_transformation,[],[f4])).
% 6.85/1.49  
% 6.85/1.49  fof(f5,axiom,(
% 6.85/1.49    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 6.85/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.85/1.49  
% 6.85/1.49  fof(f47,plain,(
% 6.85/1.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 6.85/1.49    inference(cnf_transformation,[],[f5])).
% 6.85/1.49  
% 6.85/1.49  fof(f6,axiom,(
% 6.85/1.49    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 6.85/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.85/1.49  
% 6.85/1.49  fof(f48,plain,(
% 6.85/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 6.85/1.49    inference(cnf_transformation,[],[f6])).
% 6.85/1.49  
% 6.85/1.49  fof(f81,plain,(
% 6.85/1.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 6.85/1.49    inference(definition_unfolding,[],[f47,f48])).
% 6.85/1.49  
% 6.85/1.49  fof(f82,plain,(
% 6.85/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 6.85/1.49    inference(definition_unfolding,[],[f46,f81])).
% 6.85/1.49  
% 6.85/1.49  fof(f83,plain,(
% 6.85/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 6.85/1.49    inference(definition_unfolding,[],[f45,f82])).
% 6.85/1.49  
% 6.85/1.49  fof(f84,plain,(
% 6.85/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 6.85/1.49    inference(definition_unfolding,[],[f44,f83])).
% 6.85/1.49  
% 6.85/1.49  fof(f85,plain,(
% 6.85/1.49    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 6.85/1.49    inference(definition_unfolding,[],[f43,f84])).
% 6.85/1.49  
% 6.85/1.49  fof(f87,plain,(
% 6.85/1.49    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | k1_xboole_0 = X0 | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0) )),
% 6.85/1.49    inference(definition_unfolding,[],[f53,f85])).
% 6.85/1.49  
% 6.85/1.49  fof(f12,axiom,(
% 6.85/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 6.85/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.85/1.49  
% 6.85/1.49  fof(f18,plain,(
% 6.85/1.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.85/1.49    inference(ennf_transformation,[],[f12])).
% 6.85/1.49  
% 6.85/1.49  fof(f19,plain,(
% 6.85/1.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.85/1.49    inference(flattening,[],[f18])).
% 6.85/1.49  
% 6.85/1.49  fof(f35,plain,(
% 6.85/1.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.85/1.49    inference(nnf_transformation,[],[f19])).
% 6.85/1.49  
% 6.85/1.49  fof(f36,plain,(
% 6.85/1.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.85/1.49    inference(rectify,[],[f35])).
% 6.85/1.49  
% 6.85/1.49  fof(f39,plain,(
% 6.85/1.49    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))))),
% 6.85/1.49    introduced(choice_axiom,[])).
% 6.85/1.49  
% 6.85/1.49  fof(f38,plain,(
% 6.85/1.49    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1)) = X2 & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))) )),
% 6.85/1.49    introduced(choice_axiom,[])).
% 6.85/1.49  
% 6.85/1.49  fof(f37,plain,(
% 6.85/1.49    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK3(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1))))),
% 6.85/1.49    introduced(choice_axiom,[])).
% 6.85/1.49  
% 6.85/1.49  fof(f40,plain,(
% 6.85/1.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & ((k1_funct_1(X0,sK4(X0,X1)) = sK3(X0,X1) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.85/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f36,f39,f38,f37])).
% 6.85/1.49  
% 6.85/1.49  fof(f72,plain,(
% 6.85/1.49    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK5(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.85/1.49    inference(cnf_transformation,[],[f40])).
% 6.85/1.49  
% 6.85/1.49  fof(f102,plain,(
% 6.85/1.49    ( ! [X0,X5] : (k1_funct_1(X0,sK5(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.85/1.49    inference(equality_resolution,[],[f72])).
% 6.85/1.49  
% 6.85/1.49  fof(f13,conjecture,(
% 6.85/1.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 6.85/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.85/1.49  
% 6.85/1.49  fof(f14,negated_conjecture,(
% 6.85/1.49    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 6.85/1.49    inference(negated_conjecture,[],[f13])).
% 6.85/1.49  
% 6.85/1.49  fof(f20,plain,(
% 6.85/1.49    ? [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 6.85/1.49    inference(ennf_transformation,[],[f14])).
% 6.85/1.49  
% 6.85/1.49  fof(f21,plain,(
% 6.85/1.49    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 6.85/1.49    inference(flattening,[],[f20])).
% 6.85/1.49  
% 6.85/1.49  fof(f41,plain,(
% 6.85/1.49    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) & k1_tarski(sK6) = k1_relat_1(sK7) & v1_funct_1(sK7) & v1_relat_1(sK7))),
% 6.85/1.49    introduced(choice_axiom,[])).
% 6.85/1.49  
% 6.85/1.49  fof(f42,plain,(
% 6.85/1.49    k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) & k1_tarski(sK6) = k1_relat_1(sK7) & v1_funct_1(sK7) & v1_relat_1(sK7)),
% 6.85/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f21,f41])).
% 6.85/1.49  
% 6.85/1.49  fof(f78,plain,(
% 6.85/1.49    v1_funct_1(sK7)),
% 6.85/1.49    inference(cnf_transformation,[],[f42])).
% 6.85/1.49  
% 6.85/1.49  fof(f77,plain,(
% 6.85/1.49    v1_relat_1(sK7)),
% 6.85/1.49    inference(cnf_transformation,[],[f42])).
% 6.85/1.49  
% 6.85/1.49  fof(f79,plain,(
% 6.85/1.49    k1_tarski(sK6) = k1_relat_1(sK7)),
% 6.85/1.49    inference(cnf_transformation,[],[f42])).
% 6.85/1.49  
% 6.85/1.49  fof(f91,plain,(
% 6.85/1.49    k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k1_relat_1(sK7)),
% 6.85/1.49    inference(definition_unfolding,[],[f79,f85])).
% 6.85/1.49  
% 6.85/1.49  fof(f80,plain,(
% 6.85/1.49    k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7)),
% 6.85/1.49    inference(cnf_transformation,[],[f42])).
% 6.85/1.49  
% 6.85/1.49  fof(f90,plain,(
% 6.85/1.49    k5_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) != k2_relat_1(sK7)),
% 6.85/1.49    inference(definition_unfolding,[],[f80,f85])).
% 6.85/1.49  
% 6.85/1.49  fof(f54,plain,(
% 6.85/1.49    ( ! [X0,X1] : (sK1(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 6.85/1.49    inference(cnf_transformation,[],[f27])).
% 6.85/1.49  
% 6.85/1.49  fof(f86,plain,(
% 6.85/1.49    ( ! [X0,X1] : (sK1(X0,X1) != X1 | k1_xboole_0 = X0 | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0) )),
% 6.85/1.49    inference(definition_unfolding,[],[f54,f85])).
% 6.85/1.49  
% 6.85/1.49  fof(f71,plain,(
% 6.85/1.49    ( ! [X0,X5,X1] : (r2_hidden(sK5(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.85/1.49    inference(cnf_transformation,[],[f40])).
% 6.85/1.49  
% 6.85/1.49  fof(f103,plain,(
% 6.85/1.49    ( ! [X0,X5] : (r2_hidden(sK5(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.85/1.49    inference(equality_resolution,[],[f71])).
% 6.85/1.49  
% 6.85/1.49  fof(f10,axiom,(
% 6.85/1.49    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> ~(X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)))),
% 6.85/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.85/1.49  
% 6.85/1.49  fof(f16,plain,(
% 6.85/1.49    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 6.85/1.49    inference(ennf_transformation,[],[f10])).
% 6.85/1.50  
% 6.85/1.50  fof(f22,plain,(
% 6.85/1.50    ! [X4,X3,X2,X1,X0,X5] : (sP0(X4,X3,X2,X1,X0,X5) <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 6.85/1.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 6.85/1.50  
% 6.85/1.50  fof(f23,plain,(
% 6.85/1.50    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> sP0(X4,X3,X2,X1,X0,X5))),
% 6.85/1.50    inference(definition_folding,[],[f16,f22])).
% 6.85/1.50  
% 6.85/1.50  fof(f33,plain,(
% 6.85/1.50    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | ~sP0(X4,X3,X2,X1,X0,X5)) & (sP0(X4,X3,X2,X1,X0,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 6.85/1.50    inference(nnf_transformation,[],[f23])).
% 6.85/1.50  
% 6.85/1.50  fof(f67,plain,(
% 6.85/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (sP0(X4,X3,X2,X1,X0,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5) )),
% 6.85/1.50    inference(cnf_transformation,[],[f33])).
% 6.85/1.50  
% 6.85/1.50  fof(f89,plain,(
% 6.85/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (sP0(X4,X3,X2,X1,X0,X5) | k5_enumset1(X0,X0,X0,X1,X2,X3,X4) != X5) )),
% 6.85/1.50    inference(definition_unfolding,[],[f67,f81])).
% 6.85/1.50  
% 6.85/1.50  fof(f99,plain,(
% 6.85/1.50    ( ! [X4,X2,X0,X3,X1] : (sP0(X4,X3,X2,X1,X0,k5_enumset1(X0,X0,X0,X1,X2,X3,X4))) )),
% 6.85/1.50    inference(equality_resolution,[],[f89])).
% 6.85/1.50  
% 6.85/1.50  fof(f28,plain,(
% 6.85/1.50    ! [X4,X3,X2,X1,X0,X5] : ((sP0(X4,X3,X2,X1,X0,X5) | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | ~r2_hidden(X6,X5))) | ~sP0(X4,X3,X2,X1,X0,X5)))),
% 6.85/1.50    inference(nnf_transformation,[],[f22])).
% 6.85/1.50  
% 6.85/1.50  fof(f29,plain,(
% 6.85/1.50    ! [X4,X3,X2,X1,X0,X5] : ((sP0(X4,X3,X2,X1,X0,X5) | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X5))) | ~sP0(X4,X3,X2,X1,X0,X5)))),
% 6.85/1.50    inference(flattening,[],[f28])).
% 6.85/1.50  
% 6.85/1.50  fof(f30,plain,(
% 6.85/1.50    ! [X0,X1,X2,X3,X4,X5] : ((sP0(X0,X1,X2,X3,X4,X5) | ? [X6] : (((X0 != X6 & X1 != X6 & X2 != X6 & X3 != X6 & X4 != X6) | ~r2_hidden(X6,X5)) & (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | X4 = X6 | r2_hidden(X6,X5)))) & (! [X7] : ((r2_hidden(X7,X5) | (X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | ~r2_hidden(X7,X5))) | ~sP0(X0,X1,X2,X3,X4,X5)))),
% 6.85/1.50    inference(rectify,[],[f29])).
% 6.85/1.50  
% 6.85/1.50  fof(f31,plain,(
% 6.85/1.50    ! [X5,X4,X3,X2,X1,X0] : (? [X6] : (((X0 != X6 & X1 != X6 & X2 != X6 & X3 != X6 & X4 != X6) | ~r2_hidden(X6,X5)) & (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | X4 = X6 | r2_hidden(X6,X5))) => (((sK2(X0,X1,X2,X3,X4,X5) != X0 & sK2(X0,X1,X2,X3,X4,X5) != X1 & sK2(X0,X1,X2,X3,X4,X5) != X2 & sK2(X0,X1,X2,X3,X4,X5) != X3 & sK2(X0,X1,X2,X3,X4,X5) != X4) | ~r2_hidden(sK2(X0,X1,X2,X3,X4,X5),X5)) & (sK2(X0,X1,X2,X3,X4,X5) = X0 | sK2(X0,X1,X2,X3,X4,X5) = X1 | sK2(X0,X1,X2,X3,X4,X5) = X2 | sK2(X0,X1,X2,X3,X4,X5) = X3 | sK2(X0,X1,X2,X3,X4,X5) = X4 | r2_hidden(sK2(X0,X1,X2,X3,X4,X5),X5))))),
% 6.85/1.50    introduced(choice_axiom,[])).
% 6.85/1.50  
% 6.85/1.50  fof(f32,plain,(
% 6.85/1.50    ! [X0,X1,X2,X3,X4,X5] : ((sP0(X0,X1,X2,X3,X4,X5) | (((sK2(X0,X1,X2,X3,X4,X5) != X0 & sK2(X0,X1,X2,X3,X4,X5) != X1 & sK2(X0,X1,X2,X3,X4,X5) != X2 & sK2(X0,X1,X2,X3,X4,X5) != X3 & sK2(X0,X1,X2,X3,X4,X5) != X4) | ~r2_hidden(sK2(X0,X1,X2,X3,X4,X5),X5)) & (sK2(X0,X1,X2,X3,X4,X5) = X0 | sK2(X0,X1,X2,X3,X4,X5) = X1 | sK2(X0,X1,X2,X3,X4,X5) = X2 | sK2(X0,X1,X2,X3,X4,X5) = X3 | sK2(X0,X1,X2,X3,X4,X5) = X4 | r2_hidden(sK2(X0,X1,X2,X3,X4,X5),X5)))) & (! [X7] : ((r2_hidden(X7,X5) | (X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | ~r2_hidden(X7,X5))) | ~sP0(X0,X1,X2,X3,X4,X5)))),
% 6.85/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).
% 6.85/1.50  
% 6.85/1.50  fof(f55,plain,(
% 6.85/1.50    ( ! [X4,X2,X0,X7,X5,X3,X1] : (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | ~r2_hidden(X7,X5) | ~sP0(X0,X1,X2,X3,X4,X5)) )),
% 6.85/1.50    inference(cnf_transformation,[],[f32])).
% 6.85/1.50  
% 6.85/1.50  fof(f56,plain,(
% 6.85/1.50    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,X5) | X4 != X7 | ~sP0(X0,X1,X2,X3,X4,X5)) )),
% 6.85/1.50    inference(cnf_transformation,[],[f32])).
% 6.85/1.50  
% 6.85/1.50  fof(f98,plain,(
% 6.85/1.50    ( ! [X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,X5) | ~sP0(X0,X1,X2,X3,X7,X5)) )),
% 6.85/1.50    inference(equality_resolution,[],[f56])).
% 6.85/1.50  
% 6.85/1.50  fof(f73,plain,(
% 6.85/1.50    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.85/1.50    inference(cnf_transformation,[],[f40])).
% 6.85/1.50  
% 6.85/1.50  fof(f100,plain,(
% 6.85/1.50    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.85/1.50    inference(equality_resolution,[],[f73])).
% 6.85/1.50  
% 6.85/1.50  fof(f101,plain,(
% 6.85/1.50    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.85/1.50    inference(equality_resolution,[],[f100])).
% 6.85/1.50  
% 6.85/1.50  fof(f60,plain,(
% 6.85/1.50    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,X5) | X0 != X7 | ~sP0(X0,X1,X2,X3,X4,X5)) )),
% 6.85/1.50    inference(cnf_transformation,[],[f32])).
% 6.85/1.50  
% 6.85/1.50  fof(f94,plain,(
% 6.85/1.50    ( ! [X4,X2,X7,X5,X3,X1] : (r2_hidden(X7,X5) | ~sP0(X7,X1,X2,X3,X4,X5)) )),
% 6.85/1.50    inference(equality_resolution,[],[f60])).
% 6.85/1.50  
% 6.85/1.50  fof(f7,axiom,(
% 6.85/1.50    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 6.85/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.85/1.50  
% 6.85/1.50  fof(f24,plain,(
% 6.85/1.50    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 6.85/1.50    inference(nnf_transformation,[],[f7])).
% 6.85/1.50  
% 6.85/1.50  fof(f25,plain,(
% 6.85/1.50    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 6.85/1.50    inference(flattening,[],[f24])).
% 6.85/1.50  
% 6.85/1.50  fof(f51,plain,(
% 6.85/1.50    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 6.85/1.50    inference(cnf_transformation,[],[f25])).
% 6.85/1.50  
% 6.85/1.50  fof(f92,plain,(
% 6.85/1.50    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 6.85/1.50    inference(equality_resolution,[],[f51])).
% 6.85/1.50  
% 6.85/1.50  fof(f8,axiom,(
% 6.85/1.50    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 6.85/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.85/1.50  
% 6.85/1.50  fof(f52,plain,(
% 6.85/1.50    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 6.85/1.50    inference(cnf_transformation,[],[f8])).
% 6.85/1.50  
% 6.85/1.50  cnf(c_5,plain,
% 6.85/1.50      ( r2_hidden(sK1(X0,X1),X0)
% 6.85/1.50      | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0
% 6.85/1.50      | k1_xboole_0 = X0 ),
% 6.85/1.50      inference(cnf_transformation,[],[f87]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_3077,plain,
% 6.85/1.50      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = X1
% 6.85/1.50      | k1_xboole_0 = X1
% 6.85/1.50      | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
% 6.85/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_26,plain,
% 6.85/1.50      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 6.85/1.50      | ~ v1_funct_1(X1)
% 6.85/1.50      | ~ v1_relat_1(X1)
% 6.85/1.50      | k1_funct_1(X1,sK5(X1,X0)) = X0 ),
% 6.85/1.50      inference(cnf_transformation,[],[f102]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_30,negated_conjecture,
% 6.85/1.50      ( v1_funct_1(sK7) ),
% 6.85/1.50      inference(cnf_transformation,[],[f78]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_354,plain,
% 6.85/1.50      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 6.85/1.50      | ~ v1_relat_1(X1)
% 6.85/1.50      | k1_funct_1(X1,sK5(X1,X0)) = X0
% 6.85/1.50      | sK7 != X1 ),
% 6.85/1.50      inference(resolution_lifted,[status(thm)],[c_26,c_30]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_355,plain,
% 6.85/1.50      ( ~ r2_hidden(X0,k2_relat_1(sK7))
% 6.85/1.50      | ~ v1_relat_1(sK7)
% 6.85/1.50      | k1_funct_1(sK7,sK5(sK7,X0)) = X0 ),
% 6.85/1.50      inference(unflattening,[status(thm)],[c_354]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_31,negated_conjecture,
% 6.85/1.50      ( v1_relat_1(sK7) ),
% 6.85/1.50      inference(cnf_transformation,[],[f77]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_359,plain,
% 6.85/1.50      ( ~ r2_hidden(X0,k2_relat_1(sK7)) | k1_funct_1(sK7,sK5(sK7,X0)) = X0 ),
% 6.85/1.50      inference(global_propositional_subsumption,[status(thm)],[c_355,c_31]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_3059,plain,
% 6.85/1.50      ( k1_funct_1(sK7,sK5(sK7,X0)) = X0
% 6.85/1.50      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 6.85/1.50      inference(predicate_to_equality,[status(thm)],[c_359]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_4768,plain,
% 6.85/1.50      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(sK7)
% 6.85/1.50      | k1_funct_1(sK7,sK5(sK7,sK1(k2_relat_1(sK7),X0))) = sK1(k2_relat_1(sK7),X0)
% 6.85/1.50      | k2_relat_1(sK7) = k1_xboole_0 ),
% 6.85/1.50      inference(superposition,[status(thm)],[c_3077,c_3059]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_29,negated_conjecture,
% 6.85/1.50      ( k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k1_relat_1(sK7) ),
% 6.85/1.50      inference(cnf_transformation,[],[f91]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_20060,plain,
% 6.85/1.50      ( k1_funct_1(sK7,sK5(sK7,sK1(k2_relat_1(sK7),sK6))) = sK1(k2_relat_1(sK7),sK6)
% 6.85/1.50      | k2_relat_1(sK7) = k1_relat_1(sK7)
% 6.85/1.50      | k2_relat_1(sK7) = k1_xboole_0 ),
% 6.85/1.50      inference(superposition,[status(thm)],[c_4768,c_29]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_28,negated_conjecture,
% 6.85/1.50      ( k5_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) ),
% 6.85/1.50      inference(cnf_transformation,[],[f90]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_4,plain,
% 6.85/1.50      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = X1
% 6.85/1.50      | sK1(X1,X0) != X0
% 6.85/1.50      | k1_xboole_0 = X1 ),
% 6.85/1.50      inference(cnf_transformation,[],[f86]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_3110,plain,
% 6.85/1.50      ( k5_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) = k2_relat_1(sK7)
% 6.85/1.50      | sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK6)) != k1_funct_1(sK7,sK6)
% 6.85/1.50      | k1_xboole_0 = k2_relat_1(sK7) ),
% 6.85/1.50      inference(instantiation,[status(thm)],[c_4]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_2528,plain,( X0 = X0 ),theory(equality) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_4212,plain,
% 6.85/1.50      ( k2_relat_1(sK7) = k2_relat_1(sK7) ),
% 6.85/1.50      inference(instantiation,[status(thm)],[c_2528]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_2529,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_3555,plain,
% 6.85/1.50      ( X0 != X1 | k2_relat_1(sK7) != X1 | k2_relat_1(sK7) = X0 ),
% 6.85/1.50      inference(instantiation,[status(thm)],[c_2529]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_4148,plain,
% 6.85/1.50      ( X0 != k2_relat_1(sK7)
% 6.85/1.50      | k2_relat_1(sK7) = X0
% 6.85/1.50      | k2_relat_1(sK7) != k2_relat_1(sK7) ),
% 6.85/1.50      inference(instantiation,[status(thm)],[c_3555]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_6269,plain,
% 6.85/1.50      ( k2_relat_1(sK7) != k2_relat_1(sK7)
% 6.85/1.50      | k2_relat_1(sK7) = k1_xboole_0
% 6.85/1.50      | k1_xboole_0 != k2_relat_1(sK7) ),
% 6.85/1.50      inference(instantiation,[status(thm)],[c_4148]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_27,plain,
% 6.85/1.50      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 6.85/1.50      | r2_hidden(sK5(X1,X0),k1_relat_1(X1))
% 6.85/1.50      | ~ v1_funct_1(X1)
% 6.85/1.50      | ~ v1_relat_1(X1) ),
% 6.85/1.50      inference(cnf_transformation,[],[f103]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_336,plain,
% 6.85/1.50      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 6.85/1.50      | r2_hidden(sK5(X1,X0),k1_relat_1(X1))
% 6.85/1.50      | ~ v1_relat_1(X1)
% 6.85/1.50      | sK7 != X1 ),
% 6.85/1.50      inference(resolution_lifted,[status(thm)],[c_27,c_30]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_337,plain,
% 6.85/1.50      ( ~ r2_hidden(X0,k2_relat_1(sK7))
% 6.85/1.50      | r2_hidden(sK5(sK7,X0),k1_relat_1(sK7))
% 6.85/1.50      | ~ v1_relat_1(sK7) ),
% 6.85/1.50      inference(unflattening,[status(thm)],[c_336]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_341,plain,
% 6.85/1.50      ( r2_hidden(sK5(sK7,X0),k1_relat_1(sK7))
% 6.85/1.50      | ~ r2_hidden(X0,k2_relat_1(sK7)) ),
% 6.85/1.50      inference(global_propositional_subsumption,[status(thm)],[c_337,c_31]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_342,plain,
% 6.85/1.50      ( ~ r2_hidden(X0,k2_relat_1(sK7))
% 6.85/1.50      | r2_hidden(sK5(sK7,X0),k1_relat_1(sK7)) ),
% 6.85/1.50      inference(renaming,[status(thm)],[c_341]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_3060,plain,
% 6.85/1.50      ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 6.85/1.50      | r2_hidden(sK5(sK7,X0),k1_relat_1(sK7)) = iProver_top ),
% 6.85/1.50      inference(predicate_to_equality,[status(thm)],[c_342]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_19,plain,
% 6.85/1.50      ( sP0(X0,X1,X2,X3,X4,k5_enumset1(X4,X4,X4,X3,X2,X1,X0)) ),
% 6.85/1.50      inference(cnf_transformation,[],[f99]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_3063,plain,
% 6.85/1.50      ( sP0(X0,X1,X2,X3,X4,k5_enumset1(X4,X4,X4,X3,X2,X1,X0)) = iProver_top ),
% 6.85/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_4059,plain,
% 6.85/1.50      ( sP0(sK6,sK6,sK6,sK6,sK6,k1_relat_1(sK7)) = iProver_top ),
% 6.85/1.50      inference(superposition,[status(thm)],[c_29,c_3063]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_17,plain,
% 6.85/1.50      ( ~ sP0(X0,X1,X2,X3,X4,X5)
% 6.85/1.50      | ~ r2_hidden(X6,X5)
% 6.85/1.50      | X6 = X4
% 6.85/1.50      | X6 = X3
% 6.85/1.50      | X6 = X2
% 6.85/1.50      | X6 = X1
% 6.85/1.50      | X6 = X0 ),
% 6.85/1.50      inference(cnf_transformation,[],[f55]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_3065,plain,
% 6.85/1.50      ( X0 = X1
% 6.85/1.50      | X0 = X2
% 6.85/1.50      | X0 = X3
% 6.85/1.50      | X0 = X4
% 6.85/1.50      | X0 = X5
% 6.85/1.50      | sP0(X5,X4,X3,X2,X1,X6) != iProver_top
% 6.85/1.50      | r2_hidden(X0,X6) != iProver_top ),
% 6.85/1.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_7767,plain,
% 6.85/1.50      ( sK6 = X0 | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
% 6.85/1.50      inference(superposition,[status(thm)],[c_4059,c_3065]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_8026,plain,
% 6.85/1.50      ( sK5(sK7,X0) = sK6 | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 6.85/1.50      inference(superposition,[status(thm)],[c_3060,c_7767]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_8036,plain,
% 6.85/1.50      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(sK7)
% 6.85/1.50      | sK5(sK7,sK1(k2_relat_1(sK7),X0)) = sK6
% 6.85/1.50      | k2_relat_1(sK7) = k1_xboole_0 ),
% 6.85/1.50      inference(superposition,[status(thm)],[c_3077,c_8026]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_13192,plain,
% 6.85/1.50      ( sK5(sK7,sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK6))) = sK6
% 6.85/1.50      | k2_relat_1(sK7) = k1_xboole_0 ),
% 6.85/1.50      inference(superposition,[status(thm)],[c_8036,c_28]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_20059,plain,
% 6.85/1.50      ( k1_funct_1(sK7,sK5(sK7,sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK6)))) = sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK6))
% 6.85/1.50      | k2_relat_1(sK7) = k1_xboole_0 ),
% 6.85/1.50      inference(superposition,[status(thm)],[c_4768,c_28]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_20475,plain,
% 6.85/1.50      ( sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK6)) = k1_funct_1(sK7,sK6)
% 6.85/1.50      | k2_relat_1(sK7) = k1_xboole_0 ),
% 6.85/1.50      inference(superposition,[status(thm)],[c_13192,c_20059]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_20484,plain,
% 6.85/1.50      ( k2_relat_1(sK7) = k1_xboole_0 ),
% 6.85/1.50      inference(global_propositional_subsumption,
% 6.85/1.50                [status(thm)],
% 6.85/1.50                [c_20060,c_28,c_3110,c_4212,c_6269,c_20475]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_16,plain,
% 6.85/1.50      ( ~ sP0(X0,X1,X2,X3,X4,X5) | r2_hidden(X4,X5) ),
% 6.85/1.50      inference(cnf_transformation,[],[f98]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_3066,plain,
% 6.85/1.50      ( sP0(X0,X1,X2,X3,X4,X5) != iProver_top
% 6.85/1.50      | r2_hidden(X4,X5) = iProver_top ),
% 6.85/1.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_4985,plain,
% 6.85/1.50      ( r2_hidden(sK6,k1_relat_1(sK7)) = iProver_top ),
% 6.85/1.50      inference(superposition,[status(thm)],[c_4059,c_3066]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_25,plain,
% 6.85/1.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 6.85/1.50      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 6.85/1.50      | ~ v1_funct_1(X1)
% 6.85/1.50      | ~ v1_relat_1(X1) ),
% 6.85/1.50      inference(cnf_transformation,[],[f101]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_372,plain,
% 6.85/1.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 6.85/1.50      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 6.85/1.50      | ~ v1_relat_1(X1)
% 6.85/1.50      | sK7 != X1 ),
% 6.85/1.50      inference(resolution_lifted,[status(thm)],[c_25,c_30]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_373,plain,
% 6.85/1.50      ( ~ r2_hidden(X0,k1_relat_1(sK7))
% 6.85/1.50      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7))
% 6.85/1.50      | ~ v1_relat_1(sK7) ),
% 6.85/1.50      inference(unflattening,[status(thm)],[c_372]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_377,plain,
% 6.85/1.50      ( r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7))
% 6.85/1.50      | ~ r2_hidden(X0,k1_relat_1(sK7)) ),
% 6.85/1.50      inference(global_propositional_subsumption,[status(thm)],[c_373,c_31]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_378,plain,
% 6.85/1.50      ( ~ r2_hidden(X0,k1_relat_1(sK7))
% 6.85/1.50      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) ),
% 6.85/1.50      inference(renaming,[status(thm)],[c_377]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_3058,plain,
% 6.85/1.50      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 6.85/1.50      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top ),
% 6.85/1.50      inference(predicate_to_equality,[status(thm)],[c_378]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_3320,plain,
% 6.85/1.50      ( k1_funct_1(sK7,sK5(sK7,k1_funct_1(sK7,X0))) = k1_funct_1(sK7,X0)
% 6.85/1.50      | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
% 6.85/1.50      inference(superposition,[status(thm)],[c_3058,c_3059]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_5173,plain,
% 6.85/1.50      ( k1_funct_1(sK7,sK5(sK7,k1_funct_1(sK7,sK6))) = k1_funct_1(sK7,sK6) ),
% 6.85/1.50      inference(superposition,[status(thm)],[c_4985,c_3320]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_5181,plain,
% 6.85/1.50      ( r2_hidden(sK5(sK7,k1_funct_1(sK7,sK6)),k1_relat_1(sK7)) != iProver_top
% 6.85/1.50      | r2_hidden(k1_funct_1(sK7,sK6),k2_relat_1(sK7)) = iProver_top ),
% 6.85/1.50      inference(superposition,[status(thm)],[c_5173,c_3058]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_32,plain,
% 6.85/1.50      ( v1_relat_1(sK7) = iProver_top ),
% 6.85/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_374,plain,
% 6.85/1.50      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 6.85/1.50      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
% 6.85/1.50      | v1_relat_1(sK7) != iProver_top ),
% 6.85/1.50      inference(predicate_to_equality,[status(thm)],[c_373]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_376,plain,
% 6.85/1.50      ( r2_hidden(k1_funct_1(sK7,sK6),k2_relat_1(sK7)) = iProver_top
% 6.85/1.50      | r2_hidden(sK6,k1_relat_1(sK7)) != iProver_top
% 6.85/1.50      | v1_relat_1(sK7) != iProver_top ),
% 6.85/1.50      inference(instantiation,[status(thm)],[c_374]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_12,plain,
% 6.85/1.50      ( ~ sP0(X0,X1,X2,X3,X4,X5) | r2_hidden(X0,X5) ),
% 6.85/1.50      inference(cnf_transformation,[],[f94]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_3167,plain,
% 6.85/1.50      ( ~ sP0(X0,X1,X2,X3,X4,k1_relat_1(sK7)) | r2_hidden(X0,k1_relat_1(sK7)) ),
% 6.85/1.50      inference(instantiation,[status(thm)],[c_12]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_3168,plain,
% 6.85/1.50      ( sP0(X0,X1,X2,X3,X4,k1_relat_1(sK7)) != iProver_top
% 6.85/1.50      | r2_hidden(X0,k1_relat_1(sK7)) = iProver_top ),
% 6.85/1.50      inference(predicate_to_equality,[status(thm)],[c_3167]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_3170,plain,
% 6.85/1.50      ( sP0(sK6,sK6,sK6,sK6,sK6,k1_relat_1(sK7)) != iProver_top
% 6.85/1.50      | r2_hidden(sK6,k1_relat_1(sK7)) = iProver_top ),
% 6.85/1.50      inference(instantiation,[status(thm)],[c_3168]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_5352,plain,
% 6.85/1.50      ( r2_hidden(k1_funct_1(sK7,sK6),k2_relat_1(sK7)) = iProver_top ),
% 6.85/1.50      inference(global_propositional_subsumption,
% 6.85/1.50                [status(thm)],
% 6.85/1.50                [c_5181,c_32,c_376,c_3170,c_4059]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_20541,plain,
% 6.85/1.50      ( r2_hidden(k1_funct_1(sK7,sK6),k1_xboole_0) = iProver_top ),
% 6.85/1.50      inference(demodulation,[status(thm)],[c_20484,c_5352]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_0,plain,
% 6.85/1.50      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 6.85/1.50      inference(cnf_transformation,[],[f92]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_3,plain,
% 6.85/1.50      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 6.85/1.50      inference(cnf_transformation,[],[f52]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_3078,plain,
% 6.85/1.50      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 6.85/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_4204,plain,
% 6.85/1.50      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 6.85/1.50      inference(superposition,[status(thm)],[c_0,c_3078]) ).
% 6.85/1.50  
% 6.85/1.50  cnf(c_21040,plain,
% 6.85/1.50      ( $false ),
% 6.85/1.50      inference(superposition,[status(thm)],[c_20541,c_4204]) ).
% 6.85/1.50  
% 6.85/1.50  
% 6.85/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 6.85/1.50  
% 6.85/1.50  ------                               Statistics
% 6.85/1.50  
% 6.85/1.50  ------ General
% 6.85/1.50  
% 6.85/1.50  abstr_ref_over_cycles:                  0
% 6.85/1.50  abstr_ref_under_cycles:                 0
% 6.85/1.50  gc_basic_clause_elim:                   0
% 6.85/1.50  forced_gc_time:                         0
% 6.85/1.50  parsing_time:                           0.009
% 6.85/1.50  unif_index_cands_time:                  0.
% 6.85/1.50  unif_index_add_time:                    0.
% 6.85/1.50  orderings_time:                         0.
% 6.85/1.50  out_proof_time:                         0.012
% 6.85/1.50  total_time:                             0.863
% 6.85/1.50  num_of_symbols:                         48
% 6.85/1.50  num_of_terms:                           23666
% 6.85/1.50  
% 6.85/1.50  ------ Preprocessing
% 6.85/1.50  
% 6.85/1.50  num_of_splits:                          0
% 6.85/1.50  num_of_split_atoms:                     0
% 6.85/1.50  num_of_reused_defs:                     0
% 6.85/1.50  num_eq_ax_congr_red:                    51
% 6.85/1.50  num_of_sem_filtered_clauses:            1
% 6.85/1.50  num_of_subtypes:                        0
% 6.85/1.50  monotx_restored_types:                  0
% 6.85/1.50  sat_num_of_epr_types:                   0
% 6.85/1.50  sat_num_of_non_cyclic_types:            0
% 6.85/1.50  sat_guarded_non_collapsed_types:        0
% 6.85/1.50  num_pure_diseq_elim:                    0
% 6.85/1.50  simp_replaced_by:                       0
% 6.85/1.50  res_preprocessed:                       147
% 6.85/1.50  prep_upred:                             0
% 6.85/1.50  prep_unflattend:                        92
% 6.85/1.50  smt_new_axioms:                         0
% 6.85/1.50  pred_elim_cands:                        2
% 6.85/1.50  pred_elim:                              2
% 6.85/1.50  pred_elim_cl:                           2
% 6.85/1.50  pred_elim_cycles:                       4
% 6.85/1.50  merged_defs:                            6
% 6.85/1.50  merged_defs_ncl:                        0
% 6.85/1.50  bin_hyper_res:                          6
% 6.85/1.50  prep_cycles:                            4
% 6.85/1.50  pred_elim_time:                         0.042
% 6.85/1.50  splitting_time:                         0.
% 6.85/1.50  sem_filter_time:                        0.
% 6.85/1.50  monotx_time:                            0.
% 6.85/1.50  subtype_inf_time:                       0.
% 6.85/1.50  
% 6.85/1.50  ------ Problem properties
% 6.85/1.50  
% 6.85/1.50  clauses:                                30
% 6.85/1.50  conjectures:                            2
% 6.85/1.50  epr:                                    6
% 6.85/1.50  horn:                                   23
% 6.85/1.50  ground:                                 4
% 6.85/1.50  unary:                                  6
% 6.85/1.50  binary:                                 11
% 6.85/1.50  lits:                                   76
% 6.85/1.50  lits_eq:                                38
% 6.85/1.50  fd_pure:                                0
% 6.85/1.50  fd_pseudo:                              0
% 6.85/1.50  fd_cond:                                4
% 6.85/1.50  fd_pseudo_cond:                         4
% 6.85/1.50  ac_symbols:                             0
% 6.85/1.50  
% 6.85/1.50  ------ Propositional Solver
% 6.85/1.50  
% 6.85/1.50  prop_solver_calls:                      30
% 6.85/1.50  prop_fast_solver_calls:                 1568
% 6.85/1.50  smt_solver_calls:                       0
% 6.85/1.50  smt_fast_solver_calls:                  0
% 6.85/1.50  prop_num_of_clauses:                    7947
% 6.85/1.50  prop_preprocess_simplified:             17170
% 6.85/1.50  prop_fo_subsumed:                       11
% 6.85/1.50  prop_solver_time:                       0.
% 6.85/1.50  smt_solver_time:                        0.
% 6.85/1.50  smt_fast_solver_time:                   0.
% 6.85/1.50  prop_fast_solver_time:                  0.
% 6.85/1.50  prop_unsat_core_time:                   0.
% 6.85/1.50  
% 6.85/1.50  ------ QBF
% 6.85/1.50  
% 6.85/1.50  qbf_q_res:                              0
% 6.85/1.50  qbf_num_tautologies:                    0
% 6.85/1.50  qbf_prep_cycles:                        0
% 6.85/1.50  
% 6.85/1.50  ------ BMC1
% 6.85/1.50  
% 6.85/1.50  bmc1_current_bound:                     -1
% 6.85/1.50  bmc1_last_solved_bound:                 -1
% 6.85/1.50  bmc1_unsat_core_size:                   -1
% 6.85/1.50  bmc1_unsat_core_parents_size:           -1
% 6.85/1.50  bmc1_merge_next_fun:                    0
% 6.85/1.50  bmc1_unsat_core_clauses_time:           0.
% 6.85/1.50  
% 6.85/1.50  ------ Instantiation
% 6.85/1.50  
% 6.85/1.50  inst_num_of_clauses:                    1835
% 6.85/1.50  inst_num_in_passive:                    995
% 6.85/1.50  inst_num_in_active:                     444
% 6.85/1.50  inst_num_in_unprocessed:                397
% 6.85/1.50  inst_num_of_loops:                      780
% 6.85/1.50  inst_num_of_learning_restarts:          0
% 6.85/1.50  inst_num_moves_active_passive:          335
% 6.85/1.50  inst_lit_activity:                      0
% 6.85/1.50  inst_lit_activity_moves:                0
% 6.85/1.50  inst_num_tautologies:                   0
% 6.85/1.50  inst_num_prop_implied:                  0
% 6.85/1.50  inst_num_existing_simplified:           0
% 6.85/1.50  inst_num_eq_res_simplified:             0
% 6.85/1.50  inst_num_child_elim:                    0
% 6.85/1.50  inst_num_of_dismatching_blockings:      1842
% 6.85/1.50  inst_num_of_non_proper_insts:           2015
% 6.85/1.50  inst_num_of_duplicates:                 0
% 6.85/1.50  inst_inst_num_from_inst_to_res:         0
% 6.85/1.50  inst_dismatching_checking_time:         0.
% 6.85/1.50  
% 6.85/1.50  ------ Resolution
% 6.85/1.50  
% 6.85/1.50  res_num_of_clauses:                     0
% 6.85/1.50  res_num_in_passive:                     0
% 6.85/1.50  res_num_in_active:                      0
% 6.85/1.50  res_num_of_loops:                       151
% 6.85/1.50  res_forward_subset_subsumed:            354
% 6.85/1.50  res_backward_subset_subsumed:           2
% 6.85/1.50  res_forward_subsumed:                   0
% 6.85/1.50  res_backward_subsumed:                  0
% 6.85/1.50  res_forward_subsumption_resolution:     0
% 6.85/1.50  res_backward_subsumption_resolution:    0
% 6.85/1.50  res_clause_to_clause_subsumption:       4228
% 6.85/1.50  res_orphan_elimination:                 0
% 6.85/1.50  res_tautology_del:                      41
% 6.85/1.50  res_num_eq_res_simplified:              0
% 6.85/1.50  res_num_sel_changes:                    0
% 6.85/1.50  res_moves_from_active_to_pass:          0
% 6.85/1.50  
% 6.85/1.50  ------ Superposition
% 6.85/1.50  
% 6.85/1.50  sup_time_total:                         0.
% 6.85/1.50  sup_time_generating:                    0.
% 6.85/1.50  sup_time_sim_full:                      0.
% 6.85/1.50  sup_time_sim_immed:                     0.
% 6.85/1.50  
% 6.85/1.50  sup_num_of_clauses:                     675
% 6.85/1.50  sup_num_in_active:                      81
% 6.85/1.50  sup_num_in_passive:                     594
% 6.85/1.50  sup_num_of_loops:                       155
% 6.85/1.50  sup_fw_superposition:                   662
% 6.85/1.50  sup_bw_superposition:                   436
% 6.85/1.50  sup_immediate_simplified:               105
% 6.85/1.50  sup_given_eliminated:                   0
% 6.85/1.50  comparisons_done:                       0
% 6.85/1.50  comparisons_avoided:                    105
% 6.85/1.50  
% 6.85/1.50  ------ Simplifications
% 6.85/1.50  
% 6.85/1.50  
% 6.85/1.50  sim_fw_subset_subsumed:                 59
% 6.85/1.50  sim_bw_subset_subsumed:                 5
% 6.85/1.50  sim_fw_subsumed:                        2
% 6.85/1.50  sim_bw_subsumed:                        3
% 6.85/1.50  sim_fw_subsumption_res:                 0
% 6.85/1.50  sim_bw_subsumption_res:                 0
% 6.85/1.50  sim_tautology_del:                      4
% 6.85/1.50  sim_eq_tautology_del:                   268
% 6.85/1.50  sim_eq_res_simp:                        1
% 6.85/1.50  sim_fw_demodulated:                     8
% 6.85/1.50  sim_bw_demodulated:                     74
% 6.85/1.50  sim_light_normalised:                   33
% 6.85/1.50  sim_joinable_taut:                      0
% 6.85/1.50  sim_joinable_simp:                      0
% 6.85/1.50  sim_ac_normalised:                      0
% 6.85/1.50  sim_smt_subsumption:                    0
% 6.85/1.50  
%------------------------------------------------------------------------------
