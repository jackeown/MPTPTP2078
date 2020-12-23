%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:53 EST 2020

% Result     : Theorem 2.08s
% Output     : Refutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 270 expanded)
%              Number of leaves         :   17 (  81 expanded)
%              Depth                    :   15
%              Number of atoms          :  487 (1561 expanded)
%              Number of equality atoms :  317 (1074 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f787,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f320,f344,f777,f786])).

fof(f786,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f785])).

fof(f785,plain,
    ( $false
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f784,f245])).

fof(f245,plain,(
    r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f33,f34,f126,f92])).

fof(f92,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK2(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK2(X0,X1),X1) )
              & ( ( sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f23,f26,f25,f24])).

fof(f24,plain,(
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

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK2(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X5)) = X5
        & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f126,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(superposition,[],[f96,f74])).

fof(f74,plain,(
    k1_relat_1(sK1) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f35,f72])).

fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f71])).

fof(f71,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f46,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f47,f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f48,f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f46,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f35,plain,(
    k1_tarski(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))
    & k1_tarski(sK0) = k1_relat_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
        & k1_tarski(X0) = k1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))
      & k1_tarski(sK0) = k1_relat_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f96,plain,(
    ! [X4,X2,X0,X5,X3,X1,X9] : r2_hidden(X9,k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X9)) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1,X9] :
      ( r2_hidden(X9,X7)
      | k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X9) != X7 ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] :
      ( r2_hidden(X9,X7)
      | X6 != X9
      | k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) != X7 ) ),
    inference(definition_unfolding,[],[f58,f50])).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] :
      ( r2_hidden(X9,X7)
      | X6 != X9
      | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
        | ( ( ( sK5(X0,X1,X2,X3,X4,X5,X6,X7) != X6
              & sK5(X0,X1,X2,X3,X4,X5,X6,X7) != X5
              & sK5(X0,X1,X2,X3,X4,X5,X6,X7) != X4
              & sK5(X0,X1,X2,X3,X4,X5,X6,X7) != X3
              & sK5(X0,X1,X2,X3,X4,X5,X6,X7) != X2
              & sK5(X0,X1,X2,X3,X4,X5,X6,X7) != X1
              & sK5(X0,X1,X2,X3,X4,X5,X6,X7) != X0 )
            | ~ r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X7) )
          & ( sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X6
            | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X5
            | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X4
            | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X3
            | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X2
            | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X1
            | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X0
            | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X7) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X7)
              | ( X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 ) )
            & ( X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | ~ r2_hidden(X9,X7) ) )
        | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f31])).

fof(f31,plain,(
    ! [X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X8] :
          ( ( ( X6 != X8
              & X5 != X8
              & X4 != X8
              & X3 != X8
              & X2 != X8
              & X1 != X8
              & X0 != X8 )
            | ~ r2_hidden(X8,X7) )
          & ( X6 = X8
            | X5 = X8
            | X4 = X8
            | X3 = X8
            | X2 = X8
            | X1 = X8
            | X0 = X8
            | r2_hidden(X8,X7) ) )
     => ( ( ( sK5(X0,X1,X2,X3,X4,X5,X6,X7) != X6
            & sK5(X0,X1,X2,X3,X4,X5,X6,X7) != X5
            & sK5(X0,X1,X2,X3,X4,X5,X6,X7) != X4
            & sK5(X0,X1,X2,X3,X4,X5,X6,X7) != X3
            & sK5(X0,X1,X2,X3,X4,X5,X6,X7) != X2
            & sK5(X0,X1,X2,X3,X4,X5,X6,X7) != X1
            & sK5(X0,X1,X2,X3,X4,X5,X6,X7) != X0 )
          | ~ r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X7) )
        & ( sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X6
          | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X5
          | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X4
          | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X3
          | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X2
          | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X1
          | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X0
          | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X7) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
        | ? [X8] :
            ( ( ( X6 != X8
                & X5 != X8
                & X4 != X8
                & X3 != X8
                & X2 != X8
                & X1 != X8
                & X0 != X8 )
              | ~ r2_hidden(X8,X7) )
            & ( X6 = X8
              | X5 = X8
              | X4 = X8
              | X3 = X8
              | X2 = X8
              | X1 = X8
              | X0 = X8
              | r2_hidden(X8,X7) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X7)
              | ( X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 ) )
            & ( X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | ~ r2_hidden(X9,X7) ) )
        | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7 ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
        | ? [X8] :
            ( ( ( X6 != X8
                & X5 != X8
                & X4 != X8
                & X3 != X8
                & X2 != X8
                & X1 != X8
                & X0 != X8 )
              | ~ r2_hidden(X8,X7) )
            & ( X6 = X8
              | X5 = X8
              | X4 = X8
              | X3 = X8
              | X2 = X8
              | X1 = X8
              | X0 = X8
              | r2_hidden(X8,X7) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X7)
              | ( X6 != X8
                & X5 != X8
                & X4 != X8
                & X3 != X8
                & X2 != X8
                & X1 != X8
                & X0 != X8 ) )
            & ( X6 = X8
              | X5 = X8
              | X4 = X8
              | X3 = X8
              | X2 = X8
              | X1 = X8
              | X0 = X8
              | ~ r2_hidden(X8,X7) ) )
        | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
        | ? [X8] :
            ( ( ( X6 != X8
                & X5 != X8
                & X4 != X8
                & X3 != X8
                & X2 != X8
                & X1 != X8
                & X0 != X8 )
              | ~ r2_hidden(X8,X7) )
            & ( X6 = X8
              | X5 = X8
              | X4 = X8
              | X3 = X8
              | X2 = X8
              | X1 = X8
              | X0 = X8
              | r2_hidden(X8,X7) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X7)
              | ( X6 != X8
                & X5 != X8
                & X4 != X8
                & X3 != X8
                & X2 != X8
                & X1 != X8
                & X0 != X8 ) )
            & ( X6 = X8
              | X5 = X8
              | X4 = X8
              | X3 = X8
              | X2 = X8
              | X1 = X8
              | X0 = X8
              | ~ r2_hidden(X8,X7) ) )
        | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ( X6 = X8
            | X5 = X8
            | X4 = X8
            | X3 = X8
            | X2 = X8
            | X1 = X8
            | X0 = X8 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ~ ( X6 != X8
              & X5 != X8
              & X4 != X8
              & X3 != X8
              & X2 != X8
              & X1 != X8
              & X0 != X8 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_enumset1)).

fof(f34,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f33,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f784,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | spl6_1
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f315,f318])).

fof(f318,plain,
    ( k1_funct_1(sK1,sK0) = sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f317])).

fof(f317,plain,
    ( spl6_2
  <=> k1_funct_1(sK1,sK0) = sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f315,plain,
    ( ~ r2_hidden(sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f313])).

fof(f313,plain,
    ( spl6_1
  <=> r2_hidden(sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f777,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_contradiction_clause,[],[f776])).

fof(f776,plain,
    ( $false
    | ~ spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f775,f319])).

fof(f319,plain,
    ( k1_funct_1(sK1,sK0) != sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f317])).

fof(f775,plain,
    ( k1_funct_1(sK1,sK0) = sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f380,f752])).

fof(f752,plain,
    ( sK0 = sK4(sK1,sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1)))
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f379,f134])).

fof(f134,plain,(
    ! [X8] :
      ( ~ r2_hidden(X8,k1_relat_1(sK1))
      | sK0 = X8 ) ),
    inference(duplicate_literal_removal,[],[f133])).

fof(f133,plain,(
    ! [X8] :
      ( ~ r2_hidden(X8,k1_relat_1(sK1))
      | sK0 = X8
      | sK0 = X8
      | sK0 = X8
      | sK0 = X8
      | sK0 = X8
      | sK0 = X8
      | sK0 = X8 ) ),
    inference(superposition,[],[f109,f74])).

fof(f109,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1,X9] :
      ( X6 = X9
      | X5 = X9
      | X4 = X9
      | X3 = X9
      | X2 = X9
      | X1 = X9
      | X0 = X9
      | ~ r2_hidden(X9,k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] :
      ( X6 = X9
      | X5 = X9
      | X4 = X9
      | X3 = X9
      | X2 = X9
      | X1 = X9
      | X0 = X9
      | ~ r2_hidden(X9,X7)
      | k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) != X7 ) ),
    inference(definition_unfolding,[],[f51,f50])).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] :
      ( X6 = X9
      | X5 = X9
      | X4 = X9
      | X3 = X9
      | X2 = X9
      | X1 = X9
      | X0 = X9
      | ~ r2_hidden(X9,X7)
      | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f379,plain,
    ( r2_hidden(sK4(sK1,sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1))),k1_relat_1(sK1))
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f33,f34,f314,f94])).

fof(f94,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f314,plain,
    ( r2_hidden(sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f313])).

fof(f380,plain,
    ( sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1)) = k1_funct_1(sK1,sK4(sK1,sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1))))
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f33,f34,f314,f93])).

fof(f93,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f344,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f335,f317,f313])).

fof(f335,plain,
    ( k1_funct_1(sK1,sK0) = sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | r2_hidden(sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1)) ),
    inference(equality_resolution,[],[f243])).

fof(f243,plain,(
    ! [X7] :
      ( k2_relat_1(sK1) != X7
      | k1_funct_1(sK1,sK0) = sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),X7)
      | r2_hidden(sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),X7),X7) ) ),
    inference(duplicate_literal_removal,[],[f242])).

fof(f242,plain,(
    ! [X7] :
      ( k2_relat_1(sK1) != X7
      | k1_funct_1(sK1,sK0) = sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),X7)
      | k1_funct_1(sK1,sK0) = sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),X7)
      | k1_funct_1(sK1,sK0) = sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),X7)
      | k1_funct_1(sK1,sK0) = sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),X7)
      | k1_funct_1(sK1,sK0) = sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),X7)
      | k1_funct_1(sK1,sK0) = sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),X7)
      | k1_funct_1(sK1,sK0) = sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),X7)
      | r2_hidden(sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),X7),X7) ) ),
    inference(superposition,[],[f73,f82])).

fof(f82,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = X7
      | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X6
      | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X5
      | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X4
      | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X3
      | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X2
      | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X1
      | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X0
      | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X7) ) ),
    inference(definition_unfolding,[],[f59,f50])).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
      | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X6
      | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X5
      | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X4
      | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X3
      | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X2
      | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X1
      | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X0
      | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X7) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f73,plain,(
    k2_relat_1(sK1) != k6_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    inference(definition_unfolding,[],[f36,f72])).

fof(f36,plain,(
    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f320,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f305,f317,f313])).

fof(f305,plain,
    ( k1_funct_1(sK1,sK0) != sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | ~ r2_hidden(sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1)) ),
    inference(equality_resolution,[],[f235])).

fof(f235,plain,(
    ! [X0] :
      ( k2_relat_1(sK1) != X0
      | k1_funct_1(sK1,sK0) != sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),X0)
      | ~ r2_hidden(sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),X0),X0) ) ),
    inference(superposition,[],[f73,f75])).

fof(f75,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = X7
      | sK5(X0,X1,X2,X3,X4,X5,X6,X7) != X6
      | ~ r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X7) ) ),
    inference(definition_unfolding,[],[f66,f50])).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
      | sK5(X0,X1,X2,X3,X4,X5,X6,X7) != X6
      | ~ r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X7) ) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:21:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (521)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (510)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (487)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (490)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (509)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (486)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (493)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (483)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (485)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (484)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (488)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (522)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (527)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (518)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (523)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (525)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (517)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (516)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (511)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (526)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (519)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (491)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (528)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.56  % (492)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.56  % (508)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (524)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.56  % (494)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (520)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  % (507)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (515)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 2.08/0.64  % (525)Refutation found. Thanks to Tanya!
% 2.08/0.64  % SZS status Theorem for theBenchmark
% 2.08/0.64  % SZS output start Proof for theBenchmark
% 2.08/0.64  fof(f787,plain,(
% 2.08/0.64    $false),
% 2.08/0.64    inference(avatar_sat_refutation,[],[f320,f344,f777,f786])).
% 2.08/0.64  fof(f786,plain,(
% 2.08/0.64    spl6_1 | ~spl6_2),
% 2.08/0.64    inference(avatar_contradiction_clause,[],[f785])).
% 2.08/0.64  fof(f785,plain,(
% 2.08/0.64    $false | (spl6_1 | ~spl6_2)),
% 2.08/0.64    inference(subsumption_resolution,[],[f784,f245])).
% 2.08/0.64  fof(f245,plain,(
% 2.08/0.64    r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))),
% 2.08/0.64    inference(unit_resulting_resolution,[],[f33,f34,f126,f92])).
% 2.08/0.64  fof(f92,plain,(
% 2.08/0.64    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.08/0.64    inference(equality_resolution,[],[f91])).
% 2.08/0.64  fof(f91,plain,(
% 2.08/0.64    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.08/0.64    inference(equality_resolution,[],[f40])).
% 2.08/0.64  fof(f40,plain,(
% 2.08/0.64    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.08/0.64    inference(cnf_transformation,[],[f27])).
% 2.08/0.64  fof(f27,plain,(
% 2.08/0.64    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & ((sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.08/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f23,f26,f25,f24])).
% 2.08/0.64  fof(f24,plain,(
% 2.08/0.64    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK2(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1))))),
% 2.08/0.64    introduced(choice_axiom,[])).
% 2.08/0.64  fof(f25,plain,(
% 2.08/0.64    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK2(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))))),
% 2.08/0.64    introduced(choice_axiom,[])).
% 2.08/0.64  fof(f26,plain,(
% 2.08/0.64    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))))),
% 2.08/0.64    introduced(choice_axiom,[])).
% 2.08/0.64  fof(f23,plain,(
% 2.08/0.64    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.08/0.64    inference(rectify,[],[f22])).
% 2.08/0.64  fof(f22,plain,(
% 2.08/0.64    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.08/0.64    inference(nnf_transformation,[],[f16])).
% 2.08/0.64  fof(f16,plain,(
% 2.08/0.64    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.08/0.64    inference(flattening,[],[f15])).
% 2.08/0.64  fof(f15,plain,(
% 2.08/0.64    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.08/0.64    inference(ennf_transformation,[],[f9])).
% 2.08/0.64  fof(f9,axiom,(
% 2.08/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 2.08/0.64  fof(f126,plain,(
% 2.08/0.64    r2_hidden(sK0,k1_relat_1(sK1))),
% 2.08/0.64    inference(superposition,[],[f96,f74])).
% 2.08/0.64  fof(f74,plain,(
% 2.08/0.64    k1_relat_1(sK1) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.08/0.64    inference(definition_unfolding,[],[f35,f72])).
% 2.08/0.64  fof(f72,plain,(
% 2.08/0.64    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.08/0.64    inference(definition_unfolding,[],[f37,f71])).
% 2.08/0.64  fof(f71,plain,(
% 2.08/0.64    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.08/0.64    inference(definition_unfolding,[],[f44,f70])).
% 2.08/0.64  fof(f70,plain,(
% 2.08/0.64    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.08/0.64    inference(definition_unfolding,[],[f46,f69])).
% 2.08/0.64  fof(f69,plain,(
% 2.08/0.64    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.08/0.64    inference(definition_unfolding,[],[f47,f68])).
% 2.08/0.64  fof(f68,plain,(
% 2.08/0.64    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.08/0.64    inference(definition_unfolding,[],[f48,f67])).
% 2.08/0.64  fof(f67,plain,(
% 2.08/0.64    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.08/0.64    inference(definition_unfolding,[],[f49,f50])).
% 2.08/0.64  fof(f50,plain,(
% 2.08/0.64    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.08/0.64    inference(cnf_transformation,[],[f7])).
% 2.08/0.64  fof(f7,axiom,(
% 2.08/0.64    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 2.08/0.64  fof(f49,plain,(
% 2.08/0.64    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.08/0.64    inference(cnf_transformation,[],[f6])).
% 2.08/0.64  fof(f6,axiom,(
% 2.08/0.64    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 2.08/0.64  fof(f48,plain,(
% 2.08/0.64    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.08/0.64    inference(cnf_transformation,[],[f5])).
% 2.08/0.64  fof(f5,axiom,(
% 2.08/0.64    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 2.08/0.64  fof(f47,plain,(
% 2.08/0.64    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.08/0.64    inference(cnf_transformation,[],[f4])).
% 2.08/0.64  fof(f4,axiom,(
% 2.08/0.64    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 2.08/0.64  fof(f46,plain,(
% 2.08/0.64    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.08/0.64    inference(cnf_transformation,[],[f3])).
% 2.08/0.64  fof(f3,axiom,(
% 2.08/0.64    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.08/0.64  fof(f44,plain,(
% 2.08/0.64    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.08/0.64    inference(cnf_transformation,[],[f2])).
% 2.08/0.64  fof(f2,axiom,(
% 2.08/0.64    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.08/0.64  fof(f37,plain,(
% 2.08/0.64    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.08/0.64    inference(cnf_transformation,[],[f1])).
% 2.08/0.64  fof(f1,axiom,(
% 2.08/0.64    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.08/0.64  fof(f35,plain,(
% 2.08/0.64    k1_tarski(sK0) = k1_relat_1(sK1)),
% 2.08/0.64    inference(cnf_transformation,[],[f21])).
% 2.08/0.64  fof(f21,plain,(
% 2.08/0.64    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) & k1_tarski(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 2.08/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f20])).
% 2.08/0.64  fof(f20,plain,(
% 2.08/0.64    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) & k1_tarski(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 2.08/0.64    introduced(choice_axiom,[])).
% 2.08/0.64  fof(f14,plain,(
% 2.08/0.64    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.08/0.64    inference(flattening,[],[f13])).
% 2.08/0.64  fof(f13,plain,(
% 2.08/0.64    ? [X0,X1] : ((k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 2.08/0.64    inference(ennf_transformation,[],[f12])).
% 2.08/0.64  fof(f12,negated_conjecture,(
% 2.08/0.64    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 2.08/0.64    inference(negated_conjecture,[],[f11])).
% 2.08/0.64  fof(f11,conjecture,(
% 2.08/0.64    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 2.08/0.64  fof(f96,plain,(
% 2.08/0.64    ( ! [X4,X2,X0,X5,X3,X1,X9] : (r2_hidden(X9,k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X9))) )),
% 2.08/0.64    inference(equality_resolution,[],[f95])).
% 2.08/0.64  fof(f95,plain,(
% 2.08/0.64    ( ! [X4,X2,X0,X7,X5,X3,X1,X9] : (r2_hidden(X9,X7) | k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X9) != X7) )),
% 2.08/0.64    inference(equality_resolution,[],[f83])).
% 2.08/0.64  fof(f83,plain,(
% 2.08/0.64    ( ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] : (r2_hidden(X9,X7) | X6 != X9 | k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) != X7) )),
% 2.08/0.64    inference(definition_unfolding,[],[f58,f50])).
% 2.08/0.64  fof(f58,plain,(
% 2.08/0.64    ( ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] : (r2_hidden(X9,X7) | X6 != X9 | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7) )),
% 2.08/0.64    inference(cnf_transformation,[],[f32])).
% 2.08/0.64  fof(f32,plain,(
% 2.08/0.64    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 | (((sK5(X0,X1,X2,X3,X4,X5,X6,X7) != X6 & sK5(X0,X1,X2,X3,X4,X5,X6,X7) != X5 & sK5(X0,X1,X2,X3,X4,X5,X6,X7) != X4 & sK5(X0,X1,X2,X3,X4,X5,X6,X7) != X3 & sK5(X0,X1,X2,X3,X4,X5,X6,X7) != X2 & sK5(X0,X1,X2,X3,X4,X5,X6,X7) != X1 & sK5(X0,X1,X2,X3,X4,X5,X6,X7) != X0) | ~r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X7)) & (sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X6 | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X5 | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X4 | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X3 | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X2 | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X1 | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X0 | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X7)))) & (! [X9] : ((r2_hidden(X9,X7) | (X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & (X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~r2_hidden(X9,X7))) | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7))),
% 2.08/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f31])).
% 2.08/0.64  fof(f31,plain,(
% 2.08/0.64    ! [X7,X6,X5,X4,X3,X2,X1,X0] : (? [X8] : (((X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8) | ~r2_hidden(X8,X7)) & (X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8 | r2_hidden(X8,X7))) => (((sK5(X0,X1,X2,X3,X4,X5,X6,X7) != X6 & sK5(X0,X1,X2,X3,X4,X5,X6,X7) != X5 & sK5(X0,X1,X2,X3,X4,X5,X6,X7) != X4 & sK5(X0,X1,X2,X3,X4,X5,X6,X7) != X3 & sK5(X0,X1,X2,X3,X4,X5,X6,X7) != X2 & sK5(X0,X1,X2,X3,X4,X5,X6,X7) != X1 & sK5(X0,X1,X2,X3,X4,X5,X6,X7) != X0) | ~r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X7)) & (sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X6 | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X5 | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X4 | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X3 | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X2 | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X1 | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X0 | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X7))))),
% 2.08/0.64    introduced(choice_axiom,[])).
% 2.08/0.64  fof(f30,plain,(
% 2.08/0.64    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 | ? [X8] : (((X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8) | ~r2_hidden(X8,X7)) & (X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8 | r2_hidden(X8,X7)))) & (! [X9] : ((r2_hidden(X9,X7) | (X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & (X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~r2_hidden(X9,X7))) | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7))),
% 2.08/0.64    inference(rectify,[],[f29])).
% 2.08/0.64  fof(f29,plain,(
% 2.08/0.64    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 | ? [X8] : (((X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8) | ~r2_hidden(X8,X7)) & (X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8 | r2_hidden(X8,X7)))) & (! [X8] : ((r2_hidden(X8,X7) | (X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8)) & (X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8 | ~r2_hidden(X8,X7))) | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7))),
% 2.08/0.64    inference(flattening,[],[f28])).
% 2.08/0.64  fof(f28,plain,(
% 2.08/0.64    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 | ? [X8] : (((X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8) | ~r2_hidden(X8,X7)) & ((X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8) | r2_hidden(X8,X7)))) & (! [X8] : ((r2_hidden(X8,X7) | (X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8)) & ((X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8) | ~r2_hidden(X8,X7))) | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7))),
% 2.08/0.64    inference(nnf_transformation,[],[f19])).
% 2.08/0.64  fof(f19,plain,(
% 2.08/0.64    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 <=> ! [X8] : (r2_hidden(X8,X7) <=> (X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8)))),
% 2.08/0.64    inference(ennf_transformation,[],[f8])).
% 2.08/0.64  fof(f8,axiom,(
% 2.08/0.64    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 <=> ! [X8] : (r2_hidden(X8,X7) <=> ~(X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8)))),
% 2.08/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_enumset1)).
% 2.08/0.64  fof(f34,plain,(
% 2.08/0.64    v1_funct_1(sK1)),
% 2.08/0.64    inference(cnf_transformation,[],[f21])).
% 2.08/0.64  fof(f33,plain,(
% 2.08/0.64    v1_relat_1(sK1)),
% 2.08/0.64    inference(cnf_transformation,[],[f21])).
% 2.08/0.64  fof(f784,plain,(
% 2.08/0.64    ~r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) | (spl6_1 | ~spl6_2)),
% 2.08/0.64    inference(forward_demodulation,[],[f315,f318])).
% 2.08/0.64  fof(f318,plain,(
% 2.08/0.64    k1_funct_1(sK1,sK0) = sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1)) | ~spl6_2),
% 2.08/0.64    inference(avatar_component_clause,[],[f317])).
% 2.08/0.64  fof(f317,plain,(
% 2.08/0.64    spl6_2 <=> k1_funct_1(sK1,sK0) = sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1))),
% 2.08/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.08/0.64  fof(f315,plain,(
% 2.08/0.64    ~r2_hidden(sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1)) | spl6_1),
% 2.08/0.64    inference(avatar_component_clause,[],[f313])).
% 2.08/0.64  fof(f313,plain,(
% 2.08/0.64    spl6_1 <=> r2_hidden(sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1))),
% 2.08/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.08/0.64  fof(f777,plain,(
% 2.08/0.64    ~spl6_1 | spl6_2),
% 2.08/0.64    inference(avatar_contradiction_clause,[],[f776])).
% 2.08/0.64  fof(f776,plain,(
% 2.08/0.64    $false | (~spl6_1 | spl6_2)),
% 2.08/0.64    inference(subsumption_resolution,[],[f775,f319])).
% 2.08/0.64  fof(f319,plain,(
% 2.08/0.64    k1_funct_1(sK1,sK0) != sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1)) | spl6_2),
% 2.08/0.64    inference(avatar_component_clause,[],[f317])).
% 2.08/0.64  fof(f775,plain,(
% 2.08/0.64    k1_funct_1(sK1,sK0) = sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1)) | ~spl6_1),
% 2.08/0.64    inference(backward_demodulation,[],[f380,f752])).
% 2.08/0.64  fof(f752,plain,(
% 2.08/0.64    sK0 = sK4(sK1,sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1))) | ~spl6_1),
% 2.08/0.64    inference(unit_resulting_resolution,[],[f379,f134])).
% 2.08/0.64  fof(f134,plain,(
% 2.08/0.64    ( ! [X8] : (~r2_hidden(X8,k1_relat_1(sK1)) | sK0 = X8) )),
% 2.08/0.64    inference(duplicate_literal_removal,[],[f133])).
% 2.08/0.64  fof(f133,plain,(
% 2.08/0.64    ( ! [X8] : (~r2_hidden(X8,k1_relat_1(sK1)) | sK0 = X8 | sK0 = X8 | sK0 = X8 | sK0 = X8 | sK0 = X8 | sK0 = X8 | sK0 = X8) )),
% 2.08/0.64    inference(superposition,[],[f109,f74])).
% 2.08/0.64  fof(f109,plain,(
% 2.08/0.64    ( ! [X6,X4,X2,X0,X5,X3,X1,X9] : (X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~r2_hidden(X9,k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6))) )),
% 2.08/0.64    inference(equality_resolution,[],[f90])).
% 2.08/0.64  fof(f90,plain,(
% 2.08/0.64    ( ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] : (X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~r2_hidden(X9,X7) | k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) != X7) )),
% 2.08/0.64    inference(definition_unfolding,[],[f51,f50])).
% 2.08/0.64  fof(f51,plain,(
% 2.08/0.64    ( ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] : (X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~r2_hidden(X9,X7) | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7) )),
% 2.08/0.64    inference(cnf_transformation,[],[f32])).
% 2.08/0.64  fof(f379,plain,(
% 2.08/0.64    r2_hidden(sK4(sK1,sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1))),k1_relat_1(sK1)) | ~spl6_1),
% 2.08/0.64    inference(unit_resulting_resolution,[],[f33,f34,f314,f94])).
% 2.08/0.64  fof(f94,plain,(
% 2.08/0.64    ( ! [X0,X5] : (r2_hidden(sK4(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.08/0.64    inference(equality_resolution,[],[f38])).
% 2.08/0.64  fof(f38,plain,(
% 2.08/0.64    ( ! [X0,X5,X1] : (r2_hidden(sK4(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.08/0.64    inference(cnf_transformation,[],[f27])).
% 2.08/0.64  fof(f314,plain,(
% 2.08/0.64    r2_hidden(sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1)) | ~spl6_1),
% 2.08/0.64    inference(avatar_component_clause,[],[f313])).
% 2.08/0.64  fof(f380,plain,(
% 2.08/0.64    sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1)) = k1_funct_1(sK1,sK4(sK1,sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1)))) | ~spl6_1),
% 2.08/0.64    inference(unit_resulting_resolution,[],[f33,f34,f314,f93])).
% 2.08/0.64  fof(f93,plain,(
% 2.08/0.64    ( ! [X0,X5] : (k1_funct_1(X0,sK4(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.08/0.64    inference(equality_resolution,[],[f39])).
% 2.08/0.64  fof(f39,plain,(
% 2.08/0.64    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK4(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.08/0.64    inference(cnf_transformation,[],[f27])).
% 2.08/0.64  fof(f344,plain,(
% 2.08/0.64    spl6_1 | spl6_2),
% 2.08/0.64    inference(avatar_split_clause,[],[f335,f317,f313])).
% 2.08/0.64  fof(f335,plain,(
% 2.08/0.64    k1_funct_1(sK1,sK0) = sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1)) | r2_hidden(sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1))),
% 2.08/0.64    inference(equality_resolution,[],[f243])).
% 2.08/0.64  fof(f243,plain,(
% 2.08/0.64    ( ! [X7] : (k2_relat_1(sK1) != X7 | k1_funct_1(sK1,sK0) = sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),X7) | r2_hidden(sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),X7),X7)) )),
% 2.08/0.64    inference(duplicate_literal_removal,[],[f242])).
% 2.08/0.64  fof(f242,plain,(
% 2.08/0.64    ( ! [X7] : (k2_relat_1(sK1) != X7 | k1_funct_1(sK1,sK0) = sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),X7) | k1_funct_1(sK1,sK0) = sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),X7) | k1_funct_1(sK1,sK0) = sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),X7) | k1_funct_1(sK1,sK0) = sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),X7) | k1_funct_1(sK1,sK0) = sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),X7) | k1_funct_1(sK1,sK0) = sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),X7) | k1_funct_1(sK1,sK0) = sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),X7) | r2_hidden(sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),X7),X7)) )),
% 2.08/0.64    inference(superposition,[],[f73,f82])).
% 2.08/0.64  fof(f82,plain,(
% 2.08/0.64    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = X7 | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X6 | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X5 | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X4 | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X3 | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X2 | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X1 | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X0 | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X7)) )),
% 2.08/0.64    inference(definition_unfolding,[],[f59,f50])).
% 2.08/0.64  fof(f59,plain,(
% 2.08/0.64    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X6 | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X5 | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X4 | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X3 | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X2 | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X1 | sK5(X0,X1,X2,X3,X4,X5,X6,X7) = X0 | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X7)) )),
% 2.08/0.64    inference(cnf_transformation,[],[f32])).
% 2.08/0.64  fof(f73,plain,(
% 2.08/0.64    k2_relat_1(sK1) != k6_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 2.08/0.64    inference(definition_unfolding,[],[f36,f72])).
% 2.08/0.64  fof(f36,plain,(
% 2.08/0.64    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))),
% 2.08/0.64    inference(cnf_transformation,[],[f21])).
% 2.08/0.64  fof(f320,plain,(
% 2.08/0.64    ~spl6_1 | ~spl6_2),
% 2.08/0.64    inference(avatar_split_clause,[],[f305,f317,f313])).
% 2.08/0.64  fof(f305,plain,(
% 2.08/0.64    k1_funct_1(sK1,sK0) != sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1)) | ~r2_hidden(sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1))),
% 2.08/0.64    inference(equality_resolution,[],[f235])).
% 2.08/0.64  fof(f235,plain,(
% 2.08/0.64    ( ! [X0] : (k2_relat_1(sK1) != X0 | k1_funct_1(sK1,sK0) != sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),X0) | ~r2_hidden(sK5(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),X0),X0)) )),
% 2.08/0.64    inference(superposition,[],[f73,f75])).
% 2.08/0.64  fof(f75,plain,(
% 2.08/0.64    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = X7 | sK5(X0,X1,X2,X3,X4,X5,X6,X7) != X6 | ~r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X7)) )),
% 2.08/0.64    inference(definition_unfolding,[],[f66,f50])).
% 2.08/0.64  fof(f66,plain,(
% 2.08/0.64    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 | sK5(X0,X1,X2,X3,X4,X5,X6,X7) != X6 | ~r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X7)) )),
% 2.08/0.64    inference(cnf_transformation,[],[f32])).
% 2.08/0.64  % SZS output end Proof for theBenchmark
% 2.08/0.64  % (525)------------------------------
% 2.08/0.64  % (525)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.64  % (525)Termination reason: Refutation
% 2.08/0.64  
% 2.08/0.64  % (525)Memory used [KB]: 11129
% 2.08/0.64  % (525)Time elapsed: 0.175 s
% 2.08/0.64  % (525)------------------------------
% 2.08/0.64  % (525)------------------------------
% 2.08/0.64  % (482)Success in time 0.276 s
%------------------------------------------------------------------------------
