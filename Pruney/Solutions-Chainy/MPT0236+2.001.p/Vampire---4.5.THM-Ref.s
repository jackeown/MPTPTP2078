%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:28 EST 2020

% Result     : Theorem 2.51s
% Output     : Refutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 154 expanded)
%              Number of leaves         :   13 (  47 expanded)
%              Depth                    :   20
%              Number of atoms          :  283 ( 853 expanded)
%              Number of equality atoms :  106 ( 305 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1339,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1336,f94])).

fof(f94,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(superposition,[],[f88,f69])).

fof(f69,plain,(
    ! [X0] : k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0)) ),
    inference(definition_unfolding,[],[f40,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f40,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f88,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_xboole_0(k1_tarski(X4),k1_tarski(X1))) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_xboole_0(k1_tarski(X4),k1_tarski(X1)) != X2 ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) != X2 ) ),
    inference(definition_unfolding,[],[f64,f42])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK6(X0,X1,X2) != X1
              & sK6(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( sK6(X0,X1,X2) = X1
            | sK6(X0,X1,X2) = X0
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK6(X0,X1,X2) != X1
            & sK6(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( sK6(X0,X1,X2) = X1
          | sK6(X0,X1,X2) = X0
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f1336,plain,(
    ~ r2_hidden(sK0,k1_tarski(sK0)) ),
    inference(resolution,[],[f1230,f1215])).

fof(f1215,plain,(
    r2_hidden(sK2(k1_tarski(sK0),sK0),sK0) ),
    inference(trivial_inequality_removal,[],[f1200])).

fof(f1200,plain,
    ( sK0 != sK0
    | r2_hidden(sK2(k1_tarski(sK0),sK0),sK0) ),
    inference(superposition,[],[f39,f1197])).

fof(f1197,plain,(
    ! [X0] :
      ( k3_tarski(k1_tarski(X0)) = X0
      | r2_hidden(sK2(k1_tarski(X0),X0),X0) ) ),
    inference(factoring,[],[f799])).

fof(f799,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(k1_tarski(X0),X1),X1)
      | k3_tarski(k1_tarski(X0)) = X1
      | r2_hidden(sK2(k1_tarski(X0),X1),X0) ) ),
    inference(duplicate_literal_removal,[],[f796])).

fof(f796,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(k1_tarski(X0),X1),X0)
      | k3_tarski(k1_tarski(X0)) = X1
      | r2_hidden(sK2(k1_tarski(X0),X1),X1)
      | r2_hidden(sK2(k1_tarski(X0),X1),X1)
      | k3_tarski(k1_tarski(X0)) = X1 ) ),
    inference(superposition,[],[f52,f168])).

fof(f168,plain,(
    ! [X15,X16] :
      ( sK3(k1_tarski(X15),X16) = X15
      | r2_hidden(sK2(k1_tarski(X15),X16),X16)
      | k3_tarski(k1_tarski(X15)) = X16 ) ),
    inference(resolution,[],[f53,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_tarski(X1))
      | X0 = X1 ) ),
    inference(resolution,[],[f104,f94])).

fof(f104,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X6,k1_tarski(X4))
      | ~ r2_hidden(X6,k1_tarski(X5))
      | X4 = X5 ) ),
    inference(superposition,[],[f83,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f83,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | k3_tarski(X0) = X1
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK2(X0,X1),X3) )
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( ( r2_hidden(sK3(X0,X1),X0)
              & r2_hidden(sK2(X0,X1),sK3(X0,X1)) )
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK4(X0,X5),X0)
                & r2_hidden(X5,sK4(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f23,f26,f25,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK2(X0,X1),X3) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK2(X0,X1),X4) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(sK2(X0,X1),X4) )
     => ( r2_hidden(sK3(X0,X1),X0)
        & r2_hidden(sK2(X0,X1),sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK4(X0,X5),X0)
        & r2_hidden(X5,sK4(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),sK3(X0,X1))
      | k3_tarski(X0) = X1
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f39,plain,(
    sK0 != k3_tarski(k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    sK0 != k3_tarski(k1_tarski(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f14])).

fof(f14,plain,
    ( ? [X0] : k3_tarski(k1_tarski(X0)) != X0
   => sK0 != k3_tarski(k1_tarski(sK0)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] : k3_tarski(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(f1230,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(k1_tarski(sK0),sK0),X0)
      | ~ r2_hidden(X0,k1_tarski(sK0)) ) ),
    inference(subsumption_resolution,[],[f1216,f39])).

fof(f1216,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK0))
      | ~ r2_hidden(sK2(k1_tarski(sK0),sK0),X0)
      | sK0 = k3_tarski(k1_tarski(sK0)) ) ),
    inference(resolution,[],[f1215,f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | ~ r2_hidden(X3,X0)
      | ~ r2_hidden(sK2(X0,X1),X3)
      | k3_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:08:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.52  % (8540)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (8538)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (8547)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (8539)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (8541)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (8554)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (8537)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (8564)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (8546)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (8546)Refutation not found, incomplete strategy% (8546)------------------------------
% 0.21/0.54  % (8546)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (8546)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (8546)Memory used [KB]: 10618
% 0.21/0.54  % (8546)Time elapsed: 0.136 s
% 0.21/0.54  % (8546)------------------------------
% 0.21/0.54  % (8546)------------------------------
% 0.21/0.54  % (8565)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (8548)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (8552)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (8545)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (8558)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (8544)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (8555)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (8543)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (8538)Refutation not found, incomplete strategy% (8538)------------------------------
% 0.21/0.55  % (8538)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (8538)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (8538)Memory used [KB]: 10746
% 0.21/0.55  % (8538)Time elapsed: 0.132 s
% 0.21/0.55  % (8538)------------------------------
% 0.21/0.55  % (8538)------------------------------
% 0.21/0.55  % (8550)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (8557)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (8563)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (8556)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (8557)Refutation not found, incomplete strategy% (8557)------------------------------
% 0.21/0.55  % (8557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (8557)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (8557)Memory used [KB]: 1663
% 0.21/0.55  % (8557)Time elapsed: 0.147 s
% 0.21/0.55  % (8557)------------------------------
% 0.21/0.55  % (8557)------------------------------
% 0.21/0.55  % (8560)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (8562)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (8556)Refutation not found, incomplete strategy% (8556)------------------------------
% 0.21/0.55  % (8556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (8556)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (8556)Memory used [KB]: 10746
% 0.21/0.55  % (8556)Time elapsed: 0.151 s
% 0.21/0.55  % (8556)------------------------------
% 0.21/0.55  % (8556)------------------------------
% 0.21/0.55  % (8561)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (8544)Refutation not found, incomplete strategy% (8544)------------------------------
% 0.21/0.55  % (8544)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (8544)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (8544)Memory used [KB]: 10618
% 0.21/0.55  % (8544)Time elapsed: 0.104 s
% 0.21/0.55  % (8544)------------------------------
% 0.21/0.55  % (8544)------------------------------
% 0.21/0.55  % (8558)Refutation not found, incomplete strategy% (8558)------------------------------
% 0.21/0.55  % (8558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (8558)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (8558)Memory used [KB]: 10746
% 0.21/0.55  % (8558)Time elapsed: 0.105 s
% 0.21/0.55  % (8558)------------------------------
% 0.21/0.55  % (8558)------------------------------
% 0.21/0.56  % (8549)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (8559)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.56  % (8553)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.56  % (8551)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.56  % (8536)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.54/0.58  % (8542)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 2.19/0.67  % (8570)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.19/0.69  % (8568)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.19/0.69  % (8569)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.19/0.70  % (8571)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.51/0.71  % (8567)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.51/0.73  % (8539)Refutation found. Thanks to Tanya!
% 2.51/0.73  % SZS status Theorem for theBenchmark
% 2.51/0.73  % SZS output start Proof for theBenchmark
% 2.51/0.73  fof(f1339,plain,(
% 2.51/0.73    $false),
% 2.51/0.73    inference(subsumption_resolution,[],[f1336,f94])).
% 2.51/0.73  fof(f94,plain,(
% 2.51/0.73    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 2.51/0.73    inference(superposition,[],[f88,f69])).
% 2.51/0.73  fof(f69,plain,(
% 2.51/0.73    ( ! [X0] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0))) )),
% 2.51/0.73    inference(definition_unfolding,[],[f40,f42])).
% 2.51/0.73  fof(f42,plain,(
% 2.51/0.73    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 2.51/0.73    inference(cnf_transformation,[],[f6])).
% 2.51/0.73  fof(f6,axiom,(
% 2.51/0.73    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 2.51/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 2.51/0.73  fof(f40,plain,(
% 2.51/0.73    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.51/0.73    inference(cnf_transformation,[],[f7])).
% 2.51/0.73  fof(f7,axiom,(
% 2.51/0.73    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.51/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.51/0.73  fof(f88,plain,(
% 2.51/0.73    ( ! [X4,X1] : (r2_hidden(X4,k2_xboole_0(k1_tarski(X4),k1_tarski(X1)))) )),
% 2.51/0.73    inference(equality_resolution,[],[f87])).
% 2.51/0.73  fof(f87,plain,(
% 2.51/0.73    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_xboole_0(k1_tarski(X4),k1_tarski(X1)) != X2) )),
% 2.51/0.73    inference(equality_resolution,[],[f74])).
% 2.51/0.73  fof(f74,plain,(
% 2.51/0.73    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) != X2) )),
% 2.51/0.73    inference(definition_unfolding,[],[f64,f42])).
% 2.51/0.73  fof(f64,plain,(
% 2.51/0.73    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 2.51/0.73    inference(cnf_transformation,[],[f38])).
% 2.51/0.73  fof(f38,plain,(
% 2.51/0.73    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK6(X0,X1,X2) != X1 & sK6(X0,X1,X2) != X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sK6(X0,X1,X2) = X1 | sK6(X0,X1,X2) = X0 | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.51/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f37])).
% 2.51/0.73  fof(f37,plain,(
% 2.51/0.73    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK6(X0,X1,X2) != X1 & sK6(X0,X1,X2) != X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sK6(X0,X1,X2) = X1 | sK6(X0,X1,X2) = X0 | r2_hidden(sK6(X0,X1,X2),X2))))),
% 2.51/0.73    introduced(choice_axiom,[])).
% 2.51/0.73  fof(f36,plain,(
% 2.51/0.73    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.51/0.73    inference(rectify,[],[f35])).
% 2.51/0.73  fof(f35,plain,(
% 2.51/0.73    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.51/0.73    inference(flattening,[],[f34])).
% 2.51/0.73  fof(f34,plain,(
% 2.51/0.73    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.51/0.73    inference(nnf_transformation,[],[f5])).
% 2.51/0.73  fof(f5,axiom,(
% 2.51/0.73    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.51/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 2.51/0.73  fof(f1336,plain,(
% 2.51/0.73    ~r2_hidden(sK0,k1_tarski(sK0))),
% 2.51/0.73    inference(resolution,[],[f1230,f1215])).
% 2.51/0.73  fof(f1215,plain,(
% 2.51/0.73    r2_hidden(sK2(k1_tarski(sK0),sK0),sK0)),
% 2.51/0.73    inference(trivial_inequality_removal,[],[f1200])).
% 2.51/0.73  fof(f1200,plain,(
% 2.51/0.73    sK0 != sK0 | r2_hidden(sK2(k1_tarski(sK0),sK0),sK0)),
% 2.51/0.73    inference(superposition,[],[f39,f1197])).
% 2.51/0.73  fof(f1197,plain,(
% 2.51/0.73    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0 | r2_hidden(sK2(k1_tarski(X0),X0),X0)) )),
% 2.51/0.73    inference(factoring,[],[f799])).
% 2.51/0.73  fof(f799,plain,(
% 2.51/0.73    ( ! [X0,X1] : (r2_hidden(sK2(k1_tarski(X0),X1),X1) | k3_tarski(k1_tarski(X0)) = X1 | r2_hidden(sK2(k1_tarski(X0),X1),X0)) )),
% 2.51/0.73    inference(duplicate_literal_removal,[],[f796])).
% 2.51/0.73  fof(f796,plain,(
% 2.51/0.73    ( ! [X0,X1] : (r2_hidden(sK2(k1_tarski(X0),X1),X0) | k3_tarski(k1_tarski(X0)) = X1 | r2_hidden(sK2(k1_tarski(X0),X1),X1) | r2_hidden(sK2(k1_tarski(X0),X1),X1) | k3_tarski(k1_tarski(X0)) = X1) )),
% 2.51/0.73    inference(superposition,[],[f52,f168])).
% 2.51/0.73  fof(f168,plain,(
% 2.51/0.73    ( ! [X15,X16] : (sK3(k1_tarski(X15),X16) = X15 | r2_hidden(sK2(k1_tarski(X15),X16),X16) | k3_tarski(k1_tarski(X15)) = X16) )),
% 2.51/0.73    inference(resolution,[],[f53,f115])).
% 2.51/0.73  fof(f115,plain,(
% 2.51/0.73    ( ! [X0,X1] : (~r2_hidden(X0,k1_tarski(X1)) | X0 = X1) )),
% 2.51/0.73    inference(resolution,[],[f104,f94])).
% 2.51/0.73  fof(f104,plain,(
% 2.51/0.73    ( ! [X6,X4,X5] : (~r2_hidden(X6,k1_tarski(X4)) | ~r2_hidden(X6,k1_tarski(X5)) | X4 = X5) )),
% 2.51/0.73    inference(superposition,[],[f83,f56])).
% 2.51/0.73  fof(f56,plain,(
% 2.51/0.73    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 2.51/0.73    inference(cnf_transformation,[],[f28])).
% 2.51/0.73  fof(f28,plain,(
% 2.51/0.73    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 2.51/0.73    inference(nnf_transformation,[],[f9])).
% 2.51/0.73  fof(f9,axiom,(
% 2.51/0.73    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 2.51/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 2.51/0.73  fof(f83,plain,(
% 2.51/0.73    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 2.51/0.73    inference(equality_resolution,[],[f58])).
% 2.51/0.73  fof(f58,plain,(
% 2.51/0.73    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.51/0.73    inference(cnf_transformation,[],[f33])).
% 2.51/0.73  fof(f33,plain,(
% 2.51/0.73    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.51/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).
% 2.51/0.73  fof(f32,plain,(
% 2.51/0.73    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 2.51/0.73    introduced(choice_axiom,[])).
% 2.51/0.73  fof(f31,plain,(
% 2.51/0.73    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.51/0.73    inference(rectify,[],[f30])).
% 2.51/0.73  fof(f30,plain,(
% 2.51/0.73    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.51/0.73    inference(flattening,[],[f29])).
% 2.51/0.73  fof(f29,plain,(
% 2.51/0.73    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.51/0.73    inference(nnf_transformation,[],[f3])).
% 2.51/0.73  fof(f3,axiom,(
% 2.51/0.73    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.51/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.51/0.73  fof(f53,plain,(
% 2.51/0.73    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | k3_tarski(X0) = X1 | r2_hidden(sK2(X0,X1),X1)) )),
% 2.51/0.73    inference(cnf_transformation,[],[f27])).
% 2.51/0.73  fof(f27,plain,(
% 2.51/0.73    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK2(X0,X1),X3)) | ~r2_hidden(sK2(X0,X1),X1)) & ((r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),sK3(X0,X1))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK4(X0,X5),X0) & r2_hidden(X5,sK4(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 2.51/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f23,f26,f25,f24])).
% 2.51/0.73  fof(f24,plain,(
% 2.51/0.73    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK2(X0,X1),X3)) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK2(X0,X1),X4)) | r2_hidden(sK2(X0,X1),X1))))),
% 2.51/0.73    introduced(choice_axiom,[])).
% 2.51/0.73  fof(f25,plain,(
% 2.51/0.73    ! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK2(X0,X1),X4)) => (r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),sK3(X0,X1))))),
% 2.51/0.73    introduced(choice_axiom,[])).
% 2.51/0.73  fof(f26,plain,(
% 2.51/0.73    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK4(X0,X5),X0) & r2_hidden(X5,sK4(X0,X5))))),
% 2.51/0.73    introduced(choice_axiom,[])).
% 2.51/0.73  fof(f23,plain,(
% 2.51/0.73    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 2.51/0.73    inference(rectify,[],[f22])).
% 2.51/0.73  fof(f22,plain,(
% 2.51/0.73    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 2.51/0.73    inference(nnf_transformation,[],[f8])).
% 2.51/0.73  fof(f8,axiom,(
% 2.51/0.73    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 2.51/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).
% 2.51/0.73  fof(f52,plain,(
% 2.51/0.73    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),sK3(X0,X1)) | k3_tarski(X0) = X1 | r2_hidden(sK2(X0,X1),X1)) )),
% 2.51/0.73    inference(cnf_transformation,[],[f27])).
% 2.51/0.73  fof(f39,plain,(
% 2.51/0.73    sK0 != k3_tarski(k1_tarski(sK0))),
% 2.51/0.73    inference(cnf_transformation,[],[f15])).
% 2.51/0.73  fof(f15,plain,(
% 2.51/0.73    sK0 != k3_tarski(k1_tarski(sK0))),
% 2.51/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f14])).
% 2.51/0.73  fof(f14,plain,(
% 2.51/0.73    ? [X0] : k3_tarski(k1_tarski(X0)) != X0 => sK0 != k3_tarski(k1_tarski(sK0))),
% 2.51/0.73    introduced(choice_axiom,[])).
% 2.51/0.73  fof(f12,plain,(
% 2.51/0.73    ? [X0] : k3_tarski(k1_tarski(X0)) != X0),
% 2.51/0.73    inference(ennf_transformation,[],[f11])).
% 2.51/0.73  fof(f11,negated_conjecture,(
% 2.51/0.73    ~! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 2.51/0.73    inference(negated_conjecture,[],[f10])).
% 2.51/0.73  fof(f10,conjecture,(
% 2.51/0.73    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 2.51/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).
% 2.51/0.73  fof(f1230,plain,(
% 2.51/0.73    ( ! [X0] : (~r2_hidden(sK2(k1_tarski(sK0),sK0),X0) | ~r2_hidden(X0,k1_tarski(sK0))) )),
% 2.51/0.73    inference(subsumption_resolution,[],[f1216,f39])).
% 2.51/0.73  fof(f1216,plain,(
% 2.51/0.73    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0)) | ~r2_hidden(sK2(k1_tarski(sK0),sK0),X0) | sK0 = k3_tarski(k1_tarski(sK0))) )),
% 2.51/0.73    inference(resolution,[],[f1215,f54])).
% 2.51/0.73  fof(f54,plain,(
% 2.51/0.73    ( ! [X0,X3,X1] : (~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(X3,X0) | ~r2_hidden(sK2(X0,X1),X3) | k3_tarski(X0) = X1) )),
% 2.51/0.73    inference(cnf_transformation,[],[f27])).
% 2.51/0.73  % SZS output end Proof for theBenchmark
% 2.51/0.73  % (8539)------------------------------
% 2.51/0.73  % (8539)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.51/0.73  % (8539)Termination reason: Refutation
% 2.51/0.73  
% 2.51/0.73  % (8539)Memory used [KB]: 12409
% 2.51/0.73  % (8539)Time elapsed: 0.324 s
% 2.51/0.73  % (8539)------------------------------
% 2.51/0.73  % (8539)------------------------------
% 2.51/0.73  % (8535)Success in time 0.369 s
%------------------------------------------------------------------------------
