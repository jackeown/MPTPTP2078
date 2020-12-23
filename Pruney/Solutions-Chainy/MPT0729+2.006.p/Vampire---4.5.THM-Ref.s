%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:11 EST 2020

% Result     : Theorem 2.05s
% Output     : Refutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 494 expanded)
%              Number of leaves         :   16 ( 157 expanded)
%              Depth                    :   13
%              Number of atoms          :  220 (1277 expanded)
%              Number of equality atoms :   88 ( 607 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1145,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f153,f249,f1136,f133])).

fof(f133,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f54,f55])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
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
    inference(rectify,[],[f53])).

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f1136,plain,(
    ! [X0] : ~ r2_hidden(sK0,k4_xboole_0(X0,sK1)) ),
    inference(unit_resulting_resolution,[],[f131,f832])).

fof(f832,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
      | ~ r2_hidden(X4,k4_xboole_0(X5,sK1)) ) ),
    inference(subsumption_resolution,[],[f822,f557])).

fof(f557,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
      | ~ r2_hidden(X1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ) ),
    inference(superposition,[],[f134,f149])).

fof(f149,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f136,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f84,f105])).

fof(f105,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f60,f102])).

fof(f102,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f67,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f86,f100])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f86,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f67,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f60,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f84,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f136,plain,(
    ~ r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f58,f132])).

fof(f132,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f118])).

fof(f118,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f77,f105])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f47,f48])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f58,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( sK0 != sK1
    & k1_ordinal1(sK0) = k1_ordinal1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f40])).

fof(f40,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_ordinal1(X0) = k1_ordinal1(X1) )
   => ( sK0 != sK1
      & k1_ordinal1(sK0) = k1_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_ordinal1(X0) = k1_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_ordinal1(X0) = k1_ordinal1(X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0,X1] :
      ( k1_ordinal1(X0) = k1_ordinal1(X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_ordinal1)).

fof(f134,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f822,plain,(
    ! [X4,X5] :
      ( r2_hidden(X4,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
      | ~ r2_hidden(X4,k4_xboole_0(X5,sK1))
      | ~ r2_hidden(X4,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ) ),
    inference(resolution,[],[f215,f134])).

fof(f215,plain,(
    ! [X6,X5] :
      ( r2_hidden(X6,k4_xboole_0(k4_xboole_0(X5,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
      | r2_hidden(X6,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
      | ~ r2_hidden(X6,k4_xboole_0(X5,sK1)) ) ),
    inference(superposition,[],[f133,f145])).

fof(f145,plain,(
    ! [X4] : k4_xboole_0(k4_xboole_0(X4,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = k4_xboole_0(k4_xboole_0(X4,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f143,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(definition_unfolding,[],[f87,f103])).

fof(f103,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f66,f102])).

fof(f66,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f87,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f143,plain,(
    ! [X4] : k4_xboole_0(k4_xboole_0(X4,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = k4_xboole_0(X4,k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ),
    inference(superposition,[],[f121,f107])).

fof(f107,plain,(
    k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f57,f106,f106])).

fof(f106,plain,(
    ! [X0] : k1_ordinal1(X0) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(X0,X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f61,f103,f105])).

fof(f61,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f57,plain,(
    k1_ordinal1(sK0) = k1_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f131,plain,(
    ! [X3] : r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f130])).

fof(f130,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k3_enumset1(X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f117])).

fof(f117,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f78,f105])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f249,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f238,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f238,plain,(
    r2_hidden(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f138,f218,f133])).

fof(f218,plain,(
    ! [X0] : ~ r2_hidden(sK1,k4_xboole_0(X0,sK0)) ),
    inference(unit_resulting_resolution,[],[f136,f168,f133])).

fof(f168,plain,(
    ! [X0] : ~ r2_hidden(sK1,k4_xboole_0(k4_xboole_0(X0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f164,f121])).

fof(f164,plain,(
    ! [X0] : ~ r2_hidden(sK1,k4_xboole_0(X0,k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) ),
    inference(unit_resulting_resolution,[],[f138,f134])).

fof(f138,plain,(
    r2_hidden(sK1,k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ),
    inference(superposition,[],[f108,f107])).

fof(f108,plain,(
    ! [X0] : r2_hidden(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(X0,X0,X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f59,f106])).

fof(f59,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f153,plain,(
    r2_hidden(sK0,k4_xboole_0(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(unit_resulting_resolution,[],[f108,f137,f133])).

fof(f137,plain,(
    ~ r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f58,f132])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:16:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (6085)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.49  % (6072)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.49  % (6077)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.50  % (6070)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.50  % (6081)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.51  % (6064)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (6063)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.52  % (6073)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.53  % (6082)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (6074)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.53  % (6062)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (6066)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (6084)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.53  % (6060)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.54  % (6086)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (6061)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.54  % (6079)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.54  % (6088)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (6065)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.54  % (6080)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (6075)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.54  % (6076)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.55  % (6076)Refutation not found, incomplete strategy% (6076)------------------------------
% 0.20/0.55  % (6076)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (6076)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (6076)Memory used [KB]: 10618
% 0.20/0.55  % (6076)Time elapsed: 0.128 s
% 0.20/0.55  % (6076)------------------------------
% 0.20/0.55  % (6076)------------------------------
% 0.20/0.55  % (6071)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.55  % (6069)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.55  % (6083)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.55  % (6068)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.55  % (6087)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.55  % (6078)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.55  % (6089)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.55  % (6089)Refutation not found, incomplete strategy% (6089)------------------------------
% 0.20/0.55  % (6089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (6089)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (6089)Memory used [KB]: 1663
% 0.20/0.55  % (6089)Time elapsed: 0.139 s
% 0.20/0.55  % (6089)------------------------------
% 0.20/0.55  % (6089)------------------------------
% 0.20/0.56  % (6067)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 2.05/0.64  % (6071)Refutation found. Thanks to Tanya!
% 2.05/0.64  % SZS status Theorem for theBenchmark
% 2.05/0.65  % SZS output start Proof for theBenchmark
% 2.05/0.65  fof(f1145,plain,(
% 2.05/0.65    $false),
% 2.05/0.65    inference(unit_resulting_resolution,[],[f153,f249,f1136,f133])).
% 2.05/0.66  fof(f133,plain,(
% 2.05/0.66    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 2.05/0.66    inference(equality_resolution,[],[f91])).
% 2.05/0.66  fof(f91,plain,(
% 2.05/0.66    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 2.05/0.66    inference(cnf_transformation,[],[f56])).
% 2.05/0.66  fof(f56,plain,(
% 2.05/0.66    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.05/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f54,f55])).
% 2.05/0.66  fof(f55,plain,(
% 2.05/0.66    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 2.05/0.66    introduced(choice_axiom,[])).
% 2.05/0.66  fof(f54,plain,(
% 2.05/0.66    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.05/0.66    inference(rectify,[],[f53])).
% 2.05/0.66  fof(f53,plain,(
% 2.05/0.66    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.05/0.66    inference(flattening,[],[f52])).
% 2.05/0.66  fof(f52,plain,(
% 2.05/0.66    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.05/0.66    inference(nnf_transformation,[],[f2])).
% 2.05/0.66  fof(f2,axiom,(
% 2.05/0.66    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.05/0.66  fof(f1136,plain,(
% 2.05/0.66    ( ! [X0] : (~r2_hidden(sK0,k4_xboole_0(X0,sK1))) )),
% 2.05/0.66    inference(unit_resulting_resolution,[],[f131,f832])).
% 2.05/0.66  fof(f832,plain,(
% 2.05/0.66    ( ! [X4,X5] : (~r2_hidden(X4,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X4,k4_xboole_0(X5,sK1))) )),
% 2.05/0.66    inference(subsumption_resolution,[],[f822,f557])).
% 2.05/0.66  fof(f557,plain,(
% 2.05/0.66    ( ! [X1] : (~r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) )),
% 2.05/0.66    inference(superposition,[],[f134,f149])).
% 2.05/0.66  fof(f149,plain,(
% 2.05/0.66    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 2.05/0.66    inference(unit_resulting_resolution,[],[f136,f119])).
% 2.05/0.66  fof(f119,plain,(
% 2.05/0.66    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) = X0) )),
% 2.05/0.66    inference(definition_unfolding,[],[f84,f105])).
% 2.05/0.66  fof(f105,plain,(
% 2.05/0.66    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 2.05/0.66    inference(definition_unfolding,[],[f60,f102])).
% 2.05/0.66  fof(f102,plain,(
% 2.05/0.66    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 2.05/0.66    inference(definition_unfolding,[],[f67,f101])).
% 2.05/0.66  fof(f101,plain,(
% 2.05/0.66    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 2.05/0.66    inference(definition_unfolding,[],[f86,f100])).
% 2.05/0.66  fof(f100,plain,(
% 2.05/0.66    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f19])).
% 2.05/0.66  fof(f19,axiom,(
% 2.05/0.66    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 2.05/0.66  fof(f86,plain,(
% 2.05/0.66    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f18])).
% 2.05/0.66  fof(f18,axiom,(
% 2.05/0.66    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.05/0.66  fof(f67,plain,(
% 2.05/0.66    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f17])).
% 2.05/0.66  fof(f17,axiom,(
% 2.05/0.66    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.05/0.66  fof(f60,plain,(
% 2.05/0.66    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f16])).
% 2.05/0.66  fof(f16,axiom,(
% 2.05/0.66    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.05/0.66  fof(f84,plain,(
% 2.05/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f51])).
% 2.05/0.66  fof(f51,plain,(
% 2.05/0.66    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 2.05/0.66    inference(nnf_transformation,[],[f22])).
% 2.05/0.66  fof(f22,axiom,(
% 2.05/0.66    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 2.05/0.66  fof(f136,plain,(
% 2.05/0.66    ~r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 2.05/0.66    inference(unit_resulting_resolution,[],[f58,f132])).
% 2.05/0.66  fof(f132,plain,(
% 2.05/0.66    ( ! [X0,X3] : (~r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0)) | X0 = X3) )),
% 2.05/0.66    inference(equality_resolution,[],[f118])).
% 2.05/0.66  fof(f118,plain,(
% 2.05/0.66    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 2.05/0.66    inference(definition_unfolding,[],[f77,f105])).
% 2.05/0.66  fof(f77,plain,(
% 2.05/0.66    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.05/0.66    inference(cnf_transformation,[],[f49])).
% 2.05/0.66  fof(f49,plain,(
% 2.05/0.66    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.05/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f47,f48])).
% 2.05/0.66  fof(f48,plain,(
% 2.05/0.66    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 2.05/0.66    introduced(choice_axiom,[])).
% 2.05/0.66  fof(f47,plain,(
% 2.05/0.66    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.05/0.66    inference(rectify,[],[f46])).
% 2.05/0.66  fof(f46,plain,(
% 2.05/0.66    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.05/0.66    inference(nnf_transformation,[],[f15])).
% 2.05/0.66  fof(f15,axiom,(
% 2.05/0.66    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 2.05/0.66  fof(f58,plain,(
% 2.05/0.66    sK0 != sK1),
% 2.05/0.66    inference(cnf_transformation,[],[f41])).
% 2.05/0.66  fof(f41,plain,(
% 2.05/0.66    sK0 != sK1 & k1_ordinal1(sK0) = k1_ordinal1(sK1)),
% 2.05/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f40])).
% 2.05/0.66  fof(f40,plain,(
% 2.05/0.66    ? [X0,X1] : (X0 != X1 & k1_ordinal1(X0) = k1_ordinal1(X1)) => (sK0 != sK1 & k1_ordinal1(sK0) = k1_ordinal1(sK1))),
% 2.05/0.66    introduced(choice_axiom,[])).
% 2.05/0.66  fof(f31,plain,(
% 2.05/0.66    ? [X0,X1] : (X0 != X1 & k1_ordinal1(X0) = k1_ordinal1(X1))),
% 2.05/0.66    inference(ennf_transformation,[],[f28])).
% 2.05/0.66  fof(f28,negated_conjecture,(
% 2.05/0.66    ~! [X0,X1] : (k1_ordinal1(X0) = k1_ordinal1(X1) => X0 = X1)),
% 2.05/0.66    inference(negated_conjecture,[],[f27])).
% 2.05/0.66  fof(f27,conjecture,(
% 2.05/0.66    ! [X0,X1] : (k1_ordinal1(X0) = k1_ordinal1(X1) => X0 = X1)),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_ordinal1)).
% 2.05/0.66  fof(f134,plain,(
% 2.05/0.66    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 2.05/0.66    inference(equality_resolution,[],[f90])).
% 2.05/0.66  fof(f90,plain,(
% 2.05/0.66    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.05/0.66    inference(cnf_transformation,[],[f56])).
% 2.05/0.66  fof(f822,plain,(
% 2.05/0.66    ( ! [X4,X5] : (r2_hidden(X4,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~r2_hidden(X4,k4_xboole_0(X5,sK1)) | ~r2_hidden(X4,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) )),
% 2.05/0.66    inference(resolution,[],[f215,f134])).
% 2.05/0.66  fof(f215,plain,(
% 2.05/0.66    ( ! [X6,X5] : (r2_hidden(X6,k4_xboole_0(k4_xboole_0(X5,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | r2_hidden(X6,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~r2_hidden(X6,k4_xboole_0(X5,sK1))) )),
% 2.05/0.66    inference(superposition,[],[f133,f145])).
% 2.05/0.66  fof(f145,plain,(
% 2.05/0.66    ( ! [X4] : (k4_xboole_0(k4_xboole_0(X4,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = k4_xboole_0(k4_xboole_0(X4,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) )),
% 2.05/0.66    inference(forward_demodulation,[],[f143,f121])).
% 2.05/0.66  fof(f121,plain,(
% 2.05/0.66    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))) )),
% 2.05/0.66    inference(definition_unfolding,[],[f87,f103])).
% 2.05/0.66  fof(f103,plain,(
% 2.05/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 2.05/0.66    inference(definition_unfolding,[],[f66,f102])).
% 2.05/0.66  fof(f66,plain,(
% 2.05/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.05/0.66    inference(cnf_transformation,[],[f20])).
% 2.05/0.66  fof(f20,axiom,(
% 2.05/0.66    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.05/0.66  fof(f87,plain,(
% 2.05/0.66    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.05/0.66    inference(cnf_transformation,[],[f11])).
% 2.05/0.66  fof(f11,axiom,(
% 2.05/0.66    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.05/0.66  fof(f143,plain,(
% 2.05/0.66    ( ! [X4] : (k4_xboole_0(k4_xboole_0(X4,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = k4_xboole_0(X4,k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) )),
% 2.05/0.66    inference(superposition,[],[f121,f107])).
% 2.05/0.66  fof(f107,plain,(
% 2.05/0.66    k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 2.05/0.66    inference(definition_unfolding,[],[f57,f106,f106])).
% 2.05/0.66  fof(f106,plain,(
% 2.05/0.66    ( ! [X0] : (k1_ordinal1(X0) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(X0,X0,X0,X0,X0)))) )),
% 2.05/0.66    inference(definition_unfolding,[],[f61,f103,f105])).
% 2.05/0.66  fof(f61,plain,(
% 2.05/0.66    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 2.05/0.66    inference(cnf_transformation,[],[f24])).
% 2.05/0.66  fof(f24,axiom,(
% 2.05/0.66    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 2.05/0.66  fof(f57,plain,(
% 2.05/0.66    k1_ordinal1(sK0) = k1_ordinal1(sK1)),
% 2.05/0.66    inference(cnf_transformation,[],[f41])).
% 2.05/0.66  fof(f131,plain,(
% 2.05/0.66    ( ! [X3] : (r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3))) )),
% 2.05/0.66    inference(equality_resolution,[],[f130])).
% 2.05/0.66  fof(f130,plain,(
% 2.05/0.66    ( ! [X3,X1] : (r2_hidden(X3,X1) | k3_enumset1(X3,X3,X3,X3,X3) != X1) )),
% 2.05/0.66    inference(equality_resolution,[],[f117])).
% 2.05/0.66  fof(f117,plain,(
% 2.05/0.66    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 2.05/0.66    inference(definition_unfolding,[],[f78,f105])).
% 2.05/0.66  fof(f78,plain,(
% 2.05/0.66    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 2.05/0.66    inference(cnf_transformation,[],[f49])).
% 2.05/0.66  fof(f249,plain,(
% 2.05/0.66    ~r2_hidden(sK0,sK1)),
% 2.05/0.66    inference(unit_resulting_resolution,[],[f238,f73])).
% 2.05/0.66  fof(f73,plain,(
% 2.05/0.66    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f35])).
% 2.05/0.66  fof(f35,plain,(
% 2.05/0.66    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 2.05/0.66    inference(ennf_transformation,[],[f1])).
% 2.05/0.66  fof(f1,axiom,(
% 2.05/0.66    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 2.05/0.66  fof(f238,plain,(
% 2.05/0.66    r2_hidden(sK1,sK0)),
% 2.05/0.66    inference(unit_resulting_resolution,[],[f138,f218,f133])).
% 2.05/0.66  fof(f218,plain,(
% 2.05/0.66    ( ! [X0] : (~r2_hidden(sK1,k4_xboole_0(X0,sK0))) )),
% 2.05/0.66    inference(unit_resulting_resolution,[],[f136,f168,f133])).
% 2.05/0.66  fof(f168,plain,(
% 2.05/0.66    ( ! [X0] : (~r2_hidden(sK1,k4_xboole_0(k4_xboole_0(X0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) )),
% 2.05/0.66    inference(forward_demodulation,[],[f164,f121])).
% 2.05/0.66  fof(f164,plain,(
% 2.05/0.66    ( ! [X0] : (~r2_hidden(sK1,k4_xboole_0(X0,k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))) )),
% 2.05/0.66    inference(unit_resulting_resolution,[],[f138,f134])).
% 2.05/0.66  fof(f138,plain,(
% 2.05/0.66    r2_hidden(sK1,k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),
% 2.05/0.66    inference(superposition,[],[f108,f107])).
% 2.05/0.66  fof(f108,plain,(
% 2.05/0.66    ( ! [X0] : (r2_hidden(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(X0,X0,X0,X0,X0))))) )),
% 2.05/0.66    inference(definition_unfolding,[],[f59,f106])).
% 2.05/0.66  fof(f59,plain,(
% 2.05/0.66    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 2.05/0.66    inference(cnf_transformation,[],[f25])).
% 2.05/0.66  fof(f25,axiom,(
% 2.05/0.66    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).
% 2.05/0.66  fof(f153,plain,(
% 2.05/0.66    r2_hidden(sK0,k4_xboole_0(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 2.05/0.66    inference(unit_resulting_resolution,[],[f108,f137,f133])).
% 2.05/0.66  fof(f137,plain,(
% 2.05/0.66    ~r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 2.05/0.66    inference(unit_resulting_resolution,[],[f58,f132])).
% 2.05/0.66  % SZS output end Proof for theBenchmark
% 2.05/0.66  % (6071)------------------------------
% 2.05/0.66  % (6071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.05/0.66  % (6071)Termination reason: Refutation
% 2.05/0.66  
% 2.05/0.66  % (6071)Memory used [KB]: 7419
% 2.05/0.66  % (6071)Time elapsed: 0.238 s
% 2.05/0.66  % (6071)------------------------------
% 2.05/0.66  % (6071)------------------------------
% 2.05/0.66  % (6059)Success in time 0.301 s
%------------------------------------------------------------------------------
