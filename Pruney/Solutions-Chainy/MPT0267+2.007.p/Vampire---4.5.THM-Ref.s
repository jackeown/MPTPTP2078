%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:35 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :  117 (2663 expanded)
%              Number of leaves         :   20 ( 786 expanded)
%              Depth                    :   28
%              Number of atoms          :  437 (6843 expanded)
%              Number of equality atoms :  188 (2554 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    7 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f437,plain,(
    $false ),
    inference(subsumption_resolution,[],[f436,f410])).

fof(f410,plain,(
    ! [X0,X1] : ~ r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X0,X1),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) ),
    inference(backward_demodulation,[],[f154,f399])).

fof(f399,plain,(
    sK0 = sK2 ),
    inference(subsumption_resolution,[],[f398,f118])).

fof(f118,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f56,f92])).

fof(f92,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f49,f88])).

fof(f88,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f60,f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f72,f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f81,f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f82,f83])).

fof(f83,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f53,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f49,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).

fof(f32,plain,(
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

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f398,plain,
    ( sK0 = sK2
    | r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(subsumption_resolution,[],[f397,f143])).

fof(f143,plain,(
    r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(subsumption_resolution,[],[f142,f120])).

fof(f120,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f63,f89])).

fof(f89,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f88])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & ~ r2_hidden(sK4(X0,X1,X2),X0) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( r2_hidden(sK4(X0,X1,X2),X1)
            | r2_hidden(sK4(X0,X1,X2),X0)
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & ~ r2_hidden(sK4(X0,X1,X2),X0) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( r2_hidden(sK4(X0,X1,X2),X1)
          | r2_hidden(sK4(X0,X1,X2),X0)
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f142,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(subsumption_resolution,[],[f140,f119])).

fof(f119,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f64,f89])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f140,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(resolution,[],[f139,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f139,plain,
    ( r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))
    | r2_hidden(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f137])).

fof(f137,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) ),
    inference(resolution,[],[f136,f68])).

fof(f136,plain,
    ( r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))
    | r2_hidden(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f134])).

fof(f134,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))) ),
    inference(resolution,[],[f131,f68])).

fof(f131,plain,
    ( r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))))
    | r2_hidden(sK0,sK1) ),
    inference(forward_demodulation,[],[f95,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f95,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))) ),
    inference(definition_unfolding,[],[f45,f91,f92])).

fof(f91,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f54,f90])).

fof(f90,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f55,f89])).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f45,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( sK0 = sK2
      | ~ r2_hidden(sK0,sK1)
      | ~ r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) )
    & ( ( sK0 != sK2
        & r2_hidden(sK0,sK1) )
      | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( ( X0 = X2
          | ~ r2_hidden(X0,X1)
          | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) )
        & ( ( X0 != X2
            & r2_hidden(X0,X1) )
          | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) )
   => ( ( sK0 = sK2
        | ~ r2_hidden(sK0,sK1)
        | ~ r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) )
      & ( ( sK0 != sK2
          & r2_hidden(sK0,sK1) )
        | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ( X0 = X2
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ( X0 = X2
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <~> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      <=> ( X0 != X2
          & r2_hidden(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f397,plain,
    ( sK0 = sK2
    | r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(resolution,[],[f169,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f169,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))
    | sK0 = sK2 ),
    inference(subsumption_resolution,[],[f168,f166])).

fof(f166,plain,(
    r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f163,f144])).

fof(f144,plain,
    ( ~ r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f141,f143])).

fof(f141,plain,
    ( r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(resolution,[],[f139,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f163,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(resolution,[],[f143,f121])).

fof(f121,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f107])).

fof(f107,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f62,f89])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f168,plain,
    ( sK0 = sK2
    | ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) ),
    inference(resolution,[],[f150,f69])).

fof(f150,plain,
    ( r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))
    | sK0 = sK2 ),
    inference(subsumption_resolution,[],[f149,f136])).

fof(f149,plain,
    ( sK0 = sK2
    | ~ r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))) ),
    inference(duplicate_literal_removal,[],[f147])).

fof(f147,plain,
    ( sK0 = sK2
    | ~ r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f129,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f129,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))))
    | sK0 = sK2
    | ~ r2_hidden(sK0,sK1) ),
    inference(forward_demodulation,[],[f93,f61])).

fof(f93,plain,
    ( sK0 = sK2
    | ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))) ),
    inference(definition_unfolding,[],[f47,f91,f92])).

fof(f47,plain,
    ( sK0 = sK2
    | ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f29])).

fof(f154,plain,(
    ! [X0,X1] : ~ r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X0,X1),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) ),
    inference(unit_resulting_resolution,[],[f127,f143,f69])).

fof(f127,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f126])).

fof(f126,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f74,f87])).

fof(f74,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK5(X0,X1,X2,X3) != X2
              & sK5(X0,X1,X2,X3) != X1
              & sK5(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
          & ( sK5(X0,X1,X2,X3) = X2
            | sK5(X0,X1,X2,X3) = X1
            | sK5(X0,X1,X2,X3) = X0
            | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f42,f43])).

fof(f43,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK5(X0,X1,X2,X3) != X2
            & sK5(X0,X1,X2,X3) != X1
            & sK5(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
        & ( sK5(X0,X1,X2,X3) = X2
          | sK5(X0,X1,X2,X3) = X1
          | sK5(X0,X1,X2,X3) = X0
          | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f41])).

% (13899)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f436,plain,(
    r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) ),
    inference(forward_demodulation,[],[f429,f399])).

fof(f429,plain,(
    r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) ),
    inference(trivial_inequality_removal,[],[f424])).

fof(f424,plain,
    ( sK0 != sK0
    | r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) ),
    inference(backward_demodulation,[],[f285,f399])).

fof(f285,plain,
    ( sK0 != sK2
    | r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) ),
    inference(subsumption_resolution,[],[f283,f166])).

fof(f283,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK0 != sK2
    | r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) ),
    inference(duplicate_literal_removal,[],[f281])).

fof(f281,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK0 != sK2
    | r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f133,f70])).

fof(f133,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))
    | ~ r2_hidden(sK0,sK1)
    | sK0 != sK2 ),
    inference(resolution,[],[f130,f69])).

fof(f130,plain,
    ( r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))))
    | sK0 != sK2 ),
    inference(forward_demodulation,[],[f94,f61])).

fof(f94,plain,
    ( sK0 != sK2
    | r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))) ),
    inference(definition_unfolding,[],[f46,f91,f92])).

fof(f46,plain,
    ( sK0 != sK2
    | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:40:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.53  % (13880)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.55  % (13883)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.55  % (13882)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.55  % (13878)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.55  % (13884)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (13889)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.55  % (13904)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (13888)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.56  % (13890)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.56  % (13907)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.56  % (13906)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.56/0.57  % (13881)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.56/0.57  % (13879)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.56/0.57  % (13901)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.56/0.57  % (13892)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.56/0.57  % (13879)Refutation not found, incomplete strategy% (13879)------------------------------
% 1.56/0.57  % (13879)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (13879)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.57  
% 1.56/0.57  % (13879)Memory used [KB]: 1791
% 1.56/0.57  % (13879)Time elapsed: 0.143 s
% 1.56/0.57  % (13879)------------------------------
% 1.56/0.57  % (13879)------------------------------
% 1.56/0.57  % (13893)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.56/0.57  % (13892)Refutation not found, incomplete strategy% (13892)------------------------------
% 1.56/0.57  % (13892)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (13892)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.57  
% 1.56/0.57  % (13892)Memory used [KB]: 1663
% 1.56/0.57  % (13892)Time elapsed: 0.150 s
% 1.56/0.57  % (13892)------------------------------
% 1.56/0.57  % (13892)------------------------------
% 1.56/0.57  % (13907)Refutation not found, incomplete strategy% (13907)------------------------------
% 1.56/0.57  % (13907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (13907)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.57  
% 1.56/0.57  % (13907)Memory used [KB]: 1663
% 1.56/0.57  % (13907)Time elapsed: 0.145 s
% 1.56/0.57  % (13907)------------------------------
% 1.56/0.57  % (13907)------------------------------
% 1.56/0.57  % (13894)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.56/0.57  % (13885)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.56/0.58  % (13889)Refutation found. Thanks to Tanya!
% 1.56/0.58  % SZS status Theorem for theBenchmark
% 1.56/0.58  % (13898)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.56/0.58  % (13886)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.56/0.58  % (13902)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.56/0.58  % (13900)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.56/0.58  % (13903)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.56/0.58  % (13905)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.56/0.58  % (13895)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.56/0.58  % (13891)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.73/0.59  % (13897)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.73/0.59  % (13887)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.73/0.59  % SZS output start Proof for theBenchmark
% 1.73/0.59  fof(f437,plain,(
% 1.73/0.59    $false),
% 1.73/0.59    inference(subsumption_resolution,[],[f436,f410])).
% 1.73/0.59  fof(f410,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X0,X1),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))) )),
% 1.73/0.59    inference(backward_demodulation,[],[f154,f399])).
% 1.73/0.59  fof(f399,plain,(
% 1.73/0.59    sK0 = sK2),
% 1.73/0.59    inference(subsumption_resolution,[],[f398,f118])).
% 1.73/0.59  fof(f118,plain,(
% 1.73/0.59    ( ! [X0,X3] : (~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) | X0 = X3) )),
% 1.73/0.59    inference(equality_resolution,[],[f101])).
% 1.73/0.59  fof(f101,plain,(
% 1.73/0.59    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 1.73/0.59    inference(definition_unfolding,[],[f56,f92])).
% 1.73/0.59  fof(f92,plain,(
% 1.73/0.59    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.73/0.59    inference(definition_unfolding,[],[f49,f88])).
% 1.73/0.59  fof(f88,plain,(
% 1.73/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.73/0.59    inference(definition_unfolding,[],[f53,f87])).
% 1.73/0.59  fof(f87,plain,(
% 1.73/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.73/0.59    inference(definition_unfolding,[],[f60,f86])).
% 1.73/0.59  fof(f86,plain,(
% 1.73/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.73/0.59    inference(definition_unfolding,[],[f72,f85])).
% 1.73/0.59  fof(f85,plain,(
% 1.73/0.59    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.73/0.59    inference(definition_unfolding,[],[f81,f84])).
% 1.73/0.59  fof(f84,plain,(
% 1.73/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.73/0.59    inference(definition_unfolding,[],[f82,f83])).
% 1.73/0.59  fof(f83,plain,(
% 1.73/0.59    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f17])).
% 1.73/0.59  fof(f17,axiom,(
% 1.73/0.59    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.73/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.73/0.59  fof(f82,plain,(
% 1.73/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f16])).
% 1.73/0.59  fof(f16,axiom,(
% 1.73/0.59    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.73/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.73/0.59  fof(f81,plain,(
% 1.73/0.59    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f15])).
% 1.73/0.59  fof(f15,axiom,(
% 1.73/0.59    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.73/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.73/0.59  fof(f72,plain,(
% 1.73/0.59    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f14])).
% 1.73/0.59  fof(f14,axiom,(
% 1.73/0.59    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.73/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.73/0.59  fof(f60,plain,(
% 1.73/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f13])).
% 1.73/0.59  fof(f13,axiom,(
% 1.73/0.59    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.73/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.73/0.59  fof(f53,plain,(
% 1.73/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f12])).
% 1.73/0.59  fof(f12,axiom,(
% 1.73/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.73/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.73/0.59  fof(f49,plain,(
% 1.73/0.59    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f11])).
% 1.73/0.59  fof(f11,axiom,(
% 1.73/0.59    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.73/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.73/0.59  fof(f56,plain,(
% 1.73/0.59    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.73/0.59    inference(cnf_transformation,[],[f33])).
% 1.73/0.59  fof(f33,plain,(
% 1.73/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.73/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).
% 1.73/0.59  fof(f32,plain,(
% 1.73/0.59    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 1.73/0.59    introduced(choice_axiom,[])).
% 1.73/0.59  fof(f31,plain,(
% 1.73/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.73/0.59    inference(rectify,[],[f30])).
% 1.73/0.59  fof(f30,plain,(
% 1.73/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.73/0.59    inference(nnf_transformation,[],[f10])).
% 1.73/0.59  fof(f10,axiom,(
% 1.73/0.59    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.73/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.73/0.59  fof(f398,plain,(
% 1.73/0.59    sK0 = sK2 | r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 1.73/0.59    inference(subsumption_resolution,[],[f397,f143])).
% 1.73/0.59  fof(f143,plain,(
% 1.73/0.59    r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 1.73/0.59    inference(subsumption_resolution,[],[f142,f120])).
% 1.73/0.59  fof(f120,plain,(
% 1.73/0.59    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X0)) )),
% 1.73/0.59    inference(equality_resolution,[],[f106])).
% 1.73/0.59  fof(f106,plain,(
% 1.73/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 1.73/0.59    inference(definition_unfolding,[],[f63,f89])).
% 1.73/0.59  fof(f89,plain,(
% 1.73/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.73/0.59    inference(definition_unfolding,[],[f52,f88])).
% 1.73/0.59  fof(f52,plain,(
% 1.73/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.73/0.59    inference(cnf_transformation,[],[f18])).
% 1.73/0.59  fof(f18,axiom,(
% 1.73/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.73/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.73/0.59  fof(f63,plain,(
% 1.73/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 1.73/0.59    inference(cnf_transformation,[],[f38])).
% 1.73/0.59  fof(f38,plain,(
% 1.73/0.59    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.73/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).
% 1.73/0.59  fof(f37,plain,(
% 1.73/0.59    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.73/0.59    introduced(choice_axiom,[])).
% 1.73/0.59  fof(f36,plain,(
% 1.73/0.59    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.73/0.59    inference(rectify,[],[f35])).
% 1.73/0.59  fof(f35,plain,(
% 1.73/0.59    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.73/0.59    inference(flattening,[],[f34])).
% 1.73/0.59  fof(f34,plain,(
% 1.73/0.59    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.73/0.59    inference(nnf_transformation,[],[f1])).
% 1.73/0.59  fof(f1,axiom,(
% 1.73/0.59    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.73/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.73/0.59  fof(f142,plain,(
% 1.73/0.59    r2_hidden(sK0,sK1) | r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 1.73/0.59    inference(subsumption_resolution,[],[f140,f119])).
% 1.73/0.59  fof(f119,plain,(
% 1.73/0.59    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 1.73/0.59    inference(equality_resolution,[],[f105])).
% 1.73/0.59  fof(f105,plain,(
% 1.73/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 1.73/0.59    inference(definition_unfolding,[],[f64,f89])).
% 1.73/0.59  fof(f64,plain,(
% 1.73/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 1.73/0.59    inference(cnf_transformation,[],[f38])).
% 1.73/0.59  fof(f140,plain,(
% 1.73/0.59    r2_hidden(sK0,sK1) | r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 1.73/0.59    inference(resolution,[],[f139,f68])).
% 1.73/0.59  fof(f68,plain,(
% 1.73/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f39])).
% 1.73/0.59  fof(f39,plain,(
% 1.73/0.59    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 1.73/0.59    inference(nnf_transformation,[],[f24])).
% 1.73/0.59  fof(f24,plain,(
% 1.73/0.59    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.73/0.59    inference(ennf_transformation,[],[f4])).
% 1.73/0.59  fof(f4,axiom,(
% 1.73/0.59    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.73/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.73/0.59  fof(f139,plain,(
% 1.73/0.59    r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) | r2_hidden(sK0,sK1)),
% 1.73/0.59    inference(duplicate_literal_removal,[],[f137])).
% 1.73/0.59  fof(f137,plain,(
% 1.73/0.59    r2_hidden(sK0,sK1) | r2_hidden(sK0,sK1) | r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))),
% 1.73/0.59    inference(resolution,[],[f136,f68])).
% 1.73/0.59  fof(f136,plain,(
% 1.73/0.59    r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))) | r2_hidden(sK0,sK1)),
% 1.73/0.59    inference(duplicate_literal_removal,[],[f134])).
% 1.73/0.59  fof(f134,plain,(
% 1.73/0.59    r2_hidden(sK0,sK1) | r2_hidden(sK0,sK1) | r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))),
% 1.73/0.59    inference(resolution,[],[f131,f68])).
% 1.73/0.59  fof(f131,plain,(
% 1.73/0.59    r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))) | r2_hidden(sK0,sK1)),
% 1.73/0.59    inference(forward_demodulation,[],[f95,f61])).
% 1.73/0.59  fof(f61,plain,(
% 1.73/0.59    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.73/0.59    inference(cnf_transformation,[],[f6])).
% 1.73/0.59  fof(f6,axiom,(
% 1.73/0.59    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.73/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.73/0.59  fof(f95,plain,(
% 1.73/0.59    r2_hidden(sK0,sK1) | r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))),
% 1.73/0.59    inference(definition_unfolding,[],[f45,f91,f92])).
% 1.73/0.59  fof(f91,plain,(
% 1.73/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 1.73/0.59    inference(definition_unfolding,[],[f54,f90])).
% 1.73/0.59  fof(f90,plain,(
% 1.73/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.73/0.59    inference(definition_unfolding,[],[f55,f89])).
% 1.73/0.59  fof(f55,plain,(
% 1.73/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.73/0.59    inference(cnf_transformation,[],[f8])).
% 1.73/0.59  fof(f8,axiom,(
% 1.73/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.73/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.73/0.59  fof(f54,plain,(
% 1.73/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.73/0.59    inference(cnf_transformation,[],[f5])).
% 1.73/0.59  fof(f5,axiom,(
% 1.73/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.73/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.73/0.59  fof(f45,plain,(
% 1.73/0.59    r2_hidden(sK0,sK1) | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))),
% 1.73/0.59    inference(cnf_transformation,[],[f29])).
% 1.73/0.59  fof(f29,plain,(
% 1.73/0.59    (sK0 = sK2 | ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))) & ((sK0 != sK2 & r2_hidden(sK0,sK1)) | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))))),
% 1.73/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f28])).
% 1.73/0.59  fof(f28,plain,(
% 1.73/0.59    ? [X0,X1,X2] : ((X0 = X2 | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) & ((X0 != X2 & r2_hidden(X0,X1)) | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))))) => ((sK0 = sK2 | ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))) & ((sK0 != sK2 & r2_hidden(sK0,sK1)) | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))))),
% 1.73/0.59    introduced(choice_axiom,[])).
% 1.73/0.59  fof(f27,plain,(
% 1.73/0.59    ? [X0,X1,X2] : ((X0 = X2 | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) & ((X0 != X2 & r2_hidden(X0,X1)) | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.73/0.59    inference(flattening,[],[f26])).
% 1.73/0.59  fof(f26,plain,(
% 1.73/0.59    ? [X0,X1,X2] : (((X0 = X2 | ~r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) & ((X0 != X2 & r2_hidden(X0,X1)) | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.73/0.59    inference(nnf_transformation,[],[f23])).
% 1.73/0.59  fof(f23,plain,(
% 1.73/0.59    ? [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <~> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.73/0.59    inference(ennf_transformation,[],[f20])).
% 1.73/0.59  fof(f20,negated_conjecture,(
% 1.73/0.59    ~! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.73/0.59    inference(negated_conjecture,[],[f19])).
% 1.73/0.59  fof(f19,conjecture,(
% 1.73/0.59    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.73/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 1.73/0.59  fof(f397,plain,(
% 1.73/0.59    sK0 = sK2 | r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | ~r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 1.73/0.59    inference(resolution,[],[f169,f71])).
% 1.73/0.59  fof(f71,plain,(
% 1.73/0.59    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f39])).
% 1.73/0.59  fof(f169,plain,(
% 1.73/0.59    ~r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) | sK0 = sK2),
% 1.73/0.59    inference(subsumption_resolution,[],[f168,f166])).
% 1.73/0.59  fof(f166,plain,(
% 1.73/0.59    r2_hidden(sK0,sK1)),
% 1.73/0.59    inference(subsumption_resolution,[],[f163,f144])).
% 1.73/0.59  fof(f144,plain,(
% 1.73/0.59    ~r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | r2_hidden(sK0,sK1)),
% 1.73/0.59    inference(subsumption_resolution,[],[f141,f143])).
% 1.73/0.59  fof(f141,plain,(
% 1.73/0.59    r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | ~r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 1.73/0.59    inference(resolution,[],[f139,f69])).
% 1.73/0.59  fof(f69,plain,(
% 1.73/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f39])).
% 1.73/0.59  fof(f163,plain,(
% 1.73/0.59    r2_hidden(sK0,sK1) | r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 1.73/0.59    inference(resolution,[],[f143,f121])).
% 1.73/0.59  fof(f121,plain,(
% 1.73/0.59    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | r2_hidden(X4,X0) | r2_hidden(X4,X1)) )),
% 1.73/0.59    inference(equality_resolution,[],[f107])).
% 1.73/0.59  fof(f107,plain,(
% 1.73/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 1.73/0.59    inference(definition_unfolding,[],[f62,f89])).
% 1.73/0.59  fof(f62,plain,(
% 1.73/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.73/0.59    inference(cnf_transformation,[],[f38])).
% 1.73/0.59  fof(f168,plain,(
% 1.73/0.59    sK0 = sK2 | ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))),
% 1.73/0.59    inference(resolution,[],[f150,f69])).
% 1.73/0.59  fof(f150,plain,(
% 1.73/0.59    r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))) | sK0 = sK2),
% 1.73/0.59    inference(subsumption_resolution,[],[f149,f136])).
% 1.73/0.59  fof(f149,plain,(
% 1.73/0.59    sK0 = sK2 | ~r2_hidden(sK0,sK1) | r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))),
% 1.73/0.59    inference(duplicate_literal_removal,[],[f147])).
% 1.73/0.59  fof(f147,plain,(
% 1.73/0.59    sK0 = sK2 | ~r2_hidden(sK0,sK1) | r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))) | ~r2_hidden(sK0,sK1)),
% 1.73/0.59    inference(resolution,[],[f129,f70])).
% 1.73/0.59  fof(f70,plain,(
% 1.73/0.59    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f39])).
% 1.73/0.59  fof(f129,plain,(
% 1.73/0.59    ~r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))) | sK0 = sK2 | ~r2_hidden(sK0,sK1)),
% 1.73/0.59    inference(forward_demodulation,[],[f93,f61])).
% 1.73/0.59  fof(f93,plain,(
% 1.73/0.59    sK0 = sK2 | ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))),
% 1.73/0.59    inference(definition_unfolding,[],[f47,f91,f92])).
% 1.73/0.59  fof(f47,plain,(
% 1.73/0.59    sK0 = sK2 | ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))),
% 1.73/0.59    inference(cnf_transformation,[],[f29])).
% 1.73/0.59  fof(f154,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X0,X1),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))) )),
% 1.73/0.59    inference(unit_resulting_resolution,[],[f127,f143,f69])).
% 1.73/0.59  fof(f127,plain,(
% 1.73/0.59    ( ! [X2,X5,X1] : (r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2))) )),
% 1.73/0.59    inference(equality_resolution,[],[f126])).
% 1.73/0.59  fof(f126,plain,(
% 1.73/0.59    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 1.73/0.59    inference(equality_resolution,[],[f114])).
% 1.73/0.59  fof(f114,plain,(
% 1.73/0.59    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 1.73/0.59    inference(definition_unfolding,[],[f74,f87])).
% 1.73/0.59  fof(f74,plain,(
% 1.73/0.59    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.73/0.59    inference(cnf_transformation,[],[f44])).
% 1.73/0.59  fof(f44,plain,(
% 1.73/0.59    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK5(X0,X1,X2,X3) != X2 & sK5(X0,X1,X2,X3) != X1 & sK5(X0,X1,X2,X3) != X0) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sK5(X0,X1,X2,X3) = X2 | sK5(X0,X1,X2,X3) = X1 | sK5(X0,X1,X2,X3) = X0 | r2_hidden(sK5(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.73/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f42,f43])).
% 1.73/0.59  fof(f43,plain,(
% 1.73/0.59    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK5(X0,X1,X2,X3) != X2 & sK5(X0,X1,X2,X3) != X1 & sK5(X0,X1,X2,X3) != X0) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sK5(X0,X1,X2,X3) = X2 | sK5(X0,X1,X2,X3) = X1 | sK5(X0,X1,X2,X3) = X0 | r2_hidden(sK5(X0,X1,X2,X3),X3))))),
% 1.73/0.59    introduced(choice_axiom,[])).
% 1.73/0.59  fof(f42,plain,(
% 1.73/0.59    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.73/0.59    inference(rectify,[],[f41])).
% 1.73/0.59  % (13899)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.73/0.59  fof(f41,plain,(
% 1.73/0.59    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.73/0.59    inference(flattening,[],[f40])).
% 1.73/0.59  fof(f40,plain,(
% 1.73/0.59    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.73/0.59    inference(nnf_transformation,[],[f25])).
% 1.73/0.59  fof(f25,plain,(
% 1.73/0.59    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.73/0.59    inference(ennf_transformation,[],[f9])).
% 1.73/0.59  fof(f9,axiom,(
% 1.73/0.59    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.73/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.73/0.59  fof(f436,plain,(
% 1.73/0.59    r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))),
% 1.73/0.59    inference(forward_demodulation,[],[f429,f399])).
% 1.73/0.59  fof(f429,plain,(
% 1.73/0.59    r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))),
% 1.73/0.59    inference(trivial_inequality_removal,[],[f424])).
% 1.73/0.59  fof(f424,plain,(
% 1.73/0.59    sK0 != sK0 | r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))),
% 1.73/0.59    inference(backward_demodulation,[],[f285,f399])).
% 1.73/0.59  fof(f285,plain,(
% 1.73/0.59    sK0 != sK2 | r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))),
% 1.73/0.59    inference(subsumption_resolution,[],[f283,f166])).
% 1.73/0.59  fof(f283,plain,(
% 1.73/0.59    ~r2_hidden(sK0,sK1) | sK0 != sK2 | r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))),
% 1.73/0.59    inference(duplicate_literal_removal,[],[f281])).
% 1.73/0.59  fof(f281,plain,(
% 1.73/0.59    ~r2_hidden(sK0,sK1) | sK0 != sK2 | r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) | ~r2_hidden(sK0,sK1)),
% 1.73/0.59    inference(resolution,[],[f133,f70])).
% 1.73/0.59  fof(f133,plain,(
% 1.73/0.59    ~r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))) | ~r2_hidden(sK0,sK1) | sK0 != sK2),
% 1.73/0.59    inference(resolution,[],[f130,f69])).
% 1.73/0.59  fof(f130,plain,(
% 1.73/0.59    r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))) | sK0 != sK2),
% 1.73/0.59    inference(forward_demodulation,[],[f94,f61])).
% 1.73/0.59  fof(f94,plain,(
% 1.73/0.59    sK0 != sK2 | r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))),
% 1.73/0.59    inference(definition_unfolding,[],[f46,f91,f92])).
% 1.73/0.59  fof(f46,plain,(
% 1.73/0.59    sK0 != sK2 | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))),
% 1.73/0.59    inference(cnf_transformation,[],[f29])).
% 1.73/0.59  % SZS output end Proof for theBenchmark
% 1.73/0.59  % (13889)------------------------------
% 1.73/0.59  % (13889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.59  % (13889)Termination reason: Refutation
% 1.73/0.59  
% 1.73/0.59  % (13889)Memory used [KB]: 6524
% 1.73/0.59  % (13889)Time elapsed: 0.154 s
% 1.73/0.59  % (13889)------------------------------
% 1.73/0.59  % (13889)------------------------------
% 1.73/0.59  % (13894)Refutation not found, incomplete strategy% (13894)------------------------------
% 1.73/0.59  % (13894)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.59  % (13894)Termination reason: Refutation not found, incomplete strategy
% 1.73/0.59  
% 1.73/0.59  % (13894)Memory used [KB]: 10618
% 1.73/0.59  % (13894)Time elapsed: 0.131 s
% 1.73/0.59  % (13894)------------------------------
% 1.73/0.59  % (13894)------------------------------
% 1.73/0.59  % (13877)Success in time 0.228 s
%------------------------------------------------------------------------------
