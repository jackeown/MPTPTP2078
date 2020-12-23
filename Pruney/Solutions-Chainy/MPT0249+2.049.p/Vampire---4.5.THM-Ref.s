%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:17 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 232 expanded)
%              Number of leaves         :   16 (  71 expanded)
%              Depth                    :   15
%              Number of atoms          :  254 ( 589 expanded)
%              Number of equality atoms :  114 ( 433 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f208,plain,(
    $false ),
    inference(subsumption_resolution,[],[f207,f39])).

fof(f39,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & sK1 != sK2
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f21])).

% (25199)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & sK1 != sK2
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f207,plain,(
    sK1 = sK2 ),
    inference(forward_demodulation,[],[f198,f143])).

fof(f143,plain,(
    sK1 = k2_xboole_0(sK1,sK2) ),
    inference(subsumption_resolution,[],[f138,f40])).

fof(f40,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f22])).

fof(f138,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k2_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f89,f53])).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f89,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k2_xboole_0(sK1,sK2))
      | k1_xboole_0 = X1
      | k2_xboole_0(sK1,sK2) = X1 ) ),
    inference(superposition,[],[f71,f68])).

fof(f68,plain,(
    k2_xboole_0(sK1,sK2) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f38,f67])).

fof(f67,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f58,f66])).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f62,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f63,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f62,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f38,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k3_enumset1(X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f42,f67,f67])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f198,plain,(
    sK2 = k2_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f182,f121])).

fof(f121,plain,(
    r2_hidden(sK0,sK2) ),
    inference(subsumption_resolution,[],[f120,f41])).

fof(f41,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f22])).

fof(f120,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f45,f119])).

fof(f119,plain,(
    sK0 = sK3(sK2) ),
    inference(subsumption_resolution,[],[f116,f41])).

fof(f116,plain,
    ( sK0 = sK3(sK2)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f99,f45])).

fof(f99,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | sK0 = X1 ) ),
    inference(resolution,[],[f87,f81])).

fof(f81,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).

fof(f30,plain,(
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

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f87,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_xboole_0(sK1,sK2))
      | sK0 = X0 ) ),
    inference(superposition,[],[f86,f68])).

fof(f86,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f54,f67])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f182,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK0,X2)
      | k2_xboole_0(sK1,X2) = X2 ) ),
    inference(resolution,[],[f151,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f151,plain,(
    ! [X4] :
      ( r1_tarski(sK1,X4)
      | ~ r2_hidden(sK0,X4) ) ),
    inference(backward_demodulation,[],[f95,f143])).

fof(f95,plain,(
    ! [X4] :
      ( r1_tarski(k2_xboole_0(sK1,sK2),X4)
      | ~ r2_hidden(sK0,X4) ) ),
    inference(duplicate_literal_removal,[],[f94])).

fof(f94,plain,(
    ! [X4] :
      ( r1_tarski(k2_xboole_0(sK1,sK2),X4)
      | ~ r2_hidden(sK0,X4)
      | ~ r2_hidden(sK0,X4) ) ),
    inference(superposition,[],[f76,f68])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f61,f66])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n020.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:09:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.52  % (25192)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (25191)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (25200)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.31/0.54  % (25207)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.31/0.55  % (25200)Refutation not found, incomplete strategy% (25200)------------------------------
% 1.31/0.55  % (25200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (25208)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.31/0.55  % (25194)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.31/0.55  % (25203)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.31/0.55  % (25208)Refutation found. Thanks to Tanya!
% 1.31/0.55  % SZS status Theorem for theBenchmark
% 1.31/0.55  % (25200)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.55  
% 1.31/0.55  % (25200)Memory used [KB]: 10618
% 1.31/0.55  % (25200)Time elapsed: 0.119 s
% 1.31/0.55  % (25200)------------------------------
% 1.31/0.55  % (25200)------------------------------
% 1.31/0.55  % (25210)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.31/0.55  % SZS output start Proof for theBenchmark
% 1.31/0.55  fof(f208,plain,(
% 1.31/0.55    $false),
% 1.31/0.55    inference(subsumption_resolution,[],[f207,f39])).
% 1.31/0.55  fof(f39,plain,(
% 1.31/0.55    sK1 != sK2),
% 1.31/0.55    inference(cnf_transformation,[],[f22])).
% 1.31/0.55  fof(f22,plain,(
% 1.31/0.55    k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.31/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f21])).
% 1.31/0.55  % (25199)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.31/0.55  fof(f21,plain,(
% 1.31/0.55    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2)) => (k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 1.31/0.55    introduced(choice_axiom,[])).
% 1.31/0.55  fof(f18,plain,(
% 1.31/0.55    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.31/0.55    inference(ennf_transformation,[],[f17])).
% 1.31/0.55  fof(f17,negated_conjecture,(
% 1.31/0.55    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.31/0.55    inference(negated_conjecture,[],[f16])).
% 1.31/0.55  fof(f16,conjecture,(
% 1.31/0.55    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.31/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 1.31/0.55  fof(f207,plain,(
% 1.31/0.55    sK1 = sK2),
% 1.31/0.55    inference(forward_demodulation,[],[f198,f143])).
% 1.31/0.55  fof(f143,plain,(
% 1.31/0.55    sK1 = k2_xboole_0(sK1,sK2)),
% 1.31/0.55    inference(subsumption_resolution,[],[f138,f40])).
% 1.31/0.55  fof(f40,plain,(
% 1.31/0.55    k1_xboole_0 != sK1),
% 1.31/0.55    inference(cnf_transformation,[],[f22])).
% 1.31/0.55  fof(f138,plain,(
% 1.31/0.55    k1_xboole_0 = sK1 | sK1 = k2_xboole_0(sK1,sK2)),
% 1.31/0.55    inference(resolution,[],[f89,f53])).
% 1.31/0.55  fof(f53,plain,(
% 1.31/0.55    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.31/0.55    inference(cnf_transformation,[],[f4])).
% 1.31/0.55  fof(f4,axiom,(
% 1.31/0.55    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.31/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.31/0.55  fof(f89,plain,(
% 1.31/0.55    ( ! [X1] : (~r1_tarski(X1,k2_xboole_0(sK1,sK2)) | k1_xboole_0 = X1 | k2_xboole_0(sK1,sK2) = X1) )),
% 1.31/0.55    inference(superposition,[],[f71,f68])).
% 1.31/0.55  fof(f68,plain,(
% 1.31/0.55    k2_xboole_0(sK1,sK2) = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.31/0.55    inference(definition_unfolding,[],[f38,f67])).
% 1.31/0.55  fof(f67,plain,(
% 1.31/0.55    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.31/0.55    inference(definition_unfolding,[],[f58,f66])).
% 1.31/0.55  fof(f66,plain,(
% 1.31/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.31/0.55    inference(definition_unfolding,[],[f62,f65])).
% 1.31/0.55  fof(f65,plain,(
% 1.31/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.31/0.55    inference(definition_unfolding,[],[f63,f64])).
% 1.31/0.55  fof(f64,plain,(
% 1.31/0.55    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.31/0.55    inference(cnf_transformation,[],[f9])).
% 1.31/0.55  fof(f9,axiom,(
% 1.31/0.55    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.31/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.31/0.55  fof(f63,plain,(
% 1.31/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.31/0.55    inference(cnf_transformation,[],[f8])).
% 1.31/0.55  fof(f8,axiom,(
% 1.31/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.31/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.31/0.55  fof(f62,plain,(
% 1.31/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.31/0.55    inference(cnf_transformation,[],[f7])).
% 1.31/0.55  fof(f7,axiom,(
% 1.31/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.31/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.31/0.55  fof(f58,plain,(
% 1.31/0.55    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.31/0.55    inference(cnf_transformation,[],[f6])).
% 1.31/0.55  fof(f6,axiom,(
% 1.31/0.55    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.31/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.31/0.55  fof(f38,plain,(
% 1.31/0.55    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.31/0.55    inference(cnf_transformation,[],[f22])).
% 1.31/0.55  fof(f71,plain,(
% 1.31/0.55    ( ! [X0,X1] : (~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1)) | k1_xboole_0 = X0 | k3_enumset1(X1,X1,X1,X1,X1) = X0) )),
% 1.31/0.55    inference(definition_unfolding,[],[f42,f67,f67])).
% 1.31/0.55  fof(f42,plain,(
% 1.31/0.55    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.31/0.55    inference(cnf_transformation,[],[f24])).
% 1.31/0.55  fof(f24,plain,(
% 1.31/0.55    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.31/0.55    inference(flattening,[],[f23])).
% 1.31/0.55  fof(f23,plain,(
% 1.31/0.55    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.31/0.55    inference(nnf_transformation,[],[f13])).
% 1.31/0.55  fof(f13,axiom,(
% 1.31/0.55    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.31/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.31/0.55  fof(f198,plain,(
% 1.31/0.55    sK2 = k2_xboole_0(sK1,sK2)),
% 1.31/0.55    inference(resolution,[],[f182,f121])).
% 1.31/0.55  fof(f121,plain,(
% 1.31/0.55    r2_hidden(sK0,sK2)),
% 1.31/0.55    inference(subsumption_resolution,[],[f120,f41])).
% 1.31/0.55  fof(f41,plain,(
% 1.31/0.55    k1_xboole_0 != sK2),
% 1.31/0.55    inference(cnf_transformation,[],[f22])).
% 1.31/0.55  fof(f120,plain,(
% 1.31/0.55    r2_hidden(sK0,sK2) | k1_xboole_0 = sK2),
% 1.31/0.55    inference(superposition,[],[f45,f119])).
% 1.31/0.55  fof(f119,plain,(
% 1.31/0.55    sK0 = sK3(sK2)),
% 1.31/0.55    inference(subsumption_resolution,[],[f116,f41])).
% 1.31/0.55  fof(f116,plain,(
% 1.31/0.55    sK0 = sK3(sK2) | k1_xboole_0 = sK2),
% 1.31/0.55    inference(resolution,[],[f99,f45])).
% 1.31/0.55  fof(f99,plain,(
% 1.31/0.55    ( ! [X1] : (~r2_hidden(X1,sK2) | sK0 = X1) )),
% 1.31/0.55    inference(resolution,[],[f87,f81])).
% 1.31/0.55  fof(f81,plain,(
% 1.31/0.55    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 1.31/0.55    inference(equality_resolution,[],[f48])).
% 1.31/0.55  fof(f48,plain,(
% 1.31/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 1.31/0.55    inference(cnf_transformation,[],[f31])).
% 1.31/0.55  fof(f31,plain,(
% 1.31/0.55    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.31/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).
% 1.31/0.55  fof(f30,plain,(
% 1.31/0.55    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.31/0.55    introduced(choice_axiom,[])).
% 1.31/0.55  fof(f29,plain,(
% 1.31/0.55    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.31/0.55    inference(rectify,[],[f28])).
% 1.31/0.55  fof(f28,plain,(
% 1.31/0.55    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.31/0.55    inference(flattening,[],[f27])).
% 1.31/0.55  fof(f27,plain,(
% 1.31/0.55    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.31/0.55    inference(nnf_transformation,[],[f1])).
% 1.31/0.55  fof(f1,axiom,(
% 1.31/0.55    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.31/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.31/0.55  fof(f87,plain,(
% 1.31/0.55    ( ! [X0] : (~r2_hidden(X0,k2_xboole_0(sK1,sK2)) | sK0 = X0) )),
% 1.31/0.55    inference(superposition,[],[f86,f68])).
% 1.31/0.55  fof(f86,plain,(
% 1.31/0.55    ( ! [X0,X3] : (~r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0)) | X0 = X3) )),
% 1.31/0.55    inference(equality_resolution,[],[f75])).
% 1.31/0.55  fof(f75,plain,(
% 1.31/0.55    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 1.31/0.55    inference(definition_unfolding,[],[f54,f67])).
% 1.31/0.55  fof(f54,plain,(
% 1.31/0.55    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.31/0.55    inference(cnf_transformation,[],[f35])).
% 1.31/0.55  fof(f35,plain,(
% 1.31/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.31/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f34])).
% 1.31/0.55  fof(f34,plain,(
% 1.31/0.55    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 1.31/0.55    introduced(choice_axiom,[])).
% 1.31/0.55  fof(f33,plain,(
% 1.31/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.31/0.55    inference(rectify,[],[f32])).
% 1.31/0.55  fof(f32,plain,(
% 1.31/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.31/0.55    inference(nnf_transformation,[],[f5])).
% 1.44/0.55  fof(f5,axiom,(
% 1.44/0.55    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.44/0.55  fof(f45,plain,(
% 1.44/0.55    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.44/0.55    inference(cnf_transformation,[],[f26])).
% 1.44/0.55  fof(f26,plain,(
% 1.44/0.55    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 1.44/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f25])).
% 1.44/0.55  fof(f25,plain,(
% 1.44/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.44/0.55    introduced(choice_axiom,[])).
% 1.44/0.55  fof(f19,plain,(
% 1.44/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.44/0.55    inference(ennf_transformation,[],[f2])).
% 1.44/0.55  fof(f2,axiom,(
% 1.44/0.55    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.44/0.55  fof(f182,plain,(
% 1.44/0.55    ( ! [X2] : (~r2_hidden(sK0,X2) | k2_xboole_0(sK1,X2) = X2) )),
% 1.44/0.55    inference(resolution,[],[f151,f52])).
% 1.44/0.55  fof(f52,plain,(
% 1.44/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.44/0.55    inference(cnf_transformation,[],[f20])).
% 1.44/0.55  fof(f20,plain,(
% 1.44/0.55    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.44/0.55    inference(ennf_transformation,[],[f3])).
% 1.44/0.55  fof(f3,axiom,(
% 1.44/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.44/0.55  fof(f151,plain,(
% 1.44/0.55    ( ! [X4] : (r1_tarski(sK1,X4) | ~r2_hidden(sK0,X4)) )),
% 1.44/0.55    inference(backward_demodulation,[],[f95,f143])).
% 1.44/0.55  fof(f95,plain,(
% 1.44/0.55    ( ! [X4] : (r1_tarski(k2_xboole_0(sK1,sK2),X4) | ~r2_hidden(sK0,X4)) )),
% 1.44/0.55    inference(duplicate_literal_removal,[],[f94])).
% 1.44/0.55  fof(f94,plain,(
% 1.44/0.55    ( ! [X4] : (r1_tarski(k2_xboole_0(sK1,sK2),X4) | ~r2_hidden(sK0,X4) | ~r2_hidden(sK0,X4)) )),
% 1.44/0.55    inference(superposition,[],[f76,f68])).
% 1.44/0.55  fof(f76,plain,(
% 1.44/0.55    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.44/0.55    inference(definition_unfolding,[],[f61,f66])).
% 1.44/0.55  fof(f61,plain,(
% 1.44/0.55    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f37])).
% 1.44/0.55  fof(f37,plain,(
% 1.44/0.55    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.44/0.55    inference(flattening,[],[f36])).
% 1.44/0.55  fof(f36,plain,(
% 1.44/0.55    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.44/0.55    inference(nnf_transformation,[],[f15])).
% 1.44/0.55  fof(f15,axiom,(
% 1.44/0.55    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.44/0.55  % SZS output end Proof for theBenchmark
% 1.44/0.55  % (25208)------------------------------
% 1.44/0.55  % (25208)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (25208)Termination reason: Refutation
% 1.44/0.55  
% 1.44/0.55  % (25208)Memory used [KB]: 10746
% 1.44/0.55  % (25208)Time elapsed: 0.122 s
% 1.44/0.55  % (25208)------------------------------
% 1.44/0.55  % (25208)------------------------------
% 1.44/0.56  % (25183)Success in time 0.187 s
%------------------------------------------------------------------------------
