%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:35 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 177 expanded)
%              Number of leaves         :   18 (  52 expanded)
%              Depth                    :   13
%              Number of atoms          :  249 ( 514 expanded)
%              Number of equality atoms :  159 ( 324 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f274,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f39,f38,f92,f267])).

fof(f267,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_enumset1(sK0,sK0,sK0,sK1,sK2))
      | sK1 = X0
      | sK2 = X0 ) ),
    inference(duplicate_literal_removal,[],[f262])).

fof(f262,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_enumset1(sK0,sK0,sK0,sK1,sK2))
      | sK1 = X0
      | sK1 = X0
      | sK2 = X0 ) ),
    inference(superposition,[],[f93,f256])).

% (15139)Termination reason: Refutation not found, incomplete strategy

fof(f256,plain,(
    k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k3_enumset1(sK0,sK0,sK0,sK1,sK2) ),
    inference(forward_demodulation,[],[f255,f76])).

% (15139)Memory used [KB]: 1791
% (15139)Time elapsed: 0.162 s
fof(f76,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X0,X0,X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f54,f69,f68,f71,f70])).

% (15139)------------------------------
% (15139)------------------------------
fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f69])).

fof(f46,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f71,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f42,f70])).

fof(f42,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f48,f47])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f53,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f255,plain,(
    k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ),
    inference(resolution,[],[f165,f72])).

fof(f72,plain,(
    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f37,f71,f70])).

fof(f37,plain,(
    r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( sK0 != sK2
    & sK0 != sK1
    & r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) )
   => ( sK0 != sK2
      & sK0 != sK1
      & r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & X0 != X1
      & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X2
          & X0 != X1
          & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

fof(f165,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 ) ),
    inference(forward_demodulation,[],[f164,f110])).

fof(f110,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f102,f106])).

fof(f106,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(resolution,[],[f105,f43])).

fof(f43,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f105,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k5_xboole_0(X1,X1)) ),
    inference(subsumption_resolution,[],[f104,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f23])).

% (15152)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f104,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X1)) ) ),
    inference(factoring,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f102,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
    inference(subsumption_resolution,[],[f101,f85])).

fof(f85,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f101,plain,(
    ! [X0] :
      ( k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0
      | ~ r1_tarski(X0,X0) ) ),
    inference(superposition,[],[f74,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f74,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f44,f68])).

fof(f44,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f164,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k1_xboole_0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f154,f106])).

fof(f154,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f75,f49])).

fof(f75,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f45,f68,f68])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f93,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f60,f69])).

fof(f60,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK4(X0,X1,X2,X3) != X2
              & sK4(X0,X1,X2,X3) != X1
              & sK4(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( sK4(X0,X1,X2,X3) = X2
            | sK4(X0,X1,X2,X3) = X1
            | sK4(X0,X1,X2,X3) = X0
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).

fof(f35,plain,(
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
     => ( ( ( sK4(X0,X1,X2,X3) != X2
            & sK4(X0,X1,X2,X3) != X1
            & sK4(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( sK4(X0,X1,X2,X3) = X2
          | sK4(X0,X1,X2,X3) = X1
          | sK4(X0,X1,X2,X3) = X0
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f92,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f61,f69])).

fof(f61,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f38,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f39,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:43:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.21/0.54  % (15130)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.47/0.56  % (15127)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.47/0.57  % (15151)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.47/0.57  % (15147)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.47/0.57  % (15128)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.47/0.57  % (15129)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.47/0.57  % (15143)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.47/0.58  % (15131)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.47/0.58  % (15125)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.47/0.58  % (15139)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.47/0.59  % (15148)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.47/0.59  % (15140)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.47/0.59  % (15139)Refutation not found, incomplete strategy% (15139)------------------------------
% 1.47/0.59  % (15139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.60  % (15147)Refutation found. Thanks to Tanya!
% 1.47/0.60  % SZS status Theorem for theBenchmark
% 1.47/0.60  % SZS output start Proof for theBenchmark
% 1.47/0.60  fof(f274,plain,(
% 1.47/0.60    $false),
% 1.47/0.60    inference(unit_resulting_resolution,[],[f39,f38,f92,f267])).
% 1.47/0.60  fof(f267,plain,(
% 1.47/0.60    ( ! [X0] : (~r2_hidden(X0,k3_enumset1(sK0,sK0,sK0,sK1,sK2)) | sK1 = X0 | sK2 = X0) )),
% 1.47/0.60    inference(duplicate_literal_removal,[],[f262])).
% 1.47/0.60  fof(f262,plain,(
% 1.47/0.60    ( ! [X0] : (~r2_hidden(X0,k3_enumset1(sK0,sK0,sK0,sK1,sK2)) | sK1 = X0 | sK1 = X0 | sK2 = X0) )),
% 1.47/0.60    inference(superposition,[],[f93,f256])).
% 1.47/0.60  % (15139)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.60  
% 1.47/0.60  fof(f256,plain,(
% 1.47/0.60    k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k3_enumset1(sK0,sK0,sK0,sK1,sK2)),
% 1.47/0.60    inference(forward_demodulation,[],[f255,f76])).
% 1.47/0.60  % (15139)Memory used [KB]: 1791
% 1.47/0.60  % (15139)Time elapsed: 0.162 s
% 1.47/0.60  fof(f76,plain,(
% 1.47/0.60    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X0,X0,X0,X0,X0))))) )),
% 1.47/0.60    inference(definition_unfolding,[],[f54,f69,f68,f71,f70])).
% 1.47/0.60  % (15139)------------------------------
% 1.47/0.60  % (15139)------------------------------
% 1.47/0.60  fof(f70,plain,(
% 1.47/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.47/0.60    inference(definition_unfolding,[],[f46,f69])).
% 1.47/0.60  fof(f46,plain,(
% 1.47/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.47/0.60    inference(cnf_transformation,[],[f14])).
% 1.47/0.60  fof(f14,axiom,(
% 1.47/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.47/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.47/0.60  fof(f71,plain,(
% 1.47/0.60    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.47/0.60    inference(definition_unfolding,[],[f42,f70])).
% 1.47/0.60  fof(f42,plain,(
% 1.47/0.60    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.47/0.60    inference(cnf_transformation,[],[f13])).
% 1.47/0.60  fof(f13,axiom,(
% 1.47/0.60    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.47/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.47/0.60  fof(f68,plain,(
% 1.47/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.47/0.60    inference(definition_unfolding,[],[f48,f47])).
% 1.47/0.60  fof(f47,plain,(
% 1.47/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.47/0.60    inference(cnf_transformation,[],[f6])).
% 1.47/0.60  fof(f6,axiom,(
% 1.47/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.47/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.47/0.60  fof(f48,plain,(
% 1.47/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.47/0.60    inference(cnf_transformation,[],[f10])).
% 1.47/0.60  fof(f10,axiom,(
% 1.47/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.47/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.47/0.60  fof(f69,plain,(
% 1.47/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.47/0.60    inference(definition_unfolding,[],[f53,f59])).
% 1.47/0.60  fof(f59,plain,(
% 1.47/0.60    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.47/0.60    inference(cnf_transformation,[],[f16])).
% 1.47/0.60  fof(f16,axiom,(
% 1.47/0.60    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.47/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.47/0.60  fof(f53,plain,(
% 1.47/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.47/0.60    inference(cnf_transformation,[],[f15])).
% 1.47/0.60  fof(f15,axiom,(
% 1.47/0.60    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.47/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.47/0.60  fof(f54,plain,(
% 1.47/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 1.47/0.60    inference(cnf_transformation,[],[f12])).
% 1.47/0.60  fof(f12,axiom,(
% 1.47/0.60    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 1.47/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
% 1.47/0.60  fof(f255,plain,(
% 1.47/0.60    k3_enumset1(sK1,sK1,sK1,sK1,sK2) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),
% 1.47/0.60    inference(resolution,[],[f165,f72])).
% 1.47/0.60  fof(f72,plain,(
% 1.47/0.60    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2))),
% 1.47/0.60    inference(definition_unfolding,[],[f37,f71,f70])).
% 1.47/0.60  fof(f37,plain,(
% 1.47/0.60    r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2))),
% 1.47/0.60    inference(cnf_transformation,[],[f26])).
% 1.47/0.60  fof(f26,plain,(
% 1.47/0.60    sK0 != sK2 & sK0 != sK1 & r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2))),
% 1.47/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f25])).
% 1.47/0.60  fof(f25,plain,(
% 1.47/0.60    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))) => (sK0 != sK2 & sK0 != sK1 & r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)))),
% 1.47/0.60    introduced(choice_axiom,[])).
% 1.47/0.60  fof(f20,plain,(
% 1.47/0.60    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.47/0.60    inference(ennf_transformation,[],[f18])).
% 1.47/0.60  fof(f18,negated_conjecture,(
% 1.47/0.60    ~! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.47/0.60    inference(negated_conjecture,[],[f17])).
% 1.47/0.60  fof(f17,conjecture,(
% 1.47/0.60    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.47/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).
% 1.47/0.60  fof(f165,plain,(
% 1.47/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1) )),
% 1.47/0.60    inference(forward_demodulation,[],[f164,f110])).
% 1.47/0.60  fof(f110,plain,(
% 1.47/0.60    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.47/0.60    inference(backward_demodulation,[],[f102,f106])).
% 1.47/0.60  fof(f106,plain,(
% 1.47/0.60    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.47/0.60    inference(resolution,[],[f105,f43])).
% 1.47/0.60  fof(f43,plain,(
% 1.47/0.60    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.47/0.60    inference(cnf_transformation,[],[f28])).
% 1.47/0.60  fof(f28,plain,(
% 1.47/0.60    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 1.47/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f27])).
% 1.47/0.60  fof(f27,plain,(
% 1.47/0.60    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.47/0.60    introduced(choice_axiom,[])).
% 1.47/0.60  fof(f21,plain,(
% 1.47/0.60    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.47/0.60    inference(ennf_transformation,[],[f4])).
% 1.47/0.60  fof(f4,axiom,(
% 1.47/0.60    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.47/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.47/0.60  fof(f105,plain,(
% 1.47/0.60    ( ! [X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X1))) )),
% 1.47/0.60    inference(subsumption_resolution,[],[f104,f56])).
% 1.47/0.60  fof(f56,plain,(
% 1.47/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 1.47/0.60    inference(cnf_transformation,[],[f31])).
% 1.47/0.60  fof(f31,plain,(
% 1.47/0.60    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 1.47/0.60    inference(nnf_transformation,[],[f23])).
% 1.47/0.61  % (15152)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.47/0.61  fof(f23,plain,(
% 1.47/0.61    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.47/0.61    inference(ennf_transformation,[],[f3])).
% 1.47/0.61  fof(f3,axiom,(
% 1.47/0.61    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.47/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.47/0.61  fof(f104,plain,(
% 1.47/0.61    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X1))) )),
% 1.47/0.61    inference(factoring,[],[f55])).
% 1.47/0.61  fof(f55,plain,(
% 1.47/0.61    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 1.47/0.61    inference(cnf_transformation,[],[f31])).
% 1.47/0.61  fof(f102,plain,(
% 1.47/0.61    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0) )),
% 1.47/0.61    inference(subsumption_resolution,[],[f101,f85])).
% 1.47/0.61  fof(f85,plain,(
% 1.47/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.47/0.61    inference(equality_resolution,[],[f51])).
% 1.47/0.61  fof(f51,plain,(
% 1.47/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.47/0.61    inference(cnf_transformation,[],[f30])).
% 1.47/0.61  fof(f30,plain,(
% 1.47/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.47/0.61    inference(flattening,[],[f29])).
% 1.47/0.61  fof(f29,plain,(
% 1.47/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.47/0.61    inference(nnf_transformation,[],[f5])).
% 1.47/0.61  fof(f5,axiom,(
% 1.47/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.47/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.47/0.61  fof(f101,plain,(
% 1.47/0.61    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 | ~r1_tarski(X0,X0)) )),
% 1.47/0.61    inference(superposition,[],[f74,f49])).
% 1.47/0.61  fof(f49,plain,(
% 1.47/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.47/0.61    inference(cnf_transformation,[],[f22])).
% 1.47/0.61  fof(f22,plain,(
% 1.47/0.61    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.47/0.61    inference(ennf_transformation,[],[f8])).
% 1.47/0.61  fof(f8,axiom,(
% 1.47/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.47/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.47/0.61  fof(f74,plain,(
% 1.47/0.61    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0) )),
% 1.47/0.61    inference(definition_unfolding,[],[f44,f68])).
% 1.47/0.61  fof(f44,plain,(
% 1.47/0.61    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.47/0.61    inference(cnf_transformation,[],[f19])).
% 1.47/0.61  fof(f19,plain,(
% 1.47/0.61    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.47/0.61    inference(rectify,[],[f2])).
% 1.47/0.61  fof(f2,axiom,(
% 1.47/0.61    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.47/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.47/0.61  fof(f164,plain,(
% 1.47/0.61    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k1_xboole_0) | ~r1_tarski(X0,X1)) )),
% 1.47/0.61    inference(forward_demodulation,[],[f154,f106])).
% 1.47/0.61  fof(f154,plain,(
% 1.47/0.61    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,X0)) | ~r1_tarski(X0,X1)) )),
% 1.47/0.61    inference(superposition,[],[f75,f49])).
% 1.47/0.61  fof(f75,plain,(
% 1.47/0.61    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 1.47/0.61    inference(definition_unfolding,[],[f45,f68,f68])).
% 1.47/0.61  fof(f45,plain,(
% 1.47/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.47/0.61    inference(cnf_transformation,[],[f1])).
% 1.47/0.61  fof(f1,axiom,(
% 1.47/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.47/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.47/0.61  fof(f93,plain,(
% 1.47/0.61    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 1.47/0.61    inference(equality_resolution,[],[f84])).
% 1.47/0.61  fof(f84,plain,(
% 1.47/0.61    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 1.47/0.61    inference(definition_unfolding,[],[f60,f69])).
% 1.47/0.61  fof(f60,plain,(
% 1.47/0.61    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.47/0.61    inference(cnf_transformation,[],[f36])).
% 1.47/0.61  fof(f36,plain,(
% 1.47/0.61    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.47/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).
% 1.47/0.61  fof(f35,plain,(
% 1.47/0.61    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 1.47/0.61    introduced(choice_axiom,[])).
% 1.47/0.61  fof(f34,plain,(
% 1.47/0.61    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.47/0.61    inference(rectify,[],[f33])).
% 1.47/0.61  fof(f33,plain,(
% 1.47/0.61    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.47/0.61    inference(flattening,[],[f32])).
% 1.47/0.61  fof(f32,plain,(
% 1.47/0.61    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.47/0.61    inference(nnf_transformation,[],[f24])).
% 1.47/0.61  fof(f24,plain,(
% 1.47/0.61    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.47/0.61    inference(ennf_transformation,[],[f11])).
% 1.47/0.61  fof(f11,axiom,(
% 1.47/0.61    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.47/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.47/0.61  fof(f92,plain,(
% 1.47/0.61    ( ! [X2,X5,X1] : (r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2))) )),
% 1.47/0.61    inference(equality_resolution,[],[f91])).
% 1.47/0.61  fof(f91,plain,(
% 1.47/0.61    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X5,X5,X5,X1,X2) != X3) )),
% 1.47/0.61    inference(equality_resolution,[],[f83])).
% 1.47/0.61  fof(f83,plain,(
% 1.47/0.61    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 1.47/0.61    inference(definition_unfolding,[],[f61,f69])).
% 1.47/0.61  fof(f61,plain,(
% 1.47/0.61    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.47/0.61    inference(cnf_transformation,[],[f36])).
% 1.47/0.61  fof(f38,plain,(
% 1.47/0.61    sK0 != sK1),
% 1.47/0.61    inference(cnf_transformation,[],[f26])).
% 1.47/0.61  fof(f39,plain,(
% 1.47/0.61    sK0 != sK2),
% 1.47/0.61    inference(cnf_transformation,[],[f26])).
% 1.47/0.61  % SZS output end Proof for theBenchmark
% 1.47/0.61  % (15147)------------------------------
% 1.47/0.61  % (15147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.61  % (15147)Termination reason: Refutation
% 1.47/0.61  
% 1.47/0.61  % (15147)Memory used [KB]: 6396
% 1.47/0.61  % (15147)Time elapsed: 0.172 s
% 1.47/0.61  % (15147)------------------------------
% 1.47/0.61  % (15147)------------------------------
% 1.47/0.61  % (15153)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.47/0.61  % (15124)Success in time 0.242 s
%------------------------------------------------------------------------------
