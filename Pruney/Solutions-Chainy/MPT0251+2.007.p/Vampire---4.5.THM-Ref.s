%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:35 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 655 expanded)
%              Number of leaves         :   21 ( 216 expanded)
%              Depth                    :   20
%              Number of atoms          :  248 (1070 expanded)
%              Number of equality atoms :   77 ( 631 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f432,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f237,f99,f407])).

fof(f407,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = X1 ) ),
    inference(forward_demodulation,[],[f404,f84])).

fof(f84,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f47,f81])).

fof(f81,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f54,f80])).

fof(f80,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f68,f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

% (32683)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f68,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f47,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f404,plain,(
    ! [X0,X1] :
      ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(backward_demodulation,[],[f192,f401])).

fof(f401,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(subsumption_resolution,[],[f394,f94])).

fof(f94,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

% (32671)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% (32671)Refutation not found, incomplete strategy% (32671)------------------------------
% (32671)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (32671)Termination reason: Refutation not found, incomplete strategy

% (32671)Memory used [KB]: 1663
% (32671)Time elapsed: 0.115 s
% (32671)------------------------------
% (32671)------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f394,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_xboole_0(X0,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(superposition,[],[f339,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f339,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(backward_demodulation,[],[f323,f334])).

fof(f334,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f254,f318])).

fof(f318,plain,(
    ! [X16] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X16) ),
    inference(resolution,[],[f171,f306])).

fof(f306,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f305,f256])).

fof(f256,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f252,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(superposition,[],[f97,f61])).

fof(f97,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f252,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    inference(superposition,[],[f85,f131])).

fof(f131,plain,(
    ! [X0] : k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[],[f84,f86])).

fof(f86,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f52,f80,f80])).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f85,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f51,f81])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f305,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f301,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f301,plain,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f299])).

fof(f299,plain,(
    ! [X1] :
      ( X1 != X1
      | r1_xboole_0(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f89,f254])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f67,f55])).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f171,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1,X0),X0)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(factoring,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f254,plain,(
    ! [X1] : k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(forward_demodulation,[],[f250,f131])).

fof(f250,plain,(
    ! [X1] : k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[],[f131,f88])).

fof(f88,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f57,f81,f55,f81])).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f323,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f251,f318])).

fof(f251,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(superposition,[],[f87,f131])).

fof(f87,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) ),
    inference(definition_unfolding,[],[f56,f55,f55,f81])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f192,plain,(
    ! [X0,X1] :
      ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X0,X0)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f88,f61])).

fof(f99,plain,(
    sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(backward_demodulation,[],[f83,f86])).

fof(f83,plain,(
    sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f46,f81,f82])).

% (32656)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
fof(f82,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f48,f80])).

fof(f48,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f46,plain,(
    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f237,plain,(
    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(resolution,[],[f152,f45])).

fof(f45,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f152,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r1_tarski(k3_enumset1(X0,X0,X0,X0,sK0),sK1) ) ),
    inference(resolution,[],[f91,f45])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f77,f80])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:05:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.53  % (32661)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.54  % (32660)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (32670)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.54  % (32662)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.54  % (32677)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.55  % (32678)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.41/0.55  % (32668)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.41/0.55  % (32669)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.41/0.55  % (32676)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.41/0.56  % (32670)Refutation not found, incomplete strategy% (32670)------------------------------
% 1.41/0.56  % (32670)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (32668)Refutation not found, incomplete strategy% (32668)------------------------------
% 1.41/0.56  % (32668)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (32668)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.56  
% 1.41/0.56  % (32668)Memory used [KB]: 1663
% 1.41/0.56  % (32668)Time elapsed: 0.135 s
% 1.41/0.56  % (32668)------------------------------
% 1.41/0.56  % (32668)------------------------------
% 1.41/0.56  % (32670)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.56  
% 1.41/0.56  % (32670)Memory used [KB]: 10618
% 1.41/0.56  % (32670)Time elapsed: 0.117 s
% 1.41/0.56  % (32670)------------------------------
% 1.41/0.56  % (32670)------------------------------
% 1.59/0.58  % (32659)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.59/0.59  % (32676)Refutation found. Thanks to Tanya!
% 1.59/0.59  % SZS status Theorem for theBenchmark
% 1.59/0.59  % SZS output start Proof for theBenchmark
% 1.59/0.59  fof(f432,plain,(
% 1.59/0.59    $false),
% 1.59/0.59    inference(unit_resulting_resolution,[],[f237,f99,f407])).
% 1.59/0.59  fof(f407,plain,(
% 1.59/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = X1) )),
% 1.59/0.59    inference(forward_demodulation,[],[f404,f84])).
% 1.59/0.59  fof(f84,plain,(
% 1.59/0.59    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 1.59/0.59    inference(definition_unfolding,[],[f47,f81])).
% 1.59/0.59  fof(f81,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.59/0.59    inference(definition_unfolding,[],[f54,f80])).
% 1.59/0.59  fof(f80,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.59/0.59    inference(definition_unfolding,[],[f53,f79])).
% 1.59/0.59  fof(f79,plain,(
% 1.59/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.59/0.59    inference(definition_unfolding,[],[f68,f78])).
% 1.59/0.59  fof(f78,plain,(
% 1.59/0.59    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f17])).
% 1.59/0.59  % (32683)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.59/0.59  fof(f17,axiom,(
% 1.59/0.59    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.59/0.59  fof(f68,plain,(
% 1.59/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f16])).
% 1.59/0.59  fof(f16,axiom,(
% 1.59/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.59/0.59  fof(f53,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f15])).
% 1.59/0.59  fof(f15,axiom,(
% 1.59/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.59/0.59  fof(f54,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.59/0.59    inference(cnf_transformation,[],[f18])).
% 1.59/0.59  fof(f18,axiom,(
% 1.59/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.59/0.59  fof(f47,plain,(
% 1.59/0.59    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.59/0.59    inference(cnf_transformation,[],[f7])).
% 1.59/0.59  fof(f7,axiom,(
% 1.59/0.59    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.59/0.59  fof(f404,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0)) | ~r1_tarski(X0,X1)) )),
% 1.59/0.59    inference(backward_demodulation,[],[f192,f401])).
% 1.59/0.59  fof(f401,plain,(
% 1.59/0.59    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.59/0.59    inference(subsumption_resolution,[],[f394,f94])).
% 1.59/0.59  fof(f94,plain,(
% 1.59/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.59/0.59    inference(equality_resolution,[],[f64])).
% 1.59/0.59  fof(f64,plain,(
% 1.59/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.59/0.59    inference(cnf_transformation,[],[f36])).
% 1.59/0.59  fof(f36,plain,(
% 1.59/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.59/0.59    inference(flattening,[],[f35])).
% 1.59/0.59  fof(f35,plain,(
% 1.59/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.59/0.59    inference(nnf_transformation,[],[f5])).
% 1.59/0.59  % (32671)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.59/0.59  % (32671)Refutation not found, incomplete strategy% (32671)------------------------------
% 1.59/0.59  % (32671)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.59  % (32671)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.59  
% 1.59/0.59  % (32671)Memory used [KB]: 1663
% 1.59/0.59  % (32671)Time elapsed: 0.115 s
% 1.59/0.59  % (32671)------------------------------
% 1.59/0.59  % (32671)------------------------------
% 1.59/0.59  fof(f5,axiom,(
% 1.59/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.59/0.59  fof(f394,plain,(
% 1.59/0.59    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0) | ~r1_tarski(X0,X0)) )),
% 1.59/0.59    inference(superposition,[],[f339,f61])).
% 1.59/0.59  fof(f61,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f25])).
% 1.59/0.59  fof(f25,plain,(
% 1.59/0.59    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.59/0.59    inference(ennf_transformation,[],[f8])).
% 1.59/0.59  fof(f8,axiom,(
% 1.59/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.59/0.59  fof(f339,plain,(
% 1.59/0.59    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 1.59/0.59    inference(backward_demodulation,[],[f323,f334])).
% 1.59/0.59  fof(f334,plain,(
% 1.59/0.59    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.59/0.59    inference(superposition,[],[f254,f318])).
% 1.59/0.59  fof(f318,plain,(
% 1.59/0.59    ( ! [X16] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X16)) )),
% 1.59/0.59    inference(resolution,[],[f171,f306])).
% 1.59/0.59  fof(f306,plain,(
% 1.59/0.59    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 1.59/0.59    inference(subsumption_resolution,[],[f305,f256])).
% 1.59/0.59  fof(f256,plain,(
% 1.59/0.59    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | r2_hidden(X0,X1)) )),
% 1.59/0.59    inference(resolution,[],[f252,f103])).
% 1.59/0.59  fof(f103,plain,(
% 1.59/0.59    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.59/0.59    inference(superposition,[],[f97,f61])).
% 1.59/0.59  fof(f97,plain,(
% 1.59/0.59    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X1)) )),
% 1.59/0.59    inference(equality_resolution,[],[f70])).
% 1.59/0.59  fof(f70,plain,(
% 1.59/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.59/0.59    inference(cnf_transformation,[],[f42])).
% 1.59/0.59  fof(f42,plain,(
% 1.59/0.59    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.59/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).
% 1.59/0.59  fof(f41,plain,(
% 1.59/0.59    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.59/0.59    introduced(choice_axiom,[])).
% 1.59/0.59  fof(f40,plain,(
% 1.59/0.59    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.59/0.59    inference(rectify,[],[f39])).
% 1.59/0.59  fof(f39,plain,(
% 1.59/0.59    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.59/0.59    inference(flattening,[],[f38])).
% 1.59/0.59  fof(f38,plain,(
% 1.59/0.59    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.59/0.59    inference(nnf_transformation,[],[f3])).
% 1.59/0.59  fof(f3,axiom,(
% 1.59/0.59    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.59/0.59  fof(f252,plain,(
% 1.59/0.59    ( ! [X1] : (r1_tarski(k1_xboole_0,X1)) )),
% 1.59/0.59    inference(superposition,[],[f85,f131])).
% 1.59/0.59  fof(f131,plain,(
% 1.59/0.59    ( ! [X0] : (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0) )),
% 1.59/0.59    inference(superposition,[],[f84,f86])).
% 1.59/0.59  fof(f86,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 1.59/0.59    inference(definition_unfolding,[],[f52,f80,f80])).
% 1.59/0.59  fof(f52,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f13])).
% 1.59/0.59  fof(f13,axiom,(
% 1.59/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.59/0.59  fof(f85,plain,(
% 1.59/0.59    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 1.59/0.59    inference(definition_unfolding,[],[f51,f81])).
% 1.59/0.59  fof(f51,plain,(
% 1.59/0.59    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.59/0.59    inference(cnf_transformation,[],[f11])).
% 1.59/0.59  fof(f11,axiom,(
% 1.59/0.59    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.59/0.59  fof(f305,plain,(
% 1.59/0.59    ( ! [X2,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,X2)) )),
% 1.59/0.59    inference(resolution,[],[f301,f60])).
% 1.59/0.59  fof(f60,plain,(
% 1.59/0.59    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f34])).
% 1.59/0.59  fof(f34,plain,(
% 1.59/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.59/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f33])).
% 1.59/0.59  fof(f33,plain,(
% 1.59/0.59    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.59/0.59    introduced(choice_axiom,[])).
% 1.59/0.59  fof(f24,plain,(
% 1.59/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.59/0.59    inference(ennf_transformation,[],[f22])).
% 1.59/0.59  fof(f22,plain,(
% 1.59/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.59/0.59    inference(rectify,[],[f4])).
% 1.59/0.59  fof(f4,axiom,(
% 1.59/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.59/0.59  fof(f301,plain,(
% 1.59/0.59    ( ! [X1] : (r1_xboole_0(X1,k1_xboole_0)) )),
% 1.59/0.59    inference(trivial_inequality_removal,[],[f299])).
% 1.59/0.59  fof(f299,plain,(
% 1.59/0.59    ( ! [X1] : (X1 != X1 | r1_xboole_0(X1,k1_xboole_0)) )),
% 1.59/0.59    inference(superposition,[],[f89,f254])).
% 1.59/0.59  fof(f89,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 | r1_xboole_0(X0,X1)) )),
% 1.59/0.59    inference(definition_unfolding,[],[f67,f55])).
% 1.59/0.59  fof(f55,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.59/0.59    inference(cnf_transformation,[],[f6])).
% 1.59/0.59  fof(f6,axiom,(
% 1.59/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.59/0.59  fof(f67,plain,(
% 1.59/0.59    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 1.59/0.59    inference(cnf_transformation,[],[f37])).
% 1.59/0.59  fof(f37,plain,(
% 1.59/0.59    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.59/0.59    inference(nnf_transformation,[],[f12])).
% 1.59/0.59  fof(f12,axiom,(
% 1.59/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.59/0.59  fof(f171,plain,(
% 1.59/0.59    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1,X0),X0) | k3_xboole_0(X0,X1) = X0) )),
% 1.59/0.59    inference(factoring,[],[f72])).
% 1.59/0.59  fof(f72,plain,(
% 1.59/0.59    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X0) | k3_xboole_0(X0,X1) = X2) )),
% 1.59/0.59    inference(cnf_transformation,[],[f42])).
% 1.59/0.59  fof(f254,plain,(
% 1.59/0.59    ( ! [X1] : (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1) )),
% 1.59/0.59    inference(forward_demodulation,[],[f250,f131])).
% 1.59/0.59  fof(f250,plain,(
% 1.59/0.59    ( ! [X1] : (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))) )),
% 1.59/0.59    inference(superposition,[],[f131,f88])).
% 1.59/0.59  fof(f88,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 1.59/0.59    inference(definition_unfolding,[],[f57,f81,f55,f81])).
% 1.59/0.59  fof(f57,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f9])).
% 1.59/0.59  fof(f9,axiom,(
% 1.59/0.59    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.59/0.59  fof(f323,plain,(
% 1.59/0.59    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 1.59/0.59    inference(backward_demodulation,[],[f251,f318])).
% 1.59/0.59  fof(f251,plain,(
% 1.59/0.59    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 1.59/0.59    inference(superposition,[],[f87,f131])).
% 1.59/0.59  fof(f87,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1))) )),
% 1.59/0.59    inference(definition_unfolding,[],[f56,f55,f55,f81])).
% 1.59/0.59  fof(f56,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f10])).
% 1.59/0.59  fof(f10,axiom,(
% 1.59/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.59/0.59  fof(f192,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X0,X0))) | ~r1_tarski(X0,X1)) )),
% 1.59/0.59    inference(superposition,[],[f88,f61])).
% 1.59/0.59  fof(f99,plain,(
% 1.59/0.59    sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 1.59/0.59    inference(backward_demodulation,[],[f83,f86])).
% 1.59/0.59  fof(f83,plain,(
% 1.59/0.59    sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))),
% 1.59/0.59    inference(definition_unfolding,[],[f46,f81,f82])).
% 1.59/0.59  % (32656)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.59/0.59  fof(f82,plain,(
% 1.59/0.59    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.59/0.59    inference(definition_unfolding,[],[f48,f80])).
% 1.59/0.59  fof(f48,plain,(
% 1.59/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f14])).
% 1.59/0.59  fof(f14,axiom,(
% 1.59/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.59/0.59  fof(f46,plain,(
% 1.59/0.59    sK1 != k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.59/0.59    inference(cnf_transformation,[],[f28])).
% 1.59/0.59  fof(f28,plain,(
% 1.59/0.59    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1)),
% 1.59/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f27])).
% 1.59/0.59  fof(f27,plain,(
% 1.59/0.59    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1))),
% 1.59/0.59    introduced(choice_axiom,[])).
% 1.59/0.59  fof(f23,plain,(
% 1.59/0.59    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 1.59/0.59    inference(ennf_transformation,[],[f21])).
% 1.59/0.59  fof(f21,negated_conjecture,(
% 1.59/0.59    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.59/0.59    inference(negated_conjecture,[],[f20])).
% 1.59/0.59  fof(f20,conjecture,(
% 1.59/0.59    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 1.59/0.59  fof(f237,plain,(
% 1.59/0.59    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)),
% 1.59/0.59    inference(resolution,[],[f152,f45])).
% 1.59/0.59  fof(f45,plain,(
% 1.59/0.59    r2_hidden(sK0,sK1)),
% 1.59/0.59    inference(cnf_transformation,[],[f28])).
% 1.59/0.59  fof(f152,plain,(
% 1.59/0.59    ( ! [X0] : (~r2_hidden(X0,sK1) | r1_tarski(k3_enumset1(X0,X0,X0,X0,sK0),sK1)) )),
% 1.59/0.59    inference(resolution,[],[f91,f45])).
% 1.59/0.59  fof(f91,plain,(
% 1.59/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 1.59/0.59    inference(definition_unfolding,[],[f77,f80])).
% 1.59/0.59  fof(f77,plain,(
% 1.59/0.59    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f44])).
% 1.59/0.59  fof(f44,plain,(
% 1.59/0.59    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.59/0.59    inference(flattening,[],[f43])).
% 1.59/0.59  fof(f43,plain,(
% 1.59/0.59    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.59/0.59    inference(nnf_transformation,[],[f19])).
% 1.59/0.59  fof(f19,axiom,(
% 1.59/0.59    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.59/0.59  % SZS output end Proof for theBenchmark
% 1.59/0.59  % (32676)------------------------------
% 1.59/0.59  % (32676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.59  % (32676)Termination reason: Refutation
% 1.59/0.59  
% 1.59/0.59  % (32676)Memory used [KB]: 6652
% 1.59/0.59  % (32676)Time elapsed: 0.149 s
% 1.59/0.59  % (32676)------------------------------
% 1.59/0.59  % (32676)------------------------------
% 1.59/0.59  % (32653)Success in time 0.22 s
%------------------------------------------------------------------------------
