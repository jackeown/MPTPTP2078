%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:12 EST 2020

% Result     : Theorem 1.94s
% Output     : Refutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 638 expanded)
%              Number of leaves         :   10 ( 184 expanded)
%              Depth                    :   26
%              Number of atoms          :  202 (3007 expanded)
%              Number of equality atoms :   55 ( 357 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1894,plain,(
    $false ),
    inference(subsumption_resolution,[],[f21,f1871])).

fof(f1871,plain,(
    ! [X6,X7,X5] : k1_enumset1(X5,X6,X7) = k1_enumset1(X6,X5,X7) ),
    inference(superposition,[],[f1644,f746])).

fof(f746,plain,(
    ! [X2,X0,X1] : k2_enumset1(X2,X0,X0,X1) = k1_enumset1(X2,X0,X1) ),
    inference(backward_demodulation,[],[f38,f745])).

fof(f745,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(forward_demodulation,[],[f733,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(forward_demodulation,[],[f106,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f106,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(superposition,[],[f35,f23])).

fof(f23,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f733,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(backward_demodulation,[],[f190,f718])).

fof(f718,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X1,X1) ),
    inference(superposition,[],[f692,f109])).

fof(f692,plain,(
    ! [X24,X25] : k2_tarski(X24,X25) = k2_xboole_0(k2_tarski(X24,X25),k1_tarski(X25)) ),
    inference(superposition,[],[f662,f110])).

fof(f110,plain,(
    ! [X4,X3] : k2_tarski(X3,X4) = k2_xboole_0(k1_tarski(X3),k1_tarski(X4)) ),
    inference(forward_demodulation,[],[f107,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(superposition,[],[f44,f38])).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(forward_demodulation,[],[f40,f23])).

fof(f40,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f38,f24])).

fof(f107,plain,(
    ! [X4,X3] : k2_xboole_0(k1_tarski(X3),k1_tarski(X4)) = k2_enumset1(X3,X3,X3,X4) ),
    inference(superposition,[],[f35,f73])).

fof(f73,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(superposition,[],[f61,f24])).

fof(f61,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(superposition,[],[f41,f46])).

fof(f46,plain,(
    ! [X0] : k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0)) ),
    inference(superposition,[],[f44,f22])).

fof(f22,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k2_enumset1(X1,X0,X0,X0) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0)) ),
    inference(superposition,[],[f38,f22])).

fof(f662,plain,(
    ! [X14,X13] : k2_xboole_0(X13,X14) = k2_xboole_0(k2_xboole_0(X13,X14),X14) ),
    inference(resolution,[],[f657,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,X0,X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f11])).

fof(f11,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f657,plain,(
    ! [X0,X1] : sP0(X0,k2_xboole_0(X1,X0),k2_xboole_0(X1,X0)) ),
    inference(subsumption_resolution,[],[f656,f239])).

fof(f239,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK4(X4,X5,X5),X4)
      | sP0(X4,X5,X5) ) ),
    inference(subsumption_resolution,[],[f231,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
              & ~ r2_hidden(sK4(X0,X1,X2),X1) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( r2_hidden(sK4(X0,X1,X2),X0)
            | r2_hidden(sK4(X0,X1,X2),X1)
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X0)
                & ~ r2_hidden(X4,X1) ) )
            & ( r2_hidden(X4,X0)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f18])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X3,X1) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X0)
            | r2_hidden(X3,X1)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
            & ~ r2_hidden(sK4(X0,X1,X2),X1) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( r2_hidden(sK4(X0,X1,X2),X0)
          | r2_hidden(sK4(X0,X1,X2),X1)
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X3,X1) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X0)
              | r2_hidden(X3,X1)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X0)
                & ~ r2_hidden(X4,X1) ) )
            & ( r2_hidden(X4,X0)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f15])).

% (871)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% (872)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% (875)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% (873)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% (873)Refutation not found, incomplete strategy% (873)------------------------------
% (873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (873)Termination reason: Refutation not found, incomplete strategy

% (873)Memory used [KB]: 1663
% (873)Time elapsed: 0.118 s
% (873)------------------------------
% (873)------------------------------
% (876)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% (876)Refutation not found, incomplete strategy% (876)------------------------------
% (876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (876)Termination reason: Refutation not found, incomplete strategy

% (876)Memory used [KB]: 1663
% (876)Time elapsed: 0.108 s
% (876)------------------------------
% (876)------------------------------
% (834)Refutation not found, incomplete strategy% (834)------------------------------
% (834)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (834)Termination reason: Refutation not found, incomplete strategy

% (834)Memory used [KB]: 6140
% (834)Time elapsed: 0.286 s
% (834)------------------------------
% (834)------------------------------
% (874)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
fof(f15,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f231,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK4(X4,X5,X5),X4)
      | r2_hidden(sK4(X4,X5,X5),X5)
      | sP0(X4,X5,X5) ) ),
    inference(factoring,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f656,plain,(
    ! [X0,X1] :
      ( sP0(X0,k2_xboole_0(X1,X0),k2_xboole_0(X1,X0))
      | ~ r2_hidden(sK4(X0,k2_xboole_0(X1,X0),k2_xboole_0(X1,X0)),X0) ) ),
    inference(duplicate_literal_removal,[],[f631])).

% (877)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
fof(f631,plain,(
    ! [X0,X1] :
      ( sP0(X0,k2_xboole_0(X1,X0),k2_xboole_0(X1,X0))
      | ~ r2_hidden(sK4(X0,k2_xboole_0(X1,X0),k2_xboole_0(X1,X0)),X0)
      | sP0(X0,k2_xboole_0(X1,X0),k2_xboole_0(X1,X0)) ) ),
    inference(resolution,[],[f608,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f608,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X1),k2_xboole_0(X2,X0))
      | sP0(X0,X1,X1) ) ),
    inference(resolution,[],[f255,f36])).

fof(f36,plain,(
    ! [X0,X1] : sP0(X1,X0,k2_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f255,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ sP0(X6,X9,X8)
      | r2_hidden(sK4(X6,X7,X7),X8)
      | sP0(X6,X7,X7) ) ),
    inference(resolution,[],[f239,f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X0)
      | r2_hidden(X4,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f190,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k2_xboole_0(k1_enumset1(X0,X1,X1),k1_tarski(X2)) ),
    inference(resolution,[],[f160,f32])).

fof(f160,plain,(
    ! [X4,X5,X3] : sP0(k1_tarski(X5),k1_enumset1(X3,X4,X4),k2_xboole_0(k1_tarski(X3),k2_tarski(X4,X5))) ),
    inference(superposition,[],[f108,f38])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] : sP0(k1_tarski(X3),k1_enumset1(X0,X1,X2),k2_enumset1(X0,X1,X2,X3)) ),
    inference(superposition,[],[f36,f35])).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_enumset1(X2,X0,X0,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f34,f23])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f1644,plain,(
    ! [X6,X7,X5] : k2_enumset1(X5,X6,X6,X7) = k1_enumset1(X6,X5,X7) ),
    inference(forward_demodulation,[],[f1611,f109])).

fof(f1611,plain,(
    ! [X6,X7,X5] : k2_enumset1(X5,X6,X6,X7) = k2_xboole_0(k2_tarski(X6,X5),k1_tarski(X7)) ),
    inference(superposition,[],[f35,f1590])).

fof(f1590,plain,(
    ! [X0,X1] : k2_tarski(X1,X0) = k1_enumset1(X0,X1,X1) ),
    inference(superposition,[],[f1540,f109])).

fof(f1540,plain,(
    ! [X0,X1] : k2_tarski(X1,X0) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) ),
    inference(resolution,[],[f1535,f32])).

fof(f1535,plain,(
    ! [X6,X5] : sP0(k1_tarski(X5),k2_tarski(X6,X5),k2_tarski(X5,X6)) ),
    inference(superposition,[],[f1353,f1332])).

fof(f1332,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0) ),
    inference(superposition,[],[f1297,f109])).

fof(f1297,plain,(
    ! [X28,X27] : k2_tarski(X27,X28) = k2_xboole_0(k2_tarski(X27,X28),k1_tarski(X27)) ),
    inference(superposition,[],[f1226,f44])).

fof(f1226,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f1225,f32])).

fof(f1225,plain,(
    ! [X0,X1] : sP0(X0,k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(subsumption_resolution,[],[f1224,f239])).

fof(f1224,plain,(
    ! [X0,X1] :
      ( sP0(X0,k2_xboole_0(X0,X1),k2_xboole_0(X0,X1))
      | ~ r2_hidden(sK4(X0,k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)),X0) ) ),
    inference(duplicate_literal_removal,[],[f1195])).

fof(f1195,plain,(
    ! [X0,X1] :
      ( sP0(X0,k2_xboole_0(X0,X1),k2_xboole_0(X0,X1))
      | ~ r2_hidden(sK4(X0,k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)),X0)
      | sP0(X0,k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f1166,f30])).

fof(f1166,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X1),k2_xboole_0(X0,X2))
      | sP0(X0,X1,X1) ) ),
    inference(resolution,[],[f256,f36])).

fof(f256,plain,(
    ! [X12,X10,X13,X11] :
      ( ~ sP0(X13,X10,X12)
      | r2_hidden(sK4(X10,X11,X11),X12)
      | sP0(X10,X11,X11) ) ),
    inference(resolution,[],[f239,f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | r2_hidden(X4,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1353,plain,(
    ! [X12,X10,X11] : sP0(k1_tarski(X12),k2_tarski(X11,X10),k1_enumset1(X10,X11,X12)) ),
    inference(superposition,[],[f129,f1333])).

fof(f1333,plain,(
    ! [X6,X5] : k2_tarski(X6,X5) = k2_tarski(X5,X6) ),
    inference(superposition,[],[f1297,f735])).

fof(f735,plain,(
    ! [X4,X3] : k2_tarski(X4,X3) = k2_xboole_0(k2_tarski(X3,X4),k1_tarski(X3)) ),
    inference(backward_demodulation,[],[f351,f718])).

fof(f351,plain,(
    ! [X4,X3] : k2_tarski(X4,X3) = k2_xboole_0(k1_enumset1(X3,X4,X4),k1_tarski(X3)) ),
    inference(resolution,[],[f334,f32])).

fof(f334,plain,(
    ! [X0,X1] : sP0(k1_tarski(X0),k1_enumset1(X0,X1,X1),k2_tarski(X1,X0)) ),
    inference(superposition,[],[f160,f321])).

fof(f321,plain,(
    ! [X15,X16] : k2_tarski(X15,X16) = k2_xboole_0(k1_tarski(X16),k2_tarski(X15,X16)) ),
    inference(superposition,[],[f304,f110])).

fof(f304,plain,(
    ! [X4,X3] : k2_xboole_0(X4,X3) = k2_xboole_0(X3,k2_xboole_0(X4,X3)) ),
    inference(resolution,[],[f302,f32])).

fof(f302,plain,(
    ! [X0,X1] : sP0(k2_xboole_0(X0,X1),X1,k2_xboole_0(X0,X1)) ),
    inference(subsumption_resolution,[],[f301,f274])).

fof(f274,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X0),k2_xboole_0(X2,X1))
      | sP0(X0,X1,X0) ) ),
    inference(resolution,[],[f243,f36])).

fof(f243,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ sP0(X7,X9,X8)
      | r2_hidden(sK4(X6,X7,X6),X8)
      | sP0(X6,X7,X6) ) ),
    inference(resolution,[],[f238,f27])).

fof(f238,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK4(X2,X3,X2),X3)
      | sP0(X2,X3,X2) ) ),
    inference(subsumption_resolution,[],[f230,f30])).

fof(f230,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK4(X2,X3,X2),X2)
      | r2_hidden(sK4(X2,X3,X2),X3)
      | sP0(X2,X3,X2) ) ),
    inference(factoring,[],[f28])).

fof(f301,plain,(
    ! [X0,X1] :
      ( sP0(k2_xboole_0(X0,X1),X1,k2_xboole_0(X0,X1))
      | ~ r2_hidden(sK4(k2_xboole_0(X0,X1),X1,k2_xboole_0(X0,X1)),k2_xboole_0(X0,X1)) ) ),
    inference(duplicate_literal_removal,[],[f285])).

fof(f285,plain,(
    ! [X0,X1] :
      ( sP0(k2_xboole_0(X0,X1),X1,k2_xboole_0(X0,X1))
      | ~ r2_hidden(sK4(k2_xboole_0(X0,X1),X1,k2_xboole_0(X0,X1)),k2_xboole_0(X0,X1))
      | sP0(k2_xboole_0(X0,X1),X1,k2_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f274,f30])).

fof(f129,plain,(
    ! [X2,X0,X1] : sP0(k1_tarski(X2),k2_tarski(X0,X1),k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[],[f36,f109])).

fof(f21,plain,(
    k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK2,sK1,sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK2,sK1,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f10,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2)
   => k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK2,sK1,sK3) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:22:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (854)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.51  % (847)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (854)Refutation not found, incomplete strategy% (854)------------------------------
% 0.22/0.51  % (854)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (854)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (854)Memory used [KB]: 1663
% 0.22/0.51  % (854)Time elapsed: 0.062 s
% 0.22/0.51  % (854)------------------------------
% 0.22/0.51  % (854)------------------------------
% 0.22/0.52  % (839)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (836)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (838)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.24/0.53  % (842)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.24/0.53  % (842)Refutation not found, incomplete strategy% (842)------------------------------
% 1.24/0.53  % (842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.53  % (842)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.53  
% 1.24/0.53  % (842)Memory used [KB]: 10618
% 1.24/0.53  % (842)Time elapsed: 0.107 s
% 1.24/0.53  % (842)------------------------------
% 1.24/0.53  % (842)------------------------------
% 1.24/0.53  % (843)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.24/0.53  % (852)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.24/0.53  % (843)Refutation not found, incomplete strategy% (843)------------------------------
% 1.24/0.53  % (843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.53  % (843)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.53  
% 1.24/0.53  % (843)Memory used [KB]: 10618
% 1.24/0.53  % (843)Time elapsed: 0.120 s
% 1.24/0.53  % (843)------------------------------
% 1.24/0.53  % (843)------------------------------
% 1.24/0.53  % (862)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.24/0.53  % (834)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.24/0.54  % (833)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.24/0.54  % (851)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.24/0.54  % (833)Refutation not found, incomplete strategy% (833)------------------------------
% 1.24/0.54  % (833)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.54  % (833)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.54  
% 1.24/0.54  % (833)Memory used [KB]: 1663
% 1.24/0.54  % (833)Time elapsed: 0.120 s
% 1.24/0.54  % (833)------------------------------
% 1.24/0.54  % (833)------------------------------
% 1.24/0.54  % (850)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.42/0.54  % (857)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.42/0.54  % (853)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.42/0.54  % (859)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.42/0.54  % (853)Refutation not found, incomplete strategy% (853)------------------------------
% 1.42/0.54  % (853)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.54  % (853)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.54  
% 1.42/0.54  % (853)Memory used [KB]: 10618
% 1.42/0.54  % (853)Time elapsed: 0.138 s
% 1.42/0.54  % (853)------------------------------
% 1.42/0.54  % (853)------------------------------
% 1.42/0.55  % (859)Refutation not found, incomplete strategy% (859)------------------------------
% 1.42/0.55  % (859)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (859)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (859)Memory used [KB]: 6140
% 1.42/0.55  % (859)Time elapsed: 0.133 s
% 1.42/0.55  % (859)------------------------------
% 1.42/0.55  % (859)------------------------------
% 1.42/0.55  % (861)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.42/0.55  % (837)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.42/0.55  % (845)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.42/0.55  % (837)Refutation not found, incomplete strategy% (837)------------------------------
% 1.42/0.55  % (837)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (837)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (837)Memory used [KB]: 6140
% 1.42/0.55  % (837)Time elapsed: 0.132 s
% 1.42/0.55  % (837)------------------------------
% 1.42/0.55  % (837)------------------------------
% 1.42/0.55  % (835)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.42/0.55  % (855)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.42/0.55  % (861)Refutation not found, incomplete strategy% (861)------------------------------
% 1.42/0.55  % (861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (861)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (861)Memory used [KB]: 10618
% 1.42/0.55  % (861)Time elapsed: 0.141 s
% 1.42/0.55  % (861)------------------------------
% 1.42/0.55  % (861)------------------------------
% 1.42/0.55  % (855)Refutation not found, incomplete strategy% (855)------------------------------
% 1.42/0.55  % (855)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (855)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (855)Memory used [KB]: 10618
% 1.42/0.55  % (855)Time elapsed: 0.151 s
% 1.42/0.55  % (855)------------------------------
% 1.42/0.55  % (855)------------------------------
% 1.42/0.55  % (841)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.42/0.55  % (841)Refutation not found, incomplete strategy% (841)------------------------------
% 1.42/0.55  % (841)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (841)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (841)Memory used [KB]: 10618
% 1.42/0.55  % (841)Time elapsed: 0.151 s
% 1.42/0.55  % (841)------------------------------
% 1.42/0.55  % (841)------------------------------
% 1.42/0.55  % (848)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.42/0.55  % (840)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.42/0.55  % (848)Refutation not found, incomplete strategy% (848)------------------------------
% 1.42/0.55  % (848)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (848)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (848)Memory used [KB]: 6140
% 1.42/0.55  % (848)Time elapsed: 0.001 s
% 1.42/0.55  % (848)------------------------------
% 1.42/0.55  % (848)------------------------------
% 1.42/0.56  % (850)Refutation not found, incomplete strategy% (850)------------------------------
% 1.42/0.56  % (850)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.57  % (850)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.57  
% 1.42/0.57  % (850)Memory used [KB]: 10618
% 1.42/0.57  % (850)Time elapsed: 0.149 s
% 1.42/0.57  % (850)------------------------------
% 1.42/0.57  % (850)------------------------------
% 1.42/0.57  % (863)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.42/0.57  % (849)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.42/0.57  % (835)Refutation not found, incomplete strategy% (835)------------------------------
% 1.42/0.57  % (835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.57  % (835)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.57  
% 1.42/0.57  % (835)Memory used [KB]: 10618
% 1.42/0.57  % (835)Time elapsed: 0.167 s
% 1.42/0.57  % (835)------------------------------
% 1.42/0.57  % (835)------------------------------
% 1.42/0.57  % (844)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.42/0.57  % (844)Refutation not found, incomplete strategy% (844)------------------------------
% 1.42/0.57  % (844)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.57  % (844)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.57  
% 1.42/0.57  % (844)Memory used [KB]: 10618
% 1.42/0.57  % (844)Time elapsed: 0.160 s
% 1.42/0.57  % (844)------------------------------
% 1.42/0.57  % (844)------------------------------
% 1.42/0.57  % (846)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.42/0.57  % (864)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.42/0.58  % (856)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.42/0.58  % (856)Refutation not found, incomplete strategy% (856)------------------------------
% 1.42/0.58  % (856)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.58  % (856)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.58  
% 1.42/0.58  % (856)Memory used [KB]: 1663
% 1.42/0.58  % (856)Time elapsed: 0.181 s
% 1.42/0.58  % (856)------------------------------
% 1.42/0.58  % (856)------------------------------
% 1.94/0.64  % (865)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.94/0.65  % (865)Refutation not found, incomplete strategy% (865)------------------------------
% 1.94/0.65  % (865)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.94/0.65  % (865)Termination reason: Refutation not found, incomplete strategy
% 1.94/0.65  
% 1.94/0.65  % (865)Memory used [KB]: 6140
% 1.94/0.65  % (865)Time elapsed: 0.102 s
% 1.94/0.65  % (865)------------------------------
% 1.94/0.65  % (865)------------------------------
% 1.94/0.66  % (866)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 1.94/0.67  % (868)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 1.94/0.67  % (867)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 1.94/0.68  % (870)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 1.94/0.68  % (840)Refutation found. Thanks to Tanya!
% 1.94/0.68  % SZS status Theorem for theBenchmark
% 1.94/0.68  % SZS output start Proof for theBenchmark
% 1.94/0.68  fof(f1894,plain,(
% 1.94/0.68    $false),
% 1.94/0.68    inference(subsumption_resolution,[],[f21,f1871])).
% 1.94/0.68  fof(f1871,plain,(
% 1.94/0.68    ( ! [X6,X7,X5] : (k1_enumset1(X5,X6,X7) = k1_enumset1(X6,X5,X7)) )),
% 1.94/0.68    inference(superposition,[],[f1644,f746])).
% 1.94/0.68  fof(f746,plain,(
% 1.94/0.68    ( ! [X2,X0,X1] : (k2_enumset1(X2,X0,X0,X1) = k1_enumset1(X2,X0,X1)) )),
% 1.94/0.68    inference(backward_demodulation,[],[f38,f745])).
% 1.94/0.68  fof(f745,plain,(
% 1.94/0.68    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 1.94/0.68    inference(forward_demodulation,[],[f733,f109])).
% 1.94/0.68  fof(f109,plain,(
% 1.94/0.68    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 1.94/0.68    inference(forward_demodulation,[],[f106,f24])).
% 1.94/0.68  fof(f24,plain,(
% 1.94/0.68    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.94/0.68    inference(cnf_transformation,[],[f6])).
% 1.94/0.68  fof(f6,axiom,(
% 1.94/0.68    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.94/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.94/0.68  fof(f106,plain,(
% 1.94/0.68    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 1.94/0.68    inference(superposition,[],[f35,f23])).
% 1.94/0.68  fof(f23,plain,(
% 1.94/0.68    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.94/0.68    inference(cnf_transformation,[],[f5])).
% 1.94/0.68  fof(f5,axiom,(
% 1.94/0.68    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.94/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.94/0.68  fof(f35,plain,(
% 1.94/0.68    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 1.94/0.68    inference(cnf_transformation,[],[f3])).
% 1.94/0.68  fof(f3,axiom,(
% 1.94/0.68    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 1.94/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 1.94/0.68  fof(f733,plain,(
% 1.94/0.68    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 1.94/0.68    inference(backward_demodulation,[],[f190,f718])).
% 1.94/0.68  fof(f718,plain,(
% 1.94/0.68    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X1,X1)) )),
% 1.94/0.68    inference(superposition,[],[f692,f109])).
% 1.94/0.68  fof(f692,plain,(
% 1.94/0.68    ( ! [X24,X25] : (k2_tarski(X24,X25) = k2_xboole_0(k2_tarski(X24,X25),k1_tarski(X25))) )),
% 1.94/0.68    inference(superposition,[],[f662,f110])).
% 1.94/0.68  fof(f110,plain,(
% 1.94/0.68    ( ! [X4,X3] : (k2_tarski(X3,X4) = k2_xboole_0(k1_tarski(X3),k1_tarski(X4))) )),
% 1.94/0.68    inference(forward_demodulation,[],[f107,f47])).
% 1.94/0.68  fof(f47,plain,(
% 1.94/0.68    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.94/0.68    inference(superposition,[],[f44,f38])).
% 1.94/0.68  fof(f44,plain,(
% 1.94/0.68    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 1.94/0.68    inference(forward_demodulation,[],[f40,f23])).
% 1.94/0.68  fof(f40,plain,(
% 1.94/0.68    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 1.94/0.68    inference(superposition,[],[f38,f24])).
% 1.94/0.68  fof(f107,plain,(
% 1.94/0.68    ( ! [X4,X3] : (k2_xboole_0(k1_tarski(X3),k1_tarski(X4)) = k2_enumset1(X3,X3,X3,X4)) )),
% 1.94/0.68    inference(superposition,[],[f35,f73])).
% 1.94/0.68  fof(f73,plain,(
% 1.94/0.68    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.94/0.68    inference(superposition,[],[f61,f24])).
% 1.94/0.68  fof(f61,plain,(
% 1.94/0.68    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.94/0.68    inference(superposition,[],[f41,f46])).
% 1.94/0.68  fof(f46,plain,(
% 1.94/0.68    ( ! [X0] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0))) )),
% 1.94/0.68    inference(superposition,[],[f44,f22])).
% 1.94/0.68  fof(f22,plain,(
% 1.94/0.68    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.94/0.68    inference(cnf_transformation,[],[f4])).
% 1.94/0.68  fof(f4,axiom,(
% 1.94/0.68    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.94/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.94/0.68  fof(f41,plain,(
% 1.94/0.68    ( ! [X0,X1] : (k2_enumset1(X1,X0,X0,X0) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0))) )),
% 1.94/0.68    inference(superposition,[],[f38,f22])).
% 1.94/0.68  fof(f662,plain,(
% 1.94/0.68    ( ! [X14,X13] : (k2_xboole_0(X13,X14) = k2_xboole_0(k2_xboole_0(X13,X14),X14)) )),
% 1.94/0.68    inference(resolution,[],[f657,f32])).
% 1.94/0.68  fof(f32,plain,(
% 1.94/0.68    ( ! [X2,X0,X1] : (~sP0(X1,X0,X2) | k2_xboole_0(X0,X1) = X2) )),
% 1.94/0.68    inference(cnf_transformation,[],[f20])).
% 1.94/0.68  fof(f20,plain,(
% 1.94/0.68    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_xboole_0(X0,X1) != X2))),
% 1.94/0.68    inference(nnf_transformation,[],[f12])).
% 1.94/0.68  fof(f12,plain,(
% 1.94/0.68    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.94/0.68    inference(definition_folding,[],[f1,f11])).
% 1.94/0.68  fof(f11,plain,(
% 1.94/0.68    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.94/0.68    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.94/0.68  fof(f1,axiom,(
% 1.94/0.68    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.94/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.94/0.68  fof(f657,plain,(
% 1.94/0.68    ( ! [X0,X1] : (sP0(X0,k2_xboole_0(X1,X0),k2_xboole_0(X1,X0))) )),
% 1.94/0.68    inference(subsumption_resolution,[],[f656,f239])).
% 1.94/0.68  fof(f239,plain,(
% 1.94/0.68    ( ! [X4,X5] : (r2_hidden(sK4(X4,X5,X5),X4) | sP0(X4,X5,X5)) )),
% 1.94/0.68    inference(subsumption_resolution,[],[f231,f29])).
% 1.94/0.68  fof(f29,plain,(
% 1.94/0.68    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | ~r2_hidden(sK4(X0,X1,X2),X1) | sP0(X0,X1,X2)) )),
% 1.94/0.68    inference(cnf_transformation,[],[f19])).
% 1.94/0.68  fof(f19,plain,(
% 1.94/0.68    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((~r2_hidden(sK4(X0,X1,X2),X0) & ~r2_hidden(sK4(X0,X1,X2),X1)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X0) & ~r2_hidden(X4,X1))) & (r2_hidden(X4,X0) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.94/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f18])).
% 1.94/0.68  fof(f18,plain,(
% 1.94/0.68    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X0) & ~r2_hidden(X3,X1)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2))) => (((~r2_hidden(sK4(X0,X1,X2),X0) & ~r2_hidden(sK4(X0,X1,X2),X1)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.94/0.68    introduced(choice_axiom,[])).
% 1.94/0.68  fof(f17,plain,(
% 1.94/0.68    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((~r2_hidden(X3,X0) & ~r2_hidden(X3,X1)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X0) & ~r2_hidden(X4,X1))) & (r2_hidden(X4,X0) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.94/0.68    inference(rectify,[],[f16])).
% 1.94/0.68  fof(f16,plain,(
% 1.94/0.68    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.94/0.68    inference(flattening,[],[f15])).
% 2.18/0.69  % (871)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.18/0.69  % (872)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.18/0.69  % (875)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 2.18/0.69  % (873)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.18/0.69  % (873)Refutation not found, incomplete strategy% (873)------------------------------
% 2.18/0.69  % (873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.69  % (873)Termination reason: Refutation not found, incomplete strategy
% 2.18/0.69  
% 2.18/0.69  % (873)Memory used [KB]: 1663
% 2.18/0.69  % (873)Time elapsed: 0.118 s
% 2.18/0.69  % (873)------------------------------
% 2.18/0.69  % (873)------------------------------
% 2.18/0.69  % (876)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 2.18/0.69  % (876)Refutation not found, incomplete strategy% (876)------------------------------
% 2.18/0.69  % (876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.69  % (876)Termination reason: Refutation not found, incomplete strategy
% 2.18/0.69  
% 2.18/0.69  % (876)Memory used [KB]: 1663
% 2.18/0.69  % (876)Time elapsed: 0.108 s
% 2.18/0.69  % (876)------------------------------
% 2.18/0.69  % (876)------------------------------
% 2.18/0.70  % (834)Refutation not found, incomplete strategy% (834)------------------------------
% 2.18/0.70  % (834)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.70  % (834)Termination reason: Refutation not found, incomplete strategy
% 2.18/0.70  
% 2.18/0.70  % (834)Memory used [KB]: 6140
% 2.18/0.70  % (834)Time elapsed: 0.286 s
% 2.18/0.70  % (834)------------------------------
% 2.18/0.70  % (834)------------------------------
% 2.18/0.70  % (874)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 2.18/0.70  fof(f15,plain,(
% 2.18/0.70    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 2.18/0.70    inference(nnf_transformation,[],[f11])).
% 2.18/0.70  fof(f231,plain,(
% 2.18/0.70    ( ! [X4,X5] : (r2_hidden(sK4(X4,X5,X5),X4) | r2_hidden(sK4(X4,X5,X5),X5) | sP0(X4,X5,X5)) )),
% 2.18/0.70    inference(factoring,[],[f28])).
% 2.18/0.70  fof(f28,plain,(
% 2.18/0.70    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2) | sP0(X0,X1,X2)) )),
% 2.18/0.70    inference(cnf_transformation,[],[f19])).
% 2.18/0.70  fof(f656,plain,(
% 2.18/0.70    ( ! [X0,X1] : (sP0(X0,k2_xboole_0(X1,X0),k2_xboole_0(X1,X0)) | ~r2_hidden(sK4(X0,k2_xboole_0(X1,X0),k2_xboole_0(X1,X0)),X0)) )),
% 2.18/0.70    inference(duplicate_literal_removal,[],[f631])).
% 2.18/0.70  % (877)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 2.18/0.70  fof(f631,plain,(
% 2.18/0.70    ( ! [X0,X1] : (sP0(X0,k2_xboole_0(X1,X0),k2_xboole_0(X1,X0)) | ~r2_hidden(sK4(X0,k2_xboole_0(X1,X0),k2_xboole_0(X1,X0)),X0) | sP0(X0,k2_xboole_0(X1,X0),k2_xboole_0(X1,X0))) )),
% 2.18/0.70    inference(resolution,[],[f608,f30])).
% 2.18/0.70  fof(f30,plain,(
% 2.18/0.70    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | ~r2_hidden(sK4(X0,X1,X2),X0) | sP0(X0,X1,X2)) )),
% 2.18/0.70    inference(cnf_transformation,[],[f19])).
% 2.18/0.70  fof(f608,plain,(
% 2.18/0.70    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X1),k2_xboole_0(X2,X0)) | sP0(X0,X1,X1)) )),
% 2.18/0.70    inference(resolution,[],[f255,f36])).
% 2.18/0.70  fof(f36,plain,(
% 2.18/0.70    ( ! [X0,X1] : (sP0(X1,X0,k2_xboole_0(X0,X1))) )),
% 2.18/0.70    inference(equality_resolution,[],[f31])).
% 2.18/0.70  fof(f31,plain,(
% 2.18/0.70    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_xboole_0(X0,X1) != X2) )),
% 2.18/0.70    inference(cnf_transformation,[],[f20])).
% 2.18/0.70  fof(f255,plain,(
% 2.18/0.70    ( ! [X6,X8,X7,X9] : (~sP0(X6,X9,X8) | r2_hidden(sK4(X6,X7,X7),X8) | sP0(X6,X7,X7)) )),
% 2.18/0.70    inference(resolution,[],[f239,f27])).
% 2.18/0.70  fof(f27,plain,(
% 2.18/0.70    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X0) | r2_hidden(X4,X2) | ~sP0(X0,X1,X2)) )),
% 2.18/0.70    inference(cnf_transformation,[],[f19])).
% 2.18/0.70  fof(f190,plain,(
% 2.18/0.70    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k2_xboole_0(k1_enumset1(X0,X1,X1),k1_tarski(X2))) )),
% 2.18/0.70    inference(resolution,[],[f160,f32])).
% 2.18/0.70  fof(f160,plain,(
% 2.18/0.70    ( ! [X4,X5,X3] : (sP0(k1_tarski(X5),k1_enumset1(X3,X4,X4),k2_xboole_0(k1_tarski(X3),k2_tarski(X4,X5)))) )),
% 2.18/0.70    inference(superposition,[],[f108,f38])).
% 2.18/0.70  fof(f108,plain,(
% 2.18/0.70    ( ! [X2,X0,X3,X1] : (sP0(k1_tarski(X3),k1_enumset1(X0,X1,X2),k2_enumset1(X0,X1,X2,X3))) )),
% 2.18/0.70    inference(superposition,[],[f36,f35])).
% 2.18/0.70  fof(f38,plain,(
% 2.18/0.70    ( ! [X2,X0,X1] : (k2_enumset1(X2,X0,X0,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1))) )),
% 2.18/0.70    inference(superposition,[],[f34,f23])).
% 2.18/0.70  fof(f34,plain,(
% 2.18/0.70    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 2.18/0.70    inference(cnf_transformation,[],[f2])).
% 2.18/0.70  fof(f2,axiom,(
% 2.18/0.70    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 2.18/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 2.18/0.70  fof(f1644,plain,(
% 2.18/0.70    ( ! [X6,X7,X5] : (k2_enumset1(X5,X6,X6,X7) = k1_enumset1(X6,X5,X7)) )),
% 2.18/0.70    inference(forward_demodulation,[],[f1611,f109])).
% 2.18/0.70  fof(f1611,plain,(
% 2.18/0.70    ( ! [X6,X7,X5] : (k2_enumset1(X5,X6,X6,X7) = k2_xboole_0(k2_tarski(X6,X5),k1_tarski(X7))) )),
% 2.18/0.70    inference(superposition,[],[f35,f1590])).
% 2.18/0.70  fof(f1590,plain,(
% 2.18/0.70    ( ! [X0,X1] : (k2_tarski(X1,X0) = k1_enumset1(X0,X1,X1)) )),
% 2.18/0.70    inference(superposition,[],[f1540,f109])).
% 2.18/0.70  fof(f1540,plain,(
% 2.18/0.70    ( ! [X0,X1] : (k2_tarski(X1,X0) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X1))) )),
% 2.18/0.70    inference(resolution,[],[f1535,f32])).
% 2.18/0.70  fof(f1535,plain,(
% 2.18/0.70    ( ! [X6,X5] : (sP0(k1_tarski(X5),k2_tarski(X6,X5),k2_tarski(X5,X6))) )),
% 2.18/0.70    inference(superposition,[],[f1353,f1332])).
% 2.18/0.70  fof(f1332,plain,(
% 2.18/0.70    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0)) )),
% 2.18/0.70    inference(superposition,[],[f1297,f109])).
% 2.18/0.70  fof(f1297,plain,(
% 2.18/0.70    ( ! [X28,X27] : (k2_tarski(X27,X28) = k2_xboole_0(k2_tarski(X27,X28),k1_tarski(X27))) )),
% 2.18/0.70    inference(superposition,[],[f1226,f44])).
% 2.18/0.70  fof(f1226,plain,(
% 2.18/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(X0,X1),X0)) )),
% 2.18/0.70    inference(resolution,[],[f1225,f32])).
% 2.18/0.70  fof(f1225,plain,(
% 2.18/0.70    ( ! [X0,X1] : (sP0(X0,k2_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.18/0.70    inference(subsumption_resolution,[],[f1224,f239])).
% 2.18/0.70  fof(f1224,plain,(
% 2.18/0.70    ( ! [X0,X1] : (sP0(X0,k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) | ~r2_hidden(sK4(X0,k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)),X0)) )),
% 2.18/0.70    inference(duplicate_literal_removal,[],[f1195])).
% 2.18/0.70  fof(f1195,plain,(
% 2.18/0.70    ( ! [X0,X1] : (sP0(X0,k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) | ~r2_hidden(sK4(X0,k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)),X0) | sP0(X0,k2_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.18/0.70    inference(resolution,[],[f1166,f30])).
% 2.18/0.70  fof(f1166,plain,(
% 2.18/0.70    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X1),k2_xboole_0(X0,X2)) | sP0(X0,X1,X1)) )),
% 2.18/0.70    inference(resolution,[],[f256,f36])).
% 2.18/0.70  fof(f256,plain,(
% 2.18/0.70    ( ! [X12,X10,X13,X11] : (~sP0(X13,X10,X12) | r2_hidden(sK4(X10,X11,X11),X12) | sP0(X10,X11,X11)) )),
% 2.18/0.70    inference(resolution,[],[f239,f26])).
% 2.18/0.70  fof(f26,plain,(
% 2.18/0.70    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | r2_hidden(X4,X2) | ~sP0(X0,X1,X2)) )),
% 2.18/0.70    inference(cnf_transformation,[],[f19])).
% 2.18/0.70  fof(f1353,plain,(
% 2.18/0.70    ( ! [X12,X10,X11] : (sP0(k1_tarski(X12),k2_tarski(X11,X10),k1_enumset1(X10,X11,X12))) )),
% 2.18/0.70    inference(superposition,[],[f129,f1333])).
% 2.18/0.70  fof(f1333,plain,(
% 2.18/0.70    ( ! [X6,X5] : (k2_tarski(X6,X5) = k2_tarski(X5,X6)) )),
% 2.18/0.70    inference(superposition,[],[f1297,f735])).
% 2.18/0.70  fof(f735,plain,(
% 2.18/0.70    ( ! [X4,X3] : (k2_tarski(X4,X3) = k2_xboole_0(k2_tarski(X3,X4),k1_tarski(X3))) )),
% 2.18/0.70    inference(backward_demodulation,[],[f351,f718])).
% 2.18/0.70  fof(f351,plain,(
% 2.18/0.70    ( ! [X4,X3] : (k2_tarski(X4,X3) = k2_xboole_0(k1_enumset1(X3,X4,X4),k1_tarski(X3))) )),
% 2.18/0.70    inference(resolution,[],[f334,f32])).
% 2.18/0.70  fof(f334,plain,(
% 2.18/0.70    ( ! [X0,X1] : (sP0(k1_tarski(X0),k1_enumset1(X0,X1,X1),k2_tarski(X1,X0))) )),
% 2.18/0.70    inference(superposition,[],[f160,f321])).
% 2.18/0.70  fof(f321,plain,(
% 2.18/0.70    ( ! [X15,X16] : (k2_tarski(X15,X16) = k2_xboole_0(k1_tarski(X16),k2_tarski(X15,X16))) )),
% 2.18/0.70    inference(superposition,[],[f304,f110])).
% 2.18/0.70  fof(f304,plain,(
% 2.18/0.70    ( ! [X4,X3] : (k2_xboole_0(X4,X3) = k2_xboole_0(X3,k2_xboole_0(X4,X3))) )),
% 2.18/0.70    inference(resolution,[],[f302,f32])).
% 2.18/0.70  fof(f302,plain,(
% 2.18/0.70    ( ! [X0,X1] : (sP0(k2_xboole_0(X0,X1),X1,k2_xboole_0(X0,X1))) )),
% 2.18/0.70    inference(subsumption_resolution,[],[f301,f274])).
% 2.18/0.70  fof(f274,plain,(
% 2.18/0.70    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X0),k2_xboole_0(X2,X1)) | sP0(X0,X1,X0)) )),
% 2.18/0.70    inference(resolution,[],[f243,f36])).
% 2.18/0.70  fof(f243,plain,(
% 2.18/0.70    ( ! [X6,X8,X7,X9] : (~sP0(X7,X9,X8) | r2_hidden(sK4(X6,X7,X6),X8) | sP0(X6,X7,X6)) )),
% 2.18/0.70    inference(resolution,[],[f238,f27])).
% 2.18/0.70  fof(f238,plain,(
% 2.18/0.70    ( ! [X2,X3] : (r2_hidden(sK4(X2,X3,X2),X3) | sP0(X2,X3,X2)) )),
% 2.18/0.70    inference(subsumption_resolution,[],[f230,f30])).
% 2.18/0.70  fof(f230,plain,(
% 2.18/0.70    ( ! [X2,X3] : (r2_hidden(sK4(X2,X3,X2),X2) | r2_hidden(sK4(X2,X3,X2),X3) | sP0(X2,X3,X2)) )),
% 2.18/0.70    inference(factoring,[],[f28])).
% 2.18/0.70  fof(f301,plain,(
% 2.18/0.70    ( ! [X0,X1] : (sP0(k2_xboole_0(X0,X1),X1,k2_xboole_0(X0,X1)) | ~r2_hidden(sK4(k2_xboole_0(X0,X1),X1,k2_xboole_0(X0,X1)),k2_xboole_0(X0,X1))) )),
% 2.18/0.70    inference(duplicate_literal_removal,[],[f285])).
% 2.18/0.70  fof(f285,plain,(
% 2.18/0.70    ( ! [X0,X1] : (sP0(k2_xboole_0(X0,X1),X1,k2_xboole_0(X0,X1)) | ~r2_hidden(sK4(k2_xboole_0(X0,X1),X1,k2_xboole_0(X0,X1)),k2_xboole_0(X0,X1)) | sP0(k2_xboole_0(X0,X1),X1,k2_xboole_0(X0,X1))) )),
% 2.18/0.70    inference(resolution,[],[f274,f30])).
% 2.18/0.70  fof(f129,plain,(
% 2.18/0.70    ( ! [X2,X0,X1] : (sP0(k1_tarski(X2),k2_tarski(X0,X1),k1_enumset1(X0,X1,X2))) )),
% 2.18/0.70    inference(superposition,[],[f36,f109])).
% 2.18/0.70  fof(f21,plain,(
% 2.18/0.70    k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK2,sK1,sK3)),
% 2.18/0.70    inference(cnf_transformation,[],[f14])).
% 2.18/0.70  fof(f14,plain,(
% 2.18/0.70    k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK2,sK1,sK3)),
% 2.18/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f10,f13])).
% 2.18/0.70  fof(f13,plain,(
% 2.18/0.70    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2) => k1_enumset1(sK1,sK2,sK3) != k1_enumset1(sK2,sK1,sK3)),
% 2.18/0.70    introduced(choice_axiom,[])).
% 2.18/0.70  fof(f10,plain,(
% 2.18/0.70    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2)),
% 2.18/0.70    inference(ennf_transformation,[],[f9])).
% 2.18/0.70  fof(f9,negated_conjecture,(
% 2.18/0.70    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)),
% 2.18/0.70    inference(negated_conjecture,[],[f8])).
% 2.18/0.70  fof(f8,conjecture,(
% 2.18/0.70    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)),
% 2.18/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_enumset1)).
% 2.18/0.70  % SZS output end Proof for theBenchmark
% 2.18/0.70  % (840)------------------------------
% 2.18/0.70  % (840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.70  % (840)Termination reason: Refutation
% 2.18/0.70  
% 2.18/0.70  % (840)Memory used [KB]: 7419
% 2.18/0.70  % (840)Time elapsed: 0.281 s
% 2.18/0.70  % (840)------------------------------
% 2.18/0.70  % (840)------------------------------
% 2.18/0.71  % (832)Success in time 0.352 s
%------------------------------------------------------------------------------
