%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:57 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 132 expanded)
%              Number of leaves         :   16 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  226 ( 342 expanded)
%              Number of equality atoms :  111 ( 180 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f245,plain,(
    $false ),
    inference(subsumption_resolution,[],[f244,f123])).

fof(f123,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(superposition,[],[f116,f59])).

fof(f59,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f116,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f112,f64])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f112,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
    inference(resolution,[],[f100,f99])).

fof(f99,plain,(
    ! [X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X5,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ( sK4(X0,X1,X2,X3) != X0
              & sK4(X0,X1,X2,X3) != X1
              & sK4(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( sK4(X0,X1,X2,X3) = X0
            | sK4(X0,X1,X2,X3) = X1
            | sK4(X0,X1,X2,X3) = X2
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f50,f51])).

fof(f51,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X0 != X4
              & X1 != X4
              & X2 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X0 = X4
            | X1 = X4
            | X2 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK4(X0,X1,X2,X3) != X0
            & sK4(X0,X1,X2,X3) != X1
            & sK4(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( sK4(X0,X1,X2,X3) = X0
          | sK4(X0,X1,X2,X3) = X1
          | sK4(X0,X1,X2,X3) = X2
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ( X0 != X4
                & X1 != X4
                & X2 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X0 = X4
              | X1 = X4
              | X2 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
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
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
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
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X2,X1,X0,X3] :
      ( sP0(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f100,plain,(
    ! [X2,X0,X1] : sP0(X2,X1,X0,k1_enumset1(X0,X1,X2)) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP0(X2,X1,X0,X3) )
      & ( sP0(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP0(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f40,f41])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f244,plain,(
    ~ r2_hidden(sK1,k1_tarski(sK1)) ),
    inference(resolution,[],[f235,f224])).

fof(f224,plain,(
    r2_hidden(sK1,sK2) ),
    inference(subsumption_resolution,[],[f55,f223])).

fof(f223,plain,(
    ! [X8,X9] :
      ( k1_tarski(X8) = k4_xboole_0(k1_tarski(X8),X9)
      | r2_hidden(X8,X9) ) ),
    inference(backward_demodulation,[],[f205,f211])).

fof(f211,plain,(
    ! [X2,X1] : k4_xboole_0(X2,X1) = k4_xboole_0(k2_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f209,f149])).

fof(f149,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f109,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f109,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1)) ),
    inference(superposition,[],[f65,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f209,plain,(
    ! [X6,X5] : k4_xboole_0(X5,X6) = k4_xboole_0(k2_xboole_0(X6,X5),X6) ),
    inference(forward_demodulation,[],[f208,f68])).

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f208,plain,(
    ! [X6,X5] : k4_xboole_0(X5,X6) = k4_xboole_0(k2_xboole_0(X6,k4_xboole_0(X5,X6)),X6) ),
    inference(forward_demodulation,[],[f203,f149])).

fof(f203,plain,(
    ! [X6,X5] : k4_xboole_0(X5,X6) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X5,X6),X6),X6) ),
    inference(resolution,[],[f75,f61])).

fof(f61,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

fof(f205,plain,(
    ! [X8,X9] :
      ( k1_tarski(X8) = k4_xboole_0(k2_xboole_0(k1_tarski(X8),X9),X9)
      | r2_hidden(X8,X9) ) ),
    inference(resolution,[],[f75,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f55,plain,
    ( k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),sK2)
    | r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ( r2_hidden(sK1,sK2)
      | k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),sK2) )
    & ( ~ r2_hidden(sK1,sK2)
      | k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f43,f44])).

fof(f44,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X0,X1)
          | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) )
        & ( ~ r2_hidden(X0,X1)
          | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) )
   => ( ( r2_hidden(sK1,sK2)
        | k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),sK2) )
      & ( ~ r2_hidden(sK1,sK2)
        | k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <~> ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      <=> ~ r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f31])).

fof(f31,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).

fof(f235,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,k1_tarski(sK1)) ) ),
    inference(superposition,[],[f175,f225])).

fof(f225,plain,(
    k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),sK2) ),
    inference(subsumption_resolution,[],[f54,f224])).

fof(f54,plain,
    ( ~ r2_hidden(sK1,sK2)
    | k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f175,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f72,f104])).

fof(f104,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(resolution,[],[f74,f61])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,plain,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:50:31 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.55  % (31709)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (31708)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (31718)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (31717)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.42/0.56  % (31701)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.42/0.56  % (31700)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.42/0.56  % (31701)Refutation found. Thanks to Tanya!
% 1.42/0.56  % SZS status Theorem for theBenchmark
% 1.42/0.56  % SZS output start Proof for theBenchmark
% 1.42/0.56  fof(f245,plain,(
% 1.42/0.56    $false),
% 1.42/0.56    inference(subsumption_resolution,[],[f244,f123])).
% 1.42/0.56  fof(f123,plain,(
% 1.42/0.56    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 1.42/0.56    inference(superposition,[],[f116,f59])).
% 1.42/0.56  fof(f59,plain,(
% 1.42/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f21])).
% 1.42/0.56  fof(f21,axiom,(
% 1.42/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.42/0.56  fof(f116,plain,(
% 1.42/0.56    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 1.42/0.56    inference(superposition,[],[f112,f64])).
% 1.42/0.56  fof(f64,plain,(
% 1.42/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f22])).
% 1.42/0.56  fof(f22,axiom,(
% 1.42/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.42/0.56  fof(f112,plain,(
% 1.42/0.56    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_enumset1(X0,X1,X2))) )),
% 1.42/0.56    inference(resolution,[],[f100,f99])).
% 1.42/0.56  fof(f99,plain,(
% 1.42/0.56    ( ! [X0,X5,X3,X1] : (~sP0(X0,X1,X5,X3) | r2_hidden(X5,X3)) )),
% 1.42/0.56    inference(equality_resolution,[],[f83])).
% 1.42/0.56  fof(f83,plain,(
% 1.42/0.56    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | ~sP0(X0,X1,X2,X3)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f52])).
% 1.42/0.56  fof(f52,plain,(
% 1.42/0.56    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (((sK4(X0,X1,X2,X3) != X0 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X2) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X0 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X2 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 1.42/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f50,f51])).
% 1.42/0.56  fof(f51,plain,(
% 1.42/0.56    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X0 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X2) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X0 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X2 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 1.42/0.56    introduced(choice_axiom,[])).
% 1.42/0.56  fof(f50,plain,(
% 1.42/0.56    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 1.42/0.56    inference(rectify,[],[f49])).
% 1.42/0.56  fof(f49,plain,(
% 1.42/0.56    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 1.42/0.56    inference(flattening,[],[f48])).
% 1.42/0.56  fof(f48,plain,(
% 1.42/0.56    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 1.42/0.56    inference(nnf_transformation,[],[f41])).
% 1.42/0.56  fof(f41,plain,(
% 1.42/0.56    ! [X2,X1,X0,X3] : (sP0(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.42/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.42/0.56  fof(f100,plain,(
% 1.42/0.56    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k1_enumset1(X0,X1,X2))) )),
% 1.42/0.56    inference(equality_resolution,[],[f90])).
% 1.42/0.56  fof(f90,plain,(
% 1.42/0.56    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.42/0.56    inference(cnf_transformation,[],[f53])).
% 1.42/0.56  fof(f53,plain,(
% 1.42/0.56    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 1.42/0.56    inference(nnf_transformation,[],[f42])).
% 1.42/0.56  fof(f42,plain,(
% 1.42/0.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP0(X2,X1,X0,X3))),
% 1.42/0.56    inference(definition_folding,[],[f40,f41])).
% 1.42/0.56  fof(f40,plain,(
% 1.42/0.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.42/0.56    inference(ennf_transformation,[],[f16])).
% 1.42/0.56  fof(f16,axiom,(
% 1.42/0.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.42/0.56  fof(f244,plain,(
% 1.42/0.56    ~r2_hidden(sK1,k1_tarski(sK1))),
% 1.42/0.56    inference(resolution,[],[f235,f224])).
% 1.42/0.56  fof(f224,plain,(
% 1.42/0.56    r2_hidden(sK1,sK2)),
% 1.42/0.56    inference(subsumption_resolution,[],[f55,f223])).
% 1.42/0.56  fof(f223,plain,(
% 1.42/0.56    ( ! [X8,X9] : (k1_tarski(X8) = k4_xboole_0(k1_tarski(X8),X9) | r2_hidden(X8,X9)) )),
% 1.42/0.56    inference(backward_demodulation,[],[f205,f211])).
% 1.42/0.56  fof(f211,plain,(
% 1.42/0.56    ( ! [X2,X1] : (k4_xboole_0(X2,X1) = k4_xboole_0(k2_xboole_0(X2,X1),X1)) )),
% 1.42/0.56    inference(superposition,[],[f209,f149])).
% 1.42/0.56  fof(f149,plain,(
% 1.42/0.56    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 1.42/0.56    inference(superposition,[],[f109,f65])).
% 1.42/0.56  fof(f65,plain,(
% 1.42/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.42/0.56    inference(cnf_transformation,[],[f29])).
% 1.42/0.56  fof(f29,axiom,(
% 1.42/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.42/0.56  fof(f109,plain,(
% 1.42/0.56    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1))) )),
% 1.42/0.56    inference(superposition,[],[f65,f62])).
% 1.42/0.56  fof(f62,plain,(
% 1.42/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f15])).
% 1.42/0.56  fof(f15,axiom,(
% 1.42/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.42/0.56  fof(f209,plain,(
% 1.42/0.56    ( ! [X6,X5] : (k4_xboole_0(X5,X6) = k4_xboole_0(k2_xboole_0(X6,X5),X6)) )),
% 1.42/0.56    inference(forward_demodulation,[],[f208,f68])).
% 1.42/0.56  fof(f68,plain,(
% 1.42/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f7])).
% 1.42/0.56  fof(f7,axiom,(
% 1.42/0.56    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.42/0.56  fof(f208,plain,(
% 1.42/0.56    ( ! [X6,X5] : (k4_xboole_0(X5,X6) = k4_xboole_0(k2_xboole_0(X6,k4_xboole_0(X5,X6)),X6)) )),
% 1.42/0.56    inference(forward_demodulation,[],[f203,f149])).
% 1.42/0.56  fof(f203,plain,(
% 1.42/0.56    ( ! [X6,X5] : (k4_xboole_0(X5,X6) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X5,X6),X6),X6)) )),
% 1.42/0.56    inference(resolution,[],[f75,f61])).
% 1.42/0.56  fof(f61,plain,(
% 1.42/0.56    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f10])).
% 1.42/0.56  fof(f10,axiom,(
% 1.42/0.56    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.42/0.56  fof(f75,plain,(
% 1.42/0.56    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0) )),
% 1.42/0.56    inference(cnf_transformation,[],[f39])).
% 1.42/0.56  fof(f39,plain,(
% 1.42/0.56    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 1.42/0.56    inference(ennf_transformation,[],[f11])).
% 1.42/0.56  fof(f11,axiom,(
% 1.42/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).
% 1.42/0.56  fof(f205,plain,(
% 1.42/0.56    ( ! [X8,X9] : (k1_tarski(X8) = k4_xboole_0(k2_xboole_0(k1_tarski(X8),X9),X9) | r2_hidden(X8,X9)) )),
% 1.42/0.56    inference(resolution,[],[f75,f73])).
% 1.42/0.56  fof(f73,plain,(
% 1.42/0.56    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f37])).
% 1.42/0.56  fof(f37,plain,(
% 1.42/0.56    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.42/0.56    inference(ennf_transformation,[],[f28])).
% 1.42/0.56  fof(f28,axiom,(
% 1.42/0.56    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.42/0.56  fof(f55,plain,(
% 1.42/0.56    k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),sK2) | r2_hidden(sK1,sK2)),
% 1.42/0.56    inference(cnf_transformation,[],[f45])).
% 1.42/0.56  fof(f45,plain,(
% 1.42/0.56    (r2_hidden(sK1,sK2) | k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),sK2)) & (~r2_hidden(sK1,sK2) | k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),sK2))),
% 1.42/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f43,f44])).
% 1.42/0.56  fof(f44,plain,(
% 1.42/0.56    ? [X0,X1] : ((r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1))) => ((r2_hidden(sK1,sK2) | k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),sK2)) & (~r2_hidden(sK1,sK2) | k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),sK2)))),
% 1.42/0.56    introduced(choice_axiom,[])).
% 1.42/0.56  fof(f43,plain,(
% 1.42/0.56    ? [X0,X1] : ((r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)))),
% 1.42/0.56    inference(nnf_transformation,[],[f35])).
% 1.42/0.56  fof(f35,plain,(
% 1.42/0.56    ? [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <~> ~r2_hidden(X0,X1))),
% 1.42/0.56    inference(ennf_transformation,[],[f32])).
% 1.42/0.56  fof(f32,negated_conjecture,(
% 1.42/0.56    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.42/0.56    inference(negated_conjecture,[],[f31])).
% 1.42/0.56  fof(f31,conjecture,(
% 1.42/0.56    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).
% 1.42/0.56  fof(f235,plain,(
% 1.42/0.56    ( ! [X0] : (~r2_hidden(X0,sK2) | ~r2_hidden(X0,k1_tarski(sK1))) )),
% 1.42/0.56    inference(superposition,[],[f175,f225])).
% 1.42/0.56  fof(f225,plain,(
% 1.42/0.56    k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),sK2)),
% 1.42/0.56    inference(subsumption_resolution,[],[f54,f224])).
% 1.42/0.56  fof(f54,plain,(
% 1.42/0.56    ~r2_hidden(sK1,sK2) | k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),sK2)),
% 1.42/0.56    inference(cnf_transformation,[],[f45])).
% 1.42/0.56  fof(f175,plain,(
% 1.42/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X2)) | ~r2_hidden(X0,X2)) )),
% 1.42/0.56    inference(resolution,[],[f72,f104])).
% 1.42/0.56  fof(f104,plain,(
% 1.42/0.56    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.42/0.56    inference(resolution,[],[f74,f61])).
% 1.42/0.56  fof(f74,plain,(
% 1.42/0.56    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f38])).
% 1.42/0.56  fof(f38,plain,(
% 1.42/0.56    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.42/0.56    inference(ennf_transformation,[],[f3])).
% 1.42/0.56  fof(f3,axiom,(
% 1.42/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.42/0.56  fof(f72,plain,(
% 1.42/0.56    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f47])).
% 1.42/0.56  fof(f47,plain,(
% 1.42/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.42/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f46])).
% 1.42/0.56  fof(f46,plain,(
% 1.42/0.56    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.42/0.56    introduced(choice_axiom,[])).
% 1.42/0.56  fof(f36,plain,(
% 1.42/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.42/0.56    inference(ennf_transformation,[],[f34])).
% 1.42/0.56  fof(f34,plain,(
% 1.42/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.42/0.56    inference(rectify,[],[f4])).
% 1.42/0.56  fof(f4,axiom,(
% 1.42/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.42/0.56  % SZS output end Proof for theBenchmark
% 1.42/0.56  % (31701)------------------------------
% 1.42/0.56  % (31701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (31701)Termination reason: Refutation
% 1.42/0.56  
% 1.42/0.56  % (31701)Memory used [KB]: 6396
% 1.42/0.56  % (31701)Time elapsed: 0.120 s
% 1.42/0.56  % (31701)------------------------------
% 1.42/0.56  % (31701)------------------------------
% 1.42/0.57  % (31712)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.42/0.57  % (31710)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.58/0.57  % (31696)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.58/0.58  % (31723)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.58/0.58  % (31724)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.58/0.58  % (31697)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.58/0.58  % (31721)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.58/0.58  % (31715)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.58/0.58  % (31694)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.58/0.58  % (31716)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.58/0.58  % (31703)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.58/0.58  % (31695)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.58/0.59  % (31693)Success in time 0.214 s
%------------------------------------------------------------------------------
