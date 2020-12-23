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
% DateTime   : Thu Dec  3 12:39:01 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 100 expanded)
%              Number of leaves         :   11 (  26 expanded)
%              Depth                    :   14
%              Number of atoms          :  211 ( 483 expanded)
%              Number of equality atoms :   89 ( 255 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f145,plain,(
    $false ),
    inference(subsumption_resolution,[],[f143,f39])).

fof(f39,plain,(
    ~ r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r2_hidden(sK1,sK3)
    & r1_tarski(k2_xboole_0(k2_tarski(sK1,sK2),sK3),sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f18,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) )
   => ( ~ r2_hidden(sK1,sK3)
      & r1_tarski(k2_xboole_0(k2_tarski(sK1,sK2),sK3),sK3) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

fof(f143,plain,(
    r2_hidden(sK1,sK3) ),
    inference(resolution,[],[f134,f86])).

fof(f86,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f82,f42])).

fof(f42,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f82,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
    inference(resolution,[],[f73,f72])).

fof(f72,plain,(
    ! [X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X5,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ( sK5(X0,X1,X2,X3) != X0
              & sK5(X0,X1,X2,X3) != X1
              & sK5(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
          & ( sK5(X0,X1,X2,X3) = X0
            | sK5(X0,X1,X2,X3) = X1
            | sK5(X0,X1,X2,X3) = X2
            | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).

fof(f35,plain,(
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
     => ( ( ( sK5(X0,X1,X2,X3) != X0
            & sK5(X0,X1,X2,X3) != X1
            & sK5(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
        & ( sK5(X0,X1,X2,X3) = X0
          | sK5(X0,X1,X2,X3) = X1
          | sK5(X0,X1,X2,X3) = X2
          | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X2,X1,X0,X3] :
      ( sP0(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f73,plain,(
    ! [X2,X0,X1] : sP0(X2,X1,X0,k1_enumset1(X0,X1,X2)) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP0(X2,X1,X0,X3) )
      & ( sP0(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP0(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f21,f22])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f134,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_tarski(sK1,sK2))
      | r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f133,f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f133,plain,(
    r1_tarski(k2_tarski(sK1,sK2),sK3) ),
    inference(superposition,[],[f118,f121])).

fof(f121,plain,(
    sK3 = k2_xboole_0(k2_tarski(sK1,sK2),sK3) ),
    inference(subsumption_resolution,[],[f98,f119])).

fof(f119,plain,(
    ! [X6,X5] : r1_tarski(X5,k2_xboole_0(X6,X5)) ),
    inference(resolution,[],[f78,f89])).

fof(f89,plain,(
    ! [X0,X1] : r2_hidden(X1,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f84,f42])).

fof(f84,plain,(
    ! [X6,X8,X7] : r2_hidden(X6,k1_enumset1(X7,X8,X6)) ),
    inference(resolution,[],[f73,f70])).

fof(f70,plain,(
    ! [X2,X5,X3,X1] :
      ( ~ sP0(X5,X1,X2,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_tarski(X0,X1))
      | r1_tarski(X2,k2_xboole_0(X0,X1)) ) ),
    inference(superposition,[],[f43,f41])).

fof(f41,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f98,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k2_tarski(sK1,sK2),sK3))
    | sK3 = k2_xboole_0(k2_tarski(sK1,sK2),sK3) ),
    inference(resolution,[],[f46,f38])).

fof(f38,plain,(
    r1_tarski(k2_xboole_0(k2_tarski(sK1,sK2),sK3),sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f118,plain,(
    ! [X4,X3] : r1_tarski(X3,k2_xboole_0(X3,X4)) ),
    inference(resolution,[],[f78,f86])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n015.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:32:23 EST 2020
% 0.15/0.35  % CPUTime    : 
% 1.20/0.52  % (2180)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.20/0.52  % (2172)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.20/0.52  % (2164)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.20/0.53  % (2162)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.20/0.54  % (2164)Refutation found. Thanks to Tanya!
% 1.20/0.54  % SZS status Theorem for theBenchmark
% 1.36/0.54  % SZS output start Proof for theBenchmark
% 1.36/0.54  fof(f145,plain,(
% 1.36/0.54    $false),
% 1.36/0.54    inference(subsumption_resolution,[],[f143,f39])).
% 1.36/0.54  fof(f39,plain,(
% 1.36/0.54    ~r2_hidden(sK1,sK3)),
% 1.36/0.54    inference(cnf_transformation,[],[f25])).
% 1.36/0.54  fof(f25,plain,(
% 1.36/0.54    ~r2_hidden(sK1,sK3) & r1_tarski(k2_xboole_0(k2_tarski(sK1,sK2),sK3),sK3)),
% 1.36/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f18,f24])).
% 1.36/0.54  fof(f24,plain,(
% 1.36/0.54    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)) => (~r2_hidden(sK1,sK3) & r1_tarski(k2_xboole_0(k2_tarski(sK1,sK2),sK3),sK3))),
% 1.36/0.54    introduced(choice_axiom,[])).
% 1.36/0.54  fof(f18,plain,(
% 1.36/0.54    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 1.36/0.54    inference(ennf_transformation,[],[f17])).
% 1.36/0.54  fof(f17,negated_conjecture,(
% 1.36/0.54    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 1.36/0.54    inference(negated_conjecture,[],[f16])).
% 1.36/0.54  fof(f16,conjecture,(
% 1.36/0.54    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).
% 1.36/0.54  fof(f143,plain,(
% 1.36/0.54    r2_hidden(sK1,sK3)),
% 1.36/0.54    inference(resolution,[],[f134,f86])).
% 1.36/0.54  fof(f86,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 1.36/0.54    inference(superposition,[],[f82,f42])).
% 1.36/0.54  fof(f42,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f8])).
% 1.36/0.54  fof(f8,axiom,(
% 1.36/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.36/0.54  fof(f82,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_enumset1(X0,X1,X2))) )),
% 1.36/0.54    inference(resolution,[],[f73,f72])).
% 1.36/0.54  fof(f72,plain,(
% 1.36/0.54    ( ! [X0,X5,X3,X1] : (~sP0(X0,X1,X5,X3) | r2_hidden(X5,X3)) )),
% 1.36/0.54    inference(equality_resolution,[],[f54])).
% 1.36/0.54  fof(f54,plain,(
% 1.36/0.54    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | ~sP0(X0,X1,X2,X3)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f36])).
% 1.36/0.54  fof(f36,plain,(
% 1.36/0.54    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (((sK5(X0,X1,X2,X3) != X0 & sK5(X0,X1,X2,X3) != X1 & sK5(X0,X1,X2,X3) != X2) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sK5(X0,X1,X2,X3) = X0 | sK5(X0,X1,X2,X3) = X1 | sK5(X0,X1,X2,X3) = X2 | r2_hidden(sK5(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 1.36/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).
% 1.36/0.54  fof(f35,plain,(
% 1.36/0.54    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK5(X0,X1,X2,X3) != X0 & sK5(X0,X1,X2,X3) != X1 & sK5(X0,X1,X2,X3) != X2) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sK5(X0,X1,X2,X3) = X0 | sK5(X0,X1,X2,X3) = X1 | sK5(X0,X1,X2,X3) = X2 | r2_hidden(sK5(X0,X1,X2,X3),X3))))),
% 1.36/0.54    introduced(choice_axiom,[])).
% 1.36/0.54  fof(f34,plain,(
% 1.36/0.54    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 1.36/0.54    inference(rectify,[],[f33])).
% 1.36/0.54  fof(f33,plain,(
% 1.36/0.54    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 1.36/0.54    inference(flattening,[],[f32])).
% 1.36/0.54  fof(f32,plain,(
% 1.36/0.54    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 1.36/0.54    inference(nnf_transformation,[],[f22])).
% 1.36/0.54  fof(f22,plain,(
% 1.36/0.54    ! [X2,X1,X0,X3] : (sP0(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.36/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.36/0.54  fof(f73,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k1_enumset1(X0,X1,X2))) )),
% 1.36/0.54    inference(equality_resolution,[],[f61])).
% 1.36/0.54  fof(f61,plain,(
% 1.36/0.54    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.36/0.54    inference(cnf_transformation,[],[f37])).
% 1.36/0.54  fof(f37,plain,(
% 1.36/0.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 1.36/0.54    inference(nnf_transformation,[],[f23])).
% 1.36/0.54  fof(f23,plain,(
% 1.36/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP0(X2,X1,X0,X3))),
% 1.36/0.54    inference(definition_folding,[],[f21,f22])).
% 1.36/0.54  fof(f21,plain,(
% 1.36/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.36/0.54    inference(ennf_transformation,[],[f3])).
% 1.36/0.54  fof(f3,axiom,(
% 1.36/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.36/0.54  fof(f134,plain,(
% 1.36/0.54    ( ! [X0] : (~r2_hidden(X0,k2_tarski(sK1,sK2)) | r2_hidden(X0,sK3)) )),
% 1.36/0.54    inference(resolution,[],[f133,f47])).
% 1.36/0.54  fof(f47,plain,(
% 1.36/0.54    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f31])).
% 1.36/0.54  fof(f31,plain,(
% 1.36/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.36/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).
% 1.36/0.54  fof(f30,plain,(
% 1.36/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.36/0.54    introduced(choice_axiom,[])).
% 1.36/0.54  fof(f29,plain,(
% 1.36/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.36/0.54    inference(rectify,[],[f28])).
% 1.36/0.54  fof(f28,plain,(
% 1.36/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.36/0.54    inference(nnf_transformation,[],[f20])).
% 1.36/0.54  fof(f20,plain,(
% 1.36/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.36/0.54    inference(ennf_transformation,[],[f1])).
% 1.36/0.54  fof(f1,axiom,(
% 1.36/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.36/0.54  fof(f133,plain,(
% 1.36/0.54    r1_tarski(k2_tarski(sK1,sK2),sK3)),
% 1.36/0.54    inference(superposition,[],[f118,f121])).
% 1.36/0.54  fof(f121,plain,(
% 1.36/0.54    sK3 = k2_xboole_0(k2_tarski(sK1,sK2),sK3)),
% 1.36/0.54    inference(subsumption_resolution,[],[f98,f119])).
% 1.36/0.54  fof(f119,plain,(
% 1.36/0.54    ( ! [X6,X5] : (r1_tarski(X5,k2_xboole_0(X6,X5))) )),
% 1.36/0.54    inference(resolution,[],[f78,f89])).
% 1.36/0.54  fof(f89,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r2_hidden(X1,k2_tarski(X0,X1))) )),
% 1.36/0.54    inference(superposition,[],[f84,f42])).
% 1.36/0.54  fof(f84,plain,(
% 1.36/0.54    ( ! [X6,X8,X7] : (r2_hidden(X6,k1_enumset1(X7,X8,X6))) )),
% 1.36/0.54    inference(resolution,[],[f73,f70])).
% 1.36/0.54  fof(f70,plain,(
% 1.36/0.54    ( ! [X2,X5,X3,X1] : (~sP0(X5,X1,X2,X3) | r2_hidden(X5,X3)) )),
% 1.36/0.54    inference(equality_resolution,[],[f56])).
% 1.36/0.54  fof(f56,plain,(
% 1.36/0.54    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | ~sP0(X0,X1,X2,X3)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f36])).
% 1.36/0.54  fof(f78,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_tarski(X0,X1)) | r1_tarski(X2,k2_xboole_0(X0,X1))) )),
% 1.36/0.54    inference(superposition,[],[f43,f41])).
% 1.36/0.54  fof(f41,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f15])).
% 1.36/0.54  fof(f15,axiom,(
% 1.36/0.54    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.36/0.54  fof(f43,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f19])).
% 1.36/0.54  fof(f19,plain,(
% 1.36/0.54    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 1.36/0.54    inference(ennf_transformation,[],[f14])).
% 1.36/0.54  fof(f14,axiom,(
% 1.36/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 1.36/0.54  fof(f98,plain,(
% 1.36/0.54    ~r1_tarski(sK3,k2_xboole_0(k2_tarski(sK1,sK2),sK3)) | sK3 = k2_xboole_0(k2_tarski(sK1,sK2),sK3)),
% 1.36/0.54    inference(resolution,[],[f46,f38])).
% 1.36/0.54  fof(f38,plain,(
% 1.36/0.54    r1_tarski(k2_xboole_0(k2_tarski(sK1,sK2),sK3),sK3)),
% 1.36/0.54    inference(cnf_transformation,[],[f25])).
% 1.36/0.54  fof(f46,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.36/0.54    inference(cnf_transformation,[],[f27])).
% 1.36/0.54  fof(f27,plain,(
% 1.36/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.36/0.54    inference(flattening,[],[f26])).
% 1.36/0.54  fof(f26,plain,(
% 1.36/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.36/0.54    inference(nnf_transformation,[],[f2])).
% 1.36/0.54  fof(f2,axiom,(
% 1.36/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.36/0.54  fof(f118,plain,(
% 1.36/0.54    ( ! [X4,X3] : (r1_tarski(X3,k2_xboole_0(X3,X4))) )),
% 1.36/0.54    inference(resolution,[],[f78,f86])).
% 1.36/0.54  % SZS output end Proof for theBenchmark
% 1.36/0.54  % (2164)------------------------------
% 1.36/0.54  % (2164)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (2164)Termination reason: Refutation
% 1.36/0.54  
% 1.36/0.54  % (2164)Memory used [KB]: 6268
% 1.36/0.54  % (2164)Time elapsed: 0.077 s
% 1.36/0.54  % (2164)------------------------------
% 1.36/0.54  % (2164)------------------------------
% 1.36/0.54  % (2157)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.36/0.54  % (2158)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.36/0.54  % (2156)Success in time 0.179 s
%------------------------------------------------------------------------------
