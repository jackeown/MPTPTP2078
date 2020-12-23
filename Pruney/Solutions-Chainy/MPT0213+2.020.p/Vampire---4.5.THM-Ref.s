%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:57 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :   37 (  63 expanded)
%              Number of leaves         :   11 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :  122 ( 166 expanded)
%              Number of equality atoms :   16 (  30 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f101,plain,(
    $false ),
    inference(subsumption_resolution,[],[f100,f22])).

% (7543)Termination reason: Refutation not found, incomplete strategy

% (7543)Memory used [KB]: 6140
% (7543)Time elapsed: 0.003 s
% (7543)------------------------------
% (7543)------------------------------
% (7531)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f22,plain,(
    k1_xboole_0 != k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    k1_xboole_0 != k3_tarski(k1_xboole_0) ),
    inference(flattening,[],[f7])).

fof(f7,negated_conjecture,(
    k1_xboole_0 != k3_tarski(k1_xboole_0) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f100,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(resolution,[],[f95,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k3_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ~ sP0(X0,X1) )
      & ( sP0(X0,X1)
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> sP0(X0,X1) ) ),
    inference(definition_folding,[],[f5,f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(f95,plain,(
    sP0(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f86,f46])).

fof(f46,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f45,f37])).

fof(f37,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f24,f23])).

fof(f23,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f24,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r1_xboole_0(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f27,f44])).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f39,f23])).

fof(f39,plain,(
    ! [X0] : k3_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f25,f23])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

% (7527)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f13])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f86,plain,(
    ! [X6] :
      ( r2_hidden(sK2(k1_xboole_0,X6),X6)
      | sP0(k1_xboole_0,X6) ) ),
    inference(resolution,[],[f32,f46])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r2_hidden(sK2(X0,X1),X1)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
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
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f16,f19,f18,f17])).

fof(f17,plain,(
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

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(sK2(X0,X1),X4) )
     => ( r2_hidden(sK3(X0,X1),X0)
        & r2_hidden(sK2(X0,X1),sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK4(X0,X5),X0)
        & r2_hidden(X5,sK4(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
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
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
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
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:04:00 EST 2020
% 0.15/0.35  % CPUTime    : 
% 1.25/0.53  % (7552)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.25/0.53  % (7530)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.25/0.53  % (7535)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.25/0.54  % (7535)Refutation found. Thanks to Tanya!
% 1.25/0.54  % SZS status Theorem for theBenchmark
% 1.25/0.54  % (7543)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.25/0.54  % (7543)Refutation not found, incomplete strategy% (7543)------------------------------
% 1.25/0.54  % (7543)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.54  % SZS output start Proof for theBenchmark
% 1.25/0.54  fof(f101,plain,(
% 1.25/0.54    $false),
% 1.25/0.54    inference(subsumption_resolution,[],[f100,f22])).
% 1.25/0.54  % (7543)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.54  
% 1.25/0.54  % (7543)Memory used [KB]: 6140
% 1.25/0.54  % (7543)Time elapsed: 0.003 s
% 1.25/0.54  % (7543)------------------------------
% 1.25/0.54  % (7543)------------------------------
% 1.25/0.54  % (7531)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.25/0.54  fof(f22,plain,(
% 1.25/0.54    k1_xboole_0 != k3_tarski(k1_xboole_0)),
% 1.25/0.54    inference(cnf_transformation,[],[f8])).
% 1.25/0.54  fof(f8,plain,(
% 1.25/0.54    k1_xboole_0 != k3_tarski(k1_xboole_0)),
% 1.25/0.54    inference(flattening,[],[f7])).
% 1.25/0.54  fof(f7,negated_conjecture,(
% 1.25/0.54    ~k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.25/0.54    inference(negated_conjecture,[],[f6])).
% 1.25/0.54  fof(f6,conjecture,(
% 1.25/0.54    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 1.25/0.54  fof(f100,plain,(
% 1.25/0.54    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.25/0.54    inference(resolution,[],[f95,f35])).
% 1.25/0.54  fof(f35,plain,(
% 1.25/0.54    ( ! [X0,X1] : (~sP0(X0,X1) | k3_tarski(X0) = X1) )),
% 1.25/0.54    inference(cnf_transformation,[],[f21])).
% 1.25/0.54  fof(f21,plain,(
% 1.25/0.54    ! [X0,X1] : ((k3_tarski(X0) = X1 | ~sP0(X0,X1)) & (sP0(X0,X1) | k3_tarski(X0) != X1))),
% 1.25/0.54    inference(nnf_transformation,[],[f12])).
% 1.25/0.54  fof(f12,plain,(
% 1.25/0.54    ! [X0,X1] : (k3_tarski(X0) = X1 <=> sP0(X0,X1))),
% 1.25/0.54    inference(definition_folding,[],[f5,f11])).
% 1.25/0.54  fof(f11,plain,(
% 1.25/0.54    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 1.25/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.25/0.54  fof(f5,axiom,(
% 1.25/0.54    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).
% 1.25/0.54  fof(f95,plain,(
% 1.25/0.54    sP0(k1_xboole_0,k1_xboole_0)),
% 1.25/0.54    inference(resolution,[],[f86,f46])).
% 1.25/0.54  fof(f46,plain,(
% 1.25/0.54    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 1.25/0.54    inference(subsumption_resolution,[],[f45,f37])).
% 1.25/0.54  fof(f37,plain,(
% 1.25/0.54    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 1.25/0.54    inference(superposition,[],[f24,f23])).
% 1.25/0.54  fof(f23,plain,(
% 1.25/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f3])).
% 1.25/0.54  fof(f3,axiom,(
% 1.25/0.54    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 1.25/0.54  fof(f24,plain,(
% 1.25/0.54    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f4])).
% 1.25/0.54  fof(f4,axiom,(
% 1.25/0.54    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.25/0.54  fof(f45,plain,(
% 1.25/0.54    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(k1_xboole_0,X0)) )),
% 1.25/0.54    inference(superposition,[],[f27,f44])).
% 1.25/0.54  fof(f44,plain,(
% 1.25/0.54    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.25/0.54    inference(forward_demodulation,[],[f39,f23])).
% 1.25/0.54  fof(f39,plain,(
% 1.25/0.54    ( ! [X0] : (k3_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 1.25/0.54    inference(superposition,[],[f25,f23])).
% 1.25/0.54  fof(f25,plain,(
% 1.25/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.25/0.54    inference(cnf_transformation,[],[f2])).
% 1.25/0.54  fof(f2,axiom,(
% 1.25/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.25/0.54  fof(f27,plain,(
% 1.25/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f14])).
% 1.25/0.54  % (7527)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.25/0.54  fof(f14,plain,(
% 1.25/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.25/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f13])).
% 1.25/0.54  fof(f13,plain,(
% 1.25/0.54    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 1.25/0.54    introduced(choice_axiom,[])).
% 1.25/0.54  fof(f10,plain,(
% 1.25/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.25/0.54    inference(ennf_transformation,[],[f9])).
% 1.25/0.54  fof(f9,plain,(
% 1.25/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.25/0.54    inference(rectify,[],[f1])).
% 1.25/0.54  fof(f1,axiom,(
% 1.25/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.25/0.54  fof(f86,plain,(
% 1.25/0.54    ( ! [X6] : (r2_hidden(sK2(k1_xboole_0,X6),X6) | sP0(k1_xboole_0,X6)) )),
% 1.25/0.54    inference(resolution,[],[f32,f46])).
% 1.25/0.54  fof(f32,plain,(
% 1.25/0.54    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1) | sP0(X0,X1)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f20])).
% 1.25/0.54  fof(f20,plain,(
% 1.25/0.54    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK2(X0,X1),X3)) | ~r2_hidden(sK2(X0,X1),X1)) & ((r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),sK3(X0,X1))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK4(X0,X5),X0) & r2_hidden(X5,sK4(X0,X5))) | ~r2_hidden(X5,X1))) | ~sP0(X0,X1)))),
% 1.25/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f16,f19,f18,f17])).
% 1.25/0.54  fof(f17,plain,(
% 1.25/0.54    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK2(X0,X1),X3)) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK2(X0,X1),X4)) | r2_hidden(sK2(X0,X1),X1))))),
% 1.25/0.54    introduced(choice_axiom,[])).
% 1.25/0.54  fof(f18,plain,(
% 1.25/0.54    ! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK2(X0,X1),X4)) => (r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),sK3(X0,X1))))),
% 1.25/0.54    introduced(choice_axiom,[])).
% 1.25/0.54  fof(f19,plain,(
% 1.25/0.54    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK4(X0,X5),X0) & r2_hidden(X5,sK4(X0,X5))))),
% 1.25/0.54    introduced(choice_axiom,[])).
% 1.25/0.54  fof(f16,plain,(
% 1.25/0.54    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | ~sP0(X0,X1)))),
% 1.25/0.54    inference(rectify,[],[f15])).
% 1.25/0.54  fof(f15,plain,(
% 1.25/0.54    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | ~sP0(X0,X1)))),
% 1.25/0.54    inference(nnf_transformation,[],[f11])).
% 1.25/0.54  % SZS output end Proof for theBenchmark
% 1.25/0.54  % (7535)------------------------------
% 1.25/0.54  % (7535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.54  % (7535)Termination reason: Refutation
% 1.25/0.54  
% 1.25/0.54  % (7535)Memory used [KB]: 6268
% 1.25/0.54  % (7535)Time elapsed: 0.128 s
% 1.25/0.54  % (7535)------------------------------
% 1.25/0.54  % (7535)------------------------------
% 1.40/0.54  % (7528)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.40/0.54  % (7532)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.40/0.54  % (7532)Refutation not found, incomplete strategy% (7532)------------------------------
% 1.40/0.54  % (7532)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (7532)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  
% 1.40/0.54  % (7532)Memory used [KB]: 6140
% 1.40/0.54  % (7532)Time elapsed: 0.136 s
% 1.40/0.54  % (7532)------------------------------
% 1.40/0.54  % (7532)------------------------------
% 1.40/0.54  % (7526)Success in time 0.178 s
%------------------------------------------------------------------------------
