%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:30 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   28 (  49 expanded)
%              Number of leaves         :    6 (  13 expanded)
%              Depth                    :   13
%              Number of atoms          :  114 ( 341 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f68,plain,(
    $false ),
    inference(subsumption_resolution,[],[f16,f65])).

fof(f65,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(superposition,[],[f64,f17])).

fof(f17,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f64,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f63,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,X0,X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f6])).

fof(f6,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f63,plain,(
    ! [X0] : sP0(X0,X0,X0) ),
    inference(subsumption_resolution,[],[f62,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X0)
              & ~ r2_hidden(sK2(X0,X1,X2),X1) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( r2_hidden(sK2(X0,X1,X2),X0)
            | r2_hidden(sK2(X0,X1,X2),X1)
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X0)
                & ~ r2_hidden(X4,X1) ) )
            & ( r2_hidden(X4,X0)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f13])).

fof(f13,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X3,X1) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X0)
            | r2_hidden(X3,X1)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X0)
            & ~ r2_hidden(sK2(X0,X1,X2),X1) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( r2_hidden(sK2(X0,X1,X2),X0)
          | r2_hidden(sK2(X0,X1,X2),X1)
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
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
    inference(rectify,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f62,plain,(
    ! [X0] :
      ( sP0(X0,X0,X0)
      | ~ r2_hidden(sK2(X0,X0,X0),X0) ) ),
    inference(duplicate_literal_removal,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( sP0(X0,X0,X0)
      | ~ r2_hidden(sK2(X0,X0,X0),X0)
      | sP0(X0,X0,X0) ) ),
    inference(resolution,[],[f54,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f54,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK2(X2,X3,X2),X3)
      | sP0(X2,X3,X2) ) ),
    inference(subsumption_resolution,[],[f46,f23])).

fof(f46,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK2(X2,X3,X2),X2)
      | r2_hidden(sK2(X2,X3,X2),X3)
      | sP0(X2,X3,X2) ) ),
    inference(factoring,[],[f21])).

fof(f16,plain,(
    k1_tarski(sK1) != k2_tarski(sK1,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k1_tarski(sK1) != k2_tarski(sK1,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f5,f8])).

fof(f8,plain,
    ( ? [X0] : k1_tarski(X0) != k2_tarski(X0,X0)
   => k1_tarski(sK1) != k2_tarski(sK1,sK1) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0] : k1_tarski(X0) != k2_tarski(X0,X0) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:19:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.44  % (18775)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.45  % (18775)Refutation not found, incomplete strategy% (18775)------------------------------
% 0.19/0.45  % (18775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.45  % (18775)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.45  
% 0.19/0.45  % (18775)Memory used [KB]: 1663
% 0.19/0.45  % (18775)Time elapsed: 0.053 s
% 0.19/0.45  % (18775)------------------------------
% 0.19/0.45  % (18775)------------------------------
% 0.19/0.45  % (18767)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.45  % (18767)Refutation not found, incomplete strategy% (18767)------------------------------
% 0.19/0.45  % (18767)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.45  % (18767)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.45  
% 0.19/0.45  % (18767)Memory used [KB]: 6140
% 0.19/0.45  % (18767)Time elapsed: 0.004 s
% 0.19/0.45  % (18767)------------------------------
% 0.19/0.45  % (18767)------------------------------
% 0.19/0.46  % (18759)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.46  % (18760)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.46  % (18760)Refutation not found, incomplete strategy% (18760)------------------------------
% 0.19/0.46  % (18760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (18760)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.46  
% 0.19/0.46  % (18760)Memory used [KB]: 10618
% 0.19/0.46  % (18760)Time elapsed: 0.082 s
% 0.19/0.46  % (18760)------------------------------
% 0.19/0.46  % (18760)------------------------------
% 0.19/0.47  % (18759)Refutation found. Thanks to Tanya!
% 0.19/0.47  % SZS status Theorem for theBenchmark
% 0.19/0.47  % SZS output start Proof for theBenchmark
% 0.19/0.47  fof(f68,plain,(
% 0.19/0.47    $false),
% 0.19/0.47    inference(subsumption_resolution,[],[f16,f65])).
% 0.19/0.47  fof(f65,plain,(
% 0.19/0.47    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.19/0.47    inference(superposition,[],[f64,f17])).
% 0.19/0.47  fof(f17,plain,(
% 0.19/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f2])).
% 0.19/0.47  fof(f2,axiom,(
% 0.19/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.19/0.47  fof(f64,plain,(
% 0.19/0.47    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.19/0.47    inference(resolution,[],[f63,f25])).
% 0.19/0.47  fof(f25,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~sP0(X1,X0,X2) | k2_xboole_0(X0,X1) = X2) )),
% 0.19/0.47    inference(cnf_transformation,[],[f15])).
% 0.19/0.47  fof(f15,plain,(
% 0.19/0.47    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_xboole_0(X0,X1) != X2))),
% 0.19/0.47    inference(nnf_transformation,[],[f7])).
% 0.19/0.47  fof(f7,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 0.19/0.47    inference(definition_folding,[],[f1,f6])).
% 0.19/0.47  fof(f6,plain,(
% 0.19/0.47    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.19/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.19/0.47  fof(f1,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.19/0.47  fof(f63,plain,(
% 0.19/0.47    ( ! [X0] : (sP0(X0,X0,X0)) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f62,f21])).
% 0.19/0.47  fof(f21,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2) | sP0(X0,X1,X2)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f14])).
% 0.19/0.47  fof(f14,plain,(
% 0.19/0.47    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((~r2_hidden(sK2(X0,X1,X2),X0) & ~r2_hidden(sK2(X0,X1,X2),X1)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X0) & ~r2_hidden(X4,X1))) & (r2_hidden(X4,X0) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.19/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f13])).
% 0.19/0.47  fof(f13,plain,(
% 0.19/0.47    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X0) & ~r2_hidden(X3,X1)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2))) => (((~r2_hidden(sK2(X0,X1,X2),X0) & ~r2_hidden(sK2(X0,X1,X2),X1)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.19/0.47    introduced(choice_axiom,[])).
% 0.19/0.47  fof(f12,plain,(
% 0.19/0.47    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((~r2_hidden(X3,X0) & ~r2_hidden(X3,X1)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X0) & ~r2_hidden(X4,X1))) & (r2_hidden(X4,X0) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.19/0.47    inference(rectify,[],[f11])).
% 0.19/0.47  fof(f11,plain,(
% 0.19/0.47    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.19/0.47    inference(flattening,[],[f10])).
% 0.19/0.47  fof(f10,plain,(
% 0.19/0.47    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.19/0.47    inference(nnf_transformation,[],[f6])).
% 0.19/0.47  fof(f62,plain,(
% 0.19/0.47    ( ! [X0] : (sP0(X0,X0,X0) | ~r2_hidden(sK2(X0,X0,X0),X0)) )),
% 0.19/0.47    inference(duplicate_literal_removal,[],[f56])).
% 0.19/0.47  fof(f56,plain,(
% 0.19/0.47    ( ! [X0] : (sP0(X0,X0,X0) | ~r2_hidden(sK2(X0,X0,X0),X0) | sP0(X0,X0,X0)) )),
% 0.19/0.47    inference(resolution,[],[f54,f23])).
% 0.19/0.47  fof(f23,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X2) | ~r2_hidden(sK2(X0,X1,X2),X0) | sP0(X0,X1,X2)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f14])).
% 0.19/0.47  fof(f54,plain,(
% 0.19/0.47    ( ! [X2,X3] : (r2_hidden(sK2(X2,X3,X2),X3) | sP0(X2,X3,X2)) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f46,f23])).
% 0.19/0.47  fof(f46,plain,(
% 0.19/0.47    ( ! [X2,X3] : (r2_hidden(sK2(X2,X3,X2),X2) | r2_hidden(sK2(X2,X3,X2),X3) | sP0(X2,X3,X2)) )),
% 0.19/0.47    inference(factoring,[],[f21])).
% 0.19/0.47  fof(f16,plain,(
% 0.19/0.47    k1_tarski(sK1) != k2_tarski(sK1,sK1)),
% 0.19/0.47    inference(cnf_transformation,[],[f9])).
% 0.19/0.47  fof(f9,plain,(
% 0.19/0.47    k1_tarski(sK1) != k2_tarski(sK1,sK1)),
% 0.19/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f5,f8])).
% 0.19/0.47  fof(f8,plain,(
% 0.19/0.47    ? [X0] : k1_tarski(X0) != k2_tarski(X0,X0) => k1_tarski(sK1) != k2_tarski(sK1,sK1)),
% 0.19/0.47    introduced(choice_axiom,[])).
% 0.19/0.47  fof(f5,plain,(
% 0.19/0.47    ? [X0] : k1_tarski(X0) != k2_tarski(X0,X0)),
% 0.19/0.47    inference(ennf_transformation,[],[f4])).
% 0.19/0.47  fof(f4,negated_conjecture,(
% 0.19/0.47    ~! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.19/0.47    inference(negated_conjecture,[],[f3])).
% 0.19/0.47  fof(f3,conjecture,(
% 0.19/0.47    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.19/0.47  % SZS output end Proof for theBenchmark
% 0.19/0.47  % (18759)------------------------------
% 0.19/0.47  % (18759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (18759)Termination reason: Refutation
% 0.19/0.47  
% 0.19/0.47  % (18759)Memory used [KB]: 6268
% 0.19/0.47  % (18759)Time elapsed: 0.071 s
% 0.19/0.47  % (18759)------------------------------
% 0.19/0.47  % (18759)------------------------------
% 0.19/0.47  % (18751)Success in time 0.127 s
%------------------------------------------------------------------------------
