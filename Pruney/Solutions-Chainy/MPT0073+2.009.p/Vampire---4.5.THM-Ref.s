%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   34 ( 103 expanded)
%              Number of leaves         :    7 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :   72 ( 226 expanded)
%              Number of equality atoms :   31 (  96 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f65,plain,(
    $false ),
    inference(subsumption_resolution,[],[f64,f55])).

fof(f55,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f53,f34])).

fof(f34,plain,(
    ! [X0] : ~ sP0(X0) ),
    inference(duplicate_literal_removal,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | ~ sP0(X0) ) ),
    inference(superposition,[],[f28,f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = X0
        & ~ r1_xboole_0(X0,X0) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = X0
        & ~ r1_xboole_0(X0,X0) )
      | ~ sP0(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f28,plain,(
    ~ sP0(k1_xboole_0) ),
    inference(resolution,[],[f16,f20])).

fof(f20,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f16,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f53,plain,
    ( k1_xboole_0 = sK1
    | sP0(sK1) ),
    inference(resolution,[],[f50,f19])).

fof(f19,plain,
    ( r1_xboole_0(sK1,sK1)
    | sP0(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( r1_xboole_0(sK1,sK1)
      & k1_xboole_0 != sK1 )
    | sP0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
        | sP0(X0) )
   => ( ( r1_xboole_0(sK1,sK1)
        & k1_xboole_0 != sK1 )
      | sP0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ( r1_xboole_0(X0,X0)
        & k1_xboole_0 != X0 )
      | sP0(X0) ) ),
    inference(definition_folding,[],[f8,f10])).

fof(f8,plain,(
    ? [X0] :
      ( ( r1_xboole_0(X0,X0)
        & k1_xboole_0 != X0 )
      | ( k1_xboole_0 = X0
        & ~ r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ~ ( r1_xboole_0(X0,X0)
            & k1_xboole_0 != X0 )
        & ~ ( k1_xboole_0 = X0
            & ~ r1_xboole_0(X0,X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f50,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f48,f21])).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f48,plain,(
    ! [X0] :
      ( k1_xboole_0 = k4_xboole_0(X0,k1_xboole_0)
      | ~ r1_xboole_0(X0,X0) ) ),
    inference(superposition,[],[f27,f42])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(subsumption_resolution,[],[f38,f20])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = k4_xboole_0(X0,X0)
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f27,f21])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f24,f22])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f64,plain,(
    k1_xboole_0 != sK1 ),
    inference(subsumption_resolution,[],[f61,f28])).

fof(f61,plain,
    ( sP0(k1_xboole_0)
    | k1_xboole_0 != sK1 ),
    inference(backward_demodulation,[],[f18,f55])).

fof(f18,plain,
    ( k1_xboole_0 != sK1
    | sP0(sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:26:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.55  % (20419)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (20428)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (20426)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (20428)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f65,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(subsumption_resolution,[],[f64,f55])).
% 0.22/0.55  fof(f55,plain,(
% 0.22/0.55    k1_xboole_0 = sK1),
% 0.22/0.55    inference(subsumption_resolution,[],[f53,f34])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    ( ! [X0] : (~sP0(X0)) )),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f33])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    ( ! [X0] : (~sP0(X0) | ~sP0(X0)) )),
% 0.22/0.55    inference(superposition,[],[f28,f17])).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = X0 | ~sP0(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f12])).
% 0.22/0.55  fof(f12,plain,(
% 0.22/0.55    ! [X0] : ((k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)) | ~sP0(X0))),
% 0.22/0.55    inference(nnf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,plain,(
% 0.22/0.55    ! [X0] : ((k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)) | ~sP0(X0))),
% 0.22/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ~sP0(k1_xboole_0)),
% 0.22/0.55    inference(resolution,[],[f16,f20])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f5])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.55  fof(f16,plain,(
% 0.22/0.55    ( ! [X0] : (~r1_xboole_0(X0,X0) | ~sP0(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f12])).
% 0.22/0.55  fof(f53,plain,(
% 0.22/0.55    k1_xboole_0 = sK1 | sP0(sK1)),
% 0.22/0.55    inference(resolution,[],[f50,f19])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    r1_xboole_0(sK1,sK1) | sP0(sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f14])).
% 0.22/0.55  fof(f14,plain,(
% 0.22/0.55    (r1_xboole_0(sK1,sK1) & k1_xboole_0 != sK1) | sP0(sK1)),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f13])).
% 0.22/0.55  fof(f13,plain,(
% 0.22/0.55    ? [X0] : ((r1_xboole_0(X0,X0) & k1_xboole_0 != X0) | sP0(X0)) => ((r1_xboole_0(sK1,sK1) & k1_xboole_0 != sK1) | sP0(sK1))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f11,plain,(
% 0.22/0.55    ? [X0] : ((r1_xboole_0(X0,X0) & k1_xboole_0 != X0) | sP0(X0))),
% 0.22/0.55    inference(definition_folding,[],[f8,f10])).
% 0.22/0.55  fof(f8,plain,(
% 0.22/0.55    ? [X0] : ((r1_xboole_0(X0,X0) & k1_xboole_0 != X0) | (k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,negated_conjecture,(
% 0.22/0.55    ~! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.22/0.55    inference(negated_conjecture,[],[f6])).
% 0.22/0.55  fof(f6,conjecture,(
% 0.22/0.55    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 0.22/0.55    inference(forward_demodulation,[],[f48,f21])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k1_xboole_0) | ~r1_xboole_0(X0,X0)) )),
% 0.22/0.55    inference(superposition,[],[f27,f42])).
% 0.22/0.55  fof(f42,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f38,f20])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.55    inference(superposition,[],[f27,f21])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f24,f22])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f15])).
% 0.22/0.55  fof(f15,plain,(
% 0.22/0.55    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.55    inference(nnf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.55  fof(f64,plain,(
% 0.22/0.55    k1_xboole_0 != sK1),
% 0.22/0.55    inference(subsumption_resolution,[],[f61,f28])).
% 0.22/0.55  fof(f61,plain,(
% 0.22/0.55    sP0(k1_xboole_0) | k1_xboole_0 != sK1),
% 0.22/0.55    inference(backward_demodulation,[],[f18,f55])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    k1_xboole_0 != sK1 | sP0(sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f14])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (20428)------------------------------
% 0.22/0.55  % (20428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (20428)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (20428)Memory used [KB]: 1663
% 0.22/0.55  % (20428)Time elapsed: 0.139 s
% 0.22/0.55  % (20428)------------------------------
% 0.22/0.55  % (20428)------------------------------
% 0.22/0.55  % (20410)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (20412)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  % (20410)Refutation not found, incomplete strategy% (20410)------------------------------
% 0.22/0.55  % (20410)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (20410)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (20410)Memory used [KB]: 10618
% 0.22/0.55  % (20410)Time elapsed: 0.108 s
% 0.22/0.55  % (20410)------------------------------
% 0.22/0.55  % (20410)------------------------------
% 0.22/0.55  % (20419)Refutation not found, incomplete strategy% (20419)------------------------------
% 0.22/0.55  % (20419)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (20419)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (20419)Memory used [KB]: 10618
% 0.22/0.55  % (20419)Time elapsed: 0.109 s
% 0.22/0.55  % (20419)------------------------------
% 0.22/0.55  % (20419)------------------------------
% 0.22/0.56  % (20394)Success in time 0.194 s
%------------------------------------------------------------------------------
