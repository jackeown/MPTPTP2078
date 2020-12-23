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
% DateTime   : Thu Dec  3 12:38:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 100 expanded)
%              Number of leaves         :   21 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :  159 ( 221 expanded)
%              Number of equality atoms :   54 (  82 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f353,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f48,f52,f56,f64,f68,f85,f97,f101,f150,f168,f307,f349])).

fof(f349,plain,
    ( spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_14
    | ~ spl2_16
    | ~ spl2_20
    | ~ spl2_28 ),
    inference(avatar_contradiction_clause,[],[f348])).

fof(f348,plain,
    ( $false
    | spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_14
    | ~ spl2_16
    | ~ spl2_20
    | ~ spl2_28 ),
    inference(subsumption_resolution,[],[f47,f347])).

fof(f347,plain,
    ( sK1 = k2_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_14
    | ~ spl2_16
    | ~ spl2_20
    | ~ spl2_28 ),
    inference(forward_demodulation,[],[f346,f219])).

fof(f219,plain,
    ( sK1 = k2_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_14
    | ~ spl2_20 ),
    inference(forward_demodulation,[],[f218,f55])).

fof(f55,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl2_4
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f218,plain,
    ( k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_xboole_0)
    | ~ spl2_3
    | ~ spl2_14
    | ~ spl2_20 ),
    inference(forward_demodulation,[],[f209,f51])).

fof(f51,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl2_3
  <=> ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f209,plain,
    ( k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)))
    | ~ spl2_14
    | ~ spl2_20 ),
    inference(superposition,[],[f167,f100])).

fof(f100,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl2_14
  <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f167,plain,
    ( k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl2_20
  <=> k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f346,plain,
    ( k2_xboole_0(k1_tarski(sK0),sK1) = k2_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl2_7
    | ~ spl2_16
    | ~ spl2_20
    | ~ spl2_28 ),
    inference(forward_demodulation,[],[f345,f167])).

fof(f345,plain,
    ( k2_xboole_0(k1_tarski(sK0),sK1) = k5_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | ~ spl2_7
    | ~ spl2_16
    | ~ spl2_28 ),
    inference(forward_demodulation,[],[f323,f67])).

fof(f67,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl2_7
  <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f323,plain,
    ( k2_xboole_0(k1_tarski(sK0),sK1) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),sK1),k1_tarski(sK0))
    | ~ spl2_16
    | ~ spl2_28 ),
    inference(superposition,[],[f306,f149])).

fof(f149,plain,
    ( k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl2_16
  <=> k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f306,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X1,X0))
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f305])).

fof(f305,plain,
    ( spl2_28
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f47,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl2_2
  <=> sK1 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f307,plain,
    ( spl2_28
    | ~ spl2_6
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f116,f95,f62,f305])).

fof(f62,plain,
    ( spl2_6
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f95,plain,
    ( spl2_13
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f116,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X1,X0))
    | ~ spl2_6
    | ~ spl2_13 ),
    inference(superposition,[],[f96,f63])).

fof(f63,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f62])).

fof(f96,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f95])).

fof(f168,plain,
    ( spl2_20
    | ~ spl2_13
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f163,f147,f95,f165])).

fof(f163,plain,
    ( k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | ~ spl2_13
    | ~ spl2_16 ),
    inference(superposition,[],[f96,f149])).

fof(f150,plain,
    ( spl2_16
    | ~ spl2_1
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f102,f83,f40,f147])).

fof(f40,plain,
    ( spl2_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f83,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f102,plain,
    ( k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl2_1
    | ~ spl2_10 ),
    inference(unit_resulting_resolution,[],[f42,f84])).

fof(f84,plain,
    ( ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,X1) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f83])).

fof(f42,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f101,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f34,f99])).

fof(f34,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f97,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f31,f95])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f85,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f32,f83])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(f68,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f28,f66])).

fof(f28,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f64,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f27,f62])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f56,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f25,f54])).

fof(f25,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f52,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f24,f50])).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f48,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f23,f45])).

fof(f23,plain,(
    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f43,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f22,f40])).

fof(f22,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:13:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.44  % (17713)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (17707)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (17710)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (17722)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.48  % (17709)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (17714)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (17712)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (17721)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (17717)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (17703)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (17708)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (17706)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.50  % (17708)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f353,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f43,f48,f52,f56,f64,f68,f85,f97,f101,f150,f168,f307,f349])).
% 0.21/0.50  fof(f349,plain,(
% 0.21/0.50    spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_7 | ~spl2_14 | ~spl2_16 | ~spl2_20 | ~spl2_28),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f348])).
% 0.21/0.50  fof(f348,plain,(
% 0.21/0.50    $false | (spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_7 | ~spl2_14 | ~spl2_16 | ~spl2_20 | ~spl2_28)),
% 0.21/0.50    inference(subsumption_resolution,[],[f47,f347])).
% 0.21/0.50  fof(f347,plain,(
% 0.21/0.50    sK1 = k2_xboole_0(k1_tarski(sK0),sK1) | (~spl2_3 | ~spl2_4 | ~spl2_7 | ~spl2_14 | ~spl2_16 | ~spl2_20 | ~spl2_28)),
% 0.21/0.50    inference(forward_demodulation,[],[f346,f219])).
% 0.21/0.50  fof(f219,plain,(
% 0.21/0.50    sK1 = k2_xboole_0(sK1,k1_tarski(sK0)) | (~spl2_3 | ~spl2_4 | ~spl2_14 | ~spl2_20)),
% 0.21/0.50    inference(forward_demodulation,[],[f218,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    spl2_4 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.50  fof(f218,plain,(
% 0.21/0.50    k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_xboole_0) | (~spl2_3 | ~spl2_14 | ~spl2_20)),
% 0.21/0.50    inference(forward_demodulation,[],[f209,f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) ) | ~spl2_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    spl2_3 <=> ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.50  fof(f209,plain,(
% 0.21/0.50    k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0))) | (~spl2_14 | ~spl2_20)),
% 0.21/0.50    inference(superposition,[],[f167,f100])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) ) | ~spl2_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f99])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    spl2_14 <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) | ~spl2_20),
% 0.21/0.50    inference(avatar_component_clause,[],[f165])).
% 0.21/0.50  fof(f165,plain,(
% 0.21/0.50    spl2_20 <=> k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.21/0.50  fof(f346,plain,(
% 0.21/0.50    k2_xboole_0(k1_tarski(sK0),sK1) = k2_xboole_0(sK1,k1_tarski(sK0)) | (~spl2_7 | ~spl2_16 | ~spl2_20 | ~spl2_28)),
% 0.21/0.50    inference(forward_demodulation,[],[f345,f167])).
% 0.21/0.50  fof(f345,plain,(
% 0.21/0.50    k2_xboole_0(k1_tarski(sK0),sK1) = k5_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) | (~spl2_7 | ~spl2_16 | ~spl2_28)),
% 0.21/0.50    inference(forward_demodulation,[],[f323,f67])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) ) | ~spl2_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f66])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    spl2_7 <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.50  fof(f323,plain,(
% 0.21/0.50    k2_xboole_0(k1_tarski(sK0),sK1) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),sK1),k1_tarski(sK0)) | (~spl2_16 | ~spl2_28)),
% 0.21/0.50    inference(superposition,[],[f306,f149])).
% 0.21/0.50  fof(f149,plain,(
% 0.21/0.50    k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0)) | ~spl2_16),
% 0.21/0.50    inference(avatar_component_clause,[],[f147])).
% 0.21/0.50  fof(f147,plain,(
% 0.21/0.50    spl2_16 <=> k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.50  fof(f306,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X1,X0))) ) | ~spl2_28),
% 0.21/0.50    inference(avatar_component_clause,[],[f305])).
% 0.21/0.50  fof(f305,plain,(
% 0.21/0.50    spl2_28 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X1,X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) | spl2_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    spl2_2 <=> sK1 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.50  fof(f307,plain,(
% 0.21/0.50    spl2_28 | ~spl2_6 | ~spl2_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f116,f95,f62,f305])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    spl2_6 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    spl2_13 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X1,X0))) ) | (~spl2_6 | ~spl2_13)),
% 0.21/0.50    inference(superposition,[],[f96,f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl2_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f62])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ) | ~spl2_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f95])).
% 0.21/0.50  fof(f168,plain,(
% 0.21/0.50    spl2_20 | ~spl2_13 | ~spl2_16),
% 0.21/0.50    inference(avatar_split_clause,[],[f163,f147,f95,f165])).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) | (~spl2_13 | ~spl2_16)),
% 0.21/0.50    inference(superposition,[],[f96,f149])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    spl2_16 | ~spl2_1 | ~spl2_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f102,f83,f40,f147])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    spl2_1 <=> r2_hidden(sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    spl2_10 <=> ! [X1,X0] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0)) | (~spl2_1 | ~spl2_10)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f42,f84])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1)) ) | ~spl2_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f83])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    r2_hidden(sK0,sK1) | ~spl2_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f40])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    spl2_14),
% 0.21/0.50    inference(avatar_split_clause,[],[f34,f99])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    spl2_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f31,f95])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    spl2_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f32,f83])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,axiom,(
% 0.21/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    spl2_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f28,f66])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    spl2_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f27,f62])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    spl2_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f25,f54])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    spl2_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f24,f50])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ~spl2_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f23,f45])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    sK1 != k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.21/0.50    inference(negated_conjecture,[],[f16])).
% 0.21/0.50  fof(f16,conjecture,(
% 0.21/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    spl2_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f22,f40])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    r2_hidden(sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (17708)------------------------------
% 0.21/0.50  % (17708)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (17708)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (17708)Memory used [KB]: 6396
% 0.21/0.50  % (17708)Time elapsed: 0.076 s
% 0.21/0.50  % (17708)------------------------------
% 0.21/0.50  % (17708)------------------------------
% 0.21/0.50  % (17704)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (17711)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (17699)Success in time 0.138 s
%------------------------------------------------------------------------------
