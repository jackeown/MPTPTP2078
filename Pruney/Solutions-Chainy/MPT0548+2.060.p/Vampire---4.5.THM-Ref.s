%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   71 (  88 expanded)
%              Number of leaves         :   22 (  39 expanded)
%              Depth                    :    7
%              Number of atoms          :  172 ( 213 expanded)
%              Number of equality atoms :   25 (  29 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f138,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f44,f49,f55,f60,f64,f68,f73,f121,f127,f134])).

fof(f134,plain,
    ( spl3_5
    | ~ spl3_6
    | ~ spl3_17 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | spl3_5
    | ~ spl3_6
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f59,f128])).

fof(f128,plain,
    ( ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)
    | ~ spl3_6
    | ~ spl3_17 ),
    inference(resolution,[],[f126,f63])).

fof(f63,plain,
    ( ! [X0] :
        ( r2_hidden(sK1(X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl3_6
  <=> ! [X0] :
        ( r2_hidden(sK1(X0),X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f126,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k9_relat_1(k1_xboole_0,X1))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl3_17
  <=> ! [X1,X0] : ~ r2_hidden(X0,k9_relat_1(k1_xboole_0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f59,plain,
    ( k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl3_5
  <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f127,plain,
    ( spl3_17
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f123,f119,f71,f52,f125])).

fof(f52,plain,
    ( spl3_4
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f71,plain,
    ( spl3_8
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f119,plain,
    ( spl3_16
  <=> ! [X1,X0,X2] :
        ( r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2)
        | ~ r2_hidden(X0,k9_relat_1(X2,X1))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f123,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k9_relat_1(k1_xboole_0,X1))
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f122,f54])).

fof(f54,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f52])).

fof(f122,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(k1_xboole_0,X1))
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl3_8
    | ~ spl3_16 ),
    inference(resolution,[],[f120,f72])).

fof(f72,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f71])).

fof(f120,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2)
        | ~ r2_hidden(X0,k9_relat_1(X2,X1))
        | ~ v1_relat_1(X2) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f119])).

fof(f121,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f32,f119])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2)
            & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2)
        & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f73,plain,
    ( spl3_8
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f69,f66,f42,f71])).

fof(f42,plain,
    ( spl3_2
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f66,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_xboole_0(k1_enumset1(X0,X0,X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f69,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(resolution,[],[f67,f43])).

fof(f43,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(k1_enumset1(X0,X0,X0),X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f66])).

fof(f68,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f36,f66])).

% (9690)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% (9692)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% (9693)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% (9700)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% (9698)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% (9694)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% (9705)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% (9701)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% (9702)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% (9704)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_enumset1(X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f30,f35])).

fof(f35,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f27,f29])).

fof(f29,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f27,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f64,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f28,f62])).

fof(f28,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f17])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f60,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f23,f57])).

fof(f23,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f15])).

fof(f15,plain,
    ( ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

fof(f55,plain,
    ( spl3_4
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f50,f46,f38,f52])).

fof(f38,plain,
    ( spl3_1
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f46,plain,
    ( spl3_3
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f50,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(superposition,[],[f39,f48])).

fof(f48,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f39,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f49,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f24,f46])).

fof(f24,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f44,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f26,f42])).

fof(f26,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f40,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f25,f38])).

fof(f25,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:31:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (9695)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (9695)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f138,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f40,f44,f49,f55,f60,f64,f68,f73,f121,f127,f134])).
% 0.22/0.48  fof(f134,plain,(
% 0.22/0.48    spl3_5 | ~spl3_6 | ~spl3_17),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f132])).
% 0.22/0.48  fof(f132,plain,(
% 0.22/0.48    $false | (spl3_5 | ~spl3_6 | ~spl3_17)),
% 0.22/0.48    inference(subsumption_resolution,[],[f59,f128])).
% 0.22/0.48  fof(f128,plain,(
% 0.22/0.48    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) ) | (~spl3_6 | ~spl3_17)),
% 0.22/0.48    inference(resolution,[],[f126,f63])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) ) | ~spl3_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f62])).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    spl3_6 <=> ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.48  fof(f126,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(k1_xboole_0,X1))) ) | ~spl3_17),
% 0.22/0.48    inference(avatar_component_clause,[],[f125])).
% 0.22/0.48  fof(f125,plain,(
% 0.22/0.48    spl3_17 <=> ! [X1,X0] : ~r2_hidden(X0,k9_relat_1(k1_xboole_0,X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) | spl3_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f57])).
% 0.22/0.48  fof(f57,plain,(
% 0.22/0.48    spl3_5 <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.48  fof(f127,plain,(
% 0.22/0.48    spl3_17 | ~spl3_4 | ~spl3_8 | ~spl3_16),
% 0.22/0.48    inference(avatar_split_clause,[],[f123,f119,f71,f52,f125])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    spl3_4 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    spl3_8 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.48  fof(f119,plain,(
% 0.22/0.48    spl3_16 <=> ! [X1,X0,X2] : (r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.48  fof(f123,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(k1_xboole_0,X1))) ) | (~spl3_4 | ~spl3_8 | ~spl3_16)),
% 0.22/0.48    inference(subsumption_resolution,[],[f122,f54])).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    v1_relat_1(k1_xboole_0) | ~spl3_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f52])).
% 0.22/0.48  fof(f122,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(k1_xboole_0,X1)) | ~v1_relat_1(k1_xboole_0)) ) | (~spl3_8 | ~spl3_16)),
% 0.22/0.48    inference(resolution,[],[f120,f72])).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl3_8),
% 0.22/0.48    inference(avatar_component_clause,[],[f71])).
% 0.22/0.48  fof(f120,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) ) | ~spl3_16),
% 0.22/0.48    inference(avatar_component_clause,[],[f119])).
% 0.22/0.48  fof(f121,plain,(
% 0.22/0.48    spl3_16),
% 0.22/0.48    inference(avatar_split_clause,[],[f32,f119])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.48    inference(rectify,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.48    inference(nnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    spl3_8 | ~spl3_2 | ~spl3_7),
% 0.22/0.48    inference(avatar_split_clause,[],[f69,f66,f42,f71])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    spl3_2 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    spl3_7 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_enumset1(X0,X0,X0),X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl3_2 | ~spl3_7)),
% 0.22/0.48    inference(resolution,[],[f67,f43])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl3_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f42])).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_xboole_0(k1_enumset1(X0,X0,X0),X1) | ~r2_hidden(X0,X1)) ) | ~spl3_7),
% 0.22/0.48    inference(avatar_component_clause,[],[f66])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    spl3_7),
% 0.22/0.48    inference(avatar_split_clause,[],[f36,f66])).
% 0.22/0.48  % (9690)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (9692)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (9693)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (9700)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (9698)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (9694)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (9705)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.48  % (9701)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (9702)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (9704)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_enumset1(X0,X0,X0),X1)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f30,f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f27,f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    spl3_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f28,f62])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    ~spl3_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f23,f57])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,negated_conjecture,(
% 0.22/0.49    ~! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.22/0.49    inference(negated_conjecture,[],[f9])).
% 0.22/0.49  fof(f9,conjecture,(
% 0.22/0.49    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    spl3_4 | ~spl3_1 | ~spl3_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f50,f46,f38,f52])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    spl3_1 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    spl3_3 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    v1_relat_1(k1_xboole_0) | (~spl3_1 | ~spl3_3)),
% 0.22/0.49    inference(superposition,[],[f39,f48])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl3_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f46])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl3_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f38])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    spl3_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f24,f46])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    spl3_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f26,f42])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    spl3_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f25,f38])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (9695)------------------------------
% 0.22/0.49  % (9695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (9695)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (9695)Memory used [KB]: 6140
% 0.22/0.49  % (9695)Time elapsed: 0.050 s
% 0.22/0.49  % (9695)------------------------------
% 0.22/0.49  % (9695)------------------------------
% 0.22/0.49  % (9687)Success in time 0.12 s
%------------------------------------------------------------------------------
