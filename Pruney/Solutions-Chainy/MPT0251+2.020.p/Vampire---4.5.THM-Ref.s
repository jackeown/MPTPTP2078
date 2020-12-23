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
% DateTime   : Thu Dec  3 12:38:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 127 expanded)
%              Number of leaves         :   21 (  53 expanded)
%              Depth                    :    8
%              Number of atoms          :  152 ( 240 expanded)
%              Number of equality atoms :   46 (  89 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f118,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f49,f53,f58,f62,f76,f90,f95,f101,f109,f117])).

fof(f117,plain,
    ( spl2_4
    | ~ spl2_8
    | ~ spl2_13 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | spl2_4
    | ~ spl2_8
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f112,f57])).

fof(f57,plain,
    ( sK1 != k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl2_4
  <=> sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f112,plain,
    ( sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | ~ spl2_8
    | ~ spl2_13 ),
    inference(superposition,[],[f75,f108])).

fof(f108,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl2_13
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f75,plain,
    ( ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,k3_xboole_0(X1,X0))) = X0
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl2_8
  <=> ! [X1,X0] : k3_tarski(k2_enumset1(X0,X0,X0,k3_xboole_0(X1,X0))) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f109,plain,
    ( spl2_13
    | ~ spl2_3
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f104,f98,f51,f106])).

fof(f51,plain,
    ( spl2_3
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f98,plain,
    ( spl2_12
  <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f104,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl2_3
    | ~ spl2_12 ),
    inference(resolution,[],[f100,f52])).

fof(f52,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0 )
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f100,plain,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f98])).

fof(f101,plain,
    ( spl2_12
    | ~ spl2_1
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f96,f93,f42,f98])).

fof(f42,plain,
    ( spl2_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f93,plain,
    ( spl2_11
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r1_tarski(k2_enumset1(sK0,sK0,sK0,X0),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f96,plain,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl2_1
    | ~ spl2_11 ),
    inference(resolution,[],[f94,f44])).

fof(f44,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f94,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r1_tarski(k2_enumset1(sK0,sK0,sK0,X0),sK1) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f93])).

fof(f95,plain,
    ( spl2_11
    | ~ spl2_1
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f91,f88,f42,f93])).

fof(f88,plain,
    ( spl2_10
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f91,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r1_tarski(k2_enumset1(sK0,sK0,sK0,X0),sK1) )
    | ~ spl2_1
    | ~ spl2_10 ),
    inference(resolution,[],[f89,f44])).

fof(f89,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X2)
        | ~ r2_hidden(X1,X2)
        | r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f88])).

fof(f90,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f37,f88])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f24,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f24,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f76,plain,
    ( spl2_8
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f71,f60,f47,f74])).

fof(f47,plain,
    ( spl2_2
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f60,plain,
    ( spl2_5
  <=> ! [X1,X0] : k3_tarski(k2_enumset1(X0,X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f71,plain,
    ( ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,k3_xboole_0(X1,X0))) = X0
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(superposition,[],[f61,f48])).

fof(f48,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f61,plain,
    ( ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,k3_xboole_0(X0,X1))) = X0
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f60])).

fof(f62,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f36,f60])).

fof(f36,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f23,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f25,f31])).

fof(f25,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f58,plain,(
    ~ spl2_4 ),
    inference(avatar_split_clause,[],[f40,f55])).

fof(f40,plain,(
    sK1 != k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(backward_demodulation,[],[f34,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f22,f31,f31])).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f34,plain,(
    sK1 != k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f19,f32,f33])).

fof(f33,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f20,f31])).

fof(f20,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f19,plain,(
    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f53,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f26,f51])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f49,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f21,f47])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f45,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f18,f42])).

fof(f18,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:29:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (9380)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.46  % (9387)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.46  % (9383)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (9382)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.46  % (9387)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f118,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f45,f49,f53,f58,f62,f76,f90,f95,f101,f109,f117])).
% 0.21/0.46  fof(f117,plain,(
% 0.21/0.46    spl2_4 | ~spl2_8 | ~spl2_13),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f116])).
% 0.21/0.46  fof(f116,plain,(
% 0.21/0.46    $false | (spl2_4 | ~spl2_8 | ~spl2_13)),
% 0.21/0.46    inference(subsumption_resolution,[],[f112,f57])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    sK1 != k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | spl2_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f55])).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    spl2_4 <=> sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.46  fof(f112,plain,(
% 0.21/0.46    sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | (~spl2_8 | ~spl2_13)),
% 0.21/0.46    inference(superposition,[],[f75,f108])).
% 0.21/0.46  fof(f108,plain,(
% 0.21/0.46    k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl2_13),
% 0.21/0.46    inference(avatar_component_clause,[],[f106])).
% 0.21/0.46  fof(f106,plain,(
% 0.21/0.46    spl2_13 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,k3_xboole_0(X1,X0))) = X0) ) | ~spl2_8),
% 0.21/0.46    inference(avatar_component_clause,[],[f74])).
% 0.21/0.46  fof(f74,plain,(
% 0.21/0.46    spl2_8 <=> ! [X1,X0] : k3_tarski(k2_enumset1(X0,X0,X0,k3_xboole_0(X1,X0))) = X0),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.46  fof(f109,plain,(
% 0.21/0.46    spl2_13 | ~spl2_3 | ~spl2_12),
% 0.21/0.46    inference(avatar_split_clause,[],[f104,f98,f51,f106])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    spl2_3 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.46  fof(f98,plain,(
% 0.21/0.46    spl2_12 <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.46  fof(f104,plain,(
% 0.21/0.46    k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | (~spl2_3 | ~spl2_12)),
% 0.21/0.46    inference(resolution,[],[f100,f52])).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) ) | ~spl2_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f51])).
% 0.21/0.46  fof(f100,plain,(
% 0.21/0.46    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl2_12),
% 0.21/0.46    inference(avatar_component_clause,[],[f98])).
% 0.21/0.46  fof(f101,plain,(
% 0.21/0.46    spl2_12 | ~spl2_1 | ~spl2_11),
% 0.21/0.46    inference(avatar_split_clause,[],[f96,f93,f42,f98])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    spl2_1 <=> r2_hidden(sK0,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.46  fof(f93,plain,(
% 0.21/0.46    spl2_11 <=> ! [X0] : (~r2_hidden(X0,sK1) | r1_tarski(k2_enumset1(sK0,sK0,sK0,X0),sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.46  fof(f96,plain,(
% 0.21/0.46    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | (~spl2_1 | ~spl2_11)),
% 0.21/0.46    inference(resolution,[],[f94,f44])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    r2_hidden(sK0,sK1) | ~spl2_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f42])).
% 0.21/0.46  fof(f94,plain,(
% 0.21/0.46    ( ! [X0] : (~r2_hidden(X0,sK1) | r1_tarski(k2_enumset1(sK0,sK0,sK0,X0),sK1)) ) | ~spl2_11),
% 0.21/0.46    inference(avatar_component_clause,[],[f93])).
% 0.21/0.46  fof(f95,plain,(
% 0.21/0.46    spl2_11 | ~spl2_1 | ~spl2_10),
% 0.21/0.46    inference(avatar_split_clause,[],[f91,f88,f42,f93])).
% 0.21/0.46  fof(f88,plain,(
% 0.21/0.46    spl2_10 <=> ! [X1,X0,X2] : (r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.46  fof(f91,plain,(
% 0.21/0.46    ( ! [X0] : (~r2_hidden(X0,sK1) | r1_tarski(k2_enumset1(sK0,sK0,sK0,X0),sK1)) ) | (~spl2_1 | ~spl2_10)),
% 0.21/0.46    inference(resolution,[],[f89,f44])).
% 0.21/0.46  fof(f89,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)) ) | ~spl2_10),
% 0.21/0.46    inference(avatar_component_clause,[],[f88])).
% 0.21/0.46  fof(f90,plain,(
% 0.21/0.46    spl2_10),
% 0.21/0.46    inference(avatar_split_clause,[],[f37,f88])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f30,f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f24,f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.46    inference(flattening,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.46    inference(nnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.21/0.46  fof(f76,plain,(
% 0.21/0.46    spl2_8 | ~spl2_2 | ~spl2_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f71,f60,f47,f74])).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    spl2_2 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    spl2_5 <=> ! [X1,X0] : k3_tarski(k2_enumset1(X0,X0,X0,k3_xboole_0(X0,X1))) = X0),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,k3_xboole_0(X1,X0))) = X0) ) | (~spl2_2 | ~spl2_5)),
% 0.21/0.46    inference(superposition,[],[f61,f48])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl2_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f47])).
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,k3_xboole_0(X0,X1))) = X0) ) | ~spl2_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f60])).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    spl2_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f36,f60])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,k3_xboole_0(X0,X1))) = X0) )),
% 0.21/0.46    inference(definition_unfolding,[],[f23,f32])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f25,f31])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,axiom,(
% 0.21/0.46    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    ~spl2_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f40,f55])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    sK1 != k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.21/0.46    inference(backward_demodulation,[],[f34,f35])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f22,f31,f31])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    sK1 != k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),sK1))),
% 0.21/0.46    inference(definition_unfolding,[],[f19,f32,f33])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f20,f31])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    sK1 != k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.21/0.46    inference(negated_conjecture,[],[f10])).
% 0.21/0.46  fof(f10,conjecture,(
% 0.21/0.46    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    spl2_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f26,f51])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    spl2_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f21,f47])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    spl2_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f18,f42])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    r2_hidden(sK0,sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (9387)------------------------------
% 0.21/0.46  % (9387)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (9387)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (9387)Memory used [KB]: 6140
% 0.21/0.46  % (9387)Time elapsed: 0.069 s
% 0.21/0.46  % (9387)------------------------------
% 0.21/0.46  % (9387)------------------------------
% 0.21/0.46  % (9378)Success in time 0.105 s
%------------------------------------------------------------------------------
