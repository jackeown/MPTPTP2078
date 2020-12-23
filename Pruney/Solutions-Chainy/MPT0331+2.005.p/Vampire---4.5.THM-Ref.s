%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 109 expanded)
%              Number of leaves         :   19 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :  131 ( 212 expanded)
%              Number of equality atoms :   58 (  94 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f920,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f61,f66,f116,f123,f335,f892])).

fof(f892,plain,
    ( spl3_1
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f872,f332,f120,f53])).

fof(f53,plain,
    ( spl3_1
  <=> sK2 = k4_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f120,plain,
    ( spl3_6
  <=> sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f332,plain,
    ( spl3_9
  <=> k2_enumset1(sK0,sK0,sK0,sK1) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f872,plain,
    ( sK2 = k4_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(superposition,[],[f842,f334])).

fof(f334,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK1) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f332])).

fof(f842,plain,
    ( ! [X14] : sK2 = k4_xboole_0(sK2,k4_xboole_0(X14,sK2))
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f811,f25])).

fof(f25,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f811,plain,
    ( ! [X14] : k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,k4_xboole_0(X14,sK2))
    | ~ spl3_6 ),
    inference(superposition,[],[f43,f282])).

fof(f282,plain,
    ( ! [X7] : k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X7,sK2)))
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f281,f67])).

fof(f67,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f27,f28])).

% (13661)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f27,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f281,plain,
    ( ! [X7] : k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X7,sK2))) = k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,X7),sK2))
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f205,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f205,plain,
    ( ! [X7] : k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X7,sK2))) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,X7)),sK2)
    | ~ spl3_6 ),
    inference(superposition,[],[f46,f122])).

fof(f122,plain,
    ( sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK2))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f120])).

fof(f46,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f35,f29,f29,f29])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f35,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f30,f29])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f335,plain,
    ( spl3_9
    | spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f310,f63,f58,f332])).

fof(f58,plain,
    ( spl3_2
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f63,plain,
    ( spl3_3
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f310,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK1) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)
    | spl3_2
    | spl3_3 ),
    inference(unit_resulting_resolution,[],[f60,f65,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | r2_hidden(X0,X2)
      | k2_enumset1(X0,X0,X0,X1) = k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f40,f31,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f65,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f60,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f123,plain,
    ( spl3_6
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f117,f106,f120])).

fof(f106,plain,
    ( spl3_4
  <=> sK2 = k4_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f117,plain,
    ( sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK2))
    | ~ spl3_4 ),
    inference(superposition,[],[f43,f108])).

fof(f108,plain,
    ( sK2 = k4_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f106])).

fof(f116,plain,
    ( spl3_4
    | spl3_3 ),
    inference(avatar_split_clause,[],[f104,f63,f106])).

fof(f104,plain,
    ( sK2 = k4_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | spl3_3 ),
    inference(resolution,[],[f44,f65])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f33,f41])).

fof(f41,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f26,f31])).

fof(f26,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f66,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f22,f63])).

fof(f22,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1))
    & ~ r2_hidden(sK1,sK2)
    & ~ r2_hidden(sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) )
   => ( sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1))
      & ~ r2_hidden(sK1,sK2)
      & ~ r2_hidden(sK0,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
      & ~ r2_hidden(X1,X2)
      & ~ r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
          & ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(f61,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f23,f58])).

fof(f23,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f56,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f42,f53])).

fof(f42,plain,(
    sK2 != k4_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(definition_unfolding,[],[f24,f31])).

fof(f24,plain,(
    sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:05:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (13666)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (13665)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (13664)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (13673)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (13663)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (13674)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % (13675)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (13676)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (13667)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (13672)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (13670)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.48  % (13671)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (13668)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (13662)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (13667)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (13678)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f920,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f56,f61,f66,f116,f123,f335,f892])).
% 0.21/0.50  fof(f892,plain,(
% 0.21/0.50    spl3_1 | ~spl3_6 | ~spl3_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f872,f332,f120,f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    spl3_1 <=> sK2 = k4_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    spl3_6 <=> sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.50  fof(f332,plain,(
% 0.21/0.50    spl3_9 <=> k2_enumset1(sK0,sK0,sK0,sK1) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.50  fof(f872,plain,(
% 0.21/0.50    sK2 = k4_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)) | (~spl3_6 | ~spl3_9)),
% 0.21/0.50    inference(superposition,[],[f842,f334])).
% 0.21/0.50  fof(f334,plain,(
% 0.21/0.50    k2_enumset1(sK0,sK0,sK0,sK1) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) | ~spl3_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f332])).
% 0.21/0.50  fof(f842,plain,(
% 0.21/0.50    ( ! [X14] : (sK2 = k4_xboole_0(sK2,k4_xboole_0(X14,sK2))) ) | ~spl3_6),
% 0.21/0.50    inference(forward_demodulation,[],[f811,f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.50  fof(f811,plain,(
% 0.21/0.50    ( ! [X14] : (k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,k4_xboole_0(X14,sK2))) ) | ~spl3_6),
% 0.21/0.50    inference(superposition,[],[f43,f282])).
% 0.21/0.50  fof(f282,plain,(
% 0.21/0.50    ( ! [X7] : (k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X7,sK2)))) ) | ~spl3_6),
% 0.21/0.50    inference(forward_demodulation,[],[f281,f67])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0))) )),
% 0.21/0.50    inference(superposition,[],[f27,f28])).
% 0.21/0.50  % (13661)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.21/0.50  fof(f281,plain,(
% 0.21/0.50    ( ! [X7] : (k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X7,sK2))) = k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,X7),sK2))) ) | ~spl3_6),
% 0.21/0.50    inference(forward_demodulation,[],[f205,f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.50  fof(f205,plain,(
% 0.21/0.50    ( ! [X7] : (k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X7,sK2))) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,X7)),sK2)) ) | ~spl3_6),
% 0.21/0.50    inference(superposition,[],[f46,f122])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)) | ~spl3_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f120])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f35,f29,f29,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f30,f29])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.21/0.50  fof(f335,plain,(
% 0.21/0.50    spl3_9 | spl3_2 | spl3_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f310,f63,f58,f332])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    spl3_2 <=> r2_hidden(sK1,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    spl3_3 <=> r2_hidden(sK0,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.50  fof(f310,plain,(
% 0.21/0.50    k2_enumset1(sK0,sK0,sK0,sK1) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) | (spl3_2 | spl3_3)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f60,f65,f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_enumset1(X0,X0,X0,X1) = k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f40,f31,f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.21/0.50    inference(flattening,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.21/0.50    inference(nnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ~r2_hidden(sK0,sK2) | spl3_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f63])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ~r2_hidden(sK1,sK2) | spl3_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f58])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    spl3_6 | ~spl3_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f117,f106,f120])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    spl3_4 <=> sK2 = k4_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)) | ~spl3_4),
% 0.21/0.50    inference(superposition,[],[f43,f108])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    sK2 = k4_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl3_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f106])).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    spl3_4 | spl3_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f104,f63,f106])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    sK2 = k4_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | spl3_3),
% 0.21/0.50    inference(resolution,[],[f44,f65])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0) )),
% 0.21/0.50    inference(definition_unfolding,[],[f33,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f26,f31])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ~spl3_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f22,f63])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ~r2_hidden(sK0,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1)) & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) => (sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1)) & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 0.21/0.50    inference(ennf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 0.21/0.50    inference(negated_conjecture,[],[f14])).
% 0.21/0.50  fof(f14,conjecture,(
% 0.21/0.50    ! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ~spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f23,f58])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ~r2_hidden(sK1,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ~spl3_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f42,f53])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    sK2 != k4_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1))),
% 0.21/0.50    inference(definition_unfolding,[],[f24,f31])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (13667)------------------------------
% 0.21/0.50  % (13667)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (13667)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (13667)Memory used [KB]: 6652
% 0.21/0.50  % (13667)Time elapsed: 0.026 s
% 0.21/0.50  % (13667)------------------------------
% 0.21/0.50  % (13667)------------------------------
% 0.21/0.51  % (13655)Success in time 0.153 s
%------------------------------------------------------------------------------
