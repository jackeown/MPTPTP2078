%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:10 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 154 expanded)
%              Number of leaves         :   22 (  54 expanded)
%              Depth                    :   13
%              Number of atoms          :  141 ( 255 expanded)
%              Number of equality atoms :   58 ( 131 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (21124)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
fof(f325,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f68,f118,f136,f314,f324])).

fof(f324,plain,
    ( ~ spl3_6
    | spl3_8 ),
    inference(avatar_contradiction_clause,[],[f323])).

fof(f323,plain,
    ( $false
    | ~ spl3_6
    | spl3_8 ),
    inference(subsumption_resolution,[],[f322,f28])).

fof(f28,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f322,plain,
    ( sK1 != k5_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_6
    | spl3_8 ),
    inference(forward_demodulation,[],[f319,f164])).

fof(f164,plain,
    ( k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)))
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f160,f29])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f160,plain,
    ( k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1))
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f135,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f36,f33])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f135,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl3_6
  <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f319,plain,
    ( sK1 != k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2))))
    | spl3_8 ),
    inference(superposition,[],[f313,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f313,plain,
    ( sK1 != k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f311])).

fof(f311,plain,
    ( spl3_8
  <=> sK1 = k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f314,plain,
    ( ~ spl3_8
    | spl3_3 ),
    inference(avatar_split_clause,[],[f126,f115,f311])).

fof(f115,plain,
    ( spl3_3
  <=> sK1 = k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f126,plain,
    ( sK1 != k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)))
    | spl3_3 ),
    inference(forward_demodulation,[],[f125,f30])).

fof(f30,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f125,plain,
    ( sK1 != k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)))
    | spl3_3 ),
    inference(forward_demodulation,[],[f124,f29])).

fof(f124,plain,
    ( sK1 != k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1))
    | spl3_3 ),
    inference(superposition,[],[f117,f53])).

% (21130)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% (21138)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% (21126)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% (21134)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% (21133)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% (21133)Refutation not found, incomplete strategy% (21133)------------------------------
% (21133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (21133)Termination reason: Refutation not found, incomplete strategy

% (21133)Memory used [KB]: 10618
% (21133)Time elapsed: 0.069 s
% (21133)------------------------------
% (21133)------------------------------
% (21128)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% (21131)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
fof(f53,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f34,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f31,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f32,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f37,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f42,f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f43,f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f45,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f117,plain,
    ( sK1 != k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f115])).

fof(f136,plain,
    ( spl3_6
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f96,f65,f60,f133])).

fof(f60,plain,
    ( spl3_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f65,plain,
    ( spl3_2
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f96,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1)
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f62,f67,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f41,f50])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f67,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f62,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f118,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f52,f115])).

fof(f52,plain,(
    sK1 != k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1)) ),
    inference(definition_unfolding,[],[f27,f51,f50])).

fof(f27,plain,(
    sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1)
    & r2_hidden(sK2,sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
        & r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1)
      & r2_hidden(sK2,sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(X2,X1)
          & r2_hidden(X0,X1) )
       => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).

fof(f68,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f26,f65])).

fof(f26,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f63,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f25,f60])).

fof(f25,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:48:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.43  % (21123)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.46  % (21137)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.46  % (21132)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (21127)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (21139)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.48  % (21137)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  % (21124)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  fof(f325,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f63,f68,f118,f136,f314,f324])).
% 0.22/0.48  fof(f324,plain,(
% 0.22/0.48    ~spl3_6 | spl3_8),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f323])).
% 0.22/0.48  fof(f323,plain,(
% 0.22/0.48    $false | (~spl3_6 | spl3_8)),
% 0.22/0.48    inference(subsumption_resolution,[],[f322,f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.22/0.48  fof(f322,plain,(
% 0.22/0.48    sK1 != k5_xboole_0(sK1,k1_xboole_0) | (~spl3_6 | spl3_8)),
% 0.22/0.48    inference(forward_demodulation,[],[f319,f164])).
% 0.22/0.48  fof(f164,plain,(
% 0.22/0.48    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2))) | ~spl3_6),
% 0.22/0.48    inference(forward_demodulation,[],[f160,f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.48  fof(f160,plain,(
% 0.22/0.48    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1)) | ~spl3_6),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f135,f54])).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f36,f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.22/0.48    inference(nnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.48  fof(f135,plain,(
% 0.22/0.48    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1) | ~spl3_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f133])).
% 0.22/0.48  fof(f133,plain,(
% 0.22/0.48    spl3_6 <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.48  fof(f319,plain,(
% 0.22/0.48    sK1 != k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)))) | spl3_8),
% 0.22/0.48    inference(superposition,[],[f313,f38])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.22/0.48  fof(f313,plain,(
% 0.22/0.48    sK1 != k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2))) | spl3_8),
% 0.22/0.48    inference(avatar_component_clause,[],[f311])).
% 0.22/0.48  fof(f311,plain,(
% 0.22/0.48    spl3_8 <=> sK1 = k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.48  fof(f314,plain,(
% 0.22/0.48    ~spl3_8 | spl3_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f126,f115,f311])).
% 0.22/0.48  fof(f115,plain,(
% 0.22/0.48    spl3_3 <=> sK1 = k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.48  fof(f126,plain,(
% 0.22/0.48    sK1 != k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2))) | spl3_3),
% 0.22/0.48    inference(forward_demodulation,[],[f125,f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.22/0.48  fof(f125,plain,(
% 0.22/0.48    sK1 != k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2))) | spl3_3),
% 0.22/0.48    inference(forward_demodulation,[],[f124,f29])).
% 0.22/0.48  fof(f124,plain,(
% 0.22/0.48    sK1 != k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1)) | spl3_3),
% 0.22/0.48    inference(superposition,[],[f117,f53])).
% 0.22/0.48  % (21130)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.49  % (21138)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.49  % (21126)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (21134)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (21133)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.49  % (21133)Refutation not found, incomplete strategy% (21133)------------------------------
% 0.22/0.49  % (21133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (21133)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (21133)Memory used [KB]: 10618
% 0.22/0.49  % (21133)Time elapsed: 0.069 s
% 0.22/0.49  % (21133)------------------------------
% 0.22/0.49  % (21133)------------------------------
% 0.22/0.49  % (21128)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  % (21131)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.22/0.50    inference(definition_unfolding,[],[f34,f51])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.22/0.50    inference(definition_unfolding,[],[f31,f50])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f32,f49])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f37,f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f42,f47])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f43,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f44,f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,axiom,(
% 0.22/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    sK1 != k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1)) | spl3_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f115])).
% 0.22/0.50  fof(f136,plain,(
% 0.22/0.50    spl3_6 | ~spl3_1 | ~spl3_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f96,f65,f60,f133])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    spl3_1 <=> r2_hidden(sK0,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    spl3_2 <=> r2_hidden(sK2,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1) | (~spl3_1 | ~spl3_2)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f62,f67,f56])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f41,f50])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.22/0.50    inference(flattening,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.22/0.50    inference(nnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    r2_hidden(sK2,sK1) | ~spl3_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f65])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    r2_hidden(sK0,sK1) | ~spl3_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f60])).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    ~spl3_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f52,f115])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    sK1 != k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1))),
% 0.22/0.50    inference(definition_unfolding,[],[f27,f51,f50])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1) & r2_hidden(sK2,sK1) & r2_hidden(sK0,sK1)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1) & r2_hidden(sK2,sK1) & r2_hidden(sK0,sK1))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1))),
% 0.22/0.50    inference(flattening,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & (r2_hidden(X2,X1) & r2_hidden(X0,X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 0.22/0.50    inference(negated_conjecture,[],[f16])).
% 0.22/0.50  fof(f16,conjecture,(
% 0.22/0.50    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    spl3_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f26,f65])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    r2_hidden(sK2,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    spl3_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f25,f60])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    r2_hidden(sK0,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (21137)------------------------------
% 0.22/0.50  % (21137)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (21137)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (21137)Memory used [KB]: 11001
% 0.22/0.50  % (21137)Time elapsed: 0.078 s
% 0.22/0.50  % (21137)------------------------------
% 0.22/0.50  % (21137)------------------------------
% 0.22/0.50  % (21125)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.50  % (21121)Success in time 0.138 s
%------------------------------------------------------------------------------
