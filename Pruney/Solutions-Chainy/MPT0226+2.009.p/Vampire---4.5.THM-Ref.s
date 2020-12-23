%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:14 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 185 expanded)
%              Number of leaves         :   18 (  64 expanded)
%              Depth                    :   12
%              Number of atoms          :  117 ( 251 expanded)
%              Number of equality atoms :   81 ( 207 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f156,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f81,f101,f120,f155])).

fof(f155,plain,
    ( spl3_1
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | spl3_1
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f75,f70,f135])).

fof(f135,plain,
    ( ! [X11] :
        ( ~ r2_hidden(X11,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
        | sK1 = X11 )
    | ~ spl3_4 ),
    inference(duplicate_literal_removal,[],[f133])).

fof(f133,plain,
    ( ! [X11] :
        ( ~ r2_hidden(X11,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
        | sK1 = X11
        | sK1 = X11
        | sK1 = X11 )
    | ~ spl3_4 ),
    inference(superposition,[],[f71,f118])).

fof(f118,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl3_4
  <=> k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f38,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f32,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f33,f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f42,f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f32,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f70,plain,(
    ! [X4,X2,X1] : r2_hidden(X4,k6_enumset1(X4,X4,X4,X4,X4,X4,X1,X2)) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X4,X3)
      | k6_enumset1(X4,X4,X4,X4,X4,X4,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f39,f50])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f75,plain,
    ( sK0 != sK1
    | spl3_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl3_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f120,plain,
    ( spl3_4
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f107,f98,f116])).

fof(f98,plain,
    ( spl3_3
  <=> k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f107,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | ~ spl3_3 ),
    inference(superposition,[],[f25,f100])).

fof(f100,plain,
    ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f98])).

fof(f25,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f101,plain,
    ( spl3_3
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f94,f78,f98])).

fof(f78,plain,
    ( spl3_2
  <=> k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f94,plain,
    ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f90,f56])).

fof(f56,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f27,f51,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f28,f50])).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f90,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0)
    | ~ spl3_2 ),
    inference(superposition,[],[f54,f80])).

fof(f80,plain,
    ( k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) ),
    inference(definition_unfolding,[],[f45,f46,f44,f52])).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f26,f51])).

fof(f26,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f29,f31])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f45,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

fof(f81,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f55,f78])).

fof(f55,plain,(
    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f21,f31,f52,f52])).

fof(f21,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

fof(f76,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f22,f73])).

fof(f22,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:26:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (20739)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (20754)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (20740)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (20741)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.20/0.53  % (20762)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.20/0.53  % (20749)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.20/0.53  % (20743)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.20/0.53  % (20736)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.20/0.54  % (20758)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.20/0.54  % (20747)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.20/0.54  % (20757)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.20/0.54  % (20740)Refutation not found, incomplete strategy% (20740)------------------------------
% 1.20/0.54  % (20740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.54  % (20740)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.54  
% 1.20/0.54  % (20740)Memory used [KB]: 6140
% 1.20/0.54  % (20740)Time elapsed: 0.109 s
% 1.20/0.54  % (20740)------------------------------
% 1.20/0.54  % (20740)------------------------------
% 1.20/0.54  % (20736)Refutation not found, incomplete strategy% (20736)------------------------------
% 1.20/0.54  % (20736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (20765)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.39/0.54  % (20751)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.39/0.54  % (20736)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  
% 1.39/0.54  % (20736)Memory used [KB]: 1663
% 1.39/0.54  % (20736)Time elapsed: 0.126 s
% 1.39/0.54  % (20736)------------------------------
% 1.39/0.54  % (20736)------------------------------
% 1.39/0.54  % (20742)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.39/0.55  % (20758)Refutation found. Thanks to Tanya!
% 1.39/0.55  % SZS status Theorem for theBenchmark
% 1.39/0.55  % (20763)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.39/0.55  % (20750)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.39/0.55  % (20751)Refutation not found, incomplete strategy% (20751)------------------------------
% 1.39/0.55  % (20751)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (20764)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.39/0.55  % (20759)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.39/0.55  % (20751)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (20751)Memory used [KB]: 6140
% 1.39/0.55  % (20751)Time elapsed: 0.139 s
% 1.39/0.55  % (20751)------------------------------
% 1.39/0.55  % (20751)------------------------------
% 1.39/0.55  % (20759)Refutation not found, incomplete strategy% (20759)------------------------------
% 1.39/0.55  % (20759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (20759)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (20759)Memory used [KB]: 1663
% 1.39/0.55  % (20759)Time elapsed: 0.138 s
% 1.39/0.55  % (20759)------------------------------
% 1.39/0.55  % (20759)------------------------------
% 1.39/0.55  % (20746)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.39/0.55  % (20755)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.39/0.55  % (20746)Refutation not found, incomplete strategy% (20746)------------------------------
% 1.39/0.55  % (20746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (20746)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (20746)Memory used [KB]: 10618
% 1.39/0.55  % (20746)Time elapsed: 0.137 s
% 1.39/0.55  % (20746)------------------------------
% 1.39/0.55  % (20746)------------------------------
% 1.39/0.55  % (20756)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.39/0.55  % (20748)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.39/0.56  % (20756)Refutation not found, incomplete strategy% (20756)------------------------------
% 1.39/0.56  % (20756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (20747)Refutation not found, incomplete strategy% (20747)------------------------------
% 1.39/0.56  % (20747)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (20747)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.56  
% 1.39/0.56  % (20747)Memory used [KB]: 10618
% 1.39/0.56  % (20747)Time elapsed: 0.152 s
% 1.39/0.56  % (20747)------------------------------
% 1.39/0.56  % (20747)------------------------------
% 1.39/0.56  % (20756)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.56  
% 1.39/0.56  % (20756)Memory used [KB]: 10746
% 1.39/0.56  % (20756)Time elapsed: 0.141 s
% 1.39/0.56  % (20756)------------------------------
% 1.39/0.56  % (20756)------------------------------
% 1.39/0.56  % (20744)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.39/0.57  % (20737)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.39/0.57  % (20738)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.39/0.57  % SZS output start Proof for theBenchmark
% 1.39/0.57  fof(f156,plain,(
% 1.39/0.57    $false),
% 1.39/0.57    inference(avatar_sat_refutation,[],[f76,f81,f101,f120,f155])).
% 1.39/0.57  fof(f155,plain,(
% 1.39/0.57    spl3_1 | ~spl3_4),
% 1.39/0.57    inference(avatar_contradiction_clause,[],[f145])).
% 1.39/0.57  fof(f145,plain,(
% 1.39/0.57    $false | (spl3_1 | ~spl3_4)),
% 1.39/0.57    inference(unit_resulting_resolution,[],[f75,f70,f135])).
% 1.39/0.57  fof(f135,plain,(
% 1.39/0.57    ( ! [X11] : (~r2_hidden(X11,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK1 = X11) ) | ~spl3_4),
% 1.39/0.57    inference(duplicate_literal_removal,[],[f133])).
% 1.39/0.57  fof(f133,plain,(
% 1.39/0.57    ( ! [X11] : (~r2_hidden(X11,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK1 = X11 | sK1 = X11 | sK1 = X11) ) | ~spl3_4),
% 1.39/0.57    inference(superposition,[],[f71,f118])).
% 1.39/0.57  fof(f118,plain,(
% 1.39/0.57    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) | ~spl3_4),
% 1.39/0.57    inference(avatar_component_clause,[],[f116])).
% 1.39/0.57  fof(f116,plain,(
% 1.39/0.57    spl3_4 <=> k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 1.39/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.39/0.57  fof(f71,plain,(
% 1.39/0.57    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 1.39/0.57    inference(equality_resolution,[],[f60])).
% 1.39/0.57  fof(f60,plain,(
% 1.39/0.57    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 1.39/0.57    inference(definition_unfolding,[],[f38,f50])).
% 1.39/0.57  fof(f50,plain,(
% 1.39/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.39/0.57    inference(definition_unfolding,[],[f32,f49])).
% 1.39/0.57  fof(f49,plain,(
% 1.39/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.39/0.57    inference(definition_unfolding,[],[f33,f48])).
% 1.39/0.57  fof(f48,plain,(
% 1.39/0.57    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.39/0.57    inference(definition_unfolding,[],[f42,f47])).
% 1.39/0.57  fof(f47,plain,(
% 1.39/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.39/0.57    inference(definition_unfolding,[],[f43,f44])).
% 1.39/0.57  fof(f44,plain,(
% 1.39/0.57    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 1.39/0.57    inference(cnf_transformation,[],[f16])).
% 1.39/0.57  fof(f16,axiom,(
% 1.39/0.57    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 1.39/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.39/0.57  fof(f43,plain,(
% 1.39/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.39/0.57    inference(cnf_transformation,[],[f15])).
% 1.39/0.57  fof(f15,axiom,(
% 1.39/0.57    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.39/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.39/0.57  fof(f42,plain,(
% 1.39/0.57    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.39/0.57    inference(cnf_transformation,[],[f14])).
% 1.39/0.57  fof(f14,axiom,(
% 1.39/0.57    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.39/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.39/0.57  fof(f33,plain,(
% 1.39/0.57    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.39/0.57    inference(cnf_transformation,[],[f13])).
% 1.39/0.57  fof(f13,axiom,(
% 1.39/0.57    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.39/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.39/0.57  fof(f32,plain,(
% 1.39/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.39/0.57    inference(cnf_transformation,[],[f12])).
% 1.39/0.57  fof(f12,axiom,(
% 1.39/0.57    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.39/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.39/0.57  fof(f38,plain,(
% 1.39/0.57    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.39/0.57    inference(cnf_transformation,[],[f20])).
% 1.39/0.57  fof(f20,plain,(
% 1.39/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.39/0.57    inference(ennf_transformation,[],[f8])).
% 1.39/0.57  fof(f8,axiom,(
% 1.39/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.39/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.39/0.57  fof(f70,plain,(
% 1.39/0.57    ( ! [X4,X2,X1] : (r2_hidden(X4,k6_enumset1(X4,X4,X4,X4,X4,X4,X1,X2))) )),
% 1.39/0.57    inference(equality_resolution,[],[f69])).
% 1.39/0.57  fof(f69,plain,(
% 1.39/0.57    ( ! [X4,X2,X3,X1] : (r2_hidden(X4,X3) | k6_enumset1(X4,X4,X4,X4,X4,X4,X1,X2) != X3) )),
% 1.39/0.57    inference(equality_resolution,[],[f59])).
% 1.39/0.57  fof(f59,plain,(
% 1.39/0.57    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 1.39/0.57    inference(definition_unfolding,[],[f39,f50])).
% 1.39/0.57  fof(f39,plain,(
% 1.39/0.57    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.39/0.57    inference(cnf_transformation,[],[f20])).
% 1.39/0.57  fof(f75,plain,(
% 1.39/0.57    sK0 != sK1 | spl3_1),
% 1.39/0.57    inference(avatar_component_clause,[],[f73])).
% 1.39/0.57  fof(f73,plain,(
% 1.39/0.57    spl3_1 <=> sK0 = sK1),
% 1.39/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.39/0.57  fof(f120,plain,(
% 1.39/0.57    spl3_4 | ~spl3_3),
% 1.39/0.57    inference(avatar_split_clause,[],[f107,f98,f116])).
% 1.39/0.57  fof(f98,plain,(
% 1.39/0.57    spl3_3 <=> k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 1.39/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.39/0.57  fof(f107,plain,(
% 1.39/0.57    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) | ~spl3_3),
% 1.39/0.57    inference(superposition,[],[f25,f100])).
% 1.39/0.57  fof(f100,plain,(
% 1.39/0.57    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) | ~spl3_3),
% 1.39/0.57    inference(avatar_component_clause,[],[f98])).
% 1.39/0.57  fof(f25,plain,(
% 1.39/0.57    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.39/0.57    inference(cnf_transformation,[],[f4])).
% 1.39/0.57  fof(f4,axiom,(
% 1.39/0.57    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.39/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.39/0.57  fof(f101,plain,(
% 1.39/0.57    spl3_3 | ~spl3_2),
% 1.39/0.57    inference(avatar_split_clause,[],[f94,f78,f98])).
% 1.39/0.57  fof(f78,plain,(
% 1.39/0.57    spl3_2 <=> k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 1.39/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.39/0.57  fof(f94,plain,(
% 1.39/0.57    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) | ~spl3_2),
% 1.39/0.57    inference(forward_demodulation,[],[f90,f56])).
% 1.39/0.57  fof(f56,plain,(
% 1.39/0.57    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 1.39/0.57    inference(definition_unfolding,[],[f27,f51,f51])).
% 1.39/0.57  fof(f51,plain,(
% 1.39/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.39/0.57    inference(definition_unfolding,[],[f28,f50])).
% 1.39/0.57  fof(f28,plain,(
% 1.39/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.39/0.57    inference(cnf_transformation,[],[f11])).
% 1.39/0.57  fof(f11,axiom,(
% 1.39/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.39/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.39/0.57  fof(f27,plain,(
% 1.39/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.39/0.57    inference(cnf_transformation,[],[f7])).
% 1.39/0.57  fof(f7,axiom,(
% 1.39/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.39/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.39/0.57  fof(f90,plain,(
% 1.39/0.57    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) | ~spl3_2),
% 1.39/0.57    inference(superposition,[],[f54,f80])).
% 1.39/0.57  fof(f80,plain,(
% 1.39/0.57    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) | ~spl3_2),
% 1.39/0.57    inference(avatar_component_clause,[],[f78])).
% 1.39/0.57  fof(f54,plain,(
% 1.39/0.57    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6))))) )),
% 1.39/0.57    inference(definition_unfolding,[],[f45,f46,f44,f52])).
% 1.39/0.57  fof(f52,plain,(
% 1.39/0.57    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.39/0.57    inference(definition_unfolding,[],[f26,f51])).
% 1.39/0.57  fof(f26,plain,(
% 1.39/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.39/0.57    inference(cnf_transformation,[],[f10])).
% 1.39/0.57  fof(f10,axiom,(
% 1.39/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.39/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.39/0.57  fof(f46,plain,(
% 1.39/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.39/0.57    inference(definition_unfolding,[],[f29,f31])).
% 1.39/0.57  fof(f31,plain,(
% 1.39/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.39/0.57    inference(cnf_transformation,[],[f1])).
% 1.39/0.57  fof(f1,axiom,(
% 1.39/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.39/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.39/0.57  fof(f29,plain,(
% 1.39/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.39/0.57    inference(cnf_transformation,[],[f6])).
% 1.39/0.57  fof(f6,axiom,(
% 1.39/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.39/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.39/0.57  fof(f45,plain,(
% 1.39/0.57    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))) )),
% 1.39/0.57    inference(cnf_transformation,[],[f9])).
% 1.39/0.57  fof(f9,axiom,(
% 1.39/0.57    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 1.39/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).
% 1.39/0.57  fof(f81,plain,(
% 1.39/0.57    spl3_2),
% 1.39/0.57    inference(avatar_split_clause,[],[f55,f78])).
% 1.39/0.57  fof(f55,plain,(
% 1.39/0.57    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 1.39/0.57    inference(definition_unfolding,[],[f21,f31,f52,f52])).
% 1.39/0.57  fof(f21,plain,(
% 1.39/0.57    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.39/0.57    inference(cnf_transformation,[],[f19])).
% 1.39/0.57  fof(f19,plain,(
% 1.39/0.57    ? [X0,X1] : (X0 != X1 & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.39/0.57    inference(ennf_transformation,[],[f18])).
% 1.39/0.57  fof(f18,negated_conjecture,(
% 1.39/0.57    ~! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.39/0.57    inference(negated_conjecture,[],[f17])).
% 1.39/0.57  fof(f17,conjecture,(
% 1.39/0.57    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.39/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).
% 1.39/0.57  fof(f76,plain,(
% 1.39/0.57    ~spl3_1),
% 1.39/0.57    inference(avatar_split_clause,[],[f22,f73])).
% 1.39/0.57  fof(f22,plain,(
% 1.39/0.57    sK0 != sK1),
% 1.39/0.57    inference(cnf_transformation,[],[f19])).
% 1.39/0.57  % SZS output end Proof for theBenchmark
% 1.39/0.57  % (20758)------------------------------
% 1.39/0.57  % (20758)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.57  % (20758)Termination reason: Refutation
% 1.39/0.57  
% 1.39/0.57  % (20758)Memory used [KB]: 10746
% 1.39/0.57  % (20758)Time elapsed: 0.093 s
% 1.39/0.57  % (20758)------------------------------
% 1.39/0.57  % (20758)------------------------------
% 1.39/0.57  % (20735)Success in time 0.197 s
%------------------------------------------------------------------------------
