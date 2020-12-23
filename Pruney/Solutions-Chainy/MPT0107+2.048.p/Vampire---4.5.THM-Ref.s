%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 113 expanded)
%              Number of leaves         :   27 (  54 expanded)
%              Depth                    :    7
%              Number of atoms          :  164 ( 222 expanded)
%              Number of equality atoms :   61 (  85 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f570,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f37,f41,f45,f49,f53,f61,f65,f69,f87,f96,f126,f141,f353,f537,f568])).

fof(f568,plain,
    ( spl2_1
    | ~ spl2_5
    | ~ spl2_9
    | ~ spl2_25
    | ~ spl2_31 ),
    inference(avatar_contradiction_clause,[],[f567])).

fof(f567,plain,
    ( $false
    | spl2_1
    | ~ spl2_5
    | ~ spl2_9
    | ~ spl2_25
    | ~ spl2_31 ),
    inference(subsumption_resolution,[],[f32,f566])).

fof(f566,plain,
    ( ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11))
    | ~ spl2_5
    | ~ spl2_9
    | ~ spl2_25
    | ~ spl2_31 ),
    inference(forward_demodulation,[],[f565,f68])).

fof(f68,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl2_9
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f565,plain,
    ( ! [X10,X11] : k4_xboole_0(X10,k3_xboole_0(X10,X11)) = k5_xboole_0(X10,k3_xboole_0(X10,X11))
    | ~ spl2_5
    | ~ spl2_25
    | ~ spl2_31 ),
    inference(forward_demodulation,[],[f543,f48])).

fof(f48,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl2_5
  <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f543,plain,
    ( ! [X10,X11] : k4_xboole_0(X10,k3_xboole_0(X10,X11)) = k5_xboole_0(k3_xboole_0(X10,X11),X10)
    | ~ spl2_25
    | ~ spl2_31 ),
    inference(superposition,[],[f536,f352])).

fof(f352,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f351])).

fof(f351,plain,
    ( spl2_25
  <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f536,plain,
    ( ! [X8,X7] : k4_xboole_0(X8,X7) = k5_xboole_0(X7,k2_xboole_0(X7,X8))
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f535])).

fof(f535,plain,
    ( spl2_31
  <=> ! [X7,X8] : k4_xboole_0(X8,X7) = k5_xboole_0(X7,k2_xboole_0(X7,X8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f32,plain,
    ( k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl2_1
  <=> k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f537,plain,
    ( spl2_31
    | ~ spl2_8
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f145,f139,f63,f535])).

fof(f63,plain,
    ( spl2_8
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f139,plain,
    ( spl2_16
  <=> ! [X1,X0] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f145,plain,
    ( ! [X8,X7] : k4_xboole_0(X8,X7) = k5_xboole_0(X7,k2_xboole_0(X7,X8))
    | ~ spl2_8
    | ~ spl2_16 ),
    inference(superposition,[],[f140,f64])).

fof(f64,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f63])).

fof(f140,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f139])).

fof(f353,plain,
    ( spl2_25
    | ~ spl2_6
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f127,f124,f51,f351])).

fof(f51,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f124,plain,
    ( spl2_13
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f127,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0
    | ~ spl2_6
    | ~ spl2_13 ),
    inference(unit_resulting_resolution,[],[f125,f52])).

fof(f52,plain,
    ( ! [X0,X1] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f51])).

fof(f125,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f124])).

fof(f141,plain,
    ( spl2_16
    | ~ spl2_2
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f113,f94,f85,f35,f139])).

fof(f35,plain,
    ( spl2_2
  <=> ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f85,plain,
    ( spl2_11
  <=> ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f94,plain,
    ( spl2_12
  <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f113,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1
    | ~ spl2_2
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f97,f86])).

fof(f86,plain,
    ( ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f85])).

fof(f97,plain,
    ( ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))
    | ~ spl2_2
    | ~ spl2_12 ),
    inference(superposition,[],[f95,f36])).

fof(f36,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f95,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f94])).

fof(f126,plain,
    ( spl2_13
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f76,f59,f43,f124])).

fof(f43,plain,
    ( spl2_4
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f59,plain,
    ( spl2_7
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f76,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(superposition,[],[f44,f60])).

fof(f60,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f59])).

fof(f44,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f96,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f27,f94])).

fof(f27,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f87,plain,
    ( spl2_11
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f54,f47,f39,f85])).

fof(f39,plain,
    ( spl2_3
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f54,plain,
    ( ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(superposition,[],[f48,f40])).

fof(f40,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f69,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f24,f67])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f65,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f23,f63])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f61,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f22,f59])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f53,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f28,f51])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f26,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f49,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f21,f47])).

fof(f21,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f45,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f20,f43])).

fof(f20,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f41,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f19,f39])).

fof(f19,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f37,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f18,f35])).

fof(f18,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f33,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f17,f30])).

fof(f17,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f15])).

fof(f15,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))
   => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n021.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:33:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (26581)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.50  % (26579)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.50  % (26578)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (26584)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (26588)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.51  % (26580)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (26583)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.51  % (26581)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (26589)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.52  % (26591)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.52  % (26586)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.52  % (26592)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.52  % (26576)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.52  % (26590)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 1.22/0.52  % (26582)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 1.22/0.53  % (26593)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.22/0.53  % SZS output start Proof for theBenchmark
% 1.22/0.53  fof(f570,plain,(
% 1.22/0.53    $false),
% 1.22/0.53    inference(avatar_sat_refutation,[],[f33,f37,f41,f45,f49,f53,f61,f65,f69,f87,f96,f126,f141,f353,f537,f568])).
% 1.22/0.53  fof(f568,plain,(
% 1.22/0.53    spl2_1 | ~spl2_5 | ~spl2_9 | ~spl2_25 | ~spl2_31),
% 1.22/0.53    inference(avatar_contradiction_clause,[],[f567])).
% 1.22/0.53  fof(f567,plain,(
% 1.22/0.53    $false | (spl2_1 | ~spl2_5 | ~spl2_9 | ~spl2_25 | ~spl2_31)),
% 1.22/0.53    inference(subsumption_resolution,[],[f32,f566])).
% 1.22/0.53  fof(f566,plain,(
% 1.22/0.53    ( ! [X10,X11] : (k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11))) ) | (~spl2_5 | ~spl2_9 | ~spl2_25 | ~spl2_31)),
% 1.22/0.53    inference(forward_demodulation,[],[f565,f68])).
% 1.22/0.53  fof(f68,plain,(
% 1.22/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl2_9),
% 1.22/0.53    inference(avatar_component_clause,[],[f67])).
% 1.22/0.53  fof(f67,plain,(
% 1.22/0.53    spl2_9 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 1.22/0.53  fof(f565,plain,(
% 1.22/0.53    ( ! [X10,X11] : (k4_xboole_0(X10,k3_xboole_0(X10,X11)) = k5_xboole_0(X10,k3_xboole_0(X10,X11))) ) | (~spl2_5 | ~spl2_25 | ~spl2_31)),
% 1.22/0.53    inference(forward_demodulation,[],[f543,f48])).
% 1.22/0.53  fof(f48,plain,(
% 1.22/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) ) | ~spl2_5),
% 1.22/0.53    inference(avatar_component_clause,[],[f47])).
% 1.22/0.53  fof(f47,plain,(
% 1.22/0.53    spl2_5 <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.22/0.53  fof(f543,plain,(
% 1.22/0.53    ( ! [X10,X11] : (k4_xboole_0(X10,k3_xboole_0(X10,X11)) = k5_xboole_0(k3_xboole_0(X10,X11),X10)) ) | (~spl2_25 | ~spl2_31)),
% 1.22/0.53    inference(superposition,[],[f536,f352])).
% 1.22/0.53  fof(f352,plain,(
% 1.22/0.53    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0) ) | ~spl2_25),
% 1.22/0.53    inference(avatar_component_clause,[],[f351])).
% 1.22/0.53  fof(f351,plain,(
% 1.22/0.53    spl2_25 <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0),
% 1.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 1.22/0.53  fof(f536,plain,(
% 1.22/0.53    ( ! [X8,X7] : (k4_xboole_0(X8,X7) = k5_xboole_0(X7,k2_xboole_0(X7,X8))) ) | ~spl2_31),
% 1.22/0.53    inference(avatar_component_clause,[],[f535])).
% 1.22/0.53  fof(f535,plain,(
% 1.22/0.53    spl2_31 <=> ! [X7,X8] : k4_xboole_0(X8,X7) = k5_xboole_0(X7,k2_xboole_0(X7,X8))),
% 1.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 1.22/0.53  fof(f32,plain,(
% 1.22/0.53    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | spl2_1),
% 1.22/0.53    inference(avatar_component_clause,[],[f30])).
% 1.22/0.53  fof(f30,plain,(
% 1.22/0.53    spl2_1 <=> k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.22/0.53  fof(f537,plain,(
% 1.22/0.53    spl2_31 | ~spl2_8 | ~spl2_16),
% 1.22/0.53    inference(avatar_split_clause,[],[f145,f139,f63,f535])).
% 1.22/0.53  fof(f63,plain,(
% 1.22/0.53    spl2_8 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 1.22/0.53  fof(f139,plain,(
% 1.22/0.53    spl2_16 <=> ! [X1,X0] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1),
% 1.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 1.22/0.53  fof(f145,plain,(
% 1.22/0.53    ( ! [X8,X7] : (k4_xboole_0(X8,X7) = k5_xboole_0(X7,k2_xboole_0(X7,X8))) ) | (~spl2_8 | ~spl2_16)),
% 1.22/0.53    inference(superposition,[],[f140,f64])).
% 1.22/0.53  fof(f64,plain,(
% 1.22/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl2_8),
% 1.22/0.53    inference(avatar_component_clause,[],[f63])).
% 1.22/0.53  fof(f140,plain,(
% 1.22/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) ) | ~spl2_16),
% 1.22/0.53    inference(avatar_component_clause,[],[f139])).
% 1.22/0.53  fof(f353,plain,(
% 1.22/0.53    spl2_25 | ~spl2_6 | ~spl2_13),
% 1.22/0.53    inference(avatar_split_clause,[],[f127,f124,f51,f351])).
% 1.22/0.53  fof(f51,plain,(
% 1.22/0.53    spl2_6 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.22/0.53  fof(f124,plain,(
% 1.22/0.53    spl2_13 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 1.22/0.53  fof(f127,plain,(
% 1.22/0.53    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0) ) | (~spl2_6 | ~spl2_13)),
% 1.22/0.53    inference(unit_resulting_resolution,[],[f125,f52])).
% 1.22/0.53  fof(f52,plain,(
% 1.22/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) ) | ~spl2_6),
% 1.22/0.53    inference(avatar_component_clause,[],[f51])).
% 1.22/0.53  fof(f125,plain,(
% 1.22/0.53    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl2_13),
% 1.22/0.53    inference(avatar_component_clause,[],[f124])).
% 1.22/0.53  fof(f141,plain,(
% 1.22/0.53    spl2_16 | ~spl2_2 | ~spl2_11 | ~spl2_12),
% 1.22/0.53    inference(avatar_split_clause,[],[f113,f94,f85,f35,f139])).
% 1.22/0.53  fof(f35,plain,(
% 1.22/0.53    spl2_2 <=> ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.22/0.53  fof(f85,plain,(
% 1.22/0.53    spl2_11 <=> ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1),
% 1.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 1.22/0.53  fof(f94,plain,(
% 1.22/0.53    spl2_12 <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 1.22/0.53  fof(f113,plain,(
% 1.22/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) ) | (~spl2_2 | ~spl2_11 | ~spl2_12)),
% 1.22/0.53    inference(forward_demodulation,[],[f97,f86])).
% 1.22/0.53  fof(f86,plain,(
% 1.22/0.53    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) ) | ~spl2_11),
% 1.22/0.53    inference(avatar_component_clause,[],[f85])).
% 1.22/0.53  fof(f97,plain,(
% 1.22/0.53    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) ) | (~spl2_2 | ~spl2_12)),
% 1.22/0.53    inference(superposition,[],[f95,f36])).
% 1.22/0.53  fof(f36,plain,(
% 1.22/0.53    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) ) | ~spl2_2),
% 1.22/0.53    inference(avatar_component_clause,[],[f35])).
% 1.22/0.53  fof(f95,plain,(
% 1.22/0.53    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) ) | ~spl2_12),
% 1.22/0.53    inference(avatar_component_clause,[],[f94])).
% 1.22/0.53  fof(f126,plain,(
% 1.22/0.53    spl2_13 | ~spl2_4 | ~spl2_7),
% 1.22/0.53    inference(avatar_split_clause,[],[f76,f59,f43,f124])).
% 1.22/0.53  fof(f43,plain,(
% 1.22/0.53    spl2_4 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.22/0.53  fof(f59,plain,(
% 1.22/0.53    spl2_7 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 1.22/0.53  fof(f76,plain,(
% 1.22/0.53    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | (~spl2_4 | ~spl2_7)),
% 1.22/0.53    inference(superposition,[],[f44,f60])).
% 1.22/0.53  fof(f60,plain,(
% 1.22/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl2_7),
% 1.22/0.53    inference(avatar_component_clause,[],[f59])).
% 1.22/0.53  fof(f44,plain,(
% 1.22/0.53    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl2_4),
% 1.22/0.53    inference(avatar_component_clause,[],[f43])).
% 1.22/0.53  fof(f96,plain,(
% 1.22/0.53    spl2_12),
% 1.22/0.53    inference(avatar_split_clause,[],[f27,f94])).
% 1.22/0.53  fof(f27,plain,(
% 1.22/0.53    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.22/0.53    inference(cnf_transformation,[],[f8])).
% 1.22/0.53  fof(f8,axiom,(
% 1.22/0.53    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.22/0.53  fof(f87,plain,(
% 1.22/0.53    spl2_11 | ~spl2_3 | ~spl2_5),
% 1.22/0.53    inference(avatar_split_clause,[],[f54,f47,f39,f85])).
% 1.22/0.53  fof(f39,plain,(
% 1.22/0.53    spl2_3 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.22/0.53  fof(f54,plain,(
% 1.22/0.53    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) ) | (~spl2_3 | ~spl2_5)),
% 1.22/0.53    inference(superposition,[],[f48,f40])).
% 1.22/0.53  fof(f40,plain,(
% 1.22/0.53    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_3),
% 1.22/0.53    inference(avatar_component_clause,[],[f39])).
% 1.22/0.53  fof(f69,plain,(
% 1.22/0.53    spl2_9),
% 1.22/0.53    inference(avatar_split_clause,[],[f24,f67])).
% 1.22/0.53  fof(f24,plain,(
% 1.22/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.22/0.53    inference(cnf_transformation,[],[f5])).
% 1.22/0.53  fof(f5,axiom,(
% 1.22/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.22/0.53  fof(f65,plain,(
% 1.22/0.53    spl2_8),
% 1.22/0.53    inference(avatar_split_clause,[],[f23,f63])).
% 1.22/0.53  fof(f23,plain,(
% 1.22/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.22/0.53    inference(cnf_transformation,[],[f10])).
% 1.22/0.53  fof(f10,axiom,(
% 1.22/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.22/0.53  fof(f61,plain,(
% 1.22/0.53    spl2_7),
% 1.22/0.53    inference(avatar_split_clause,[],[f22,f59])).
% 1.22/0.53  fof(f22,plain,(
% 1.22/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.22/0.53    inference(cnf_transformation,[],[f6])).
% 1.22/0.53  fof(f6,axiom,(
% 1.22/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.22/0.53  fof(f53,plain,(
% 1.22/0.53    spl2_6),
% 1.22/0.53    inference(avatar_split_clause,[],[f28,f51])).
% 1.22/0.53  fof(f28,plain,(
% 1.22/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.22/0.53    inference(forward_demodulation,[],[f26,f25])).
% 1.22/0.53  fof(f25,plain,(
% 1.22/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.22/0.53    inference(cnf_transformation,[],[f3])).
% 1.22/0.53  fof(f3,axiom,(
% 1.22/0.53    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.22/0.53  fof(f26,plain,(
% 1.22/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 1.22/0.53    inference(cnf_transformation,[],[f14])).
% 1.22/0.53  fof(f14,plain,(
% 1.22/0.53    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 1.22/0.53    inference(ennf_transformation,[],[f4])).
% 1.22/0.53  fof(f4,axiom,(
% 1.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 1.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).
% 1.22/0.53  fof(f49,plain,(
% 1.22/0.53    spl2_5),
% 1.22/0.53    inference(avatar_split_clause,[],[f21,f47])).
% 1.22/0.53  fof(f21,plain,(
% 1.22/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.22/0.53    inference(cnf_transformation,[],[f1])).
% 1.22/0.53  fof(f1,axiom,(
% 1.22/0.53    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.22/0.53  fof(f45,plain,(
% 1.22/0.53    spl2_4),
% 1.22/0.53    inference(avatar_split_clause,[],[f20,f43])).
% 1.22/0.53  fof(f20,plain,(
% 1.22/0.53    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.22/0.53    inference(cnf_transformation,[],[f2])).
% 1.22/0.53  fof(f2,axiom,(
% 1.22/0.53    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.22/0.53  fof(f41,plain,(
% 1.22/0.53    spl2_3),
% 1.22/0.53    inference(avatar_split_clause,[],[f19,f39])).
% 1.22/0.53  fof(f19,plain,(
% 1.22/0.53    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.22/0.53    inference(cnf_transformation,[],[f7])).
% 1.22/0.53  fof(f7,axiom,(
% 1.22/0.53    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.22/0.53  fof(f37,plain,(
% 1.22/0.53    spl2_2),
% 1.22/0.53    inference(avatar_split_clause,[],[f18,f35])).
% 1.22/0.53  fof(f18,plain,(
% 1.22/0.53    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.22/0.53    inference(cnf_transformation,[],[f9])).
% 1.22/0.53  fof(f9,axiom,(
% 1.22/0.53    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.22/0.53  fof(f33,plain,(
% 1.22/0.53    ~spl2_1),
% 1.22/0.53    inference(avatar_split_clause,[],[f17,f30])).
% 1.22/0.53  fof(f17,plain,(
% 1.22/0.53    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.22/0.53    inference(cnf_transformation,[],[f16])).
% 1.22/0.53  fof(f16,plain,(
% 1.22/0.53    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f15])).
% 1.22/0.53  fof(f15,plain,(
% 1.22/0.53    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.22/0.53    introduced(choice_axiom,[])).
% 1.22/0.53  fof(f13,plain,(
% 1.22/0.53    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.22/0.53    inference(ennf_transformation,[],[f12])).
% 1.22/0.53  fof(f12,negated_conjecture,(
% 1.22/0.53    ~! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.22/0.53    inference(negated_conjecture,[],[f11])).
% 1.22/0.53  fof(f11,conjecture,(
% 1.22/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.22/0.53  % SZS output end Proof for theBenchmark
% 1.22/0.53  % (26581)------------------------------
% 1.22/0.53  % (26581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.53  % (26581)Termination reason: Refutation
% 1.22/0.53  
% 1.22/0.53  % (26581)Memory used [KB]: 6780
% 1.22/0.53  % (26581)Time elapsed: 0.078 s
% 1.22/0.53  % (26581)------------------------------
% 1.22/0.53  % (26581)------------------------------
% 1.22/0.53  % (26587)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 1.22/0.53  % (26577)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 1.22/0.53  % (26587)Refutation not found, incomplete strategy% (26587)------------------------------
% 1.22/0.53  % (26587)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.53  % (26587)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.53  
% 1.22/0.53  % (26587)Memory used [KB]: 10490
% 1.22/0.53  % (26587)Time elapsed: 0.084 s
% 1.22/0.53  % (26587)------------------------------
% 1.22/0.53  % (26587)------------------------------
% 1.22/0.53  % (26575)Success in time 0.162 s
%------------------------------------------------------------------------------
