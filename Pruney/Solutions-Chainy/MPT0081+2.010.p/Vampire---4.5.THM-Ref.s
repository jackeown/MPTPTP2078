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
% DateTime   : Thu Dec  3 12:31:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 455 expanded)
%              Number of leaves         :   12 ( 139 expanded)
%              Depth                    :   25
%              Number of atoms          :  109 ( 717 expanded)
%              Number of equality atoms :   60 ( 344 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f565,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f364,f366,f564])).

fof(f564,plain,(
    ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f563])).

fof(f563,plain,
    ( $false
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f36,f555])).

fof(f555,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,X0))
    | ~ spl3_7 ),
    inference(superposition,[],[f550,f22])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f550,plain,
    ( ! [X1] : k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK1,X1))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f549,f55])).

fof(f55,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f54,f33])).

fof(f33,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f25,f18])).

fof(f18,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( r1_xboole_0(sK0,sK1)
    & ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) )
   => ( r1_xboole_0(sK0,sK1)
      & ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
      & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f54,plain,(
    k3_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f51,f22])).

fof(f51,plain,(
    k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) ),
    inference(superposition,[],[f22,f46])).

fof(f46,plain,(
    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f23,f33])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

% (13773)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
fof(f549,plain,
    ( ! [X1] : k3_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,k4_xboole_0(sK1,X1))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f543,f22])).

fof(f543,plain,
    ( ! [X1] : k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) = k3_xboole_0(sK0,k4_xboole_0(sK1,X1))
    | ~ spl3_7 ),
    inference(superposition,[],[f22,f501])).

fof(f501,plain,
    ( ! [X20] : k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(sK1,X20))
    | ~ spl3_7 ),
    inference(backward_demodulation,[],[f416,f481])).

fof(f481,plain,
    ( ! [X3] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X3)
    | ~ spl3_7 ),
    inference(superposition,[],[f459,f41])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f38,f23])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f22,f22])).

fof(f459,plain,
    ( ! [X1] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)
    | ~ spl3_7 ),
    inference(superposition,[],[f440,f22])).

fof(f440,plain,
    ( ! [X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f436,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f436,plain,
    ( ! [X1] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))
    | ~ spl3_7 ),
    inference(superposition,[],[f28,f359])).

fof(f359,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f357])).

fof(f357,plain,
    ( spl3_7
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f28,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f416,plain,(
    ! [X20] : k4_xboole_0(sK0,k4_xboole_0(sK1,X20)) = k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,X20)) ),
    inference(forward_demodulation,[],[f380,f28])).

fof(f380,plain,(
    ! [X20] : k4_xboole_0(sK0,k4_xboole_0(sK1,X20)) = k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k3_xboole_0(sK0,X20)) ),
    inference(superposition,[],[f28,f46])).

fof(f36,plain,(
    k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f26,f17])).

fof(f17,plain,(
    ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f366,plain,(
    spl3_8 ),
    inference(avatar_contradiction_clause,[],[f365])).

fof(f365,plain,
    ( $false
    | spl3_8 ),
    inference(resolution,[],[f363,f19])).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f363,plain,
    ( ~ r1_tarski(k4_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f361])).

fof(f361,plain,
    ( spl3_8
  <=> r1_tarski(k4_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f364,plain,
    ( spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f354,f361,f357])).

fof(f354,plain,
    ( ~ r1_tarski(k4_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f24,f344])).

fof(f344,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f340,f233])).

fof(f233,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k3_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0)) ),
    inference(forward_demodulation,[],[f232,f55])).

fof(f232,plain,(
    ! [X0] : k3_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,k3_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0)) ),
    inference(forward_demodulation,[],[f223,f22])).

fof(f223,plain,(
    ! [X0] : k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k3_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0)) ),
    inference(superposition,[],[f197,f20])).

fof(f197,plain,(
    ! [X0] : k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f27,f194])).

fof(f194,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f190,f172])).

fof(f172,plain,(
    ! [X2] : k1_xboole_0 = k3_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,X2))) ),
    inference(superposition,[],[f168,f41])).

fof(f168,plain,(
    ! [X4] : k1_xboole_0 = k3_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X4))) ),
    inference(forward_demodulation,[],[f167,f55])).

fof(f167,plain,(
    ! [X4] : k3_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X4))) ),
    inference(forward_demodulation,[],[f163,f22])).

fof(f163,plain,(
    ! [X4] : k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) = k3_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X4))) ),
    inference(superposition,[],[f22,f128])).

fof(f128,plain,(
    ! [X0] : k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X0))) ),
    inference(forward_demodulation,[],[f119,f46])).

fof(f119,plain,(
    ! [X0] : k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X0))) ),
    inference(superposition,[],[f110,f20])).

fof(f110,plain,(
    ! [X9] : k4_xboole_0(sK0,k2_xboole_0(sK1,X9)) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X9)) ),
    inference(forward_demodulation,[],[f94,f27])).

fof(f94,plain,(
    ! [X9] : k4_xboole_0(sK0,k2_xboole_0(sK1,X9)) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X9) ),
    inference(superposition,[],[f27,f46])).

fof(f190,plain,(
    ! [X4] : k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) = k3_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,X4))) ),
    inference(superposition,[],[f22,f130])).

% (13775)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
fof(f130,plain,(
    ! [X1] : k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,X1))) ),
    inference(forward_demodulation,[],[f121,f46])).

fof(f121,plain,(
    ! [X1] : k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,X1))) ),
    inference(superposition,[],[f110,f71])).

fof(f71,plain,(
    ! [X4,X5] : k2_xboole_0(X4,k4_xboole_0(X4,X5)) = X4 ),
    inference(superposition,[],[f20,f41])).

fof(f27,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f340,plain,(
    ! [X4] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k3_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X4)) ),
    inference(superposition,[],[f23,f281])).

fof(f281,plain,(
    ! [X7] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,k3_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X7)) ),
    inference(superposition,[],[f22,f233])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:32:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.42  % (13776)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (13788)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.46  % (13785)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.47  % (13788)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f565,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f364,f366,f564])).
% 0.20/0.47  fof(f564,plain,(
% 0.20/0.47    ~spl3_7),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f563])).
% 0.20/0.47  fof(f563,plain,(
% 0.20/0.47    $false | ~spl3_7),
% 0.20/0.47    inference(subsumption_resolution,[],[f36,f555])).
% 0.20/0.47  fof(f555,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,X0))) ) | ~spl3_7),
% 0.20/0.47    inference(superposition,[],[f550,f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.47  fof(f550,plain,(
% 0.20/0.47    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK1,X1))) ) | ~spl3_7),
% 0.20/0.47    inference(forward_demodulation,[],[f549,f55])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    k1_xboole_0 = k3_xboole_0(sK0,k1_xboole_0)),
% 0.20/0.47    inference(forward_demodulation,[],[f54,f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.20/0.47    inference(resolution,[],[f25,f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    r1_xboole_0(sK0,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2))) => (r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 0.20/0.47    inference(ennf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 0.20/0.47    inference(negated_conjecture,[],[f10])).
% 0.20/0.47  fof(f10,conjecture,(
% 0.20/0.47    ! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.47    inference(nnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    k3_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k1_xboole_0)),
% 0.20/0.47    inference(forward_demodulation,[],[f51,f22])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0))),
% 0.20/0.47    inference(superposition,[],[f22,f46])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0)),
% 0.20/0.47    inference(superposition,[],[f23,f33])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.20/0.47  % (13773)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  fof(f549,plain,(
% 0.20/0.47    ( ! [X1] : (k3_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,k4_xboole_0(sK1,X1))) ) | ~spl3_7),
% 0.20/0.47    inference(forward_demodulation,[],[f543,f22])).
% 0.20/0.47  fof(f543,plain,(
% 0.20/0.47    ( ! [X1] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) = k3_xboole_0(sK0,k4_xboole_0(sK1,X1))) ) | ~spl3_7),
% 0.20/0.47    inference(superposition,[],[f22,f501])).
% 0.20/0.47  fof(f501,plain,(
% 0.20/0.47    ( ! [X20] : (k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(sK1,X20))) ) | ~spl3_7),
% 0.20/0.47    inference(backward_demodulation,[],[f416,f481])).
% 0.20/0.47  fof(f481,plain,(
% 0.20/0.47    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X3)) ) | ~spl3_7),
% 0.20/0.47    inference(superposition,[],[f459,f41])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(forward_demodulation,[],[f38,f23])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(superposition,[],[f22,f22])).
% 0.20/0.47  fof(f459,plain,(
% 0.20/0.47    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)) ) | ~spl3_7),
% 0.20/0.47    inference(superposition,[],[f440,f22])).
% 0.20/0.47  fof(f440,plain,(
% 0.20/0.47    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) ) | ~spl3_7),
% 0.20/0.47    inference(forward_demodulation,[],[f436,f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.20/0.47  fof(f436,plain,(
% 0.20/0.47    ( ! [X1] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))) ) | ~spl3_7),
% 0.20/0.47    inference(superposition,[],[f28,f359])).
% 0.20/0.47  fof(f359,plain,(
% 0.20/0.47    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl3_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f357])).
% 0.20/0.47  fof(f357,plain,(
% 0.20/0.47    spl3_7 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
% 0.20/0.47  fof(f416,plain,(
% 0.20/0.47    ( ! [X20] : (k4_xboole_0(sK0,k4_xboole_0(sK1,X20)) = k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,X20))) )),
% 0.20/0.47    inference(forward_demodulation,[],[f380,f28])).
% 0.20/0.47  fof(f380,plain,(
% 0.20/0.47    ( ! [X20] : (k4_xboole_0(sK0,k4_xboole_0(sK1,X20)) = k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k3_xboole_0(sK0,X20))) )),
% 0.20/0.47    inference(superposition,[],[f28,f46])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.47    inference(resolution,[],[f26,f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f366,plain,(
% 0.20/0.47    spl3_8),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f365])).
% 0.20/0.47  fof(f365,plain,(
% 0.20/0.47    $false | spl3_8),
% 0.20/0.47    inference(resolution,[],[f363,f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.47  fof(f363,plain,(
% 0.20/0.47    ~r1_tarski(k4_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) | spl3_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f361])).
% 0.20/0.47  fof(f361,plain,(
% 0.20/0.47    spl3_8 <=> r1_tarski(k4_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.47  fof(f364,plain,(
% 0.20/0.47    spl3_7 | ~spl3_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f354,f361,f357])).
% 0.20/0.47  fof(f354,plain,(
% 0.20/0.47    ~r1_tarski(k4_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) | k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.20/0.47    inference(superposition,[],[f24,f344])).
% 0.20/0.47  fof(f344,plain,(
% 0.20/0.47    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))),
% 0.20/0.47    inference(forward_demodulation,[],[f340,f233])).
% 0.20/0.47  fof(f233,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k3_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0))) )),
% 0.20/0.47    inference(forward_demodulation,[],[f232,f55])).
% 0.20/0.47  fof(f232,plain,(
% 0.20/0.47    ( ! [X0] : (k3_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,k3_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0))) )),
% 0.20/0.47    inference(forward_demodulation,[],[f223,f22])).
% 0.20/0.47  fof(f223,plain,(
% 0.20/0.47    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k3_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0))) )),
% 0.20/0.47    inference(superposition,[],[f197,f20])).
% 0.20/0.47  fof(f197,plain,(
% 0.20/0.47    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0)) = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.47    inference(superposition,[],[f27,f194])).
% 0.20/0.47  fof(f194,plain,(
% 0.20/0.47    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0))),
% 0.20/0.47    inference(forward_demodulation,[],[f190,f172])).
% 0.20/0.47  fof(f172,plain,(
% 0.20/0.47    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,X2)))) )),
% 0.20/0.47    inference(superposition,[],[f168,f41])).
% 0.20/0.47  fof(f168,plain,(
% 0.20/0.47    ( ! [X4] : (k1_xboole_0 = k3_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X4)))) )),
% 0.20/0.47    inference(forward_demodulation,[],[f167,f55])).
% 0.20/0.47  fof(f167,plain,(
% 0.20/0.47    ( ! [X4] : (k3_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X4)))) )),
% 0.20/0.47    inference(forward_demodulation,[],[f163,f22])).
% 0.20/0.47  fof(f163,plain,(
% 0.20/0.47    ( ! [X4] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) = k3_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X4)))) )),
% 0.20/0.47    inference(superposition,[],[f22,f128])).
% 0.20/0.47  fof(f128,plain,(
% 0.20/0.47    ( ! [X0] : (k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X0)))) )),
% 0.20/0.47    inference(forward_demodulation,[],[f119,f46])).
% 0.20/0.47  fof(f119,plain,(
% 0.20/0.47    ( ! [X0] : (k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X0)))) )),
% 0.20/0.47    inference(superposition,[],[f110,f20])).
% 0.20/0.47  fof(f110,plain,(
% 0.20/0.47    ( ! [X9] : (k4_xboole_0(sK0,k2_xboole_0(sK1,X9)) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X9))) )),
% 0.20/0.47    inference(forward_demodulation,[],[f94,f27])).
% 0.20/0.47  fof(f94,plain,(
% 0.20/0.47    ( ! [X9] : (k4_xboole_0(sK0,k2_xboole_0(sK1,X9)) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X9)) )),
% 0.20/0.47    inference(superposition,[],[f27,f46])).
% 0.20/0.47  fof(f190,plain,(
% 0.20/0.47    ( ! [X4] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) = k3_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,X4)))) )),
% 0.20/0.47    inference(superposition,[],[f22,f130])).
% 0.20/0.47  % (13775)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  fof(f130,plain,(
% 0.20/0.47    ( ! [X1] : (k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,X1)))) )),
% 0.20/0.47    inference(forward_demodulation,[],[f121,f46])).
% 0.20/0.47  fof(f121,plain,(
% 0.20/0.47    ( ! [X1] : (k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,X1)))) )),
% 0.20/0.47    inference(superposition,[],[f110,f71])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    ( ! [X4,X5] : (k2_xboole_0(X4,k4_xboole_0(X4,X5)) = X4) )),
% 0.20/0.47    inference(superposition,[],[f20,f41])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.20/0.47  fof(f340,plain,(
% 0.20/0.47    ( ! [X4] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k3_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X4))) )),
% 0.20/0.47    inference(superposition,[],[f23,f281])).
% 0.20/0.47  fof(f281,plain,(
% 0.20/0.47    ( ! [X7] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,k3_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X7))) )),
% 0.20/0.47    inference(superposition,[],[f22,f233])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (13788)------------------------------
% 0.20/0.47  % (13788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (13788)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (13788)Memory used [KB]: 6524
% 0.20/0.47  % (13788)Time elapsed: 0.012 s
% 0.20/0.47  % (13788)------------------------------
% 0.20/0.47  % (13788)------------------------------
% 0.20/0.47  % (13767)Success in time 0.109 s
%------------------------------------------------------------------------------
