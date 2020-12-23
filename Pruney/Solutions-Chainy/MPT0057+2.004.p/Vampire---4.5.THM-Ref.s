%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:09 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 108 expanded)
%              Number of leaves         :   20 (  52 expanded)
%              Depth                    :    6
%              Number of atoms          :  140 ( 218 expanded)
%              Number of equality atoms :   55 (  94 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1162,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f31,f35,f39,f43,f65,f69,f117,f296,f577,f1042,f1052,f1093])).

fof(f1093,plain,
    ( ~ spl3_5
    | spl3_10
    | ~ spl3_35 ),
    inference(avatar_contradiction_clause,[],[f1092])).

fof(f1092,plain,
    ( $false
    | ~ spl3_5
    | spl3_10
    | ~ spl3_35 ),
    inference(subsumption_resolution,[],[f116,f1091])).

fof(f1091,plain,
    ( ! [X6,X8,X7] : k3_xboole_0(X6,k4_xboole_0(X8,k3_xboole_0(X6,X7))) = k3_xboole_0(X6,k4_xboole_0(X8,X7))
    | ~ spl3_5
    | ~ spl3_35 ),
    inference(forward_demodulation,[],[f1055,f1051])).

fof(f1051,plain,
    ( ! [X4,X5,X3] : k3_xboole_0(k4_xboole_0(X3,X4),X5) = k3_xboole_0(X3,k4_xboole_0(X5,X4))
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f1050])).

fof(f1050,plain,
    ( spl3_35
  <=> ! [X3,X5,X4] : k3_xboole_0(k4_xboole_0(X3,X4),X5) = k3_xboole_0(X3,k4_xboole_0(X5,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f1055,plain,
    ( ! [X6,X8,X7] : k3_xboole_0(k4_xboole_0(X6,X7),X8) = k3_xboole_0(X6,k4_xboole_0(X8,k3_xboole_0(X6,X7)))
    | ~ spl3_5
    | ~ spl3_35 ),
    inference(superposition,[],[f1051,f42])).

fof(f42,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl3_5
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f116,plain,
    ( k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,k4_xboole_0(sK1,k3_xboole_0(sK0,sK2)))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl3_10
  <=> k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k3_xboole_0(sK0,k4_xboole_0(sK1,k3_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f1052,plain,
    ( spl3_35
    | ~ spl3_2
    | ~ spl3_20
    | ~ spl3_27
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f1044,f1040,f575,f294,f29,f1050])).

fof(f29,plain,
    ( spl3_2
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

% (21486)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% (21482)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% (21484)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
fof(f294,plain,
    ( spl3_20
  <=> ! [X3,X5,X4] : k2_xboole_0(X5,k4_xboole_0(X3,X4)) = k2_xboole_0(X5,k4_xboole_0(X3,k2_xboole_0(X4,X5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f575,plain,
    ( spl3_27
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f1040,plain,
    ( spl3_33
  <=> ! [X3,X5,X4] : k3_xboole_0(k4_xboole_0(X3,X4),X5) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,k2_xboole_0(X4,X5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f1044,plain,
    ( ! [X4,X5,X3] : k3_xboole_0(k4_xboole_0(X3,X4),X5) = k3_xboole_0(X3,k4_xboole_0(X5,X4))
    | ~ spl3_2
    | ~ spl3_20
    | ~ spl3_27
    | ~ spl3_33 ),
    inference(forward_demodulation,[],[f1043,f591])).

fof(f591,plain,
    ( ! [X4,X2,X3] : k3_xboole_0(X2,k4_xboole_0(X3,X4)) = k4_xboole_0(X2,k2_xboole_0(X4,k4_xboole_0(X2,X3)))
    | ~ spl3_2
    | ~ spl3_27 ),
    inference(superposition,[],[f576,f30])).

fof(f30,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f576,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f575])).

fof(f1043,plain,
    ( ! [X4,X5,X3] : k3_xboole_0(k4_xboole_0(X3,X4),X5) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,X5)))
    | ~ spl3_2
    | ~ spl3_20
    | ~ spl3_33 ),
    inference(forward_demodulation,[],[f1041,f318])).

fof(f318,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(X1,k4_xboole_0(X2,X0)) = k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X0)))
    | ~ spl3_2
    | ~ spl3_20 ),
    inference(superposition,[],[f295,f30])).

fof(f295,plain,
    ( ! [X4,X5,X3] : k2_xboole_0(X5,k4_xboole_0(X3,X4)) = k2_xboole_0(X5,k4_xboole_0(X3,k2_xboole_0(X4,X5)))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f294])).

fof(f1041,plain,
    ( ! [X4,X5,X3] : k3_xboole_0(k4_xboole_0(X3,X4),X5) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,k2_xboole_0(X4,X5))))
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f1040])).

fof(f1042,plain,
    ( spl3_33
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f99,f67,f37,f1040])).

fof(f37,plain,
    ( spl3_4
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f67,plain,
    ( spl3_8
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f99,plain,
    ( ! [X4,X5,X3] : k3_xboole_0(k4_xboole_0(X3,X4),X5) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,k2_xboole_0(X4,X5))))
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f86,f68])).

fof(f68,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f67])).

fof(f86,plain,
    ( ! [X4,X5,X3] : k3_xboole_0(k4_xboole_0(X3,X4),X5) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(k4_xboole_0(X3,X4),X5)))
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(superposition,[],[f68,f38])).

fof(f38,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f37])).

fof(f577,plain,
    ( spl3_27
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f92,f67,f63,f37,f575])).

fof(f63,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f92,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f81,f64])).

fof(f64,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f63])).

fof(f81,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(superposition,[],[f68,f38])).

fof(f296,plain,
    ( spl3_20
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f89,f67,f33,f294])).

fof(f33,plain,
    ( spl3_3
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f89,plain,
    ( ! [X4,X5,X3] : k2_xboole_0(X5,k4_xboole_0(X3,X4)) = k2_xboole_0(X5,k4_xboole_0(X3,k2_xboole_0(X4,X5)))
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(superposition,[],[f34,f68])).

% (21492)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
fof(f34,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f33])).

fof(f117,plain,
    ( ~ spl3_10
    | spl3_1
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f72,f63,f24,f114])).

fof(f24,plain,
    ( spl3_1
  <=> k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f72,plain,
    ( k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,k4_xboole_0(sK1,k3_xboole_0(sK0,sK2)))
    | spl3_1
    | ~ spl3_7 ),
    inference(superposition,[],[f26,f64])).

fof(f26,plain,
    ( k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f69,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f21,f67])).

fof(f21,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

% (21495)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
fof(f65,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f20,f63])).

fof(f20,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f43,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f18,f41])).

fof(f18,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

% (21494)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
fof(f39,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f17,f37])).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f35,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f16,f33])).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f31,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f15,f29])).

fof(f15,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f27,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f14,f24])).

fof(f14,plain,(
    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))
   => k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:12:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.41  % (21485)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.43  % (21493)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.45  % (21485)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f1162,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(avatar_sat_refutation,[],[f27,f31,f35,f39,f43,f65,f69,f117,f296,f577,f1042,f1052,f1093])).
% 0.20/0.45  fof(f1093,plain,(
% 0.20/0.45    ~spl3_5 | spl3_10 | ~spl3_35),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f1092])).
% 0.20/0.45  fof(f1092,plain,(
% 0.20/0.45    $false | (~spl3_5 | spl3_10 | ~spl3_35)),
% 0.20/0.45    inference(subsumption_resolution,[],[f116,f1091])).
% 0.20/0.45  fof(f1091,plain,(
% 0.20/0.45    ( ! [X6,X8,X7] : (k3_xboole_0(X6,k4_xboole_0(X8,k3_xboole_0(X6,X7))) = k3_xboole_0(X6,k4_xboole_0(X8,X7))) ) | (~spl3_5 | ~spl3_35)),
% 0.20/0.45    inference(forward_demodulation,[],[f1055,f1051])).
% 0.20/0.45  fof(f1051,plain,(
% 0.20/0.45    ( ! [X4,X5,X3] : (k3_xboole_0(k4_xboole_0(X3,X4),X5) = k3_xboole_0(X3,k4_xboole_0(X5,X4))) ) | ~spl3_35),
% 0.20/0.45    inference(avatar_component_clause,[],[f1050])).
% 0.20/0.45  fof(f1050,plain,(
% 0.20/0.45    spl3_35 <=> ! [X3,X5,X4] : k3_xboole_0(k4_xboole_0(X3,X4),X5) = k3_xboole_0(X3,k4_xboole_0(X5,X4))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.20/0.45  fof(f1055,plain,(
% 0.20/0.45    ( ! [X6,X8,X7] : (k3_xboole_0(k4_xboole_0(X6,X7),X8) = k3_xboole_0(X6,k4_xboole_0(X8,k3_xboole_0(X6,X7)))) ) | (~spl3_5 | ~spl3_35)),
% 0.20/0.45    inference(superposition,[],[f1051,f42])).
% 0.20/0.45  fof(f42,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl3_5),
% 0.20/0.45    inference(avatar_component_clause,[],[f41])).
% 0.20/0.45  fof(f41,plain,(
% 0.20/0.45    spl3_5 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.45  fof(f116,plain,(
% 0.20/0.45    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,k4_xboole_0(sK1,k3_xboole_0(sK0,sK2))) | spl3_10),
% 0.20/0.45    inference(avatar_component_clause,[],[f114])).
% 0.20/0.45  fof(f114,plain,(
% 0.20/0.45    spl3_10 <=> k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k3_xboole_0(sK0,k4_xboole_0(sK1,k3_xboole_0(sK0,sK2)))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.45  fof(f1052,plain,(
% 0.20/0.45    spl3_35 | ~spl3_2 | ~spl3_20 | ~spl3_27 | ~spl3_33),
% 0.20/0.45    inference(avatar_split_clause,[],[f1044,f1040,f575,f294,f29,f1050])).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    spl3_2 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.46  % (21486)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.46  % (21482)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.46  % (21484)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  fof(f294,plain,(
% 0.20/0.47    spl3_20 <=> ! [X3,X5,X4] : k2_xboole_0(X5,k4_xboole_0(X3,X4)) = k2_xboole_0(X5,k4_xboole_0(X3,k2_xboole_0(X4,X5)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.47  fof(f575,plain,(
% 0.20/0.47    spl3_27 <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.20/0.47  fof(f1040,plain,(
% 0.20/0.47    spl3_33 <=> ! [X3,X5,X4] : k3_xboole_0(k4_xboole_0(X3,X4),X5) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,k2_xboole_0(X4,X5))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.20/0.47  fof(f1044,plain,(
% 0.20/0.47    ( ! [X4,X5,X3] : (k3_xboole_0(k4_xboole_0(X3,X4),X5) = k3_xboole_0(X3,k4_xboole_0(X5,X4))) ) | (~spl3_2 | ~spl3_20 | ~spl3_27 | ~spl3_33)),
% 0.20/0.47    inference(forward_demodulation,[],[f1043,f591])).
% 0.20/0.47  fof(f591,plain,(
% 0.20/0.47    ( ! [X4,X2,X3] : (k3_xboole_0(X2,k4_xboole_0(X3,X4)) = k4_xboole_0(X2,k2_xboole_0(X4,k4_xboole_0(X2,X3)))) ) | (~spl3_2 | ~spl3_27)),
% 0.20/0.47    inference(superposition,[],[f576,f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl3_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f29])).
% 0.20/0.47  fof(f576,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) ) | ~spl3_27),
% 0.20/0.47    inference(avatar_component_clause,[],[f575])).
% 0.20/0.47  fof(f1043,plain,(
% 0.20/0.47    ( ! [X4,X5,X3] : (k3_xboole_0(k4_xboole_0(X3,X4),X5) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,X5)))) ) | (~spl3_2 | ~spl3_20 | ~spl3_33)),
% 0.20/0.47    inference(forward_demodulation,[],[f1041,f318])).
% 0.20/0.47  fof(f318,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k2_xboole_0(X1,k4_xboole_0(X2,X0)) = k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X0)))) ) | (~spl3_2 | ~spl3_20)),
% 0.20/0.47    inference(superposition,[],[f295,f30])).
% 0.20/0.47  fof(f295,plain,(
% 0.20/0.47    ( ! [X4,X5,X3] : (k2_xboole_0(X5,k4_xboole_0(X3,X4)) = k2_xboole_0(X5,k4_xboole_0(X3,k2_xboole_0(X4,X5)))) ) | ~spl3_20),
% 0.20/0.47    inference(avatar_component_clause,[],[f294])).
% 0.20/0.47  fof(f1041,plain,(
% 0.20/0.47    ( ! [X4,X5,X3] : (k3_xboole_0(k4_xboole_0(X3,X4),X5) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,k2_xboole_0(X4,X5))))) ) | ~spl3_33),
% 0.20/0.47    inference(avatar_component_clause,[],[f1040])).
% 0.20/0.47  fof(f1042,plain,(
% 0.20/0.47    spl3_33 | ~spl3_4 | ~spl3_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f99,f67,f37,f1040])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    spl3_4 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    spl3_8 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.47  fof(f99,plain,(
% 0.20/0.47    ( ! [X4,X5,X3] : (k3_xboole_0(k4_xboole_0(X3,X4),X5) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,k2_xboole_0(X4,X5))))) ) | (~spl3_4 | ~spl3_8)),
% 0.20/0.47    inference(forward_demodulation,[],[f86,f68])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl3_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f67])).
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    ( ! [X4,X5,X3] : (k3_xboole_0(k4_xboole_0(X3,X4),X5) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(k4_xboole_0(X3,X4),X5)))) ) | (~spl3_4 | ~spl3_8)),
% 0.20/0.47    inference(superposition,[],[f68,f38])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl3_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f37])).
% 0.20/0.47  fof(f577,plain,(
% 0.20/0.47    spl3_27 | ~spl3_4 | ~spl3_7 | ~spl3_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f92,f67,f63,f37,f575])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    spl3_7 <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.47  fof(f92,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) ) | (~spl3_4 | ~spl3_7 | ~spl3_8)),
% 0.20/0.47    inference(forward_demodulation,[],[f81,f64])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) ) | ~spl3_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f63])).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) ) | (~spl3_4 | ~spl3_8)),
% 0.20/0.47    inference(superposition,[],[f68,f38])).
% 0.20/0.47  fof(f296,plain,(
% 0.20/0.47    spl3_20 | ~spl3_3 | ~spl3_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f89,f67,f33,f294])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    spl3_3 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.47  fof(f89,plain,(
% 0.20/0.47    ( ! [X4,X5,X3] : (k2_xboole_0(X5,k4_xboole_0(X3,X4)) = k2_xboole_0(X5,k4_xboole_0(X3,k2_xboole_0(X4,X5)))) ) | (~spl3_3 | ~spl3_8)),
% 0.20/0.47    inference(superposition,[],[f34,f68])).
% 0.20/0.47  % (21492)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl3_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f33])).
% 0.20/0.47  fof(f117,plain,(
% 0.20/0.47    ~spl3_10 | spl3_1 | ~spl3_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f72,f63,f24,f114])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    spl3_1 <=> k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,k4_xboole_0(sK1,k3_xboole_0(sK0,sK2))) | (spl3_1 | ~spl3_7)),
% 0.20/0.47    inference(superposition,[],[f26,f64])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) | spl3_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f24])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    spl3_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f21,f67])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.20/0.47  % (21495)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    spl3_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f20,f63])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    spl3_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f18,f41])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.20/0.47  % (21494)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    spl3_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f17,f37])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    spl3_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f16,f33])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    spl3_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f15,f29])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ~spl3_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f14,f24])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) => k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.20/0.47    inference(ennf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.20/0.47    inference(negated_conjecture,[],[f9])).
% 0.20/0.47  fof(f9,conjecture,(
% 0.20/0.47    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (21485)------------------------------
% 0.20/0.47  % (21485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (21485)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (21485)Memory used [KB]: 7291
% 0.20/0.47  % (21485)Time elapsed: 0.057 s
% 0.20/0.47  % (21485)------------------------------
% 0.20/0.47  % (21485)------------------------------
% 0.20/0.47  % (21479)Success in time 0.112 s
%------------------------------------------------------------------------------
