%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   56 (  75 expanded)
%              Number of leaves         :   16 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :  116 ( 154 expanded)
%              Number of equality atoms :   35 (  49 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f88,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f39,f44,f50,f55,f66,f77,f86])).

fof(f86,plain,
    ( spl1_5
    | ~ spl1_7 ),
    inference(avatar_contradiction_clause,[],[f80])).

fof(f80,plain,
    ( $false
    | spl1_5
    | ~ spl1_7 ),
    inference(unit_resulting_resolution,[],[f54,f22,f76,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f76,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl1_7
  <=> ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f22,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f54,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)
    | spl1_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl1_5
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f77,plain,
    ( spl1_7
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f73,f63,f47,f41,f75])).

fof(f41,plain,
    ( spl1_3
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f47,plain,
    ( spl1_4
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f63,plain,
    ( spl1_6
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f73,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_6 ),
    inference(forward_demodulation,[],[f69,f65])).

fof(f65,plain,
    ( k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f63])).

fof(f69,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k10_relat_1(k1_xboole_0,k1_xboole_0))
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f68,f49])).

fof(f49,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f68,plain,
    ( ! [X0] :
        ( r1_tarski(k10_relat_1(k1_xboole_0,X0),k10_relat_1(k1_xboole_0,k1_xboole_0))
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_3 ),
    inference(superposition,[],[f24,f43])).

fof(f43,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t170_relat_1)).

fof(f66,plain,
    ( spl1_6
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f59,f47,f41,f36,f63])).

fof(f36,plain,
    ( spl1_2
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f59,plain,
    ( k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(forward_demodulation,[],[f58,f38])).

fof(f38,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f58,plain,
    ( k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(forward_demodulation,[],[f57,f43])).

fof(f57,plain,
    ( k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0))
    | ~ spl1_4 ),
    inference(resolution,[],[f23,f49])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f55,plain,(
    ~ spl1_5 ),
    inference(avatar_split_clause,[],[f17,f52])).

fof(f17,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f13])).

fof(f13,plain,
    ( ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

fof(f50,plain,
    ( spl1_4
    | ~ spl1_1 ),
    inference(avatar_split_clause,[],[f45,f31,f47])).

fof(f31,plain,
    ( spl1_1
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f45,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_1 ),
    inference(superposition,[],[f21,f33])).

fof(f33,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f21,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f44,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f20,f41])).

fof(f20,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f39,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f19,f36])).

fof(f19,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f34,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f18,f31])).

fof(f18,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:22:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (11652)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.49  % (11659)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.50  % (11659)Refutation not found, incomplete strategy% (11659)------------------------------
% 0.22/0.50  % (11659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (11659)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (11659)Memory used [KB]: 1535
% 0.22/0.50  % (11659)Time elapsed: 0.069 s
% 0.22/0.50  % (11659)------------------------------
% 0.22/0.50  % (11659)------------------------------
% 0.22/0.50  % (11652)Refutation not found, incomplete strategy% (11652)------------------------------
% 0.22/0.50  % (11652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (11652)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (11652)Memory used [KB]: 10490
% 0.22/0.50  % (11652)Time elapsed: 0.069 s
% 0.22/0.50  % (11652)------------------------------
% 0.22/0.50  % (11652)------------------------------
% 0.22/0.50  % (11673)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % (11653)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (11653)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f34,f39,f44,f50,f55,f66,f77,f86])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    spl1_5 | ~spl1_7),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f80])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    $false | (spl1_5 | ~spl1_7)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f54,f22,f76,f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.51    inference(flattening,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    ( ! [X0] : (r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)) ) | ~spl1_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f75])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    spl1_7 <=> ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) | spl1_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    spl1_5 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    spl1_7 | ~spl1_3 | ~spl1_4 | ~spl1_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f73,f63,f47,f41,f75])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    spl1_3 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    spl1_4 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    spl1_6 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    ( ! [X0] : (r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)) ) | (~spl1_3 | ~spl1_4 | ~spl1_6)),
% 0.22/0.51    inference(forward_demodulation,[],[f69,f65])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0) | ~spl1_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f63])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    ( ! [X0] : (r1_tarski(k10_relat_1(k1_xboole_0,X0),k10_relat_1(k1_xboole_0,k1_xboole_0))) ) | (~spl1_3 | ~spl1_4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f68,f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    v1_relat_1(k1_xboole_0) | ~spl1_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f47])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    ( ! [X0] : (r1_tarski(k10_relat_1(k1_xboole_0,X0),k10_relat_1(k1_xboole_0,k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) ) | ~spl1_3),
% 0.22/0.51    inference(superposition,[],[f24,f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl1_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f41])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t170_relat_1)).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    spl1_6 | ~spl1_2 | ~spl1_3 | ~spl1_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f59,f47,f41,f36,f63])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    spl1_2 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0) | (~spl1_2 | ~spl1_3 | ~spl1_4)),
% 0.22/0.51    inference(forward_demodulation,[],[f58,f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f36])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,k1_xboole_0) | (~spl1_3 | ~spl1_4)),
% 0.22/0.51    inference(forward_demodulation,[],[f57,f43])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0)) | ~spl1_4),
% 0.22/0.51    inference(resolution,[],[f23,f49])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ~spl1_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f17,f52])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,negated_conjecture,(
% 0.22/0.51    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.22/0.51    inference(negated_conjecture,[],[f8])).
% 0.22/0.51  fof(f8,conjecture,(
% 0.22/0.51    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    spl1_4 | ~spl1_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f45,f31,f47])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    spl1_1 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    v1_relat_1(k1_xboole_0) | ~spl1_1),
% 0.22/0.51    inference(superposition,[],[f21,f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl1_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f31])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    spl1_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f20,f41])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    spl1_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f19,f36])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    spl1_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f18,f31])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (11653)------------------------------
% 0.22/0.51  % (11653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (11653)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (11653)Memory used [KB]: 6140
% 0.22/0.51  % (11653)Time elapsed: 0.082 s
% 0.22/0.51  % (11653)------------------------------
% 0.22/0.51  % (11653)------------------------------
% 0.22/0.51  % (11654)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (11650)Success in time 0.147 s
%------------------------------------------------------------------------------
