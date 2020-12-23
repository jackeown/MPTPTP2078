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
% DateTime   : Thu Dec  3 12:49:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   58 (  76 expanded)
%              Number of leaves         :   15 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :  117 ( 153 expanded)
%              Number of equality atoms :   48 (  60 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f85,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f39,f44,f52,f60,f71,f84])).

fof(f84,plain,
    ( spl1_1
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_6 ),
    inference(avatar_contradiction_clause,[],[f83])).

fof(f83,plain,
    ( $false
    | spl1_1
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_6 ),
    inference(trivial_inequality_removal,[],[f82])).

fof(f82,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl1_1
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_6 ),
    inference(superposition,[],[f33,f76])).

fof(f76,plain,
    ( ! [X3] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X3)
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_6 ),
    inference(forward_demodulation,[],[f75,f70])).

fof(f70,plain,
    ( k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl1_6
  <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f75,plain,
    ( ! [X3] : k9_relat_1(k1_xboole_0,X3) = k9_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(forward_demodulation,[],[f74,f18])).

fof(f18,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f74,plain,
    ( ! [X3] : k9_relat_1(k1_xboole_0,X3) = k9_relat_1(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3)))
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(forward_demodulation,[],[f73,f43])).

fof(f43,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl1_3
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f73,plain,
    ( ! [X3] : k9_relat_1(k1_xboole_0,X3) = k9_relat_1(k1_xboole_0,k4_xboole_0(k1_relat_1(k1_xboole_0),k4_xboole_0(k1_relat_1(k1_xboole_0),X3)))
    | ~ spl1_4 ),
    inference(resolution,[],[f27,f49])).

fof(f49,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl1_4
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k9_relat_1(X1,k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f23,f21])).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_relat_1)).

fof(f33,plain,
    ( k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl1_1
  <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f71,plain,
    ( spl1_6
    | ~ spl1_2
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f66,f57,f47,f36,f68])).

fof(f36,plain,
    ( spl1_2
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f57,plain,
    ( spl1_5
  <=> k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f66,plain,
    ( k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_2
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(forward_demodulation,[],[f65,f38])).

fof(f38,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f65,plain,
    ( k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(superposition,[],[f62,f59])).

fof(f59,plain,
    ( k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f62,plain,
    ( ! [X3] : k9_relat_1(k1_xboole_0,X3) = k2_relat_1(k7_relat_1(k1_xboole_0,X3))
    | ~ spl1_4 ),
    inference(resolution,[],[f22,f49])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f60,plain,
    ( spl1_5
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f55,f47,f41,f57])).

% (1477)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f55,plain,
    ( k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(forward_demodulation,[],[f54,f43])).

fof(f54,plain,
    ( k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0))
    | ~ spl1_4 ),
    inference(resolution,[],[f19,f49])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(f52,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f51,f47])).

fof(f51,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f20,f29])).

fof(f29,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f20,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f44,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f16,f41])).

fof(f16,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f39,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f17,f36])).

fof(f17,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f34,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f15,f31])).

fof(f15,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:55:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.53  % (1468)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (1468)Refutation not found, incomplete strategy% (1468)------------------------------
% 0.22/0.54  % (1468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (1468)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (1468)Memory used [KB]: 1663
% 0.22/0.54  % (1468)Time elapsed: 0.111 s
% 0.22/0.54  % (1468)------------------------------
% 0.22/0.54  % (1468)------------------------------
% 0.22/0.56  % (1476)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.56  % (1484)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.56  % (1485)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.56  % (1474)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.56  % (1476)Refutation not found, incomplete strategy% (1476)------------------------------
% 0.22/0.56  % (1476)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (1476)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (1476)Memory used [KB]: 10618
% 0.22/0.56  % (1476)Time elapsed: 0.132 s
% 0.22/0.56  % (1476)------------------------------
% 0.22/0.56  % (1476)------------------------------
% 0.22/0.57  % (1484)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.57  % (1494)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  fof(f85,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(avatar_sat_refutation,[],[f34,f39,f44,f52,f60,f71,f84])).
% 0.22/0.57  fof(f84,plain,(
% 0.22/0.57    spl1_1 | ~spl1_3 | ~spl1_4 | ~spl1_6),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f83])).
% 0.22/0.57  fof(f83,plain,(
% 0.22/0.57    $false | (spl1_1 | ~spl1_3 | ~spl1_4 | ~spl1_6)),
% 0.22/0.57    inference(trivial_inequality_removal,[],[f82])).
% 0.22/0.57  fof(f82,plain,(
% 0.22/0.57    k1_xboole_0 != k1_xboole_0 | (spl1_1 | ~spl1_3 | ~spl1_4 | ~spl1_6)),
% 0.22/0.57    inference(superposition,[],[f33,f76])).
% 0.22/0.57  fof(f76,plain,(
% 0.22/0.57    ( ! [X3] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X3)) ) | (~spl1_3 | ~spl1_4 | ~spl1_6)),
% 0.22/0.57    inference(forward_demodulation,[],[f75,f70])).
% 0.22/0.57  fof(f70,plain,(
% 0.22/0.57    k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0) | ~spl1_6),
% 0.22/0.57    inference(avatar_component_clause,[],[f68])).
% 0.22/0.57  fof(f68,plain,(
% 0.22/0.57    spl1_6 <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.22/0.57  fof(f75,plain,(
% 0.22/0.57    ( ! [X3] : (k9_relat_1(k1_xboole_0,X3) = k9_relat_1(k1_xboole_0,k1_xboole_0)) ) | (~spl1_3 | ~spl1_4)),
% 0.22/0.57    inference(forward_demodulation,[],[f74,f18])).
% 0.22/0.57  fof(f18,plain,(
% 0.22/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f2])).
% 0.22/0.57  fof(f2,axiom,(
% 0.22/0.57    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.22/0.57  fof(f74,plain,(
% 0.22/0.57    ( ! [X3] : (k9_relat_1(k1_xboole_0,X3) = k9_relat_1(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3)))) ) | (~spl1_3 | ~spl1_4)),
% 0.22/0.57    inference(forward_demodulation,[],[f73,f43])).
% 0.22/0.57  fof(f43,plain,(
% 0.22/0.57    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_3),
% 0.22/0.57    inference(avatar_component_clause,[],[f41])).
% 0.22/0.57  fof(f41,plain,(
% 0.22/0.57    spl1_3 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.57  fof(f73,plain,(
% 0.22/0.57    ( ! [X3] : (k9_relat_1(k1_xboole_0,X3) = k9_relat_1(k1_xboole_0,k4_xboole_0(k1_relat_1(k1_xboole_0),k4_xboole_0(k1_relat_1(k1_xboole_0),X3)))) ) | ~spl1_4),
% 0.22/0.57    inference(resolution,[],[f27,f49])).
% 0.22/0.57  fof(f49,plain,(
% 0.22/0.57    v1_relat_1(k1_xboole_0) | ~spl1_4),
% 0.22/0.57    inference(avatar_component_clause,[],[f47])).
% 0.22/0.57  fof(f47,plain,(
% 0.22/0.57    spl1_4 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.22/0.57  fof(f27,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k9_relat_1(X1,X0) = k9_relat_1(X1,k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)))) )),
% 0.22/0.57    inference(definition_unfolding,[],[f23,f21])).
% 0.22/0.57  fof(f21,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f1])).
% 0.22/0.57  fof(f1,axiom,(
% 0.22/0.57    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.57  fof(f23,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f14])).
% 0.22/0.57  fof(f14,plain,(
% 0.22/0.57    ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.57    inference(ennf_transformation,[],[f5])).
% 0.22/0.57  fof(f5,axiom,(
% 0.22/0.57    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_relat_1)).
% 0.22/0.57  fof(f33,plain,(
% 0.22/0.57    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) | spl1_1),
% 0.22/0.57    inference(avatar_component_clause,[],[f31])).
% 0.22/0.57  fof(f31,plain,(
% 0.22/0.57    spl1_1 <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.57  fof(f71,plain,(
% 0.22/0.57    spl1_6 | ~spl1_2 | ~spl1_4 | ~spl1_5),
% 0.22/0.57    inference(avatar_split_clause,[],[f66,f57,f47,f36,f68])).
% 0.22/0.57  fof(f36,plain,(
% 0.22/0.57    spl1_2 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.57  fof(f57,plain,(
% 0.22/0.57    spl1_5 <=> k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.22/0.57  fof(f66,plain,(
% 0.22/0.57    k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0) | (~spl1_2 | ~spl1_4 | ~spl1_5)),
% 0.22/0.57    inference(forward_demodulation,[],[f65,f38])).
% 0.22/0.57  fof(f38,plain,(
% 0.22/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl1_2),
% 0.22/0.57    inference(avatar_component_clause,[],[f36])).
% 0.22/0.57  fof(f65,plain,(
% 0.22/0.57    k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_xboole_0) | (~spl1_4 | ~spl1_5)),
% 0.22/0.57    inference(superposition,[],[f62,f59])).
% 0.22/0.57  fof(f59,plain,(
% 0.22/0.57    k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0) | ~spl1_5),
% 0.22/0.57    inference(avatar_component_clause,[],[f57])).
% 0.22/0.57  fof(f62,plain,(
% 0.22/0.57    ( ! [X3] : (k9_relat_1(k1_xboole_0,X3) = k2_relat_1(k7_relat_1(k1_xboole_0,X3))) ) | ~spl1_4),
% 0.22/0.57    inference(resolution,[],[f22,f49])).
% 0.22/0.57  fof(f22,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f13])).
% 0.22/0.57  fof(f13,plain,(
% 0.22/0.57    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 0.22/0.57    inference(ennf_transformation,[],[f6])).
% 0.22/0.57  fof(f6,axiom,(
% 0.22/0.57    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.57  fof(f60,plain,(
% 0.22/0.57    spl1_5 | ~spl1_3 | ~spl1_4),
% 0.22/0.57    inference(avatar_split_clause,[],[f55,f47,f41,f57])).
% 0.22/0.57  % (1477)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.57  fof(f55,plain,(
% 0.22/0.57    k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0) | (~spl1_3 | ~spl1_4)),
% 0.22/0.57    inference(forward_demodulation,[],[f54,f43])).
% 0.22/0.57  fof(f54,plain,(
% 0.22/0.57    k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) | ~spl1_4),
% 0.22/0.57    inference(resolution,[],[f19,f49])).
% 0.22/0.57  fof(f19,plain,(
% 0.22/0.57    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 0.22/0.57    inference(cnf_transformation,[],[f12])).
% 0.22/0.57  fof(f12,plain,(
% 0.22/0.57    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f8])).
% 0.22/0.57  fof(f8,axiom,(
% 0.22/0.57    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 0.22/0.57  fof(f52,plain,(
% 0.22/0.57    spl1_4),
% 0.22/0.57    inference(avatar_split_clause,[],[f51,f47])).
% 0.22/0.57  fof(f51,plain,(
% 0.22/0.57    v1_relat_1(k1_xboole_0)),
% 0.22/0.57    inference(superposition,[],[f20,f29])).
% 0.22/0.57  fof(f29,plain,(
% 0.22/0.57    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.22/0.57    inference(equality_resolution,[],[f25])).
% 0.22/0.57  fof(f25,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f3])).
% 0.22/0.57  fof(f3,axiom,(
% 0.22/0.57    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.57  fof(f20,plain,(
% 0.22/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f4])).
% 0.22/0.57  fof(f4,axiom,(
% 0.22/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.57  fof(f44,plain,(
% 0.22/0.57    spl1_3),
% 0.22/0.57    inference(avatar_split_clause,[],[f16,f41])).
% 0.22/0.57  fof(f16,plain,(
% 0.22/0.57    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.57    inference(cnf_transformation,[],[f7])).
% 0.22/0.57  fof(f7,axiom,(
% 0.22/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.57  fof(f39,plain,(
% 0.22/0.57    spl1_2),
% 0.22/0.57    inference(avatar_split_clause,[],[f17,f36])).
% 0.22/0.57  fof(f17,plain,(
% 0.22/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.57    inference(cnf_transformation,[],[f7])).
% 0.22/0.57  fof(f34,plain,(
% 0.22/0.57    ~spl1_1),
% 0.22/0.57    inference(avatar_split_clause,[],[f15,f31])).
% 0.22/0.57  fof(f15,plain,(
% 0.22/0.57    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.22/0.57    inference(cnf_transformation,[],[f11])).
% 0.22/0.57  fof(f11,plain,(
% 0.22/0.57    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)),
% 0.22/0.57    inference(ennf_transformation,[],[f10])).
% 0.22/0.57  fof(f10,negated_conjecture,(
% 0.22/0.57    ~! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.22/0.57    inference(negated_conjecture,[],[f9])).
% 0.22/0.57  fof(f9,conjecture,(
% 0.22/0.57    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
% 0.22/0.57  % SZS output end Proof for theBenchmark
% 0.22/0.57  % (1484)------------------------------
% 0.22/0.57  % (1484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (1484)Termination reason: Refutation
% 0.22/0.57  
% 0.22/0.57  % (1484)Memory used [KB]: 10746
% 0.22/0.57  % (1484)Time elapsed: 0.132 s
% 0.22/0.57  % (1484)------------------------------
% 0.22/0.57  % (1484)------------------------------
% 0.22/0.57  % (1467)Success in time 0.208 s
%------------------------------------------------------------------------------
