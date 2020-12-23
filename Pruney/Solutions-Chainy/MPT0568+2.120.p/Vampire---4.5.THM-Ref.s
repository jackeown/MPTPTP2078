%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:26 EST 2020

% Result     : Theorem 0.79s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   62 (  85 expanded)
%              Number of leaves         :   15 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :  132 ( 196 expanded)
%              Number of equality atoms :   64 ( 108 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f340,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f40,f45,f51,f66,f76,f270])).

fof(f270,plain,
    ( ~ spl1_2
    | ~ spl1_4
    | ~ spl1_5
    | spl1_6 ),
    inference(avatar_contradiction_clause,[],[f269])).

fof(f269,plain,
    ( $false
    | ~ spl1_2
    | ~ spl1_4
    | ~ spl1_5
    | spl1_6 ),
    inference(subsumption_resolution,[],[f244,f30])).

fof(f30,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f244,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_2
    | ~ spl1_4
    | ~ spl1_5
    | spl1_6 ),
    inference(backward_demodulation,[],[f75,f243])).

fof(f243,plain,
    ( ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)
    | ~ spl1_2
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(forward_demodulation,[],[f242,f62])).

fof(f62,plain,
    ( k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl1_5
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f242,plain,
    ( ! [X0] : k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_2
    | ~ spl1_4 ),
    inference(forward_demodulation,[],[f241,f53])).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f21,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f21,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f241,plain,
    ( ! [X0] : k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))
    | ~ spl1_2
    | ~ spl1_4 ),
    inference(forward_demodulation,[],[f238,f39])).

fof(f39,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl1_2
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f238,plain,
    ( ! [X0] : k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k3_xboole_0(k2_relat_1(k1_xboole_0),X0))
    | ~ spl1_4 ),
    inference(unit_resulting_resolution,[],[f50,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(f50,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl1_4
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f75,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k10_relat_1(k1_xboole_0,sK0),k10_relat_1(k1_xboole_0,sK0))
    | spl1_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl1_6
  <=> k1_xboole_0 = k2_zfmisc_1(k10_relat_1(k1_xboole_0,sK0),k10_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

% (23845)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f76,plain,
    ( ~ spl1_6
    | spl1_1 ),
    inference(avatar_split_clause,[],[f67,f32,f73])).

fof(f32,plain,
    ( spl1_1
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f67,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k10_relat_1(k1_xboole_0,sK0),k10_relat_1(k1_xboole_0,sK0))
    | spl1_1 ),
    inference(unit_resulting_resolution,[],[f34,f34,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f34,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f66,plain,
    ( spl1_5
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f65,f48,f42,f37,f60])).

fof(f42,plain,
    ( spl1_3
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f65,plain,
    ( k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(forward_demodulation,[],[f64,f44])).

fof(f44,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f64,plain,
    ( k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_2
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f56,f50])).

fof(f56,plain,
    ( k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl1_2 ),
    inference(superposition,[],[f22,f39])).

fof(f22,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f51,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f46,f48])).

fof(f46,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f23,f29])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f23,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f45,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f19,f42])).

fof(f19,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f40,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f20,f37])).

fof(f20,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f35,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f18,f32])).

fof(f18,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f14])).

fof(f14,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:02:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.38  ipcrm: permission denied for id (1228472326)
% 0.13/0.41  ipcrm: permission denied for id (1228537891)
% 0.13/0.42  ipcrm: permission denied for id (1228603430)
% 0.13/0.42  ipcrm: permission denied for id (1228636200)
% 0.21/0.45  ipcrm: permission denied for id (1228701761)
% 0.21/0.46  ipcrm: permission denied for id (1228734536)
% 0.21/0.47  ipcrm: permission denied for id (1228767317)
% 0.21/0.48  ipcrm: permission denied for id (1228800093)
% 0.21/0.48  ipcrm: permission denied for id (1228832863)
% 0.21/0.49  ipcrm: permission denied for id (1228865635)
% 0.21/0.51  ipcrm: permission denied for id (1228931189)
% 0.21/0.52  ipcrm: permission denied for id (1228963964)
% 0.79/0.62  % (23835)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.79/0.62  % (23841)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.79/0.63  % (23842)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.79/0.63  % (23844)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.79/0.63  % (23837)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.79/0.63  % (23844)Refutation not found, incomplete strategy% (23844)------------------------------
% 0.79/0.63  % (23844)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.79/0.63  % (23844)Termination reason: Refutation not found, incomplete strategy
% 0.79/0.63  
% 0.79/0.63  % (23844)Memory used [KB]: 6012
% 0.79/0.63  % (23844)Time elapsed: 0.051 s
% 0.79/0.63  % (23844)------------------------------
% 0.79/0.63  % (23844)------------------------------
% 0.79/0.63  % (23847)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.79/0.64  % (23847)Refutation not found, incomplete strategy% (23847)------------------------------
% 0.79/0.64  % (23847)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.79/0.64  % (23854)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.79/0.64  % (23854)Refutation not found, incomplete strategy% (23854)------------------------------
% 0.79/0.64  % (23854)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.79/0.64  % (23854)Termination reason: Refutation not found, incomplete strategy
% 0.79/0.64  
% 0.79/0.64  % (23854)Memory used [KB]: 10490
% 0.79/0.64  % (23854)Time elapsed: 0.074 s
% 0.79/0.64  % (23854)------------------------------
% 0.79/0.64  % (23854)------------------------------
% 0.79/0.64  % (23850)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.79/0.64  % (23835)Refutation not found, incomplete strategy% (23835)------------------------------
% 0.79/0.64  % (23835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.79/0.64  % (23835)Termination reason: Refutation not found, incomplete strategy
% 0.79/0.64  
% 0.79/0.64  % (23835)Memory used [KB]: 10490
% 0.79/0.64  % (23835)Time elapsed: 0.071 s
% 0.79/0.64  % (23835)------------------------------
% 0.79/0.64  % (23835)------------------------------
% 0.79/0.64  % (23839)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.79/0.64  % (23850)Refutation found. Thanks to Tanya!
% 0.79/0.64  % SZS status Theorem for theBenchmark
% 0.79/0.64  % SZS output start Proof for theBenchmark
% 0.79/0.64  fof(f340,plain,(
% 0.79/0.64    $false),
% 0.79/0.64    inference(avatar_sat_refutation,[],[f35,f40,f45,f51,f66,f76,f270])).
% 0.79/0.64  fof(f270,plain,(
% 0.79/0.64    ~spl1_2 | ~spl1_4 | ~spl1_5 | spl1_6),
% 0.79/0.64    inference(avatar_contradiction_clause,[],[f269])).
% 0.79/0.64  fof(f269,plain,(
% 0.79/0.64    $false | (~spl1_2 | ~spl1_4 | ~spl1_5 | spl1_6)),
% 0.79/0.64    inference(subsumption_resolution,[],[f244,f30])).
% 0.79/0.64  fof(f30,plain,(
% 0.79/0.64    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.79/0.64    inference(equality_resolution,[],[f27])).
% 0.79/0.64  fof(f27,plain,(
% 0.79/0.64    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.79/0.64    inference(cnf_transformation,[],[f17])).
% 0.79/0.64  fof(f17,plain,(
% 0.79/0.64    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.79/0.64    inference(flattening,[],[f16])).
% 0.79/0.64  fof(f16,plain,(
% 0.79/0.64    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.79/0.64    inference(nnf_transformation,[],[f3])).
% 0.79/0.64  fof(f3,axiom,(
% 0.79/0.64    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.79/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.79/0.64  fof(f244,plain,(
% 0.79/0.64    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) | (~spl1_2 | ~spl1_4 | ~spl1_5 | spl1_6)),
% 0.79/0.64    inference(backward_demodulation,[],[f75,f243])).
% 0.79/0.64  fof(f243,plain,(
% 0.79/0.64    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) ) | (~spl1_2 | ~spl1_4 | ~spl1_5)),
% 0.79/0.64    inference(forward_demodulation,[],[f242,f62])).
% 0.79/0.64  fof(f62,plain,(
% 0.79/0.64    k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0) | ~spl1_5),
% 0.79/0.64    inference(avatar_component_clause,[],[f60])).
% 0.79/0.64  fof(f60,plain,(
% 0.79/0.64    spl1_5 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.79/0.64    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.79/0.64  fof(f242,plain,(
% 0.79/0.64    ( ! [X0] : (k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k1_xboole_0)) ) | (~spl1_2 | ~spl1_4)),
% 0.79/0.64    inference(forward_demodulation,[],[f241,f53])).
% 0.79/0.64  fof(f53,plain,(
% 0.79/0.64    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.79/0.64    inference(unit_resulting_resolution,[],[f21,f25])).
% 0.79/0.64  fof(f25,plain,(
% 0.79/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.79/0.64    inference(cnf_transformation,[],[f13])).
% 0.79/0.64  fof(f13,plain,(
% 0.79/0.64    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.79/0.64    inference(ennf_transformation,[],[f1])).
% 0.79/0.64  fof(f1,axiom,(
% 0.79/0.64    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.79/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.79/0.64  fof(f21,plain,(
% 0.79/0.64    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.79/0.64    inference(cnf_transformation,[],[f2])).
% 0.79/0.64  fof(f2,axiom,(
% 0.79/0.64    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.79/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.79/0.64  fof(f241,plain,(
% 0.79/0.64    ( ! [X0] : (k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) ) | (~spl1_2 | ~spl1_4)),
% 0.79/0.64    inference(forward_demodulation,[],[f238,f39])).
% 0.79/0.64  fof(f39,plain,(
% 0.79/0.64    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl1_2),
% 0.79/0.64    inference(avatar_component_clause,[],[f37])).
% 0.79/0.64  fof(f37,plain,(
% 0.79/0.64    spl1_2 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.79/0.64    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.79/0.64  fof(f238,plain,(
% 0.79/0.64    ( ! [X0] : (k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k3_xboole_0(k2_relat_1(k1_xboole_0),X0))) ) | ~spl1_4),
% 0.79/0.64    inference(unit_resulting_resolution,[],[f50,f24])).
% 0.79/0.64  fof(f24,plain,(
% 0.79/0.64    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.79/0.64    inference(cnf_transformation,[],[f12])).
% 0.79/0.64  fof(f12,plain,(
% 0.79/0.64    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.79/0.64    inference(ennf_transformation,[],[f5])).
% 0.79/0.64  fof(f5,axiom,(
% 0.79/0.64    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 0.79/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).
% 0.79/0.64  fof(f50,plain,(
% 0.79/0.64    v1_relat_1(k1_xboole_0) | ~spl1_4),
% 0.79/0.64    inference(avatar_component_clause,[],[f48])).
% 0.79/0.64  fof(f48,plain,(
% 0.79/0.64    spl1_4 <=> v1_relat_1(k1_xboole_0)),
% 0.79/0.64    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.79/0.64  fof(f75,plain,(
% 0.79/0.64    k1_xboole_0 != k2_zfmisc_1(k10_relat_1(k1_xboole_0,sK0),k10_relat_1(k1_xboole_0,sK0)) | spl1_6),
% 0.79/0.64    inference(avatar_component_clause,[],[f73])).
% 0.79/0.64  fof(f73,plain,(
% 0.79/0.64    spl1_6 <=> k1_xboole_0 = k2_zfmisc_1(k10_relat_1(k1_xboole_0,sK0),k10_relat_1(k1_xboole_0,sK0))),
% 0.79/0.64    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.79/0.64  % (23845)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.79/0.64  fof(f76,plain,(
% 0.79/0.64    ~spl1_6 | spl1_1),
% 0.79/0.64    inference(avatar_split_clause,[],[f67,f32,f73])).
% 0.79/0.64  fof(f32,plain,(
% 0.79/0.64    spl1_1 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0)),
% 0.79/0.64    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.79/0.64  fof(f67,plain,(
% 0.79/0.64    k1_xboole_0 != k2_zfmisc_1(k10_relat_1(k1_xboole_0,sK0),k10_relat_1(k1_xboole_0,sK0)) | spl1_1),
% 0.79/0.64    inference(unit_resulting_resolution,[],[f34,f34,f26])).
% 0.79/0.64  fof(f26,plain,(
% 0.79/0.64    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.79/0.64    inference(cnf_transformation,[],[f17])).
% 0.79/0.64  fof(f34,plain,(
% 0.79/0.64    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) | spl1_1),
% 0.79/0.64    inference(avatar_component_clause,[],[f32])).
% 1.19/0.64  fof(f66,plain,(
% 1.19/0.64    spl1_5 | ~spl1_2 | ~spl1_3 | ~spl1_4),
% 1.19/0.64    inference(avatar_split_clause,[],[f65,f48,f42,f37,f60])).
% 1.19/0.64  fof(f42,plain,(
% 1.19/0.64    spl1_3 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.19/0.64    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 1.19/0.64  fof(f65,plain,(
% 1.19/0.64    k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0) | (~spl1_2 | ~spl1_3 | ~spl1_4)),
% 1.19/0.64    inference(forward_demodulation,[],[f64,f44])).
% 1.19/0.64  fof(f44,plain,(
% 1.19/0.64    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_3),
% 1.19/0.64    inference(avatar_component_clause,[],[f42])).
% 1.19/0.64  fof(f64,plain,(
% 1.19/0.64    k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,k1_xboole_0) | (~spl1_2 | ~spl1_4)),
% 1.19/0.64    inference(subsumption_resolution,[],[f56,f50])).
% 1.19/0.64  fof(f56,plain,(
% 1.19/0.64    k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~spl1_2),
% 1.19/0.64    inference(superposition,[],[f22,f39])).
% 1.19/0.64  fof(f22,plain,(
% 1.19/0.64    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.19/0.64    inference(cnf_transformation,[],[f11])).
% 1.19/0.64  fof(f11,plain,(
% 1.19/0.64    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.19/0.64    inference(ennf_transformation,[],[f6])).
% 1.19/0.64  fof(f6,axiom,(
% 1.19/0.64    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.19/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 1.19/0.64  fof(f51,plain,(
% 1.19/0.64    spl1_4),
% 1.19/0.64    inference(avatar_split_clause,[],[f46,f48])).
% 1.19/0.64  fof(f46,plain,(
% 1.19/0.64    v1_relat_1(k1_xboole_0)),
% 1.19/0.64    inference(superposition,[],[f23,f29])).
% 1.19/0.64  fof(f29,plain,(
% 1.19/0.64    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.19/0.64    inference(equality_resolution,[],[f28])).
% 1.19/0.64  fof(f28,plain,(
% 1.19/0.64    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.19/0.64    inference(cnf_transformation,[],[f17])).
% 1.19/0.64  fof(f23,plain,(
% 1.19/0.64    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.19/0.64    inference(cnf_transformation,[],[f4])).
% 1.19/0.64  fof(f4,axiom,(
% 1.19/0.64    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.19/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.19/0.64  fof(f45,plain,(
% 1.19/0.64    spl1_3),
% 1.19/0.64    inference(avatar_split_clause,[],[f19,f42])).
% 1.19/0.64  fof(f19,plain,(
% 1.19/0.64    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.19/0.64    inference(cnf_transformation,[],[f7])).
% 1.19/0.64  fof(f7,axiom,(
% 1.19/0.64    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.19/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.19/0.64  fof(f40,plain,(
% 1.19/0.64    spl1_2),
% 1.19/0.64    inference(avatar_split_clause,[],[f20,f37])).
% 1.19/0.64  fof(f20,plain,(
% 1.19/0.64    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.19/0.64    inference(cnf_transformation,[],[f7])).
% 1.19/0.64  fof(f35,plain,(
% 1.19/0.64    ~spl1_1),
% 1.19/0.64    inference(avatar_split_clause,[],[f18,f32])).
% 1.19/0.64  fof(f18,plain,(
% 1.19/0.64    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 1.19/0.64    inference(cnf_transformation,[],[f15])).
% 1.19/0.64  fof(f15,plain,(
% 1.19/0.64    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 1.19/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f14])).
% 1.19/0.64  fof(f14,plain,(
% 1.19/0.64    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 1.19/0.64    introduced(choice_axiom,[])).
% 1.19/0.64  fof(f10,plain,(
% 1.19/0.64    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 1.19/0.64    inference(ennf_transformation,[],[f9])).
% 1.19/0.64  fof(f9,negated_conjecture,(
% 1.19/0.64    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 1.19/0.64    inference(negated_conjecture,[],[f8])).
% 1.19/0.64  fof(f8,conjecture,(
% 1.19/0.64    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 1.19/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
% 1.19/0.64  % SZS output end Proof for theBenchmark
% 1.19/0.64  % (23850)------------------------------
% 1.19/0.64  % (23850)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.64  % (23850)Termination reason: Refutation
% 1.19/0.64  
% 1.19/0.64  % (23850)Memory used [KB]: 10746
% 1.19/0.64  % (23850)Time elapsed: 0.062 s
% 1.19/0.64  % (23850)------------------------------
% 1.19/0.64  % (23850)------------------------------
% 1.19/0.65  % (23700)Success in time 0.281 s
%------------------------------------------------------------------------------
