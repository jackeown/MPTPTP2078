%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   48 (  62 expanded)
%              Number of leaves         :   14 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :  103 ( 135 expanded)
%              Number of equality atoms :   30 (  38 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f78,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f29,f37,f41,f45,f54,f59,f72,f77])).

fof(f77,plain,
    ( spl1_1
    | ~ spl1_11 ),
    inference(avatar_contradiction_clause,[],[f73])).

fof(f73,plain,
    ( $false
    | spl1_1
    | ~ spl1_11 ),
    inference(unit_resulting_resolution,[],[f24,f71])).

fof(f71,plain,
    ( ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl1_11
  <=> ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f24,plain,
    ( k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f23])).

fof(f23,plain,
    ( spl1_1
  <=> k1_xboole_0 = k8_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f72,plain,
    ( spl1_11
    | ~ spl1_2
    | ~ spl1_4
    | ~ spl1_8
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f66,f57,f52,f35,f27,f70])).

fof(f27,plain,
    ( spl1_2
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f35,plain,
    ( spl1_4
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f52,plain,
    ( spl1_8
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f57,plain,
    ( spl1_9
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | k8_relat_1(X0,X1) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f66,plain,
    ( ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)
    | ~ spl1_2
    | ~ spl1_4
    | ~ spl1_8
    | ~ spl1_9 ),
    inference(subsumption_resolution,[],[f65,f53])).

fof(f53,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f52])).

fof(f65,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k1_xboole_0)
        | k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) )
    | ~ spl1_2
    | ~ spl1_4
    | ~ spl1_9 ),
    inference(subsumption_resolution,[],[f64,f28])).

fof(f28,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f64,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | ~ v1_relat_1(k1_xboole_0)
        | k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) )
    | ~ spl1_4
    | ~ spl1_9 ),
    inference(superposition,[],[f58,f36])).

fof(f36,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f35])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1)
        | k8_relat_1(X0,X1) = X1 )
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f57])).

fof(f59,plain,(
    spl1_9 ),
    inference(avatar_split_clause,[],[f16,f57])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k8_relat_1(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(f54,plain,
    ( spl1_8
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f50,f43,f39,f52])).

fof(f39,plain,
    ( spl1_5
  <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f43,plain,
    ( spl1_6
  <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f50,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(superposition,[],[f40,f44])).

fof(f44,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f43])).

fof(f40,plain,
    ( ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f39])).

fof(f45,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f20,f43])).

fof(f20,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f41,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f15,f39])).

fof(f15,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f37,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f13,f35])).

fof(f13,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

% (2986)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f5,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f29,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f14,f27])).

fof(f14,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f25,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f11,f23])).

fof(f11,plain,(
    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:48:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (2984)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.47  % (2984)Refutation not found, incomplete strategy% (2984)------------------------------
% 0.21/0.47  % (2984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (2984)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (2984)Memory used [KB]: 10490
% 0.21/0.47  % (2984)Time elapsed: 0.051 s
% 0.21/0.47  % (2984)------------------------------
% 0.21/0.47  % (2984)------------------------------
% 0.21/0.47  % (2993)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (2982)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (2982)Refutation not found, incomplete strategy% (2982)------------------------------
% 0.21/0.49  % (2982)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (2988)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (2982)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (2982)Memory used [KB]: 10490
% 0.21/0.49  % (2982)Time elapsed: 0.062 s
% 0.21/0.49  % (2982)------------------------------
% 0.21/0.49  % (2982)------------------------------
% 0.21/0.49  % (2987)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (2990)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (2994)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (2994)Refutation not found, incomplete strategy% (2994)------------------------------
% 0.21/0.49  % (2994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (2994)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (2994)Memory used [KB]: 1535
% 0.21/0.49  % (2994)Time elapsed: 0.075 s
% 0.21/0.49  % (2994)------------------------------
% 0.21/0.49  % (2994)------------------------------
% 0.21/0.49  % (2990)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f25,f29,f37,f41,f45,f54,f59,f72,f77])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    spl1_1 | ~spl1_11),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f73])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    $false | (spl1_1 | ~spl1_11)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f24,f71])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)) ) | ~spl1_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f70])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    spl1_11 <=> ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) | spl1_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    spl1_1 <=> k1_xboole_0 = k8_relat_1(sK0,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    spl1_11 | ~spl1_2 | ~spl1_4 | ~spl1_8 | ~spl1_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f66,f57,f52,f35,f27,f70])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    spl1_2 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    spl1_4 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    spl1_8 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    spl1_9 <=> ! [X1,X0] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)) ) | (~spl1_2 | ~spl1_4 | ~spl1_8 | ~spl1_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f65,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    v1_relat_1(k1_xboole_0) | ~spl1_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f52])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)) ) | (~spl1_2 | ~spl1_4 | ~spl1_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f64,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl1_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f27])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)) ) | (~spl1_4 | ~spl1_9)),
% 0.21/0.49    inference(superposition,[],[f58,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl1_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f35])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | k8_relat_1(X0,X1) = X1) ) | ~spl1_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f57])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    spl1_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f16,f57])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    spl1_8 | ~spl1_5 | ~spl1_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f50,f43,f39,f52])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    spl1_5 <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    spl1_6 <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    v1_relat_1(k1_xboole_0) | (~spl1_5 | ~spl1_6)),
% 0.21/0.50    inference(superposition,[],[f40,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl1_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f43])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) ) | ~spl1_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f39])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    spl1_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f20,f43])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    spl1_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f15,f39])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    spl1_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f13,f35])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  % (2986)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    spl1_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f14,f27])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ~spl1_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f11,f23])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,plain,(
% 0.21/0.50    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0)),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,negated_conjecture,(
% 0.21/0.50    ~! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 0.21/0.50    inference(negated_conjecture,[],[f6])).
% 0.21/0.50  fof(f6,conjecture,(
% 0.21/0.50    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (2990)------------------------------
% 0.21/0.50  % (2990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (2990)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (2990)Memory used [KB]: 10618
% 0.21/0.50  % (2990)Time elapsed: 0.074 s
% 0.21/0.50  % (2990)------------------------------
% 0.21/0.50  % (2990)------------------------------
% 0.21/0.50  % (2972)Success in time 0.134 s
%------------------------------------------------------------------------------
