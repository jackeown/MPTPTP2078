%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:07 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   56 (  79 expanded)
%              Number of leaves         :   15 (  34 expanded)
%              Depth                    :    6
%              Number of atoms          :  142 ( 201 expanded)
%              Number of equality atoms :   38 (  56 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f87,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f26,f31,f35,f43,f47,f51,f56,f63,f83,f86])).

fof(f86,plain,
    ( ~ spl1_2
    | ~ spl1_6
    | spl1_12 ),
    inference(avatar_contradiction_clause,[],[f85])).

fof(f85,plain,
    ( $false
    | ~ spl1_2
    | ~ spl1_6
    | spl1_12 ),
    inference(subsumption_resolution,[],[f84,f30])).

fof(f30,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl1_2
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f84,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl1_6
    | spl1_12 ),
    inference(resolution,[],[f82,f46])).

fof(f46,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k8_relat_1(X0,X1))
        | ~ v1_relat_1(X1) )
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl1_6
  <=> ! [X1,X0] :
        ( v1_relat_1(k8_relat_1(X0,X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f82,plain,
    ( ~ v1_relat_1(k8_relat_1(k1_xboole_0,sK0))
    | spl1_12 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl1_12
  <=> v1_relat_1(k8_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f83,plain,
    ( ~ spl1_12
    | spl1_1
    | ~ spl1_3
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f78,f60,f33,f23,f80])).

fof(f23,plain,
    ( spl1_1
  <=> k1_xboole_0 = k8_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f33,plain,
    ( spl1_3
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 != k2_relat_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f60,plain,
    ( spl1_9
  <=> k1_xboole_0 = k2_relat_1(k8_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f78,plain,
    ( ~ v1_relat_1(k8_relat_1(k1_xboole_0,sK0))
    | spl1_1
    | ~ spl1_3
    | ~ spl1_9 ),
    inference(subsumption_resolution,[],[f77,f25])).

fof(f25,plain,
    ( k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f23])).

fof(f77,plain,
    ( k1_xboole_0 = k8_relat_1(k1_xboole_0,sK0)
    | ~ v1_relat_1(k8_relat_1(k1_xboole_0,sK0))
    | ~ spl1_3
    | ~ spl1_9 ),
    inference(trivial_inequality_removal,[],[f76])).

fof(f76,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k8_relat_1(k1_xboole_0,sK0)
    | ~ v1_relat_1(k8_relat_1(k1_xboole_0,sK0))
    | ~ spl1_3
    | ~ spl1_9 ),
    inference(superposition,[],[f34,f62])).

fof(f62,plain,
    ( k1_xboole_0 = k2_relat_1(k8_relat_1(k1_xboole_0,sK0))
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f60])).

fof(f34,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k2_relat_1(X0)
        | k1_xboole_0 = X0
        | ~ v1_relat_1(X0) )
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f33])).

fof(f63,plain,
    ( spl1_9
    | ~ spl1_2
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f57,f54,f28,f60])).

fof(f54,plain,
    ( spl1_8
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k2_relat_1(k8_relat_1(k1_xboole_0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f57,plain,
    ( k1_xboole_0 = k2_relat_1(k8_relat_1(k1_xboole_0,sK0))
    | ~ spl1_2
    | ~ spl1_8 ),
    inference(resolution,[],[f55,f30])).

fof(f55,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k2_relat_1(k8_relat_1(k1_xboole_0,X0)) )
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f54])).

fof(f56,plain,
    ( spl1_8
    | ~ spl1_5
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f52,f49,f41,f54])).

fof(f41,plain,
    ( spl1_5
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f49,plain,
    ( spl1_7
  <=> ! [X1,X0] :
        ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f52,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k2_relat_1(k8_relat_1(k1_xboole_0,X0)) )
    | ~ spl1_5
    | ~ spl1_7 ),
    inference(resolution,[],[f50,f42])).

fof(f42,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f41])).

fof(f50,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f49])).

fof(f51,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f21,f49])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).

fof(f47,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f20,f45])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f43,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f19,f41])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f35,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f18,f33])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f31,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f15,f28])).

fof(f15,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k8_relat_1(k1_xboole_0,X0)
        & v1_relat_1(X0) )
   => ( k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( k1_xboole_0 != k8_relat_1(k1_xboole_0,X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).

fof(f26,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f16,f23])).

fof(f16,plain,(
    k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:33:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.39  % (4559)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.12/0.39  % (4559)Refutation found. Thanks to Tanya!
% 0.12/0.39  % SZS status Theorem for theBenchmark
% 0.12/0.39  % SZS output start Proof for theBenchmark
% 0.12/0.39  fof(f87,plain,(
% 0.12/0.39    $false),
% 0.12/0.39    inference(avatar_sat_refutation,[],[f26,f31,f35,f43,f47,f51,f56,f63,f83,f86])).
% 0.12/0.39  fof(f86,plain,(
% 0.12/0.39    ~spl1_2 | ~spl1_6 | spl1_12),
% 0.12/0.39    inference(avatar_contradiction_clause,[],[f85])).
% 0.12/0.39  fof(f85,plain,(
% 0.12/0.39    $false | (~spl1_2 | ~spl1_6 | spl1_12)),
% 0.12/0.39    inference(subsumption_resolution,[],[f84,f30])).
% 0.12/0.39  fof(f30,plain,(
% 0.12/0.39    v1_relat_1(sK0) | ~spl1_2),
% 0.12/0.39    inference(avatar_component_clause,[],[f28])).
% 0.12/0.39  fof(f28,plain,(
% 0.12/0.39    spl1_2 <=> v1_relat_1(sK0)),
% 0.12/0.39    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.12/0.39  fof(f84,plain,(
% 0.12/0.39    ~v1_relat_1(sK0) | (~spl1_6 | spl1_12)),
% 0.12/0.39    inference(resolution,[],[f82,f46])).
% 0.12/0.39  fof(f46,plain,(
% 0.12/0.39    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) ) | ~spl1_6),
% 0.12/0.39    inference(avatar_component_clause,[],[f45])).
% 0.12/0.39  fof(f45,plain,(
% 0.12/0.39    spl1_6 <=> ! [X1,X0] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.12/0.39    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.12/0.39  fof(f82,plain,(
% 0.12/0.39    ~v1_relat_1(k8_relat_1(k1_xboole_0,sK0)) | spl1_12),
% 0.12/0.39    inference(avatar_component_clause,[],[f80])).
% 0.12/0.39  fof(f80,plain,(
% 0.12/0.39    spl1_12 <=> v1_relat_1(k8_relat_1(k1_xboole_0,sK0))),
% 0.12/0.39    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.12/0.39  fof(f83,plain,(
% 0.12/0.39    ~spl1_12 | spl1_1 | ~spl1_3 | ~spl1_9),
% 0.12/0.39    inference(avatar_split_clause,[],[f78,f60,f33,f23,f80])).
% 0.12/0.39  fof(f23,plain,(
% 0.12/0.39    spl1_1 <=> k1_xboole_0 = k8_relat_1(k1_xboole_0,sK0)),
% 0.12/0.39    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.12/0.39  fof(f33,plain,(
% 0.12/0.39    spl1_3 <=> ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.12/0.39    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.12/0.39  fof(f60,plain,(
% 0.12/0.39    spl1_9 <=> k1_xboole_0 = k2_relat_1(k8_relat_1(k1_xboole_0,sK0))),
% 0.12/0.39    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.12/0.39  fof(f78,plain,(
% 0.12/0.39    ~v1_relat_1(k8_relat_1(k1_xboole_0,sK0)) | (spl1_1 | ~spl1_3 | ~spl1_9)),
% 0.12/0.39    inference(subsumption_resolution,[],[f77,f25])).
% 0.12/0.39  fof(f25,plain,(
% 0.12/0.39    k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0) | spl1_1),
% 0.12/0.39    inference(avatar_component_clause,[],[f23])).
% 0.12/0.39  fof(f77,plain,(
% 0.12/0.39    k1_xboole_0 = k8_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(k8_relat_1(k1_xboole_0,sK0)) | (~spl1_3 | ~spl1_9)),
% 0.12/0.39    inference(trivial_inequality_removal,[],[f76])).
% 0.12/0.39  fof(f76,plain,(
% 0.12/0.39    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k8_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(k8_relat_1(k1_xboole_0,sK0)) | (~spl1_3 | ~spl1_9)),
% 0.12/0.39    inference(superposition,[],[f34,f62])).
% 0.12/0.39  fof(f62,plain,(
% 0.12/0.39    k1_xboole_0 = k2_relat_1(k8_relat_1(k1_xboole_0,sK0)) | ~spl1_9),
% 0.12/0.39    inference(avatar_component_clause,[],[f60])).
% 0.12/0.39  fof(f34,plain,(
% 0.12/0.39    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) ) | ~spl1_3),
% 0.12/0.39    inference(avatar_component_clause,[],[f33])).
% 0.12/0.39  fof(f63,plain,(
% 0.12/0.39    spl1_9 | ~spl1_2 | ~spl1_8),
% 0.12/0.39    inference(avatar_split_clause,[],[f57,f54,f28,f60])).
% 0.12/0.39  fof(f54,plain,(
% 0.12/0.39    spl1_8 <=> ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(k8_relat_1(k1_xboole_0,X0)))),
% 0.12/0.39    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.12/0.39  fof(f57,plain,(
% 0.12/0.39    k1_xboole_0 = k2_relat_1(k8_relat_1(k1_xboole_0,sK0)) | (~spl1_2 | ~spl1_8)),
% 0.12/0.39    inference(resolution,[],[f55,f30])).
% 0.12/0.39  fof(f55,plain,(
% 0.12/0.39    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(k8_relat_1(k1_xboole_0,X0))) ) | ~spl1_8),
% 0.12/0.39    inference(avatar_component_clause,[],[f54])).
% 0.12/0.39  fof(f56,plain,(
% 0.12/0.39    spl1_8 | ~spl1_5 | ~spl1_7),
% 0.12/0.39    inference(avatar_split_clause,[],[f52,f49,f41,f54])).
% 0.12/0.39  fof(f41,plain,(
% 0.12/0.39    spl1_5 <=> ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.12/0.39    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.12/0.39  fof(f49,plain,(
% 0.12/0.39    spl1_7 <=> ! [X1,X0] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1))),
% 0.12/0.39    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.12/0.39  fof(f52,plain,(
% 0.12/0.39    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(k8_relat_1(k1_xboole_0,X0))) ) | (~spl1_5 | ~spl1_7)),
% 0.12/0.39    inference(resolution,[],[f50,f42])).
% 0.12/0.39  fof(f42,plain,(
% 0.12/0.39    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl1_5),
% 0.12/0.39    inference(avatar_component_clause,[],[f41])).
% 0.12/0.39  fof(f50,plain,(
% 0.12/0.39    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1)) ) | ~spl1_7),
% 0.12/0.39    inference(avatar_component_clause,[],[f49])).
% 0.12/0.39  fof(f51,plain,(
% 0.12/0.39    spl1_7),
% 0.12/0.39    inference(avatar_split_clause,[],[f21,f49])).
% 0.12/0.39  fof(f21,plain,(
% 0.12/0.39    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1)) )),
% 0.12/0.39    inference(cnf_transformation,[],[f12])).
% 0.12/0.39  fof(f12,plain,(
% 0.12/0.39    ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1))),
% 0.12/0.39    inference(ennf_transformation,[],[f3])).
% 0.12/0.39  fof(f3,axiom,(
% 0.12/0.39    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0))),
% 0.12/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).
% 0.12/0.39  fof(f47,plain,(
% 0.12/0.39    spl1_6),
% 0.12/0.39    inference(avatar_split_clause,[],[f20,f45])).
% 0.12/0.39  fof(f20,plain,(
% 0.12/0.39    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.12/0.39    inference(cnf_transformation,[],[f11])).
% 0.12/0.39  fof(f11,plain,(
% 0.12/0.39    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.12/0.39    inference(ennf_transformation,[],[f2])).
% 0.12/0.39  fof(f2,axiom,(
% 0.12/0.39    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.12/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.12/0.39  fof(f43,plain,(
% 0.12/0.39    spl1_5),
% 0.12/0.39    inference(avatar_split_clause,[],[f19,f41])).
% 0.12/0.39  fof(f19,plain,(
% 0.12/0.39    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.12/0.39    inference(cnf_transformation,[],[f10])).
% 0.12/0.39  fof(f10,plain,(
% 0.12/0.39    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.12/0.39    inference(ennf_transformation,[],[f1])).
% 0.12/0.39  fof(f1,axiom,(
% 0.12/0.39    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.12/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.12/0.39  fof(f35,plain,(
% 0.12/0.39    spl1_3),
% 0.12/0.39    inference(avatar_split_clause,[],[f18,f33])).
% 0.12/0.39  fof(f18,plain,(
% 0.12/0.39    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.12/0.39    inference(cnf_transformation,[],[f9])).
% 0.12/0.39  fof(f9,plain,(
% 0.12/0.39    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.12/0.39    inference(flattening,[],[f8])).
% 0.12/0.39  fof(f8,plain,(
% 0.12/0.39    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.12/0.39    inference(ennf_transformation,[],[f4])).
% 0.12/0.39  fof(f4,axiom,(
% 0.12/0.39    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.12/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.12/0.39  fof(f31,plain,(
% 0.12/0.39    spl1_2),
% 0.12/0.39    inference(avatar_split_clause,[],[f15,f28])).
% 0.12/0.39  fof(f15,plain,(
% 0.12/0.39    v1_relat_1(sK0)),
% 0.12/0.39    inference(cnf_transformation,[],[f14])).
% 0.12/0.39  fof(f14,plain,(
% 0.12/0.39    k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0) & v1_relat_1(sK0)),
% 0.12/0.39    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f13])).
% 0.12/0.39  fof(f13,plain,(
% 0.12/0.39    ? [X0] : (k1_xboole_0 != k8_relat_1(k1_xboole_0,X0) & v1_relat_1(X0)) => (k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0) & v1_relat_1(sK0))),
% 0.12/0.39    introduced(choice_axiom,[])).
% 0.12/0.39  fof(f7,plain,(
% 0.12/0.39    ? [X0] : (k1_xboole_0 != k8_relat_1(k1_xboole_0,X0) & v1_relat_1(X0))),
% 0.12/0.39    inference(ennf_transformation,[],[f6])).
% 0.12/0.39  fof(f6,negated_conjecture,(
% 0.12/0.39    ~! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0))),
% 0.12/0.39    inference(negated_conjecture,[],[f5])).
% 0.12/0.39  fof(f5,conjecture,(
% 0.12/0.39    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0))),
% 0.12/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).
% 0.12/0.39  fof(f26,plain,(
% 0.12/0.39    ~spl1_1),
% 0.12/0.39    inference(avatar_split_clause,[],[f16,f23])).
% 0.12/0.39  fof(f16,plain,(
% 0.12/0.39    k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0)),
% 0.12/0.39    inference(cnf_transformation,[],[f14])).
% 0.12/0.39  % SZS output end Proof for theBenchmark
% 0.12/0.39  % (4559)------------------------------
% 0.12/0.39  % (4559)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.39  % (4559)Termination reason: Refutation
% 0.12/0.39  
% 0.12/0.39  % (4559)Memory used [KB]: 10618
% 0.12/0.39  % (4559)Time elapsed: 0.004 s
% 0.12/0.39  % (4559)------------------------------
% 0.12/0.39  % (4559)------------------------------
% 0.12/0.39  % (4553)Success in time 0.038 s
%------------------------------------------------------------------------------
