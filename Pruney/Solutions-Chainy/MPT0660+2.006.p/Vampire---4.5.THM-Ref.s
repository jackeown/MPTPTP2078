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
% DateTime   : Thu Dec  3 12:53:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   66 (  94 expanded)
%              Number of leaves         :   17 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :  223 ( 295 expanded)
%              Number of equality atoms :   70 (  93 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f79,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f31,f39,f40,f44,f48,f52,f56,f62,f75,f78])).

fof(f78,plain,
    ( spl1_1
    | ~ spl1_10 ),
    inference(avatar_contradiction_clause,[],[f77])).

fof(f77,plain,
    ( $false
    | spl1_1
    | ~ spl1_10 ),
    inference(trivial_inequality_removal,[],[f76])).

fof(f76,plain,
    ( k6_relat_1(sK0) != k6_relat_1(sK0)
    | spl1_1
    | ~ spl1_10 ),
    inference(superposition,[],[f26,f74])).

fof(f74,plain,
    ( ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl1_10
  <=> ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f26,plain,
    ( k6_relat_1(sK0) != k2_funct_1(k6_relat_1(sK0))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl1_1
  <=> k6_relat_1(sK0) = k2_funct_1(k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f75,plain,
    ( spl1_10
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_8
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f71,f60,f54,f46,f42,f37,f33,f29,f73])).

fof(f29,plain,
    ( spl1_2
  <=> ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f33,plain,
    ( spl1_3
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f37,plain,
    ( spl1_4
  <=> ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f42,plain,
    ( spl1_5
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f46,plain,
    ( spl1_6
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f54,plain,
    ( spl1_8
  <=> ! [X1,X0] :
        ( k2_funct_1(X0) = X1
        | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
        | k2_relat_1(X1) != k1_relat_1(X0)
        | ~ v2_funct_1(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f60,plain,
    ( spl1_9
  <=> ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f71,plain,
    ( ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_8
    | ~ spl1_9 ),
    inference(subsumption_resolution,[],[f70,f47])).

fof(f47,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f46])).

fof(f70,plain,
    ( ! [X0] :
        ( k1_relat_1(k6_relat_1(X0)) != X0
        | k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) )
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5
    | ~ spl1_8
    | ~ spl1_9 ),
    inference(forward_demodulation,[],[f69,f43])).

% (21996)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
fof(f43,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f42])).

fof(f69,plain,
    ( ! [X0] :
        ( k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))
        | k1_relat_1(k6_relat_1(X0)) != k2_relat_1(k6_relat_1(X0)) )
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5
    | ~ spl1_8
    | ~ spl1_9 ),
    inference(trivial_inequality_removal,[],[f68])).

fof(f68,plain,
    ( ! [X0] :
        ( k6_relat_1(X0) != k6_relat_1(X0)
        | k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))
        | k1_relat_1(k6_relat_1(X0)) != k2_relat_1(k6_relat_1(X0)) )
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5
    | ~ spl1_8
    | ~ spl1_9 ),
    inference(forward_demodulation,[],[f67,f43])).

fof(f67,plain,
    ( ! [X0] :
        ( k6_relat_1(X0) != k6_relat_1(k2_relat_1(k6_relat_1(X0)))
        | k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))
        | k1_relat_1(k6_relat_1(X0)) != k2_relat_1(k6_relat_1(X0)) )
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_8
    | ~ spl1_9 ),
    inference(subsumption_resolution,[],[f66,f34])).

fof(f34,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f33])).

fof(f66,plain,
    ( ! [X0] :
        ( k6_relat_1(X0) != k6_relat_1(k2_relat_1(k6_relat_1(X0)))
        | k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))
        | k1_relat_1(k6_relat_1(X0)) != k2_relat_1(k6_relat_1(X0))
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl1_2
    | ~ spl1_4
    | ~ spl1_8
    | ~ spl1_9 ),
    inference(subsumption_resolution,[],[f65,f38])).

fof(f38,plain,
    ( ! [X0] : v1_funct_1(k6_relat_1(X0))
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f37])).

fof(f65,plain,
    ( ! [X0] :
        ( k6_relat_1(X0) != k6_relat_1(k2_relat_1(k6_relat_1(X0)))
        | k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))
        | k1_relat_1(k6_relat_1(X0)) != k2_relat_1(k6_relat_1(X0))
        | ~ v1_funct_1(k6_relat_1(X0))
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl1_2
    | ~ spl1_8
    | ~ spl1_9 ),
    inference(subsumption_resolution,[],[f64,f30])).

fof(f30,plain,
    ( ! [X0] : v2_funct_1(k6_relat_1(X0))
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f64,plain,
    ( ! [X0] :
        ( k6_relat_1(X0) != k6_relat_1(k2_relat_1(k6_relat_1(X0)))
        | k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))
        | k1_relat_1(k6_relat_1(X0)) != k2_relat_1(k6_relat_1(X0))
        | ~ v2_funct_1(k6_relat_1(X0))
        | ~ v1_funct_1(k6_relat_1(X0))
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl1_8
    | ~ spl1_9 ),
    inference(duplicate_literal_removal,[],[f63])).

fof(f63,plain,
    ( ! [X0] :
        ( k6_relat_1(X0) != k6_relat_1(k2_relat_1(k6_relat_1(X0)))
        | k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))
        | k1_relat_1(k6_relat_1(X0)) != k2_relat_1(k6_relat_1(X0))
        | ~ v2_funct_1(k6_relat_1(X0))
        | ~ v1_funct_1(k6_relat_1(X0))
        | ~ v1_relat_1(k6_relat_1(X0))
        | ~ v1_funct_1(k6_relat_1(X0))
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl1_8
    | ~ spl1_9 ),
    inference(superposition,[],[f55,f61])).

fof(f61,plain,
    ( ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f60])).

fof(f55,plain,
    ( ! [X0,X1] :
        ( k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
        | k2_funct_1(X0) = X1
        | k2_relat_1(X1) != k1_relat_1(X0)
        | ~ v2_funct_1(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f54])).

fof(f62,plain,
    ( spl1_9
    | ~ spl1_3
    | ~ spl1_5
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f58,f50,f42,f33,f60])).

fof(f50,plain,
    ( spl1_7
  <=> ! [X0] :
        ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f58,plain,
    ( ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))
    | ~ spl1_3
    | ~ spl1_5
    | ~ spl1_7 ),
    inference(forward_demodulation,[],[f57,f43])).

fof(f57,plain,
    ( ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0))))
    | ~ spl1_3
    | ~ spl1_7 ),
    inference(resolution,[],[f51,f34])).

fof(f51,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 )
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f50])).

fof(f56,plain,(
    spl1_8 ),
    inference(avatar_split_clause,[],[f22,f54])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

fof(f52,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f21,f50])).

fof(f21,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f48,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f19,f46])).

fof(f19,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f44,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f20,f42])).

fof(f20,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f40,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f17,f33])).

fof(f17,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f39,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f18,f37])).

fof(f18,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f31,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f16,f29])).

fof(f16,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f27,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f14,f24])).

fof(f14,plain,(
    k6_relat_1(sK0) != k2_funct_1(k6_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    k6_relat_1(sK0) != k2_funct_1(k6_relat_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f12])).

fof(f12,plain,
    ( ? [X0] : k6_relat_1(X0) != k2_funct_1(k6_relat_1(X0))
   => k6_relat_1(sK0) != k2_funct_1(k6_relat_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] : k6_relat_1(X0) != k2_funct_1(k6_relat_1(X0)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:29:06 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.42  % (21994)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.43  % (21994)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f79,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f27,f31,f39,f40,f44,f48,f52,f56,f62,f75,f78])).
% 0.22/0.43  fof(f78,plain,(
% 0.22/0.43    spl1_1 | ~spl1_10),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f77])).
% 0.22/0.43  fof(f77,plain,(
% 0.22/0.43    $false | (spl1_1 | ~spl1_10)),
% 0.22/0.43    inference(trivial_inequality_removal,[],[f76])).
% 0.22/0.43  fof(f76,plain,(
% 0.22/0.43    k6_relat_1(sK0) != k6_relat_1(sK0) | (spl1_1 | ~spl1_10)),
% 0.22/0.43    inference(superposition,[],[f26,f74])).
% 0.22/0.43  fof(f74,plain,(
% 0.22/0.43    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) ) | ~spl1_10),
% 0.22/0.43    inference(avatar_component_clause,[],[f73])).
% 0.22/0.43  fof(f73,plain,(
% 0.22/0.43    spl1_10 <=> ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    k6_relat_1(sK0) != k2_funct_1(k6_relat_1(sK0)) | spl1_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f24])).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    spl1_1 <=> k6_relat_1(sK0) = k2_funct_1(k6_relat_1(sK0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.43  fof(f75,plain,(
% 0.22/0.43    spl1_10 | ~spl1_2 | ~spl1_3 | ~spl1_4 | ~spl1_5 | ~spl1_6 | ~spl1_8 | ~spl1_9),
% 0.22/0.43    inference(avatar_split_clause,[],[f71,f60,f54,f46,f42,f37,f33,f29,f73])).
% 0.22/0.43  fof(f29,plain,(
% 0.22/0.43    spl1_2 <=> ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.43  fof(f33,plain,(
% 0.22/0.43    spl1_3 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.43  fof(f37,plain,(
% 0.22/0.43    spl1_4 <=> ! [X0] : v1_funct_1(k6_relat_1(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.22/0.43  fof(f42,plain,(
% 0.22/0.43    spl1_5 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.22/0.43  fof(f46,plain,(
% 0.22/0.43    spl1_6 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.22/0.43  fof(f54,plain,(
% 0.22/0.43    spl1_8 <=> ! [X1,X0] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.22/0.43  fof(f60,plain,(
% 0.22/0.43    spl1_9 <=> ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.22/0.43  fof(f71,plain,(
% 0.22/0.43    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) ) | (~spl1_2 | ~spl1_3 | ~spl1_4 | ~spl1_5 | ~spl1_6 | ~spl1_8 | ~spl1_9)),
% 0.22/0.43    inference(subsumption_resolution,[],[f70,f47])).
% 0.22/0.43  fof(f47,plain,(
% 0.22/0.43    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl1_6),
% 0.22/0.43    inference(avatar_component_clause,[],[f46])).
% 0.22/0.43  fof(f70,plain,(
% 0.22/0.43    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) != X0 | k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) ) | (~spl1_2 | ~spl1_3 | ~spl1_4 | ~spl1_5 | ~spl1_8 | ~spl1_9)),
% 0.22/0.43    inference(forward_demodulation,[],[f69,f43])).
% 0.22/0.43  % (21996)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.43  fof(f43,plain,(
% 0.22/0.43    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl1_5),
% 0.22/0.43    inference(avatar_component_clause,[],[f42])).
% 0.22/0.43  fof(f69,plain,(
% 0.22/0.43    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) | k1_relat_1(k6_relat_1(X0)) != k2_relat_1(k6_relat_1(X0))) ) | (~spl1_2 | ~spl1_3 | ~spl1_4 | ~spl1_5 | ~spl1_8 | ~spl1_9)),
% 0.22/0.43    inference(trivial_inequality_removal,[],[f68])).
% 0.22/0.43  fof(f68,plain,(
% 0.22/0.43    ( ! [X0] : (k6_relat_1(X0) != k6_relat_1(X0) | k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) | k1_relat_1(k6_relat_1(X0)) != k2_relat_1(k6_relat_1(X0))) ) | (~spl1_2 | ~spl1_3 | ~spl1_4 | ~spl1_5 | ~spl1_8 | ~spl1_9)),
% 0.22/0.43    inference(forward_demodulation,[],[f67,f43])).
% 0.22/0.43  fof(f67,plain,(
% 0.22/0.43    ( ! [X0] : (k6_relat_1(X0) != k6_relat_1(k2_relat_1(k6_relat_1(X0))) | k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) | k1_relat_1(k6_relat_1(X0)) != k2_relat_1(k6_relat_1(X0))) ) | (~spl1_2 | ~spl1_3 | ~spl1_4 | ~spl1_8 | ~spl1_9)),
% 0.22/0.43    inference(subsumption_resolution,[],[f66,f34])).
% 0.22/0.43  fof(f34,plain,(
% 0.22/0.43    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl1_3),
% 0.22/0.43    inference(avatar_component_clause,[],[f33])).
% 0.22/0.43  fof(f66,plain,(
% 0.22/0.43    ( ! [X0] : (k6_relat_1(X0) != k6_relat_1(k2_relat_1(k6_relat_1(X0))) | k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) | k1_relat_1(k6_relat_1(X0)) != k2_relat_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) ) | (~spl1_2 | ~spl1_4 | ~spl1_8 | ~spl1_9)),
% 0.22/0.43    inference(subsumption_resolution,[],[f65,f38])).
% 0.22/0.43  fof(f38,plain,(
% 0.22/0.43    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) ) | ~spl1_4),
% 0.22/0.43    inference(avatar_component_clause,[],[f37])).
% 0.22/0.43  fof(f65,plain,(
% 0.22/0.43    ( ! [X0] : (k6_relat_1(X0) != k6_relat_1(k2_relat_1(k6_relat_1(X0))) | k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) | k1_relat_1(k6_relat_1(X0)) != k2_relat_1(k6_relat_1(X0)) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) ) | (~spl1_2 | ~spl1_8 | ~spl1_9)),
% 0.22/0.43    inference(subsumption_resolution,[],[f64,f30])).
% 0.22/0.43  fof(f30,plain,(
% 0.22/0.43    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) ) | ~spl1_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f29])).
% 0.22/0.43  fof(f64,plain,(
% 0.22/0.43    ( ! [X0] : (k6_relat_1(X0) != k6_relat_1(k2_relat_1(k6_relat_1(X0))) | k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) | k1_relat_1(k6_relat_1(X0)) != k2_relat_1(k6_relat_1(X0)) | ~v2_funct_1(k6_relat_1(X0)) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) ) | (~spl1_8 | ~spl1_9)),
% 0.22/0.43    inference(duplicate_literal_removal,[],[f63])).
% 0.22/0.43  fof(f63,plain,(
% 0.22/0.43    ( ! [X0] : (k6_relat_1(X0) != k6_relat_1(k2_relat_1(k6_relat_1(X0))) | k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) | k1_relat_1(k6_relat_1(X0)) != k2_relat_1(k6_relat_1(X0)) | ~v2_funct_1(k6_relat_1(X0)) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) ) | (~spl1_8 | ~spl1_9)),
% 0.22/0.43    inference(superposition,[],[f55,f61])).
% 0.22/0.43  fof(f61,plain,(
% 0.22/0.43    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))) ) | ~spl1_9),
% 0.22/0.43    inference(avatar_component_clause,[],[f60])).
% 0.22/0.43  fof(f55,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_funct_1(X0) = X1 | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl1_8),
% 0.22/0.43    inference(avatar_component_clause,[],[f54])).
% 0.22/0.43  fof(f62,plain,(
% 0.22/0.43    spl1_9 | ~spl1_3 | ~spl1_5 | ~spl1_7),
% 0.22/0.43    inference(avatar_split_clause,[],[f58,f50,f42,f33,f60])).
% 0.22/0.43  fof(f50,plain,(
% 0.22/0.43    spl1_7 <=> ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.22/0.43  fof(f58,plain,(
% 0.22/0.43    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))) ) | (~spl1_3 | ~spl1_5 | ~spl1_7)),
% 0.22/0.43    inference(forward_demodulation,[],[f57,f43])).
% 0.22/0.43  fof(f57,plain,(
% 0.22/0.43    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0))))) ) | (~spl1_3 | ~spl1_7)),
% 0.22/0.43    inference(resolution,[],[f51,f34])).
% 0.22/0.43  fof(f51,plain,(
% 0.22/0.43    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) ) | ~spl1_7),
% 0.22/0.43    inference(avatar_component_clause,[],[f50])).
% 0.22/0.43  fof(f56,plain,(
% 0.22/0.43    spl1_8),
% 0.22/0.43    inference(avatar_split_clause,[],[f22,f54])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f11])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.43    inference(flattening,[],[f10])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.43    inference(ennf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,axiom,(
% 0.22/0.43    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).
% 0.22/0.43  fof(f52,plain,(
% 0.22/0.43    spl1_7),
% 0.22/0.43    inference(avatar_split_clause,[],[f21,f50])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f9])).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 0.22/0.43  fof(f48,plain,(
% 0.22/0.43    spl1_6),
% 0.22/0.43    inference(avatar_split_clause,[],[f19,f46])).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.43  fof(f44,plain,(
% 0.22/0.43    spl1_5),
% 0.22/0.43    inference(avatar_split_clause,[],[f20,f42])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f1])).
% 0.22/0.43  fof(f40,plain,(
% 0.22/0.43    spl1_3),
% 0.22/0.43    inference(avatar_split_clause,[],[f17,f33])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.22/0.43  fof(f39,plain,(
% 0.22/0.43    spl1_4),
% 0.22/0.43    inference(avatar_split_clause,[],[f18,f37])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f3])).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    spl1_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f16,f29])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    ~spl1_1),
% 0.22/0.43    inference(avatar_split_clause,[],[f14,f24])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    k6_relat_1(sK0) != k2_funct_1(k6_relat_1(sK0))),
% 0.22/0.43    inference(cnf_transformation,[],[f13])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    k6_relat_1(sK0) != k2_funct_1(k6_relat_1(sK0))),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f12])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ? [X0] : k6_relat_1(X0) != k2_funct_1(k6_relat_1(X0)) => k6_relat_1(sK0) != k2_funct_1(k6_relat_1(sK0))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f8,plain,(
% 0.22/0.43    ? [X0] : k6_relat_1(X0) != k2_funct_1(k6_relat_1(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f7])).
% 0.22/0.43  fof(f7,negated_conjecture,(
% 0.22/0.43    ~! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 0.22/0.43    inference(negated_conjecture,[],[f6])).
% 0.22/0.43  fof(f6,conjecture,(
% 0.22/0.43    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (21994)------------------------------
% 0.22/0.43  % (21994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (21994)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (21994)Memory used [KB]: 10618
% 0.22/0.43  % (21994)Time elapsed: 0.007 s
% 0.22/0.43  % (21994)------------------------------
% 0.22/0.43  % (21994)------------------------------
% 0.22/0.43  % (21988)Success in time 0.065 s
%------------------------------------------------------------------------------
