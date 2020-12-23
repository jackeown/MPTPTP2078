%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:09 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 132 expanded)
%              Number of leaves         :   16 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :  235 ( 377 expanded)
%              Number of equality atoms :   33 (  61 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f161,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f37,f42,f47,f59,f66,f91,f98,f101,f111,f160])).

% (17893)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
fof(f160,plain,
    ( ~ spl1_4
    | spl1_11 ),
    inference(avatar_contradiction_clause,[],[f159])).

fof(f159,plain,
    ( $false
    | ~ spl1_4
    | spl1_11 ),
    inference(subsumption_resolution,[],[f158,f46])).

fof(f46,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl1_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f158,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_11 ),
    inference(trivial_inequality_removal,[],[f157])).

fof(f157,plain,
    ( sK0 != sK0
    | ~ v1_relat_1(sK0)
    | spl1_11 ),
    inference(superposition,[],[f110,f23])).

fof(f23,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f110,plain,
    ( sK0 != k4_relat_1(k4_relat_1(sK0))
    | spl1_11 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl1_11
  <=> sK0 = k4_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f111,plain,
    ( ~ spl1_11
    | spl1_6
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f104,f80,f63,f108])).

fof(f63,plain,
    ( spl1_6
  <=> sK0 = k2_funct_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f80,plain,
    ( spl1_8
  <=> k2_funct_1(k4_relat_1(sK0)) = k4_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f104,plain,
    ( sK0 != k4_relat_1(k4_relat_1(sK0))
    | spl1_6
    | ~ spl1_8 ),
    inference(superposition,[],[f65,f82])).

fof(f82,plain,
    ( k2_funct_1(k4_relat_1(sK0)) = k4_relat_1(k4_relat_1(sK0))
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f80])).

fof(f65,plain,
    ( sK0 != k2_funct_1(k4_relat_1(sK0))
    | spl1_6 ),
    inference(avatar_component_clause,[],[f63])).

fof(f101,plain,
    ( ~ spl1_4
    | spl1_10 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | ~ spl1_4
    | spl1_10 ),
    inference(subsumption_resolution,[],[f99,f46])).

fof(f99,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_10 ),
    inference(resolution,[],[f90,f22])).

fof(f22,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f90,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | spl1_10 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl1_10
  <=> v1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f98,plain,
    ( ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4
    | spl1_9 ),
    inference(avatar_contradiction_clause,[],[f97])).

fof(f97,plain,
    ( $false
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4
    | spl1_9 ),
    inference(subsumption_resolution,[],[f96,f46])).

fof(f96,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl1_2
    | ~ spl1_3
    | spl1_9 ),
    inference(subsumption_resolution,[],[f95,f36])).

fof(f36,plain,
    ( v2_funct_1(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl1_2
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f95,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_3
    | spl1_9 ),
    inference(subsumption_resolution,[],[f93,f41])).

fof(f41,plain,
    ( v1_funct_1(sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl1_3
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f93,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_9 ),
    inference(resolution,[],[f86,f25])).

fof(f25,plain,(
    ! [X0] :
      ( v1_funct_1(k4_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_funct_1)).

fof(f86,plain,
    ( ~ v1_funct_1(k4_relat_1(sK0))
    | spl1_9 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl1_9
  <=> v1_funct_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f91,plain,
    ( spl1_8
    | ~ spl1_9
    | ~ spl1_10
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f78,f56,f44,f39,f34,f88,f84,f80])).

fof(f56,plain,
    ( spl1_5
  <=> k2_funct_1(sK0) = k4_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f78,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | ~ v1_funct_1(k4_relat_1(sK0))
    | k2_funct_1(k4_relat_1(sK0)) = k4_relat_1(k4_relat_1(sK0))
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(subsumption_resolution,[],[f77,f46])).

fof(f77,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | ~ v1_funct_1(k4_relat_1(sK0))
    | k2_funct_1(k4_relat_1(sK0)) = k4_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_5 ),
    inference(subsumption_resolution,[],[f76,f36])).

fof(f76,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | ~ v1_funct_1(k4_relat_1(sK0))
    | k2_funct_1(k4_relat_1(sK0)) = k4_relat_1(k4_relat_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_3
    | ~ spl1_5 ),
    inference(subsumption_resolution,[],[f75,f41])).

fof(f75,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | ~ v1_funct_1(k4_relat_1(sK0))
    | k2_funct_1(k4_relat_1(sK0)) = k4_relat_1(k4_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_5 ),
    inference(superposition,[],[f52,f58])).

fof(f58,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f56])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | k2_funct_1(k2_funct_1(X0)) = k4_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f27,f26])).

fof(f26,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => v2_funct_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).

fof(f27,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f66,plain,
    ( ~ spl1_6
    | spl1_1
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f60,f56,f29,f63])).

fof(f29,plain,
    ( spl1_1
  <=> sK0 = k2_funct_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f60,plain,
    ( sK0 != k2_funct_1(k4_relat_1(sK0))
    | spl1_1
    | ~ spl1_5 ),
    inference(superposition,[],[f31,f58])).

fof(f31,plain,
    ( sK0 != k2_funct_1(k2_funct_1(sK0))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f59,plain,
    ( spl1_5
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f54,f44,f39,f34,f56])).

fof(f54,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f53,f46])).

fof(f53,plain,
    ( ~ v1_relat_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f51,f41])).

fof(f51,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl1_2 ),
    inference(resolution,[],[f27,f36])).

fof(f47,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f18,f44])).

fof(f18,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( k2_funct_1(k2_funct_1(X0)) != X0
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( k2_funct_1(k2_funct_1(X0)) != X0
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(f42,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f19,f39])).

fof(f19,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f37,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f20,f34])).

fof(f20,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f32,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f21,f29])).

fof(f21,plain,(
    sK0 != k2_funct_1(k2_funct_1(sK0)) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:08:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (17894)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.42  % (17888)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.22/0.43  % (17891)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.43  % (17888)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f161,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f32,f37,f42,f47,f59,f66,f91,f98,f101,f111,f160])).
% 0.22/0.43  % (17893)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.43  fof(f160,plain,(
% 0.22/0.43    ~spl1_4 | spl1_11),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f159])).
% 0.22/0.43  fof(f159,plain,(
% 0.22/0.43    $false | (~spl1_4 | spl1_11)),
% 0.22/0.43    inference(subsumption_resolution,[],[f158,f46])).
% 0.22/0.43  fof(f46,plain,(
% 0.22/0.43    v1_relat_1(sK0) | ~spl1_4),
% 0.22/0.43    inference(avatar_component_clause,[],[f44])).
% 0.22/0.43  fof(f44,plain,(
% 0.22/0.43    spl1_4 <=> v1_relat_1(sK0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.22/0.43  fof(f158,plain,(
% 0.22/0.43    ~v1_relat_1(sK0) | spl1_11),
% 0.22/0.43    inference(trivial_inequality_removal,[],[f157])).
% 0.22/0.43  fof(f157,plain,(
% 0.22/0.43    sK0 != sK0 | ~v1_relat_1(sK0) | spl1_11),
% 0.22/0.43    inference(superposition,[],[f110,f23])).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f11])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 0.22/0.43  fof(f110,plain,(
% 0.22/0.43    sK0 != k4_relat_1(k4_relat_1(sK0)) | spl1_11),
% 0.22/0.43    inference(avatar_component_clause,[],[f108])).
% 0.22/0.43  fof(f108,plain,(
% 0.22/0.43    spl1_11 <=> sK0 = k4_relat_1(k4_relat_1(sK0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.22/0.43  fof(f111,plain,(
% 0.22/0.43    ~spl1_11 | spl1_6 | ~spl1_8),
% 0.22/0.43    inference(avatar_split_clause,[],[f104,f80,f63,f108])).
% 0.22/0.43  fof(f63,plain,(
% 0.22/0.43    spl1_6 <=> sK0 = k2_funct_1(k4_relat_1(sK0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.22/0.43  fof(f80,plain,(
% 0.22/0.43    spl1_8 <=> k2_funct_1(k4_relat_1(sK0)) = k4_relat_1(k4_relat_1(sK0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.22/0.43  fof(f104,plain,(
% 0.22/0.43    sK0 != k4_relat_1(k4_relat_1(sK0)) | (spl1_6 | ~spl1_8)),
% 0.22/0.43    inference(superposition,[],[f65,f82])).
% 0.22/0.43  fof(f82,plain,(
% 0.22/0.43    k2_funct_1(k4_relat_1(sK0)) = k4_relat_1(k4_relat_1(sK0)) | ~spl1_8),
% 0.22/0.43    inference(avatar_component_clause,[],[f80])).
% 0.22/0.43  fof(f65,plain,(
% 0.22/0.43    sK0 != k2_funct_1(k4_relat_1(sK0)) | spl1_6),
% 0.22/0.43    inference(avatar_component_clause,[],[f63])).
% 0.22/0.43  fof(f101,plain,(
% 0.22/0.43    ~spl1_4 | spl1_10),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f100])).
% 0.22/0.43  fof(f100,plain,(
% 0.22/0.43    $false | (~spl1_4 | spl1_10)),
% 0.22/0.43    inference(subsumption_resolution,[],[f99,f46])).
% 0.22/0.43  fof(f99,plain,(
% 0.22/0.43    ~v1_relat_1(sK0) | spl1_10),
% 0.22/0.43    inference(resolution,[],[f90,f22])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f10])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.22/0.43  fof(f90,plain,(
% 0.22/0.43    ~v1_relat_1(k4_relat_1(sK0)) | spl1_10),
% 0.22/0.43    inference(avatar_component_clause,[],[f88])).
% 0.22/0.43  fof(f88,plain,(
% 0.22/0.43    spl1_10 <=> v1_relat_1(k4_relat_1(sK0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.22/0.43  fof(f98,plain,(
% 0.22/0.43    ~spl1_2 | ~spl1_3 | ~spl1_4 | spl1_9),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f97])).
% 0.22/0.43  fof(f97,plain,(
% 0.22/0.43    $false | (~spl1_2 | ~spl1_3 | ~spl1_4 | spl1_9)),
% 0.22/0.43    inference(subsumption_resolution,[],[f96,f46])).
% 0.22/0.43  fof(f96,plain,(
% 0.22/0.43    ~v1_relat_1(sK0) | (~spl1_2 | ~spl1_3 | spl1_9)),
% 0.22/0.43    inference(subsumption_resolution,[],[f95,f36])).
% 0.22/0.43  fof(f36,plain,(
% 0.22/0.43    v2_funct_1(sK0) | ~spl1_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f34])).
% 0.22/0.43  fof(f34,plain,(
% 0.22/0.43    spl1_2 <=> v2_funct_1(sK0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.43  fof(f95,plain,(
% 0.22/0.43    ~v2_funct_1(sK0) | ~v1_relat_1(sK0) | (~spl1_3 | spl1_9)),
% 0.22/0.43    inference(subsumption_resolution,[],[f93,f41])).
% 0.22/0.43  fof(f41,plain,(
% 0.22/0.43    v1_funct_1(sK0) | ~spl1_3),
% 0.22/0.43    inference(avatar_component_clause,[],[f39])).
% 0.22/0.43  fof(f39,plain,(
% 0.22/0.43    spl1_3 <=> v1_funct_1(sK0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.43  fof(f93,plain,(
% 0.22/0.43    ~v1_funct_1(sK0) | ~v2_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_9),
% 0.22/0.43    inference(resolution,[],[f86,f25])).
% 0.22/0.43  fof(f25,plain,(
% 0.22/0.43    ( ! [X0] : (v1_funct_1(k4_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f13])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ! [X0] : ((v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.43    inference(flattening,[],[f12])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ! [X0] : ((v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.43    inference(ennf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_funct_1)).
% 0.22/0.43  fof(f86,plain,(
% 0.22/0.43    ~v1_funct_1(k4_relat_1(sK0)) | spl1_9),
% 0.22/0.43    inference(avatar_component_clause,[],[f84])).
% 0.22/0.43  fof(f84,plain,(
% 0.22/0.43    spl1_9 <=> v1_funct_1(k4_relat_1(sK0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.22/0.43  fof(f91,plain,(
% 0.22/0.43    spl1_8 | ~spl1_9 | ~spl1_10 | ~spl1_2 | ~spl1_3 | ~spl1_4 | ~spl1_5),
% 0.22/0.43    inference(avatar_split_clause,[],[f78,f56,f44,f39,f34,f88,f84,f80])).
% 0.22/0.43  fof(f56,plain,(
% 0.22/0.43    spl1_5 <=> k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.22/0.43  fof(f78,plain,(
% 0.22/0.43    ~v1_relat_1(k4_relat_1(sK0)) | ~v1_funct_1(k4_relat_1(sK0)) | k2_funct_1(k4_relat_1(sK0)) = k4_relat_1(k4_relat_1(sK0)) | (~spl1_2 | ~spl1_3 | ~spl1_4 | ~spl1_5)),
% 0.22/0.43    inference(subsumption_resolution,[],[f77,f46])).
% 0.22/0.43  fof(f77,plain,(
% 0.22/0.43    ~v1_relat_1(k4_relat_1(sK0)) | ~v1_funct_1(k4_relat_1(sK0)) | k2_funct_1(k4_relat_1(sK0)) = k4_relat_1(k4_relat_1(sK0)) | ~v1_relat_1(sK0) | (~spl1_2 | ~spl1_3 | ~spl1_5)),
% 0.22/0.43    inference(subsumption_resolution,[],[f76,f36])).
% 0.22/0.43  fof(f76,plain,(
% 0.22/0.43    ~v1_relat_1(k4_relat_1(sK0)) | ~v1_funct_1(k4_relat_1(sK0)) | k2_funct_1(k4_relat_1(sK0)) = k4_relat_1(k4_relat_1(sK0)) | ~v2_funct_1(sK0) | ~v1_relat_1(sK0) | (~spl1_3 | ~spl1_5)),
% 0.22/0.43    inference(subsumption_resolution,[],[f75,f41])).
% 0.22/0.43  fof(f75,plain,(
% 0.22/0.43    ~v1_relat_1(k4_relat_1(sK0)) | ~v1_funct_1(k4_relat_1(sK0)) | k2_funct_1(k4_relat_1(sK0)) = k4_relat_1(k4_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v2_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl1_5),
% 0.22/0.43    inference(superposition,[],[f52,f58])).
% 0.22/0.43  fof(f58,plain,(
% 0.22/0.43    k2_funct_1(sK0) = k4_relat_1(sK0) | ~spl1_5),
% 0.22/0.43    inference(avatar_component_clause,[],[f56])).
% 0.22/0.43  fof(f52,plain,(
% 0.22/0.43    ( ! [X0] : (~v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(k2_funct_1(X0)) | k2_funct_1(k2_funct_1(X0)) = k4_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.43    inference(resolution,[],[f27,f26])).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f15])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.43    inference(flattening,[],[f14])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.43    inference(ennf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,axiom,(
% 0.22/0.43    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => v2_funct_1(k2_funct_1(X0))))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f17])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.43    inference(flattening,[],[f16])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.43    inference(ennf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 0.22/0.43  fof(f66,plain,(
% 0.22/0.43    ~spl1_6 | spl1_1 | ~spl1_5),
% 0.22/0.43    inference(avatar_split_clause,[],[f60,f56,f29,f63])).
% 0.22/0.43  fof(f29,plain,(
% 0.22/0.43    spl1_1 <=> sK0 = k2_funct_1(k2_funct_1(sK0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.43  fof(f60,plain,(
% 0.22/0.43    sK0 != k2_funct_1(k4_relat_1(sK0)) | (spl1_1 | ~spl1_5)),
% 0.22/0.43    inference(superposition,[],[f31,f58])).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    sK0 != k2_funct_1(k2_funct_1(sK0)) | spl1_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f29])).
% 0.22/0.43  fof(f59,plain,(
% 0.22/0.43    spl1_5 | ~spl1_2 | ~spl1_3 | ~spl1_4),
% 0.22/0.43    inference(avatar_split_clause,[],[f54,f44,f39,f34,f56])).
% 0.22/0.43  fof(f54,plain,(
% 0.22/0.43    k2_funct_1(sK0) = k4_relat_1(sK0) | (~spl1_2 | ~spl1_3 | ~spl1_4)),
% 0.22/0.43    inference(subsumption_resolution,[],[f53,f46])).
% 0.22/0.43  fof(f53,plain,(
% 0.22/0.43    ~v1_relat_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0) | (~spl1_2 | ~spl1_3)),
% 0.22/0.43    inference(subsumption_resolution,[],[f51,f41])).
% 0.22/0.43  fof(f51,plain,(
% 0.22/0.43    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0) | ~spl1_2),
% 0.22/0.43    inference(resolution,[],[f27,f36])).
% 0.22/0.43  fof(f47,plain,(
% 0.22/0.43    spl1_4),
% 0.22/0.43    inference(avatar_split_clause,[],[f18,f44])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    v1_relat_1(sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f9])).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    ? [X0] : (k2_funct_1(k2_funct_1(X0)) != X0 & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.43    inference(flattening,[],[f8])).
% 0.22/0.43  fof(f8,plain,(
% 0.22/0.43    ? [X0] : ((k2_funct_1(k2_funct_1(X0)) != X0 & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.43    inference(ennf_transformation,[],[f7])).
% 0.22/0.43  fof(f7,negated_conjecture,(
% 0.22/0.43    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.22/0.43    inference(negated_conjecture,[],[f6])).
% 0.22/0.43  fof(f6,conjecture,(
% 0.22/0.43    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 0.22/0.43  fof(f42,plain,(
% 0.22/0.43    spl1_3),
% 0.22/0.43    inference(avatar_split_clause,[],[f19,f39])).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    v1_funct_1(sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f9])).
% 0.22/0.43  fof(f37,plain,(
% 0.22/0.43    spl1_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f20,f34])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    v2_funct_1(sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f9])).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    ~spl1_1),
% 0.22/0.43    inference(avatar_split_clause,[],[f21,f29])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    sK0 != k2_funct_1(k2_funct_1(sK0))),
% 0.22/0.43    inference(cnf_transformation,[],[f9])).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (17888)------------------------------
% 0.22/0.43  % (17888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (17888)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (17888)Memory used [KB]: 10618
% 0.22/0.43  % (17888)Time elapsed: 0.007 s
% 0.22/0.43  % (17888)------------------------------
% 0.22/0.43  % (17888)------------------------------
% 0.22/0.43  % (17886)Success in time 0.074 s
%------------------------------------------------------------------------------
