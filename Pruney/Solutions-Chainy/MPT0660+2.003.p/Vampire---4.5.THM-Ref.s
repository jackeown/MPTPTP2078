%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   46 (  59 expanded)
%              Number of leaves         :   13 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :  107 ( 139 expanded)
%              Number of equality atoms :   26 (  32 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f54,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f22,f26,f30,f34,f38,f42,f50,f53])).

fof(f53,plain,
    ( spl1_1
    | ~ spl1_7 ),
    inference(avatar_contradiction_clause,[],[f52])).

fof(f52,plain,
    ( $false
    | spl1_1
    | ~ spl1_7 ),
    inference(trivial_inequality_removal,[],[f51])).

fof(f51,plain,
    ( k6_relat_1(sK0) != k6_relat_1(sK0)
    | spl1_1
    | ~ spl1_7 ),
    inference(superposition,[],[f21,f49])).

fof(f49,plain,
    ( ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl1_7
  <=> ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f21,plain,
    ( k6_relat_1(sK0) != k2_funct_1(k6_relat_1(sK0))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f19])).

fof(f19,plain,
    ( spl1_1
  <=> k6_relat_1(sK0) = k2_funct_1(k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f50,plain,
    ( spl1_7
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f46,f40,f36,f32,f28,f24,f48])).

fof(f24,plain,
    ( spl1_2
  <=> ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f28,plain,
    ( spl1_3
  <=> ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f32,plain,
    ( spl1_4
  <=> ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f36,plain,
    ( spl1_5
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f40,plain,
    ( spl1_6
  <=> ! [X0] :
        ( k2_funct_1(X0) = k4_relat_1(X0)
        | ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f46,plain,
    ( ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(forward_demodulation,[],[f45,f29])).

fof(f29,plain,
    ( ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f28])).

fof(f45,plain,
    ( ! [X0] : k4_relat_1(k6_relat_1(X0)) = k2_funct_1(k6_relat_1(X0))
    | ~ spl1_2
    | ~ spl1_4
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(subsumption_resolution,[],[f44,f37])).

fof(f37,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f36])).

fof(f44,plain,
    ( ! [X0] :
        ( k4_relat_1(k6_relat_1(X0)) = k2_funct_1(k6_relat_1(X0))
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl1_2
    | ~ spl1_4
    | ~ spl1_6 ),
    inference(subsumption_resolution,[],[f43,f33])).

fof(f33,plain,
    ( ! [X0] : v1_funct_1(k6_relat_1(X0))
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f32])).

fof(f43,plain,
    ( ! [X0] :
        ( k4_relat_1(k6_relat_1(X0)) = k2_funct_1(k6_relat_1(X0))
        | ~ v1_funct_1(k6_relat_1(X0))
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl1_2
    | ~ spl1_6 ),
    inference(resolution,[],[f41,f25])).

fof(f25,plain,
    ( ! [X0] : v2_funct_1(k6_relat_1(X0))
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f24])).

fof(f41,plain,
    ( ! [X0] :
        ( ~ v2_funct_1(X0)
        | k2_funct_1(X0) = k4_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f40])).

fof(f42,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f17,f40])).

fof(f17,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(X0) = k4_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f38,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f15,f36])).

fof(f15,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f34,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f16,f32])).

fof(f16,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f30,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f14,f28])).

fof(f14,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

fof(f26,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f13,f24])).

fof(f13,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

fof(f22,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f12,f19])).

fof(f12,plain,(
    k6_relat_1(sK0) != k2_funct_1(k6_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    k6_relat_1(sK0) != k2_funct_1(k6_relat_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f10])).

fof(f10,plain,
    ( ? [X0] : k6_relat_1(X0) != k2_funct_1(k6_relat_1(X0))
   => k6_relat_1(sK0) != k2_funct_1(k6_relat_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] : k6_relat_1(X0) != k2_funct_1(k6_relat_1(X0)) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:50:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.42  % (14083)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.42  % (14083)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f54,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(avatar_sat_refutation,[],[f22,f26,f30,f34,f38,f42,f50,f53])).
% 0.22/0.42  fof(f53,plain,(
% 0.22/0.42    spl1_1 | ~spl1_7),
% 0.22/0.42    inference(avatar_contradiction_clause,[],[f52])).
% 0.22/0.42  fof(f52,plain,(
% 0.22/0.42    $false | (spl1_1 | ~spl1_7)),
% 0.22/0.42    inference(trivial_inequality_removal,[],[f51])).
% 0.22/0.42  fof(f51,plain,(
% 0.22/0.42    k6_relat_1(sK0) != k6_relat_1(sK0) | (spl1_1 | ~spl1_7)),
% 0.22/0.42    inference(superposition,[],[f21,f49])).
% 0.22/0.42  fof(f49,plain,(
% 0.22/0.42    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) ) | ~spl1_7),
% 0.22/0.42    inference(avatar_component_clause,[],[f48])).
% 0.22/0.42  fof(f48,plain,(
% 0.22/0.42    spl1_7 <=> ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.22/0.42  fof(f21,plain,(
% 0.22/0.42    k6_relat_1(sK0) != k2_funct_1(k6_relat_1(sK0)) | spl1_1),
% 0.22/0.42    inference(avatar_component_clause,[],[f19])).
% 0.22/0.42  fof(f19,plain,(
% 0.22/0.42    spl1_1 <=> k6_relat_1(sK0) = k2_funct_1(k6_relat_1(sK0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.42  fof(f50,plain,(
% 0.22/0.42    spl1_7 | ~spl1_2 | ~spl1_3 | ~spl1_4 | ~spl1_5 | ~spl1_6),
% 0.22/0.42    inference(avatar_split_clause,[],[f46,f40,f36,f32,f28,f24,f48])).
% 0.22/0.42  fof(f24,plain,(
% 0.22/0.42    spl1_2 <=> ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.42  fof(f28,plain,(
% 0.22/0.42    spl1_3 <=> ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.42  fof(f32,plain,(
% 0.22/0.42    spl1_4 <=> ! [X0] : v1_funct_1(k6_relat_1(X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.22/0.42  fof(f36,plain,(
% 0.22/0.42    spl1_5 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.22/0.42  fof(f40,plain,(
% 0.22/0.42    spl1_6 <=> ! [X0] : (k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.22/0.42  fof(f46,plain,(
% 0.22/0.42    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) ) | (~spl1_2 | ~spl1_3 | ~spl1_4 | ~spl1_5 | ~spl1_6)),
% 0.22/0.42    inference(forward_demodulation,[],[f45,f29])).
% 0.22/0.42  fof(f29,plain,(
% 0.22/0.42    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) ) | ~spl1_3),
% 0.22/0.42    inference(avatar_component_clause,[],[f28])).
% 0.22/0.42  fof(f45,plain,(
% 0.22/0.42    ( ! [X0] : (k4_relat_1(k6_relat_1(X0)) = k2_funct_1(k6_relat_1(X0))) ) | (~spl1_2 | ~spl1_4 | ~spl1_5 | ~spl1_6)),
% 0.22/0.42    inference(subsumption_resolution,[],[f44,f37])).
% 0.22/0.42  fof(f37,plain,(
% 0.22/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl1_5),
% 0.22/0.42    inference(avatar_component_clause,[],[f36])).
% 0.22/0.42  fof(f44,plain,(
% 0.22/0.42    ( ! [X0] : (k4_relat_1(k6_relat_1(X0)) = k2_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) ) | (~spl1_2 | ~spl1_4 | ~spl1_6)),
% 0.22/0.42    inference(subsumption_resolution,[],[f43,f33])).
% 0.22/0.42  fof(f33,plain,(
% 0.22/0.42    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) ) | ~spl1_4),
% 0.22/0.42    inference(avatar_component_clause,[],[f32])).
% 0.22/0.42  fof(f43,plain,(
% 0.22/0.42    ( ! [X0] : (k4_relat_1(k6_relat_1(X0)) = k2_funct_1(k6_relat_1(X0)) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) ) | (~spl1_2 | ~spl1_6)),
% 0.22/0.42    inference(resolution,[],[f41,f25])).
% 0.22/0.42  fof(f25,plain,(
% 0.22/0.42    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) ) | ~spl1_2),
% 0.22/0.42    inference(avatar_component_clause,[],[f24])).
% 0.22/0.42  fof(f41,plain,(
% 0.22/0.42    ( ! [X0] : (~v2_funct_1(X0) | k2_funct_1(X0) = k4_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl1_6),
% 0.22/0.42    inference(avatar_component_clause,[],[f40])).
% 0.22/0.42  fof(f42,plain,(
% 0.22/0.42    spl1_6),
% 0.22/0.42    inference(avatar_split_clause,[],[f17,f40])).
% 0.22/0.42  fof(f17,plain,(
% 0.22/0.42    ( ! [X0] : (k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f9])).
% 0.22/0.42  fof(f9,plain,(
% 0.22/0.42    ! [X0] : (k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.42    inference(flattening,[],[f8])).
% 0.22/0.42  fof(f8,plain,(
% 0.22/0.42    ! [X0] : ((k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.42    inference(ennf_transformation,[],[f2])).
% 0.22/0.42  fof(f2,axiom,(
% 0.22/0.42    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(X0) = k4_relat_1(X0)))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.22/0.42  fof(f38,plain,(
% 0.22/0.42    spl1_5),
% 0.22/0.42    inference(avatar_split_clause,[],[f15,f36])).
% 0.22/0.42  fof(f15,plain,(
% 0.22/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f3])).
% 0.22/0.42  fof(f3,axiom,(
% 0.22/0.42    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.22/0.42  fof(f34,plain,(
% 0.22/0.42    spl1_4),
% 0.22/0.42    inference(avatar_split_clause,[],[f16,f32])).
% 0.22/0.42  fof(f16,plain,(
% 0.22/0.42    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f3])).
% 0.22/0.42  fof(f30,plain,(
% 0.22/0.42    spl1_3),
% 0.22/0.42    inference(avatar_split_clause,[],[f14,f28])).
% 0.22/0.42  fof(f14,plain,(
% 0.22/0.42    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f1])).
% 0.22/0.42  fof(f1,axiom,(
% 0.22/0.42    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).
% 0.22/0.42  fof(f26,plain,(
% 0.22/0.42    spl1_2),
% 0.22/0.42    inference(avatar_split_clause,[],[f13,f24])).
% 0.22/0.42  fof(f13,plain,(
% 0.22/0.42    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f4])).
% 0.22/0.42  fof(f4,axiom,(
% 0.22/0.42    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).
% 0.22/0.42  fof(f22,plain,(
% 0.22/0.42    ~spl1_1),
% 0.22/0.42    inference(avatar_split_clause,[],[f12,f19])).
% 0.22/0.42  fof(f12,plain,(
% 0.22/0.42    k6_relat_1(sK0) != k2_funct_1(k6_relat_1(sK0))),
% 0.22/0.42    inference(cnf_transformation,[],[f11])).
% 0.22/0.42  fof(f11,plain,(
% 0.22/0.42    k6_relat_1(sK0) != k2_funct_1(k6_relat_1(sK0))),
% 0.22/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f10])).
% 0.22/0.42  fof(f10,plain,(
% 0.22/0.42    ? [X0] : k6_relat_1(X0) != k2_funct_1(k6_relat_1(X0)) => k6_relat_1(sK0) != k2_funct_1(k6_relat_1(sK0))),
% 0.22/0.42    introduced(choice_axiom,[])).
% 0.22/0.42  fof(f7,plain,(
% 0.22/0.42    ? [X0] : k6_relat_1(X0) != k2_funct_1(k6_relat_1(X0))),
% 0.22/0.42    inference(ennf_transformation,[],[f6])).
% 0.22/0.42  fof(f6,negated_conjecture,(
% 0.22/0.42    ~! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 0.22/0.42    inference(negated_conjecture,[],[f5])).
% 0.22/0.42  fof(f5,conjecture,(
% 0.22/0.42    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).
% 0.22/0.42  % SZS output end Proof for theBenchmark
% 0.22/0.42  % (14083)------------------------------
% 0.22/0.42  % (14083)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (14083)Termination reason: Refutation
% 0.22/0.42  
% 0.22/0.42  % (14083)Memory used [KB]: 10490
% 0.22/0.42  % (14083)Time elapsed: 0.006 s
% 0.22/0.42  % (14083)------------------------------
% 0.22/0.42  % (14083)------------------------------
% 0.22/0.42  % (14077)Success in time 0.063 s
%------------------------------------------------------------------------------
