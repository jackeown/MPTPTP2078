%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:39 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   44 (  65 expanded)
%              Number of leaves         :   10 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   99 ( 151 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f95,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f22,f27,f32,f38,f45,f59,f94])).

fof(f94,plain,
    ( ~ spl3_3
    | spl3_7 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | ~ spl3_3
    | spl3_7 ),
    inference(subsumption_resolution,[],[f92,f31])).

fof(f31,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f92,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_7 ),
    inference(resolution,[],[f56,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f56,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl3_7
  <=> v1_relat_1(k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f59,plain,
    ( ~ spl3_7
    | spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f58,f42,f19,f54])).

fof(f19,plain,
    ( spl3_1
  <=> r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f42,plain,
    ( spl3_5
  <=> k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f58,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | spl3_1
    | ~ spl3_5 ),
    inference(global_subsumption,[],[f52])).

fof(f52,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | spl3_1
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f50,f21])).

fof(f21,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f19])).

fof(f50,plain,
    ( r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ spl3_5 ),
    inference(superposition,[],[f16,f44])).

fof(f44,plain,
    ( k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK1),sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f42])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f45,plain,
    ( spl3_5
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f39,f36,f24,f42])).

fof(f24,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f36,plain,
    ( spl3_4
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | k7_relat_1(k7_relat_1(sK2,X1),X0) = k7_relat_1(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f39,plain,
    ( k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK1),sK0)
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(resolution,[],[f37,f26])).

fof(f26,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f24])).

fof(f37,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k7_relat_1(k7_relat_1(sK2,X1),X0) = k7_relat_1(sK2,X0) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f36])).

fof(f38,plain,
    ( spl3_4
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f33,f29,f36])).

fof(f33,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k7_relat_1(k7_relat_1(sK2,X1),X0) = k7_relat_1(sK2,X0) )
    | ~ spl3_3 ),
    inference(resolution,[],[f17,f31])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

fof(f32,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f12,f29])).

fof(f12,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_relat_1)).

fof(f27,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f13,f24])).

fof(f13,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f22,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f14,f19])).

fof(f14,plain,(
    ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:01:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.41  % (26437)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.14/0.41  % (26437)Refutation found. Thanks to Tanya!
% 0.14/0.41  % SZS status Theorem for theBenchmark
% 0.14/0.41  % SZS output start Proof for theBenchmark
% 0.14/0.41  fof(f95,plain,(
% 0.14/0.41    $false),
% 0.14/0.41    inference(avatar_sat_refutation,[],[f22,f27,f32,f38,f45,f59,f94])).
% 0.14/0.41  fof(f94,plain,(
% 0.14/0.41    ~spl3_3 | spl3_7),
% 0.14/0.41    inference(avatar_contradiction_clause,[],[f93])).
% 0.14/0.41  fof(f93,plain,(
% 0.14/0.41    $false | (~spl3_3 | spl3_7)),
% 0.14/0.41    inference(subsumption_resolution,[],[f92,f31])).
% 0.14/0.41  fof(f31,plain,(
% 0.14/0.41    v1_relat_1(sK2) | ~spl3_3),
% 0.14/0.41    inference(avatar_component_clause,[],[f29])).
% 0.14/0.41  fof(f29,plain,(
% 0.14/0.41    spl3_3 <=> v1_relat_1(sK2)),
% 0.14/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.14/0.41  fof(f92,plain,(
% 0.14/0.41    ~v1_relat_1(sK2) | spl3_7),
% 0.14/0.41    inference(resolution,[],[f56,f15])).
% 0.14/0.41  fof(f15,plain,(
% 0.14/0.41    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.14/0.41    inference(cnf_transformation,[],[f8])).
% 0.14/0.41  fof(f8,plain,(
% 0.14/0.41    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.14/0.41    inference(ennf_transformation,[],[f1])).
% 0.14/0.41  fof(f1,axiom,(
% 0.14/0.41    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.14/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.14/0.41  fof(f56,plain,(
% 0.14/0.41    ~v1_relat_1(k7_relat_1(sK2,sK1)) | spl3_7),
% 0.14/0.41    inference(avatar_component_clause,[],[f54])).
% 0.14/0.41  fof(f54,plain,(
% 0.14/0.41    spl3_7 <=> v1_relat_1(k7_relat_1(sK2,sK1))),
% 0.14/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.14/0.41  fof(f59,plain,(
% 0.14/0.41    ~spl3_7 | spl3_1 | ~spl3_5),
% 0.14/0.41    inference(avatar_split_clause,[],[f58,f42,f19,f54])).
% 0.14/0.41  fof(f19,plain,(
% 0.14/0.41    spl3_1 <=> r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),
% 0.14/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.14/0.41  fof(f42,plain,(
% 0.14/0.41    spl3_5 <=> k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK1),sK0)),
% 0.14/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.14/0.41  fof(f58,plain,(
% 0.14/0.41    ~v1_relat_1(k7_relat_1(sK2,sK1)) | (spl3_1 | ~spl3_5)),
% 0.14/0.41    inference(global_subsumption,[],[f52])).
% 0.14/0.41  fof(f52,plain,(
% 0.14/0.41    ~v1_relat_1(k7_relat_1(sK2,sK1)) | (spl3_1 | ~spl3_5)),
% 0.14/0.41    inference(subsumption_resolution,[],[f50,f21])).
% 0.14/0.41  fof(f21,plain,(
% 0.14/0.41    ~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)) | spl3_1),
% 0.14/0.41    inference(avatar_component_clause,[],[f19])).
% 0.14/0.41  fof(f50,plain,(
% 0.14/0.41    r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)) | ~v1_relat_1(k7_relat_1(sK2,sK1)) | ~spl3_5),
% 0.14/0.41    inference(superposition,[],[f16,f44])).
% 0.14/0.41  fof(f44,plain,(
% 0.14/0.41    k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK1),sK0) | ~spl3_5),
% 0.14/0.41    inference(avatar_component_clause,[],[f42])).
% 0.14/0.41  fof(f16,plain,(
% 0.14/0.41    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.14/0.41    inference(cnf_transformation,[],[f9])).
% 0.14/0.41  fof(f9,plain,(
% 0.14/0.41    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.14/0.41    inference(ennf_transformation,[],[f3])).
% 0.14/0.41  fof(f3,axiom,(
% 0.14/0.41    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.14/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 0.14/0.41  fof(f45,plain,(
% 0.14/0.41    spl3_5 | ~spl3_2 | ~spl3_4),
% 0.14/0.41    inference(avatar_split_clause,[],[f39,f36,f24,f42])).
% 0.14/0.41  fof(f24,plain,(
% 0.14/0.41    spl3_2 <=> r1_tarski(sK0,sK1)),
% 0.14/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.14/0.41  fof(f36,plain,(
% 0.14/0.41    spl3_4 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | k7_relat_1(k7_relat_1(sK2,X1),X0) = k7_relat_1(sK2,X0))),
% 0.14/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.14/0.41  fof(f39,plain,(
% 0.14/0.41    k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK1),sK0) | (~spl3_2 | ~spl3_4)),
% 0.14/0.41    inference(resolution,[],[f37,f26])).
% 0.14/0.41  fof(f26,plain,(
% 0.14/0.41    r1_tarski(sK0,sK1) | ~spl3_2),
% 0.14/0.41    inference(avatar_component_clause,[],[f24])).
% 0.14/0.41  fof(f37,plain,(
% 0.14/0.41    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k7_relat_1(k7_relat_1(sK2,X1),X0) = k7_relat_1(sK2,X0)) ) | ~spl3_4),
% 0.14/0.41    inference(avatar_component_clause,[],[f36])).
% 0.14/0.41  fof(f38,plain,(
% 0.14/0.41    spl3_4 | ~spl3_3),
% 0.14/0.41    inference(avatar_split_clause,[],[f33,f29,f36])).
% 0.14/0.41  fof(f33,plain,(
% 0.14/0.41    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k7_relat_1(k7_relat_1(sK2,X1),X0) = k7_relat_1(sK2,X0)) ) | ~spl3_3),
% 0.14/0.41    inference(resolution,[],[f17,f31])).
% 0.14/0.41  fof(f17,plain,(
% 0.14/0.41    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)) )),
% 0.14/0.41    inference(cnf_transformation,[],[f11])).
% 0.21/0.41  fof(f11,plain,(
% 0.21/0.41    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.41    inference(flattening,[],[f10])).
% 0.21/0.41  fof(f10,plain,(
% 0.21/0.41    ! [X0,X1,X2] : ((k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.41    inference(ennf_transformation,[],[f2])).
% 0.21/0.41  fof(f2,axiom,(
% 0.21/0.41    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).
% 0.21/0.41  fof(f32,plain,(
% 0.21/0.41    spl3_3),
% 0.21/0.41    inference(avatar_split_clause,[],[f12,f29])).
% 0.21/0.41  fof(f12,plain,(
% 0.21/0.41    v1_relat_1(sK2)),
% 0.21/0.41    inference(cnf_transformation,[],[f7])).
% 0.21/0.41  fof(f7,plain,(
% 0.21/0.41    ? [X0,X1,X2] : (~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.21/0.41    inference(flattening,[],[f6])).
% 0.21/0.41  fof(f6,plain,(
% 0.21/0.41    ? [X0,X1,X2] : ((~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.21/0.41    inference(ennf_transformation,[],[f5])).
% 0.21/0.41  fof(f5,negated_conjecture,(
% 0.21/0.41    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))))),
% 0.21/0.41    inference(negated_conjecture,[],[f4])).
% 0.21/0.41  fof(f4,conjecture,(
% 0.21/0.41    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_relat_1)).
% 0.21/0.41  fof(f27,plain,(
% 0.21/0.41    spl3_2),
% 0.21/0.41    inference(avatar_split_clause,[],[f13,f24])).
% 0.21/0.41  fof(f13,plain,(
% 0.21/0.41    r1_tarski(sK0,sK1)),
% 0.21/0.41    inference(cnf_transformation,[],[f7])).
% 0.21/0.41  fof(f22,plain,(
% 0.21/0.41    ~spl3_1),
% 0.21/0.41    inference(avatar_split_clause,[],[f14,f19])).
% 0.21/0.41  fof(f14,plain,(
% 0.21/0.41    ~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),
% 0.21/0.41    inference(cnf_transformation,[],[f7])).
% 0.21/0.41  % SZS output end Proof for theBenchmark
% 0.21/0.41  % (26437)------------------------------
% 0.21/0.41  % (26437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (26437)Termination reason: Refutation
% 0.21/0.41  
% 0.21/0.41  % (26437)Memory used [KB]: 10618
% 0.21/0.41  % (26437)Time elapsed: 0.005 s
% 0.21/0.41  % (26437)------------------------------
% 0.21/0.41  % (26437)------------------------------
% 0.21/0.42  % (26433)Success in time 0.06 s
%------------------------------------------------------------------------------
