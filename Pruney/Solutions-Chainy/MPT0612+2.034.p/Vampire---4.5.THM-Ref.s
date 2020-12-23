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
% DateTime   : Thu Dec  3 12:51:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   51 (  81 expanded)
%              Number of leaves         :   13 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :  108 ( 182 expanded)
%              Number of equality atoms :   23 (  45 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f114,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f40,f61,f72,f94,f101,f113])).

fof(f113,plain,(
    spl3_12 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | spl3_12 ),
    inference(global_subsumption,[],[f17,f106])).

fof(f106,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_12 ),
    inference(resolution,[],[f100,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f100,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(k1_relat_1(sK2),sK1))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl3_12
  <=> r1_xboole_0(sK0,k4_xboole_0(k1_relat_1(sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f17,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t216_relat_1)).

fof(f101,plain,
    ( ~ spl3_12
    | spl3_9
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f95,f92,f69,f98])).

fof(f69,plain,
    ( spl3_9
  <=> r1_xboole_0(sK0,k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f92,plain,
    ( spl3_11
  <=> ! [X0] : k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0))) = k4_xboole_0(k1_relat_1(sK2),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f95,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(k1_relat_1(sK2),sK1))
    | spl3_9
    | ~ spl3_11 ),
    inference(superposition,[],[f71,f93])).

fof(f93,plain,
    ( ! [X0] : k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0))) = k4_xboole_0(k1_relat_1(sK2),X0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f92])).

fof(f71,plain,
    ( ~ r1_xboole_0(sK0,k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1))))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f94,plain,
    ( spl3_11
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f78,f27,f92])).

fof(f27,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f78,plain,
    ( ! [X0] : k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0))) = k4_xboole_0(k1_relat_1(sK2),X0)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f29,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k4_xboole_0(X1,k7_relat_1(X1,X0))) = k4_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(definition_unfolding,[],[f22,f20,f20])).

fof(f20,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).

fof(f29,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f72,plain,
    ( ~ spl3_9
    | ~ spl3_3
    | spl3_7 ),
    inference(avatar_split_clause,[],[f67,f58,f38,f69])).

fof(f38,plain,
    ( spl3_3
  <=> ! [X0] : v1_relat_1(k4_xboole_0(sK2,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f58,plain,
    ( spl3_7
  <=> k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f67,plain,
    ( ~ r1_xboole_0(sK0,k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1))))
    | ~ spl3_3
    | spl3_7 ),
    inference(unit_resulting_resolution,[],[f39,f60,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,k1_relat_1(X0))
      | k7_relat_1(X0,X1) = k1_xboole_0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_relat_1(X0,X1) = k1_xboole_0
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k7_relat_1(X0,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

fof(f60,plain,
    ( k1_xboole_0 != k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f58])).

fof(f39,plain,
    ( ! [X0] : v1_relat_1(k4_xboole_0(sK2,X0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f61,plain,(
    ~ spl3_7 ),
    inference(avatar_split_clause,[],[f24,f58])).

fof(f24,plain,(
    k1_xboole_0 != k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0) ),
    inference(definition_unfolding,[],[f18,f20])).

fof(f18,plain,(
    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f40,plain,
    ( spl3_3
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f36,f27,f38])).

fof(f36,plain,
    ( ! [X0] : v1_relat_1(k4_xboole_0(sK2,X0))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f29,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

fof(f30,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f16,f27])).

fof(f16,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:56:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (26998)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.42  % (26998)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f114,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f30,f40,f61,f72,f94,f101,f113])).
% 0.21/0.42  fof(f113,plain,(
% 0.21/0.42    spl3_12),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f112])).
% 0.21/0.42  fof(f112,plain,(
% 0.21/0.42    $false | spl3_12),
% 0.21/0.42    inference(global_subsumption,[],[f17,f106])).
% 0.21/0.42  fof(f106,plain,(
% 0.21/0.42    ~r1_tarski(sK0,sK1) | spl3_12),
% 0.21/0.42    inference(resolution,[],[f100,f23])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.21/0.42  fof(f100,plain,(
% 0.21/0.42    ~r1_xboole_0(sK0,k4_xboole_0(k1_relat_1(sK2),sK1)) | spl3_12),
% 0.21/0.42    inference(avatar_component_clause,[],[f98])).
% 0.21/0.42  fof(f98,plain,(
% 0.21/0.42    spl3_12 <=> r1_xboole_0(sK0,k4_xboole_0(k1_relat_1(sK2),sK1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    r1_tarski(sK0,sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.21/0.42    inference(flattening,[],[f8])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ? [X0,X1,X2] : ((k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.21/0.42    inference(ennf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)))),
% 0.21/0.42    inference(negated_conjecture,[],[f6])).
% 0.21/0.42  fof(f6,conjecture,(
% 0.21/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t216_relat_1)).
% 0.21/0.42  fof(f101,plain,(
% 0.21/0.42    ~spl3_12 | spl3_9 | ~spl3_11),
% 0.21/0.42    inference(avatar_split_clause,[],[f95,f92,f69,f98])).
% 0.21/0.42  fof(f69,plain,(
% 0.21/0.42    spl3_9 <=> r1_xboole_0(sK0,k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1))))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.42  fof(f92,plain,(
% 0.21/0.42    spl3_11 <=> ! [X0] : k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0))) = k4_xboole_0(k1_relat_1(sK2),X0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.42  fof(f95,plain,(
% 0.21/0.42    ~r1_xboole_0(sK0,k4_xboole_0(k1_relat_1(sK2),sK1)) | (spl3_9 | ~spl3_11)),
% 0.21/0.42    inference(superposition,[],[f71,f93])).
% 0.21/0.42  fof(f93,plain,(
% 0.21/0.42    ( ! [X0] : (k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0))) = k4_xboole_0(k1_relat_1(sK2),X0)) ) | ~spl3_11),
% 0.21/0.42    inference(avatar_component_clause,[],[f92])).
% 0.21/0.42  fof(f71,plain,(
% 0.21/0.42    ~r1_xboole_0(sK0,k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)))) | spl3_9),
% 0.21/0.42    inference(avatar_component_clause,[],[f69])).
% 0.21/0.42  fof(f94,plain,(
% 0.21/0.42    spl3_11 | ~spl3_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f78,f27,f92])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    spl3_1 <=> v1_relat_1(sK2)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.42  fof(f78,plain,(
% 0.21/0.42    ( ! [X0] : (k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0))) = k4_xboole_0(k1_relat_1(sK2),X0)) ) | ~spl3_1),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f29,f25])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k4_xboole_0(X1,k7_relat_1(X1,X0))) = k4_xboole_0(k1_relat_1(X1),X0)) )),
% 0.21/0.42    inference(definition_unfolding,[],[f22,f20,f20])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    v1_relat_1(sK2) | ~spl3_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f27])).
% 0.21/0.42  fof(f72,plain,(
% 0.21/0.42    ~spl3_9 | ~spl3_3 | spl3_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f67,f58,f38,f69])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    spl3_3 <=> ! [X0] : v1_relat_1(k4_xboole_0(sK2,X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    spl3_7 <=> k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.42  fof(f67,plain,(
% 0.21/0.42    ~r1_xboole_0(sK0,k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)))) | (~spl3_3 | spl3_7)),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f39,f60,f19])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_xboole_0(X1,k1_relat_1(X0)) | k7_relat_1(X0,X1) = k1_xboole_0 | ~v1_relat_1(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (k7_relat_1(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k7_relat_1(X0,X1) = k1_xboole_0))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).
% 0.21/0.42  fof(f60,plain,(
% 0.21/0.42    k1_xboole_0 != k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0) | spl3_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f58])).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    ( ! [X0] : (v1_relat_1(k4_xboole_0(sK2,X0))) ) | ~spl3_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f38])).
% 0.21/0.42  fof(f61,plain,(
% 0.21/0.42    ~spl3_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f24,f58])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    k1_xboole_0 != k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0)),
% 0.21/0.42    inference(definition_unfolding,[],[f18,f20])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f15])).
% 0.21/0.42  fof(f40,plain,(
% 0.21/0.42    spl3_3 | ~spl3_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f36,f27,f38])).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    ( ! [X0] : (v1_relat_1(k4_xboole_0(sK2,X0))) ) | ~spl3_1),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f29,f21])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k4_xboole_0(X0,X1)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    spl3_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f16,f27])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    v1_relat_1(sK2)),
% 0.21/0.42    inference(cnf_transformation,[],[f15])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (26998)------------------------------
% 0.21/0.42  % (26998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (26998)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (26998)Memory used [KB]: 10618
% 0.21/0.42  % (26998)Time elapsed: 0.006 s
% 0.21/0.42  % (26998)------------------------------
% 0.21/0.42  % (26998)------------------------------
% 0.21/0.42  % (26980)Success in time 0.063 s
%------------------------------------------------------------------------------
