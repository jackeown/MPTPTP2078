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
% DateTime   : Thu Dec  3 12:48:37 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   50 (  79 expanded)
%              Number of leaves         :   13 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :  110 ( 186 expanded)
%              Number of equality atoms :   35 (  59 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f80,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f26,f31,f36,f43,f55,f61,f69,f79])).

fof(f79,plain,
    ( spl3_3
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f78])).

fof(f78,plain,
    ( $false
    | spl3_3
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(global_subsumption,[],[f42,f75])).

fof(f75,plain,
    ( k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
    | spl3_3
    | ~ spl3_8 ),
    inference(superposition,[],[f35,f68])).

fof(f68,plain,
    ( ! [X2,X3] : k7_relat_1(k7_relat_1(sK2,X2),X3) = k7_relat_1(k7_relat_1(sK2,X3),X2)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl3_8
  <=> ! [X3,X2] : k7_relat_1(k7_relat_1(sK2,X2),X3) = k7_relat_1(k7_relat_1(sK2,X3),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f35,plain,
    ( k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl3_3
  <=> k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f42,plain,
    ( k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl3_4
  <=> k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f69,plain,
    ( spl3_8
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f64,f59,f53,f67])).

fof(f53,plain,
    ( spl3_6
  <=> ! [X1,X0] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f59,plain,
    ( spl3_7
  <=> ! [X1,X0] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k2_tarski(X1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f64,plain,
    ( ! [X2,X3] : k7_relat_1(k7_relat_1(sK2,X2),X3) = k7_relat_1(k7_relat_1(sK2,X3),X2)
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(superposition,[],[f60,f54])).

fof(f54,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f53])).

fof(f60,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k2_tarski(X1,X0)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f59])).

fof(f61,plain,
    ( spl3_7
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f56,f53,f59])).

fof(f56,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k2_tarski(X1,X0)))
    | ~ spl3_6 ),
    inference(superposition,[],[f54,f17])).

fof(f17,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f55,plain,
    ( spl3_6
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f50,f23,f53])).

fof(f23,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f50,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1)))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f25,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f19,f18])).

fof(f18,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f25,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f23])).

fof(f43,plain,
    ( spl3_4
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f37,f28,f23,f40])).

fof(f28,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f37,plain,
    ( k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1)
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f25,f30,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

fof(f30,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f36,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f16,f33])).

fof(f16,plain,(
    k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

fof(f31,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f15,f28])).

fof(f15,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f26,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f14,f23])).

fof(f14,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:42:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.44  % (16852)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.45  % (16852)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f80,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(avatar_sat_refutation,[],[f26,f31,f36,f43,f55,f61,f69,f79])).
% 0.22/0.45  fof(f79,plain,(
% 0.22/0.45    spl3_3 | ~spl3_4 | ~spl3_8),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f78])).
% 0.22/0.45  fof(f78,plain,(
% 0.22/0.45    $false | (spl3_3 | ~spl3_4 | ~spl3_8)),
% 0.22/0.45    inference(global_subsumption,[],[f42,f75])).
% 0.22/0.45  fof(f75,plain,(
% 0.22/0.45    k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1) | (spl3_3 | ~spl3_8)),
% 0.22/0.45    inference(superposition,[],[f35,f68])).
% 0.22/0.45  fof(f68,plain,(
% 0.22/0.45    ( ! [X2,X3] : (k7_relat_1(k7_relat_1(sK2,X2),X3) = k7_relat_1(k7_relat_1(sK2,X3),X2)) ) | ~spl3_8),
% 0.22/0.45    inference(avatar_component_clause,[],[f67])).
% 0.22/0.45  fof(f67,plain,(
% 0.22/0.45    spl3_8 <=> ! [X3,X2] : k7_relat_1(k7_relat_1(sK2,X2),X3) = k7_relat_1(k7_relat_1(sK2,X3),X2)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.45  fof(f35,plain,(
% 0.22/0.45    k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0) | spl3_3),
% 0.22/0.45    inference(avatar_component_clause,[],[f33])).
% 0.22/0.45  fof(f33,plain,(
% 0.22/0.45    spl3_3 <=> k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK1),sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.45  fof(f42,plain,(
% 0.22/0.45    k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1) | ~spl3_4),
% 0.22/0.45    inference(avatar_component_clause,[],[f40])).
% 0.22/0.45  fof(f40,plain,(
% 0.22/0.45    spl3_4 <=> k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.45  fof(f69,plain,(
% 0.22/0.45    spl3_8 | ~spl3_6 | ~spl3_7),
% 0.22/0.45    inference(avatar_split_clause,[],[f64,f59,f53,f67])).
% 0.22/0.45  fof(f53,plain,(
% 0.22/0.45    spl3_6 <=> ! [X1,X0] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.45  fof(f59,plain,(
% 0.22/0.45    spl3_7 <=> ! [X1,X0] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k2_tarski(X1,X0)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.45  fof(f64,plain,(
% 0.22/0.45    ( ! [X2,X3] : (k7_relat_1(k7_relat_1(sK2,X2),X3) = k7_relat_1(k7_relat_1(sK2,X3),X2)) ) | (~spl3_6 | ~spl3_7)),
% 0.22/0.45    inference(superposition,[],[f60,f54])).
% 0.22/0.45  fof(f54,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1)))) ) | ~spl3_6),
% 0.22/0.45    inference(avatar_component_clause,[],[f53])).
% 0.22/0.45  fof(f60,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k2_tarski(X1,X0)))) ) | ~spl3_7),
% 0.22/0.45    inference(avatar_component_clause,[],[f59])).
% 0.22/0.45  fof(f61,plain,(
% 0.22/0.45    spl3_7 | ~spl3_6),
% 0.22/0.45    inference(avatar_split_clause,[],[f56,f53,f59])).
% 0.22/0.45  fof(f56,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k2_tarski(X1,X0)))) ) | ~spl3_6),
% 0.22/0.45    inference(superposition,[],[f54,f17])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.45  fof(f55,plain,(
% 0.22/0.45    spl3_6 | ~spl3_1),
% 0.22/0.45    inference(avatar_split_clause,[],[f50,f23,f53])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    spl3_1 <=> v1_relat_1(sK2)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.45  fof(f50,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1)))) ) | ~spl3_1),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f25,f21])).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.22/0.45    inference(definition_unfolding,[],[f19,f18])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f2])).
% 0.22/0.45  fof(f2,axiom,(
% 0.22/0.45    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f9])).
% 0.22/0.45  fof(f9,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.45    inference(ennf_transformation,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 0.22/0.45  fof(f25,plain,(
% 0.22/0.45    v1_relat_1(sK2) | ~spl3_1),
% 0.22/0.45    inference(avatar_component_clause,[],[f23])).
% 0.22/0.45  fof(f43,plain,(
% 0.22/0.45    spl3_4 | ~spl3_1 | ~spl3_2),
% 0.22/0.45    inference(avatar_split_clause,[],[f37,f28,f23,f40])).
% 0.22/0.45  fof(f28,plain,(
% 0.22/0.45    spl3_2 <=> r1_tarski(sK0,sK1)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.45  fof(f37,plain,(
% 0.22/0.45    k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1) | (~spl3_1 | ~spl3_2)),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f25,f30,f20])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f11])).
% 0.22/0.45  fof(f11,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.45    inference(flattening,[],[f10])).
% 0.22/0.45  fof(f10,plain,(
% 0.22/0.45    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.45    inference(ennf_transformation,[],[f4])).
% 0.22/0.45  fof(f4,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).
% 0.22/0.45  fof(f30,plain,(
% 0.22/0.45    r1_tarski(sK0,sK1) | ~spl3_2),
% 0.22/0.45    inference(avatar_component_clause,[],[f28])).
% 0.22/0.45  fof(f36,plain,(
% 0.22/0.45    ~spl3_3),
% 0.22/0.45    inference(avatar_split_clause,[],[f16,f33])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f13])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f12])).
% 0.22/0.45  fof(f12,plain,(
% 0.22/0.45    ? [X0,X1,X2] : (k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f8,plain,(
% 0.22/0.45    ? [X0,X1,X2] : (k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.22/0.45    inference(flattening,[],[f7])).
% 0.22/0.45  fof(f7,plain,(
% 0.22/0.45    ? [X0,X1,X2] : ((k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.22/0.45    inference(ennf_transformation,[],[f6])).
% 0.22/0.45  fof(f6,negated_conjecture,(
% 0.22/0.45    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)))),
% 0.22/0.45    inference(negated_conjecture,[],[f5])).
% 0.22/0.45  fof(f5,conjecture,(
% 0.22/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).
% 0.22/0.45  fof(f31,plain,(
% 0.22/0.45    spl3_2),
% 0.22/0.45    inference(avatar_split_clause,[],[f15,f28])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    r1_tarski(sK0,sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f13])).
% 0.22/0.45  fof(f26,plain,(
% 0.22/0.45    spl3_1),
% 0.22/0.45    inference(avatar_split_clause,[],[f14,f23])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    v1_relat_1(sK2)),
% 0.22/0.45    inference(cnf_transformation,[],[f13])).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (16852)------------------------------
% 0.22/0.45  % (16852)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (16852)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (16852)Memory used [KB]: 10618
% 0.22/0.45  % (16852)Time elapsed: 0.007 s
% 0.22/0.45  % (16852)------------------------------
% 0.22/0.45  % (16852)------------------------------
% 0.22/0.45  % (16834)Success in time 0.083 s
%------------------------------------------------------------------------------
