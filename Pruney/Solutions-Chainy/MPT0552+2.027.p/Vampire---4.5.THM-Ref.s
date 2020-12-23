%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 148 expanded)
%              Number of leaves         :   17 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :  149 ( 280 expanded)
%              Number of equality atoms :   20 (  57 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f380,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f258,f265,f278,f286,f349,f369,f374])).

fof(f374,plain,
    ( ~ spl3_3
    | ~ spl3_14
    | spl3_12 ),
    inference(avatar_split_clause,[],[f370,f346,f359,f246])).

fof(f246,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f359,plain,
    ( spl3_14
  <=> v1_relat_1(k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f346,plain,
    ( spl3_12
  <=> r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK1),sK0)),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f370,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | spl3_12 ),
    inference(resolution,[],[f348,f36])).

fof(f36,plain,(
    ! [X4,X2,X3] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(X2,X3),X4)),k9_relat_1(X2,X3))
      | ~ v1_relat_1(k7_relat_1(X2,X3))
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f26,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).

fof(f348,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK1),sK0)),k9_relat_1(sK2,sK1))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f346])).

fof(f369,plain,(
    spl3_14 ),
    inference(avatar_contradiction_clause,[],[f368])).

fof(f368,plain,
    ( $false
    | spl3_14 ),
    inference(resolution,[],[f367,f20])).

fof(f20,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).

fof(f367,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_14 ),
    inference(resolution,[],[f361,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f361,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f359])).

fof(f349,plain,
    ( ~ spl3_3
    | ~ spl3_12
    | spl3_2 ),
    inference(avatar_split_clause,[],[f329,f47,f346,f246])).

fof(f47,plain,
    ( spl3_2
  <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f329,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK1),sK0)),k9_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | spl3_2 ),
    inference(superposition,[],[f49,f108])).

fof(f108,plain,(
    ! [X10,X11,X9] :
      ( k9_relat_1(X9,k1_setfam_1(k1_enumset1(X10,X10,X11))) = k2_relat_1(k7_relat_1(k7_relat_1(X9,X11),X10))
      | ~ v1_relat_1(X9) ) ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,(
    ! [X10,X11,X9] :
      ( k9_relat_1(X9,k1_setfam_1(k1_enumset1(X10,X10,X11))) = k2_relat_1(k7_relat_1(k7_relat_1(X9,X11),X10))
      | ~ v1_relat_1(X9)
      | ~ v1_relat_1(X9) ) ),
    inference(superposition,[],[f27,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k1_enumset1(X1,X1,X0)))
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f33,f32])).

fof(f32,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f22,f23,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f28,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f24,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

% (26658)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f49,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k9_relat_1(sK2,sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f286,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f285])).

fof(f285,plain,
    ( $false
    | spl3_7 ),
    inference(resolution,[],[f284,f20])).

fof(f284,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_7 ),
    inference(resolution,[],[f270,f25])).

fof(f270,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f268])).

fof(f268,plain,
    ( spl3_7
  <=> v1_relat_1(k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f278,plain,
    ( ~ spl3_3
    | ~ spl3_7
    | spl3_5 ),
    inference(avatar_split_clause,[],[f276,f255,f268,f246])).

fof(f255,plain,
    ( spl3_5
  <=> r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k9_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f276,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(sK2)
    | spl3_5 ),
    inference(resolution,[],[f257,f36])).

fof(f257,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k9_relat_1(sK2,sK0))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f255])).

fof(f265,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f264])).

fof(f264,plain,
    ( $false
    | spl3_3 ),
    inference(resolution,[],[f248,f20])).

fof(f248,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f246])).

fof(f258,plain,
    ( ~ spl3_3
    | ~ spl3_5
    | spl3_1 ),
    inference(avatar_split_clause,[],[f236,f43,f255,f246])).

fof(f43,plain,
    ( spl3_1
  <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k9_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f236,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k9_relat_1(sK2,sK0))
    | ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(superposition,[],[f45,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) = k2_relat_1(k7_relat_1(k7_relat_1(X0,X1),X2))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) = k2_relat_1(k7_relat_1(k7_relat_1(X0,X1),X2))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f27,f33])).

fof(f45,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k9_relat_1(sK2,sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f50,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f41,f47,f43])).

fof(f41,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k9_relat_1(sK2,sK1))
    | ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k9_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f31,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f30])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f31,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) ),
    inference(definition_unfolding,[],[f21,f30,f30])).

fof(f21,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:11:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.45  % (26663)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.46  % (26650)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (26655)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.46  % (26651)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (26646)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (26647)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (26650)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (26654)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (26652)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f380,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f50,f258,f265,f278,f286,f349,f369,f374])).
% 0.21/0.48  fof(f374,plain,(
% 0.21/0.48    ~spl3_3 | ~spl3_14 | spl3_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f370,f346,f359,f246])).
% 0.21/0.48  fof(f246,plain,(
% 0.21/0.48    spl3_3 <=> v1_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.48  fof(f359,plain,(
% 0.21/0.48    spl3_14 <=> v1_relat_1(k7_relat_1(sK2,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.48  fof(f346,plain,(
% 0.21/0.48    spl3_12 <=> r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK1),sK0)),k9_relat_1(sK2,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.48  fof(f370,plain,(
% 0.21/0.48    ~v1_relat_1(k7_relat_1(sK2,sK1)) | ~v1_relat_1(sK2) | spl3_12),
% 0.21/0.48    inference(resolution,[],[f348,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X4,X2,X3] : (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(X2,X3),X4)),k9_relat_1(X2,X3)) | ~v1_relat_1(k7_relat_1(X2,X3)) | ~v1_relat_1(X2)) )),
% 0.21/0.48    inference(superposition,[],[f26,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).
% 0.21/0.48  fof(f348,plain,(
% 0.21/0.48    ~r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK1),sK0)),k9_relat_1(sK2,sK1)) | spl3_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f346])).
% 0.21/0.48  fof(f369,plain,(
% 0.21/0.48    spl3_14),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f368])).
% 0.21/0.48  fof(f368,plain,(
% 0.21/0.48    $false | spl3_14),
% 0.21/0.48    inference(resolution,[],[f367,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    v1_relat_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) & v1_relat_1(sK2)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) & v1_relat_1(sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.21/0.48    inference(negated_conjecture,[],[f9])).
% 0.21/0.48  fof(f9,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).
% 0.21/0.48  fof(f367,plain,(
% 0.21/0.48    ~v1_relat_1(sK2) | spl3_14),
% 0.21/0.48    inference(resolution,[],[f361,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.48  fof(f361,plain,(
% 0.21/0.48    ~v1_relat_1(k7_relat_1(sK2,sK1)) | spl3_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f359])).
% 0.21/0.48  fof(f349,plain,(
% 0.21/0.48    ~spl3_3 | ~spl3_12 | spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f329,f47,f346,f246])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    spl3_2 <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k9_relat_1(sK2,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.48  fof(f329,plain,(
% 0.21/0.48    ~r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK1),sK0)),k9_relat_1(sK2,sK1)) | ~v1_relat_1(sK2) | spl3_2),
% 0.21/0.48    inference(superposition,[],[f49,f108])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    ( ! [X10,X11,X9] : (k9_relat_1(X9,k1_setfam_1(k1_enumset1(X10,X10,X11))) = k2_relat_1(k7_relat_1(k7_relat_1(X9,X11),X10)) | ~v1_relat_1(X9)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f88])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    ( ! [X10,X11,X9] : (k9_relat_1(X9,k1_setfam_1(k1_enumset1(X10,X10,X11))) = k2_relat_1(k7_relat_1(k7_relat_1(X9,X11),X10)) | ~v1_relat_1(X9) | ~v1_relat_1(X9)) )),
% 0.21/0.48    inference(superposition,[],[f27,f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k1_enumset1(X1,X1,X0))) | ~v1_relat_1(X2)) )),
% 0.21/0.48    inference(superposition,[],[f33,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f22,f23,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1))) | ~v1_relat_1(X2)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f28,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f24,f23])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.48  % (26658)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k9_relat_1(sK2,sK1)) | spl3_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f47])).
% 0.21/0.48  fof(f286,plain,(
% 0.21/0.48    spl3_7),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f285])).
% 0.21/0.48  fof(f285,plain,(
% 0.21/0.48    $false | spl3_7),
% 0.21/0.48    inference(resolution,[],[f284,f20])).
% 0.21/0.48  fof(f284,plain,(
% 0.21/0.48    ~v1_relat_1(sK2) | spl3_7),
% 0.21/0.48    inference(resolution,[],[f270,f25])).
% 0.21/0.48  fof(f270,plain,(
% 0.21/0.48    ~v1_relat_1(k7_relat_1(sK2,sK0)) | spl3_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f268])).
% 0.21/0.48  fof(f268,plain,(
% 0.21/0.48    spl3_7 <=> v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.48  fof(f278,plain,(
% 0.21/0.48    ~spl3_3 | ~spl3_7 | spl3_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f276,f255,f268,f246])).
% 0.21/0.48  fof(f255,plain,(
% 0.21/0.48    spl3_5 <=> r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k9_relat_1(sK2,sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.48  fof(f276,plain,(
% 0.21/0.48    ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(sK2) | spl3_5),
% 0.21/0.48    inference(resolution,[],[f257,f36])).
% 0.21/0.48  fof(f257,plain,(
% 0.21/0.48    ~r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k9_relat_1(sK2,sK0)) | spl3_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f255])).
% 0.21/0.48  fof(f265,plain,(
% 0.21/0.48    spl3_3),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f264])).
% 0.21/0.48  fof(f264,plain,(
% 0.21/0.48    $false | spl3_3),
% 0.21/0.48    inference(resolution,[],[f248,f20])).
% 0.21/0.48  fof(f248,plain,(
% 0.21/0.48    ~v1_relat_1(sK2) | spl3_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f246])).
% 0.21/0.48  fof(f258,plain,(
% 0.21/0.48    ~spl3_3 | ~spl3_5 | spl3_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f236,f43,f255,f246])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    spl3_1 <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k9_relat_1(sK2,sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f236,plain,(
% 0.21/0.48    ~r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k9_relat_1(sK2,sK0)) | ~v1_relat_1(sK2) | spl3_1),
% 0.21/0.48    inference(superposition,[],[f45,f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k9_relat_1(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) = k2_relat_1(k7_relat_1(k7_relat_1(X0,X1),X2)) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k9_relat_1(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) = k2_relat_1(k7_relat_1(k7_relat_1(X0,X1),X2)) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(superposition,[],[f27,f33])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k9_relat_1(sK2,sK0)) | spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f43])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ~spl3_1 | ~spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f41,f47,f43])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k9_relat_1(sK2,sK1)) | ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k9_relat_1(sK2,sK0))),
% 0.21/0.48    inference(resolution,[],[f31,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f29,f30])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))))),
% 0.21/0.48    inference(definition_unfolding,[],[f21,f30,f30])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (26650)------------------------------
% 0.21/0.48  % (26650)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (26650)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (26650)Memory used [KB]: 6268
% 0.21/0.48  % (26650)Time elapsed: 0.050 s
% 0.21/0.48  % (26650)------------------------------
% 0.21/0.48  % (26650)------------------------------
% 0.21/0.48  % (26659)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (26656)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (26645)Success in time 0.124 s
%------------------------------------------------------------------------------
