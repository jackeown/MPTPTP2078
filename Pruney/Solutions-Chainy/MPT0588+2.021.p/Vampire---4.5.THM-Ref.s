%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:58 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 128 expanded)
%              Number of leaves         :   20 (  51 expanded)
%              Depth                    :    8
%              Number of atoms          :  153 ( 246 expanded)
%              Number of equality atoms :   48 (  96 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f119,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f46,f50,f54,f61,f65,f71,f99,f105,f115])).

fof(f115,plain,
    ( spl2_5
    | ~ spl2_7
    | ~ spl2_13 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | spl2_5
    | ~ spl2_7
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f108,f70])).

fof(f70,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(sK1))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl2_7
  <=> ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f108,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1))
    | spl2_5
    | ~ spl2_13 ),
    inference(superposition,[],[f60,f104])).

fof(f104,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK1,X0),X1) = k7_relat_1(sK1,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl2_13
  <=> ! [X1,X0] : k7_relat_1(k7_relat_1(sK1,X0),X1) = k7_relat_1(sK1,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f60,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k1_relat_1(sK1))))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl2_5
  <=> k7_relat_1(sK1,sK0) = k7_relat_1(sK1,k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k1_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f105,plain,
    ( spl2_13
    | ~ spl2_1
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f100,f97,f39,f103])).

fof(f39,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f97,plain,
    ( spl2_12
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f100,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK1,X0),X1) = k7_relat_1(sK1,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)))
    | ~ spl2_1
    | ~ spl2_12 ),
    inference(resolution,[],[f98,f41])).

fof(f41,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f98,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f97])).

fof(f99,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f36,f97])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f29,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f23,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f24,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f28,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f24,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f71,plain,
    ( spl2_7
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f66,f63,f39,f69])).

fof(f63,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( k7_relat_1(X0,X1) = k7_relat_1(k7_relat_1(X0,X1),k1_relat_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f66,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(resolution,[],[f64,f41])).

fof(f64,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k7_relat_1(X0,X1) = k7_relat_1(k7_relat_1(X0,X1),k1_relat_1(X0)) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f63])).

fof(f65,plain,
    ( spl2_6
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f56,f52,f48,f44,f63])).

fof(f44,plain,
    ( spl2_2
  <=> ! [X1,X0] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f48,plain,
    ( spl2_3
  <=> ! [X1,X0] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f52,plain,
    ( spl2_4
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = X1
        | ~ r1_tarski(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f56,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(X0,X1) = k7_relat_1(k7_relat_1(X0,X1),k1_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f55,f45])).

fof(f45,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f55,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(X0,X1) = k7_relat_1(k7_relat_1(X0,X1),k1_relat_1(X0))
        | ~ v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(resolution,[],[f53,f49])).

fof(f49,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f53,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(X1),X0)
        | k7_relat_1(X1,X0) = X1
        | ~ v1_relat_1(X1) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f52])).

fof(f61,plain,(
    ~ spl2_5 ),
    inference(avatar_split_clause,[],[f37,f58])).

fof(f37,plain,(
    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k1_relat_1(sK1)))) ),
    inference(backward_demodulation,[],[f34,f35])).

fof(f35,plain,(
    ! [X0,X1] : k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f22,f33,f33])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f34,plain,(
    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k3_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0))) ),
    inference(definition_unfolding,[],[f21,f33])).

fof(f21,plain,(
    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
        & v1_relat_1(X1) )
   => ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

fof(f54,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f27,f52])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f50,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f26,f48])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

fof(f46,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f25,f44])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f42,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f20,f39])).

fof(f20,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:52:24 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.45  % (7352)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.46  % (7360)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.46  % (7352)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.46  fof(f119,plain,(
% 0.22/0.46    $false),
% 0.22/0.46    inference(avatar_sat_refutation,[],[f42,f46,f50,f54,f61,f65,f71,f99,f105,f115])).
% 0.22/0.46  fof(f115,plain,(
% 0.22/0.46    spl2_5 | ~spl2_7 | ~spl2_13),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f114])).
% 0.22/0.46  fof(f114,plain,(
% 0.22/0.46    $false | (spl2_5 | ~spl2_7 | ~spl2_13)),
% 0.22/0.46    inference(subsumption_resolution,[],[f108,f70])).
% 0.22/0.46  fof(f70,plain,(
% 0.22/0.46    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(sK1))) ) | ~spl2_7),
% 0.22/0.46    inference(avatar_component_clause,[],[f69])).
% 0.22/0.46  fof(f69,plain,(
% 0.22/0.46    spl2_7 <=> ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(sK1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.46  fof(f108,plain,(
% 0.22/0.46    k7_relat_1(sK1,sK0) != k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1)) | (spl2_5 | ~spl2_13)),
% 0.22/0.46    inference(superposition,[],[f60,f104])).
% 0.22/0.46  fof(f104,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK1,X0),X1) = k7_relat_1(sK1,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)))) ) | ~spl2_13),
% 0.22/0.46    inference(avatar_component_clause,[],[f103])).
% 0.22/0.46  fof(f103,plain,(
% 0.22/0.46    spl2_13 <=> ! [X1,X0] : k7_relat_1(k7_relat_1(sK1,X0),X1) = k7_relat_1(sK1,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.22/0.46  fof(f60,plain,(
% 0.22/0.46    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k1_relat_1(sK1)))) | spl2_5),
% 0.22/0.46    inference(avatar_component_clause,[],[f58])).
% 0.22/0.46  fof(f58,plain,(
% 0.22/0.46    spl2_5 <=> k7_relat_1(sK1,sK0) = k7_relat_1(sK1,k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k1_relat_1(sK1))))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.46  fof(f105,plain,(
% 0.22/0.46    spl2_13 | ~spl2_1 | ~spl2_12),
% 0.22/0.46    inference(avatar_split_clause,[],[f100,f97,f39,f103])).
% 0.22/0.46  fof(f39,plain,(
% 0.22/0.46    spl2_1 <=> v1_relat_1(sK1)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.46  fof(f97,plain,(
% 0.22/0.46    spl2_12 <=> ! [X1,X0,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) | ~v1_relat_1(X2))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.46  fof(f100,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK1,X0),X1) = k7_relat_1(sK1,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)))) ) | (~spl2_1 | ~spl2_12)),
% 0.22/0.46    inference(resolution,[],[f98,f41])).
% 0.22/0.46  fof(f41,plain,(
% 0.22/0.46    v1_relat_1(sK1) | ~spl2_1),
% 0.22/0.46    inference(avatar_component_clause,[],[f39])).
% 0.22/0.46  fof(f98,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)))) ) | ~spl2_12),
% 0.22/0.46    inference(avatar_component_clause,[],[f97])).
% 0.22/0.46  fof(f99,plain,(
% 0.22/0.46    spl2_12),
% 0.22/0.46    inference(avatar_split_clause,[],[f36,f97])).
% 0.22/0.46  fof(f36,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) | ~v1_relat_1(X2)) )),
% 0.22/0.46    inference(definition_unfolding,[],[f29,f33])).
% 0.22/0.46  fof(f33,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.22/0.46    inference(definition_unfolding,[],[f23,f32])).
% 0.22/0.46  fof(f32,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.22/0.46    inference(definition_unfolding,[],[f24,f31])).
% 0.22/0.46  fof(f31,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.22/0.46    inference(definition_unfolding,[],[f28,f30])).
% 0.22/0.46  fof(f30,plain,(
% 0.22/0.46    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f4])).
% 0.22/0.46  fof(f4,axiom,(
% 0.22/0.46    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.46  fof(f28,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f3])).
% 0.22/0.46  fof(f3,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.46  fof(f24,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.46  fof(f23,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f5])).
% 0.22/0.46  fof(f5,axiom,(
% 0.22/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.46  fof(f29,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f17])).
% 0.22/0.46  fof(f17,plain,(
% 0.22/0.46    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.46    inference(ennf_transformation,[],[f7])).
% 0.22/0.46  fof(f7,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 0.22/0.46  fof(f71,plain,(
% 0.22/0.46    spl2_7 | ~spl2_1 | ~spl2_6),
% 0.22/0.46    inference(avatar_split_clause,[],[f66,f63,f39,f69])).
% 0.22/0.46  fof(f63,plain,(
% 0.22/0.46    spl2_6 <=> ! [X1,X0] : (k7_relat_1(X0,X1) = k7_relat_1(k7_relat_1(X0,X1),k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.46  fof(f66,plain,(
% 0.22/0.46    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(sK1))) ) | (~spl2_1 | ~spl2_6)),
% 0.22/0.46    inference(resolution,[],[f64,f41])).
% 0.22/0.46  fof(f64,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~v1_relat_1(X0) | k7_relat_1(X0,X1) = k7_relat_1(k7_relat_1(X0,X1),k1_relat_1(X0))) ) | ~spl2_6),
% 0.22/0.46    inference(avatar_component_clause,[],[f63])).
% 0.22/0.46  fof(f65,plain,(
% 0.22/0.46    spl2_6 | ~spl2_2 | ~spl2_3 | ~spl2_4),
% 0.22/0.46    inference(avatar_split_clause,[],[f56,f52,f48,f44,f63])).
% 0.22/0.46  fof(f44,plain,(
% 0.22/0.46    spl2_2 <=> ! [X1,X0] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.46  fof(f48,plain,(
% 0.22/0.46    spl2_3 <=> ! [X1,X0] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.46  fof(f52,plain,(
% 0.22/0.46    spl2_4 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.46  fof(f56,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k7_relat_1(X0,X1) = k7_relat_1(k7_relat_1(X0,X1),k1_relat_1(X0)) | ~v1_relat_1(X0)) ) | (~spl2_2 | ~spl2_3 | ~spl2_4)),
% 0.22/0.46    inference(subsumption_resolution,[],[f55,f45])).
% 0.22/0.46  fof(f45,plain,(
% 0.22/0.46    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl2_2),
% 0.22/0.46    inference(avatar_component_clause,[],[f44])).
% 0.22/0.46  fof(f55,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k7_relat_1(X0,X1) = k7_relat_1(k7_relat_1(X0,X1),k1_relat_1(X0)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | (~spl2_3 | ~spl2_4)),
% 0.22/0.46    inference(resolution,[],[f53,f49])).
% 0.22/0.46  fof(f49,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1)) ) | ~spl2_3),
% 0.22/0.46    inference(avatar_component_clause,[],[f48])).
% 0.22/0.46  fof(f53,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) ) | ~spl2_4),
% 0.22/0.46    inference(avatar_component_clause,[],[f52])).
% 0.22/0.46  fof(f61,plain,(
% 0.22/0.46    ~spl2_5),
% 0.22/0.46    inference(avatar_split_clause,[],[f37,f58])).
% 0.22/0.46  fof(f37,plain,(
% 0.22/0.46    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,k1_relat_1(sK1))))),
% 0.22/0.46    inference(backward_demodulation,[],[f34,f35])).
% 0.22/0.46  fof(f35,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X0))) )),
% 0.22/0.46    inference(definition_unfolding,[],[f22,f33,f33])).
% 0.22/0.46  fof(f22,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f1])).
% 0.22/0.46  fof(f1,axiom,(
% 0.22/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.46  fof(f34,plain,(
% 0.22/0.46    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k3_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0)))),
% 0.22/0.46    inference(definition_unfolding,[],[f21,f33])).
% 0.22/0.46  fof(f21,plain,(
% 0.22/0.46    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))),
% 0.22/0.46    inference(cnf_transformation,[],[f19])).
% 0.22/0.46  fof(f19,plain,(
% 0.22/0.46    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) & v1_relat_1(sK1)),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f18])).
% 0.22/0.46  fof(f18,plain,(
% 0.22/0.46    ? [X0,X1] : (k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1)) => (k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) & v1_relat_1(sK1))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f12,plain,(
% 0.22/0.46    ? [X0,X1] : (k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f11])).
% 0.22/0.46  fof(f11,negated_conjecture,(
% 0.22/0.46    ~! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.22/0.46    inference(negated_conjecture,[],[f10])).
% 0.22/0.46  fof(f10,conjecture,(
% 0.22/0.46    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).
% 0.22/0.46  fof(f54,plain,(
% 0.22/0.46    spl2_4),
% 0.22/0.46    inference(avatar_split_clause,[],[f27,f52])).
% 0.22/0.46  fof(f27,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f16])).
% 0.22/0.46  fof(f16,plain,(
% 0.22/0.46    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.46    inference(flattening,[],[f15])).
% 0.22/0.46  fof(f15,plain,(
% 0.22/0.46    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f9])).
% 0.22/0.46  fof(f9,axiom,(
% 0.22/0.46    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 0.22/0.46  fof(f50,plain,(
% 0.22/0.46    spl2_3),
% 0.22/0.46    inference(avatar_split_clause,[],[f26,f48])).
% 0.22/0.46  fof(f26,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f14])).
% 0.22/0.46  fof(f14,plain,(
% 0.22/0.46    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f8])).
% 0.22/0.46  fof(f8,axiom,(
% 0.22/0.46    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).
% 0.22/0.46  fof(f46,plain,(
% 0.22/0.46    spl2_2),
% 0.22/0.46    inference(avatar_split_clause,[],[f25,f44])).
% 0.22/0.46  fof(f25,plain,(
% 0.22/0.46    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f13])).
% 0.22/0.46  fof(f13,plain,(
% 0.22/0.46    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f6])).
% 0.22/0.46  fof(f6,axiom,(
% 0.22/0.46    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.22/0.46  fof(f42,plain,(
% 0.22/0.46    spl2_1),
% 0.22/0.46    inference(avatar_split_clause,[],[f20,f39])).
% 0.22/0.46  fof(f20,plain,(
% 0.22/0.46    v1_relat_1(sK1)),
% 0.22/0.46    inference(cnf_transformation,[],[f19])).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (7352)------------------------------
% 0.22/0.46  % (7352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (7352)Termination reason: Refutation
% 0.22/0.46  
% 0.22/0.46  % (7352)Memory used [KB]: 6140
% 0.22/0.46  % (7352)Time elapsed: 0.051 s
% 0.22/0.46  % (7352)------------------------------
% 0.22/0.46  % (7352)------------------------------
% 0.22/0.47  % (7344)Success in time 0.105 s
%------------------------------------------------------------------------------
