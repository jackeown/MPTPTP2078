%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:57 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 149 expanded)
%              Number of leaves         :   17 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  154 ( 263 expanded)
%              Number of equality atoms :   36 ( 103 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f152,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f104,f117,f130,f147,f151])).

fof(f151,plain,(
    spl2_8 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | spl2_8 ),
    inference(resolution,[],[f148,f24])).

fof(f24,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
        & v1_relat_1(X1) )
   => ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

fof(f148,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_8 ),
    inference(resolution,[],[f146,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f146,plain,
    ( ~ r1_tarski(k7_relat_1(sK1,sK0),sK1)
    | spl2_8 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl2_8
  <=> r1_tarski(k7_relat_1(sK1,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f147,plain,
    ( ~ spl2_6
    | ~ spl2_1
    | ~ spl2_8
    | spl2_7 ),
    inference(avatar_split_clause,[],[f141,f114,f144,f63,f110])).

fof(f110,plain,
    ( spl2_6
  <=> v1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f63,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f114,plain,
    ( spl2_7
  <=> r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f141,plain,
    ( ~ r1_tarski(k7_relat_1(sK1,sK0),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl2_7 ),
    inference(resolution,[],[f116,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f116,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(sK1))
    | spl2_7 ),
    inference(avatar_component_clause,[],[f114])).

fof(f130,plain,(
    spl2_6 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | spl2_6 ),
    inference(resolution,[],[f126,f24])).

fof(f126,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_6 ),
    inference(resolution,[],[f112,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f52,f32])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | v1_relat_1(X0) ) ),
    inference(superposition,[],[f46,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f38])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f30,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f29,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f41,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f28,f37,f37])).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f31,f38])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f112,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f110])).

fof(f117,plain,
    ( ~ spl2_6
    | ~ spl2_7
    | spl2_5 ),
    inference(avatar_split_clause,[],[f108,f101,f114,f110])).

fof(f101,plain,
    ( spl2_5
  <=> k7_relat_1(sK1,sK0) = k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f108,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(sK1))
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl2_5 ),
    inference(trivial_inequality_removal,[],[f107])).

fof(f107,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,sK0)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(sK1))
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl2_5 ),
    inference(superposition,[],[f103,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f103,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f104,plain,
    ( ~ spl2_1
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f95,f101,f63])).

fof(f95,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f58,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f36,f38])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(f58,plain,(
    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k1_relat_1(sK1)))) ),
    inference(forward_demodulation,[],[f39,f40])).

fof(f39,plain,(
    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0))) ),
    inference(definition_unfolding,[],[f25,f38])).

fof(f25,plain,(
    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f79,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f78])).

fof(f78,plain,
    ( $false
    | spl2_1 ),
    inference(resolution,[],[f65,f24])).

fof(f65,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f63])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:13:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.40  % (32120)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.41  % (32120)Refutation found. Thanks to Tanya!
% 0.19/0.41  % SZS status Theorem for theBenchmark
% 0.19/0.41  % (32128)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.19/0.41  % SZS output start Proof for theBenchmark
% 0.19/0.41  fof(f152,plain,(
% 0.19/0.41    $false),
% 0.19/0.41    inference(avatar_sat_refutation,[],[f79,f104,f117,f130,f147,f151])).
% 0.19/0.41  fof(f151,plain,(
% 0.19/0.41    spl2_8),
% 0.19/0.41    inference(avatar_contradiction_clause,[],[f150])).
% 0.19/0.41  fof(f150,plain,(
% 0.19/0.41    $false | spl2_8),
% 0.19/0.41    inference(resolution,[],[f148,f24])).
% 0.19/0.41  fof(f24,plain,(
% 0.19/0.41    v1_relat_1(sK1)),
% 0.19/0.41    inference(cnf_transformation,[],[f23])).
% 0.19/0.41  fof(f23,plain,(
% 0.19/0.41    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) & v1_relat_1(sK1)),
% 0.19/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f22])).
% 0.19/0.41  fof(f22,plain,(
% 0.19/0.41    ? [X0,X1] : (k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1)) => (k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) & v1_relat_1(sK1))),
% 0.19/0.41    introduced(choice_axiom,[])).
% 0.19/0.41  fof(f13,plain,(
% 0.19/0.41    ? [X0,X1] : (k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.19/0.41    inference(ennf_transformation,[],[f12])).
% 0.19/0.41  fof(f12,negated_conjecture,(
% 0.19/0.41    ~! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.19/0.41    inference(negated_conjecture,[],[f11])).
% 0.19/0.41  fof(f11,conjecture,(
% 0.19/0.41    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).
% 0.19/0.41  fof(f148,plain,(
% 0.19/0.41    ~v1_relat_1(sK1) | spl2_8),
% 0.19/0.41    inference(resolution,[],[f146,f32])).
% 0.19/0.41  fof(f32,plain,(
% 0.19/0.41    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f17])).
% 0.19/0.41  fof(f17,plain,(
% 0.19/0.41    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.19/0.41    inference(ennf_transformation,[],[f9])).
% 0.19/0.41  fof(f9,axiom,(
% 0.19/0.41    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 0.19/0.41  fof(f146,plain,(
% 0.19/0.41    ~r1_tarski(k7_relat_1(sK1,sK0),sK1) | spl2_8),
% 0.19/0.41    inference(avatar_component_clause,[],[f144])).
% 0.19/0.41  fof(f144,plain,(
% 0.19/0.41    spl2_8 <=> r1_tarski(k7_relat_1(sK1,sK0),sK1)),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.19/0.41  fof(f147,plain,(
% 0.19/0.41    ~spl2_6 | ~spl2_1 | ~spl2_8 | spl2_7),
% 0.19/0.41    inference(avatar_split_clause,[],[f141,f114,f144,f63,f110])).
% 0.19/0.41  fof(f110,plain,(
% 0.19/0.41    spl2_6 <=> v1_relat_1(k7_relat_1(sK1,sK0))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.19/0.41  fof(f63,plain,(
% 0.19/0.41    spl2_1 <=> v1_relat_1(sK1)),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.19/0.41  fof(f114,plain,(
% 0.19/0.41    spl2_7 <=> r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(sK1))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.19/0.41  fof(f141,plain,(
% 0.19/0.41    ~r1_tarski(k7_relat_1(sK1,sK0),sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(k7_relat_1(sK1,sK0)) | spl2_7),
% 0.19/0.41    inference(resolution,[],[f116,f26])).
% 0.19/0.41  fof(f26,plain,(
% 0.19/0.41    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f15])).
% 0.19/0.41  fof(f15,plain,(
% 0.19/0.41    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.41    inference(flattening,[],[f14])).
% 0.19/0.41  fof(f14,plain,(
% 0.19/0.41    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.41    inference(ennf_transformation,[],[f8])).
% 0.19/0.41  fof(f8,axiom,(
% 0.19/0.41    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.19/0.41  fof(f116,plain,(
% 0.19/0.41    ~r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(sK1)) | spl2_7),
% 0.19/0.41    inference(avatar_component_clause,[],[f114])).
% 0.19/0.41  fof(f130,plain,(
% 0.19/0.41    spl2_6),
% 0.19/0.41    inference(avatar_contradiction_clause,[],[f129])).
% 0.19/0.41  fof(f129,plain,(
% 0.19/0.41    $false | spl2_6),
% 0.19/0.41    inference(resolution,[],[f126,f24])).
% 0.19/0.41  fof(f126,plain,(
% 0.19/0.41    ~v1_relat_1(sK1) | spl2_6),
% 0.19/0.41    inference(resolution,[],[f112,f55])).
% 0.19/0.41  fof(f55,plain,(
% 0.19/0.41    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.19/0.41    inference(duplicate_literal_removal,[],[f54])).
% 0.19/0.41  fof(f54,plain,(
% 0.19/0.41    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.19/0.41    inference(resolution,[],[f52,f32])).
% 0.19/0.41  fof(f52,plain,(
% 0.19/0.41    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | v1_relat_1(X0)) )),
% 0.19/0.41    inference(superposition,[],[f46,f42])).
% 0.19/0.41  fof(f42,plain,(
% 0.19/0.41    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 0.19/0.41    inference(definition_unfolding,[],[f34,f38])).
% 0.19/0.42  fof(f38,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.19/0.42    inference(definition_unfolding,[],[f30,f37])).
% 0.19/0.42  fof(f37,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.19/0.42    inference(definition_unfolding,[],[f29,f35])).
% 0.19/0.42  fof(f35,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f4])).
% 0.19/0.42  fof(f4,axiom,(
% 0.19/0.42    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.19/0.42  fof(f29,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f3])).
% 0.19/0.42  fof(f3,axiom,(
% 0.19/0.42    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.19/0.42  fof(f30,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.19/0.42    inference(cnf_transformation,[],[f5])).
% 0.19/0.42  fof(f5,axiom,(
% 0.19/0.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.19/0.42  fof(f34,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f20])).
% 0.19/0.42  fof(f20,plain,(
% 0.19/0.42    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.19/0.42    inference(ennf_transformation,[],[f1])).
% 0.19/0.42  fof(f1,axiom,(
% 0.19/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.19/0.42  fof(f46,plain,(
% 0.19/0.42    ( ! [X0,X1] : (v1_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) | ~v1_relat_1(X0)) )),
% 0.19/0.42    inference(superposition,[],[f41,f40])).
% 0.19/0.42  fof(f40,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 0.19/0.42    inference(definition_unfolding,[],[f28,f37,f37])).
% 0.19/0.42  fof(f28,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f2])).
% 0.19/0.42  fof(f2,axiom,(
% 0.19/0.42    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.19/0.42  fof(f41,plain,(
% 0.19/0.42    ( ! [X0,X1] : (v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X0)) )),
% 0.19/0.42    inference(definition_unfolding,[],[f31,f38])).
% 0.19/0.42  fof(f31,plain,(
% 0.19/0.42    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f16])).
% 0.19/0.42  fof(f16,plain,(
% 0.19/0.42    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.19/0.42    inference(ennf_transformation,[],[f6])).
% 0.19/0.42  fof(f6,axiom,(
% 0.19/0.42    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).
% 0.19/0.42  fof(f112,plain,(
% 0.19/0.42    ~v1_relat_1(k7_relat_1(sK1,sK0)) | spl2_6),
% 0.19/0.42    inference(avatar_component_clause,[],[f110])).
% 0.19/0.42  fof(f117,plain,(
% 0.19/0.42    ~spl2_6 | ~spl2_7 | spl2_5),
% 0.19/0.42    inference(avatar_split_clause,[],[f108,f101,f114,f110])).
% 0.19/0.42  fof(f101,plain,(
% 0.19/0.42    spl2_5 <=> k7_relat_1(sK1,sK0) = k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.19/0.42  fof(f108,plain,(
% 0.19/0.42    ~r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(sK1)) | ~v1_relat_1(k7_relat_1(sK1,sK0)) | spl2_5),
% 0.19/0.42    inference(trivial_inequality_removal,[],[f107])).
% 0.19/0.42  fof(f107,plain,(
% 0.19/0.42    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,sK0) | ~r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(sK1)) | ~v1_relat_1(k7_relat_1(sK1,sK0)) | spl2_5),
% 0.19/0.42    inference(superposition,[],[f103,f33])).
% 0.19/0.42  fof(f33,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f19])).
% 0.19/0.42  fof(f19,plain,(
% 0.19/0.42    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.19/0.42    inference(flattening,[],[f18])).
% 0.19/0.42  fof(f18,plain,(
% 0.19/0.42    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.42    inference(ennf_transformation,[],[f10])).
% 0.19/0.42  fof(f10,axiom,(
% 0.19/0.42    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 0.19/0.42  fof(f103,plain,(
% 0.19/0.42    k7_relat_1(sK1,sK0) != k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1)) | spl2_5),
% 0.19/0.42    inference(avatar_component_clause,[],[f101])).
% 0.19/0.42  fof(f104,plain,(
% 0.19/0.42    ~spl2_1 | ~spl2_5),
% 0.19/0.42    inference(avatar_split_clause,[],[f95,f101,f63])).
% 0.19/0.42  fof(f95,plain,(
% 0.19/0.42    k7_relat_1(sK1,sK0) != k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 0.19/0.42    inference(superposition,[],[f58,f43])).
% 0.19/0.42  fof(f43,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X2)) )),
% 0.19/0.42    inference(definition_unfolding,[],[f36,f38])).
% 0.19/0.42  fof(f36,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f21])).
% 0.19/0.42  fof(f21,plain,(
% 0.19/0.42    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.19/0.42    inference(ennf_transformation,[],[f7])).
% 0.19/0.42  fof(f7,axiom,(
% 0.19/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).
% 0.19/0.42  fof(f58,plain,(
% 0.19/0.42    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k1_relat_1(sK1))))),
% 0.19/0.42    inference(forward_demodulation,[],[f39,f40])).
% 0.19/0.42  fof(f39,plain,(
% 0.19/0.42    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0)))),
% 0.19/0.42    inference(definition_unfolding,[],[f25,f38])).
% 0.19/0.42  fof(f25,plain,(
% 0.19/0.42    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))),
% 0.19/0.42    inference(cnf_transformation,[],[f23])).
% 0.19/0.42  fof(f79,plain,(
% 0.19/0.42    spl2_1),
% 0.19/0.42    inference(avatar_contradiction_clause,[],[f78])).
% 0.19/0.42  fof(f78,plain,(
% 0.19/0.42    $false | spl2_1),
% 0.19/0.42    inference(resolution,[],[f65,f24])).
% 0.19/0.42  fof(f65,plain,(
% 0.19/0.42    ~v1_relat_1(sK1) | spl2_1),
% 0.19/0.42    inference(avatar_component_clause,[],[f63])).
% 0.19/0.42  % SZS output end Proof for theBenchmark
% 0.19/0.42  % (32120)------------------------------
% 0.19/0.42  % (32120)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.42  % (32120)Termination reason: Refutation
% 0.19/0.42  
% 0.19/0.42  % (32120)Memory used [KB]: 6140
% 0.19/0.42  % (32120)Time elapsed: 0.040 s
% 0.19/0.42  % (32120)------------------------------
% 0.19/0.42  % (32120)------------------------------
% 0.19/0.42  % (32111)Success in time 0.07 s
%------------------------------------------------------------------------------
