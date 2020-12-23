%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:18 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 148 expanded)
%              Number of leaves         :   19 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :  160 ( 304 expanded)
%              Number of equality atoms :   11 (  46 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f116,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f83,f87,f89,f91,f111,f113,f115])).

fof(f115,plain,(
    spl2_9 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | spl2_9 ),
    inference(resolution,[],[f110,f47])).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X0)),X0) ),
    inference(superposition,[],[f45,f37])).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f28,f29,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f45,plain,(
    ! [X2,X3] : r1_tarski(k1_setfam_1(k1_enumset1(X2,X2,X3)),X2) ),
    inference(superposition,[],[f27,f38])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f31,f35])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f30,f29])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f110,plain,
    ( ~ r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK1)
    | spl2_9 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl2_9
  <=> r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f113,plain,(
    spl2_8 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | spl2_8 ),
    inference(resolution,[],[f106,f23])).

fof(f23,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relat_1)).

fof(f106,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_8 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl2_8
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f111,plain,
    ( ~ spl2_3
    | ~ spl2_8
    | ~ spl2_9
    | spl2_2 ),
    inference(avatar_split_clause,[],[f93,f66,f108,f104,f72])).

fof(f72,plain,
    ( spl2_3
  <=> v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f66,plain,
    ( spl2_2
  <=> r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f93,plain,
    ( ~ r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))
    | spl2_2 ),
    inference(resolution,[],[f68,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(f68,plain,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k3_relat_1(sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f91,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f90])).

fof(f90,plain,
    ( $false
    | spl2_5 ),
    inference(resolution,[],[f82,f45])).

fof(f82,plain,
    ( ~ r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl2_5
  <=> r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f89,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | spl2_4 ),
    inference(resolution,[],[f78,f22])).

fof(f22,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f78,plain,
    ( ~ v1_relat_1(sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl2_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f87,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f86])).

fof(f86,plain,
    ( $false
    | spl2_3 ),
    inference(resolution,[],[f85,f22])).

fof(f85,plain,
    ( ~ v1_relat_1(sK0)
    | spl2_3 ),
    inference(resolution,[],[f74,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f45,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f26,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f74,plain,
    ( ~ v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f83,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | spl2_1 ),
    inference(avatar_split_clause,[],[f70,f62,f80,f76,f72])).

fof(f62,plain,
    ( spl2_1
  <=> r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f70,plain,
    ( ~ r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))
    | spl2_1 ),
    inference(resolution,[],[f64,f25])).

fof(f64,plain,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k3_relat_1(sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f69,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f58,f66,f62])).

fof(f58,plain,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k3_relat_1(sK1))
    | ~ r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k3_relat_1(sK0)) ),
    inference(resolution,[],[f39,f36])).

fof(f36,plain,(
    ~ r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK1)))) ),
    inference(definition_unfolding,[],[f24,f35,f35])).

fof(f24,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 11:53:41 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.21/0.43  % (24062)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.23/0.46  % (24056)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.23/0.46  % (24056)Refutation not found, incomplete strategy% (24056)------------------------------
% 0.23/0.46  % (24056)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.46  % (24056)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.46  
% 0.23/0.46  % (24056)Memory used [KB]: 10618
% 0.23/0.46  % (24056)Time elapsed: 0.005 s
% 0.23/0.46  % (24056)------------------------------
% 0.23/0.46  % (24056)------------------------------
% 0.23/0.47  % (24047)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.23/0.48  % (24047)Refutation found. Thanks to Tanya!
% 0.23/0.48  % SZS status Theorem for theBenchmark
% 0.23/0.48  % SZS output start Proof for theBenchmark
% 0.23/0.48  fof(f116,plain,(
% 0.23/0.48    $false),
% 0.23/0.48    inference(avatar_sat_refutation,[],[f69,f83,f87,f89,f91,f111,f113,f115])).
% 0.23/0.48  fof(f115,plain,(
% 0.23/0.48    spl2_9),
% 0.23/0.48    inference(avatar_contradiction_clause,[],[f114])).
% 0.23/0.48  fof(f114,plain,(
% 0.23/0.48    $false | spl2_9),
% 0.23/0.48    inference(resolution,[],[f110,f47])).
% 0.23/0.48  fof(f47,plain,(
% 0.23/0.48    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X0)),X0)) )),
% 0.23/0.48    inference(superposition,[],[f45,f37])).
% 0.23/0.48  fof(f37,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 0.23/0.48    inference(definition_unfolding,[],[f28,f29,f29])).
% 0.23/0.48  fof(f29,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f5])).
% 0.23/0.48  fof(f5,axiom,(
% 0.23/0.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.23/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.23/0.48  fof(f28,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f4])).
% 0.23/0.48  fof(f4,axiom,(
% 0.23/0.48    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.23/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.23/0.48  fof(f45,plain,(
% 0.23/0.48    ( ! [X2,X3] : (r1_tarski(k1_setfam_1(k1_enumset1(X2,X2,X3)),X2)) )),
% 0.23/0.48    inference(superposition,[],[f27,f38])).
% 0.23/0.48  fof(f38,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.23/0.48    inference(definition_unfolding,[],[f31,f35])).
% 0.23/0.48  fof(f35,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.23/0.48    inference(definition_unfolding,[],[f30,f29])).
% 0.23/0.48  fof(f30,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.23/0.48    inference(cnf_transformation,[],[f6])).
% 0.23/0.48  fof(f6,axiom,(
% 0.23/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.23/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.23/0.48  fof(f31,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f3])).
% 0.23/0.48  fof(f3,axiom,(
% 0.23/0.48    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.23/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.23/0.48  fof(f27,plain,(
% 0.23/0.48    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f2])).
% 0.23/0.48  fof(f2,axiom,(
% 0.23/0.48    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.23/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.23/0.48  fof(f110,plain,(
% 0.23/0.48    ~r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK1) | spl2_9),
% 0.23/0.48    inference(avatar_component_clause,[],[f108])).
% 0.23/0.48  fof(f108,plain,(
% 0.23/0.48    spl2_9 <=> r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK1)),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.23/0.48  fof(f113,plain,(
% 0.23/0.48    spl2_8),
% 0.23/0.48    inference(avatar_contradiction_clause,[],[f112])).
% 0.23/0.48  fof(f112,plain,(
% 0.23/0.48    $false | spl2_8),
% 0.23/0.48    inference(resolution,[],[f106,f23])).
% 0.23/0.48  fof(f23,plain,(
% 0.23/0.48    v1_relat_1(sK1)),
% 0.23/0.48    inference(cnf_transformation,[],[f20])).
% 0.23/0.48  fof(f20,plain,(
% 0.23/0.48    (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.23/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f19,f18])).
% 0.23/0.48  fof(f18,plain,(
% 0.23/0.48    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.23/0.48    introduced(choice_axiom,[])).
% 0.23/0.48  fof(f19,plain,(
% 0.23/0.48    ? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.23/0.48    introduced(choice_axiom,[])).
% 0.23/0.48  fof(f12,plain,(
% 0.23/0.48    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.23/0.48    inference(ennf_transformation,[],[f11])).
% 0.23/0.48  fof(f11,negated_conjecture,(
% 0.23/0.48    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.23/0.48    inference(negated_conjecture,[],[f10])).
% 0.23/0.48  fof(f10,conjecture,(
% 0.23/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.23/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relat_1)).
% 0.23/0.48  fof(f106,plain,(
% 0.23/0.48    ~v1_relat_1(sK1) | spl2_8),
% 0.23/0.48    inference(avatar_component_clause,[],[f104])).
% 0.23/0.48  fof(f104,plain,(
% 0.23/0.48    spl2_8 <=> v1_relat_1(sK1)),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.23/0.48  fof(f111,plain,(
% 0.23/0.48    ~spl2_3 | ~spl2_8 | ~spl2_9 | spl2_2),
% 0.23/0.48    inference(avatar_split_clause,[],[f93,f66,f108,f104,f72])).
% 0.23/0.48  fof(f72,plain,(
% 0.23/0.48    spl2_3 <=> v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.23/0.48  fof(f66,plain,(
% 0.23/0.48    spl2_2 <=> r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k3_relat_1(sK1))),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.23/0.48  fof(f93,plain,(
% 0.23/0.48    ~r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) | spl2_2),
% 0.23/0.48    inference(resolution,[],[f68,f25])).
% 0.23/0.48  fof(f25,plain,(
% 0.23/0.48    ( ! [X0,X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f14])).
% 0.23/0.48  fof(f14,plain,(
% 0.23/0.48    ! [X0] : (! [X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.23/0.48    inference(flattening,[],[f13])).
% 0.23/0.48  fof(f13,plain,(
% 0.23/0.48    ! [X0] : (! [X1] : ((r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.23/0.48    inference(ennf_transformation,[],[f9])).
% 0.23/0.48  fof(f9,axiom,(
% 0.23/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.23/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).
% 0.23/0.48  fof(f68,plain,(
% 0.23/0.48    ~r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k3_relat_1(sK1)) | spl2_2),
% 0.23/0.48    inference(avatar_component_clause,[],[f66])).
% 0.23/0.48  fof(f91,plain,(
% 0.23/0.48    spl2_5),
% 0.23/0.48    inference(avatar_contradiction_clause,[],[f90])).
% 0.23/0.48  fof(f90,plain,(
% 0.23/0.48    $false | spl2_5),
% 0.23/0.48    inference(resolution,[],[f82,f45])).
% 0.23/0.48  fof(f82,plain,(
% 0.23/0.48    ~r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK0) | spl2_5),
% 0.23/0.48    inference(avatar_component_clause,[],[f80])).
% 0.23/0.48  fof(f80,plain,(
% 0.23/0.48    spl2_5 <=> r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK0)),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.23/0.48  fof(f89,plain,(
% 0.23/0.48    spl2_4),
% 0.23/0.48    inference(avatar_contradiction_clause,[],[f88])).
% 0.23/0.48  fof(f88,plain,(
% 0.23/0.48    $false | spl2_4),
% 0.23/0.48    inference(resolution,[],[f78,f22])).
% 0.23/0.48  fof(f22,plain,(
% 0.23/0.48    v1_relat_1(sK0)),
% 0.23/0.48    inference(cnf_transformation,[],[f20])).
% 0.23/0.48  fof(f78,plain,(
% 0.23/0.48    ~v1_relat_1(sK0) | spl2_4),
% 0.23/0.48    inference(avatar_component_clause,[],[f76])).
% 0.23/0.48  fof(f76,plain,(
% 0.23/0.48    spl2_4 <=> v1_relat_1(sK0)),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.23/0.48  fof(f87,plain,(
% 0.23/0.48    spl2_3),
% 0.23/0.48    inference(avatar_contradiction_clause,[],[f86])).
% 0.23/0.48  fof(f86,plain,(
% 0.23/0.48    $false | spl2_3),
% 0.23/0.48    inference(resolution,[],[f85,f22])).
% 0.23/0.48  fof(f85,plain,(
% 0.23/0.48    ~v1_relat_1(sK0) | spl2_3),
% 0.23/0.48    inference(resolution,[],[f74,f46])).
% 0.23/0.48  fof(f46,plain,(
% 0.23/0.48    ( ! [X0,X1] : (v1_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) | ~v1_relat_1(X0)) )),
% 0.23/0.48    inference(resolution,[],[f45,f41])).
% 0.23/0.48  fof(f41,plain,(
% 0.23/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | v1_relat_1(X0)) )),
% 0.23/0.48    inference(resolution,[],[f26,f33])).
% 0.23/0.48  fof(f33,plain,(
% 0.23/0.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f21])).
% 0.23/0.48  fof(f21,plain,(
% 0.23/0.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.23/0.48    inference(nnf_transformation,[],[f7])).
% 0.23/0.48  fof(f7,axiom,(
% 0.23/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.23/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.23/0.48  fof(f26,plain,(
% 0.23/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f15])).
% 0.23/0.48  fof(f15,plain,(
% 0.23/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.23/0.48    inference(ennf_transformation,[],[f8])).
% 0.23/0.48  fof(f8,axiom,(
% 0.23/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.23/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.23/0.48  fof(f74,plain,(
% 0.23/0.48    ~v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) | spl2_3),
% 0.23/0.48    inference(avatar_component_clause,[],[f72])).
% 0.23/0.48  fof(f83,plain,(
% 0.23/0.48    ~spl2_3 | ~spl2_4 | ~spl2_5 | spl2_1),
% 0.23/0.48    inference(avatar_split_clause,[],[f70,f62,f80,f76,f72])).
% 0.23/0.48  fof(f62,plain,(
% 0.23/0.48    spl2_1 <=> r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k3_relat_1(sK0))),
% 0.23/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.23/0.48  fof(f70,plain,(
% 0.23/0.48    ~r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK0) | ~v1_relat_1(sK0) | ~v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) | spl2_1),
% 0.23/0.48    inference(resolution,[],[f64,f25])).
% 0.23/0.48  fof(f64,plain,(
% 0.23/0.48    ~r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k3_relat_1(sK0)) | spl2_1),
% 0.23/0.48    inference(avatar_component_clause,[],[f62])).
% 0.23/0.48  fof(f69,plain,(
% 0.23/0.48    ~spl2_1 | ~spl2_2),
% 0.23/0.48    inference(avatar_split_clause,[],[f58,f66,f62])).
% 0.23/0.48  fof(f58,plain,(
% 0.23/0.48    ~r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k3_relat_1(sK1)) | ~r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k3_relat_1(sK0))),
% 0.23/0.48    inference(resolution,[],[f39,f36])).
% 0.23/0.48  fof(f36,plain,(
% 0.23/0.48    ~r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK1))))),
% 0.23/0.48    inference(definition_unfolding,[],[f24,f35,f35])).
% 0.23/0.48  fof(f24,plain,(
% 0.23/0.48    ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))),
% 0.23/0.48    inference(cnf_transformation,[],[f20])).
% 0.23/0.48  fof(f39,plain,(
% 0.23/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.23/0.48    inference(definition_unfolding,[],[f34,f35])).
% 0.23/0.48  fof(f34,plain,(
% 0.23/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f17])).
% 0.23/0.48  fof(f17,plain,(
% 0.23/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.23/0.48    inference(flattening,[],[f16])).
% 0.23/0.48  fof(f16,plain,(
% 0.23/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.23/0.48    inference(ennf_transformation,[],[f1])).
% 0.23/0.48  fof(f1,axiom,(
% 0.23/0.48    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.23/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.23/0.48  % SZS output end Proof for theBenchmark
% 0.23/0.48  % (24047)------------------------------
% 0.23/0.48  % (24047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.48  % (24047)Termination reason: Refutation
% 0.23/0.48  
% 0.23/0.48  % (24047)Memory used [KB]: 6140
% 0.23/0.48  % (24047)Time elapsed: 0.057 s
% 0.23/0.48  % (24047)------------------------------
% 0.23/0.48  % (24047)------------------------------
% 0.23/0.48  % (24044)Success in time 0.107 s
%------------------------------------------------------------------------------
