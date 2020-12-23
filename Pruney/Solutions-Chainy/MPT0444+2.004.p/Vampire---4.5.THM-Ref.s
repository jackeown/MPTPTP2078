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
% DateTime   : Thu Dec  3 12:47:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 187 expanded)
%              Number of leaves         :   21 (  68 expanded)
%              Depth                    :   10
%              Number of atoms          :  172 ( 349 expanded)
%              Number of equality atoms :   15 (  83 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f193,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f102,f104,f126,f169,f178,f190,f192])).

fof(f192,plain,(
    spl2_9 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | spl2_9 ),
    inference(resolution,[],[f177,f116])).

fof(f116,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X1) ),
    inference(forward_demodulation,[],[f115,f66])).

fof(f66,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f60,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f60,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[],[f44,f42])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_enumset1(X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f27,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f27,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f33,f40])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f115,plain,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_xboole_0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1) ),
    inference(forward_demodulation,[],[f106,f66])).

fof(f106,plain,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_xboole_0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k2_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f45,f42])).

fof(f45,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X2))),k2_xboole_0(X1,X2)) ),
    inference(definition_unfolding,[],[f38,f40,f40])).

fof(f38,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f177,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1)
    | spl2_9 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl2_9
  <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f190,plain,(
    spl2_8 ),
    inference(avatar_contradiction_clause,[],[f189])).

fof(f189,plain,
    ( $false
    | spl2_8 ),
    inference(resolution,[],[f173,f25])).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).

fof(f173,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_8 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl2_8
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f178,plain,
    ( ~ spl2_5
    | ~ spl2_8
    | ~ spl2_9
    | spl2_4 ),
    inference(avatar_split_clause,[],[f127,f85,f175,f171,f91])).

fof(f91,plain,
    ( spl2_5
  <=> v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f85,plain,
    ( spl2_4
  <=> r1_tarski(k2_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f127,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))
    | spl2_4 ),
    inference(resolution,[],[f87,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f87,plain,
    ( ~ r1_tarski(k2_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k2_relat_1(sK1))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f169,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | spl2_5 ),
    inference(resolution,[],[f165,f24])).

fof(f24,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f165,plain,
    ( ~ v1_relat_1(sK0)
    | spl2_5 ),
    inference(resolution,[],[f49,f93])).

fof(f93,plain,
    ( ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f91])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f43,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f30,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f31,f40])).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f126,plain,(
    spl2_7 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | spl2_7 ),
    inference(resolution,[],[f101,f43])).

fof(f101,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0)
    | spl2_7 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl2_7
  <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f104,plain,(
    spl2_6 ),
    inference(avatar_contradiction_clause,[],[f103])).

fof(f103,plain,
    ( $false
    | spl2_6 ),
    inference(resolution,[],[f97,f24])).

fof(f97,plain,
    ( ~ v1_relat_1(sK0)
    | spl2_6 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl2_6
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f102,plain,
    ( ~ spl2_5
    | ~ spl2_6
    | ~ spl2_7
    | spl2_3 ),
    inference(avatar_split_clause,[],[f89,f81,f99,f95,f91])).

fof(f81,plain,
    ( spl2_3
  <=> r1_tarski(k2_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f89,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))
    | spl2_3 ),
    inference(resolution,[],[f83,f29])).

fof(f83,plain,
    ( ~ r1_tarski(k2_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k2_relat_1(sK0))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f88,plain,
    ( ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f78,f85,f81])).

fof(f78,plain,
    ( ~ r1_tarski(k2_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k2_relat_1(sK1))
    | ~ r1_tarski(k2_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k2_relat_1(sK0)) ),
    inference(resolution,[],[f46,f41])).

fof(f41,plain,(
    ~ r1_tarski(k2_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK1)))) ),
    inference(definition_unfolding,[],[f26,f40,f40])).

fof(f26,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:17:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (16590)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (16583)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (16583)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (16590)Refutation not found, incomplete strategy% (16590)------------------------------
% 0.21/0.48  % (16590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f193,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f88,f102,f104,f126,f169,f178,f190,f192])).
% 0.21/0.48  fof(f192,plain,(
% 0.21/0.48    spl2_9),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f191])).
% 0.21/0.48  fof(f191,plain,(
% 0.21/0.48    $false | spl2_9),
% 0.21/0.48    inference(resolution,[],[f177,f116])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X1)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f115,f66])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 0.21/0.48    inference(superposition,[],[f60,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.48    inference(superposition,[],[f44,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_enumset1(X0,X0,X0,k1_xboole_0))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f27,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f34,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = X0) )),
% 0.21/0.48    inference(definition_unfolding,[],[f33,f40])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_xboole_0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f106,f66])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_xboole_0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k2_xboole_0(k1_xboole_0,X1))) )),
% 0.21/0.48    inference(superposition,[],[f45,f42])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X2))),k2_xboole_0(X1,X2))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f38,f40,f40])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).
% 0.21/0.48  fof(f177,plain,(
% 0.21/0.48    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) | spl2_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f175])).
% 0.21/0.48  fof(f175,plain,(
% 0.21/0.48    spl2_9 <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.48  fof(f190,plain,(
% 0.21/0.48    spl2_8),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f189])).
% 0.21/0.48  fof(f189,plain,(
% 0.21/0.48    $false | spl2_8),
% 0.21/0.48    inference(resolution,[],[f173,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    v1_relat_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f21,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f12])).
% 0.21/0.48  fof(f12,conjecture,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).
% 0.21/0.48  fof(f173,plain,(
% 0.21/0.48    ~v1_relat_1(sK1) | spl2_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f171])).
% 0.21/0.48  fof(f171,plain,(
% 0.21/0.48    spl2_8 <=> v1_relat_1(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.48  fof(f178,plain,(
% 0.21/0.48    ~spl2_5 | ~spl2_8 | ~spl2_9 | spl2_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f127,f85,f175,f171,f91])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    spl2_5 <=> v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    spl2_4 <=> r1_tarski(k2_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k2_relat_1(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) | spl2_4),
% 0.21/0.48    inference(resolution,[],[f87,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    ~r1_tarski(k2_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k2_relat_1(sK1)) | spl2_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f85])).
% 0.21/0.48  fof(f169,plain,(
% 0.21/0.48    spl2_5),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f168])).
% 0.21/0.48  fof(f168,plain,(
% 0.21/0.48    $false | spl2_5),
% 0.21/0.48    inference(resolution,[],[f165,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    v1_relat_1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f165,plain,(
% 0.21/0.48    ~v1_relat_1(sK0) | spl2_5),
% 0.21/0.48    inference(resolution,[],[f49,f93])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    ~v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) | spl2_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f91])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(resolution,[],[f43,f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | v1_relat_1(X0)) )),
% 0.21/0.48    inference(resolution,[],[f30,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.48    inference(nnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f31,f40])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    spl2_7),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f125])).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    $false | spl2_7),
% 0.21/0.48    inference(resolution,[],[f101,f43])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0) | spl2_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f99])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    spl2_7 <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    spl2_6),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f103])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    $false | spl2_6),
% 0.21/0.48    inference(resolution,[],[f97,f24])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    ~v1_relat_1(sK0) | spl2_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f95])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    spl2_6 <=> v1_relat_1(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    ~spl2_5 | ~spl2_6 | ~spl2_7 | spl2_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f89,f81,f99,f95,f91])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    spl2_3 <=> r1_tarski(k2_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k2_relat_1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0) | ~v1_relat_1(sK0) | ~v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) | spl2_3),
% 0.21/0.48    inference(resolution,[],[f83,f29])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    ~r1_tarski(k2_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k2_relat_1(sK0)) | spl2_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f81])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    ~spl2_3 | ~spl2_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f78,f85,f81])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    ~r1_tarski(k2_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k2_relat_1(sK1)) | ~r1_tarski(k2_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k2_relat_1(sK0))),
% 0.21/0.48    inference(resolution,[],[f46,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ~r1_tarski(k2_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK1))))),
% 0.21/0.48    inference(definition_unfolding,[],[f26,f40,f40])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f39,f40])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (16583)------------------------------
% 0.21/0.48  % (16583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (16583)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (16583)Memory used [KB]: 6140
% 0.21/0.48  % (16583)Time elapsed: 0.068 s
% 0.21/0.48  % (16583)------------------------------
% 0.21/0.48  % (16583)------------------------------
% 0.21/0.48  % (16574)Success in time 0.127 s
%------------------------------------------------------------------------------
