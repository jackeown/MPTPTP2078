%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 184 expanded)
%              Number of leaves         :   23 (  68 expanded)
%              Depth                    :   12
%              Number of atoms          :  138 ( 276 expanded)
%              Number of equality atoms :   57 ( 137 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f614,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f65,f70,f97,f110,f597,f613])).

fof(f613,plain,
    ( spl3_1
    | ~ spl3_3
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f603,f594,f67,f57])).

fof(f57,plain,
    ( spl3_1
  <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f67,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f594,plain,
    ( spl3_39
  <=> sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f603,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | ~ spl3_3
    | ~ spl3_39 ),
    inference(superposition,[],[f219,f596])).

fof(f596,plain,
    ( sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1))
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f594])).

fof(f219,plain,
    ( ! [X2,X3] : r1_tarski(k10_relat_1(sK2,X2),k10_relat_1(sK2,k3_tarski(k1_enumset1(X2,X2,X3))))
    | ~ spl3_3 ),
    inference(superposition,[],[f49,f131])).

fof(f131,plain,
    ( ! [X0,X1] : k10_relat_1(sK2,k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f69,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(X2,k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k10_relat_1(X2,X0),k10_relat_1(X2,X0),k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f43,f46,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f38,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

fof(f69,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f33,f46])).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f597,plain,
    ( spl3_39
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f592,f107,f594])).

fof(f107,plain,
    ( spl3_5
  <=> k3_tarski(k1_enumset1(sK1,sK1,k5_xboole_0(sK0,sK0))) = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f592,plain,
    ( sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f585,f47])).

fof(f47,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f30,f46])).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f585,plain,
    ( k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k3_tarski(k1_enumset1(sK1,sK1,k1_xboole_0))
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f109,f379])).

fof(f379,plain,(
    ! [X5] : k1_xboole_0 = k5_xboole_0(X5,X5) ),
    inference(forward_demodulation,[],[f378,f48])).

fof(f48,plain,(
    ! [X0] : k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f32,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f37,f36])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f32,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f378,plain,(
    ! [X5] : k1_xboole_0 = k5_xboole_0(X5,k1_setfam_1(k1_enumset1(X5,X5,X5))) ),
    inference(forward_demodulation,[],[f371,f29])).

fof(f29,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f371,plain,(
    ! [X5] : k1_xboole_0 = k5_xboole_0(X5,k1_setfam_1(k1_enumset1(X5,X5,k5_xboole_0(X5,k1_xboole_0)))) ),
    inference(superposition,[],[f111,f72])).

fof(f72,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)) ),
    inference(unit_resulting_resolution,[],[f50,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f34,f44])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f111,plain,(
    ! [X0,X1] : k1_setfam_1(k1_enumset1(X1,X1,X0)) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X1,X1,X0)))))) ),
    inference(superposition,[],[f52,f51])).

fof(f51,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f35,f36,f36])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f52,plain,(
    ! [X0,X1] : k1_setfam_1(k1_enumset1(X0,X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))))) ),
    inference(definition_unfolding,[],[f40,f44,f45,f45])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f39,f44])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f109,plain,
    ( k3_tarski(k1_enumset1(sK1,sK1,k5_xboole_0(sK0,sK0))) = k3_tarski(k1_enumset1(sK0,sK0,sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f107])).

fof(f110,plain,
    ( spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f105,f93,f107])).

fof(f93,plain,
    ( spl3_4
  <=> sK0 = k1_setfam_1(k1_enumset1(sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f105,plain,
    ( k3_tarski(k1_enumset1(sK1,sK1,k5_xboole_0(sK0,sK0))) = k3_tarski(k1_enumset1(sK0,sK0,sK1))
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f103,f51])).

fof(f103,plain,
    ( k3_tarski(k1_enumset1(sK1,sK1,sK0)) = k3_tarski(k1_enumset1(sK1,sK1,k5_xboole_0(sK0,sK0)))
    | ~ spl3_4 ),
    inference(superposition,[],[f53,f95])).

fof(f95,plain,
    ( sK0 = k1_setfam_1(k1_enumset1(sK0,sK0,sK1))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f53,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X0,X0,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X0))))) ),
    inference(definition_unfolding,[],[f41,f46,f45,f46])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f97,plain,
    ( spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f87,f62,f93])).

fof(f62,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f87,plain,
    ( sK0 = k1_setfam_1(k1_enumset1(sK0,sK0,sK1))
    | ~ spl3_2 ),
    inference(resolution,[],[f54,f64])).

fof(f64,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f42,f44])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f70,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f26,f67])).

fof(f26,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

% (3743)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
fof(f65,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f27,f62])).

fof(f27,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f60,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f28,f57])).

fof(f28,plain,(
    ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:24:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  ipcrm: permission denied for id (1206255617)
% 0.14/0.37  ipcrm: permission denied for id (1210482692)
% 0.14/0.37  ipcrm: permission denied for id (1210515461)
% 0.14/0.37  ipcrm: permission denied for id (1206452231)
% 0.14/0.37  ipcrm: permission denied for id (1206517769)
% 0.14/0.37  ipcrm: permission denied for id (1206550538)
% 0.14/0.37  ipcrm: permission denied for id (1206583307)
% 0.14/0.37  ipcrm: permission denied for id (1206616076)
% 0.14/0.37  ipcrm: permission denied for id (1210613773)
% 0.14/0.37  ipcrm: permission denied for id (1210646542)
% 0.14/0.38  ipcrm: permission denied for id (1206747152)
% 0.14/0.38  ipcrm: permission denied for id (1206779921)
% 0.14/0.38  ipcrm: permission denied for id (1206812690)
% 0.14/0.38  ipcrm: permission denied for id (1210712083)
% 0.14/0.38  ipcrm: permission denied for id (1206878228)
% 0.14/0.38  ipcrm: permission denied for id (1206943766)
% 0.14/0.38  ipcrm: permission denied for id (1207009304)
% 0.14/0.38  ipcrm: permission denied for id (1207042073)
% 0.14/0.38  ipcrm: permission denied for id (1207074842)
% 0.14/0.39  ipcrm: permission denied for id (1210843164)
% 0.14/0.39  ipcrm: permission denied for id (1207238687)
% 0.14/0.39  ipcrm: permission denied for id (1207271456)
% 0.14/0.39  ipcrm: permission denied for id (1210974242)
% 0.14/0.39  ipcrm: permission denied for id (1211007011)
% 0.14/0.39  ipcrm: permission denied for id (1211072549)
% 0.14/0.40  ipcrm: permission denied for id (1211170856)
% 0.14/0.40  ipcrm: permission denied for id (1207631915)
% 0.14/0.40  ipcrm: permission denied for id (1211269164)
% 0.14/0.40  ipcrm: permission denied for id (1207697453)
% 0.14/0.40  ipcrm: permission denied for id (1211301934)
% 0.14/0.40  ipcrm: permission denied for id (1207762991)
% 0.14/0.40  ipcrm: permission denied for id (1207795760)
% 0.14/0.40  ipcrm: permission denied for id (1207828529)
% 0.14/0.40  ipcrm: permission denied for id (1207861298)
% 0.14/0.41  ipcrm: permission denied for id (1207894067)
% 0.14/0.41  ipcrm: permission denied for id (1207926836)
% 0.21/0.41  ipcrm: permission denied for id (1207992374)
% 0.21/0.41  ipcrm: permission denied for id (1208057912)
% 0.21/0.41  ipcrm: permission denied for id (1208090681)
% 0.21/0.41  ipcrm: permission denied for id (1211400250)
% 0.21/0.41  ipcrm: permission denied for id (1211433019)
% 0.21/0.41  ipcrm: permission denied for id (1208188988)
% 0.21/0.42  ipcrm: permission denied for id (1208254526)
% 0.21/0.42  ipcrm: permission denied for id (1211498559)
% 0.21/0.42  ipcrm: permission denied for id (1211564097)
% 0.21/0.42  ipcrm: permission denied for id (1208418371)
% 0.21/0.42  ipcrm: permission denied for id (1211629636)
% 0.21/0.42  ipcrm: permission denied for id (1208483909)
% 0.21/0.42  ipcrm: permission denied for id (1211662406)
% 0.21/0.43  ipcrm: permission denied for id (1211695175)
% 0.21/0.43  ipcrm: permission denied for id (1208647754)
% 0.21/0.43  ipcrm: permission denied for id (1208713292)
% 0.21/0.43  ipcrm: permission denied for id (1208746061)
% 0.21/0.43  ipcrm: permission denied for id (1211826254)
% 0.21/0.43  ipcrm: permission denied for id (1211859023)
% 0.21/0.44  ipcrm: permission denied for id (1211924561)
% 0.21/0.44  ipcrm: permission denied for id (1208909906)
% 0.21/0.44  ipcrm: permission denied for id (1208942675)
% 0.21/0.44  ipcrm: permission denied for id (1211957332)
% 0.21/0.44  ipcrm: permission denied for id (1212022870)
% 0.21/0.44  ipcrm: permission denied for id (1212055639)
% 0.21/0.44  ipcrm: permission denied for id (1209139288)
% 0.21/0.45  ipcrm: permission denied for id (1209204826)
% 0.21/0.45  ipcrm: permission denied for id (1209237595)
% 0.21/0.45  ipcrm: permission denied for id (1212153948)
% 0.21/0.45  ipcrm: permission denied for id (1212186717)
% 0.21/0.45  ipcrm: permission denied for id (1209401440)
% 0.21/0.45  ipcrm: permission denied for id (1209434209)
% 0.21/0.45  ipcrm: permission denied for id (1209499747)
% 0.21/0.46  ipcrm: permission denied for id (1209532516)
% 0.21/0.46  ipcrm: permission denied for id (1209598054)
% 0.21/0.46  ipcrm: permission denied for id (1209630823)
% 0.21/0.46  ipcrm: permission denied for id (1209696362)
% 0.21/0.46  ipcrm: permission denied for id (1212448876)
% 0.21/0.46  ipcrm: permission denied for id (1209794669)
% 0.21/0.47  ipcrm: permission denied for id (1209892976)
% 0.21/0.47  ipcrm: permission denied for id (1209958515)
% 0.21/0.47  ipcrm: permission denied for id (1210024053)
% 0.21/0.47  ipcrm: permission denied for id (1210089591)
% 0.21/0.48  ipcrm: permission denied for id (1212711032)
% 0.21/0.48  ipcrm: permission denied for id (1212743801)
% 0.21/0.48  ipcrm: permission denied for id (1210220667)
% 0.21/0.48  ipcrm: permission denied for id (1210253436)
% 0.21/0.48  ipcrm: permission denied for id (1210286205)
% 0.21/0.48  ipcrm: permission denied for id (1210351743)
% 0.21/0.54  % (3737)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.55  % (3732)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.56  % (3729)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.58  % (3732)Refutation found. Thanks to Tanya!
% 0.21/0.58  % SZS status Theorem for theBenchmark
% 0.21/0.58  % SZS output start Proof for theBenchmark
% 0.21/0.58  fof(f614,plain,(
% 0.21/0.58    $false),
% 0.21/0.58    inference(avatar_sat_refutation,[],[f60,f65,f70,f97,f110,f597,f613])).
% 0.21/0.58  fof(f613,plain,(
% 0.21/0.58    spl3_1 | ~spl3_3 | ~spl3_39),
% 0.21/0.58    inference(avatar_split_clause,[],[f603,f594,f67,f57])).
% 0.21/0.58  fof(f57,plain,(
% 0.21/0.58    spl3_1 <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.58  fof(f67,plain,(
% 0.21/0.58    spl3_3 <=> v1_relat_1(sK2)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.58  fof(f594,plain,(
% 0.21/0.58    spl3_39 <=> sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.21/0.58  fof(f603,plain,(
% 0.21/0.58    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | (~spl3_3 | ~spl3_39)),
% 0.21/0.58    inference(superposition,[],[f219,f596])).
% 0.21/0.58  fof(f596,plain,(
% 0.21/0.58    sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) | ~spl3_39),
% 0.21/0.58    inference(avatar_component_clause,[],[f594])).
% 0.21/0.58  fof(f219,plain,(
% 0.21/0.58    ( ! [X2,X3] : (r1_tarski(k10_relat_1(sK2,X2),k10_relat_1(sK2,k3_tarski(k1_enumset1(X2,X2,X3))))) ) | ~spl3_3),
% 0.21/0.58    inference(superposition,[],[f49,f131])).
% 0.21/0.58  fof(f131,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k10_relat_1(sK2,k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)))) ) | ~spl3_3),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f69,f55])).
% 0.21/0.58  fof(f55,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(X2,k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k10_relat_1(X2,X0),k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) )),
% 0.21/0.58    inference(definition_unfolding,[],[f43,f46,f46])).
% 0.21/0.58  fof(f46,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 0.21/0.58    inference(definition_unfolding,[],[f38,f36])).
% 0.21/0.58  fof(f36,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f12])).
% 0.21/0.58  fof(f12,axiom,(
% 0.21/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.58  fof(f38,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f13])).
% 0.21/0.58  fof(f13,axiom,(
% 0.21/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.58  fof(f43,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f23])).
% 0.21/0.58  fof(f23,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.21/0.58    inference(ennf_transformation,[],[f15])).
% 0.21/0.58  fof(f15,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).
% 0.21/0.58  fof(f69,plain,(
% 0.21/0.58    v1_relat_1(sK2) | ~spl3_3),
% 0.21/0.58    inference(avatar_component_clause,[],[f67])).
% 0.21/0.58  fof(f49,plain,(
% 0.21/0.58    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 0.21/0.58    inference(definition_unfolding,[],[f33,f46])).
% 0.21/0.58  fof(f33,plain,(
% 0.21/0.58    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f10])).
% 0.21/0.58  fof(f10,axiom,(
% 0.21/0.58    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.58  fof(f597,plain,(
% 0.21/0.58    spl3_39 | ~spl3_5),
% 0.21/0.58    inference(avatar_split_clause,[],[f592,f107,f594])).
% 0.21/0.58  fof(f107,plain,(
% 0.21/0.58    spl3_5 <=> k3_tarski(k1_enumset1(sK1,sK1,k5_xboole_0(sK0,sK0))) = k3_tarski(k1_enumset1(sK0,sK0,sK1))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.58  fof(f592,plain,(
% 0.21/0.58    sK1 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) | ~spl3_5),
% 0.21/0.58    inference(forward_demodulation,[],[f585,f47])).
% 0.21/0.58  fof(f47,plain,(
% 0.21/0.58    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0) )),
% 0.21/0.58    inference(definition_unfolding,[],[f30,f46])).
% 0.21/0.58  fof(f30,plain,(
% 0.21/0.58    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f4])).
% 0.21/0.58  fof(f4,axiom,(
% 0.21/0.58    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.58  fof(f585,plain,(
% 0.21/0.58    k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k3_tarski(k1_enumset1(sK1,sK1,k1_xboole_0)) | ~spl3_5),
% 0.21/0.58    inference(backward_demodulation,[],[f109,f379])).
% 0.21/0.58  fof(f379,plain,(
% 0.21/0.58    ( ! [X5] : (k1_xboole_0 = k5_xboole_0(X5,X5)) )),
% 0.21/0.58    inference(forward_demodulation,[],[f378,f48])).
% 0.21/0.58  fof(f48,plain,(
% 0.21/0.58    ( ! [X0] : (k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0) )),
% 0.21/0.58    inference(definition_unfolding,[],[f32,f44])).
% 0.21/0.58  fof(f44,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.21/0.58    inference(definition_unfolding,[],[f37,f36])).
% 0.21/0.58  fof(f37,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f14])).
% 0.21/0.58  fof(f14,axiom,(
% 0.21/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.58  fof(f32,plain,(
% 0.21/0.58    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f18])).
% 0.21/0.58  fof(f18,plain,(
% 0.21/0.58    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.58    inference(rectify,[],[f1])).
% 0.21/0.58  fof(f1,axiom,(
% 0.21/0.58    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.21/0.58  fof(f378,plain,(
% 0.21/0.58    ( ! [X5] : (k1_xboole_0 = k5_xboole_0(X5,k1_setfam_1(k1_enumset1(X5,X5,X5)))) )),
% 0.21/0.58    inference(forward_demodulation,[],[f371,f29])).
% 0.21/0.58  fof(f29,plain,(
% 0.21/0.58    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f9])).
% 0.21/0.58  fof(f9,axiom,(
% 0.21/0.58    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.58  fof(f371,plain,(
% 0.21/0.58    ( ! [X5] : (k1_xboole_0 = k5_xboole_0(X5,k1_setfam_1(k1_enumset1(X5,X5,k5_xboole_0(X5,k1_xboole_0))))) )),
% 0.21/0.58    inference(superposition,[],[f111,f72])).
% 0.21/0.58  fof(f72,plain,(
% 0.21/0.58    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X0))) )),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f50,f31])).
% 0.21/0.58  fof(f31,plain,(
% 0.21/0.58    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f21])).
% 0.21/0.58  fof(f21,plain,(
% 0.21/0.58    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.58    inference(ennf_transformation,[],[f7])).
% 0.21/0.58  fof(f7,axiom,(
% 0.21/0.58    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.58  fof(f50,plain,(
% 0.21/0.58    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0)) )),
% 0.21/0.58    inference(definition_unfolding,[],[f34,f44])).
% 0.21/0.58  fof(f34,plain,(
% 0.21/0.58    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f3])).
% 0.21/0.58  fof(f3,axiom,(
% 0.21/0.58    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.58  fof(f111,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X1,X1,X0)) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X1,X1,X0))))))) )),
% 0.21/0.58    inference(superposition,[],[f52,f51])).
% 0.21/0.58  fof(f51,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 0.21/0.58    inference(definition_unfolding,[],[f35,f36,f36])).
% 0.91/0.58  fof(f35,plain,(
% 0.91/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.91/0.58    inference(cnf_transformation,[],[f11])).
% 0.91/0.58  fof(f11,axiom,(
% 0.91/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.91/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.91/0.58  fof(f52,plain,(
% 0.91/0.58    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))))))) )),
% 0.91/0.58    inference(definition_unfolding,[],[f40,f44,f45,f45])).
% 0.91/0.58  fof(f45,plain,(
% 0.91/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 0.91/0.58    inference(definition_unfolding,[],[f39,f44])).
% 0.91/0.58  fof(f39,plain,(
% 0.91/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.91/0.58    inference(cnf_transformation,[],[f2])).
% 0.91/0.58  fof(f2,axiom,(
% 0.91/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.91/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.91/0.58  fof(f40,plain,(
% 0.91/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.91/0.58    inference(cnf_transformation,[],[f8])).
% 0.91/0.58  fof(f8,axiom,(
% 0.91/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.91/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.91/0.58  fof(f109,plain,(
% 0.91/0.58    k3_tarski(k1_enumset1(sK1,sK1,k5_xboole_0(sK0,sK0))) = k3_tarski(k1_enumset1(sK0,sK0,sK1)) | ~spl3_5),
% 0.91/0.58    inference(avatar_component_clause,[],[f107])).
% 0.91/0.58  fof(f110,plain,(
% 0.91/0.58    spl3_5 | ~spl3_4),
% 0.91/0.58    inference(avatar_split_clause,[],[f105,f93,f107])).
% 0.91/0.58  fof(f93,plain,(
% 0.91/0.58    spl3_4 <=> sK0 = k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),
% 0.91/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.91/0.58  fof(f105,plain,(
% 0.91/0.58    k3_tarski(k1_enumset1(sK1,sK1,k5_xboole_0(sK0,sK0))) = k3_tarski(k1_enumset1(sK0,sK0,sK1)) | ~spl3_4),
% 0.91/0.58    inference(forward_demodulation,[],[f103,f51])).
% 0.91/0.58  fof(f103,plain,(
% 0.91/0.58    k3_tarski(k1_enumset1(sK1,sK1,sK0)) = k3_tarski(k1_enumset1(sK1,sK1,k5_xboole_0(sK0,sK0))) | ~spl3_4),
% 0.91/0.58    inference(superposition,[],[f53,f95])).
% 0.91/0.58  fof(f95,plain,(
% 0.91/0.58    sK0 = k1_setfam_1(k1_enumset1(sK0,sK0,sK1)) | ~spl3_4),
% 0.91/0.58    inference(avatar_component_clause,[],[f93])).
% 0.91/0.58  fof(f53,plain,(
% 0.91/0.58    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X0,X0,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X0)))))) )),
% 0.91/0.58    inference(definition_unfolding,[],[f41,f46,f45,f46])).
% 0.91/0.58  fof(f41,plain,(
% 0.91/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.91/0.58    inference(cnf_transformation,[],[f6])).
% 0.91/0.58  fof(f6,axiom,(
% 0.91/0.58    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.91/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.91/0.58  fof(f97,plain,(
% 0.91/0.58    spl3_4 | ~spl3_2),
% 0.91/0.58    inference(avatar_split_clause,[],[f87,f62,f93])).
% 0.91/0.58  fof(f62,plain,(
% 0.91/0.58    spl3_2 <=> r1_tarski(sK0,sK1)),
% 0.91/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.91/0.58  fof(f87,plain,(
% 0.91/0.58    sK0 = k1_setfam_1(k1_enumset1(sK0,sK0,sK1)) | ~spl3_2),
% 0.91/0.58    inference(resolution,[],[f54,f64])).
% 0.91/0.58  fof(f64,plain,(
% 0.91/0.58    r1_tarski(sK0,sK1) | ~spl3_2),
% 0.91/0.58    inference(avatar_component_clause,[],[f62])).
% 0.91/0.58  fof(f54,plain,(
% 0.91/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0) )),
% 0.91/0.58    inference(definition_unfolding,[],[f42,f44])).
% 0.91/0.58  fof(f42,plain,(
% 0.91/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.91/0.58    inference(cnf_transformation,[],[f22])).
% 0.91/0.58  fof(f22,plain,(
% 0.91/0.58    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.91/0.58    inference(ennf_transformation,[],[f5])).
% 0.91/0.58  fof(f5,axiom,(
% 0.91/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.91/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.91/0.58  fof(f70,plain,(
% 0.91/0.58    spl3_3),
% 0.91/0.58    inference(avatar_split_clause,[],[f26,f67])).
% 0.91/0.58  fof(f26,plain,(
% 0.91/0.58    v1_relat_1(sK2)),
% 0.91/0.58    inference(cnf_transformation,[],[f25])).
% 0.91/0.58  fof(f25,plain,(
% 0.91/0.58    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.91/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f24])).
% 0.91/0.58  fof(f24,plain,(
% 0.91/0.58    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.91/0.58    introduced(choice_axiom,[])).
% 0.91/0.58  fof(f20,plain,(
% 0.91/0.58    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.91/0.58    inference(flattening,[],[f19])).
% 0.91/0.58  fof(f19,plain,(
% 0.91/0.58    ? [X0,X1,X2] : ((~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.91/0.58    inference(ennf_transformation,[],[f17])).
% 0.91/0.58  fof(f17,negated_conjecture,(
% 0.91/0.58    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.91/0.58    inference(negated_conjecture,[],[f16])).
% 0.91/0.58  fof(f16,conjecture,(
% 0.91/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.91/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).
% 0.91/0.58  % (3743)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.91/0.58  fof(f65,plain,(
% 0.91/0.58    spl3_2),
% 0.91/0.58    inference(avatar_split_clause,[],[f27,f62])).
% 0.91/0.58  fof(f27,plain,(
% 0.91/0.58    r1_tarski(sK0,sK1)),
% 0.91/0.58    inference(cnf_transformation,[],[f25])).
% 0.91/0.58  fof(f60,plain,(
% 0.91/0.58    ~spl3_1),
% 0.91/0.58    inference(avatar_split_clause,[],[f28,f57])).
% 0.91/0.58  fof(f28,plain,(
% 0.91/0.58    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.91/0.58    inference(cnf_transformation,[],[f25])).
% 0.91/0.58  % SZS output end Proof for theBenchmark
% 0.91/0.58  % (3732)------------------------------
% 0.91/0.58  % (3732)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.91/0.58  % (3732)Termination reason: Refutation
% 0.91/0.58  
% 0.91/0.58  % (3732)Memory used [KB]: 6524
% 0.91/0.58  % (3732)Time elapsed: 0.030 s
% 0.91/0.58  % (3732)------------------------------
% 0.91/0.58  % (3732)------------------------------
% 0.91/0.58  % (3591)Success in time 0.224 s
%------------------------------------------------------------------------------
