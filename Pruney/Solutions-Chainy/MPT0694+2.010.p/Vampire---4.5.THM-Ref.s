%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 177 expanded)
%              Number of leaves         :   16 (  61 expanded)
%              Depth                    :   10
%              Number of atoms          :  157 ( 317 expanded)
%              Number of equality atoms :   14 (  82 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f295,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f49,f58,f64,f132,f134,f294])).

fof(f294,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f293])).

fof(f293,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | spl3_5 ),
    inference(subsumption_resolution,[],[f291,f92])).

fof(f92,plain,
    ( ! [X0,X1] : r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1))),k9_relat_1(sK2,X1))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f78,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k1_setfam_1(k1_enumset1(X1,X1,X0)))
      | r1_tarski(X2,X0) ) ),
    inference(superposition,[],[f38,f35])).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f25,f26,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f27,f26])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f78,plain,
    ( ! [X0,X1] : r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f43,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1))),k1_setfam_1(k1_enumset1(k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X1))))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f30,f33,f33])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).

fof(f43,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f291,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,k10_relat_1(sK2,sK1)))
    | ~ spl3_1
    | ~ spl3_2
    | spl3_5 ),
    inference(superposition,[],[f136,f70])).

fof(f70,plain,
    ( ! [X0] : k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(sK2,k10_relat_1(sK2,X0))))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f66,f35])).

fof(f66,plain,
    ( ! [X0] : k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k1_setfam_1(k1_enumset1(k9_relat_1(sK2,k10_relat_1(sK2,X0)),k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f52,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f28,f33])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f52,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f43,f48,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f48,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl3_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f136,plain,
    ( ! [X0] : ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(sK1,sK1,X0)))
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f127,f38])).

fof(f127,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),sK1)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl3_5
  <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f134,plain,
    ( ~ spl3_1
    | spl3_6 ),
    inference(avatar_contradiction_clause,[],[f133])).

fof(f133,plain,
    ( $false
    | ~ spl3_1
    | spl3_6 ),
    inference(subsumption_resolution,[],[f131,f93])).

fof(f93,plain,
    ( ! [X0,X1] : r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1))),k9_relat_1(sK2,X0))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f78,f38])).

fof(f131,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl3_6
  <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f132,plain,
    ( ~ spl3_5
    | ~ spl3_6
    | spl3_4 ),
    inference(avatar_split_clause,[],[f75,f61,f129,f125])).

fof(f61,plain,
    ( spl3_4
  <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f75,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0))
    | ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),sK1)
    | spl3_4 ),
    inference(resolution,[],[f39,f63])).

fof(f63,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f61])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f33])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f64,plain,
    ( ~ spl3_4
    | spl3_3 ),
    inference(avatar_split_clause,[],[f59,f55,f61])).

fof(f55,plain,
    ( spl3_3
  <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f59,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))))
    | spl3_3 ),
    inference(forward_demodulation,[],[f57,f35])).

fof(f57,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f58,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f34,f55])).

fof(f34,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) ),
    inference(definition_unfolding,[],[f24,f33,f33])).

fof(f24,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_funct_1)).

fof(f49,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f23,f46])).

fof(f23,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f44,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f22,f41])).

fof(f22,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:09:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.45  % (13419)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.46  % (13408)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (13419)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f295,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f44,f49,f58,f64,f132,f134,f294])).
% 0.21/0.46  fof(f294,plain,(
% 0.21/0.46    ~spl3_1 | ~spl3_2 | spl3_5),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f293])).
% 0.21/0.46  fof(f293,plain,(
% 0.21/0.46    $false | (~spl3_1 | ~spl3_2 | spl3_5)),
% 0.21/0.46    inference(subsumption_resolution,[],[f291,f92])).
% 0.21/0.46  fof(f92,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1))),k9_relat_1(sK2,X1))) ) | ~spl3_1),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f78,f50])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r1_tarski(X2,k1_setfam_1(k1_enumset1(X1,X1,X0))) | r1_tarski(X2,X0)) )),
% 0.21/0.46    inference(superposition,[],[f38,f35])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f25,f26,f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) | r1_tarski(X0,X1)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f31,f33])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f27,f26])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.46    inference(ennf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).
% 0.21/0.46  fof(f78,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))))) ) | ~spl3_1),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f43,f37])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1))),k1_setfam_1(k1_enumset1(k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) | ~v1_relat_1(X2)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f30,f33,f33])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) | ~v1_relat_1(X2))),
% 0.21/0.46    inference(ennf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    v1_relat_1(sK2) | ~spl3_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f41])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    spl3_1 <=> v1_relat_1(sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.46  fof(f291,plain,(
% 0.21/0.46    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,k10_relat_1(sK2,sK1))) | (~spl3_1 | ~spl3_2 | spl3_5)),
% 0.21/0.46    inference(superposition,[],[f136,f70])).
% 0.21/0.46  fof(f70,plain,(
% 0.21/0.46    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(sK2,k10_relat_1(sK2,X0))))) ) | (~spl3_1 | ~spl3_2)),
% 0.21/0.46    inference(forward_demodulation,[],[f66,f35])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k1_setfam_1(k1_enumset1(k9_relat_1(sK2,k10_relat_1(sK2,X0)),k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0))) ) | (~spl3_1 | ~spl3_2)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f52,f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0) )),
% 0.21/0.47    inference(definition_unfolding,[],[f28,f33])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    ( ! [X0] : (r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)) ) | (~spl3_1 | ~spl3_2)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f43,f48,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_funct_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(flattening,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    v1_funct_1(sK2) | ~spl3_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    spl3_2 <=> v1_funct_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.47  fof(f136,plain,(
% 0.21/0.47    ( ! [X0] : (~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(sK1,sK1,X0)))) ) | spl3_5),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f127,f38])).
% 0.21/0.47  fof(f127,plain,(
% 0.21/0.47    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) | spl3_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f125])).
% 0.21/0.47  fof(f125,plain,(
% 0.21/0.47    spl3_5 <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.47  fof(f134,plain,(
% 0.21/0.47    ~spl3_1 | spl3_6),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f133])).
% 0.21/0.47  fof(f133,plain,(
% 0.21/0.47    $false | (~spl3_1 | spl3_6)),
% 0.21/0.47    inference(subsumption_resolution,[],[f131,f93])).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1))),k9_relat_1(sK2,X0))) ) | ~spl3_1),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f78,f38])).
% 0.21/0.47  fof(f131,plain,(
% 0.21/0.47    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0)) | spl3_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f129])).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    spl3_6 <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.47  fof(f132,plain,(
% 0.21/0.47    ~spl3_5 | ~spl3_6 | spl3_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f75,f61,f129,f125])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    spl3_4 <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0)) | ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) | spl3_4),
% 0.21/0.47    inference(resolution,[],[f39,f63])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)))) | spl3_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f61])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f32,f33])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    ~spl3_4 | spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f59,f55,f61])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    spl3_3 <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)))) | spl3_3),
% 0.21/0.47    inference(forward_demodulation,[],[f57,f35])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) | spl3_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f55])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    ~spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f34,f55])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)))),
% 0.21/0.47    inference(definition_unfolding,[],[f24,f33,f33])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.47    inference(flattening,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.47    inference(ennf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 0.21/0.47    inference(negated_conjecture,[],[f9])).
% 0.21/0.47  fof(f9,conjecture,(
% 0.21/0.47    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_funct_1)).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f23,f46])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    v1_funct_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    spl3_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f22,f41])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    v1_relat_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (13419)------------------------------
% 0.21/0.47  % (13419)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (13419)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (13419)Memory used [KB]: 11001
% 0.21/0.47  % (13419)Time elapsed: 0.019 s
% 0.21/0.47  % (13419)------------------------------
% 0.21/0.47  % (13419)------------------------------
% 0.21/0.47  % (13406)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (13403)Success in time 0.105 s
%------------------------------------------------------------------------------
