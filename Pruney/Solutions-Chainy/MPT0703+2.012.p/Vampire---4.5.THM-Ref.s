%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 120 expanded)
%              Number of leaves         :   16 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :  162 ( 352 expanded)
%              Number of equality atoms :   29 (  44 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f138,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f47,f52,f57,f81,f104,f132,f137])).

fof(f137,plain,
    ( spl3_3
    | ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | spl3_3
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f134,f46])).

fof(f46,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl3_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f134,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_10 ),
    inference(superposition,[],[f58,f131])).

fof(f131,plain,
    ( sK0 = k1_setfam_1(k2_tarski(sK0,sK1))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl3_10
  <=> sK0 = k1_setfam_1(k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0) ),
    inference(superposition,[],[f29,f30])).

fof(f30,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f24,f25,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

% (28803)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f23,f25])).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f132,plain,
    ( spl3_10
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f112,f101,f78,f39,f34,f129])).

fof(f34,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f39,plain,
    ( spl3_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f78,plain,
    ( spl3_7
  <=> sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f101,plain,
    ( spl3_9
  <=> k10_relat_1(sK2,sK0) = k1_setfam_1(k2_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f112,plain,
    ( sK0 = k1_setfam_1(k2_tarski(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f111,f80])).

fof(f80,plain,
    ( sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f78])).

fof(f111,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),sK1))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(superposition,[],[f70,f103])).

fof(f103,plain,
    ( k10_relat_1(sK2,sK0) = k1_setfam_1(k2_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f101])).

fof(f70,plain,
    ( ! [X0,X1] : k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,k10_relat_1(sK2,X1)))) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),X1))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f36,f41,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k9_relat_1(X2,k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1)))) = k1_setfam_1(k2_tarski(k9_relat_1(X2,X0),X1))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f28,f25,f25])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_funct_1)).

fof(f41,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f36,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f104,plain,
    ( spl3_9
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f61,f54,f101])).

fof(f54,plain,
    ( spl3_5
  <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f61,plain,
    ( k10_relat_1(sK2,sK0) = k1_setfam_1(k2_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f56,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f26,f25])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f56,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f81,plain,
    ( spl3_7
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f66,f49,f39,f34,f78])).

fof(f49,plain,
    ( spl3_4
  <=> r1_tarski(sK0,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f66,plain,
    ( sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f36,f41,f51,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f51,plain,
    ( r1_tarski(sK0,k2_relat_1(sK2))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f57,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f20,f54])).

fof(f20,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k2_relat_1(sK2))
    & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_tarski(X0,k2_relat_1(X2))
        & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_tarski(sK0,k2_relat_1(sK2))
      & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

fof(f52,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f21,f49])).

fof(f21,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f47,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f22,f44])).

fof(f22,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f42,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f19,f39])).

fof(f19,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f37,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f18,f34])).

fof(f18,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:08:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (28814)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.45  % (28806)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.46  % (28814)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % (28802)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f138,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f37,f42,f47,f52,f57,f81,f104,f132,f137])).
% 0.20/0.46  fof(f137,plain,(
% 0.20/0.46    spl3_3 | ~spl3_10),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f136])).
% 0.20/0.46  fof(f136,plain,(
% 0.20/0.46    $false | (spl3_3 | ~spl3_10)),
% 0.20/0.46    inference(subsumption_resolution,[],[f134,f46])).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    ~r1_tarski(sK0,sK1) | spl3_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f44])).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    spl3_3 <=> r1_tarski(sK0,sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.46  fof(f134,plain,(
% 0.20/0.46    r1_tarski(sK0,sK1) | ~spl3_10),
% 0.20/0.46    inference(superposition,[],[f58,f131])).
% 0.20/0.46  fof(f131,plain,(
% 0.20/0.46    sK0 = k1_setfam_1(k2_tarski(sK0,sK1)) | ~spl3_10),
% 0.20/0.46    inference(avatar_component_clause,[],[f129])).
% 0.20/0.46  fof(f129,plain,(
% 0.20/0.46    spl3_10 <=> sK0 = k1_setfam_1(k2_tarski(sK0,sK1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.46  fof(f58,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0)) )),
% 0.20/0.46    inference(superposition,[],[f29,f30])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f24,f25,f25])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.46  % (28803)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f23,f25])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.46  fof(f132,plain,(
% 0.20/0.46    spl3_10 | ~spl3_1 | ~spl3_2 | ~spl3_7 | ~spl3_9),
% 0.20/0.46    inference(avatar_split_clause,[],[f112,f101,f78,f39,f34,f129])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    spl3_1 <=> v1_relat_1(sK2)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    spl3_2 <=> v1_funct_1(sK2)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.46  fof(f78,plain,(
% 0.20/0.46    spl3_7 <=> sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.46  fof(f101,plain,(
% 0.20/0.46    spl3_9 <=> k10_relat_1(sK2,sK0) = k1_setfam_1(k2_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.46  fof(f112,plain,(
% 0.20/0.46    sK0 = k1_setfam_1(k2_tarski(sK0,sK1)) | (~spl3_1 | ~spl3_2 | ~spl3_7 | ~spl3_9)),
% 0.20/0.46    inference(forward_demodulation,[],[f111,f80])).
% 0.20/0.46  fof(f80,plain,(
% 0.20/0.46    sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0)) | ~spl3_7),
% 0.20/0.46    inference(avatar_component_clause,[],[f78])).
% 0.20/0.46  fof(f111,plain,(
% 0.20/0.46    k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),sK1)) | (~spl3_1 | ~spl3_2 | ~spl3_9)),
% 0.20/0.46    inference(superposition,[],[f70,f103])).
% 0.20/0.46  fof(f103,plain,(
% 0.20/0.46    k10_relat_1(sK2,sK0) = k1_setfam_1(k2_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) | ~spl3_9),
% 0.20/0.46    inference(avatar_component_clause,[],[f101])).
% 0.20/0.46  fof(f70,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,k10_relat_1(sK2,X1)))) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),X1))) ) | (~spl3_1 | ~spl3_2)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f36,f41,f32])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k9_relat_1(X2,k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1)))) = k1_setfam_1(k2_tarski(k9_relat_1(X2,X0),X1)) | ~v1_relat_1(X2)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f28,f25,f25])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.46    inference(flattening,[],[f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.46    inference(ennf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_funct_1)).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    v1_funct_1(sK2) | ~spl3_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f39])).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    v1_relat_1(sK2) | ~spl3_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f34])).
% 0.20/0.46  fof(f104,plain,(
% 0.20/0.46    spl3_9 | ~spl3_5),
% 0.20/0.46    inference(avatar_split_clause,[],[f61,f54,f101])).
% 0.20/0.46  fof(f54,plain,(
% 0.20/0.46    spl3_5 <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.46  fof(f61,plain,(
% 0.20/0.46    k10_relat_1(sK2,sK0) = k1_setfam_1(k2_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) | ~spl3_5),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f56,f31])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 0.20/0.46    inference(definition_unfolding,[],[f26,f25])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.46  fof(f56,plain,(
% 0.20/0.46    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | ~spl3_5),
% 0.20/0.46    inference(avatar_component_clause,[],[f54])).
% 0.20/0.46  fof(f81,plain,(
% 0.20/0.46    spl3_7 | ~spl3_1 | ~spl3_2 | ~spl3_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f66,f49,f39,f34,f78])).
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    spl3_4 <=> r1_tarski(sK0,k2_relat_1(sK2))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.46  fof(f66,plain,(
% 0.20/0.46    sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0)) | (~spl3_1 | ~spl3_2 | ~spl3_4)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f36,f41,f51,f27])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(flattening,[],[f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.46    inference(ennf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 0.20/0.46  fof(f51,plain,(
% 0.20/0.46    r1_tarski(sK0,k2_relat_1(sK2)) | ~spl3_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f49])).
% 0.20/0.46  fof(f57,plain,(
% 0.20/0.46    spl3_5),
% 0.20/0.46    inference(avatar_split_clause,[],[f20,f54])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.20/0.46    inference(cnf_transformation,[],[f17])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.46    inference(flattening,[],[f9])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.20/0.46    inference(ennf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.20/0.46    inference(negated_conjecture,[],[f7])).
% 0.20/0.46  fof(f7,conjecture,(
% 0.20/0.46    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).
% 0.20/0.46  fof(f52,plain,(
% 0.20/0.46    spl3_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f21,f49])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    r1_tarski(sK0,k2_relat_1(sK2))),
% 0.20/0.46    inference(cnf_transformation,[],[f17])).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    ~spl3_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f22,f44])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ~r1_tarski(sK0,sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f17])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    spl3_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f19,f39])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    v1_funct_1(sK2)),
% 0.20/0.46    inference(cnf_transformation,[],[f17])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    spl3_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f18,f34])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    v1_relat_1(sK2)),
% 0.20/0.46    inference(cnf_transformation,[],[f17])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (28814)------------------------------
% 0.20/0.46  % (28814)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (28814)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (28814)Memory used [KB]: 10746
% 0.20/0.46  % (28814)Time elapsed: 0.011 s
% 0.20/0.46  % (28814)------------------------------
% 0.20/0.46  % (28814)------------------------------
% 0.20/0.46  % (28812)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.46  % (28807)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.46  % (28798)Success in time 0.108 s
%------------------------------------------------------------------------------
