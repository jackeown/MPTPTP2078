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
% DateTime   : Thu Dec  3 12:53:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 102 expanded)
%              Number of leaves         :   16 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :  136 ( 214 expanded)
%              Number of equality atoms :   34 (  45 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f438,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f47,f52,f104,f239,f437])).

fof(f437,plain,
    ( ~ spl2_1
    | spl2_3
    | ~ spl2_8 ),
    inference(avatar_contradiction_clause,[],[f436])).

fof(f436,plain,
    ( $false
    | ~ spl2_1
    | spl2_3
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f435,f51])).

fof(f51,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl2_3
  <=> r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f435,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | ~ spl2_1
    | ~ spl2_8 ),
    inference(superposition,[],[f240,f238])).

fof(f238,plain,
    ( sK0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl2_8
  <=> sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f240,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(sK1,k9_relat_1(sK1,X0)))
    | ~ spl2_1 ),
    inference(superposition,[],[f126,f73])).

fof(f73,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0))
    | ~ spl2_1 ),
    inference(backward_demodulation,[],[f65,f68])).

fof(f68,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f41,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f41,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f65,plain,
    ( ! [X0] : k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0))
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f53,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f53,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK1,X0))
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f41,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f126,plain,
    ( ! [X0,X1] : r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),k10_relat_1(sK1,X1))
    | ~ spl2_1 ),
    inference(superposition,[],[f54,f79])).

fof(f79,plain,
    ( ! [X0,X1] : k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(sK1,X1)))
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f41,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f33,f28])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0) ),
    inference(superposition,[],[f34,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f26,f28])).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f239,plain,
    ( spl2_8
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f227,f101,f39,f236])).

fof(f101,plain,
    ( spl2_5
  <=> sK0 = k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f227,plain,
    ( sK0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(superposition,[],[f118,f103])).

fof(f103,plain,
    ( sK0 = k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1)))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f118,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1)))
    | ~ spl2_1 ),
    inference(superposition,[],[f74,f27])).

fof(f74,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f41,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f31,f28])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f104,plain,
    ( spl2_5
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f59,f44,f101])).

fof(f44,plain,
    ( spl2_2
  <=> r1_tarski(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f59,plain,
    ( sK0 = k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1)))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f46,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f32,f28])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f46,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f52,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f24,f49])).

fof(f24,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f47,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f23,f44])).

fof(f23,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f42,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f22,f39])).

fof(f22,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).
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
% 0.14/0.34  % DateTime   : Tue Dec  1 14:24:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (30331)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.44  % (30331)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f438,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f42,f47,f52,f104,f239,f437])).
% 0.21/0.44  fof(f437,plain,(
% 0.21/0.44    ~spl2_1 | spl2_3 | ~spl2_8),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f436])).
% 0.21/0.44  fof(f436,plain,(
% 0.21/0.44    $false | (~spl2_1 | spl2_3 | ~spl2_8)),
% 0.21/0.44    inference(subsumption_resolution,[],[f435,f51])).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) | spl2_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f49])).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    spl2_3 <=> r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.44  fof(f435,plain,(
% 0.21/0.44    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) | (~spl2_1 | ~spl2_8)),
% 0.21/0.44    inference(superposition,[],[f240,f238])).
% 0.21/0.44  fof(f238,plain,(
% 0.21/0.44    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~spl2_8),
% 0.21/0.44    inference(avatar_component_clause,[],[f236])).
% 0.21/0.44  fof(f236,plain,(
% 0.21/0.44    spl2_8 <=> sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.44  fof(f240,plain,(
% 0.21/0.44    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(sK1,k9_relat_1(sK1,X0)))) ) | ~spl2_1),
% 0.21/0.44    inference(superposition,[],[f126,f73])).
% 0.21/0.44  fof(f73,plain,(
% 0.21/0.44    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0))) ) | ~spl2_1),
% 0.21/0.44    inference(backward_demodulation,[],[f65,f68])).
% 0.21/0.44  fof(f68,plain,(
% 0.21/0.44    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)) ) | ~spl2_1),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f41,f30])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    v1_relat_1(sK1) | ~spl2_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f39])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    spl2_1 <=> v1_relat_1(sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.44  fof(f65,plain,(
% 0.21/0.44    ( ! [X0] : (k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0))) ) | ~spl2_1),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f53,f25])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,axiom,(
% 0.21/0.44    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 0.21/0.44  fof(f53,plain,(
% 0.21/0.44    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) ) | ~spl2_1),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f41,f29])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.44  fof(f126,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),k10_relat_1(sK1,X1))) ) | ~spl2_1),
% 0.21/0.44    inference(superposition,[],[f54,f79])).
% 0.21/0.44  fof(f79,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(sK1,X1)))) ) | ~spl2_1),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f41,f37])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1)))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f33,f28])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.21/0.44    inference(ennf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0)) )),
% 0.21/0.44    inference(superposition,[],[f34,f27])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f26,f28])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.44  fof(f239,plain,(
% 0.21/0.44    spl2_8 | ~spl2_1 | ~spl2_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f227,f101,f39,f236])).
% 0.21/0.44  fof(f101,plain,(
% 0.21/0.44    spl2_5 <=> sK0 = k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.44  fof(f227,plain,(
% 0.21/0.44    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) | (~spl2_1 | ~spl2_5)),
% 0.21/0.44    inference(superposition,[],[f118,f103])).
% 0.21/0.44  fof(f103,plain,(
% 0.21/0.44    sK0 = k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) | ~spl2_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f101])).
% 0.21/0.44  fof(f118,plain,(
% 0.21/0.44    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1)))) ) | ~spl2_1),
% 0.21/0.44    inference(superposition,[],[f74,f27])).
% 0.21/0.44  fof(f74,plain,(
% 0.21/0.44    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))) ) | ~spl2_1),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f41,f35])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f31,f28])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.21/0.44  fof(f104,plain,(
% 0.21/0.44    spl2_5 | ~spl2_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f59,f44,f101])).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    spl2_2 <=> r1_tarski(sK0,k1_relat_1(sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.44  fof(f59,plain,(
% 0.21/0.44    sK0 = k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) | ~spl2_2),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f46,f36])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 0.21/0.44    inference(definition_unfolding,[],[f32,f28])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    r1_tarski(sK0,k1_relat_1(sK1)) | ~spl2_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f44])).
% 0.21/0.44  fof(f52,plain,(
% 0.21/0.44    ~spl2_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f24,f49])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 0.21/0.44    inference(cnf_transformation,[],[f21])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 0.21/0.44    inference(flattening,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.21/0.44    inference(negated_conjecture,[],[f10])).
% 0.21/0.44  fof(f10,conjecture,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    spl2_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f23,f44])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.21/0.44    inference(cnf_transformation,[],[f21])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    spl2_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f22,f39])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    v1_relat_1(sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f21])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (30331)------------------------------
% 0.21/0.44  % (30331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (30331)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (30331)Memory used [KB]: 11001
% 0.21/0.44  % (30331)Time elapsed: 0.016 s
% 0.21/0.44  % (30331)------------------------------
% 0.21/0.44  % (30331)------------------------------
% 0.21/0.44  % (30315)Success in time 0.081 s
%------------------------------------------------------------------------------
