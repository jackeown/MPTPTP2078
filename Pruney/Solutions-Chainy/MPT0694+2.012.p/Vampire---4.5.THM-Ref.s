%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:01 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 122 expanded)
%              Number of leaves         :   14 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :  144 ( 258 expanded)
%              Number of equality atoms :   10 (  32 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f126,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f51,f57,f118,f120,f125])).

fof(f125,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | spl3_5 ),
    inference(subsumption_resolution,[],[f121,f89])).

fof(f89,plain,
    ( ! [X0,X1] : r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))),k9_relat_1(sK2,X1))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f73,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k1_setfam_1(k2_tarski(X1,X0)))
      | r1_tarski(X2,X0) ) ),
    inference(superposition,[],[f31,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2)))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f23])).

fof(f23,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f73,plain,
    ( ! [X0,X1] : r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))),k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f36,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))),k1_setfam_1(k2_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f25,f23,f23])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).

fof(f36,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f121,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,k10_relat_1(sK2,sK1)))
    | ~ spl3_1
    | ~ spl3_2
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f113,f85])).

fof(f85,plain,
    ( ! [X6,X7] :
        ( ~ r1_tarski(X7,k9_relat_1(sK2,k10_relat_1(sK2,X6)))
        | r1_tarski(X7,X6) )
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(superposition,[],[f31,f71])).

fof(f71,plain,
    ( ! [X0] : k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k1_setfam_1(k2_tarski(X0,k9_relat_1(sK2,k1_relat_1(sK2))))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f36,f41,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(X0,k9_relat_1(X1,k1_relat_1(X1))))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

fof(f41,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl3_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f113,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))),sK1)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl3_5
  <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f120,plain,
    ( ~ spl3_1
    | spl3_6 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | ~ spl3_1
    | spl3_6 ),
    inference(subsumption_resolution,[],[f117,f90])).

fof(f90,plain,
    ( ! [X0,X1] : r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))),k9_relat_1(sK2,X0))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f73,f31])).

fof(f117,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl3_6
  <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f118,plain,
    ( ~ spl3_5
    | ~ spl3_6
    | spl3_4 ),
    inference(avatar_split_clause,[],[f62,f54,f115,f111])).

fof(f54,plain,
    ( spl3_4
  <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_tarski(sK1,k9_relat_1(sK2,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f62,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0))
    | ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))),sK1)
    | spl3_4 ),
    inference(resolution,[],[f32,f56])).

fof(f56,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_tarski(sK1,k9_relat_1(sK2,sK0))))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f27,f23])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f57,plain,
    ( ~ spl3_4
    | spl3_3 ),
    inference(avatar_split_clause,[],[f52,f48,f54])).

fof(f48,plain,
    ( spl3_3
  <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_tarski(k9_relat_1(sK2,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f52,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_tarski(sK1,k9_relat_1(sK2,sK0))))
    | spl3_3 ),
    inference(forward_demodulation,[],[f50,f22])).

fof(f50,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_tarski(k9_relat_1(sK2,sK0),sK1)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f51,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f28,f48])).

fof(f28,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_tarski(k9_relat_1(sK2,sK0),sK1))) ),
    inference(definition_unfolding,[],[f21,f23,f23])).

fof(f21,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_funct_1)).

fof(f42,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f20,f39])).

fof(f20,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f37,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f19,f34])).

fof(f19,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:58:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (7370)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.45  % (7362)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (7359)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.46  % (7363)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (7373)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.46  % (7371)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.46  % (7358)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.46  % (7369)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.47  % (7364)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (7365)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.47  % (7361)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (7373)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f126,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f37,f42,f51,f57,f118,f120,f125])).
% 0.20/0.47  fof(f125,plain,(
% 0.20/0.47    ~spl3_1 | ~spl3_2 | spl3_5),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f124])).
% 0.20/0.47  fof(f124,plain,(
% 0.20/0.47    $false | (~spl3_1 | ~spl3_2 | spl3_5)),
% 0.20/0.47    inference(subsumption_resolution,[],[f121,f89])).
% 0.20/0.47  fof(f89,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))),k9_relat_1(sK2,X1))) ) | ~spl3_1),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f73,f43])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X2,k1_setfam_1(k2_tarski(X1,X0))) | r1_tarski(X2,X0)) )),
% 0.20/0.47    inference(superposition,[],[f31,f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) | r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f26,f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))),k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))))) ) | ~spl3_1),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f36,f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))),k1_setfam_1(k2_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) | ~v1_relat_1(X2)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f25,f23,f23])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) | ~v1_relat_1(X2))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    v1_relat_1(sK2) | ~spl3_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    spl3_1 <=> v1_relat_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.47  fof(f121,plain,(
% 0.20/0.47    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,k10_relat_1(sK2,sK1))) | (~spl3_1 | ~spl3_2 | spl3_5)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f113,f85])).
% 0.20/0.47  fof(f85,plain,(
% 0.20/0.47    ( ! [X6,X7] : (~r1_tarski(X7,k9_relat_1(sK2,k10_relat_1(sK2,X6))) | r1_tarski(X7,X6)) ) | (~spl3_1 | ~spl3_2)),
% 0.20/0.47    inference(superposition,[],[f31,f71])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k1_setfam_1(k2_tarski(X0,k9_relat_1(sK2,k1_relat_1(sK2))))) ) | (~spl3_1 | ~spl3_2)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f36,f41,f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_funct_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(X0,k9_relat_1(X1,k1_relat_1(X1)))) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f24,f23])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    v1_funct_1(sK2) | ~spl3_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f39])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    spl3_2 <=> v1_funct_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.47  fof(f113,plain,(
% 0.20/0.47    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))),sK1) | spl3_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f111])).
% 0.20/0.47  fof(f111,plain,(
% 0.20/0.47    spl3_5 <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))),sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.47  fof(f120,plain,(
% 0.20/0.47    ~spl3_1 | spl3_6),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f119])).
% 0.20/0.47  fof(f119,plain,(
% 0.20/0.47    $false | (~spl3_1 | spl3_6)),
% 0.20/0.47    inference(subsumption_resolution,[],[f117,f90])).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))),k9_relat_1(sK2,X0))) ) | ~spl3_1),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f73,f31])).
% 0.20/0.47  fof(f117,plain,(
% 0.20/0.47    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0)) | spl3_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f115])).
% 0.20/0.47  fof(f115,plain,(
% 0.20/0.47    spl3_6 <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.47  fof(f118,plain,(
% 0.20/0.47    ~spl3_5 | ~spl3_6 | spl3_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f62,f54,f115,f111])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    spl3_4 <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_tarski(sK1,k9_relat_1(sK2,sK0))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0)) | ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))),sK1) | spl3_4),
% 0.20/0.47    inference(resolution,[],[f32,f56])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_tarski(sK1,k9_relat_1(sK2,sK0)))) | spl3_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f54])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f27,f23])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.47    inference(flattening,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    ~spl3_4 | spl3_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f52,f48,f54])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    spl3_3 <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_tarski(k9_relat_1(sK2,sK0),sK1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_tarski(sK1,k9_relat_1(sK2,sK0)))) | spl3_3),
% 0.20/0.47    inference(forward_demodulation,[],[f50,f22])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_tarski(k9_relat_1(sK2,sK0),sK1))) | spl3_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f48])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    ~spl3_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f28,f48])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_tarski(k9_relat_1(sK2,sK0),sK1)))),
% 0.20/0.47    inference(definition_unfolding,[],[f21,f23,f23])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.47    inference(flattening,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 0.20/0.47    inference(negated_conjecture,[],[f7])).
% 0.20/0.47  fof(f7,conjecture,(
% 0.20/0.47    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_funct_1)).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    spl3_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f20,f39])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    v1_funct_1(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    spl3_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f19,f34])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    v1_relat_1(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (7373)------------------------------
% 0.20/0.47  % (7373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (7373)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (7373)Memory used [KB]: 10746
% 0.20/0.47  % (7373)Time elapsed: 0.011 s
% 0.20/0.47  % (7373)------------------------------
% 0.20/0.47  % (7373)------------------------------
% 0.20/0.47  % (7372)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (7368)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.47  % (7357)Success in time 0.118 s
%------------------------------------------------------------------------------
