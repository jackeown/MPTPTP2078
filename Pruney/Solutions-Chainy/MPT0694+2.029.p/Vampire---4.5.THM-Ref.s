%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 132 expanded)
%              Number of leaves         :   14 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :  145 ( 268 expanded)
%              Number of equality atoms :   11 (  42 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f147,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f43,f56,f62,f138,f140,f146])).

fof(f146,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | spl3_5 ),
    inference(subsumption_resolution,[],[f141,f105])).

fof(f105,plain,
    ( ! [X0,X1] : r1_tarski(k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k9_relat_1(sK2,X1))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f80,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k4_xboole_0(X1,k4_xboole_0(X1,X0)))
      | r1_tarski(X2,X0) ) ),
    inference(superposition,[],[f32,f29])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f22,f23,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f23])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f80,plain,
    ( ! [X0,X1] : r1_tarski(k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f37,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k9_relat_1(X2,X0),k4_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).

fof(f37,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f141,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,k10_relat_1(sK2,sK1)))
    | ~ spl3_1
    | ~ spl3_2
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f133,f94])).

fof(f94,plain,
    ( ! [X4,X5] :
        ( ~ r1_tarski(X5,k9_relat_1(sK2,k10_relat_1(sK2,X4)))
        | r1_tarski(X5,X4) )
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(superposition,[],[f32,f78])).

fof(f78,plain,
    ( ! [X0] : k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2))))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f37,f42,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(f42,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl3_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f133,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl3_5
  <=> r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f140,plain,
    ( ~ spl3_1
    | spl3_6 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | ~ spl3_1
    | spl3_6 ),
    inference(subsumption_resolution,[],[f137,f106])).

fof(f106,plain,
    ( ! [X0,X1] : r1_tarski(k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k9_relat_1(sK2,X0))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f80,f32])).

fof(f137,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl3_6
  <=> r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f138,plain,
    ( ~ spl3_5
    | ~ spl3_6
    | spl3_4 ),
    inference(avatar_split_clause,[],[f67,f59,f135,f131])).

fof(f59,plain,
    ( spl3_4
  <=> r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(sK1,k4_xboole_0(sK1,k9_relat_1(sK2,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f67,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0))
    | ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1)
    | spl3_4 ),
    inference(resolution,[],[f33,f61])).

fof(f61,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(sK1,k4_xboole_0(sK1,k9_relat_1(sK2,sK0))))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f62,plain,
    ( ~ spl3_4
    | spl3_3 ),
    inference(avatar_split_clause,[],[f57,f53,f59])).

fof(f53,plain,
    ( spl3_3
  <=> r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f57,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(sK1,k4_xboole_0(sK1,k9_relat_1(sK2,sK0))))
    | spl3_3 ),
    inference(forward_demodulation,[],[f55,f29])).

fof(f55,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),sK1)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f56,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f28,f53])).

fof(f28,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),sK1))) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_funct_1)).

fof(f43,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f20,f40])).

fof(f20,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f38,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f19,f35])).

fof(f19,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n001.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:28:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (31029)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % (31041)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (31033)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.48  % (31035)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (31030)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.48  % (31044)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.49  % (31036)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  % (31045)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.49  % (31037)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.49  % (31032)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (31043)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.50  % (31042)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.50  % (31034)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (31043)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f147,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f38,f43,f56,f62,f138,f140,f146])).
% 0.20/0.50  fof(f146,plain,(
% 0.20/0.50    ~spl3_1 | ~spl3_2 | spl3_5),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f145])).
% 0.20/0.50  fof(f145,plain,(
% 0.20/0.50    $false | (~spl3_1 | ~spl3_2 | spl3_5)),
% 0.20/0.50    inference(subsumption_resolution,[],[f141,f105])).
% 0.20/0.50  fof(f105,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k9_relat_1(sK2,X1))) ) | ~spl3_1),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f80,f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X2,k4_xboole_0(X1,k4_xboole_0(X1,X0))) | r1_tarski(X2,X0)) )),
% 0.20/0.50    inference(superposition,[],[f32,f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.20/0.50    inference(definition_unfolding,[],[f22,f23,f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f26,f23])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))))) ) | ~spl3_1),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f37,f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k9_relat_1(X2,X0),k4_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) | ~v1_relat_1(X2)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f25,f23,f23])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) | ~v1_relat_1(X2))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    v1_relat_1(sK2) | ~spl3_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    spl3_1 <=> v1_relat_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.50  fof(f141,plain,(
% 0.20/0.50    ~r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,k10_relat_1(sK2,sK1))) | (~spl3_1 | ~spl3_2 | spl3_5)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f133,f94])).
% 0.20/0.50  fof(f94,plain,(
% 0.20/0.50    ( ! [X4,X5] : (~r1_tarski(X5,k9_relat_1(sK2,k10_relat_1(sK2,X4))) | r1_tarski(X5,X4)) ) | (~spl3_1 | ~spl3_2)),
% 0.20/0.50    inference(superposition,[],[f32,f78])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2))))) ) | (~spl3_1 | ~spl3_2)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f37,f42,f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_funct_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f24,f23])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(flattening,[],[f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    v1_funct_1(sK2) | ~spl3_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    spl3_2 <=> v1_funct_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.50  fof(f133,plain,(
% 0.20/0.50    ~r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1) | spl3_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f131])).
% 0.20/0.50  fof(f131,plain,(
% 0.20/0.50    spl3_5 <=> r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.50  fof(f140,plain,(
% 0.20/0.50    ~spl3_1 | spl3_6),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f139])).
% 0.20/0.50  fof(f139,plain,(
% 0.20/0.50    $false | (~spl3_1 | spl3_6)),
% 0.20/0.50    inference(subsumption_resolution,[],[f137,f106])).
% 0.20/0.50  fof(f106,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k9_relat_1(sK2,X0))) ) | ~spl3_1),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f80,f32])).
% 0.20/0.50  fof(f137,plain,(
% 0.20/0.50    ~r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0)) | spl3_6),
% 0.20/0.50    inference(avatar_component_clause,[],[f135])).
% 0.20/0.50  fof(f135,plain,(
% 0.20/0.50    spl3_6 <=> r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.50  fof(f138,plain,(
% 0.20/0.50    ~spl3_5 | ~spl3_6 | spl3_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f67,f59,f135,f131])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    spl3_4 <=> r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(sK1,k4_xboole_0(sK1,k9_relat_1(sK2,sK0))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    ~r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0)) | ~r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1) | spl3_4),
% 0.20/0.50    inference(resolution,[],[f33,f61])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    ~r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(sK1,k4_xboole_0(sK1,k9_relat_1(sK2,sK0)))) | spl3_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f59])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f27,f23])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.50    inference(flattening,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    ~spl3_4 | spl3_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f57,f53,f59])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    spl3_3 <=> r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),sK1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ~r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(sK1,k4_xboole_0(sK1,k9_relat_1(sK2,sK0)))) | spl3_3),
% 0.20/0.50    inference(forward_demodulation,[],[f55,f29])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ~r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),sK1))) | spl3_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f53])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    ~spl3_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f28,f53])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ~r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),sK1)))),
% 0.20/0.50    inference(definition_unfolding,[],[f21,f23,f23])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f10,plain,(
% 0.20/0.50    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.50    inference(flattening,[],[f9])).
% 0.20/0.50  fof(f9,plain,(
% 0.20/0.50    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 0.20/0.50    inference(negated_conjecture,[],[f7])).
% 0.20/0.50  fof(f7,conjecture,(
% 0.20/0.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_funct_1)).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    spl3_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f20,f40])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    v1_funct_1(sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    spl3_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f19,f35])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    v1_relat_1(sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (31043)------------------------------
% 0.20/0.50  % (31043)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (31043)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (31043)Memory used [KB]: 10746
% 0.20/0.50  % (31043)Time elapsed: 0.049 s
% 0.20/0.50  % (31043)------------------------------
% 0.20/0.50  % (31043)------------------------------
% 0.20/0.50  % (31031)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.50  % (31027)Success in time 0.144 s
%------------------------------------------------------------------------------
