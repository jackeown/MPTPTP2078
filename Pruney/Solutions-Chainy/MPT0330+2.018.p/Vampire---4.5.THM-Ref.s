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
% DateTime   : Thu Dec  3 12:43:01 EST 2020

% Result     : Theorem 1.77s
% Output     : Refutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 142 expanded)
%              Number of leaves         :   15 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :  135 ( 258 expanded)
%              Number of equality atoms :   22 (  71 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3236,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f46,f69,f75,f130,f3233,f3235])).

fof(f3235,plain,
    ( ~ spl6_5
    | spl6_11 ),
    inference(avatar_contradiction_clause,[],[f3234])).

fof(f3234,plain,
    ( $false
    | ~ spl6_5
    | spl6_11 ),
    inference(subsumption_resolution,[],[f3232,f3147])).

fof(f3147,plain,
    ( ! [X2] : r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(X2,sK4)),sK5))
    | ~ spl6_5 ),
    inference(superposition,[],[f280,f84])).

fof(f84,plain,(
    ! [X6,X7,X5] : k3_tarski(k2_tarski(k2_zfmisc_1(X7,X6),k2_zfmisc_1(X5,X6))) = k2_zfmisc_1(k3_tarski(k2_tarski(X5,X7)),X6) ),
    inference(superposition,[],[f34,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f22,f23,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f34,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_tarski(k2_tarski(X0,X1)),X2) = k3_tarski(k2_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
    inference(definition_unfolding,[],[f25,f23,f23])).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f280,plain,
    ( ! [X15] : r1_tarski(sK1,k3_tarski(k2_tarski(k2_zfmisc_1(sK4,sK5),X15)))
    | ~ spl6_5 ),
    inference(superposition,[],[f59,f129])).

fof(f129,plain,
    ( k2_zfmisc_1(sK4,sK5) = k3_tarski(k2_tarski(sK1,k2_zfmisc_1(sK4,sK5)))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl6_5
  <=> k2_zfmisc_1(sK4,sK5) = k3_tarski(k2_tarski(sK1,k2_zfmisc_1(sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f59,plain,(
    ! [X2,X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X2))) ),
    inference(unit_resulting_resolution,[],[f30,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_tarski(k2_tarski(X0,X1)),X2)
      | r1_tarski(X0,X2) ) ),
    inference(definition_unfolding,[],[f27,f23])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f21,f23])).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f3232,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),sK5))
    | spl6_11 ),
    inference(avatar_component_clause,[],[f3230])).

fof(f3230,plain,
    ( spl6_11
  <=> r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f3233,plain,
    ( ~ spl6_11
    | spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f2897,f72,f66,f3230])).

fof(f66,plain,
    ( spl6_3
  <=> r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f72,plain,
    ( spl6_4
  <=> k2_zfmisc_1(sK2,sK3) = k3_tarski(k2_tarski(sK0,k2_zfmisc_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f2897,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),sK5))
    | spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f2828,f1140])).

fof(f1140,plain,
    ( ! [X0] : r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,X0)),sK3))
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f91,f132])).

fof(f132,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(sK2,sK3),X0)
        | r1_tarski(sK0,X0) )
    | ~ spl6_4 ),
    inference(superposition,[],[f35,f74])).

fof(f74,plain,
    ( k2_zfmisc_1(sK2,sK3) = k3_tarski(k2_tarski(sK0,k2_zfmisc_1(sK2,sK3)))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f91,plain,(
    ! [X17,X15,X16] : r1_tarski(k2_zfmisc_1(X15,X16),k2_zfmisc_1(k3_tarski(k2_tarski(X15,X17)),X16)) ),
    inference(superposition,[],[f30,f34])).

fof(f2828,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),sK5))
    | ~ r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),sK3))
    | spl6_3 ),
    inference(resolution,[],[f116,f68])).

fof(f68,plain,
    ( ~ r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5))))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f116,plain,(
    ! [X12,X10,X8,X11,X9] :
      ( r1_tarski(k3_tarski(k2_tarski(X11,X12)),k2_zfmisc_1(X8,k3_tarski(k2_tarski(X9,X10))))
      | ~ r1_tarski(X12,k2_zfmisc_1(X8,X10))
      | ~ r1_tarski(X11,k2_zfmisc_1(X8,X9)) ) ),
    inference(superposition,[],[f36,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ),
    inference(definition_unfolding,[],[f26,f23,f23])).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),k3_tarski(k2_tarski(X1,X3)))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f23,f23])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).

fof(f130,plain,
    ( spl6_5
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f52,f43,f127])).

fof(f43,plain,
    ( spl6_2
  <=> r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f52,plain,
    ( k2_zfmisc_1(sK4,sK5) = k3_tarski(k2_tarski(sK1,k2_zfmisc_1(sK4,sK5)))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f45,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k2_tarski(X0,X1)) = X1 ) ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f45,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f75,plain,
    ( spl6_4
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f51,f38,f72])).

fof(f38,plain,
    ( spl6_1
  <=> r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f51,plain,
    ( k2_zfmisc_1(sK2,sK3) = k3_tarski(k2_tarski(sK0,k2_zfmisc_1(sK2,sK3)))
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f40,f32])).

fof(f40,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f69,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f29,f66])).

fof(f29,plain,(
    ~ r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) ),
    inference(definition_unfolding,[],[f20,f23,f23,f23])).

fof(f20,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f11,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
        & r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
   => ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
      & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
      & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
          & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
       => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
     => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(f46,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f19,f43])).

fof(f19,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f17])).

fof(f41,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f18,f38])).

fof(f18,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:51:53 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.42  % (16384)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.46  % (16369)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.46  % (16374)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (16385)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.48  % (16382)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (16379)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (16373)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (16376)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.49  % (16371)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.49  % (16372)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (16375)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  % (16386)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.49  % (16380)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.49  % (16378)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.49  % (16370)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.50  % (16383)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.51  % (16377)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.52  % (16381)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 1.77/0.58  % (16384)Refutation found. Thanks to Tanya!
% 1.77/0.58  % SZS status Theorem for theBenchmark
% 1.77/0.58  % SZS output start Proof for theBenchmark
% 1.77/0.58  fof(f3236,plain,(
% 1.77/0.58    $false),
% 1.77/0.58    inference(avatar_sat_refutation,[],[f41,f46,f69,f75,f130,f3233,f3235])).
% 1.77/0.58  fof(f3235,plain,(
% 1.77/0.58    ~spl6_5 | spl6_11),
% 1.77/0.58    inference(avatar_contradiction_clause,[],[f3234])).
% 1.77/0.58  fof(f3234,plain,(
% 1.77/0.58    $false | (~spl6_5 | spl6_11)),
% 1.77/0.58    inference(subsumption_resolution,[],[f3232,f3147])).
% 1.77/0.58  fof(f3147,plain,(
% 1.77/0.58    ( ! [X2] : (r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(X2,sK4)),sK5))) ) | ~spl6_5),
% 1.77/0.58    inference(superposition,[],[f280,f84])).
% 1.77/0.58  fof(f84,plain,(
% 1.77/0.58    ( ! [X6,X7,X5] : (k3_tarski(k2_tarski(k2_zfmisc_1(X7,X6),k2_zfmisc_1(X5,X6))) = k2_zfmisc_1(k3_tarski(k2_tarski(X5,X7)),X6)) )),
% 1.77/0.58    inference(superposition,[],[f34,f31])).
% 1.77/0.58  fof(f31,plain,(
% 1.77/0.58    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0))) )),
% 1.77/0.58    inference(definition_unfolding,[],[f22,f23,f23])).
% 1.77/0.58  fof(f23,plain,(
% 1.77/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.77/0.58    inference(cnf_transformation,[],[f6])).
% 1.77/0.58  fof(f6,axiom,(
% 1.77/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.77/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.77/0.58  fof(f22,plain,(
% 1.77/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.77/0.58    inference(cnf_transformation,[],[f1])).
% 1.77/0.58  fof(f1,axiom,(
% 1.77/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.77/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.77/0.58  fof(f34,plain,(
% 1.77/0.58    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_tarski(k2_tarski(X0,X1)),X2) = k3_tarski(k2_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) )),
% 1.77/0.58    inference(definition_unfolding,[],[f25,f23,f23])).
% 1.77/0.58  fof(f25,plain,(
% 1.77/0.58    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 1.77/0.58    inference(cnf_transformation,[],[f7])).
% 1.77/0.58  fof(f7,axiom,(
% 1.77/0.58    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 1.77/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 1.77/0.58  fof(f280,plain,(
% 1.77/0.58    ( ! [X15] : (r1_tarski(sK1,k3_tarski(k2_tarski(k2_zfmisc_1(sK4,sK5),X15)))) ) | ~spl6_5),
% 1.77/0.58    inference(superposition,[],[f59,f129])).
% 1.77/0.58  fof(f129,plain,(
% 1.77/0.58    k2_zfmisc_1(sK4,sK5) = k3_tarski(k2_tarski(sK1,k2_zfmisc_1(sK4,sK5))) | ~spl6_5),
% 1.77/0.58    inference(avatar_component_clause,[],[f127])).
% 1.77/0.58  fof(f127,plain,(
% 1.77/0.58    spl6_5 <=> k2_zfmisc_1(sK4,sK5) = k3_tarski(k2_tarski(sK1,k2_zfmisc_1(sK4,sK5)))),
% 1.77/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.77/0.58  fof(f59,plain,(
% 1.77/0.58    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X2)))) )),
% 1.77/0.58    inference(unit_resulting_resolution,[],[f30,f35])).
% 1.77/0.58  fof(f35,plain,(
% 1.77/0.58    ( ! [X2,X0,X1] : (~r1_tarski(k3_tarski(k2_tarski(X0,X1)),X2) | r1_tarski(X0,X2)) )),
% 1.77/0.58    inference(definition_unfolding,[],[f27,f23])).
% 1.77/0.58  fof(f27,plain,(
% 1.77/0.58    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 1.77/0.58    inference(cnf_transformation,[],[f13])).
% 1.77/0.58  fof(f13,plain,(
% 1.77/0.58    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.77/0.58    inference(ennf_transformation,[],[f2])).
% 1.77/0.58  fof(f2,axiom,(
% 1.77/0.58    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.77/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.77/0.58  fof(f30,plain,(
% 1.77/0.58    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 1.77/0.58    inference(definition_unfolding,[],[f21,f23])).
% 1.77/0.58  fof(f21,plain,(
% 1.77/0.58    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.77/0.58    inference(cnf_transformation,[],[f5])).
% 1.77/0.58  fof(f5,axiom,(
% 1.77/0.58    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.77/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.77/0.58  fof(f3232,plain,(
% 1.77/0.58    ~r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),sK5)) | spl6_11),
% 1.77/0.58    inference(avatar_component_clause,[],[f3230])).
% 1.77/0.58  fof(f3230,plain,(
% 1.77/0.58    spl6_11 <=> r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),sK5))),
% 1.77/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.77/0.58  fof(f3233,plain,(
% 1.77/0.58    ~spl6_11 | spl6_3 | ~spl6_4),
% 1.77/0.58    inference(avatar_split_clause,[],[f2897,f72,f66,f3230])).
% 1.77/0.58  fof(f66,plain,(
% 1.77/0.58    spl6_3 <=> r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5))))),
% 1.77/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.77/0.58  fof(f72,plain,(
% 1.77/0.58    spl6_4 <=> k2_zfmisc_1(sK2,sK3) = k3_tarski(k2_tarski(sK0,k2_zfmisc_1(sK2,sK3)))),
% 1.77/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.77/0.58  fof(f2897,plain,(
% 1.77/0.58    ~r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),sK5)) | (spl6_3 | ~spl6_4)),
% 1.77/0.58    inference(subsumption_resolution,[],[f2828,f1140])).
% 1.77/0.58  fof(f1140,plain,(
% 1.77/0.58    ( ! [X0] : (r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,X0)),sK3))) ) | ~spl6_4),
% 1.77/0.58    inference(unit_resulting_resolution,[],[f91,f132])).
% 1.77/0.58  fof(f132,plain,(
% 1.77/0.58    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(sK2,sK3),X0) | r1_tarski(sK0,X0)) ) | ~spl6_4),
% 1.77/0.58    inference(superposition,[],[f35,f74])).
% 1.77/0.58  fof(f74,plain,(
% 1.77/0.58    k2_zfmisc_1(sK2,sK3) = k3_tarski(k2_tarski(sK0,k2_zfmisc_1(sK2,sK3))) | ~spl6_4),
% 1.77/0.58    inference(avatar_component_clause,[],[f72])).
% 1.77/0.58  fof(f91,plain,(
% 1.77/0.58    ( ! [X17,X15,X16] : (r1_tarski(k2_zfmisc_1(X15,X16),k2_zfmisc_1(k3_tarski(k2_tarski(X15,X17)),X16))) )),
% 1.77/0.58    inference(superposition,[],[f30,f34])).
% 1.77/0.58  fof(f2828,plain,(
% 1.77/0.58    ~r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),sK5)) | ~r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),sK3)) | spl6_3),
% 1.77/0.58    inference(resolution,[],[f116,f68])).
% 1.77/0.58  fof(f68,plain,(
% 1.77/0.58    ~r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) | spl6_3),
% 1.77/0.58    inference(avatar_component_clause,[],[f66])).
% 1.77/0.58  fof(f116,plain,(
% 1.77/0.58    ( ! [X12,X10,X8,X11,X9] : (r1_tarski(k3_tarski(k2_tarski(X11,X12)),k2_zfmisc_1(X8,k3_tarski(k2_tarski(X9,X10)))) | ~r1_tarski(X12,k2_zfmisc_1(X8,X10)) | ~r1_tarski(X11,k2_zfmisc_1(X8,X9))) )),
% 1.77/0.58    inference(superposition,[],[f36,f33])).
% 1.77/0.58  fof(f33,plain,(
% 1.77/0.58    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) )),
% 1.77/0.58    inference(definition_unfolding,[],[f26,f23,f23])).
% 1.77/0.58  fof(f26,plain,(
% 1.77/0.58    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 1.77/0.58    inference(cnf_transformation,[],[f7])).
% 1.77/0.58  fof(f36,plain,(
% 1.77/0.58    ( ! [X2,X0,X3,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),k3_tarski(k2_tarski(X1,X3))) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 1.77/0.58    inference(definition_unfolding,[],[f28,f23,f23])).
% 1.77/0.58  fof(f28,plain,(
% 1.77/0.58    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 1.77/0.58    inference(cnf_transformation,[],[f15])).
% 1.77/0.58  fof(f15,plain,(
% 1.77/0.58    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 1.77/0.58    inference(flattening,[],[f14])).
% 1.77/0.58  fof(f14,plain,(
% 1.77/0.58    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 1.77/0.58    inference(ennf_transformation,[],[f4])).
% 1.77/0.58  fof(f4,axiom,(
% 1.77/0.58    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)))),
% 1.77/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).
% 1.77/0.58  fof(f130,plain,(
% 1.77/0.58    spl6_5 | ~spl6_2),
% 1.77/0.58    inference(avatar_split_clause,[],[f52,f43,f127])).
% 1.77/0.58  fof(f43,plain,(
% 1.77/0.58    spl6_2 <=> r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 1.77/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.77/0.58  fof(f52,plain,(
% 1.77/0.58    k2_zfmisc_1(sK4,sK5) = k3_tarski(k2_tarski(sK1,k2_zfmisc_1(sK4,sK5))) | ~spl6_2),
% 1.77/0.58    inference(unit_resulting_resolution,[],[f45,f32])).
% 1.77/0.58  fof(f32,plain,(
% 1.77/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k2_tarski(X0,X1)) = X1) )),
% 1.77/0.58    inference(definition_unfolding,[],[f24,f23])).
% 1.77/0.58  fof(f24,plain,(
% 1.77/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.77/0.58    inference(cnf_transformation,[],[f12])).
% 1.77/0.58  fof(f12,plain,(
% 1.77/0.58    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.77/0.58    inference(ennf_transformation,[],[f3])).
% 1.77/0.58  fof(f3,axiom,(
% 1.77/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.77/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.77/0.58  fof(f45,plain,(
% 1.77/0.58    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) | ~spl6_2),
% 1.77/0.58    inference(avatar_component_clause,[],[f43])).
% 1.77/0.58  fof(f75,plain,(
% 1.77/0.58    spl6_4 | ~spl6_1),
% 1.77/0.58    inference(avatar_split_clause,[],[f51,f38,f72])).
% 1.77/0.58  fof(f38,plain,(
% 1.77/0.58    spl6_1 <=> r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 1.77/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.77/0.58  fof(f51,plain,(
% 1.77/0.58    k2_zfmisc_1(sK2,sK3) = k3_tarski(k2_tarski(sK0,k2_zfmisc_1(sK2,sK3))) | ~spl6_1),
% 1.77/0.58    inference(unit_resulting_resolution,[],[f40,f32])).
% 1.77/0.58  fof(f40,plain,(
% 1.77/0.58    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) | ~spl6_1),
% 1.77/0.58    inference(avatar_component_clause,[],[f38])).
% 1.77/0.58  fof(f69,plain,(
% 1.77/0.58    ~spl6_3),
% 1.77/0.58    inference(avatar_split_clause,[],[f29,f66])).
% 1.77/0.58  fof(f29,plain,(
% 1.77/0.58    ~r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5))))),
% 1.77/0.58    inference(definition_unfolding,[],[f20,f23,f23,f23])).
% 1.77/0.58  fof(f20,plain,(
% 1.77/0.58    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 1.77/0.58    inference(cnf_transformation,[],[f17])).
% 1.77/0.58  fof(f17,plain,(
% 1.77/0.58    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 1.77/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f11,f16])).
% 1.77/0.58  fof(f16,plain,(
% 1.77/0.58    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => (~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)))),
% 1.77/0.58    introduced(choice_axiom,[])).
% 1.77/0.58  fof(f11,plain,(
% 1.77/0.58    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3)))),
% 1.77/0.58    inference(flattening,[],[f10])).
% 1.77/0.58  fof(f10,plain,(
% 1.77/0.58    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & (r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))))),
% 1.77/0.58    inference(ennf_transformation,[],[f9])).
% 1.77/0.58  fof(f9,negated_conjecture,(
% 1.77/0.58    ~! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 1.77/0.58    inference(negated_conjecture,[],[f8])).
% 1.77/0.58  fof(f8,conjecture,(
% 1.77/0.58    ! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 1.77/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).
% 1.77/0.58  fof(f46,plain,(
% 1.77/0.58    spl6_2),
% 1.77/0.58    inference(avatar_split_clause,[],[f19,f43])).
% 1.77/0.58  fof(f19,plain,(
% 1.77/0.58    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 1.77/0.58    inference(cnf_transformation,[],[f17])).
% 1.77/0.58  fof(f41,plain,(
% 1.77/0.58    spl6_1),
% 1.77/0.58    inference(avatar_split_clause,[],[f18,f38])).
% 1.77/0.58  fof(f18,plain,(
% 1.77/0.58    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 1.77/0.58    inference(cnf_transformation,[],[f17])).
% 1.77/0.58  % SZS output end Proof for theBenchmark
% 1.77/0.58  % (16384)------------------------------
% 1.77/0.58  % (16384)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.58  % (16384)Termination reason: Refutation
% 1.77/0.58  
% 1.77/0.58  % (16384)Memory used [KB]: 15351
% 1.77/0.58  % (16384)Time elapsed: 0.165 s
% 1.77/0.58  % (16384)------------------------------
% 1.77/0.58  % (16384)------------------------------
% 1.77/0.59  % (16368)Success in time 0.23 s
%------------------------------------------------------------------------------
