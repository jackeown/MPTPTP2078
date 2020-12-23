%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:01 EST 2020

% Result     : Theorem 2.02s
% Output     : Refutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 412 expanded)
%              Number of leaves         :   13 ( 140 expanded)
%              Depth                    :   10
%              Number of atoms          :  128 ( 540 expanded)
%              Number of equality atoms :   22 ( 313 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1284,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f650,f775,f1274,f1283])).

fof(f1283,plain,
    ( ~ spl6_8
    | ~ spl6_28 ),
    inference(avatar_contradiction_clause,[],[f1275])).

fof(f1275,plain,
    ( $false
    | ~ spl6_8
    | ~ spl6_28 ),
    inference(unit_resulting_resolution,[],[f115,f34,f230,f473,f200])).

fof(f200,plain,(
    ! [X14,X12,X15,X13] :
      ( r1_tarski(k3_tarski(k1_enumset1(X14,X14,X15)),X13)
      | ~ r1_tarski(X15,X13)
      | ~ r1_tarski(X14,X12)
      | ~ r1_tarski(X12,X13) ) ),
    inference(superposition,[],[f41,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f25,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f23,f24])).

fof(f24,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),k3_tarski(k1_enumset1(X1,X1,X3)))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f33,f33])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X3)
      | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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

fof(f473,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK3))
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f472])).

fof(f472,plain,
    ( spl6_28
  <=> r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f230,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,k3_tarski(k1_enumset1(X1,X1,X2)))) ),
    inference(superposition,[],[f35,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ),
    inference(definition_unfolding,[],[f30,f33,f33])).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f21,f33])).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f34,plain,(
    ~ r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) ),
    inference(definition_unfolding,[],[f20,f33,f33,f33])).

fof(f20,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
          & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
       => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
     => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(f115,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5))))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl6_8
  <=> r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f1274,plain,(
    spl6_28 ),
    inference(avatar_contradiction_clause,[],[f1270])).

fof(f1270,plain,
    ( $false
    | spl6_28 ),
    inference(unit_resulting_resolution,[],[f18,f306,f474,f438])).

fof(f438,plain,(
    ! [X35,X36,X34] :
      ( ~ r1_tarski(X36,X34)
      | ~ r1_tarski(X35,X36)
      | r1_tarski(X35,X34) ) ),
    inference(superposition,[],[f70,f355])).

fof(f355,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X0
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X2,X0) ) ),
    inference(resolution,[],[f45,f211])).

fof(f211,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k3_tarski(k1_enumset1(X4,X4,X3)),X4)
      | ~ r1_tarski(X3,X5)
      | ~ r1_tarski(X5,X4) ) ),
    inference(superposition,[],[f93,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X1,X1,X0)) ),
    inference(definition_unfolding,[],[f22,f33,f33])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f93,plain,(
    ! [X10,X11,X9] :
      ( r1_tarski(k3_tarski(k1_enumset1(X11,X11,X10)),X10)
      | ~ r1_tarski(X11,X9)
      | ~ r1_tarski(X9,X10) ) ),
    inference(superposition,[],[f40,f37])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),k3_tarski(k1_enumset1(X1,X1,X2)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f33,f33])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).

fof(f45,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k3_tarski(k1_enumset1(X1,X1,X2)),X1)
      | k3_tarski(k1_enumset1(X1,X1,X2)) = X1 ) ),
    inference(resolution,[],[f28,f35])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f70,plain,(
    ! [X2,X3] : r1_tarski(X2,k3_tarski(k1_enumset1(X3,X3,X2))) ),
    inference(superposition,[],[f35,f36])).

fof(f474,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK3))
    | spl6_28 ),
    inference(avatar_component_clause,[],[f472])).

fof(f306,plain,(
    ! [X4,X2,X3] : r1_tarski(k2_zfmisc_1(X2,X3),k2_zfmisc_1(k3_tarski(k1_enumset1(X2,X2,X4)),X3)) ),
    inference(superposition,[],[f35,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_tarski(k1_enumset1(X0,X0,X1)),X2) = k3_tarski(k1_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
    inference(definition_unfolding,[],[f29,f33,f33])).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f18,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f13])).

fof(f775,plain,
    ( spl6_8
    | ~ spl6_17 ),
    inference(avatar_contradiction_clause,[],[f767])).

fof(f767,plain,
    ( $false
    | spl6_8
    | ~ spl6_17 ),
    inference(unit_resulting_resolution,[],[f116,f315,f160,f438])).

fof(f160,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k1_enumset1(sK3,sK3,sK5))))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl6_17
  <=> r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k1_enumset1(sK3,sK3,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f315,plain,(
    ! [X37,X35,X36] : r1_tarski(k2_zfmisc_1(X37,X36),k2_zfmisc_1(k3_tarski(k1_enumset1(X35,X35,X37)),X36)) ),
    inference(superposition,[],[f70,f39])).

fof(f116,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5))))
    | spl6_8 ),
    inference(avatar_component_clause,[],[f114])).

fof(f650,plain,(
    spl6_17 ),
    inference(avatar_contradiction_clause,[],[f627])).

fof(f627,plain,
    ( $false
    | spl6_17 ),
    inference(unit_resulting_resolution,[],[f19,f161,f239,f438])).

fof(f239,plain,(
    ! [X35,X33,X34] : r1_tarski(k2_zfmisc_1(X33,X35),k2_zfmisc_1(X33,k3_tarski(k1_enumset1(X34,X34,X35)))) ),
    inference(superposition,[],[f70,f38])).

fof(f161,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k1_enumset1(sK3,sK3,sK5))))
    | spl6_17 ),
    inference(avatar_component_clause,[],[f159])).

fof(f19,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:52:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (15384)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.50  % (15376)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.50  % (15376)Refutation not found, incomplete strategy% (15376)------------------------------
% 0.21/0.50  % (15376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (15376)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (15376)Memory used [KB]: 10618
% 0.21/0.50  % (15376)Time elapsed: 0.085 s
% 0.21/0.50  % (15376)------------------------------
% 0.21/0.50  % (15376)------------------------------
% 0.21/0.51  % (15369)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (15374)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (15377)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.52  % (15366)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (15364)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (15360)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (15361)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (15375)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (15385)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.53  % (15368)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (15386)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (15371)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (15383)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (15382)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (15379)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (15362)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (15388)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (15363)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (15365)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (15372)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  % (15378)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (15367)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (15370)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (15381)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (15370)Refutation not found, incomplete strategy% (15370)------------------------------
% 0.21/0.55  % (15370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (15370)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (15370)Memory used [KB]: 10746
% 0.21/0.55  % (15370)Time elapsed: 0.138 s
% 0.21/0.55  % (15370)------------------------------
% 0.21/0.55  % (15370)------------------------------
% 0.21/0.55  % (15373)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (15380)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.56  % (15387)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.56  % (15389)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.56  % (15389)Refutation not found, incomplete strategy% (15389)------------------------------
% 0.21/0.56  % (15389)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (15389)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (15389)Memory used [KB]: 1663
% 0.21/0.56  % (15389)Time elapsed: 0.150 s
% 0.21/0.56  % (15389)------------------------------
% 0.21/0.56  % (15389)------------------------------
% 0.21/0.56  % (15388)Refutation not found, incomplete strategy% (15388)------------------------------
% 0.21/0.56  % (15388)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (15388)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (15388)Memory used [KB]: 10746
% 0.21/0.56  % (15388)Time elapsed: 0.151 s
% 0.21/0.56  % (15388)------------------------------
% 0.21/0.56  % (15388)------------------------------
% 2.02/0.64  % (15373)Refutation found. Thanks to Tanya!
% 2.02/0.64  % SZS status Theorem for theBenchmark
% 2.02/0.64  % SZS output start Proof for theBenchmark
% 2.02/0.64  fof(f1284,plain,(
% 2.02/0.64    $false),
% 2.02/0.64    inference(avatar_sat_refutation,[],[f650,f775,f1274,f1283])).
% 2.02/0.64  fof(f1283,plain,(
% 2.02/0.64    ~spl6_8 | ~spl6_28),
% 2.02/0.64    inference(avatar_contradiction_clause,[],[f1275])).
% 2.02/0.64  fof(f1275,plain,(
% 2.02/0.64    $false | (~spl6_8 | ~spl6_28)),
% 2.02/0.64    inference(unit_resulting_resolution,[],[f115,f34,f230,f473,f200])).
% 2.02/0.64  fof(f200,plain,(
% 2.02/0.64    ( ! [X14,X12,X15,X13] : (r1_tarski(k3_tarski(k1_enumset1(X14,X14,X15)),X13) | ~r1_tarski(X15,X13) | ~r1_tarski(X14,X12) | ~r1_tarski(X12,X13)) )),
% 2.02/0.64    inference(superposition,[],[f41,f37])).
% 2.02/0.64  fof(f37,plain,(
% 2.02/0.64    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 2.02/0.64    inference(definition_unfolding,[],[f25,f33])).
% 2.02/0.64  fof(f33,plain,(
% 2.02/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 2.02/0.64    inference(definition_unfolding,[],[f23,f24])).
% 2.02/0.64  fof(f24,plain,(
% 2.02/0.64    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.02/0.64    inference(cnf_transformation,[],[f7])).
% 2.02/0.64  fof(f7,axiom,(
% 2.02/0.64    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.02/0.64  fof(f23,plain,(
% 2.02/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.02/0.64    inference(cnf_transformation,[],[f8])).
% 2.02/0.64  fof(f8,axiom,(
% 2.02/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.02/0.64  fof(f25,plain,(
% 2.02/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.02/0.64    inference(cnf_transformation,[],[f14])).
% 2.02/0.64  fof(f14,plain,(
% 2.02/0.64    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.02/0.64    inference(ennf_transformation,[],[f3])).
% 2.02/0.64  fof(f3,axiom,(
% 2.02/0.64    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.02/0.64  fof(f41,plain,(
% 2.02/0.64    ( ! [X2,X0,X3,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),k3_tarski(k1_enumset1(X1,X1,X3))) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 2.02/0.64    inference(definition_unfolding,[],[f32,f33,f33])).
% 2.02/0.64  fof(f32,plain,(
% 2.02/0.64    ( ! [X2,X0,X3,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))) )),
% 2.02/0.64    inference(cnf_transformation,[],[f17])).
% 2.02/0.64  fof(f17,plain,(
% 2.02/0.64    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 2.02/0.64    inference(flattening,[],[f16])).
% 2.02/0.64  fof(f16,plain,(
% 2.02/0.64    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 2.02/0.64    inference(ennf_transformation,[],[f4])).
% 2.02/0.64  fof(f4,axiom,(
% 2.02/0.64    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)))),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).
% 2.02/0.64  fof(f473,plain,(
% 2.02/0.64    r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK3)) | ~spl6_28),
% 2.02/0.64    inference(avatar_component_clause,[],[f472])).
% 2.02/0.64  fof(f472,plain,(
% 2.02/0.64    spl6_28 <=> r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK3))),
% 2.02/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 2.02/0.64  fof(f230,plain,(
% 2.02/0.64    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,k3_tarski(k1_enumset1(X1,X1,X2))))) )),
% 2.02/0.64    inference(superposition,[],[f35,f38])).
% 2.02/0.64  fof(f38,plain,(
% 2.02/0.64    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) )),
% 2.02/0.64    inference(definition_unfolding,[],[f30,f33,f33])).
% 2.02/0.64  fof(f30,plain,(
% 2.02/0.64    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 2.02/0.64    inference(cnf_transformation,[],[f9])).
% 2.02/0.64  fof(f9,axiom,(
% 2.02/0.64    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 2.02/0.64  fof(f35,plain,(
% 2.02/0.64    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 2.02/0.64    inference(definition_unfolding,[],[f21,f33])).
% 2.02/0.64  fof(f21,plain,(
% 2.02/0.64    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.02/0.64    inference(cnf_transformation,[],[f5])).
% 2.02/0.64  fof(f5,axiom,(
% 2.02/0.64    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.02/0.64  fof(f34,plain,(
% 2.02/0.64    ~r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5))))),
% 2.02/0.64    inference(definition_unfolding,[],[f20,f33,f33,f33])).
% 2.02/0.64  fof(f20,plain,(
% 2.02/0.64    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 2.02/0.64    inference(cnf_transformation,[],[f13])).
% 2.02/0.64  fof(f13,plain,(
% 2.02/0.64    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3)))),
% 2.02/0.64    inference(flattening,[],[f12])).
% 2.02/0.64  fof(f12,plain,(
% 2.02/0.64    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & (r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))))),
% 2.02/0.64    inference(ennf_transformation,[],[f11])).
% 2.02/0.64  fof(f11,negated_conjecture,(
% 2.02/0.64    ~! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 2.02/0.64    inference(negated_conjecture,[],[f10])).
% 2.02/0.64  fof(f10,conjecture,(
% 2.02/0.64    ! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).
% 2.02/0.64  fof(f115,plain,(
% 2.02/0.64    r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) | ~spl6_8),
% 2.02/0.64    inference(avatar_component_clause,[],[f114])).
% 2.02/0.64  fof(f114,plain,(
% 2.02/0.64    spl6_8 <=> r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5))))),
% 2.02/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 2.02/0.64  fof(f1274,plain,(
% 2.02/0.64    spl6_28),
% 2.02/0.64    inference(avatar_contradiction_clause,[],[f1270])).
% 2.02/0.64  fof(f1270,plain,(
% 2.02/0.64    $false | spl6_28),
% 2.02/0.64    inference(unit_resulting_resolution,[],[f18,f306,f474,f438])).
% 2.02/0.64  fof(f438,plain,(
% 2.02/0.64    ( ! [X35,X36,X34] : (~r1_tarski(X36,X34) | ~r1_tarski(X35,X36) | r1_tarski(X35,X34)) )),
% 2.02/0.64    inference(superposition,[],[f70,f355])).
% 2.02/0.64  fof(f355,plain,(
% 2.02/0.64    ( ! [X2,X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = X0 | ~r1_tarski(X1,X2) | ~r1_tarski(X2,X0)) )),
% 2.02/0.64    inference(resolution,[],[f45,f211])).
% 2.02/0.64  fof(f211,plain,(
% 2.02/0.64    ( ! [X4,X5,X3] : (r1_tarski(k3_tarski(k1_enumset1(X4,X4,X3)),X4) | ~r1_tarski(X3,X5) | ~r1_tarski(X5,X4)) )),
% 2.02/0.64    inference(superposition,[],[f93,f36])).
% 2.02/0.64  fof(f36,plain,(
% 2.02/0.64    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X1,X1,X0))) )),
% 2.02/0.64    inference(definition_unfolding,[],[f22,f33,f33])).
% 2.02/0.64  fof(f22,plain,(
% 2.02/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.02/0.64    inference(cnf_transformation,[],[f1])).
% 2.02/0.64  fof(f1,axiom,(
% 2.02/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.02/0.64  fof(f93,plain,(
% 2.02/0.64    ( ! [X10,X11,X9] : (r1_tarski(k3_tarski(k1_enumset1(X11,X11,X10)),X10) | ~r1_tarski(X11,X9) | ~r1_tarski(X9,X10)) )),
% 2.02/0.64    inference(superposition,[],[f40,f37])).
% 2.02/0.64  fof(f40,plain,(
% 2.02/0.64    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),k3_tarski(k1_enumset1(X1,X1,X2))) | ~r1_tarski(X0,X1)) )),
% 2.02/0.64    inference(definition_unfolding,[],[f31,f33,f33])).
% 2.02/0.64  fof(f31,plain,(
% 2.02/0.64    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))) )),
% 2.02/0.64    inference(cnf_transformation,[],[f15])).
% 2.02/0.64  fof(f15,plain,(
% 2.02/0.64    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 2.02/0.64    inference(ennf_transformation,[],[f6])).
% 2.02/0.64  fof(f6,axiom,(
% 2.02/0.64    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)))),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).
% 2.02/0.64  fof(f45,plain,(
% 2.02/0.64    ( ! [X2,X1] : (~r1_tarski(k3_tarski(k1_enumset1(X1,X1,X2)),X1) | k3_tarski(k1_enumset1(X1,X1,X2)) = X1) )),
% 2.02/0.64    inference(resolution,[],[f28,f35])).
% 2.02/0.64  fof(f28,plain,(
% 2.02/0.64    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 2.02/0.64    inference(cnf_transformation,[],[f2])).
% 2.02/0.64  fof(f2,axiom,(
% 2.02/0.64    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.02/0.64  fof(f70,plain,(
% 2.02/0.64    ( ! [X2,X3] : (r1_tarski(X2,k3_tarski(k1_enumset1(X3,X3,X2)))) )),
% 2.02/0.64    inference(superposition,[],[f35,f36])).
% 2.02/0.64  fof(f474,plain,(
% 2.02/0.64    ~r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK3)) | spl6_28),
% 2.02/0.64    inference(avatar_component_clause,[],[f472])).
% 2.02/0.64  fof(f306,plain,(
% 2.02/0.64    ( ! [X4,X2,X3] : (r1_tarski(k2_zfmisc_1(X2,X3),k2_zfmisc_1(k3_tarski(k1_enumset1(X2,X2,X4)),X3))) )),
% 2.02/0.64    inference(superposition,[],[f35,f39])).
% 2.02/0.64  fof(f39,plain,(
% 2.02/0.64    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_tarski(k1_enumset1(X0,X0,X1)),X2) = k3_tarski(k1_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) )),
% 2.02/0.64    inference(definition_unfolding,[],[f29,f33,f33])).
% 2.02/0.64  fof(f29,plain,(
% 2.02/0.64    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 2.02/0.64    inference(cnf_transformation,[],[f9])).
% 2.02/0.64  fof(f18,plain,(
% 2.02/0.64    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 2.02/0.64    inference(cnf_transformation,[],[f13])).
% 2.02/0.64  fof(f775,plain,(
% 2.02/0.64    spl6_8 | ~spl6_17),
% 2.02/0.64    inference(avatar_contradiction_clause,[],[f767])).
% 2.02/0.64  fof(f767,plain,(
% 2.02/0.64    $false | (spl6_8 | ~spl6_17)),
% 2.02/0.64    inference(unit_resulting_resolution,[],[f116,f315,f160,f438])).
% 2.02/0.64  fof(f160,plain,(
% 2.02/0.64    r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k1_enumset1(sK3,sK3,sK5)))) | ~spl6_17),
% 2.02/0.64    inference(avatar_component_clause,[],[f159])).
% 2.02/0.64  fof(f159,plain,(
% 2.02/0.64    spl6_17 <=> r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k1_enumset1(sK3,sK3,sK5))))),
% 2.02/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 2.02/0.64  fof(f315,plain,(
% 2.02/0.64    ( ! [X37,X35,X36] : (r1_tarski(k2_zfmisc_1(X37,X36),k2_zfmisc_1(k3_tarski(k1_enumset1(X35,X35,X37)),X36))) )),
% 2.02/0.64    inference(superposition,[],[f70,f39])).
% 2.02/0.64  fof(f116,plain,(
% 2.02/0.64    ~r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) | spl6_8),
% 2.02/0.64    inference(avatar_component_clause,[],[f114])).
% 2.02/0.64  fof(f650,plain,(
% 2.02/0.64    spl6_17),
% 2.02/0.64    inference(avatar_contradiction_clause,[],[f627])).
% 2.02/0.64  fof(f627,plain,(
% 2.02/0.64    $false | spl6_17),
% 2.02/0.64    inference(unit_resulting_resolution,[],[f19,f161,f239,f438])).
% 2.02/0.64  fof(f239,plain,(
% 2.02/0.64    ( ! [X35,X33,X34] : (r1_tarski(k2_zfmisc_1(X33,X35),k2_zfmisc_1(X33,k3_tarski(k1_enumset1(X34,X34,X35))))) )),
% 2.02/0.64    inference(superposition,[],[f70,f38])).
% 2.02/0.64  fof(f161,plain,(
% 2.02/0.64    ~r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k1_enumset1(sK3,sK3,sK5)))) | spl6_17),
% 2.02/0.64    inference(avatar_component_clause,[],[f159])).
% 2.02/0.64  fof(f19,plain,(
% 2.02/0.64    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 2.02/0.64    inference(cnf_transformation,[],[f13])).
% 2.02/0.64  % SZS output end Proof for theBenchmark
% 2.02/0.64  % (15373)------------------------------
% 2.02/0.64  % (15373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.02/0.64  % (15373)Termination reason: Refutation
% 2.02/0.64  
% 2.02/0.64  % (15373)Memory used [KB]: 7164
% 2.02/0.64  % (15373)Time elapsed: 0.228 s
% 2.02/0.64  % (15373)------------------------------
% 2.02/0.64  % (15373)------------------------------
% 2.02/0.64  % (15359)Success in time 0.274 s
%------------------------------------------------------------------------------
