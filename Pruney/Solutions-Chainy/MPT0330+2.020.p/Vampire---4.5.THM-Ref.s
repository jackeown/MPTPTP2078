%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:02 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 112 expanded)
%              Number of leaves         :   11 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :  109 ( 214 expanded)
%              Number of equality atoms :   11 (  45 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f915,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f402,f906,f914])).

fof(f914,plain,(
    spl6_6 ),
    inference(avatar_contradiction_clause,[],[f912])).

fof(f912,plain,
    ( $false
    | spl6_6 ),
    inference(resolution,[],[f908,f20])).

fof(f20,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f11,f17])).

fof(f17,plain,
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(f908,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    | spl6_6 ),
    inference(resolution,[],[f425,f205])).

fof(f205,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,k3_tarski(k2_tarski(X2,X1)))) ),
    inference(resolution,[],[f41,f22])).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k4_xboole_0(X3,k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X2))
      | r1_tarski(X3,k2_zfmisc_1(X0,k3_tarski(k2_tarski(X1,X2)))) ) ),
    inference(superposition,[],[f34,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ),
    inference(definition_unfolding,[],[f26,f24,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f27,f24])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f425,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_zfmisc_1(sK4,k3_tarski(k2_tarski(sK3,sK5))))
        | ~ r1_tarski(sK1,X0) )
    | spl6_6 ),
    inference(resolution,[],[f401,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f401,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k2_tarski(sK3,sK5))))
    | spl6_6 ),
    inference(avatar_component_clause,[],[f399])).

fof(f399,plain,
    ( spl6_6
  <=> r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k2_tarski(sK3,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f906,plain,(
    spl6_5 ),
    inference(avatar_contradiction_clause,[],[f904])).

fof(f904,plain,
    ( $false
    | spl6_5 ),
    inference(resolution,[],[f901,f19])).

fof(f19,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f18])).

fof(f901,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))
    | spl6_5 ),
    inference(resolution,[],[f424,f226])).

fof(f226,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X2,k3_tarski(k2_tarski(X1,X0)))) ),
    inference(superposition,[],[f205,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f23,f24,f24])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f424,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5))))
        | ~ r1_tarski(sK0,X0) )
    | spl6_5 ),
    inference(resolution,[],[f397,f28])).

fof(f397,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5))))
    | spl6_5 ),
    inference(avatar_component_clause,[],[f395])).

fof(f395,plain,
    ( spl6_5
  <=> r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f402,plain,
    ( ~ spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f372,f399,f395])).

fof(f372,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k2_tarski(sK3,sK5))))
    | ~ r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5)))) ),
    inference(resolution,[],[f76,f30])).

fof(f30,plain,(
    ~ r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) ),
    inference(definition_unfolding,[],[f21,f24,f24,f24])).

fof(f21,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    inference(cnf_transformation,[],[f18])).

fof(f76,plain,(
    ! [X14,X17,X15,X13,X16] :
      ( r1_tarski(k3_tarski(k2_tarski(X16,X17)),k2_zfmisc_1(k3_tarski(k2_tarski(X13,X15)),X14))
      | ~ r1_tarski(X17,k2_zfmisc_1(X15,X14))
      | ~ r1_tarski(X16,k2_zfmisc_1(X13,X14)) ) ),
    inference(superposition,[],[f35,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_tarski(k2_tarski(X0,X1)),X2) = k3_tarski(k2_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
    inference(definition_unfolding,[],[f25,f24,f24])).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),k3_tarski(k2_tarski(X1,X3)))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f24,f24])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:53:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (14571)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.43  % (14579)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (14572)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (14573)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (14582)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (14574)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (14583)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (14581)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (14575)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (14580)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.50  % (14569)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (14570)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.51  % (14568)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.52  % (14584)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.34/0.52  % (14578)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 1.34/0.52  % (14572)Refutation found. Thanks to Tanya!
% 1.34/0.52  % SZS status Theorem for theBenchmark
% 1.34/0.52  % SZS output start Proof for theBenchmark
% 1.34/0.52  fof(f915,plain,(
% 1.34/0.52    $false),
% 1.34/0.52    inference(avatar_sat_refutation,[],[f402,f906,f914])).
% 1.34/0.52  fof(f914,plain,(
% 1.34/0.52    spl6_6),
% 1.34/0.52    inference(avatar_contradiction_clause,[],[f912])).
% 1.34/0.53  fof(f912,plain,(
% 1.34/0.53    $false | spl6_6),
% 1.34/0.53    inference(resolution,[],[f908,f20])).
% 1.34/0.53  fof(f20,plain,(
% 1.34/0.53    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 1.34/0.53    inference(cnf_transformation,[],[f18])).
% 1.34/0.53  fof(f18,plain,(
% 1.34/0.53    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 1.34/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f11,f17])).
% 1.34/0.53  fof(f17,plain,(
% 1.34/0.53    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => (~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)))),
% 1.34/0.53    introduced(choice_axiom,[])).
% 1.34/0.53  fof(f11,plain,(
% 1.34/0.53    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3)))),
% 1.34/0.53    inference(flattening,[],[f10])).
% 1.34/0.53  fof(f10,plain,(
% 1.34/0.53    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & (r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))))),
% 1.34/0.53    inference(ennf_transformation,[],[f9])).
% 1.34/0.53  fof(f9,negated_conjecture,(
% 1.34/0.53    ~! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 1.34/0.53    inference(negated_conjecture,[],[f8])).
% 1.34/0.53  fof(f8,conjecture,(
% 1.34/0.53    ! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).
% 1.34/0.53  fof(f908,plain,(
% 1.34/0.53    ~r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) | spl6_6),
% 1.34/0.53    inference(resolution,[],[f425,f205])).
% 1.34/0.53  fof(f205,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,k3_tarski(k2_tarski(X2,X1))))) )),
% 1.34/0.53    inference(resolution,[],[f41,f22])).
% 1.34/0.53  fof(f22,plain,(
% 1.34/0.53    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f4])).
% 1.34/0.53  fof(f4,axiom,(
% 1.34/0.53    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.34/0.53  fof(f41,plain,(
% 1.34/0.53    ( ! [X2,X0,X3,X1] : (~r1_tarski(k4_xboole_0(X3,k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X2)) | r1_tarski(X3,k2_zfmisc_1(X0,k3_tarski(k2_tarski(X1,X2))))) )),
% 1.34/0.53    inference(superposition,[],[f34,f32])).
% 1.34/0.53  fof(f32,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) )),
% 1.34/0.53    inference(definition_unfolding,[],[f26,f24,f24])).
% 1.34/0.53  fof(f24,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.34/0.53    inference(cnf_transformation,[],[f6])).
% 1.34/0.53  fof(f6,axiom,(
% 1.34/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.34/0.53  fof(f26,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 1.34/0.53    inference(cnf_transformation,[],[f7])).
% 1.34/0.53  fof(f7,axiom,(
% 1.34/0.53    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 1.34/0.53  fof(f34,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 1.34/0.53    inference(definition_unfolding,[],[f27,f24])).
% 1.34/0.53  fof(f27,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f12])).
% 1.34/0.53  fof(f12,plain,(
% 1.34/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.34/0.53    inference(ennf_transformation,[],[f5])).
% 1.34/0.53  fof(f5,axiom,(
% 1.34/0.53    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 1.34/0.53  fof(f425,plain,(
% 1.34/0.53    ( ! [X0] : (~r1_tarski(X0,k2_zfmisc_1(sK4,k3_tarski(k2_tarski(sK3,sK5)))) | ~r1_tarski(sK1,X0)) ) | spl6_6),
% 1.34/0.53    inference(resolution,[],[f401,f28])).
% 1.34/0.53  fof(f28,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f14])).
% 1.34/0.53  fof(f14,plain,(
% 1.34/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.34/0.53    inference(flattening,[],[f13])).
% 1.34/0.53  fof(f13,plain,(
% 1.34/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.34/0.53    inference(ennf_transformation,[],[f3])).
% 1.34/0.53  fof(f3,axiom,(
% 1.34/0.53    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.34/0.53  fof(f401,plain,(
% 1.34/0.53    ~r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k2_tarski(sK3,sK5)))) | spl6_6),
% 1.34/0.53    inference(avatar_component_clause,[],[f399])).
% 1.34/0.53  fof(f399,plain,(
% 1.34/0.53    spl6_6 <=> r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k2_tarski(sK3,sK5))))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.34/0.53  fof(f906,plain,(
% 1.34/0.53    spl6_5),
% 1.34/0.53    inference(avatar_contradiction_clause,[],[f904])).
% 1.34/0.53  fof(f904,plain,(
% 1.34/0.53    $false | spl6_5),
% 1.34/0.53    inference(resolution,[],[f901,f19])).
% 1.34/0.53  fof(f19,plain,(
% 1.34/0.53    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 1.34/0.53    inference(cnf_transformation,[],[f18])).
% 1.34/0.53  fof(f901,plain,(
% 1.34/0.53    ~r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) | spl6_5),
% 1.34/0.53    inference(resolution,[],[f424,f226])).
% 1.34/0.53  fof(f226,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X2,k3_tarski(k2_tarski(X1,X0))))) )),
% 1.34/0.53    inference(superposition,[],[f205,f31])).
% 1.34/0.53  fof(f31,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0))) )),
% 1.34/0.53    inference(definition_unfolding,[],[f23,f24,f24])).
% 1.34/0.53  fof(f23,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f1])).
% 1.34/0.53  fof(f1,axiom,(
% 1.34/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.34/0.53  fof(f424,plain,(
% 1.34/0.53    ( ! [X0] : (~r1_tarski(X0,k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5)))) | ~r1_tarski(sK0,X0)) ) | spl6_5),
% 1.34/0.53    inference(resolution,[],[f397,f28])).
% 1.34/0.53  fof(f397,plain,(
% 1.34/0.53    ~r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5)))) | spl6_5),
% 1.34/0.53    inference(avatar_component_clause,[],[f395])).
% 1.34/0.53  fof(f395,plain,(
% 1.34/0.53    spl6_5 <=> r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5))))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.34/0.53  fof(f402,plain,(
% 1.34/0.53    ~spl6_5 | ~spl6_6),
% 1.34/0.53    inference(avatar_split_clause,[],[f372,f399,f395])).
% 1.34/0.53  fof(f372,plain,(
% 1.34/0.53    ~r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k2_tarski(sK3,sK5)))) | ~r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5))))),
% 1.34/0.53    inference(resolution,[],[f76,f30])).
% 1.34/0.53  fof(f30,plain,(
% 1.34/0.53    ~r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5))))),
% 1.34/0.53    inference(definition_unfolding,[],[f21,f24,f24,f24])).
% 1.34/0.53  fof(f21,plain,(
% 1.34/0.53    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 1.34/0.53    inference(cnf_transformation,[],[f18])).
% 1.34/0.53  fof(f76,plain,(
% 1.34/0.53    ( ! [X14,X17,X15,X13,X16] : (r1_tarski(k3_tarski(k2_tarski(X16,X17)),k2_zfmisc_1(k3_tarski(k2_tarski(X13,X15)),X14)) | ~r1_tarski(X17,k2_zfmisc_1(X15,X14)) | ~r1_tarski(X16,k2_zfmisc_1(X13,X14))) )),
% 1.34/0.53    inference(superposition,[],[f35,f33])).
% 1.34/0.53  fof(f33,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_tarski(k2_tarski(X0,X1)),X2) = k3_tarski(k2_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) )),
% 1.34/0.53    inference(definition_unfolding,[],[f25,f24,f24])).
% 1.34/0.53  fof(f25,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 1.34/0.53    inference(cnf_transformation,[],[f7])).
% 1.34/0.53  fof(f35,plain,(
% 1.34/0.53    ( ! [X2,X0,X3,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),k3_tarski(k2_tarski(X1,X3))) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 1.34/0.53    inference(definition_unfolding,[],[f29,f24,f24])).
% 1.34/0.53  fof(f29,plain,(
% 1.34/0.53    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f16])).
% 1.34/0.53  fof(f16,plain,(
% 1.34/0.53    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 1.34/0.53    inference(flattening,[],[f15])).
% 1.34/0.53  fof(f15,plain,(
% 1.34/0.53    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 1.34/0.53    inference(ennf_transformation,[],[f2])).
% 1.34/0.53  fof(f2,axiom,(
% 1.34/0.53    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).
% 1.34/0.53  % SZS output end Proof for theBenchmark
% 1.34/0.53  % (14572)------------------------------
% 1.34/0.53  % (14572)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (14572)Termination reason: Refutation
% 1.34/0.53  
% 1.34/0.53  % (14572)Memory used [KB]: 7036
% 1.34/0.53  % (14572)Time elapsed: 0.104 s
% 1.34/0.53  % (14572)------------------------------
% 1.34/0.53  % (14572)------------------------------
% 1.34/0.53  % (14567)Success in time 0.169 s
%------------------------------------------------------------------------------
