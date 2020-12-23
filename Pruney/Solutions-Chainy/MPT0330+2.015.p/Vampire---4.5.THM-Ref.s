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
% DateTime   : Thu Dec  3 12:43:01 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 140 expanded)
%              Number of leaves         :   10 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :  102 ( 236 expanded)
%              Number of equality atoms :   16 (  78 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2017,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f625,f2015,f2016])).

fof(f2016,plain,
    ( ~ spl6_2
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f1557,f169,f68])).

fof(f68,plain,
    ( spl6_2
  <=> r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f169,plain,
    ( spl6_10
  <=> r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f1557,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5))))
    | ~ r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) ),
    inference(resolution,[],[f140,f31])).

fof(f31,plain,(
    ~ r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) ),
    inference(definition_unfolding,[],[f21,f24,f24,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f21,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f12,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
        & r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
   => ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
      & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
      & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
          & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
       => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
     => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(f140,plain,(
    ! [X14,X15,X16] :
      ( r1_tarski(k3_tarski(k2_tarski(X16,X15)),X14)
      | ~ r1_tarski(X16,X14)
      | ~ r1_tarski(X15,X14) ) ),
    inference(superposition,[],[f38,f42])).

fof(f42,plain,(
    ! [X2,X3] :
      ( k3_tarski(k2_tarski(X3,X2)) = X3
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f34,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f23,f24,f24])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_tarski(X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f25,f24])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),k3_tarski(k2_tarski(X1,X2)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f24,f24])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
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

fof(f2015,plain,(
    spl6_10 ),
    inference(avatar_contradiction_clause,[],[f2013])).

fof(f2013,plain,
    ( $false
    | spl6_10 ),
    inference(resolution,[],[f2007,f19])).

fof(f19,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f18])).

fof(f2007,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))
    | spl6_10 ),
    inference(resolution,[],[f1905,f225])).

fof(f225,plain,(
    ! [X19,X17,X18,X16] :
      ( r1_tarski(X19,k2_zfmisc_1(k3_tarski(k2_tarski(X16,X18)),X17))
      | ~ r1_tarski(X19,k2_zfmisc_1(X16,X17)) ) ),
    inference(superposition,[],[f51,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_tarski(k2_tarski(X0,X1)),X2) = k3_tarski(k2_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
    inference(definition_unfolding,[],[f26,f24,f24])).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f51,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(X5,k3_tarski(k2_tarski(X4,X3)))
      | ~ r1_tarski(X5,X4) ) ),
    inference(superposition,[],[f37,f33])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f24])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f1905,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),sK3))
    | spl6_10 ),
    inference(resolution,[],[f224,f171])).

fof(f171,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5))))
    | spl6_10 ),
    inference(avatar_component_clause,[],[f169])).

fof(f224,plain,(
    ! [X14,X12,X15,X13] :
      ( r1_tarski(X15,k2_zfmisc_1(X12,k3_tarski(k2_tarski(X13,X14))))
      | ~ r1_tarski(X15,k2_zfmisc_1(X12,X13)) ) ),
    inference(superposition,[],[f51,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ),
    inference(definition_unfolding,[],[f27,f24,f24])).

fof(f27,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f625,plain,(
    spl6_2 ),
    inference(avatar_contradiction_clause,[],[f623])).

fof(f623,plain,
    ( $false
    | spl6_2 ),
    inference(resolution,[],[f619,f20])).

fof(f20,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f18])).

fof(f619,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    | spl6_2 ),
    inference(resolution,[],[f470,f124])).

fof(f124,plain,(
    ! [X14,X17,X15,X16] :
      ( r1_tarski(X17,k2_zfmisc_1(k3_tarski(k2_tarski(X14,X16)),X15))
      | ~ r1_tarski(X17,k2_zfmisc_1(X16,X15)) ) ),
    inference(superposition,[],[f37,f36])).

fof(f470,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),sK5))
    | spl6_2 ),
    inference(resolution,[],[f106,f70])).

fof(f70,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5))))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f106,plain,(
    ! [X14,X12,X15,X13] :
      ( r1_tarski(X15,k2_zfmisc_1(X12,k3_tarski(k2_tarski(X13,X14))))
      | ~ r1_tarski(X15,k2_zfmisc_1(X12,X14)) ) ),
    inference(superposition,[],[f37,f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:00:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (21995)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.46  % (21990)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (21996)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (21994)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.47  % (21986)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (21987)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (21998)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (21988)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (22001)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (22003)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.48  % (21991)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (21992)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (21993)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (22000)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (21999)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (21989)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (21997)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.50  % (22002)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.39/0.54  % (21990)Refutation found. Thanks to Tanya!
% 1.39/0.54  % SZS status Theorem for theBenchmark
% 1.39/0.54  % SZS output start Proof for theBenchmark
% 1.39/0.54  fof(f2017,plain,(
% 1.39/0.54    $false),
% 1.39/0.54    inference(avatar_sat_refutation,[],[f625,f2015,f2016])).
% 1.39/0.54  fof(f2016,plain,(
% 1.39/0.54    ~spl6_2 | ~spl6_10),
% 1.39/0.54    inference(avatar_split_clause,[],[f1557,f169,f68])).
% 1.39/0.54  fof(f68,plain,(
% 1.39/0.54    spl6_2 <=> r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5))))),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.39/0.54  fof(f169,plain,(
% 1.39/0.54    spl6_10 <=> r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5))))),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.39/0.54  fof(f1557,plain,(
% 1.39/0.54    ~r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) | ~r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5))))),
% 1.39/0.54    inference(resolution,[],[f140,f31])).
% 1.39/0.54  fof(f31,plain,(
% 1.39/0.54    ~r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5))))),
% 1.39/0.54    inference(definition_unfolding,[],[f21,f24,f24,f24])).
% 1.39/0.54  fof(f24,plain,(
% 1.39/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.39/0.54    inference(cnf_transformation,[],[f7])).
% 1.39/0.54  fof(f7,axiom,(
% 1.39/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.39/0.54  fof(f21,plain,(
% 1.39/0.54    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 1.39/0.54    inference(cnf_transformation,[],[f18])).
% 1.39/0.54  fof(f18,plain,(
% 1.39/0.54    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 1.39/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f12,f17])).
% 1.39/0.54  fof(f17,plain,(
% 1.39/0.54    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => (~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)))),
% 1.39/0.54    introduced(choice_axiom,[])).
% 1.39/0.54  fof(f12,plain,(
% 1.39/0.54    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3)))),
% 1.39/0.54    inference(flattening,[],[f11])).
% 1.39/0.54  fof(f11,plain,(
% 1.39/0.54    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & (r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))))),
% 1.39/0.54    inference(ennf_transformation,[],[f10])).
% 1.39/0.54  fof(f10,negated_conjecture,(
% 1.39/0.54    ~! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 1.39/0.54    inference(negated_conjecture,[],[f9])).
% 1.39/0.54  fof(f9,conjecture,(
% 1.39/0.54    ! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).
% 1.39/0.54  fof(f140,plain,(
% 1.39/0.54    ( ! [X14,X15,X16] : (r1_tarski(k3_tarski(k2_tarski(X16,X15)),X14) | ~r1_tarski(X16,X14) | ~r1_tarski(X15,X14)) )),
% 1.39/0.54    inference(superposition,[],[f38,f42])).
% 1.39/0.54  fof(f42,plain,(
% 1.39/0.54    ( ! [X2,X3] : (k3_tarski(k2_tarski(X3,X2)) = X3 | ~r1_tarski(X2,X3)) )),
% 1.39/0.54    inference(superposition,[],[f34,f33])).
% 1.39/0.54  fof(f33,plain,(
% 1.39/0.54    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0))) )),
% 1.39/0.54    inference(definition_unfolding,[],[f23,f24,f24])).
% 1.39/0.54  fof(f23,plain,(
% 1.39/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f1])).
% 1.39/0.54  fof(f1,axiom,(
% 1.39/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.39/0.54  fof(f34,plain,(
% 1.39/0.54    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 1.39/0.54    inference(definition_unfolding,[],[f25,f24])).
% 1.39/0.54  fof(f25,plain,(
% 1.39/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f13])).
% 1.39/0.54  fof(f13,plain,(
% 1.39/0.54    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.39/0.54    inference(ennf_transformation,[],[f4])).
% 1.39/0.54  fof(f4,axiom,(
% 1.39/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.39/0.54  fof(f38,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),k3_tarski(k2_tarski(X1,X2))) | ~r1_tarski(X0,X1)) )),
% 1.39/0.54    inference(definition_unfolding,[],[f29,f24,f24])).
% 1.39/0.54  fof(f29,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f15])).
% 1.39/0.54  fof(f15,plain,(
% 1.39/0.54    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 1.39/0.54    inference(ennf_transformation,[],[f6])).
% 1.39/0.54  fof(f6,axiom,(
% 1.39/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).
% 1.39/0.54  fof(f2015,plain,(
% 1.39/0.54    spl6_10),
% 1.39/0.54    inference(avatar_contradiction_clause,[],[f2013])).
% 1.39/0.54  fof(f2013,plain,(
% 1.39/0.54    $false | spl6_10),
% 1.39/0.54    inference(resolution,[],[f2007,f19])).
% 1.39/0.54  fof(f19,plain,(
% 1.39/0.54    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 1.39/0.54    inference(cnf_transformation,[],[f18])).
% 1.39/0.54  fof(f2007,plain,(
% 1.39/0.54    ~r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) | spl6_10),
% 1.39/0.54    inference(resolution,[],[f1905,f225])).
% 1.39/0.54  fof(f225,plain,(
% 1.39/0.54    ( ! [X19,X17,X18,X16] : (r1_tarski(X19,k2_zfmisc_1(k3_tarski(k2_tarski(X16,X18)),X17)) | ~r1_tarski(X19,k2_zfmisc_1(X16,X17))) )),
% 1.39/0.54    inference(superposition,[],[f51,f36])).
% 1.39/0.54  fof(f36,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_tarski(k2_tarski(X0,X1)),X2) = k3_tarski(k2_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) )),
% 1.39/0.54    inference(definition_unfolding,[],[f26,f24,f24])).
% 1.39/0.54  fof(f26,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 1.39/0.54    inference(cnf_transformation,[],[f8])).
% 1.39/0.54  fof(f8,axiom,(
% 1.39/0.54    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 1.39/0.54  fof(f51,plain,(
% 1.39/0.54    ( ! [X4,X5,X3] : (r1_tarski(X5,k3_tarski(k2_tarski(X4,X3))) | ~r1_tarski(X5,X4)) )),
% 1.39/0.54    inference(superposition,[],[f37,f33])).
% 1.39/0.54  fof(f37,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) | ~r1_tarski(X0,X1)) )),
% 1.39/0.54    inference(definition_unfolding,[],[f28,f24])).
% 1.39/0.54  fof(f28,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f14])).
% 1.39/0.54  fof(f14,plain,(
% 1.39/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.39/0.54    inference(ennf_transformation,[],[f2])).
% 1.39/0.54  fof(f2,axiom,(
% 1.39/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 1.39/0.54  fof(f1905,plain,(
% 1.39/0.54    ~r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),sK3)) | spl6_10),
% 1.39/0.54    inference(resolution,[],[f224,f171])).
% 1.39/0.54  fof(f171,plain,(
% 1.39/0.54    ~r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) | spl6_10),
% 1.39/0.54    inference(avatar_component_clause,[],[f169])).
% 1.39/0.54  fof(f224,plain,(
% 1.39/0.54    ( ! [X14,X12,X15,X13] : (r1_tarski(X15,k2_zfmisc_1(X12,k3_tarski(k2_tarski(X13,X14)))) | ~r1_tarski(X15,k2_zfmisc_1(X12,X13))) )),
% 1.39/0.54    inference(superposition,[],[f51,f35])).
% 1.39/0.54  fof(f35,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) )),
% 1.39/0.54    inference(definition_unfolding,[],[f27,f24,f24])).
% 1.39/0.54  fof(f27,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 1.39/0.54    inference(cnf_transformation,[],[f8])).
% 1.39/0.54  fof(f625,plain,(
% 1.39/0.54    spl6_2),
% 1.39/0.54    inference(avatar_contradiction_clause,[],[f623])).
% 1.39/0.54  fof(f623,plain,(
% 1.39/0.54    $false | spl6_2),
% 1.39/0.54    inference(resolution,[],[f619,f20])).
% 1.39/0.54  fof(f20,plain,(
% 1.39/0.54    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 1.39/0.54    inference(cnf_transformation,[],[f18])).
% 1.39/0.54  fof(f619,plain,(
% 1.39/0.54    ~r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) | spl6_2),
% 1.39/0.54    inference(resolution,[],[f470,f124])).
% 1.39/0.54  fof(f124,plain,(
% 1.39/0.54    ( ! [X14,X17,X15,X16] : (r1_tarski(X17,k2_zfmisc_1(k3_tarski(k2_tarski(X14,X16)),X15)) | ~r1_tarski(X17,k2_zfmisc_1(X16,X15))) )),
% 1.39/0.54    inference(superposition,[],[f37,f36])).
% 1.39/0.54  fof(f470,plain,(
% 1.39/0.54    ~r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),sK5)) | spl6_2),
% 1.39/0.54    inference(resolution,[],[f106,f70])).
% 1.39/0.54  fof(f70,plain,(
% 1.39/0.54    ~r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) | spl6_2),
% 1.39/0.54    inference(avatar_component_clause,[],[f68])).
% 1.39/0.54  fof(f106,plain,(
% 1.39/0.54    ( ! [X14,X12,X15,X13] : (r1_tarski(X15,k2_zfmisc_1(X12,k3_tarski(k2_tarski(X13,X14)))) | ~r1_tarski(X15,k2_zfmisc_1(X12,X14))) )),
% 1.39/0.54    inference(superposition,[],[f37,f35])).
% 1.39/0.54  % SZS output end Proof for theBenchmark
% 1.39/0.54  % (21990)------------------------------
% 1.39/0.54  % (21990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (21990)Termination reason: Refutation
% 1.39/0.54  
% 1.39/0.54  % (21990)Memory used [KB]: 7291
% 1.39/0.54  % (21990)Time elapsed: 0.116 s
% 1.39/0.54  % (21990)------------------------------
% 1.39/0.54  % (21990)------------------------------
% 1.39/0.54  % (21985)Success in time 0.187 s
%------------------------------------------------------------------------------
