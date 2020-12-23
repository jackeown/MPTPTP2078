%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 107 expanded)
%              Number of leaves         :   20 (  48 expanded)
%              Depth                    :    6
%              Number of atoms          :  173 ( 274 expanded)
%              Number of equality atoms :   44 (  71 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f168,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f40,f45,f53,f57,f69,f81,f85,f95,f116,f147,f155,f165])).

fof(f165,plain,
    ( spl2_3
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_14
    | ~ spl2_18
    | ~ spl2_19 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | spl2_3
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_14
    | ~ spl2_18
    | ~ spl2_19 ),
    inference(subsumption_resolution,[],[f150,f162])).

fof(f162,plain,
    ( ! [X0] : k7_relat_1(sK0,X0) = k7_relat_1(sK0,k3_xboole_0(X0,k1_relat_1(sK0)))
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_14
    | ~ spl2_19 ),
    inference(forward_demodulation,[],[f158,f104])).

fof(f104,plain,
    ( ! [X0] : k7_relat_1(sK0,X0) = k3_xboole_0(k7_relat_1(sK0,X0),sK0)
    | ~ spl2_9
    | ~ spl2_11 ),
    inference(unit_resulting_resolution,[],[f84,f68])).

fof(f68,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f84,plain,
    ( ! [X0] : r1_tarski(k7_relat_1(sK0,X0),sK0)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl2_11
  <=> ! [X0] : r1_tarski(k7_relat_1(sK0,X0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f158,plain,
    ( ! [X0] : k3_xboole_0(k7_relat_1(sK0,X0),sK0) = k7_relat_1(sK0,k3_xboole_0(X0,k1_relat_1(sK0)))
    | ~ spl2_14
    | ~ spl2_19 ),
    inference(superposition,[],[f154,f115])).

fof(f115,plain,
    ( sK0 = k7_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl2_14
  <=> sK0 = k7_relat_1(sK0,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f154,plain,
    ( ! [X0,X1] : k7_relat_1(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(sK0,X0),k7_relat_1(sK0,X1))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl2_19
  <=> ! [X1,X0] : k7_relat_1(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(sK0,X0),k7_relat_1(sK0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f150,plain,
    ( k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)))
    | spl2_3
    | ~ spl2_18 ),
    inference(superposition,[],[f44,f146])).

fof(f146,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0)
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl2_18
  <=> ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f44,plain,
    ( k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl2_3
  <=> k7_relat_1(sK0,k1_relat_1(sK1)) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f155,plain,
    ( spl2_19
    | ~ spl2_1
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f96,f93,f32,f153])).

fof(f32,plain,
    ( spl2_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f93,plain,
    ( spl2_12
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f96,plain,
    ( ! [X0,X1] : k7_relat_1(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(sK0,X0),k7_relat_1(sK0,X1))
    | ~ spl2_1
    | ~ spl2_12 ),
    inference(unit_resulting_resolution,[],[f34,f94])).

fof(f94,plain,
    ( ! [X2,X0,X1] :
        ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
        | ~ v1_relat_1(X2) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f93])).

fof(f34,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f147,plain,
    ( spl2_18
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f87,f79,f37,f145])).

fof(f37,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f79,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f87,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0)
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(unit_resulting_resolution,[],[f39,f80])).

fof(f80,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f79])).

fof(f39,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f116,plain,
    ( spl2_14
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f72,f55,f32,f113])).

fof(f55,plain,
    ( spl2_6
  <=> ! [X0] :
        ( k7_relat_1(X0,k1_relat_1(X0)) = X0
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f72,plain,
    ( sK0 = k7_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f34,f56])).

fof(f56,plain,
    ( ! [X0] :
        ( k7_relat_1(X0,k1_relat_1(X0)) = X0
        | ~ v1_relat_1(X0) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f55])).

fof(f95,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f30,f93])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_relat_1)).

fof(f85,plain,
    ( spl2_11
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f70,f51,f32,f83])).

fof(f51,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( r1_tarski(k7_relat_1(X1,X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f70,plain,
    ( ! [X0] : r1_tarski(k7_relat_1(sK0,X0),sK0)
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f34,f52])).

fof(f52,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k7_relat_1(X1,X0),X1)
        | ~ v1_relat_1(X1) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f51])).

fof(f81,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f28,f79])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f69,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f29,f67])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f57,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f23,f55])).

fof(f23,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(f53,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f27,f51])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f45,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f22,f42])).

fof(f22,plain,(
    k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k7_relat_1(X0,k1_relat_1(X1)) != k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k7_relat_1(sK0,k1_relat_1(X1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(X1,k1_relat_1(sK0))))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( k7_relat_1(sK0,k1_relat_1(X1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(X1,k1_relat_1(sK0))))
        & v1_relat_1(X1) )
   => ( k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k7_relat_1(X0,k1_relat_1(X1)) != k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_relat_1)).

fof(f40,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f21,f37])).

fof(f21,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f35,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f20,f32])).

fof(f20,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:58:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (17814)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (17815)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (17816)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (17813)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (17817)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (17816)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f168,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f35,f40,f45,f53,f57,f69,f81,f85,f95,f116,f147,f155,f165])).
% 0.22/0.48  fof(f165,plain,(
% 0.22/0.48    spl2_3 | ~spl2_9 | ~spl2_11 | ~spl2_14 | ~spl2_18 | ~spl2_19),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f163])).
% 0.22/0.48  fof(f163,plain,(
% 0.22/0.48    $false | (spl2_3 | ~spl2_9 | ~spl2_11 | ~spl2_14 | ~spl2_18 | ~spl2_19)),
% 0.22/0.48    inference(subsumption_resolution,[],[f150,f162])).
% 0.22/0.48  fof(f162,plain,(
% 0.22/0.48    ( ! [X0] : (k7_relat_1(sK0,X0) = k7_relat_1(sK0,k3_xboole_0(X0,k1_relat_1(sK0)))) ) | (~spl2_9 | ~spl2_11 | ~spl2_14 | ~spl2_19)),
% 0.22/0.48    inference(forward_demodulation,[],[f158,f104])).
% 0.22/0.48  fof(f104,plain,(
% 0.22/0.48    ( ! [X0] : (k7_relat_1(sK0,X0) = k3_xboole_0(k7_relat_1(sK0,X0),sK0)) ) | (~spl2_9 | ~spl2_11)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f84,f68])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | ~spl2_9),
% 0.22/0.48    inference(avatar_component_clause,[],[f67])).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    spl2_9 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    ( ! [X0] : (r1_tarski(k7_relat_1(sK0,X0),sK0)) ) | ~spl2_11),
% 0.22/0.48    inference(avatar_component_clause,[],[f83])).
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    spl2_11 <=> ! [X0] : r1_tarski(k7_relat_1(sK0,X0),sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.48  fof(f158,plain,(
% 0.22/0.48    ( ! [X0] : (k3_xboole_0(k7_relat_1(sK0,X0),sK0) = k7_relat_1(sK0,k3_xboole_0(X0,k1_relat_1(sK0)))) ) | (~spl2_14 | ~spl2_19)),
% 0.22/0.48    inference(superposition,[],[f154,f115])).
% 0.22/0.48  fof(f115,plain,(
% 0.22/0.48    sK0 = k7_relat_1(sK0,k1_relat_1(sK0)) | ~spl2_14),
% 0.22/0.48    inference(avatar_component_clause,[],[f113])).
% 0.22/0.48  fof(f113,plain,(
% 0.22/0.48    spl2_14 <=> sK0 = k7_relat_1(sK0,k1_relat_1(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.22/0.48  fof(f154,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k7_relat_1(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(sK0,X0),k7_relat_1(sK0,X1))) ) | ~spl2_19),
% 0.22/0.48    inference(avatar_component_clause,[],[f153])).
% 0.22/0.48  fof(f153,plain,(
% 0.22/0.48    spl2_19 <=> ! [X1,X0] : k7_relat_1(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(sK0,X0),k7_relat_1(sK0,X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.22/0.48  fof(f150,plain,(
% 0.22/0.48    k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0))) | (spl2_3 | ~spl2_18)),
% 0.22/0.48    inference(superposition,[],[f44,f146])).
% 0.22/0.48  fof(f146,plain,(
% 0.22/0.48    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0)) ) | ~spl2_18),
% 0.22/0.48    inference(avatar_component_clause,[],[f145])).
% 0.22/0.48  fof(f145,plain,(
% 0.22/0.48    spl2_18 <=> ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))) | spl2_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f42])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    spl2_3 <=> k7_relat_1(sK0,k1_relat_1(sK1)) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.48  fof(f155,plain,(
% 0.22/0.48    spl2_19 | ~spl2_1 | ~spl2_12),
% 0.22/0.48    inference(avatar_split_clause,[],[f96,f93,f32,f153])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    spl2_1 <=> v1_relat_1(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    spl2_12 <=> ! [X1,X0,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.48  fof(f96,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k7_relat_1(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(sK0,X0),k7_relat_1(sK0,X1))) ) | (~spl2_1 | ~spl2_12)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f34,f94])).
% 0.22/0.48  fof(f94,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~v1_relat_1(X2)) ) | ~spl2_12),
% 0.22/0.48    inference(avatar_component_clause,[],[f93])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    v1_relat_1(sK0) | ~spl2_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f32])).
% 0.22/0.48  fof(f147,plain,(
% 0.22/0.48    spl2_18 | ~spl2_2 | ~spl2_10),
% 0.22/0.48    inference(avatar_split_clause,[],[f87,f79,f37,f145])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    spl2_2 <=> v1_relat_1(sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    spl2_10 <=> ! [X1,X0] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.48  fof(f87,plain,(
% 0.22/0.48    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0)) ) | (~spl2_2 | ~spl2_10)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f39,f80])).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) ) | ~spl2_10),
% 0.22/0.48    inference(avatar_component_clause,[],[f79])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    v1_relat_1(sK1) | ~spl2_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f37])).
% 0.22/0.48  fof(f116,plain,(
% 0.22/0.48    spl2_14 | ~spl2_1 | ~spl2_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f72,f55,f32,f113])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    spl2_6 <=> ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    sK0 = k7_relat_1(sK0,k1_relat_1(sK0)) | (~spl2_1 | ~spl2_6)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f34,f56])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) ) | ~spl2_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f55])).
% 0.22/0.48  fof(f95,plain,(
% 0.22/0.48    spl2_12),
% 0.22/0.48    inference(avatar_split_clause,[],[f30,f93])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_relat_1)).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    spl2_11 | ~spl2_1 | ~spl2_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f70,f51,f32,f83])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    spl2_5 <=> ! [X1,X0] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    ( ! [X0] : (r1_tarski(k7_relat_1(sK0,X0),sK0)) ) | (~spl2_1 | ~spl2_5)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f34,f52])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) ) | ~spl2_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f51])).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    spl2_10),
% 0.22/0.48    inference(avatar_split_clause,[],[f28,f79])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    spl2_9),
% 0.22/0.48    inference(avatar_split_clause,[],[f29,f67])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.48  fof(f57,plain,(
% 0.22/0.48    spl2_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f23,f55])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    spl2_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f27,f51])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ~spl2_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f22,f42])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    (k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f18,f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (k7_relat_1(X0,k1_relat_1(X1)) != k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (k7_relat_1(sK0,k1_relat_1(X1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(X1,k1_relat_1(sK0)))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ? [X1] : (k7_relat_1(sK0,k1_relat_1(X1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(X1,k1_relat_1(sK0)))) & v1_relat_1(X1)) => (k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))) & v1_relat_1(sK1))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (k7_relat_1(X0,k1_relat_1(X1)) != k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,negated_conjecture,(
% 0.22/0.48    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))))),
% 0.22/0.48    inference(negated_conjecture,[],[f9])).
% 0.22/0.48  fof(f9,conjecture,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_relat_1)).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    spl2_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f21,f37])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    v1_relat_1(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    spl2_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f20,f32])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    v1_relat_1(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (17816)------------------------------
% 0.22/0.48  % (17816)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (17816)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (17816)Memory used [KB]: 6140
% 0.22/0.48  % (17816)Time elapsed: 0.056 s
% 0.22/0.48  % (17816)------------------------------
% 0.22/0.48  % (17816)------------------------------
% 0.22/0.48  % (17823)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (17810)Success in time 0.117 s
%------------------------------------------------------------------------------
