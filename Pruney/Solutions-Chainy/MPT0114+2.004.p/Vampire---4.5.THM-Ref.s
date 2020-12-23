%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:46 EST 2020

% Result     : Theorem 1.09s
% Output     : Refutation 1.09s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 105 expanded)
%              Number of leaves         :   12 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :  137 ( 268 expanded)
%              Number of equality atoms :   15 (  36 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f141,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f50,f93,f96,f98,f140])).

fof(f140,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f137,f47,f42,f38])).

fof(f38,plain,
    ( spl3_1
  <=> r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f42,plain,
    ( spl3_2
  <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f47,plain,
    ( spl3_3
  <=> r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f137,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))
    | ~ spl3_3 ),
    inference(superposition,[],[f111,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f24,f30,f22])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f23,f22])).

fof(f23,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f111,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,k2_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))
        | r1_tarski(sK0,X0) )
    | ~ spl3_3 ),
    inference(superposition,[],[f103,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f103,plain,
    ( ! [X2] :
        ( ~ r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X2))
        | r1_tarski(sK0,X2) )
    | ~ spl3_3 ),
    inference(superposition,[],[f29,f99])).

fof(f99,plain,
    ( sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ spl3_3 ),
    inference(resolution,[],[f49,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f49,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f98,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_contradiction_clause,[],[f97])).

fof(f97,plain,
    ( $false
    | ~ spl3_1
    | spl3_2 ),
    inference(resolution,[],[f52,f43])).

fof(f43,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f52,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(resolution,[],[f40,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f40,plain,
    ( r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f96,plain,
    ( ~ spl3_1
    | spl3_3 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | ~ spl3_1
    | spl3_3 ),
    inference(resolution,[],[f48,f51])).

fof(f51,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ spl3_1 ),
    inference(resolution,[],[f40,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f48,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f93,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f31,f47,f42,f38])).

fof(f31,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(definition_unfolding,[],[f20,f22,f30])).

fof(f20,plain,
    ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
      | ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2)) )
    & ( ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
        & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) )
      | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
          | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
          | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) )
        & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
            & r1_tarski(X0,k2_xboole_0(X1,X2)) )
          | r1_tarski(X0,k5_xboole_0(X1,X2)) ) )
   => ( ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
        | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
        | ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2)) )
      & ( ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
          & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) )
        | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( r1_tarski(X0,k5_xboole_0(X1,X2))
    <~> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k5_xboole_0(X1,X2))
      <=> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k5_xboole_0(X1,X2))
    <=> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_xboole_1)).

fof(f50,plain,
    ( spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f32,f47,f38])).

fof(f32,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(definition_unfolding,[],[f19,f22,f30])).

fof(f19,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f45,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f33,f42,f38])).

fof(f33,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(definition_unfolding,[],[f18,f30])).

fof(f18,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:20:04 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.36  ipcrm: permission denied for id (1211662336)
% 0.19/0.37  ipcrm: permission denied for id (1211858952)
% 0.19/0.37  ipcrm: permission denied for id (1211957259)
% 0.19/0.38  ipcrm: permission denied for id (1211990028)
% 0.19/0.38  ipcrm: permission denied for id (1212055567)
% 0.19/0.38  ipcrm: permission denied for id (1212088336)
% 0.19/0.38  ipcrm: permission denied for id (1212121105)
% 0.19/0.38  ipcrm: permission denied for id (1212186643)
% 0.19/0.38  ipcrm: permission denied for id (1212219412)
% 0.19/0.39  ipcrm: permission denied for id (1212317719)
% 0.19/0.39  ipcrm: permission denied for id (1212383257)
% 0.19/0.39  ipcrm: permission denied for id (1212416026)
% 0.19/0.39  ipcrm: permission denied for id (1212514331)
% 0.19/0.39  ipcrm: permission denied for id (1212481564)
% 0.19/0.40  ipcrm: permission denied for id (1212547101)
% 0.19/0.40  ipcrm: permission denied for id (1212678177)
% 0.19/0.41  ipcrm: permission denied for id (1212809254)
% 0.19/0.41  ipcrm: permission denied for id (1212973101)
% 0.19/0.42  ipcrm: permission denied for id (1213038639)
% 0.19/0.42  ipcrm: permission denied for id (1213071408)
% 0.19/0.42  ipcrm: permission denied for id (1213104177)
% 0.19/0.42  ipcrm: permission denied for id (1213136946)
% 0.19/0.42  ipcrm: permission denied for id (1213169715)
% 0.19/0.42  ipcrm: permission denied for id (1213268022)
% 0.21/0.43  ipcrm: permission denied for id (1213300791)
% 0.21/0.43  ipcrm: permission denied for id (1213333561)
% 0.21/0.43  ipcrm: permission denied for id (1213366330)
% 0.21/0.43  ipcrm: permission denied for id (1213431868)
% 0.21/0.43  ipcrm: permission denied for id (1213530175)
% 0.21/0.44  ipcrm: permission denied for id (1213595713)
% 0.21/0.44  ipcrm: permission denied for id (1213661251)
% 0.21/0.44  ipcrm: permission denied for id (1213694020)
% 0.21/0.44  ipcrm: permission denied for id (1213792327)
% 0.21/0.45  ipcrm: permission denied for id (1213825096)
% 0.21/0.45  ipcrm: permission denied for id (1213857865)
% 0.21/0.45  ipcrm: permission denied for id (1213956172)
% 0.21/0.45  ipcrm: permission denied for id (1213988941)
% 0.21/0.45  ipcrm: permission denied for id (1214021710)
% 0.21/0.45  ipcrm: permission denied for id (1214054479)
% 0.21/0.46  ipcrm: permission denied for id (1214087251)
% 0.21/0.46  ipcrm: permission denied for id (1214120020)
% 0.21/0.46  ipcrm: permission denied for id (1214152790)
% 0.21/0.46  ipcrm: permission denied for id (1214185560)
% 0.21/0.47  ipcrm: permission denied for id (1214218330)
% 0.21/0.47  ipcrm: permission denied for id (1214251099)
% 0.21/0.47  ipcrm: permission denied for id (1214283868)
% 0.21/0.47  ipcrm: permission denied for id (1214382175)
% 0.21/0.47  ipcrm: permission denied for id (1214447713)
% 0.21/0.48  ipcrm: permission denied for id (1214578789)
% 0.21/0.48  ipcrm: permission denied for id (1214644327)
% 0.21/0.48  ipcrm: permission denied for id (1214709865)
% 0.21/0.49  ipcrm: permission denied for id (1214808172)
% 0.21/0.49  ipcrm: permission denied for id (1214939248)
% 0.21/0.49  ipcrm: permission denied for id (1214972017)
% 0.21/0.49  ipcrm: permission denied for id (1215004786)
% 0.21/0.50  ipcrm: permission denied for id (1215070324)
% 0.21/0.50  ipcrm: permission denied for id (1215103093)
% 0.21/0.50  ipcrm: permission denied for id (1215135862)
% 0.21/0.50  ipcrm: permission denied for id (1215168631)
% 0.21/0.50  ipcrm: permission denied for id (1215201400)
% 0.21/0.50  ipcrm: permission denied for id (1215299707)
% 0.21/0.51  ipcrm: permission denied for id (1215332476)
% 0.21/0.51  ipcrm: permission denied for id (1215430783)
% 0.92/0.62  % (30682)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.92/0.62  % (30670)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.92/0.62  % (30667)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 1.09/0.63  % (30667)Refutation found. Thanks to Tanya!
% 1.09/0.63  % SZS status Theorem for theBenchmark
% 1.09/0.63  % SZS output start Proof for theBenchmark
% 1.09/0.63  fof(f141,plain,(
% 1.09/0.63    $false),
% 1.09/0.63    inference(avatar_sat_refutation,[],[f45,f50,f93,f96,f98,f140])).
% 1.09/0.63  fof(f140,plain,(
% 1.09/0.63    spl3_1 | ~spl3_2 | ~spl3_3),
% 1.09/0.63    inference(avatar_split_clause,[],[f137,f47,f42,f38])).
% 1.09/0.63  fof(f38,plain,(
% 1.09/0.63    spl3_1 <=> r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))),
% 1.09/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.09/0.63  fof(f42,plain,(
% 1.09/0.63    spl3_2 <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 1.09/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.09/0.63  fof(f47,plain,(
% 1.09/0.63    spl3_3 <=> r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 1.09/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.09/0.63  fof(f137,plain,(
% 1.09/0.63    ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) | ~spl3_3),
% 1.09/0.63    inference(superposition,[],[f111,f34])).
% 1.09/0.63  fof(f34,plain,(
% 1.09/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.09/0.63    inference(definition_unfolding,[],[f24,f30,f22])).
% 1.09/0.63  fof(f22,plain,(
% 1.09/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.09/0.63    inference(cnf_transformation,[],[f5])).
% 1.09/0.63  fof(f5,axiom,(
% 1.09/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.09/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.09/0.63  fof(f30,plain,(
% 1.09/0.63    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.09/0.63    inference(definition_unfolding,[],[f23,f22])).
% 1.09/0.63  fof(f23,plain,(
% 1.09/0.63    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.09/0.63    inference(cnf_transformation,[],[f2])).
% 1.09/0.63  fof(f2,axiom,(
% 1.09/0.63    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.09/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).
% 1.09/0.63  fof(f24,plain,(
% 1.09/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.09/0.63    inference(cnf_transformation,[],[f7])).
% 1.09/0.63  fof(f7,axiom,(
% 1.09/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.09/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).
% 1.09/0.63  fof(f111,plain,(
% 1.09/0.63    ( ! [X0] : (~r1_tarski(sK0,k2_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) | r1_tarski(sK0,X0)) ) | ~spl3_3),
% 1.09/0.63    inference(superposition,[],[f103,f21])).
% 1.09/0.63  fof(f21,plain,(
% 1.09/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.09/0.63    inference(cnf_transformation,[],[f1])).
% 1.09/0.63  fof(f1,axiom,(
% 1.09/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.09/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.09/0.63  fof(f103,plain,(
% 1.09/0.63    ( ! [X2] : (~r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X2)) | r1_tarski(sK0,X2)) ) | ~spl3_3),
% 1.09/0.63    inference(superposition,[],[f29,f99])).
% 1.09/0.63  fof(f99,plain,(
% 1.09/0.63    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | ~spl3_3),
% 1.09/0.63    inference(resolution,[],[f49,f25])).
% 1.09/0.63  fof(f25,plain,(
% 1.09/0.63    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.09/0.63    inference(cnf_transformation,[],[f17])).
% 1.09/0.63  fof(f17,plain,(
% 1.09/0.63    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.09/0.63    inference(nnf_transformation,[],[f6])).
% 1.09/0.63  fof(f6,axiom,(
% 1.09/0.63    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.09/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.09/0.63  fof(f49,plain,(
% 1.09/0.63    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | ~spl3_3),
% 1.09/0.63    inference(avatar_component_clause,[],[f47])).
% 1.09/0.63  fof(f29,plain,(
% 1.09/0.63    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 1.09/0.63    inference(cnf_transformation,[],[f12])).
% 1.09/0.63  fof(f12,plain,(
% 1.09/0.63    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.09/0.63    inference(ennf_transformation,[],[f4])).
% 1.09/0.63  fof(f4,axiom,(
% 1.09/0.63    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.09/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 1.09/0.63  fof(f98,plain,(
% 1.09/0.63    ~spl3_1 | spl3_2),
% 1.09/0.63    inference(avatar_contradiction_clause,[],[f97])).
% 1.09/0.63  fof(f97,plain,(
% 1.09/0.63    $false | (~spl3_1 | spl3_2)),
% 1.09/0.63    inference(resolution,[],[f52,f43])).
% 1.09/0.63  fof(f43,plain,(
% 1.09/0.63    ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | spl3_2),
% 1.09/0.63    inference(avatar_component_clause,[],[f42])).
% 1.09/0.63  fof(f52,plain,(
% 1.09/0.63    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_1),
% 1.09/0.63    inference(resolution,[],[f40,f27])).
% 1.09/0.63  fof(f27,plain,(
% 1.09/0.63    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 1.09/0.63    inference(cnf_transformation,[],[f11])).
% 1.09/0.63  fof(f11,plain,(
% 1.09/0.63    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.09/0.63    inference(ennf_transformation,[],[f3])).
% 1.09/0.63  fof(f3,axiom,(
% 1.09/0.63    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.09/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.09/0.63  fof(f40,plain,(
% 1.09/0.63    r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) | ~spl3_1),
% 1.09/0.63    inference(avatar_component_clause,[],[f38])).
% 1.09/0.63  fof(f96,plain,(
% 1.09/0.63    ~spl3_1 | spl3_3),
% 1.09/0.63    inference(avatar_contradiction_clause,[],[f94])).
% 1.09/0.63  fof(f94,plain,(
% 1.09/0.63    $false | (~spl3_1 | spl3_3)),
% 1.09/0.63    inference(resolution,[],[f48,f51])).
% 1.09/0.63  fof(f51,plain,(
% 1.09/0.63    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | ~spl3_1),
% 1.09/0.63    inference(resolution,[],[f40,f28])).
% 1.09/0.63  fof(f28,plain,(
% 1.09/0.63    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 1.09/0.63    inference(cnf_transformation,[],[f11])).
% 1.09/0.63  fof(f48,plain,(
% 1.09/0.63    ~r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | spl3_3),
% 1.09/0.63    inference(avatar_component_clause,[],[f47])).
% 1.09/0.63  fof(f93,plain,(
% 1.09/0.63    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 1.09/0.63    inference(avatar_split_clause,[],[f31,f47,f42,f38])).
% 1.09/0.63  fof(f31,plain,(
% 1.09/0.63    ~r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))),
% 1.09/0.63    inference(definition_unfolding,[],[f20,f22,f30])).
% 1.09/0.63  fof(f20,plain,(
% 1.09/0.63    ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k5_xboole_0(sK1,sK2))),
% 1.09/0.63    inference(cnf_transformation,[],[f16])).
% 1.09/0.63  fof(f16,plain,(
% 1.09/0.63    (~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k5_xboole_0(sK1,sK2))) & ((r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))) | r1_tarski(sK0,k5_xboole_0(sK1,sK2)))),
% 1.09/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).
% 1.09/0.63  fof(f15,plain,(
% 1.09/0.63    ? [X0,X1,X2] : ((~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | r1_tarski(X0,k5_xboole_0(X1,X2)))) => ((~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k5_xboole_0(sK1,sK2))) & ((r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))) | r1_tarski(sK0,k5_xboole_0(sK1,sK2))))),
% 1.09/0.63    introduced(choice_axiom,[])).
% 1.09/0.63  fof(f14,plain,(
% 1.09/0.63    ? [X0,X1,X2] : ((~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | r1_tarski(X0,k5_xboole_0(X1,X2))))),
% 1.09/0.63    inference(flattening,[],[f13])).
% 1.09/0.63  fof(f13,plain,(
% 1.09/0.63    ? [X0,X1,X2] : (((~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | r1_tarski(X0,k5_xboole_0(X1,X2))))),
% 1.09/0.63    inference(nnf_transformation,[],[f10])).
% 1.09/0.63  fof(f10,plain,(
% 1.09/0.63    ? [X0,X1,X2] : (r1_tarski(X0,k5_xboole_0(X1,X2)) <~> (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 1.09/0.63    inference(ennf_transformation,[],[f9])).
% 1.09/0.63  fof(f9,negated_conjecture,(
% 1.09/0.63    ~! [X0,X1,X2] : (r1_tarski(X0,k5_xboole_0(X1,X2)) <=> (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 1.09/0.63    inference(negated_conjecture,[],[f8])).
% 1.09/0.63  fof(f8,conjecture,(
% 1.09/0.63    ! [X0,X1,X2] : (r1_tarski(X0,k5_xboole_0(X1,X2)) <=> (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 1.09/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_xboole_1)).
% 1.09/0.63  fof(f50,plain,(
% 1.09/0.63    spl3_1 | spl3_3),
% 1.09/0.63    inference(avatar_split_clause,[],[f32,f47,f38])).
% 1.09/0.63  fof(f32,plain,(
% 1.09/0.63    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))),
% 1.09/0.63    inference(definition_unfolding,[],[f19,f22,f30])).
% 1.09/0.63  fof(f19,plain,(
% 1.09/0.63    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | r1_tarski(sK0,k5_xboole_0(sK1,sK2))),
% 1.09/0.63    inference(cnf_transformation,[],[f16])).
% 1.09/0.63  fof(f45,plain,(
% 1.09/0.63    spl3_1 | spl3_2),
% 1.09/0.63    inference(avatar_split_clause,[],[f33,f42,f38])).
% 1.09/0.63  fof(f33,plain,(
% 1.09/0.63    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))),
% 1.09/0.63    inference(definition_unfolding,[],[f18,f30])).
% 1.09/0.63  fof(f18,plain,(
% 1.09/0.63    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | r1_tarski(sK0,k5_xboole_0(sK1,sK2))),
% 1.09/0.63    inference(cnf_transformation,[],[f16])).
% 1.09/0.63  % SZS output end Proof for theBenchmark
% 1.09/0.63  % (30667)------------------------------
% 1.09/0.63  % (30667)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.09/0.63  % (30667)Termination reason: Refutation
% 1.09/0.63  
% 1.09/0.63  % (30667)Memory used [KB]: 6140
% 1.09/0.63  % (30667)Time elapsed: 0.059 s
% 1.09/0.63  % (30667)------------------------------
% 1.09/0.63  % (30667)------------------------------
% 1.09/0.63  % (30513)Success in time 0.27 s
%------------------------------------------------------------------------------
