%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:50 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 169 expanded)
%              Number of leaves         :   13 (  59 expanded)
%              Depth                    :   15
%              Number of atoms          :   71 ( 183 expanded)
%              Number of equality atoms :   56 ( 165 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2647,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f1232,f2638])).

fof(f2638,plain,(
    spl2_6 ),
    inference(avatar_contradiction_clause,[],[f2637])).

fof(f2637,plain,
    ( $false
    | spl2_6 ),
    inference(subsumption_resolution,[],[f2583,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f2583,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK1,sK0)
    | spl2_6 ),
    inference(superposition,[],[f1231,f2477])).

fof(f2477,plain,(
    ! [X8,X7] : k2_xboole_0(X7,X8) = k2_xboole_0(k4_xboole_0(X7,X8),X8) ),
    inference(backward_demodulation,[],[f569,f2429])).

fof(f2429,plain,(
    ! [X17,X16] : k2_xboole_0(X16,X17) = k2_xboole_0(X16,k4_xboole_0(X17,X16)) ),
    inference(superposition,[],[f571,f67])).

fof(f67,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[],[f34,f32])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f21,f23,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f25,f23])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f571,plain,(
    ! [X12,X13,X11] : k2_xboole_0(X11,X13) = k2_xboole_0(X11,k2_xboole_0(k4_xboole_0(X11,X12),X13)) ),
    inference(forward_demodulation,[],[f544,f423])).

fof(f423,plain,(
    ! [X6,X8,X7] : k2_xboole_0(X6,X8) = k2_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,X7)),k2_xboole_0(X6,X8)) ),
    inference(superposition,[],[f39,f384])).

fof(f384,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(forward_demodulation,[],[f371,f19])).

fof(f19,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f371,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(backward_demodulation,[],[f95,f364])).

fof(f364,plain,(
    ! [X4] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X4) ),
    inference(backward_demodulation,[],[f170,f354])).

fof(f354,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X1)) = X0 ),
    inference(superposition,[],[f69,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f29,f23])).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f69,plain,(
    ! [X4,X5] : k2_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,k4_xboole_0(X4,X5))) = X4 ),
    inference(superposition,[],[f34,f33])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f170,plain,(
    ! [X4] : k4_xboole_0(k1_xboole_0,X4) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X4,X4)) ),
    inference(superposition,[],[f33,f48])).

fof(f48,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f32,f19])).

fof(f95,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f35,f19])).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(superposition,[],[f28,f22])).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f544,plain,(
    ! [X12,X13,X11] : k2_xboole_0(X11,k2_xboole_0(k4_xboole_0(X11,X12),X13)) = k2_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X11,X12))),k2_xboole_0(X11,X13)) ),
    inference(superposition,[],[f76,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(superposition,[],[f28,f34])).

fof(f569,plain,(
    ! [X8,X7] : k2_xboole_0(X7,k4_xboole_0(X8,X7)) = k2_xboole_0(k4_xboole_0(X7,X8),X8) ),
    inference(forward_demodulation,[],[f542,f33])).

fof(f542,plain,(
    ! [X8,X7] : k2_xboole_0(X7,k4_xboole_0(X8,X7)) = k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X7,X8))),X8) ),
    inference(superposition,[],[f76,f67])).

fof(f1231,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),sK0)
    | spl2_6 ),
    inference(avatar_component_clause,[],[f1229])).

fof(f1229,plain,
    ( spl2_6
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK1,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f1232,plain,
    ( ~ spl2_6
    | spl2_1 ),
    inference(avatar_split_clause,[],[f365,f82,f1229])).

fof(f82,plain,
    ( spl2_1
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f365,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),sK0)
    | spl2_1 ),
    inference(backward_demodulation,[],[f206,f354])).

fof(f206,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK1,sK1)))
    | spl2_1 ),
    inference(forward_demodulation,[],[f199,f35])).

fof(f199,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | spl2_1 ),
    inference(superposition,[],[f84,f39])).

fof(f84,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f85,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f30,f82])).

fof(f30,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f18,f26,f23])).

fof(f26,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f18,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f16])).

fof(f16,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:51:48 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (809926658)
% 0.14/0.37  ipcrm: permission denied for id (809959427)
% 0.14/0.37  ipcrm: permission denied for id (809992196)
% 0.14/0.37  ipcrm: permission denied for id (810024965)
% 0.14/0.37  ipcrm: permission denied for id (810090504)
% 0.21/0.38  ipcrm: permission denied for id (810221580)
% 0.21/0.39  ipcrm: permission denied for id (810352659)
% 0.21/0.39  ipcrm: permission denied for id (810418197)
% 0.21/0.39  ipcrm: permission denied for id (810450966)
% 0.21/0.39  ipcrm: permission denied for id (810516504)
% 0.21/0.39  ipcrm: permission denied for id (810549273)
% 0.21/0.40  ipcrm: permission denied for id (810582042)
% 0.21/0.40  ipcrm: permission denied for id (810647580)
% 0.21/0.40  ipcrm: permission denied for id (810680349)
% 0.21/0.40  ipcrm: permission denied for id (810713119)
% 0.21/0.41  ipcrm: permission denied for id (810811427)
% 0.21/0.41  ipcrm: permission denied for id (810844196)
% 0.21/0.41  ipcrm: permission denied for id (810876966)
% 0.21/0.41  ipcrm: permission denied for id (810909735)
% 0.21/0.42  ipcrm: permission denied for id (810975276)
% 0.21/0.42  ipcrm: permission denied for id (811040814)
% 0.21/0.42  ipcrm: permission denied for id (811073583)
% 0.21/0.42  ipcrm: permission denied for id (811106352)
% 0.21/0.42  ipcrm: permission denied for id (811139121)
% 0.21/0.42  ipcrm: permission denied for id (811171890)
% 0.21/0.43  ipcrm: permission denied for id (811270198)
% 0.21/0.43  ipcrm: permission denied for id (811302967)
% 0.21/0.43  ipcrm: permission denied for id (811335736)
% 0.21/0.43  ipcrm: permission denied for id (811368506)
% 0.21/0.44  ipcrm: permission denied for id (811401277)
% 0.21/0.44  ipcrm: permission denied for id (811499587)
% 0.21/0.45  ipcrm: permission denied for id (811532356)
% 0.21/0.45  ipcrm: permission denied for id (811565125)
% 0.21/0.45  ipcrm: permission denied for id (811663433)
% 0.21/0.45  ipcrm: permission denied for id (811696202)
% 0.21/0.46  ipcrm: permission denied for id (811728973)
% 0.21/0.46  ipcrm: permission denied for id (811794511)
% 0.21/0.46  ipcrm: permission denied for id (811827281)
% 0.21/0.47  ipcrm: permission denied for id (811991128)
% 0.21/0.47  ipcrm: permission denied for id (812056666)
% 0.21/0.48  ipcrm: permission denied for id (812187744)
% 0.21/0.48  ipcrm: permission denied for id (812253283)
% 0.21/0.49  ipcrm: permission denied for id (812351591)
% 0.21/0.49  ipcrm: permission denied for id (812384360)
% 0.21/0.49  ipcrm: permission denied for id (812449898)
% 0.21/0.49  ipcrm: permission denied for id (812482667)
% 0.21/0.50  ipcrm: permission denied for id (812613749)
% 0.21/0.51  ipcrm: permission denied for id (812679289)
% 0.21/0.51  ipcrm: permission denied for id (812744827)
% 0.21/0.51  ipcrm: permission denied for id (812810367)
% 0.38/0.59  % (27690)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.38/0.61  % (27682)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.38/0.63  % (27695)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.38/0.63  % (27688)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.38/0.63  % (27684)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.38/0.64  % (27697)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.38/0.64  % (27685)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.38/0.64  % (27683)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.38/0.64  % (27694)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.38/0.64  % (27681)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.38/0.64  % (27693)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.38/0.64  % (27689)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.38/0.65  % (27687)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.38/0.65  % (27686)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.38/0.65  % (27696)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.38/0.66  % (27692)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.38/0.66  % (27691)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.38/0.66  % (27680)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.39/0.68  % (27691)Refutation not found, incomplete strategy% (27691)------------------------------
% 0.39/0.68  % (27691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.39/0.68  % (27691)Termination reason: Refutation not found, incomplete strategy
% 0.39/0.68  
% 0.39/0.68  % (27691)Memory used [KB]: 10618
% 0.39/0.68  % (27691)Time elapsed: 0.120 s
% 0.39/0.68  % (27691)------------------------------
% 0.39/0.68  % (27691)------------------------------
% 0.39/0.70  % (27695)Refutation found. Thanks to Tanya!
% 0.39/0.70  % SZS status Theorem for theBenchmark
% 0.39/0.70  % SZS output start Proof for theBenchmark
% 0.39/0.70  fof(f2647,plain,(
% 0.39/0.70    $false),
% 0.39/0.70    inference(avatar_sat_refutation,[],[f85,f1232,f2638])).
% 0.39/0.70  fof(f2638,plain,(
% 0.39/0.70    spl2_6),
% 0.39/0.70    inference(avatar_contradiction_clause,[],[f2637])).
% 0.39/0.70  fof(f2637,plain,(
% 0.39/0.70    $false | spl2_6),
% 0.39/0.70    inference(subsumption_resolution,[],[f2583,f22])).
% 0.39/0.70  fof(f22,plain,(
% 0.39/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.39/0.70    inference(cnf_transformation,[],[f1])).
% 0.39/0.70  fof(f1,axiom,(
% 0.39/0.70    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.39/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.39/0.70  fof(f2583,plain,(
% 0.39/0.70    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK1,sK0) | spl2_6),
% 0.39/0.70    inference(superposition,[],[f1231,f2477])).
% 0.39/0.70  fof(f2477,plain,(
% 0.39/0.70    ( ! [X8,X7] : (k2_xboole_0(X7,X8) = k2_xboole_0(k4_xboole_0(X7,X8),X8)) )),
% 0.39/0.70    inference(backward_demodulation,[],[f569,f2429])).
% 0.39/0.70  fof(f2429,plain,(
% 0.39/0.70    ( ! [X17,X16] : (k2_xboole_0(X16,X17) = k2_xboole_0(X16,k4_xboole_0(X17,X16))) )),
% 0.39/0.70    inference(superposition,[],[f571,f67])).
% 0.39/0.70  fof(f67,plain,(
% 0.39/0.70    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X0) )),
% 0.39/0.70    inference(superposition,[],[f34,f32])).
% 0.39/0.70  fof(f32,plain,(
% 0.39/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.39/0.70    inference(definition_unfolding,[],[f21,f23,f23])).
% 0.39/0.70  fof(f23,plain,(
% 0.39/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.39/0.70    inference(cnf_transformation,[],[f8])).
% 0.39/0.70  fof(f8,axiom,(
% 0.39/0.70    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.39/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.39/0.70  fof(f21,plain,(
% 0.39/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.39/0.70    inference(cnf_transformation,[],[f2])).
% 0.39/0.70  fof(f2,axiom,(
% 0.39/0.70    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.39/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.39/0.70  fof(f34,plain,(
% 0.39/0.70    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 0.39/0.70    inference(definition_unfolding,[],[f25,f23])).
% 0.39/0.70  fof(f25,plain,(
% 0.39/0.70    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.39/0.70    inference(cnf_transformation,[],[f10])).
% 0.39/0.70  fof(f10,axiom,(
% 0.39/0.70    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.39/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.39/0.70  fof(f571,plain,(
% 0.39/0.70    ( ! [X12,X13,X11] : (k2_xboole_0(X11,X13) = k2_xboole_0(X11,k2_xboole_0(k4_xboole_0(X11,X12),X13))) )),
% 0.39/0.70    inference(forward_demodulation,[],[f544,f423])).
% 0.39/0.70  fof(f423,plain,(
% 0.39/0.70    ( ! [X6,X8,X7] : (k2_xboole_0(X6,X8) = k2_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,X7)),k2_xboole_0(X6,X8))) )),
% 0.39/0.70    inference(superposition,[],[f39,f384])).
% 0.39/0.70  fof(f384,plain,(
% 0.39/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 0.39/0.70    inference(forward_demodulation,[],[f371,f19])).
% 0.39/0.70  fof(f19,plain,(
% 0.39/0.70    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.39/0.70    inference(cnf_transformation,[],[f6])).
% 0.39/0.70  fof(f6,axiom,(
% 0.39/0.70    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.39/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.39/0.70  fof(f371,plain,(
% 0.39/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.39/0.70    inference(backward_demodulation,[],[f95,f364])).
% 0.39/0.70  fof(f364,plain,(
% 0.39/0.70    ( ! [X4] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X4)) )),
% 0.39/0.70    inference(backward_demodulation,[],[f170,f354])).
% 0.39/0.70  fof(f354,plain,(
% 0.39/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X1)) = X0) )),
% 0.39/0.70    inference(superposition,[],[f69,f35])).
% 0.39/0.70  fof(f35,plain,(
% 0.39/0.70    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 0.39/0.70    inference(definition_unfolding,[],[f29,f23])).
% 0.39/0.70  fof(f29,plain,(
% 0.39/0.70    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.39/0.70    inference(cnf_transformation,[],[f11])).
% 0.39/0.70  fof(f11,axiom,(
% 0.39/0.70    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.39/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 0.39/0.70  fof(f69,plain,(
% 0.39/0.70    ( ! [X4,X5] : (k2_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,k4_xboole_0(X4,X5))) = X4) )),
% 0.39/0.70    inference(superposition,[],[f34,f33])).
% 0.39/0.70  fof(f33,plain,(
% 0.39/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.39/0.70    inference(definition_unfolding,[],[f24,f23])).
% 0.39/0.70  fof(f24,plain,(
% 0.39/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.39/0.70    inference(cnf_transformation,[],[f7])).
% 0.39/0.70  fof(f7,axiom,(
% 0.39/0.70    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.39/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.39/0.70  fof(f170,plain,(
% 0.39/0.70    ( ! [X4] : (k4_xboole_0(k1_xboole_0,X4) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X4,X4))) )),
% 0.39/0.70    inference(superposition,[],[f33,f48])).
% 0.39/0.70  fof(f48,plain,(
% 0.39/0.70    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 0.39/0.70    inference(superposition,[],[f32,f19])).
% 0.39/0.70  fof(f95,plain,(
% 0.39/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1))) )),
% 0.39/0.70    inference(superposition,[],[f35,f19])).
% 0.39/0.70  fof(f39,plain,(
% 0.39/0.70    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2)) )),
% 0.39/0.70    inference(superposition,[],[f28,f22])).
% 0.39/0.70  fof(f28,plain,(
% 0.39/0.70    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.39/0.70    inference(cnf_transformation,[],[f9])).
% 0.39/0.70  fof(f9,axiom,(
% 0.39/0.70    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.39/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.39/0.70  fof(f544,plain,(
% 0.39/0.70    ( ! [X12,X13,X11] : (k2_xboole_0(X11,k2_xboole_0(k4_xboole_0(X11,X12),X13)) = k2_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X11,X12))),k2_xboole_0(X11,X13))) )),
% 0.39/0.70    inference(superposition,[],[f76,f76])).
% 0.39/0.70  fof(f76,plain,(
% 0.39/0.70    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X0,X1),X2))) )),
% 0.39/0.70    inference(superposition,[],[f28,f34])).
% 0.39/0.70  fof(f569,plain,(
% 0.39/0.70    ( ! [X8,X7] : (k2_xboole_0(X7,k4_xboole_0(X8,X7)) = k2_xboole_0(k4_xboole_0(X7,X8),X8)) )),
% 0.39/0.70    inference(forward_demodulation,[],[f542,f33])).
% 0.39/0.70  fof(f542,plain,(
% 0.39/0.70    ( ! [X8,X7] : (k2_xboole_0(X7,k4_xboole_0(X8,X7)) = k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X7,X8))),X8)) )),
% 0.39/0.70    inference(superposition,[],[f76,f67])).
% 0.39/0.70  fof(f1231,plain,(
% 0.39/0.70    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),sK0) | spl2_6),
% 0.39/0.70    inference(avatar_component_clause,[],[f1229])).
% 0.39/0.70  fof(f1229,plain,(
% 0.39/0.70    spl2_6 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK1,sK0),sK0)),
% 0.39/0.70    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.39/0.70  fof(f1232,plain,(
% 0.39/0.70    ~spl2_6 | spl2_1),
% 0.39/0.70    inference(avatar_split_clause,[],[f365,f82,f1229])).
% 0.39/0.70  fof(f82,plain,(
% 0.39/0.70    spl2_1 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.39/0.70    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.39/0.70  fof(f365,plain,(
% 0.39/0.70    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),sK0) | spl2_1),
% 0.39/0.70    inference(backward_demodulation,[],[f206,f354])).
% 0.39/0.70  fof(f206,plain,(
% 0.39/0.70    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK1,sK1))) | spl2_1),
% 0.39/0.70    inference(forward_demodulation,[],[f199,f35])).
% 0.39/0.70  fof(f199,plain,(
% 0.39/0.70    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | spl2_1),
% 0.39/0.70    inference(superposition,[],[f84,f39])).
% 0.39/0.70  fof(f84,plain,(
% 0.39/0.70    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_1),
% 0.39/0.70    inference(avatar_component_clause,[],[f82])).
% 0.39/0.70  fof(f85,plain,(
% 0.39/0.70    ~spl2_1),
% 0.39/0.70    inference(avatar_split_clause,[],[f30,f82])).
% 0.39/0.70  fof(f30,plain,(
% 0.39/0.70    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.39/0.70    inference(definition_unfolding,[],[f18,f26,f23])).
% 0.39/0.70  fof(f26,plain,(
% 0.39/0.70    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.39/0.70    inference(cnf_transformation,[],[f3])).
% 0.39/0.70  fof(f3,axiom,(
% 0.39/0.70    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.39/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.39/0.70  fof(f18,plain,(
% 0.39/0.70    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 0.39/0.70    inference(cnf_transformation,[],[f17])).
% 0.39/0.70  fof(f17,plain,(
% 0.39/0.70    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 0.39/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f16])).
% 0.39/0.70  fof(f16,plain,(
% 0.39/0.70    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 0.39/0.70    introduced(choice_axiom,[])).
% 0.39/0.70  fof(f14,plain,(
% 0.39/0.70    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.39/0.70    inference(ennf_transformation,[],[f13])).
% 0.39/0.70  fof(f13,negated_conjecture,(
% 0.39/0.70    ~! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.39/0.70    inference(negated_conjecture,[],[f12])).
% 0.39/0.70  fof(f12,conjecture,(
% 0.39/0.70    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.39/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).
% 0.39/0.70  % SZS output end Proof for theBenchmark
% 0.39/0.70  % (27695)------------------------------
% 0.39/0.70  % (27695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.39/0.70  % (27695)Termination reason: Refutation
% 0.39/0.70  
% 0.39/0.70  % (27695)Memory used [KB]: 13176
% 0.39/0.70  % (27695)Time elapsed: 0.119 s
% 0.39/0.70  % (27695)------------------------------
% 0.39/0.70  % (27695)------------------------------
% 0.39/0.70  % (27546)Success in time 0.342 s
%------------------------------------------------------------------------------
