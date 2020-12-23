%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:13 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 115 expanded)
%              Number of leaves         :   24 (  56 expanded)
%              Depth                    :    6
%              Number of atoms          :  172 ( 254 expanded)
%              Number of equality atoms :   53 (  84 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1053,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f31,f35,f39,f43,f47,f53,f57,f77,f81,f109,f200,f401,f807,f1007,f1041])).

fof(f1041,plain,
    ( ~ spl3_33
    | spl3_41
    | ~ spl3_55 ),
    inference(avatar_contradiction_clause,[],[f1040])).

fof(f1040,plain,
    ( $false
    | ~ spl3_33
    | spl3_41
    | ~ spl3_55 ),
    inference(subsumption_resolution,[],[f806,f1008])).

fof(f1008,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl3_33
    | ~ spl3_55 ),
    inference(unit_resulting_resolution,[],[f1006,f400])).

fof(f400,plain,
    ( ! [X14,X12,X13] :
        ( k1_xboole_0 != k4_xboole_0(X12,k2_xboole_0(X13,X14))
        | r1_tarski(k4_xboole_0(X12,X13),X14) )
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f399])).

fof(f399,plain,
    ( spl3_33
  <=> ! [X13,X12,X14] :
        ( k1_xboole_0 != k4_xboole_0(X12,k2_xboole_0(X13,X14))
        | r1_tarski(k4_xboole_0(X12,X13),X14) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f1006,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0))
    | ~ spl3_55 ),
    inference(avatar_component_clause,[],[f1005])).

fof(f1005,plain,
    ( spl3_55
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).

fof(f806,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),sK0)
    | spl3_41 ),
    inference(avatar_component_clause,[],[f804])).

fof(f804,plain,
    ( spl3_41
  <=> r1_tarski(k4_xboole_0(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f1007,plain,
    ( spl3_55
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f147,f51,f45,f1005])).

fof(f45,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f51,plain,
    ( spl3_7
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f147,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0))
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f52,f46])).

fof(f46,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f45])).

fof(f52,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f51])).

fof(f807,plain,
    ( ~ spl3_41
    | ~ spl3_10
    | spl3_11
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f213,f198,f106,f79,f804])).

fof(f79,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f106,plain,
    ( spl3_11
  <=> k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(k3_xboole_0(k4_xboole_0(sK0,sK1),sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f198,plain,
    ( spl3_22
  <=> ! [X1,X2] :
        ( k3_xboole_0(X1,X2) = X1
        | ~ r1_tarski(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f213,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),sK0)
    | ~ spl3_10
    | spl3_11
    | ~ spl3_22 ),
    inference(trivial_inequality_removal,[],[f212])).

fof(f212,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_tarski(k4_xboole_0(sK0,sK1),sK0)
    | ~ spl3_10
    | spl3_11
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f210,f80])).

fof(f80,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f79])).

fof(f210,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)
    | ~ r1_tarski(k4_xboole_0(sK0,sK1),sK0)
    | spl3_11
    | ~ spl3_22 ),
    inference(superposition,[],[f108,f199])).

fof(f199,plain,
    ( ! [X2,X1] :
        ( k3_xboole_0(X1,X2) = X1
        | ~ r1_tarski(X1,X2) )
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f198])).

fof(f108,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(k4_xboole_0(sK0,sK1),sK0),sK2)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f106])).

fof(f401,plain,
    ( spl3_33
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f97,f79,f41,f399])).

fof(f41,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f97,plain,
    ( ! [X14,X12,X13] :
        ( k1_xboole_0 != k4_xboole_0(X12,k2_xboole_0(X13,X14))
        | r1_tarski(k4_xboole_0(X12,X13),X14) )
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(superposition,[],[f42,f80])).

fof(f42,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) != k1_xboole_0
        | r1_tarski(X0,X1) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f41])).

fof(f200,plain,
    ( spl3_22
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f73,f55,f45,f29,f198])).

fof(f29,plain,
    ( spl3_2
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f55,plain,
    ( spl3_8
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f73,plain,
    ( ! [X2,X1] :
        ( k3_xboole_0(X1,X2) = X1
        | ~ r1_tarski(X1,X2) )
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f68,f30])).

fof(f30,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f68,plain,
    ( ! [X2,X1] :
        ( k3_xboole_0(X1,X2) = k4_xboole_0(X1,k1_xboole_0)
        | ~ r1_tarski(X1,X2) )
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(superposition,[],[f56,f46])).

fof(f56,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f55])).

fof(f109,plain,
    ( ~ spl3_11
    | spl3_1
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f85,f75,f24,f106])).

fof(f24,plain,
    ( spl3_1
  <=> k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f75,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f85,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(k4_xboole_0(sK0,sK1),sK0),sK2)
    | spl3_1
    | ~ spl3_9 ),
    inference(superposition,[],[f26,f76])).

fof(f76,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f75])).

fof(f26,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f81,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f22,f79])).

fof(f22,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f77,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f21,f75])).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f57,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f18,f55])).

fof(f18,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f53,plain,
    ( spl3_7
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f48,f37,f33,f51])).

fof(f33,plain,
    ( spl3_3
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f37,plain,
    ( spl3_4
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f48,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0))
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(superposition,[],[f34,f38])).

fof(f38,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f37])).

fof(f34,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f33])).

fof(f47,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f20,f45])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f43,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f19,f41])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f39,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f17,f37])).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f35,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f16,f33])).

fof(f16,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f31,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f15,f29])).

fof(f15,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f27,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f14,f24])).

fof(f14,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))
   => k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:53:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.42  % (27538)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.47  % (27523)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.47  % (27525)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (27527)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (27528)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  % (27524)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.49  % (27530)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.49  % (27522)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.50  % (27531)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.50  % (27536)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.50  % (27533)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (27535)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.50  % (27533)Refutation not found, incomplete strategy% (27533)------------------------------
% 0.22/0.50  % (27533)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (27533)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (27533)Memory used [KB]: 10618
% 0.22/0.50  % (27533)Time elapsed: 0.070 s
% 0.22/0.50  % (27533)------------------------------
% 0.22/0.50  % (27533)------------------------------
% 0.22/0.50  % (27529)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.51  % (27526)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (27532)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.51  % (27534)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.51  % (27539)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.52  % (27537)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.52  % (27527)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f1053,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f27,f31,f35,f39,f43,f47,f53,f57,f77,f81,f109,f200,f401,f807,f1007,f1041])).
% 0.22/0.53  fof(f1041,plain,(
% 0.22/0.53    ~spl3_33 | spl3_41 | ~spl3_55),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f1040])).
% 0.22/0.53  fof(f1040,plain,(
% 0.22/0.53    $false | (~spl3_33 | spl3_41 | ~spl3_55)),
% 0.22/0.53    inference(subsumption_resolution,[],[f806,f1008])).
% 0.22/0.53  fof(f1008,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | (~spl3_33 | ~spl3_55)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f1006,f400])).
% 0.22/0.53  fof(f400,plain,(
% 0.22/0.53    ( ! [X14,X12,X13] : (k1_xboole_0 != k4_xboole_0(X12,k2_xboole_0(X13,X14)) | r1_tarski(k4_xboole_0(X12,X13),X14)) ) | ~spl3_33),
% 0.22/0.53    inference(avatar_component_clause,[],[f399])).
% 0.22/0.53  fof(f399,plain,(
% 0.22/0.53    spl3_33 <=> ! [X13,X12,X14] : (k1_xboole_0 != k4_xboole_0(X12,k2_xboole_0(X13,X14)) | r1_tarski(k4_xboole_0(X12,X13),X14))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.22/0.53  fof(f1006,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0))) ) | ~spl3_55),
% 0.22/0.53    inference(avatar_component_clause,[],[f1005])).
% 0.22/0.53  fof(f1005,plain,(
% 0.22/0.53    spl3_55 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).
% 0.22/0.53  fof(f806,plain,(
% 0.22/0.53    ~r1_tarski(k4_xboole_0(sK0,sK1),sK0) | spl3_41),
% 0.22/0.53    inference(avatar_component_clause,[],[f804])).
% 0.22/0.53  fof(f804,plain,(
% 0.22/0.53    spl3_41 <=> r1_tarski(k4_xboole_0(sK0,sK1),sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.22/0.53  fof(f1007,plain,(
% 0.22/0.53    spl3_55 | ~spl3_6 | ~spl3_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f147,f51,f45,f1005])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    spl3_6 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    spl3_7 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X1,X0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.53  fof(f147,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0))) ) | (~spl3_6 | ~spl3_7)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f52,f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) ) | ~spl3_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f45])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) ) | ~spl3_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f51])).
% 0.22/0.53  fof(f807,plain,(
% 0.22/0.53    ~spl3_41 | ~spl3_10 | spl3_11 | ~spl3_22),
% 0.22/0.53    inference(avatar_split_clause,[],[f213,f198,f106,f79,f804])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    spl3_10 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.53  fof(f106,plain,(
% 0.22/0.53    spl3_11 <=> k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(k3_xboole_0(k4_xboole_0(sK0,sK1),sK0),sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.53  fof(f198,plain,(
% 0.22/0.53    spl3_22 <=> ! [X1,X2] : (k3_xboole_0(X1,X2) = X1 | ~r1_tarski(X1,X2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.22/0.53  fof(f213,plain,(
% 0.22/0.53    ~r1_tarski(k4_xboole_0(sK0,sK1),sK0) | (~spl3_10 | spl3_11 | ~spl3_22)),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f212])).
% 0.22/0.53  fof(f212,plain,(
% 0.22/0.53    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~r1_tarski(k4_xboole_0(sK0,sK1),sK0) | (~spl3_10 | spl3_11 | ~spl3_22)),
% 0.22/0.53    inference(forward_demodulation,[],[f210,f80])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl3_10),
% 0.22/0.53    inference(avatar_component_clause,[],[f79])).
% 0.22/0.53  fof(f210,plain,(
% 0.22/0.53    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) | ~r1_tarski(k4_xboole_0(sK0,sK1),sK0) | (spl3_11 | ~spl3_22)),
% 0.22/0.53    inference(superposition,[],[f108,f199])).
% 0.22/0.53  fof(f199,plain,(
% 0.22/0.53    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = X1 | ~r1_tarski(X1,X2)) ) | ~spl3_22),
% 0.22/0.53    inference(avatar_component_clause,[],[f198])).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(k4_xboole_0(sK0,sK1),sK0),sK2) | spl3_11),
% 0.22/0.53    inference(avatar_component_clause,[],[f106])).
% 0.22/0.53  fof(f401,plain,(
% 0.22/0.53    spl3_33 | ~spl3_5 | ~spl3_10),
% 0.22/0.53    inference(avatar_split_clause,[],[f97,f79,f41,f399])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    spl3_5 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.53  fof(f97,plain,(
% 0.22/0.53    ( ! [X14,X12,X13] : (k1_xboole_0 != k4_xboole_0(X12,k2_xboole_0(X13,X14)) | r1_tarski(k4_xboole_0(X12,X13),X14)) ) | (~spl3_5 | ~spl3_10)),
% 0.22/0.53    inference(superposition,[],[f42,f80])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) ) | ~spl3_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f41])).
% 0.22/0.53  fof(f200,plain,(
% 0.22/0.53    spl3_22 | ~spl3_2 | ~spl3_6 | ~spl3_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f73,f55,f45,f29,f198])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    spl3_2 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    spl3_8 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = X1 | ~r1_tarski(X1,X2)) ) | (~spl3_2 | ~spl3_6 | ~spl3_8)),
% 0.22/0.53    inference(forward_demodulation,[],[f68,f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f29])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k4_xboole_0(X1,k1_xboole_0) | ~r1_tarski(X1,X2)) ) | (~spl3_6 | ~spl3_8)),
% 0.22/0.53    inference(superposition,[],[f56,f46])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) ) | ~spl3_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f55])).
% 0.22/0.53  fof(f109,plain,(
% 0.22/0.53    ~spl3_11 | spl3_1 | ~spl3_9),
% 0.22/0.53    inference(avatar_split_clause,[],[f85,f75,f24,f106])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    spl3_1 <=> k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    spl3_9 <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(k4_xboole_0(sK0,sK1),sK0),sK2) | (spl3_1 | ~spl3_9)),
% 0.22/0.53    inference(superposition,[],[f26,f76])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) ) | ~spl3_9),
% 0.22/0.53    inference(avatar_component_clause,[],[f75])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) | spl3_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f24])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    spl3_10),
% 0.22/0.53    inference(avatar_split_clause,[],[f22,f79])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    spl3_9),
% 0.22/0.53    inference(avatar_split_clause,[],[f21,f75])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    spl3_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f18,f55])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    spl3_7 | ~spl3_3 | ~spl3_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f48,f37,f33,f51])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    spl3_3 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    spl3_4 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) ) | (~spl3_3 | ~spl3_4)),
% 0.22/0.53    inference(superposition,[],[f34,f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl3_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f37])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | ~spl3_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f33])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    spl3_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f20,f45])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.22/0.53    inference(nnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    spl3_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f19,f41])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    spl3_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f17,f37])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    spl3_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f16,f33])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    spl3_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f15,f29])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ~spl3_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f14,f24])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) => k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 0.22/0.53    inference(negated_conjecture,[],[f8])).
% 0.22/0.53  fof(f8,conjecture,(
% 0.22/0.53    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_xboole_1)).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (27527)------------------------------
% 0.22/0.53  % (27527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (27527)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (27527)Memory used [KB]: 6908
% 0.22/0.53  % (27527)Time elapsed: 0.093 s
% 0.22/0.53  % (27527)------------------------------
% 0.22/0.53  % (27527)------------------------------
% 0.22/0.53  % (27521)Success in time 0.159 s
%------------------------------------------------------------------------------
