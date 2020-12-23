%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:52 EST 2020

% Result     : Theorem 1.73s
% Output     : Refutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 121 expanded)
%              Number of leaves         :   16 (  35 expanded)
%              Depth                    :   15
%              Number of atoms          :  146 ( 235 expanded)
%              Number of equality atoms :   33 (  64 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1007,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f914,f996])).

fof(f996,plain,(
    spl8_2 ),
    inference(avatar_contradiction_clause,[],[f995])).

fof(f995,plain,
    ( $false
    | spl8_2 ),
    inference(subsumption_resolution,[],[f994,f62])).

fof(f62,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ~ r1_tarski(k5_xboole_0(sK3,sK5),sK4)
    & r1_tarski(sK5,sK4)
    & r1_tarski(sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f28,f45])).

fof(f45,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k5_xboole_0(sK3,sK5),sK4)
      & r1_tarski(sK5,sK4)
      & r1_tarski(sK3,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X2,X1)
          & r1_tarski(X0,X1) )
       => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).

fof(f994,plain,
    ( ~ r1_tarski(sK3,sK4)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f979,f63])).

fof(f63,plain,(
    r1_tarski(sK5,sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f979,plain,
    ( ~ r1_tarski(sK5,sK4)
    | ~ r1_tarski(sK3,sK4)
    | spl8_2 ),
    inference(resolution,[],[f114,f893])).

fof(f893,plain,
    ( ~ r1_tarski(k5_xboole_0(sK3,k4_xboole_0(sK5,sK3)),sK4)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f891])).

fof(f891,plain,
    ( spl8_2
  <=> r1_tarski(k5_xboole_0(sK3,k4_xboole_0(sK5,sK3)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f85,f72])).

fof(f72,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f914,plain,(
    ~ spl8_2 ),
    inference(avatar_split_clause,[],[f871,f891])).

fof(f871,plain,(
    ~ r1_tarski(k5_xboole_0(sK3,k4_xboole_0(sK5,sK3)),sK4) ),
    inference(resolution,[],[f847,f671])).

fof(f671,plain,(
    ! [X7] : r1_tarski(X7,X7) ),
    inference(subsumption_resolution,[],[f257,f667])).

fof(f667,plain,(
    ! [X8] : r1_tarski(k1_xboole_0,X8) ),
    inference(superposition,[],[f623,f587])).

fof(f587,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f582,f68])).

fof(f68,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f582,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(condensation,[],[f581])).

fof(f581,plain,(
    ! [X19,X18] :
      ( k1_xboole_0 = X18
      | ~ r1_tarski(X18,k1_xboole_0)
      | ~ r1_tarski(X18,X19) ) ),
    inference(superposition,[],[f550,f566])).

fof(f566,plain,(
    ! [X14,X13] :
      ( k4_xboole_0(X13,k1_xboole_0) = X13
      | ~ r1_tarski(X13,X14) ) ),
    inference(duplicate_literal_removal,[],[f560])).

fof(f560,plain,(
    ! [X14,X13] :
      ( k4_xboole_0(X13,k1_xboole_0) = X13
      | ~ r1_tarski(X13,X14)
      | ~ r1_tarski(X13,X14) ) ),
    inference(superposition,[],[f109,f550])).

fof(f109,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f77,f74])).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f77,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f550,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f528,f65])).

fof(f65,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f528,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f104,f109])).

fof(f104,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f73,f74])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f623,plain,(
    ! [X6,X7] : r1_tarski(k4_xboole_0(X7,k4_xboole_0(X7,X6)),X6) ),
    inference(superposition,[],[f68,f105])).

fof(f105,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f70,f74,f74])).

fof(f70,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f257,plain,(
    ! [X7] :
      ( r1_tarski(X7,X7)
      | ~ r1_tarski(k1_xboole_0,X7) ) ),
    inference(superposition,[],[f68,f225])).

fof(f225,plain,(
    ! [X6] :
      ( k4_xboole_0(X6,k1_xboole_0) = X6
      | ~ r1_tarski(k1_xboole_0,X6) ) ),
    inference(superposition,[],[f108,f121])).

fof(f121,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f69,f66])).

fof(f66,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f69,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f108,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f76,f72])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f847,plain,(
    ! [X26,X25] :
      ( ~ r1_tarski(k5_xboole_0(sK3,sK5),k5_xboole_0(X25,X26))
      | ~ r1_tarski(k5_xboole_0(X25,k4_xboole_0(X26,X25)),sK4) ) ),
    inference(resolution,[],[f119,f129])).

fof(f129,plain,(
    ! [X0] :
      ( ~ r1_tarski(k5_xboole_0(sK3,sK5),X0)
      | ~ r1_tarski(X0,sK4) ) ),
    inference(resolution,[],[f83,f64])).

fof(f64,plain,(
    ~ r1_tarski(k5_xboole_0(sK3,sK5),sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))
      | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f101,f72])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k5_xboole_0(X1,X2))
        | ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k5_xboole_0(X1,X2))
        | ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k5_xboole_0(X1,X2))
    <=> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:44:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (21569)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (21570)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (21577)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  % (21574)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (21572)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (21576)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (21586)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.51  % (21585)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (21591)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.52  % (21594)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.52  % (21592)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (21593)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (21582)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (21584)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (21573)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (21600)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.52  % (21571)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (21595)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (21575)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (21590)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (21583)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (21578)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.53  % (21588)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  % (21579)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (21589)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.53  % (21596)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (21587)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (21580)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (21599)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.55  % (21598)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.73/0.60  % (21598)Refutation found. Thanks to Tanya!
% 1.73/0.60  % SZS status Theorem for theBenchmark
% 1.73/0.60  % SZS output start Proof for theBenchmark
% 1.73/0.60  fof(f1007,plain,(
% 1.73/0.60    $false),
% 1.73/0.60    inference(avatar_sat_refutation,[],[f914,f996])).
% 1.73/0.60  fof(f996,plain,(
% 1.73/0.60    spl8_2),
% 1.73/0.60    inference(avatar_contradiction_clause,[],[f995])).
% 1.73/0.60  fof(f995,plain,(
% 1.73/0.60    $false | spl8_2),
% 1.73/0.60    inference(subsumption_resolution,[],[f994,f62])).
% 1.73/0.60  fof(f62,plain,(
% 1.73/0.60    r1_tarski(sK3,sK4)),
% 1.73/0.60    inference(cnf_transformation,[],[f46])).
% 1.73/0.60  fof(f46,plain,(
% 1.73/0.60    ~r1_tarski(k5_xboole_0(sK3,sK5),sK4) & r1_tarski(sK5,sK4) & r1_tarski(sK3,sK4)),
% 1.73/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f28,f45])).
% 1.73/0.60  fof(f45,plain,(
% 1.73/0.60    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => (~r1_tarski(k5_xboole_0(sK3,sK5),sK4) & r1_tarski(sK5,sK4) & r1_tarski(sK3,sK4))),
% 1.73/0.60    introduced(choice_axiom,[])).
% 1.73/0.60  fof(f28,plain,(
% 1.73/0.60    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & r1_tarski(X2,X1) & r1_tarski(X0,X1))),
% 1.73/0.60    inference(flattening,[],[f27])).
% 1.73/0.60  fof(f27,plain,(
% 1.73/0.60    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & (r1_tarski(X2,X1) & r1_tarski(X0,X1)))),
% 1.73/0.60    inference(ennf_transformation,[],[f26])).
% 1.73/0.60  fof(f26,negated_conjecture,(
% 1.73/0.60    ~! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 1.73/0.60    inference(negated_conjecture,[],[f25])).
% 1.73/0.60  fof(f25,conjecture,(
% 1.73/0.60    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 1.73/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).
% 1.73/0.60  fof(f994,plain,(
% 1.73/0.60    ~r1_tarski(sK3,sK4) | spl8_2),
% 1.73/0.60    inference(subsumption_resolution,[],[f979,f63])).
% 1.73/0.60  fof(f63,plain,(
% 1.73/0.60    r1_tarski(sK5,sK4)),
% 1.73/0.60    inference(cnf_transformation,[],[f46])).
% 1.73/0.60  fof(f979,plain,(
% 1.73/0.60    ~r1_tarski(sK5,sK4) | ~r1_tarski(sK3,sK4) | spl8_2),
% 1.73/0.60    inference(resolution,[],[f114,f893])).
% 1.73/0.60  fof(f893,plain,(
% 1.73/0.60    ~r1_tarski(k5_xboole_0(sK3,k4_xboole_0(sK5,sK3)),sK4) | spl8_2),
% 1.73/0.60    inference(avatar_component_clause,[],[f891])).
% 1.73/0.60  fof(f891,plain,(
% 1.73/0.60    spl8_2 <=> r1_tarski(k5_xboole_0(sK3,k4_xboole_0(sK5,sK3)),sK4)),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.73/0.60  fof(f114,plain,(
% 1.73/0.60    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.73/0.60    inference(definition_unfolding,[],[f85,f72])).
% 1.73/0.60  fof(f72,plain,(
% 1.73/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.73/0.60    inference(cnf_transformation,[],[f24])).
% 1.73/0.60  fof(f24,axiom,(
% 1.73/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.73/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.73/0.60  fof(f85,plain,(
% 1.73/0.60    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f38])).
% 1.73/0.60  fof(f38,plain,(
% 1.73/0.60    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.73/0.60    inference(flattening,[],[f37])).
% 1.73/0.60  fof(f37,plain,(
% 1.73/0.60    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.73/0.60    inference(ennf_transformation,[],[f21])).
% 1.73/0.60  fof(f21,axiom,(
% 1.73/0.60    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 1.73/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 1.73/0.60  fof(f914,plain,(
% 1.73/0.60    ~spl8_2),
% 1.73/0.60    inference(avatar_split_clause,[],[f871,f891])).
% 1.73/0.60  fof(f871,plain,(
% 1.73/0.60    ~r1_tarski(k5_xboole_0(sK3,k4_xboole_0(sK5,sK3)),sK4)),
% 1.73/0.60    inference(resolution,[],[f847,f671])).
% 1.73/0.60  fof(f671,plain,(
% 1.73/0.60    ( ! [X7] : (r1_tarski(X7,X7)) )),
% 1.73/0.60    inference(subsumption_resolution,[],[f257,f667])).
% 1.73/0.60  fof(f667,plain,(
% 1.73/0.60    ( ! [X8] : (r1_tarski(k1_xboole_0,X8)) )),
% 1.73/0.60    inference(superposition,[],[f623,f587])).
% 1.73/0.60  fof(f587,plain,(
% 1.73/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.73/0.60    inference(resolution,[],[f582,f68])).
% 1.73/0.60  fof(f68,plain,(
% 1.73/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f15])).
% 1.73/0.60  fof(f15,axiom,(
% 1.73/0.60    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.73/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.73/0.60  fof(f582,plain,(
% 1.73/0.60    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.73/0.60    inference(condensation,[],[f581])).
% 1.73/0.60  fof(f581,plain,(
% 1.73/0.60    ( ! [X19,X18] : (k1_xboole_0 = X18 | ~r1_tarski(X18,k1_xboole_0) | ~r1_tarski(X18,X19)) )),
% 1.73/0.60    inference(superposition,[],[f550,f566])).
% 1.73/0.60  fof(f566,plain,(
% 1.73/0.60    ( ! [X14,X13] : (k4_xboole_0(X13,k1_xboole_0) = X13 | ~r1_tarski(X13,X14)) )),
% 1.73/0.60    inference(duplicate_literal_removal,[],[f560])).
% 1.73/0.60  fof(f560,plain,(
% 1.73/0.60    ( ! [X14,X13] : (k4_xboole_0(X13,k1_xboole_0) = X13 | ~r1_tarski(X13,X14) | ~r1_tarski(X13,X14)) )),
% 1.73/0.60    inference(superposition,[],[f109,f550])).
% 1.73/0.60  fof(f109,plain,(
% 1.73/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 1.73/0.60    inference(definition_unfolding,[],[f77,f74])).
% 1.73/0.60  fof(f74,plain,(
% 1.73/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.73/0.60    inference(cnf_transformation,[],[f16])).
% 1.73/0.60  fof(f16,axiom,(
% 1.73/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.73/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.73/0.60  fof(f77,plain,(
% 1.73/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f31])).
% 1.73/0.60  fof(f31,plain,(
% 1.73/0.60    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.73/0.60    inference(ennf_transformation,[],[f13])).
% 1.73/0.60  fof(f13,axiom,(
% 1.73/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.73/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.73/0.60  fof(f550,plain,(
% 1.73/0.60    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 1.73/0.60    inference(forward_demodulation,[],[f528,f65])).
% 1.73/0.60  fof(f65,plain,(
% 1.73/0.60    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f23])).
% 1.73/0.60  fof(f23,axiom,(
% 1.73/0.60    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.73/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.73/0.60  fof(f528,plain,(
% 1.73/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,X0) | ~r1_tarski(X0,X1)) )),
% 1.73/0.60    inference(superposition,[],[f104,f109])).
% 1.73/0.60  fof(f104,plain,(
% 1.73/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.73/0.60    inference(definition_unfolding,[],[f73,f74])).
% 1.73/0.60  fof(f73,plain,(
% 1.73/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.73/0.60    inference(cnf_transformation,[],[f6])).
% 1.73/0.60  fof(f6,axiom,(
% 1.73/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.73/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.73/0.60  fof(f623,plain,(
% 1.73/0.60    ( ! [X6,X7] : (r1_tarski(k4_xboole_0(X7,k4_xboole_0(X7,X6)),X6)) )),
% 1.73/0.60    inference(superposition,[],[f68,f105])).
% 1.73/0.60  fof(f105,plain,(
% 1.73/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.73/0.60    inference(definition_unfolding,[],[f70,f74,f74])).
% 1.73/0.60  fof(f70,plain,(
% 1.73/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f1])).
% 1.73/0.60  fof(f1,axiom,(
% 1.73/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.73/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.73/0.60  fof(f257,plain,(
% 1.73/0.60    ( ! [X7] : (r1_tarski(X7,X7) | ~r1_tarski(k1_xboole_0,X7)) )),
% 1.73/0.60    inference(superposition,[],[f68,f225])).
% 1.73/0.60  fof(f225,plain,(
% 1.73/0.60    ( ! [X6] : (k4_xboole_0(X6,k1_xboole_0) = X6 | ~r1_tarski(k1_xboole_0,X6)) )),
% 1.73/0.60    inference(superposition,[],[f108,f121])).
% 1.73/0.60  fof(f121,plain,(
% 1.73/0.60    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.73/0.60    inference(superposition,[],[f69,f66])).
% 1.73/0.60  fof(f66,plain,(
% 1.73/0.60    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.73/0.60    inference(cnf_transformation,[],[f20])).
% 1.73/0.60  fof(f20,axiom,(
% 1.73/0.60    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.73/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.73/0.60  fof(f69,plain,(
% 1.73/0.60    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f2])).
% 1.73/0.60  fof(f2,axiom,(
% 1.73/0.60    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.73/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.73/0.60  fof(f108,plain,(
% 1.73/0.60    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 1.73/0.60    inference(definition_unfolding,[],[f76,f72])).
% 1.95/0.62  fof(f76,plain,(
% 1.95/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.95/0.62    inference(cnf_transformation,[],[f30])).
% 1.95/0.62  fof(f30,plain,(
% 1.95/0.62    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.95/0.62    inference(ennf_transformation,[],[f8])).
% 1.95/0.62  fof(f8,axiom,(
% 1.95/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.95/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.95/0.62  fof(f847,plain,(
% 1.95/0.62    ( ! [X26,X25] : (~r1_tarski(k5_xboole_0(sK3,sK5),k5_xboole_0(X25,X26)) | ~r1_tarski(k5_xboole_0(X25,k4_xboole_0(X26,X25)),sK4)) )),
% 1.95/0.62    inference(resolution,[],[f119,f129])).
% 1.95/0.62  fof(f129,plain,(
% 1.95/0.62    ( ! [X0] : (~r1_tarski(k5_xboole_0(sK3,sK5),X0) | ~r1_tarski(X0,sK4)) )),
% 1.95/0.62    inference(resolution,[],[f83,f64])).
% 1.95/0.62  fof(f64,plain,(
% 1.95/0.62    ~r1_tarski(k5_xboole_0(sK3,sK5),sK4)),
% 1.95/0.62    inference(cnf_transformation,[],[f46])).
% 1.95/0.62  fof(f83,plain,(
% 1.95/0.62    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.95/0.62    inference(cnf_transformation,[],[f34])).
% 1.95/0.62  fof(f34,plain,(
% 1.95/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.95/0.62    inference(flattening,[],[f33])).
% 1.95/0.62  fof(f33,plain,(
% 1.95/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.95/0.62    inference(ennf_transformation,[],[f11])).
% 1.95/0.62  fof(f11,axiom,(
% 1.95/0.62    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.95/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.95/0.62  fof(f119,plain,(
% 1.95/0.62    ( ! [X2,X0,X1] : (r1_tarski(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) )),
% 1.95/0.62    inference(definition_unfolding,[],[f101,f72])).
% 1.95/0.62  fof(f101,plain,(
% 1.95/0.62    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) )),
% 1.95/0.62    inference(cnf_transformation,[],[f61])).
% 1.95/0.62  fof(f61,plain,(
% 1.95/0.62    ! [X0,X1,X2] : ((r1_tarski(X0,k5_xboole_0(X1,X2)) | ~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | ~r1_tarski(X0,k5_xboole_0(X1,X2))))),
% 1.95/0.62    inference(flattening,[],[f60])).
% 1.95/0.62  fof(f60,plain,(
% 1.95/0.62    ! [X0,X1,X2] : ((r1_tarski(X0,k5_xboole_0(X1,X2)) | (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | ~r1_tarski(X0,k5_xboole_0(X1,X2))))),
% 1.95/0.62    inference(nnf_transformation,[],[f7])).
% 1.95/0.62  fof(f7,axiom,(
% 1.95/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k5_xboole_0(X1,X2)) <=> (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 1.95/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).
% 1.95/0.62  % SZS output end Proof for theBenchmark
% 1.95/0.62  % (21598)------------------------------
% 1.95/0.62  % (21598)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.95/0.62  % (21598)Termination reason: Refutation
% 1.95/0.62  
% 1.95/0.62  % (21598)Memory used [KB]: 6652
% 1.95/0.62  % (21598)Time elapsed: 0.183 s
% 1.95/0.62  % (21598)------------------------------
% 1.95/0.62  % (21598)------------------------------
% 1.95/0.62  % (21566)Success in time 0.262 s
%------------------------------------------------------------------------------
