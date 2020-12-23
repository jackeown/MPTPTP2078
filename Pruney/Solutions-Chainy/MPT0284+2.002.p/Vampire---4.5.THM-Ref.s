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
% DateTime   : Thu Dec  3 12:41:38 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 223 expanded)
%              Number of leaves         :   17 (  68 expanded)
%              Depth                    :   14
%              Number of atoms          :  113 ( 354 expanded)
%              Number of equality atoms :   41 ( 189 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1156,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f105,f986,f1130])).

fof(f1130,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f1100])).

fof(f1100,plain,
    ( $false
    | spl2_2 ),
    inference(resolution,[],[f974,f1032])).

fof(f1032,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK0),k5_xboole_0(sK0,sK1))
    | spl2_2 ),
    inference(resolution,[],[f104,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f104,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl2_2
  <=> r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f974,plain,(
    ! [X2,X1] : r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X2,X1)) ),
    inference(superposition,[],[f891,f671])).

fof(f671,plain,(
    ! [X2,X3] : k5_xboole_0(X2,X3) = k5_xboole_0(X3,X2) ),
    inference(superposition,[],[f115,f42])).

fof(f42,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k3_tarski(k1_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f33,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f30,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f33,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f115,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k3_tarski(k1_enumset1(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0),k4_xboole_0(X0,X1))) ),
    inference(superposition,[],[f42,f45])).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f27,f29,f29])).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f891,plain,(
    ! [X8,X9] : r1_tarski(k4_xboole_0(X8,X9),k5_xboole_0(X8,X9)) ),
    inference(superposition,[],[f26,f162])).

fof(f162,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X1),X0)) ),
    inference(forward_demodulation,[],[f161,f69])).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f43,f46])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f28,f32,f32])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f161,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X1),X0)) ),
    inference(forward_demodulation,[],[f143,f63])).

fof(f63,plain,(
    ! [X0] : k4_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
    inference(backward_demodulation,[],[f55,f61])).

fof(f61,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f43,f55])).

fof(f55,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(resolution,[],[f47,f50])).

fof(f50,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f34,f32])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f143,plain,(
    ! [X0,X1] : k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X1),X0)) = k5_xboole_0(k4_xboole_0(X0,k5_xboole_0(X0,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f48,f61])).

fof(f48,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(k5_xboole_0(X0,X2),X1)) ),
    inference(definition_unfolding,[],[f39,f32,f32,f32])).

fof(f39,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f986,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f957])).

fof(f957,plain,
    ( $false
    | spl2_1 ),
    inference(resolution,[],[f891,f106])).

fof(f106,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))
    | spl2_1 ),
    inference(resolution,[],[f100,f35])).

fof(f100,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl2_1
  <=> r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f105,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f96,f102,f98])).

fof(f96,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f44,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f44,plain,(
    ~ r1_tarski(k3_tarski(k1_enumset1(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0)))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f25,f41])).

fof(f25,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f21])).

fof(f21,plain,
    ( ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))
   => ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:52:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (31670)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.48  % (31696)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.48  % (31688)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.49  % (31680)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.49  % (31696)Refutation not found, incomplete strategy% (31696)------------------------------
% 0.21/0.49  % (31696)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (31677)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.50  % (31680)Refutation not found, incomplete strategy% (31680)------------------------------
% 0.21/0.50  % (31680)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (31680)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (31680)Memory used [KB]: 10618
% 0.21/0.50  % (31680)Time elapsed: 0.124 s
% 0.21/0.50  % (31680)------------------------------
% 0.21/0.50  % (31680)------------------------------
% 0.21/0.50  % (31678)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.50  % (31696)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (31696)Memory used [KB]: 10618
% 0.21/0.50  % (31696)Time elapsed: 0.106 s
% 0.21/0.50  % (31696)------------------------------
% 0.21/0.50  % (31696)------------------------------
% 0.21/0.51  % (31678)Refutation not found, incomplete strategy% (31678)------------------------------
% 0.21/0.51  % (31678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31678)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (31678)Memory used [KB]: 10618
% 0.21/0.51  % (31678)Time elapsed: 0.107 s
% 0.21/0.51  % (31678)------------------------------
% 0.21/0.51  % (31678)------------------------------
% 0.21/0.51  % (31682)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (31682)Refutation not found, incomplete strategy% (31682)------------------------------
% 0.21/0.51  % (31682)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31682)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (31682)Memory used [KB]: 1663
% 0.21/0.51  % (31682)Time elapsed: 0.072 s
% 0.21/0.51  % (31682)------------------------------
% 0.21/0.51  % (31682)------------------------------
% 0.21/0.51  % (31671)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (31692)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.51  % (31672)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (31674)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (31690)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (31684)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.52  % (31684)Refutation not found, incomplete strategy% (31684)------------------------------
% 0.21/0.52  % (31684)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31692)Refutation not found, incomplete strategy% (31692)------------------------------
% 0.21/0.52  % (31692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31684)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31684)Memory used [KB]: 10618
% 0.21/0.52  % (31684)Time elapsed: 0.114 s
% 0.21/0.52  % (31684)------------------------------
% 0.21/0.52  % (31684)------------------------------
% 0.21/0.52  % (31697)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (31695)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.52  % (31697)Refutation not found, incomplete strategy% (31697)------------------------------
% 0.21/0.52  % (31697)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31697)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31697)Memory used [KB]: 1663
% 0.21/0.52  % (31697)Time elapsed: 0.093 s
% 0.21/0.52  % (31697)------------------------------
% 0.21/0.52  % (31697)------------------------------
% 0.21/0.52  % (31692)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31692)Memory used [KB]: 10618
% 0.21/0.52  % (31692)Time elapsed: 0.113 s
% 0.21/0.52  % (31692)------------------------------
% 0.21/0.52  % (31692)------------------------------
% 0.21/0.52  % (31679)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (31679)Refutation not found, incomplete strategy% (31679)------------------------------
% 0.21/0.52  % (31679)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31679)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31679)Memory used [KB]: 6140
% 0.21/0.52  % (31679)Time elapsed: 0.128 s
% 0.21/0.52  % (31679)------------------------------
% 0.21/0.52  % (31679)------------------------------
% 0.21/0.52  % (31668)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (31689)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (31685)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.52  % (31685)Refutation not found, incomplete strategy% (31685)------------------------------
% 0.21/0.52  % (31685)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31685)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31685)Memory used [KB]: 1663
% 0.21/0.52  % (31685)Time elapsed: 0.133 s
% 0.21/0.52  % (31685)------------------------------
% 0.21/0.52  % (31685)------------------------------
% 0.21/0.53  % (31669)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (31669)Refutation not found, incomplete strategy% (31669)------------------------------
% 0.21/0.53  % (31669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31669)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (31669)Memory used [KB]: 1663
% 0.21/0.53  % (31669)Time elapsed: 0.125 s
% 0.21/0.53  % (31669)------------------------------
% 0.21/0.53  % (31669)------------------------------
% 0.21/0.53  % (31681)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (31683)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (31673)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (31693)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (31693)Refutation not found, incomplete strategy% (31693)------------------------------
% 0.21/0.54  % (31693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31693)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (31693)Memory used [KB]: 6140
% 0.21/0.54  % (31693)Time elapsed: 0.139 s
% 0.21/0.54  % (31693)------------------------------
% 0.21/0.54  % (31693)------------------------------
% 0.21/0.54  % (31676)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (31695)Refutation not found, incomplete strategy% (31695)------------------------------
% 0.21/0.54  % (31695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31695)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (31695)Memory used [KB]: 6140
% 0.21/0.54  % (31695)Time elapsed: 0.124 s
% 0.21/0.54  % (31695)------------------------------
% 0.21/0.54  % (31695)------------------------------
% 1.43/0.55  % (31686)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.43/0.55  % (31694)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.43/0.55  % (31686)Refutation not found, incomplete strategy% (31686)------------------------------
% 1.43/0.55  % (31686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (31686)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (31686)Memory used [KB]: 1663
% 1.43/0.55  % (31686)Time elapsed: 0.150 s
% 1.43/0.55  % (31686)------------------------------
% 1.43/0.55  % (31686)------------------------------
% 1.43/0.55  % (31694)Refutation not found, incomplete strategy% (31694)------------------------------
% 1.43/0.55  % (31694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (31694)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (31694)Memory used [KB]: 6140
% 1.43/0.55  % (31694)Time elapsed: 0.141 s
% 1.43/0.55  % (31694)------------------------------
% 1.43/0.55  % (31694)------------------------------
% 1.43/0.55  % (31675)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.43/0.55  % (31691)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.43/0.55  % (31687)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.60/0.59  % (31674)Refutation found. Thanks to Tanya!
% 1.60/0.59  % SZS status Theorem for theBenchmark
% 1.60/0.59  % SZS output start Proof for theBenchmark
% 1.60/0.59  fof(f1156,plain,(
% 1.60/0.59    $false),
% 1.60/0.59    inference(avatar_sat_refutation,[],[f105,f986,f1130])).
% 1.60/0.59  fof(f1130,plain,(
% 1.60/0.59    spl2_2),
% 1.60/0.59    inference(avatar_contradiction_clause,[],[f1100])).
% 1.60/0.59  fof(f1100,plain,(
% 1.60/0.59    $false | spl2_2),
% 1.60/0.59    inference(resolution,[],[f974,f1032])).
% 1.60/0.59  fof(f1032,plain,(
% 1.60/0.59    ~r1_tarski(k4_xboole_0(sK1,sK0),k5_xboole_0(sK0,sK1)) | spl2_2),
% 1.60/0.59    inference(resolution,[],[f104,f35])).
% 1.60/0.59  fof(f35,plain,(
% 1.60/0.59    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f18])).
% 1.60/0.59  fof(f18,plain,(
% 1.60/0.59    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 1.60/0.59    inference(ennf_transformation,[],[f13])).
% 1.60/0.59  fof(f13,axiom,(
% 1.60/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 1.60/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 1.60/0.59  fof(f104,plain,(
% 1.60/0.59    ~r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | spl2_2),
% 1.60/0.59    inference(avatar_component_clause,[],[f102])).
% 1.60/0.59  fof(f102,plain,(
% 1.60/0.59    spl2_2 <=> r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 1.60/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.60/0.59  fof(f974,plain,(
% 1.60/0.59    ( ! [X2,X1] : (r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X2,X1))) )),
% 1.60/0.59    inference(superposition,[],[f891,f671])).
% 1.60/0.59  fof(f671,plain,(
% 1.60/0.59    ( ! [X2,X3] : (k5_xboole_0(X2,X3) = k5_xboole_0(X3,X2)) )),
% 1.60/0.59    inference(superposition,[],[f115,f42])).
% 1.60/0.59  fof(f42,plain,(
% 1.60/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k3_tarski(k1_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) )),
% 1.60/0.59    inference(definition_unfolding,[],[f33,f41])).
% 1.60/0.59  fof(f41,plain,(
% 1.60/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 1.60/0.59    inference(definition_unfolding,[],[f30,f29])).
% 1.60/0.59  fof(f29,plain,(
% 1.60/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f11])).
% 1.60/0.59  fof(f11,axiom,(
% 1.60/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.60/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.60/0.59  fof(f30,plain,(
% 1.60/0.59    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f12])).
% 1.60/0.59  fof(f12,axiom,(
% 1.60/0.59    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 1.60/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.60/0.59  fof(f33,plain,(
% 1.60/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 1.60/0.59    inference(cnf_transformation,[],[f2])).
% 1.60/0.59  fof(f2,axiom,(
% 1.60/0.59    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 1.60/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 1.60/0.59  fof(f115,plain,(
% 1.60/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k3_tarski(k1_enumset1(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0),k4_xboole_0(X0,X1)))) )),
% 1.60/0.59    inference(superposition,[],[f42,f45])).
% 1.60/0.59  fof(f45,plain,(
% 1.60/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 1.60/0.59    inference(definition_unfolding,[],[f27,f29,f29])).
% 1.60/0.59  fof(f27,plain,(
% 1.60/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f10])).
% 1.60/0.59  fof(f10,axiom,(
% 1.60/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.60/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.60/0.59  fof(f891,plain,(
% 1.60/0.59    ( ! [X8,X9] : (r1_tarski(k4_xboole_0(X8,X9),k5_xboole_0(X8,X9))) )),
% 1.60/0.59    inference(superposition,[],[f26,f162])).
% 1.60/0.59  fof(f162,plain,(
% 1.60/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X1),X0))) )),
% 1.60/0.59    inference(forward_demodulation,[],[f161,f69])).
% 1.60/0.59  fof(f69,plain,(
% 1.60/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 1.60/0.59    inference(superposition,[],[f43,f46])).
% 1.60/0.59  fof(f46,plain,(
% 1.60/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.60/0.59    inference(definition_unfolding,[],[f28,f32,f32])).
% 1.60/0.59  fof(f32,plain,(
% 1.60/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.60/0.59    inference(cnf_transformation,[],[f8])).
% 1.60/0.59  fof(f8,axiom,(
% 1.60/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.60/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.60/0.59  fof(f28,plain,(
% 1.60/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f1])).
% 1.60/0.59  fof(f1,axiom,(
% 1.60/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.60/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.60/0.59  fof(f43,plain,(
% 1.60/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.60/0.59    inference(definition_unfolding,[],[f31,f32])).
% 1.60/0.59  fof(f31,plain,(
% 1.60/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.60/0.59    inference(cnf_transformation,[],[f4])).
% 1.60/0.59  fof(f4,axiom,(
% 1.60/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.60/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.60/0.59  fof(f161,plain,(
% 1.60/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X1),X0))) )),
% 1.60/0.59    inference(forward_demodulation,[],[f143,f63])).
% 1.60/0.59  fof(f63,plain,(
% 1.60/0.59    ( ! [X0] : (k4_xboole_0(X0,k5_xboole_0(X0,X0)) = X0) )),
% 1.60/0.59    inference(backward_demodulation,[],[f55,f61])).
% 1.60/0.59  fof(f61,plain,(
% 1.60/0.59    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 1.60/0.59    inference(superposition,[],[f43,f55])).
% 1.60/0.59  fof(f55,plain,(
% 1.60/0.59    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.60/0.59    inference(resolution,[],[f47,f50])).
% 1.60/0.59  fof(f50,plain,(
% 1.60/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.60/0.59    inference(equality_resolution,[],[f37])).
% 1.60/0.59  fof(f37,plain,(
% 1.60/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.60/0.59    inference(cnf_transformation,[],[f24])).
% 1.60/0.59  fof(f24,plain,(
% 1.60/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.60/0.59    inference(flattening,[],[f23])).
% 1.60/0.59  fof(f23,plain,(
% 1.60/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.60/0.59    inference(nnf_transformation,[],[f3])).
% 1.60/0.59  fof(f3,axiom,(
% 1.60/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.60/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.60/0.59  fof(f47,plain,(
% 1.60/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 1.60/0.59    inference(definition_unfolding,[],[f34,f32])).
% 1.60/0.59  fof(f34,plain,(
% 1.60/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f17])).
% 1.60/0.59  fof(f17,plain,(
% 1.60/0.59    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.60/0.59    inference(ennf_transformation,[],[f6])).
% 1.60/0.59  fof(f6,axiom,(
% 1.60/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.60/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.60/0.59  fof(f143,plain,(
% 1.60/0.59    ( ! [X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X1),X0)) = k5_xboole_0(k4_xboole_0(X0,k5_xboole_0(X0,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 1.60/0.59    inference(superposition,[],[f48,f61])).
% 1.60/0.59  fof(f48,plain,(
% 1.60/0.59    ( ! [X2,X0,X1] : (k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(k5_xboole_0(X0,X2),X1))) )),
% 1.60/0.59    inference(definition_unfolding,[],[f39,f32,f32,f32])).
% 1.60/0.59  fof(f39,plain,(
% 1.60/0.59    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f5])).
% 1.60/0.59  fof(f5,axiom,(
% 1.60/0.59    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 1.60/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).
% 1.60/0.59  fof(f26,plain,(
% 1.60/0.59    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f7])).
% 1.60/0.59  fof(f7,axiom,(
% 1.60/0.59    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.60/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.60/0.59  fof(f986,plain,(
% 1.60/0.59    spl2_1),
% 1.60/0.59    inference(avatar_contradiction_clause,[],[f957])).
% 1.60/0.59  fof(f957,plain,(
% 1.60/0.59    $false | spl2_1),
% 1.60/0.59    inference(resolution,[],[f891,f106])).
% 1.60/0.59  fof(f106,plain,(
% 1.60/0.59    ~r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) | spl2_1),
% 1.60/0.59    inference(resolution,[],[f100,f35])).
% 1.60/0.59  fof(f100,plain,(
% 1.60/0.59    ~r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | spl2_1),
% 1.60/0.59    inference(avatar_component_clause,[],[f98])).
% 1.60/0.59  fof(f98,plain,(
% 1.60/0.59    spl2_1 <=> r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 1.60/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.60/0.59  fof(f105,plain,(
% 1.60/0.59    ~spl2_1 | ~spl2_2),
% 1.60/0.59    inference(avatar_split_clause,[],[f96,f102,f98])).
% 1.60/0.59  fof(f96,plain,(
% 1.60/0.59    ~r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | ~r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 1.60/0.59    inference(resolution,[],[f44,f49])).
% 1.60/0.59  fof(f49,plain,(
% 1.60/0.59    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.60/0.59    inference(definition_unfolding,[],[f40,f41])).
% 1.60/0.59  fof(f40,plain,(
% 1.60/0.59    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f20])).
% 1.60/0.59  fof(f20,plain,(
% 1.60/0.59    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.60/0.59    inference(flattening,[],[f19])).
% 1.60/0.59  fof(f19,plain,(
% 1.60/0.59    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.60/0.59    inference(ennf_transformation,[],[f9])).
% 1.60/0.59  fof(f9,axiom,(
% 1.60/0.59    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 1.60/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 1.60/0.59  fof(f44,plain,(
% 1.60/0.59    ~r1_tarski(k3_tarski(k1_enumset1(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0)))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 1.60/0.59    inference(definition_unfolding,[],[f25,f41])).
% 1.60/0.59  fof(f25,plain,(
% 1.60/0.59    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 1.60/0.59    inference(cnf_transformation,[],[f22])).
% 1.60/0.59  fof(f22,plain,(
% 1.60/0.59    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 1.60/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f21])).
% 1.60/0.59  fof(f21,plain,(
% 1.60/0.59    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) => ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 1.60/0.59    introduced(choice_axiom,[])).
% 1.60/0.59  fof(f16,plain,(
% 1.60/0.59    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 1.60/0.59    inference(ennf_transformation,[],[f15])).
% 1.60/0.59  fof(f15,negated_conjecture,(
% 1.60/0.59    ~! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 1.60/0.59    inference(negated_conjecture,[],[f14])).
% 1.60/0.59  fof(f14,conjecture,(
% 1.60/0.59    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 1.60/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_zfmisc_1)).
% 1.60/0.59  % SZS output end Proof for theBenchmark
% 1.60/0.59  % (31674)------------------------------
% 1.60/0.59  % (31674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.59  % (31674)Termination reason: Refutation
% 1.60/0.59  
% 1.60/0.59  % (31674)Memory used [KB]: 11641
% 1.60/0.59  % (31674)Time elapsed: 0.162 s
% 1.60/0.59  % (31674)------------------------------
% 1.60/0.59  % (31674)------------------------------
% 1.60/0.61  % (31670)Refutation not found, incomplete strategy% (31670)------------------------------
% 1.60/0.61  % (31670)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.61  % (31670)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.61  
% 1.60/0.61  % (31670)Memory used [KB]: 6140
% 1.60/0.61  % (31670)Time elapsed: 0.216 s
% 1.60/0.61  % (31670)------------------------------
% 1.60/0.61  % (31670)------------------------------
% 1.60/0.62  % (31667)Success in time 0.254 s
%------------------------------------------------------------------------------
