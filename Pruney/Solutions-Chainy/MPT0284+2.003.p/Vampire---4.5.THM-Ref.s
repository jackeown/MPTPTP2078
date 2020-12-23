%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:39 EST 2020

% Result     : Theorem 0.95s
% Output     : Refutation 0.95s
% Verified   : 
% Statistics : Number of formulae       :   50 (  89 expanded)
%              Number of leaves         :   12 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :   91 ( 152 expanded)
%              Number of equality atoms :   17 (  47 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f157,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f120,f156])).

fof(f156,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f155])).

fof(f155,plain,
    ( $false
    | spl2_2 ),
    inference(subsumption_resolution,[],[f154,f49])).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X0))) ),
    inference(superposition,[],[f44,f37])).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f22,f23,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(resolution,[],[f38,f40])).

fof(f40,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_tarski(k1_enumset1(X0,X0,X1)),X2)
      | r1_tarski(X0,X2) ) ),
    inference(definition_unfolding,[],[f31,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f154,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK0),k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))
    | spl2_2 ),
    inference(resolution,[],[f80,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f80,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl2_2
  <=> r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f120,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f119])).

% (8963)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
fof(f119,plain,
    ( $false
    | spl2_1 ),
    inference(subsumption_resolution,[],[f118,f44])).

fof(f118,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))
    | spl2_1 ),
    inference(resolution,[],[f76,f27])).

fof(f76,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl2_1
  <=> r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f81,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f72,f78,f74])).

fof(f72,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))
    | ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) ),
    inference(resolution,[],[f36,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f33])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f36,plain,(
    ~ r1_tarski(k3_tarski(k1_enumset1(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0)))),k1_zfmisc_1(k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) ),
    inference(definition_unfolding,[],[f21,f33,f34])).

fof(f34,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k3_tarski(k1_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f26,f33])).

fof(f26,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f21,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f17])).

fof(f17,plain,
    ( ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))
   => ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:35:15 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.35  ipcrm: permission denied for id (731119617)
% 0.19/0.36  ipcrm: permission denied for id (731185155)
% 0.19/0.38  ipcrm: permission denied for id (731447318)
% 0.19/0.38  ipcrm: permission denied for id (731512857)
% 0.19/0.38  ipcrm: permission denied for id (731545626)
% 0.19/0.38  ipcrm: permission denied for id (731643933)
% 0.19/0.39  ipcrm: permission denied for id (731709471)
% 0.19/0.39  ipcrm: permission denied for id (731742240)
% 0.19/0.39  ipcrm: permission denied for id (731807778)
% 0.19/0.40  ipcrm: permission denied for id (731840550)
% 0.19/0.40  ipcrm: permission denied for id (731971627)
% 0.19/0.41  ipcrm: permission denied for id (732135473)
% 0.19/0.42  ipcrm: permission denied for id (732430397)
% 0.19/0.43  ipcrm: permission denied for id (732528708)
% 0.19/0.44  ipcrm: permission denied for id (732725327)
% 0.19/0.44  ipcrm: permission denied for id (732856403)
% 0.19/0.45  ipcrm: permission denied for id (733053021)
% 0.19/0.45  ipcrm: permission denied for id (733118559)
% 0.19/0.45  ipcrm: permission denied for id (733151328)
% 0.19/0.45  ipcrm: permission denied for id (733184098)
% 0.19/0.45  ipcrm: permission denied for id (733249636)
% 0.19/0.46  ipcrm: permission denied for id (733282405)
% 0.19/0.46  ipcrm: permission denied for id (733446252)
% 0.19/0.47  ipcrm: permission denied for id (733544562)
% 0.19/0.47  ipcrm: permission denied for id (733577331)
% 0.19/0.47  ipcrm: permission denied for id (733610101)
% 0.19/0.48  ipcrm: permission denied for id (733675639)
% 0.19/0.48  ipcrm: permission denied for id (733741178)
% 0.19/0.48  ipcrm: permission denied for id (733773947)
% 0.19/0.49  ipcrm: permission denied for id (733839487)
% 0.95/0.63  % (8956)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.95/0.64  % (8946)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.95/0.64  % (8948)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.95/0.64  % (8956)Refutation not found, incomplete strategy% (8956)------------------------------
% 0.95/0.64  % (8956)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.95/0.64  % (8956)Termination reason: Refutation not found, incomplete strategy
% 0.95/0.64  
% 0.95/0.64  % (8956)Memory used [KB]: 1663
% 0.95/0.64  % (8956)Time elapsed: 0.084 s
% 0.95/0.64  % (8956)------------------------------
% 0.95/0.64  % (8956)------------------------------
% 0.95/0.64  % (8950)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.95/0.65  % (8948)Refutation found. Thanks to Tanya!
% 0.95/0.65  % SZS status Theorem for theBenchmark
% 0.95/0.65  % SZS output start Proof for theBenchmark
% 0.95/0.65  fof(f157,plain,(
% 0.95/0.65    $false),
% 0.95/0.65    inference(avatar_sat_refutation,[],[f81,f120,f156])).
% 0.95/0.65  fof(f156,plain,(
% 0.95/0.65    spl2_2),
% 0.95/0.65    inference(avatar_contradiction_clause,[],[f155])).
% 0.95/0.65  fof(f155,plain,(
% 0.95/0.65    $false | spl2_2),
% 0.95/0.65    inference(subsumption_resolution,[],[f154,f49])).
% 0.95/0.65  fof(f49,plain,(
% 0.95/0.65    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X0)))) )),
% 0.95/0.65    inference(superposition,[],[f44,f37])).
% 0.95/0.65  fof(f37,plain,(
% 0.95/0.65    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 0.95/0.65    inference(definition_unfolding,[],[f22,f23,f23])).
% 0.95/0.65  fof(f23,plain,(
% 0.95/0.65    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.95/0.65    inference(cnf_transformation,[],[f7])).
% 0.95/0.65  fof(f7,axiom,(
% 0.95/0.65    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.95/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.95/0.65  fof(f22,plain,(
% 0.95/0.65    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.95/0.65    inference(cnf_transformation,[],[f6])).
% 0.95/0.65  fof(f6,axiom,(
% 0.95/0.65    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.95/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.95/0.65  fof(f44,plain,(
% 0.95/0.65    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 0.95/0.65    inference(resolution,[],[f38,f40])).
% 0.95/0.65  fof(f40,plain,(
% 0.95/0.65    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.95/0.65    inference(equality_resolution,[],[f29])).
% 0.95/0.65  fof(f29,plain,(
% 0.95/0.65    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.95/0.65    inference(cnf_transformation,[],[f20])).
% 0.95/0.65  fof(f20,plain,(
% 0.95/0.65    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.95/0.65    inference(flattening,[],[f19])).
% 0.95/0.65  fof(f19,plain,(
% 0.95/0.65    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.95/0.65    inference(nnf_transformation,[],[f2])).
% 0.95/0.65  fof(f2,axiom,(
% 0.95/0.65    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.95/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.95/0.65  fof(f38,plain,(
% 0.95/0.65    ( ! [X2,X0,X1] : (~r1_tarski(k3_tarski(k1_enumset1(X0,X0,X1)),X2) | r1_tarski(X0,X2)) )),
% 0.95/0.65    inference(definition_unfolding,[],[f31,f33])).
% 0.95/0.65  fof(f33,plain,(
% 0.95/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 0.95/0.65    inference(definition_unfolding,[],[f24,f23])).
% 0.95/0.65  fof(f24,plain,(
% 0.95/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.95/0.65    inference(cnf_transformation,[],[f8])).
% 0.95/0.65  fof(f8,axiom,(
% 0.95/0.65    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.95/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.95/0.65  fof(f31,plain,(
% 0.95/0.65    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.95/0.65    inference(cnf_transformation,[],[f14])).
% 0.95/0.65  fof(f14,plain,(
% 0.95/0.65    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.95/0.65    inference(ennf_transformation,[],[f4])).
% 0.95/0.65  fof(f4,axiom,(
% 0.95/0.65    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.95/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.95/0.65  fof(f154,plain,(
% 0.95/0.65    ~r1_tarski(k4_xboole_0(sK1,sK0),k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) | spl2_2),
% 0.95/0.65    inference(resolution,[],[f80,f27])).
% 0.95/0.65  fof(f27,plain,(
% 0.95/0.65    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.95/0.65    inference(cnf_transformation,[],[f13])).
% 0.95/0.65  fof(f13,plain,(
% 0.95/0.65    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.95/0.65    inference(ennf_transformation,[],[f9])).
% 0.95/0.65  fof(f9,axiom,(
% 0.95/0.65    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 0.95/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 0.95/0.65  fof(f80,plain,(
% 0.95/0.65    ~r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) | spl2_2),
% 0.95/0.65    inference(avatar_component_clause,[],[f78])).
% 0.95/0.65  fof(f78,plain,(
% 0.95/0.65    spl2_2 <=> r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))),
% 0.95/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.95/0.65  fof(f120,plain,(
% 0.95/0.65    spl2_1),
% 0.95/0.65    inference(avatar_contradiction_clause,[],[f119])).
% 0.95/0.65  % (8963)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.95/0.65  fof(f119,plain,(
% 0.95/0.65    $false | spl2_1),
% 0.95/0.65    inference(subsumption_resolution,[],[f118,f44])).
% 0.95/0.65  fof(f118,plain,(
% 0.95/0.65    ~r1_tarski(k4_xboole_0(sK0,sK1),k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) | spl2_1),
% 0.95/0.65    inference(resolution,[],[f76,f27])).
% 0.95/0.65  fof(f76,plain,(
% 0.95/0.65    ~r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) | spl2_1),
% 0.95/0.65    inference(avatar_component_clause,[],[f74])).
% 0.95/0.65  fof(f74,plain,(
% 0.95/0.65    spl2_1 <=> r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))),
% 0.95/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.95/0.65  fof(f81,plain,(
% 0.95/0.65    ~spl2_1 | ~spl2_2),
% 0.95/0.65    inference(avatar_split_clause,[],[f72,f78,f74])).
% 0.95/0.65  fof(f72,plain,(
% 0.95/0.65    ~r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) | ~r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))),
% 0.95/0.65    inference(resolution,[],[f36,f39])).
% 0.95/0.65  fof(f39,plain,(
% 0.95/0.65    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.95/0.65    inference(definition_unfolding,[],[f32,f33])).
% 0.95/0.65  fof(f32,plain,(
% 0.95/0.65    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.95/0.65    inference(cnf_transformation,[],[f16])).
% 0.95/0.65  fof(f16,plain,(
% 0.95/0.65    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.95/0.65    inference(flattening,[],[f15])).
% 0.95/0.65  fof(f15,plain,(
% 0.95/0.65    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.95/0.65    inference(ennf_transformation,[],[f5])).
% 0.95/0.65  fof(f5,axiom,(
% 0.95/0.65    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.95/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.95/0.65  fof(f36,plain,(
% 0.95/0.65    ~r1_tarski(k3_tarski(k1_enumset1(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0)))),k1_zfmisc_1(k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))),
% 0.95/0.65    inference(definition_unfolding,[],[f21,f33,f34])).
% 0.95/0.65  fof(f34,plain,(
% 0.95/0.65    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k3_tarski(k1_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) )),
% 0.95/0.65    inference(definition_unfolding,[],[f26,f33])).
% 0.95/0.65  fof(f26,plain,(
% 0.95/0.65    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.95/0.65    inference(cnf_transformation,[],[f1])).
% 0.95/0.65  fof(f1,axiom,(
% 0.95/0.65    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.95/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.95/0.65  fof(f21,plain,(
% 0.95/0.65    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 0.95/0.65    inference(cnf_transformation,[],[f18])).
% 0.95/0.65  fof(f18,plain,(
% 0.95/0.65    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 0.95/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f17])).
% 0.95/0.65  fof(f17,plain,(
% 0.95/0.65    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) => ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 0.95/0.65    introduced(choice_axiom,[])).
% 0.95/0.65  fof(f12,plain,(
% 0.95/0.65    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 0.95/0.65    inference(ennf_transformation,[],[f11])).
% 0.95/0.65  fof(f11,negated_conjecture,(
% 0.95/0.65    ~! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 0.95/0.65    inference(negated_conjecture,[],[f10])).
% 0.95/0.65  fof(f10,conjecture,(
% 0.95/0.65    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 0.95/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_zfmisc_1)).
% 0.95/0.65  % SZS output end Proof for theBenchmark
% 0.95/0.65  % (8948)------------------------------
% 0.95/0.65  % (8948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.95/0.65  % (8948)Termination reason: Refutation
% 0.95/0.65  
% 0.95/0.65  % (8948)Memory used [KB]: 10746
% 0.95/0.65  % (8948)Time elapsed: 0.094 s
% 0.95/0.65  % (8948)------------------------------
% 0.95/0.65  % (8948)------------------------------
% 0.95/0.65  % (8780)Success in time 0.299 s
%------------------------------------------------------------------------------
