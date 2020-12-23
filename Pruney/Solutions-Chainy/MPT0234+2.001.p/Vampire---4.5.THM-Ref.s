%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 107 expanded)
%              Number of leaves         :   18 (  45 expanded)
%              Depth                    :    9
%              Number of atoms          :   98 ( 172 expanded)
%              Number of equality atoms :   65 ( 124 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (12115)Termination reason: Refutation not found, incomplete strategy

% (12115)Memory used [KB]: 1663
fof(f105,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f43,f51,f56,f97,f103,f104])).

% (12115)Time elapsed: 0.097 s
% (12115)------------------------------
% (12115)------------------------------
fof(f104,plain,
    ( k2_tarski(sK0,sK0) != k5_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK1,sK1))
    | k2_tarski(sK0,sK1) != k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1))
    | k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f103,plain,
    ( spl2_10
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f98,f53,f48,f100])).

fof(f100,plain,
    ( spl2_10
  <=> k2_tarski(sK0,sK0) = k5_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f48,plain,
    ( spl2_3
  <=> k2_tarski(sK1,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f53,plain,
    ( spl2_4
  <=> k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f98,plain,
    ( k2_tarski(sK0,sK0) = k5_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK1,sK1))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f89,f50])).

fof(f50,plain,
    ( k2_tarski(sK1,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f89,plain,
    ( k2_tarski(sK0,sK0) = k5_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0)))
    | ~ spl2_4 ),
    inference(superposition,[],[f28,f55])).

fof(f55,plain,
    ( k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK1,sK1))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f23,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f97,plain,
    ( spl2_9
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f92,f53,f48,f94])).

fof(f94,plain,
    ( spl2_9
  <=> k2_tarski(sK0,sK1) = k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f92,plain,
    ( k2_tarski(sK0,sK1) = k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f91,f50])).

fof(f91,plain,
    ( k2_tarski(sK0,sK1) = k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0)))
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f90,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f22,f18,f24,f18])).

fof(f18,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f22,plain,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

fof(f90,plain,
    ( k2_tarski(sK0,sK1) = k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))),k4_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK1)))))
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f88,f30])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f20,f24,f24])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f88,plain,
    ( k2_tarski(sK0,sK1) = k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))),k4_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0)))))
    | ~ spl2_4 ),
    inference(superposition,[],[f31,f55])).

fof(f31,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = X0 ),
    inference(definition_unfolding,[],[f21,f27,f24])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f25,f24])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f56,plain,
    ( spl2_4
    | spl2_2 ),
    inference(avatar_split_clause,[],[f44,f40,f53])).

fof(f40,plain,
    ( spl2_2
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f44,plain,
    ( k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK1,sK1))
    | spl2_2 ),
    inference(unit_resulting_resolution,[],[f42,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X0,X1),k2_tarski(X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f26,f18,f18])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_zfmisc_1)).

fof(f42,plain,
    ( sK0 != sK1
    | spl2_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f51,plain,
    ( spl2_3
    | spl2_2 ),
    inference(avatar_split_clause,[],[f46,f40,f48])).

fof(f46,plain,
    ( k2_tarski(sK1,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))
    | spl2_2 ),
    inference(forward_demodulation,[],[f45,f19])).

fof(f19,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f45,plain,
    ( k2_tarski(sK1,sK1) = k4_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK0,sK0))
    | spl2_2 ),
    inference(unit_resulting_resolution,[],[f42,f33])).

fof(f43,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f16,f40])).

fof(f16,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    & sK0 != sK1 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( k2_tarski(X0,X1) != k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
        & X0 != X1 )
   => ( k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
      & sK0 != sK1 ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k2_tarski(X0,X1) != k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( X0 != X1
       => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( X0 != X1
     => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

fof(f38,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f29,f35])).

fof(f35,plain,
    ( spl2_1
  <=> k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f29,plain,(
    k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)) ),
    inference(definition_unfolding,[],[f17,f18,f18])).

fof(f17,plain,(
    k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:20:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (12117)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.49  % (12130)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.49  % (12132)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.49  % (12121)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.49  % (12141)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.49  % (12122)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.49  % (12123)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.50  % (12138)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.50  % (12115)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.50  % (12124)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.50  % (12132)Refutation not found, incomplete strategy% (12132)------------------------------
% 0.20/0.50  % (12132)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (12140)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.50  % (12137)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.50  % (12115)Refutation not found, incomplete strategy% (12115)------------------------------
% 0.20/0.50  % (12115)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (12140)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  % (12115)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (12115)Memory used [KB]: 1663
% 0.20/0.50  fof(f105,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f38,f43,f51,f56,f97,f103,f104])).
% 0.20/0.50  % (12115)Time elapsed: 0.097 s
% 0.20/0.50  % (12115)------------------------------
% 0.20/0.50  % (12115)------------------------------
% 0.20/0.50  fof(f104,plain,(
% 0.20/0.50    k2_tarski(sK0,sK0) != k5_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK1,sK1)) | k2_tarski(sK0,sK1) != k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1)) | k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))),
% 0.20/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.50  fof(f103,plain,(
% 0.20/0.50    spl2_10 | ~spl2_3 | ~spl2_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f98,f53,f48,f100])).
% 0.20/0.50  fof(f100,plain,(
% 0.20/0.50    spl2_10 <=> k2_tarski(sK0,sK0) = k5_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK1,sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    spl2_3 <=> k2_tarski(sK1,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    spl2_4 <=> k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK1,sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.50  fof(f98,plain,(
% 0.20/0.50    k2_tarski(sK0,sK0) = k5_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK1,sK1)) | (~spl2_3 | ~spl2_4)),
% 0.20/0.50    inference(forward_demodulation,[],[f89,f50])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    k2_tarski(sK1,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0)) | ~spl2_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f48])).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    k2_tarski(sK0,sK0) = k5_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))) | ~spl2_4),
% 0.20/0.50    inference(superposition,[],[f28,f55])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK1,sK1)) | ~spl2_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f53])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.20/0.50    inference(definition_unfolding,[],[f23,f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.50  fof(f97,plain,(
% 0.20/0.50    spl2_9 | ~spl2_3 | ~spl2_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f92,f53,f48,f94])).
% 0.20/0.50  fof(f94,plain,(
% 0.20/0.50    spl2_9 <=> k2_tarski(sK0,sK1) = k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.50  fof(f92,plain,(
% 0.20/0.50    k2_tarski(sK0,sK1) = k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1)) | (~spl2_3 | ~spl2_4)),
% 0.20/0.50    inference(forward_demodulation,[],[f91,f50])).
% 0.20/0.50  fof(f91,plain,(
% 0.20/0.50    k2_tarski(sK0,sK1) = k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))) | ~spl2_4),
% 0.20/0.50    inference(forward_demodulation,[],[f90,f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1)))) )),
% 0.20/0.50    inference(definition_unfolding,[],[f22,f18,f24,f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).
% 0.20/0.50  fof(f90,plain,(
% 0.20/0.50    k2_tarski(sK0,sK1) = k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))),k4_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK1))))) | ~spl2_4),
% 0.20/0.50    inference(forward_demodulation,[],[f88,f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.20/0.50    inference(definition_unfolding,[],[f20,f24,f24])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    k2_tarski(sK0,sK1) = k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))),k4_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))))) | ~spl2_4),
% 0.20/0.50    inference(superposition,[],[f31,f55])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = X0) )),
% 0.20/0.50    inference(definition_unfolding,[],[f21,f27,f24])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.20/0.50    inference(definition_unfolding,[],[f25,f24])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    spl2_4 | spl2_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f44,f40,f53])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    spl2_2 <=> sK0 = sK1),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK1,sK1)) | spl2_2),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f42,f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X0,X1),k2_tarski(X1,X1)) | X0 = X1) )),
% 0.20/0.50    inference(definition_unfolding,[],[f26,f18,f18])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) | X0 = X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) | X0 = X1)),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0,X1] : (X0 != X1 => k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_zfmisc_1)).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    sK0 != sK1 | spl2_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f40])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    spl2_3 | spl2_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f46,f40,f48])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    k2_tarski(sK1,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0)) | spl2_2),
% 0.20/0.50    inference(forward_demodulation,[],[f45,f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    k2_tarski(sK1,sK1) = k4_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK0,sK0)) | spl2_2),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f42,f33])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ~spl2_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f16,f40])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    sK0 != sK1),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) & sK0 != sK1),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ? [X0,X1] : (k2_tarski(X0,X1) != k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) & X0 != X1) => (k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) & sK0 != sK1)),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ? [X0,X1] : (k2_tarski(X0,X1) != k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) & X0 != X1)),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1] : (X0 != X1 => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.20/0.50    inference(negated_conjecture,[],[f10])).
% 0.20/0.50  fof(f10,conjecture,(
% 0.20/0.50    ! [X0,X1] : (X0 != X1 => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ~spl2_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f29,f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    spl2_1 <=> k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))),
% 0.20/0.50    inference(definition_unfolding,[],[f17,f18,f18])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (12140)------------------------------
% 0.20/0.50  % (12140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (12140)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (12140)Memory used [KB]: 6268
% 0.20/0.50  % (12140)Time elapsed: 0.089 s
% 0.20/0.50  % (12140)------------------------------
% 0.20/0.50  % (12140)------------------------------
% 0.20/0.50  % (12132)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  % (12114)Success in time 0.145 s
%------------------------------------------------------------------------------
