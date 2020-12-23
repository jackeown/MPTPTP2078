%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:06 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 160 expanded)
%              Number of leaves         :   20 (  59 expanded)
%              Depth                    :   12
%              Number of atoms          :  117 ( 252 expanded)
%              Number of equality atoms :   61 ( 166 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f465,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f55,f59,f110,f464])).

fof(f464,plain,
    ( spl4_1
    | spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f459,f108,f53,f49])).

fof(f49,plain,
    ( spl4_1
  <=> sK0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f53,plain,
    ( spl4_2
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f108,plain,
    ( spl4_4
  <=> k3_enumset1(sK2,sK2,sK2,sK2,sK3) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK3),k3_enumset1(sK0,sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f459,plain,
    ( sK0 = sK2
    | sK0 = sK3
    | ~ spl4_4 ),
    inference(resolution,[],[f435,f44])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f29,f42,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f31,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f36,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f27,f41])).

fof(f27,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f435,plain,
    ( ! [X3] :
        ( ~ r1_tarski(k3_enumset1(X3,X3,X3,X3,X3),k3_enumset1(sK0,sK0,sK0,sK0,sK1))
        | sK2 = X3
        | sK3 = X3 )
    | ~ spl4_4 ),
    inference(resolution,[],[f428,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X2))
      | X0 = X1
      | X0 = X2 ) ),
    inference(definition_unfolding,[],[f38,f42,f41])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

% (15138)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% (15150)Refutation not found, incomplete strategy% (15150)------------------------------
% (15150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15150)Termination reason: Refutation not found, incomplete strategy

% (15150)Memory used [KB]: 10618
% (15150)Time elapsed: 0.166 s
% (15150)------------------------------
% (15150)------------------------------
% (15155)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f18,plain,(
    ! [X0,X1,X2] :
      ( X0 = X2
      | X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

fof(f428,plain,
    ( ! [X16] :
        ( r1_tarski(X16,k3_enumset1(sK2,sK2,sK2,sK2,sK3))
        | ~ r1_tarski(X16,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) )
    | ~ spl4_4 ),
    inference(superposition,[],[f225,f109])).

fof(f109,plain,
    ( k3_enumset1(sK2,sK2,sK2,sK2,sK3) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK3),k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f225,plain,(
    ! [X4,X2,X3] :
      ( r1_tarski(X2,k5_xboole_0(X3,k4_xboole_0(X4,X3)))
      | ~ r1_tarski(X2,X3) ) ),
    inference(forward_demodulation,[],[f224,f137])).

fof(f137,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k4_xboole_0(k4_xboole_0(X2,X3),X2)) = X2 ),
    inference(superposition,[],[f103,f45])).

fof(f45,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f30,f33,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f103,plain,(
    ! [X4,X3] : k5_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X3,k4_xboole_0(X3,X4))) = X3 ),
    inference(resolution,[],[f77,f28])).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f77,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | k5_xboole_0(X1,k4_xboole_0(X2,X1)) = X2 ) ),
    inference(forward_demodulation,[],[f70,f25])).

fof(f25,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f70,plain,(
    ! [X2,X1] :
      ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k5_xboole_0(X2,k1_xboole_0)
      | ~ r1_tarski(X1,X2) ) ),
    inference(superposition,[],[f45,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f224,plain,(
    ! [X4,X2,X3] :
      ( r1_tarski(k5_xboole_0(X2,k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X4)),X2)),k5_xboole_0(X3,k4_xboole_0(X4,X3)))
      | ~ r1_tarski(X2,X3) ) ),
    inference(forward_demodulation,[],[f190,f26])).

fof(f26,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f190,plain,(
    ! [X4,X2,X3] :
      ( r1_tarski(k5_xboole_0(k4_xboole_0(X2,k1_xboole_0),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X4)),k4_xboole_0(X2,k1_xboole_0))),k5_xboole_0(X3,k4_xboole_0(X4,X3)))
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f46,f35])).

fof(f46,plain,(
    ! [X2,X0,X1] : r1_tarski(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f37,f33,f32,f32,f33])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f37,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f110,plain,
    ( spl4_4
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f105,f57,f108])).

fof(f57,plain,
    ( spl4_3
  <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f105,plain,
    ( k3_enumset1(sK2,sK2,sK2,sK2,sK3) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK3),k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | ~ spl4_3 ),
    inference(resolution,[],[f77,f58])).

fof(f58,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK3))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f59,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f43,f57])).

fof(f43,plain,(
    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK3)) ),
    inference(definition_unfolding,[],[f22,f41,f41])).

fof(f22,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( sK0 != sK3
    & sK0 != sK2
    & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK0 != sK3
      & sK0 != sK2
      & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(f55,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f23,f53])).

fof(f23,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f20])).

fof(f51,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f24,f49])).

fof(f24,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:48:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (15156)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.51  % (15148)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.51  % (15140)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (15134)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (15133)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (15133)Refutation not found, incomplete strategy% (15133)------------------------------
% 0.22/0.53  % (15133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (15133)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (15133)Memory used [KB]: 1663
% 0.22/0.53  % (15133)Time elapsed: 0.112 s
% 0.22/0.53  % (15133)------------------------------
% 0.22/0.53  % (15133)------------------------------
% 0.22/0.54  % (15137)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (15136)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (15135)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (15146)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  % (15153)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (15149)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (15152)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (15151)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.47/0.55  % (15161)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.47/0.55  % (15162)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.47/0.55  % (15144)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.47/0.55  % (15141)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.47/0.55  % (15143)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.47/0.55  % (15144)Refutation not found, incomplete strategy% (15144)------------------------------
% 1.47/0.55  % (15144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.55  % (15144)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.55  
% 1.47/0.55  % (15144)Memory used [KB]: 10618
% 1.47/0.55  % (15144)Time elapsed: 0.137 s
% 1.47/0.55  % (15144)------------------------------
% 1.47/0.55  % (15144)------------------------------
% 1.47/0.55  % (15143)Refutation not found, incomplete strategy% (15143)------------------------------
% 1.47/0.55  % (15143)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.55  % (15143)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.55  
% 1.47/0.55  % (15143)Memory used [KB]: 10618
% 1.47/0.55  % (15143)Time elapsed: 0.136 s
% 1.47/0.55  % (15143)------------------------------
% 1.47/0.55  % (15143)------------------------------
% 1.47/0.56  % (15139)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.47/0.56  % (15160)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.47/0.56  % (15150)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.47/0.56  % (15157)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.47/0.56  % (15159)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.47/0.56  % (15145)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.47/0.56  % (15142)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.47/0.57  % (15142)Refutation not found, incomplete strategy% (15142)------------------------------
% 1.47/0.57  % (15142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.57  % (15142)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.57  
% 1.47/0.57  % (15142)Memory used [KB]: 10618
% 1.47/0.57  % (15142)Time elapsed: 0.147 s
% 1.47/0.57  % (15142)------------------------------
% 1.47/0.57  % (15142)------------------------------
% 1.47/0.57  % (15154)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.60/0.57  % (15158)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.60/0.57  % (15152)Refutation found. Thanks to Tanya!
% 1.60/0.57  % SZS status Theorem for theBenchmark
% 1.60/0.57  % SZS output start Proof for theBenchmark
% 1.60/0.58  fof(f465,plain,(
% 1.60/0.58    $false),
% 1.60/0.58    inference(avatar_sat_refutation,[],[f51,f55,f59,f110,f464])).
% 1.60/0.58  fof(f464,plain,(
% 1.60/0.58    spl4_1 | spl4_2 | ~spl4_4),
% 1.60/0.58    inference(avatar_split_clause,[],[f459,f108,f53,f49])).
% 1.60/0.58  fof(f49,plain,(
% 1.60/0.58    spl4_1 <=> sK0 = sK3),
% 1.60/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.60/0.58  fof(f53,plain,(
% 1.60/0.58    spl4_2 <=> sK0 = sK2),
% 1.60/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.60/0.58  fof(f108,plain,(
% 1.60/0.58    spl4_4 <=> k3_enumset1(sK2,sK2,sK2,sK2,sK3) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK3),k3_enumset1(sK0,sK0,sK0,sK0,sK1)))),
% 1.60/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.60/0.58  fof(f459,plain,(
% 1.60/0.58    sK0 = sK2 | sK0 = sK3 | ~spl4_4),
% 1.60/0.58    inference(resolution,[],[f435,f44])).
% 1.60/0.58  fof(f44,plain,(
% 1.60/0.58    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.60/0.58    inference(definition_unfolding,[],[f29,f42,f41])).
% 1.60/0.58  fof(f41,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.60/0.58    inference(definition_unfolding,[],[f31,f40])).
% 1.60/0.58  fof(f40,plain,(
% 1.60/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.60/0.58    inference(definition_unfolding,[],[f36,f39])).
% 1.60/0.58  fof(f39,plain,(
% 1.60/0.58    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f12])).
% 1.60/0.58  fof(f12,axiom,(
% 1.60/0.58    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.60/0.58  fof(f36,plain,(
% 1.60/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f11])).
% 1.60/0.58  fof(f11,axiom,(
% 1.60/0.58    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.60/0.58  fof(f31,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f10])).
% 1.60/0.58  fof(f10,axiom,(
% 1.60/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.60/0.58  fof(f42,plain,(
% 1.60/0.58    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.60/0.58    inference(definition_unfolding,[],[f27,f41])).
% 1.60/0.58  fof(f27,plain,(
% 1.60/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f9])).
% 1.60/0.58  fof(f9,axiom,(
% 1.60/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.60/0.58  fof(f29,plain,(
% 1.60/0.58    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 1.60/0.58    inference(cnf_transformation,[],[f13])).
% 1.60/0.58  fof(f13,axiom,(
% 1.60/0.58    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 1.60/0.58  fof(f435,plain,(
% 1.60/0.58    ( ! [X3] : (~r1_tarski(k3_enumset1(X3,X3,X3,X3,X3),k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | sK2 = X3 | sK3 = X3) ) | ~spl4_4),
% 1.60/0.58    inference(resolution,[],[f428,f47])).
% 1.60/0.58  fof(f47,plain,(
% 1.60/0.58    ( ! [X2,X0,X1] : (~r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X2)) | X0 = X1 | X0 = X2) )),
% 1.60/0.58    inference(definition_unfolding,[],[f38,f42,f41])).
% 1.60/0.58  fof(f38,plain,(
% 1.60/0.58    ( ! [X2,X0,X1] : (X0 = X2 | X0 = X1 | ~r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 1.60/0.58    inference(cnf_transformation,[],[f18])).
% 1.60/0.58  % (15138)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.60/0.58  % (15150)Refutation not found, incomplete strategy% (15150)------------------------------
% 1.60/0.58  % (15150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.58  % (15150)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.58  
% 1.60/0.58  % (15150)Memory used [KB]: 10618
% 1.60/0.58  % (15150)Time elapsed: 0.166 s
% 1.60/0.58  % (15150)------------------------------
% 1.60/0.58  % (15150)------------------------------
% 1.60/0.59  % (15155)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.60/0.60  fof(f18,plain,(
% 1.60/0.60    ! [X0,X1,X2] : (X0 = X2 | X0 = X1 | ~r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.60/0.60    inference(ennf_transformation,[],[f14])).
% 1.60/0.60  fof(f14,axiom,(
% 1.60/0.60    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).
% 1.60/0.60  fof(f428,plain,(
% 1.60/0.60    ( ! [X16] : (r1_tarski(X16,k3_enumset1(sK2,sK2,sK2,sK2,sK3)) | ~r1_tarski(X16,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) ) | ~spl4_4),
% 1.60/0.60    inference(superposition,[],[f225,f109])).
% 1.60/0.60  fof(f109,plain,(
% 1.60/0.60    k3_enumset1(sK2,sK2,sK2,sK2,sK3) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK3),k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | ~spl4_4),
% 1.60/0.60    inference(avatar_component_clause,[],[f108])).
% 1.60/0.60  fof(f225,plain,(
% 1.60/0.60    ( ! [X4,X2,X3] : (r1_tarski(X2,k5_xboole_0(X3,k4_xboole_0(X4,X3))) | ~r1_tarski(X2,X3)) )),
% 1.60/0.60    inference(forward_demodulation,[],[f224,f137])).
% 1.60/0.60  fof(f137,plain,(
% 1.60/0.60    ( ! [X2,X3] : (k5_xboole_0(X2,k4_xboole_0(k4_xboole_0(X2,X3),X2)) = X2) )),
% 1.60/0.60    inference(superposition,[],[f103,f45])).
% 1.60/0.60  fof(f45,plain,(
% 1.60/0.60    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 1.60/0.60    inference(definition_unfolding,[],[f30,f33,f33])).
% 1.60/0.60  fof(f33,plain,(
% 1.60/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.60/0.60    inference(cnf_transformation,[],[f8])).
% 1.60/0.60  fof(f8,axiom,(
% 1.60/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.60/0.60  fof(f30,plain,(
% 1.60/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.60/0.60    inference(cnf_transformation,[],[f1])).
% 1.60/0.60  fof(f1,axiom,(
% 1.60/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.60/0.60  fof(f103,plain,(
% 1.60/0.60    ( ! [X4,X3] : (k5_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X3,k4_xboole_0(X3,X4))) = X3) )),
% 1.60/0.60    inference(resolution,[],[f77,f28])).
% 1.60/0.60  fof(f28,plain,(
% 1.60/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.60/0.60    inference(cnf_transformation,[],[f4])).
% 1.60/0.60  fof(f4,axiom,(
% 1.60/0.60    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.60/0.60  fof(f77,plain,(
% 1.60/0.60    ( ! [X2,X1] : (~r1_tarski(X1,X2) | k5_xboole_0(X1,k4_xboole_0(X2,X1)) = X2) )),
% 1.60/0.60    inference(forward_demodulation,[],[f70,f25])).
% 1.60/0.60  fof(f25,plain,(
% 1.60/0.60    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.60/0.60    inference(cnf_transformation,[],[f7])).
% 1.60/0.60  fof(f7,axiom,(
% 1.60/0.60    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.60/0.60  fof(f70,plain,(
% 1.60/0.60    ( ! [X2,X1] : (k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k5_xboole_0(X2,k1_xboole_0) | ~r1_tarski(X1,X2)) )),
% 1.60/0.60    inference(superposition,[],[f45,f35])).
% 1.60/0.60  fof(f35,plain,(
% 1.60/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.60/0.60    inference(cnf_transformation,[],[f21])).
% 1.60/0.60  fof(f21,plain,(
% 1.60/0.60    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.60/0.60    inference(nnf_transformation,[],[f2])).
% 1.60/0.60  fof(f2,axiom,(
% 1.60/0.60    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.60/0.60  fof(f224,plain,(
% 1.60/0.60    ( ! [X4,X2,X3] : (r1_tarski(k5_xboole_0(X2,k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X4)),X2)),k5_xboole_0(X3,k4_xboole_0(X4,X3))) | ~r1_tarski(X2,X3)) )),
% 1.60/0.60    inference(forward_demodulation,[],[f190,f26])).
% 1.60/0.60  fof(f26,plain,(
% 1.60/0.60    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.60/0.60    inference(cnf_transformation,[],[f5])).
% 1.60/0.60  fof(f5,axiom,(
% 1.60/0.60    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.60/0.60  fof(f190,plain,(
% 1.60/0.60    ( ! [X4,X2,X3] : (r1_tarski(k5_xboole_0(k4_xboole_0(X2,k1_xboole_0),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X4)),k4_xboole_0(X2,k1_xboole_0))),k5_xboole_0(X3,k4_xboole_0(X4,X3))) | ~r1_tarski(X2,X3)) )),
% 1.60/0.60    inference(superposition,[],[f46,f35])).
% 1.60/0.60  fof(f46,plain,(
% 1.60/0.60    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k5_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 1.60/0.60    inference(definition_unfolding,[],[f37,f33,f32,f32,f33])).
% 1.60/0.60  fof(f32,plain,(
% 1.60/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.60/0.60    inference(cnf_transformation,[],[f6])).
% 1.60/0.60  fof(f6,axiom,(
% 1.60/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.60/0.60  fof(f37,plain,(
% 1.60/0.60    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 1.60/0.60    inference(cnf_transformation,[],[f3])).
% 1.60/0.60  fof(f3,axiom,(
% 1.60/0.60    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).
% 1.60/0.60  fof(f110,plain,(
% 1.60/0.60    spl4_4 | ~spl4_3),
% 1.60/0.60    inference(avatar_split_clause,[],[f105,f57,f108])).
% 1.60/0.60  fof(f57,plain,(
% 1.60/0.60    spl4_3 <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK3))),
% 1.60/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.60/0.60  fof(f105,plain,(
% 1.60/0.60    k3_enumset1(sK2,sK2,sK2,sK2,sK3) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK3),k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | ~spl4_3),
% 1.60/0.60    inference(resolution,[],[f77,f58])).
% 1.60/0.60  fof(f58,plain,(
% 1.60/0.60    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK3)) | ~spl4_3),
% 1.60/0.60    inference(avatar_component_clause,[],[f57])).
% 1.60/0.60  fof(f59,plain,(
% 1.60/0.60    spl4_3),
% 1.60/0.60    inference(avatar_split_clause,[],[f43,f57])).
% 1.60/0.60  fof(f43,plain,(
% 1.60/0.60    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK3))),
% 1.60/0.60    inference(definition_unfolding,[],[f22,f41,f41])).
% 1.60/0.60  fof(f22,plain,(
% 1.60/0.60    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 1.60/0.60    inference(cnf_transformation,[],[f20])).
% 1.60/0.60  fof(f20,plain,(
% 1.60/0.60    sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 1.60/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f19])).
% 1.60/0.60  fof(f19,plain,(
% 1.60/0.60    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)))),
% 1.60/0.60    introduced(choice_axiom,[])).
% 1.60/0.60  fof(f17,plain,(
% 1.60/0.60    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.60/0.60    inference(ennf_transformation,[],[f16])).
% 1.60/0.60  fof(f16,negated_conjecture,(
% 1.60/0.60    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.60/0.60    inference(negated_conjecture,[],[f15])).
% 1.60/0.60  fof(f15,conjecture,(
% 1.60/0.60    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).
% 1.60/0.60  fof(f55,plain,(
% 1.60/0.60    ~spl4_2),
% 1.60/0.60    inference(avatar_split_clause,[],[f23,f53])).
% 1.60/0.60  fof(f23,plain,(
% 1.60/0.60    sK0 != sK2),
% 1.60/0.60    inference(cnf_transformation,[],[f20])).
% 1.60/0.60  fof(f51,plain,(
% 1.60/0.60    ~spl4_1),
% 1.60/0.60    inference(avatar_split_clause,[],[f24,f49])).
% 1.60/0.60  fof(f24,plain,(
% 1.60/0.60    sK0 != sK3),
% 1.60/0.60    inference(cnf_transformation,[],[f20])).
% 1.60/0.60  % SZS output end Proof for theBenchmark
% 1.60/0.60  % (15152)------------------------------
% 1.60/0.60  % (15152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.60  % (15152)Termination reason: Refutation
% 1.60/0.60  
% 1.60/0.60  % (15152)Memory used [KB]: 11001
% 1.60/0.60  % (15152)Time elapsed: 0.164 s
% 1.60/0.60  % (15152)------------------------------
% 1.60/0.60  % (15152)------------------------------
% 1.60/0.60  % (15147)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.60/0.60  % (15132)Success in time 0.234 s
%------------------------------------------------------------------------------
