%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 384 expanded)
%              Number of leaves         :   17 ( 120 expanded)
%              Depth                    :   13
%              Number of atoms          :  172 ( 794 expanded)
%              Number of equality atoms :   38 ( 171 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f708,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f424,f564,f616,f696,f706])).

fof(f706,plain,
    ( ~ spl5_16
    | spl5_23 ),
    inference(avatar_contradiction_clause,[],[f701])).

fof(f701,plain,
    ( $false
    | ~ spl5_16
    | spl5_23 ),
    inference(resolution,[],[f700,f614])).

fof(f614,plain,(
    ! [X2] : r1_xboole_0(k1_xboole_0,X2) ),
    inference(subsumption_resolution,[],[f184,f96])).

fof(f96,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f94,f30])).

fof(f30,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r1_xboole_0(X0,X0) ) ),
    inference(superposition,[],[f39,f93])).

fof(f93,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f91,f32])).

fof(f32,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f91,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0) ),
    inference(superposition,[],[f36,f77])).

fof(f77,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f73,f31])).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f73,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f36,f32])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f184,plain,(
    ! [X2] :
      ( r2_hidden(sK4(k1_xboole_0,X2),k1_xboole_0)
      | r1_xboole_0(k1_xboole_0,X2) ) ),
    inference(superposition,[],[f38,f62])).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f59,f30])).

fof(f59,plain,(
    ! [X2,X1] :
      ( ~ r1_xboole_0(X2,X1)
      | k1_xboole_0 = k3_xboole_0(X1,X2) ) ),
    inference(resolution,[],[f46,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f39,f33])).

fof(f33,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f700,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl5_16
    | spl5_23 ),
    inference(forward_demodulation,[],[f698,f635])).

fof(f635,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK0))
    | ~ spl5_16 ),
    inference(superposition,[],[f631,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f631,plain,
    ( k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,sK1),sK0)
    | ~ spl5_16 ),
    inference(resolution,[],[f559,f59])).

fof(f559,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f557])).

fof(f557,plain,
    ( spl5_16
  <=> r1_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f698,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,k3_xboole_0(sK1,sK0)),k3_xboole_0(sK0,k3_xboole_0(sK1,sK0)))
    | spl5_23 ),
    inference(resolution,[],[f656,f180])).

fof(f180,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(X2,X3)
      | ~ r1_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X2,X3)) ) ),
    inference(resolution,[],[f38,f94])).

fof(f656,plain,
    ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK0))
    | spl5_23 ),
    inference(avatar_component_clause,[],[f655])).

fof(f655,plain,
    ( spl5_23
  <=> r1_xboole_0(sK0,k3_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f696,plain,(
    ~ spl5_23 ),
    inference(avatar_contradiction_clause,[],[f691])).

fof(f691,plain,
    ( $false
    | ~ spl5_23 ),
    inference(resolution,[],[f679,f614])).

fof(f679,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl5_23 ),
    inference(backward_demodulation,[],[f324,f673])).

fof(f673,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK0)
    | ~ spl5_23 ),
    inference(forward_demodulation,[],[f665,f93])).

fof(f665,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,k3_xboole_0(sK0,sK0))
    | ~ spl5_23 ),
    inference(superposition,[],[f663,f43])).

fof(f663,plain,
    ( k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK0),sK0)
    | ~ spl5_23 ),
    inference(resolution,[],[f657,f59])).

fof(f657,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK0))
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f655])).

fof(f324,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK0)) ),
    inference(resolution,[],[f180,f44])).

fof(f44,plain,(
    ~ r1_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f40,f27])).

fof(f27,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    & r1_tarski(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      & r1_tarski(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f616,plain,(
    ~ spl5_17 ),
    inference(avatar_contradiction_clause,[],[f615])).

fof(f615,plain,
    ( $false
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f563,f96])).

fof(f563,plain,
    ( r2_hidden(sK4(sK0,k3_xboole_0(sK0,sK1)),k1_xboole_0)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f561])).

fof(f561,plain,
    ( spl5_17
  <=> r2_hidden(sK4(sK0,k3_xboole_0(sK0,sK1)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f564,plain,
    ( spl5_16
    | spl5_17
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f549,f390,f561,f557])).

fof(f390,plain,
    ( spl5_8
  <=> r1_xboole_0(sK1,k3_xboole_0(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f549,plain,
    ( r2_hidden(sK4(sK0,k3_xboole_0(sK0,sK1)),k1_xboole_0)
    | r1_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl5_8 ),
    inference(superposition,[],[f38,f542])).

fof(f542,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f535,f31])).

fof(f535,plain,
    ( k3_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl5_8 ),
    inference(superposition,[],[f359,f434])).

fof(f434,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,k3_xboole_0(sK0,sK1))
    | ~ spl5_8 ),
    inference(superposition,[],[f427,f43])).

fof(f427,plain,
    ( k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK2,sK0),sK1)
    | ~ spl5_8 ),
    inference(resolution,[],[f392,f59])).

fof(f392,plain,
    ( r1_xboole_0(sK1,k3_xboole_0(sK2,sK0))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f390])).

fof(f359,plain,(
    ! [X11] : k3_xboole_0(sK0,k3_xboole_0(sK2,X11)) = k3_xboole_0(sK0,X11) ),
    inference(superposition,[],[f43,f78])).

fof(f78,plain,(
    sK0 = k3_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f75,f32])).

fof(f75,plain,(
    k3_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f36,f56])).

fof(f56,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f42,f28])).

fof(f28,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f424,plain,(
    spl5_8 ),
    inference(avatar_contradiction_clause,[],[f421])).

fof(f421,plain,
    ( $false
    | spl5_8 ),
    inference(resolution,[],[f419,f30])).

fof(f419,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl5_8 ),
    inference(forward_demodulation,[],[f417,f361])).

fof(f361,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,k3_xboole_0(sK2,sK0)) ),
    inference(superposition,[],[f43,f64])).

fof(f64,plain,(
    k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0) ),
    inference(resolution,[],[f59,f29])).

fof(f29,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f417,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK2,sK0)),k3_xboole_0(sK1,k3_xboole_0(sK2,sK0)))
    | spl5_8 ),
    inference(resolution,[],[f391,f180])).

fof(f391,plain,
    ( ~ r1_xboole_0(sK1,k3_xboole_0(sK2,sK0))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f390])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:57:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (17711)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (17717)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (17716)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (17728)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.47  % (17713)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (17715)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (17725)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (17727)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.48  % (17724)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (17719)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (17714)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (17720)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (17712)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (17726)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (17718)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % (17723)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.50  % (17722)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.50  % (17727)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f708,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f424,f564,f616,f696,f706])).
% 0.21/0.50  fof(f706,plain,(
% 0.21/0.50    ~spl5_16 | spl5_23),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f701])).
% 0.21/0.50  fof(f701,plain,(
% 0.21/0.50    $false | (~spl5_16 | spl5_23)),
% 0.21/0.50    inference(resolution,[],[f700,f614])).
% 0.21/0.50  fof(f614,plain,(
% 0.21/0.50    ( ! [X2] : (r1_xboole_0(k1_xboole_0,X2)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f184,f96])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(resolution,[],[f94,f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r1_xboole_0(X0,X0)) )),
% 0.21/0.50    inference(superposition,[],[f39,f93])).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.21/0.50    inference(forward_demodulation,[],[f91,f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0)) )),
% 0.21/0.50    inference(superposition,[],[f36,f77])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f73,f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 0.21/0.50    inference(superposition,[],[f36,f32])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.50    inference(rectify,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.50  fof(f184,plain,(
% 0.21/0.50    ( ! [X2] : (r2_hidden(sK4(k1_xboole_0,X2),k1_xboole_0) | r1_xboole_0(k1_xboole_0,X2)) )),
% 0.21/0.50    inference(superposition,[],[f38,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.50    inference(resolution,[],[f59,f30])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~r1_xboole_0(X2,X1) | k1_xboole_0 = k3_xboole_0(X1,X2)) )),
% 0.21/0.50    inference(resolution,[],[f46,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.50    inference(resolution,[],[f39,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f700,plain,(
% 0.21/0.50    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl5_16 | spl5_23)),
% 0.21/0.50    inference(forward_demodulation,[],[f698,f635])).
% 0.21/0.50  fof(f635,plain,(
% 0.21/0.50    k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK0)) | ~spl5_16),
% 0.21/0.50    inference(superposition,[],[f631,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.21/0.50  fof(f631,plain,(
% 0.21/0.50    k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,sK1),sK0) | ~spl5_16),
% 0.21/0.50    inference(resolution,[],[f559,f59])).
% 0.21/0.50  fof(f559,plain,(
% 0.21/0.50    r1_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | ~spl5_16),
% 0.21/0.50    inference(avatar_component_clause,[],[f557])).
% 0.21/0.50  fof(f557,plain,(
% 0.21/0.50    spl5_16 <=> r1_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.50  fof(f698,plain,(
% 0.21/0.50    ~r1_xboole_0(k3_xboole_0(sK0,k3_xboole_0(sK1,sK0)),k3_xboole_0(sK0,k3_xboole_0(sK1,sK0))) | spl5_23),
% 0.21/0.50    inference(resolution,[],[f656,f180])).
% 0.21/0.50  fof(f180,plain,(
% 0.21/0.50    ( ! [X2,X3] : (r1_xboole_0(X2,X3) | ~r1_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X2,X3))) )),
% 0.21/0.50    inference(resolution,[],[f38,f94])).
% 0.21/0.50  fof(f656,plain,(
% 0.21/0.50    ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK0)) | spl5_23),
% 0.21/0.50    inference(avatar_component_clause,[],[f655])).
% 0.21/0.50  fof(f655,plain,(
% 0.21/0.50    spl5_23 <=> r1_xboole_0(sK0,k3_xboole_0(sK1,sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.21/0.50  fof(f696,plain,(
% 0.21/0.50    ~spl5_23),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f691])).
% 0.21/0.50  fof(f691,plain,(
% 0.21/0.50    $false | ~spl5_23),
% 0.21/0.50    inference(resolution,[],[f679,f614])).
% 0.21/0.50  fof(f679,plain,(
% 0.21/0.50    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl5_23),
% 0.21/0.50    inference(backward_demodulation,[],[f324,f673])).
% 0.21/0.50  fof(f673,plain,(
% 0.21/0.50    k1_xboole_0 = k3_xboole_0(sK1,sK0) | ~spl5_23),
% 0.21/0.50    inference(forward_demodulation,[],[f665,f93])).
% 0.21/0.50  fof(f665,plain,(
% 0.21/0.50    k1_xboole_0 = k3_xboole_0(sK1,k3_xboole_0(sK0,sK0)) | ~spl5_23),
% 0.21/0.50    inference(superposition,[],[f663,f43])).
% 0.21/0.50  fof(f663,plain,(
% 0.21/0.50    k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK0),sK0) | ~spl5_23),
% 0.21/0.50    inference(resolution,[],[f657,f59])).
% 0.21/0.50  fof(f657,plain,(
% 0.21/0.50    r1_xboole_0(sK0,k3_xboole_0(sK1,sK0)) | ~spl5_23),
% 0.21/0.50    inference(avatar_component_clause,[],[f655])).
% 0.21/0.50  fof(f324,plain,(
% 0.21/0.50    ~r1_xboole_0(k3_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK0))),
% 0.21/0.50    inference(resolution,[],[f180,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ~r1_xboole_0(sK1,sK0)),
% 0.21/0.50    inference(resolution,[],[f40,f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ~r1_xboole_0(sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.21/0.50    inference(negated_conjecture,[],[f13])).
% 0.21/0.50  fof(f13,conjecture,(
% 0.21/0.50    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).
% 0.21/0.50  fof(f616,plain,(
% 0.21/0.50    ~spl5_17),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f615])).
% 0.21/0.50  fof(f615,plain,(
% 0.21/0.50    $false | ~spl5_17),
% 0.21/0.50    inference(subsumption_resolution,[],[f563,f96])).
% 0.21/0.50  fof(f563,plain,(
% 0.21/0.50    r2_hidden(sK4(sK0,k3_xboole_0(sK0,sK1)),k1_xboole_0) | ~spl5_17),
% 0.21/0.50    inference(avatar_component_clause,[],[f561])).
% 0.21/0.50  fof(f561,plain,(
% 0.21/0.50    spl5_17 <=> r2_hidden(sK4(sK0,k3_xboole_0(sK0,sK1)),k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.50  fof(f564,plain,(
% 0.21/0.50    spl5_16 | spl5_17 | ~spl5_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f549,f390,f561,f557])).
% 0.21/0.50  fof(f390,plain,(
% 0.21/0.50    spl5_8 <=> r1_xboole_0(sK1,k3_xboole_0(sK2,sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.50  fof(f549,plain,(
% 0.21/0.50    r2_hidden(sK4(sK0,k3_xboole_0(sK0,sK1)),k1_xboole_0) | r1_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | ~spl5_8),
% 0.21/0.50    inference(superposition,[],[f38,f542])).
% 0.21/0.50  fof(f542,plain,(
% 0.21/0.50    k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | ~spl5_8),
% 0.21/0.50    inference(forward_demodulation,[],[f535,f31])).
% 0.21/0.50  fof(f535,plain,(
% 0.21/0.50    k3_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | ~spl5_8),
% 0.21/0.50    inference(superposition,[],[f359,f434])).
% 0.21/0.50  fof(f434,plain,(
% 0.21/0.50    k1_xboole_0 = k3_xboole_0(sK2,k3_xboole_0(sK0,sK1)) | ~spl5_8),
% 0.21/0.50    inference(superposition,[],[f427,f43])).
% 0.21/0.50  fof(f427,plain,(
% 0.21/0.50    k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK2,sK0),sK1) | ~spl5_8),
% 0.21/0.50    inference(resolution,[],[f392,f59])).
% 0.21/0.50  fof(f392,plain,(
% 0.21/0.50    r1_xboole_0(sK1,k3_xboole_0(sK2,sK0)) | ~spl5_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f390])).
% 0.21/0.50  fof(f359,plain,(
% 0.21/0.50    ( ! [X11] : (k3_xboole_0(sK0,k3_xboole_0(sK2,X11)) = k3_xboole_0(sK0,X11)) )),
% 0.21/0.50    inference(superposition,[],[f43,f78])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    sK0 = k3_xboole_0(sK0,sK2)),
% 0.21/0.50    inference(forward_demodulation,[],[f75,f32])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    k3_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0)),
% 0.21/0.50    inference(superposition,[],[f36,f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 0.21/0.50    inference(resolution,[],[f42,f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    r1_tarski(sK0,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.21/0.50    inference(nnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.50  fof(f424,plain,(
% 0.21/0.50    spl5_8),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f421])).
% 0.21/0.50  fof(f421,plain,(
% 0.21/0.50    $false | spl5_8),
% 0.21/0.50    inference(resolution,[],[f419,f30])).
% 0.21/0.50  fof(f419,plain,(
% 0.21/0.50    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | spl5_8),
% 0.21/0.50    inference(forward_demodulation,[],[f417,f361])).
% 0.21/0.50  fof(f361,plain,(
% 0.21/0.50    k1_xboole_0 = k3_xboole_0(sK1,k3_xboole_0(sK2,sK0))),
% 0.21/0.50    inference(superposition,[],[f43,f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)),
% 0.21/0.50    inference(resolution,[],[f59,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f417,plain,(
% 0.21/0.50    ~r1_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK2,sK0)),k3_xboole_0(sK1,k3_xboole_0(sK2,sK0))) | spl5_8),
% 0.21/0.50    inference(resolution,[],[f391,f180])).
% 0.21/0.50  fof(f391,plain,(
% 0.21/0.50    ~r1_xboole_0(sK1,k3_xboole_0(sK2,sK0)) | spl5_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f390])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (17727)------------------------------
% 0.21/0.50  % (17727)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (17727)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (17727)Memory used [KB]: 6396
% 0.21/0.50  % (17727)Time elapsed: 0.077 s
% 0.21/0.50  % (17727)------------------------------
% 0.21/0.50  % (17727)------------------------------
% 0.21/0.50  % (17710)Success in time 0.143 s
%------------------------------------------------------------------------------
