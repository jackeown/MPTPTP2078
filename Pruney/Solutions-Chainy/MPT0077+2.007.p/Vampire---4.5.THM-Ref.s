%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:44 EST 2020

% Result     : Theorem 2.01s
% Output     : Refutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 187 expanded)
%              Number of leaves         :   20 (  69 expanded)
%              Depth                    :   10
%              Number of atoms          :  210 ( 422 expanded)
%              Number of equality atoms :   27 (  80 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3783,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f84,f85,f1508,f1510,f2467,f2638,f2643,f3327,f3759,f3782])).

fof(f3782,plain,(
    spl4_39 ),
    inference(avatar_contradiction_clause,[],[f3781])).

fof(f3781,plain,
    ( $false
    | spl4_39 ),
    inference(resolution,[],[f3780,f46])).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f3780,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | spl4_39 ),
    inference(resolution,[],[f3326,f1483])).

fof(f1483,plain,(
    ! [X2,X1] :
      ( r1_tarski(X2,k2_xboole_0(X2,X1))
      | ~ r1_tarski(k1_xboole_0,X1) ) ),
    inference(superposition,[],[f1455,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1455,plain,(
    ! [X43,X44] :
      ( r1_tarski(X43,k2_xboole_0(X44,X43))
      | ~ r1_tarski(k1_xboole_0,X44) ) ),
    inference(superposition,[],[f68,f239])).

fof(f239,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f233,f48])).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f233,plain,(
    ! [X2,X1] : k2_xboole_0(k3_xboole_0(X1,X2),X1) = X1 ),
    inference(forward_demodulation,[],[f226,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f226,plain,(
    ! [X2,X1] : k2_xboole_0(k3_xboole_0(X1,X2),X1) = k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) ),
    inference(superposition,[],[f55,f56])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).

fof(f3326,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
    | spl4_39 ),
    inference(avatar_component_clause,[],[f3324])).

fof(f3324,plain,
    ( spl4_39
  <=> r1_tarski(sK1,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f3759,plain,
    ( ~ spl4_1
    | spl4_2
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f3758])).

fof(f3758,plain,
    ( $false
    | ~ spl4_1
    | spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f3359,f3735])).

fof(f3735,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK1)
    | ~ spl4_1
    | spl4_2 ),
    inference(superposition,[],[f3361,f3129])).

fof(f3129,plain,
    ( ! [X33] : k3_xboole_0(sK0,X33) = k3_xboole_0(sK0,k2_xboole_0(X33,sK2))
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f3128,f239])).

fof(f3128,plain,
    ( ! [X33] : k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X33)) = k3_xboole_0(sK0,k2_xboole_0(X33,sK2))
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f3048,f53])).

fof(f3048,plain,
    ( ! [X33] : k3_xboole_0(sK0,k2_xboole_0(X33,sK2)) = k2_xboole_0(k3_xboole_0(sK0,X33),k1_xboole_0)
    | ~ spl4_1 ),
    inference(superposition,[],[f64,f2645])).

fof(f2645,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl4_1 ),
    inference(resolution,[],[f74,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f74,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl4_1
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f64,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f3361,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | spl4_2 ),
    inference(resolution,[],[f77,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f77,plain,
    ( ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl4_2
  <=> r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f3359,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl4_3 ),
    inference(resolution,[],[f83,f62])).

fof(f83,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl4_3
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f3327,plain,
    ( ~ spl4_19
    | ~ spl4_39
    | ~ spl4_2
    | spl4_3 ),
    inference(avatar_split_clause,[],[f3290,f81,f76,f3324,f2460])).

fof(f2460,plain,
    ( spl4_19
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f3290,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,sK0)
    | ~ spl4_2
    | spl4_3 ),
    inference(resolution,[],[f2416,f78])).

fof(f78,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f2416,plain,
    ( ! [X54,X53] :
        ( ~ r1_xboole_0(X53,X54)
        | ~ r1_tarski(sK1,X54)
        | ~ r1_tarski(sK0,X53) )
    | spl4_3 ),
    inference(resolution,[],[f70,f82])).

fof(f82,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X1,X3)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).

fof(f2643,plain,
    ( ~ spl4_11
    | spl4_19 ),
    inference(avatar_contradiction_clause,[],[f2642])).

fof(f2642,plain,
    ( $false
    | ~ spl4_11
    | spl4_19 ),
    inference(resolution,[],[f2462,f1507])).

fof(f1507,plain,
    ( ! [X28] : r1_tarski(X28,X28)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f1506])).

fof(f1506,plain,
    ( spl4_11
  <=> ! [X28] : r1_tarski(X28,X28) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f2462,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl4_19 ),
    inference(avatar_component_clause,[],[f2460])).

fof(f2638,plain,(
    spl4_20 ),
    inference(avatar_contradiction_clause,[],[f2637])).

fof(f2637,plain,
    ( $false
    | spl4_20 ),
    inference(resolution,[],[f2636,f46])).

fof(f2636,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | spl4_20 ),
    inference(resolution,[],[f2466,f1455])).

fof(f2466,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | spl4_20 ),
    inference(avatar_component_clause,[],[f2464])).

fof(f2464,plain,
    ( spl4_20
  <=> r1_tarski(sK2,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f2467,plain,
    ( ~ spl4_19
    | ~ spl4_20
    | spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f2429,f76,f72,f2464,f2460])).

fof(f2429,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,sK0)
    | spl4_1
    | ~ spl4_2 ),
    inference(resolution,[],[f2415,f78])).

fof(f2415,plain,
    ( ! [X52,X51] :
        ( ~ r1_xboole_0(X51,X52)
        | ~ r1_tarski(sK2,X52)
        | ~ r1_tarski(sK0,X51) )
    | spl4_1 ),
    inference(resolution,[],[f70,f73])).

fof(f73,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f1510,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f1509])).

fof(f1509,plain,
    ( $false
    | spl4_10 ),
    inference(resolution,[],[f1504,f46])).

fof(f1504,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f1502])).

fof(f1502,plain,
    ( spl4_10
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f1508,plain,
    ( ~ spl4_10
    | spl4_11 ),
    inference(avatar_split_clause,[],[f1497,f1506,f1502])).

fof(f1497,plain,(
    ! [X28] :
      ( r1_tarski(X28,X28)
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ) ),
    inference(superposition,[],[f1455,f239])).

fof(f85,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f40,f72,f81,f76])).

fof(f40,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
      & ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_xboole_0(sK0,sK1) ) )
    | ( r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK0,sK1)
      & ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f35])).

fof(f35,plain,
    ( ? [X0,X1,X2] :
        ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ( ~ r1_xboole_0(X0,X2)
            | ~ r1_xboole_0(X0,X1) ) )
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) )
   => ( ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
        & ( ~ r1_xboole_0(sK0,sK2)
          | ~ r1_xboole_0(sK0,sK1) ) )
      | ( r1_xboole_0(sK0,sK2)
        & r1_xboole_0(sK0,sK1)
        & ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
        & ( ~ r1_xboole_0(X0,X2)
          | ~ r1_xboole_0(X0,X1) ) )
      | ( r1_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
            & ~ ( r1_xboole_0(X0,X2)
                & r1_xboole_0(X0,X1) ) )
        & ~ ( r1_xboole_0(X0,X2)
            & r1_xboole_0(X0,X1)
            & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f84,plain,
    ( spl4_3
    | spl4_2 ),
    inference(avatar_split_clause,[],[f44,f76,f81])).

fof(f44,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f79,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f45,f76,f72])).

fof(f45,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:34:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.44  % (8213)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.46  % (8214)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.46  % (8219)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (8220)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (8223)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (8226)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (8227)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (8228)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (8217)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (8222)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (8218)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (8224)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (8215)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (8230)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.50  % (8216)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.50  % (8225)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.51  % (8221)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.52  % (8229)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 2.01/0.62  % (8229)Refutation found. Thanks to Tanya!
% 2.01/0.62  % SZS status Theorem for theBenchmark
% 2.01/0.62  % SZS output start Proof for theBenchmark
% 2.01/0.62  fof(f3783,plain,(
% 2.01/0.62    $false),
% 2.01/0.62    inference(avatar_sat_refutation,[],[f79,f84,f85,f1508,f1510,f2467,f2638,f2643,f3327,f3759,f3782])).
% 2.01/0.62  fof(f3782,plain,(
% 2.01/0.62    spl4_39),
% 2.01/0.62    inference(avatar_contradiction_clause,[],[f3781])).
% 2.01/0.62  fof(f3781,plain,(
% 2.01/0.62    $false | spl4_39),
% 2.01/0.62    inference(resolution,[],[f3780,f46])).
% 2.01/0.62  fof(f46,plain,(
% 2.01/0.62    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.01/0.62    inference(cnf_transformation,[],[f7])).
% 2.01/0.62  fof(f7,axiom,(
% 2.01/0.62    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.01/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.01/0.62  fof(f3780,plain,(
% 2.01/0.62    ~r1_tarski(k1_xboole_0,sK2) | spl4_39),
% 2.01/0.62    inference(resolution,[],[f3326,f1483])).
% 2.01/0.62  fof(f1483,plain,(
% 2.01/0.62    ( ! [X2,X1] : (r1_tarski(X2,k2_xboole_0(X2,X1)) | ~r1_tarski(k1_xboole_0,X1)) )),
% 2.01/0.62    inference(superposition,[],[f1455,f53])).
% 2.01/0.62  fof(f53,plain,(
% 2.01/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.01/0.62    inference(cnf_transformation,[],[f1])).
% 2.01/0.62  fof(f1,axiom,(
% 2.01/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.01/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.01/0.62  fof(f1455,plain,(
% 2.01/0.62    ( ! [X43,X44] : (r1_tarski(X43,k2_xboole_0(X44,X43)) | ~r1_tarski(k1_xboole_0,X44)) )),
% 2.01/0.62    inference(superposition,[],[f68,f239])).
% 2.01/0.62  fof(f239,plain,(
% 2.01/0.62    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.01/0.62    inference(superposition,[],[f233,f48])).
% 2.01/0.62  fof(f48,plain,(
% 2.01/0.62    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.01/0.62    inference(cnf_transformation,[],[f6])).
% 2.01/0.62  fof(f6,axiom,(
% 2.01/0.62    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.01/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 2.01/0.62  fof(f233,plain,(
% 2.01/0.62    ( ! [X2,X1] : (k2_xboole_0(k3_xboole_0(X1,X2),X1) = X1) )),
% 2.01/0.62    inference(forward_demodulation,[],[f226,f58])).
% 2.01/0.62  fof(f58,plain,(
% 2.01/0.62    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 2.01/0.62    inference(cnf_transformation,[],[f19])).
% 2.01/0.62  fof(f19,axiom,(
% 2.01/0.62    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 2.01/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 2.01/0.62  fof(f226,plain,(
% 2.01/0.62    ( ! [X2,X1] : (k2_xboole_0(k3_xboole_0(X1,X2),X1) = k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))) )),
% 2.01/0.62    inference(superposition,[],[f55,f56])).
% 2.01/0.62  fof(f56,plain,(
% 2.01/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.01/0.62    inference(cnf_transformation,[],[f15])).
% 2.01/0.62  fof(f15,axiom,(
% 2.01/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.01/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.01/0.62  fof(f55,plain,(
% 2.01/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.01/0.62    inference(cnf_transformation,[],[f9])).
% 2.01/0.62  fof(f9,axiom,(
% 2.01/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.01/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.01/0.62  fof(f68,plain,(
% 2.01/0.62    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 2.01/0.62    inference(cnf_transformation,[],[f31])).
% 2.01/0.62  fof(f31,plain,(
% 2.01/0.62    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 2.01/0.62    inference(ennf_transformation,[],[f23])).
% 2.01/0.62  fof(f23,axiom,(
% 2.01/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)))),
% 2.01/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).
% 2.01/0.62  fof(f3326,plain,(
% 2.01/0.62    ~r1_tarski(sK1,k2_xboole_0(sK1,sK2)) | spl4_39),
% 2.01/0.62    inference(avatar_component_clause,[],[f3324])).
% 2.01/0.62  fof(f3324,plain,(
% 2.01/0.62    spl4_39 <=> r1_tarski(sK1,k2_xboole_0(sK1,sK2))),
% 2.01/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 2.01/0.62  fof(f3759,plain,(
% 2.01/0.62    ~spl4_1 | spl4_2 | ~spl4_3),
% 2.01/0.62    inference(avatar_contradiction_clause,[],[f3758])).
% 2.01/0.62  fof(f3758,plain,(
% 2.01/0.62    $false | (~spl4_1 | spl4_2 | ~spl4_3)),
% 2.01/0.62    inference(subsumption_resolution,[],[f3359,f3735])).
% 2.01/0.62  fof(f3735,plain,(
% 2.01/0.62    k1_xboole_0 != k3_xboole_0(sK0,sK1) | (~spl4_1 | spl4_2)),
% 2.01/0.62    inference(superposition,[],[f3361,f3129])).
% 2.01/0.62  fof(f3129,plain,(
% 2.01/0.62    ( ! [X33] : (k3_xboole_0(sK0,X33) = k3_xboole_0(sK0,k2_xboole_0(X33,sK2))) ) | ~spl4_1),
% 2.01/0.62    inference(forward_demodulation,[],[f3128,f239])).
% 2.01/0.62  fof(f3128,plain,(
% 2.01/0.62    ( ! [X33] : (k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X33)) = k3_xboole_0(sK0,k2_xboole_0(X33,sK2))) ) | ~spl4_1),
% 2.01/0.62    inference(forward_demodulation,[],[f3048,f53])).
% 2.01/0.62  fof(f3048,plain,(
% 2.01/0.62    ( ! [X33] : (k3_xboole_0(sK0,k2_xboole_0(X33,sK2)) = k2_xboole_0(k3_xboole_0(sK0,X33),k1_xboole_0)) ) | ~spl4_1),
% 2.01/0.62    inference(superposition,[],[f64,f2645])).
% 2.01/0.62  fof(f2645,plain,(
% 2.01/0.62    k1_xboole_0 = k3_xboole_0(sK0,sK2) | ~spl4_1),
% 2.01/0.62    inference(resolution,[],[f74,f62])).
% 2.01/0.62  fof(f62,plain,(
% 2.01/0.62    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.01/0.62    inference(cnf_transformation,[],[f39])).
% 2.01/0.62  fof(f39,plain,(
% 2.01/0.62    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.01/0.62    inference(nnf_transformation,[],[f2])).
% 2.01/0.62  fof(f2,axiom,(
% 2.01/0.62    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.01/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.01/0.62  fof(f74,plain,(
% 2.01/0.62    r1_xboole_0(sK0,sK2) | ~spl4_1),
% 2.01/0.62    inference(avatar_component_clause,[],[f72])).
% 2.01/0.62  fof(f72,plain,(
% 2.01/0.62    spl4_1 <=> r1_xboole_0(sK0,sK2)),
% 2.01/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.01/0.62  fof(f64,plain,(
% 2.01/0.62    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 2.01/0.62    inference(cnf_transformation,[],[f5])).
% 2.01/0.62  fof(f5,axiom,(
% 2.01/0.62    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 2.01/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).
% 2.01/0.62  fof(f3361,plain,(
% 2.01/0.62    k1_xboole_0 != k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | spl4_2),
% 2.01/0.62    inference(resolution,[],[f77,f63])).
% 2.01/0.62  fof(f63,plain,(
% 2.01/0.62    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.01/0.62    inference(cnf_transformation,[],[f39])).
% 2.01/0.62  fof(f77,plain,(
% 2.01/0.62    ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | spl4_2),
% 2.01/0.62    inference(avatar_component_clause,[],[f76])).
% 2.01/0.62  fof(f76,plain,(
% 2.01/0.62    spl4_2 <=> r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 2.01/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.01/0.62  fof(f3359,plain,(
% 2.01/0.62    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl4_3),
% 2.01/0.62    inference(resolution,[],[f83,f62])).
% 2.01/0.62  fof(f83,plain,(
% 2.01/0.62    r1_xboole_0(sK0,sK1) | ~spl4_3),
% 2.01/0.62    inference(avatar_component_clause,[],[f81])).
% 2.01/0.62  fof(f81,plain,(
% 2.01/0.62    spl4_3 <=> r1_xboole_0(sK0,sK1)),
% 2.01/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.01/0.62  fof(f3327,plain,(
% 2.01/0.62    ~spl4_19 | ~spl4_39 | ~spl4_2 | spl4_3),
% 2.01/0.62    inference(avatar_split_clause,[],[f3290,f81,f76,f3324,f2460])).
% 2.01/0.62  fof(f2460,plain,(
% 2.01/0.62    spl4_19 <=> r1_tarski(sK0,sK0)),
% 2.01/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 2.01/0.62  fof(f3290,plain,(
% 2.01/0.62    ~r1_tarski(sK1,k2_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,sK0) | (~spl4_2 | spl4_3)),
% 2.01/0.62    inference(resolution,[],[f2416,f78])).
% 2.01/0.62  fof(f78,plain,(
% 2.01/0.62    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl4_2),
% 2.01/0.62    inference(avatar_component_clause,[],[f76])).
% 2.01/0.62  fof(f2416,plain,(
% 2.01/0.62    ( ! [X54,X53] : (~r1_xboole_0(X53,X54) | ~r1_tarski(sK1,X54) | ~r1_tarski(sK0,X53)) ) | spl4_3),
% 2.01/0.62    inference(resolution,[],[f70,f82])).
% 2.01/0.62  fof(f82,plain,(
% 2.01/0.62    ~r1_xboole_0(sK0,sK1) | spl4_3),
% 2.01/0.62    inference(avatar_component_clause,[],[f81])).
% 2.01/0.62  fof(f70,plain,(
% 2.01/0.62    ( ! [X2,X0,X3,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 2.01/0.62    inference(cnf_transformation,[],[f34])).
% 2.01/0.62  fof(f34,plain,(
% 2.01/0.62    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 2.01/0.62    inference(flattening,[],[f33])).
% 2.01/0.62  fof(f33,plain,(
% 2.01/0.62    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 2.01/0.62    inference(ennf_transformation,[],[f21])).
% 2.01/0.62  fof(f21,axiom,(
% 2.01/0.62    ! [X0,X1,X2,X3] : ((r1_xboole_0(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 2.01/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).
% 2.01/0.62  fof(f2643,plain,(
% 2.01/0.62    ~spl4_11 | spl4_19),
% 2.01/0.62    inference(avatar_contradiction_clause,[],[f2642])).
% 2.01/0.62  fof(f2642,plain,(
% 2.01/0.62    $false | (~spl4_11 | spl4_19)),
% 2.01/0.62    inference(resolution,[],[f2462,f1507])).
% 2.01/0.62  fof(f1507,plain,(
% 2.01/0.62    ( ! [X28] : (r1_tarski(X28,X28)) ) | ~spl4_11),
% 2.01/0.62    inference(avatar_component_clause,[],[f1506])).
% 2.01/0.62  fof(f1506,plain,(
% 2.01/0.62    spl4_11 <=> ! [X28] : r1_tarski(X28,X28)),
% 2.01/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 2.01/0.62  fof(f2462,plain,(
% 2.01/0.62    ~r1_tarski(sK0,sK0) | spl4_19),
% 2.01/0.62    inference(avatar_component_clause,[],[f2460])).
% 2.01/0.62  fof(f2638,plain,(
% 2.01/0.62    spl4_20),
% 2.01/0.62    inference(avatar_contradiction_clause,[],[f2637])).
% 2.01/0.62  fof(f2637,plain,(
% 2.01/0.62    $false | spl4_20),
% 2.01/0.62    inference(resolution,[],[f2636,f46])).
% 2.01/0.62  fof(f2636,plain,(
% 2.01/0.62    ~r1_tarski(k1_xboole_0,sK1) | spl4_20),
% 2.01/0.62    inference(resolution,[],[f2466,f1455])).
% 2.01/0.62  fof(f2466,plain,(
% 2.01/0.62    ~r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | spl4_20),
% 2.01/0.62    inference(avatar_component_clause,[],[f2464])).
% 2.01/0.62  fof(f2464,plain,(
% 2.01/0.62    spl4_20 <=> r1_tarski(sK2,k2_xboole_0(sK1,sK2))),
% 2.01/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 2.01/0.62  fof(f2467,plain,(
% 2.01/0.62    ~spl4_19 | ~spl4_20 | spl4_1 | ~spl4_2),
% 2.01/0.62    inference(avatar_split_clause,[],[f2429,f76,f72,f2464,f2460])).
% 2.01/0.62  fof(f2429,plain,(
% 2.01/0.62    ~r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,sK0) | (spl4_1 | ~spl4_2)),
% 2.01/0.62    inference(resolution,[],[f2415,f78])).
% 2.01/0.62  fof(f2415,plain,(
% 2.01/0.62    ( ! [X52,X51] : (~r1_xboole_0(X51,X52) | ~r1_tarski(sK2,X52) | ~r1_tarski(sK0,X51)) ) | spl4_1),
% 2.01/0.62    inference(resolution,[],[f70,f73])).
% 2.01/0.62  fof(f73,plain,(
% 2.01/0.62    ~r1_xboole_0(sK0,sK2) | spl4_1),
% 2.01/0.62    inference(avatar_component_clause,[],[f72])).
% 2.01/0.62  fof(f1510,plain,(
% 2.01/0.62    spl4_10),
% 2.01/0.62    inference(avatar_contradiction_clause,[],[f1509])).
% 2.01/0.62  fof(f1509,plain,(
% 2.01/0.62    $false | spl4_10),
% 2.01/0.62    inference(resolution,[],[f1504,f46])).
% 2.01/0.62  fof(f1504,plain,(
% 2.01/0.62    ~r1_tarski(k1_xboole_0,k1_xboole_0) | spl4_10),
% 2.01/0.62    inference(avatar_component_clause,[],[f1502])).
% 2.01/0.62  fof(f1502,plain,(
% 2.01/0.62    spl4_10 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 2.01/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 2.01/0.62  fof(f1508,plain,(
% 2.01/0.62    ~spl4_10 | spl4_11),
% 2.01/0.62    inference(avatar_split_clause,[],[f1497,f1506,f1502])).
% 2.01/0.62  fof(f1497,plain,(
% 2.01/0.62    ( ! [X28] : (r1_tarski(X28,X28) | ~r1_tarski(k1_xboole_0,k1_xboole_0)) )),
% 2.01/0.62    inference(superposition,[],[f1455,f239])).
% 2.01/0.62  fof(f85,plain,(
% 2.01/0.62    ~spl4_2 | ~spl4_3 | ~spl4_1),
% 2.01/0.62    inference(avatar_split_clause,[],[f40,f72,f81,f76])).
% 2.01/0.62  fof(f40,plain,(
% 2.01/0.62    ~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 2.01/0.62    inference(cnf_transformation,[],[f36])).
% 2.01/0.62  fof(f36,plain,(
% 2.01/0.62    (r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 2.01/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f35])).
% 2.01/0.62  fof(f35,plain,(
% 2.01/0.62    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2)))) => ((r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))))),
% 2.01/0.62    introduced(choice_axiom,[])).
% 2.01/0.62  fof(f27,plain,(
% 2.01/0.62    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.01/0.62    inference(ennf_transformation,[],[f25])).
% 2.01/0.62  fof(f25,negated_conjecture,(
% 2.01/0.62    ~! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.01/0.62    inference(negated_conjecture,[],[f24])).
% 2.01/0.62  fof(f24,conjecture,(
% 2.01/0.62    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.01/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 2.01/0.62  fof(f84,plain,(
% 2.01/0.62    spl4_3 | spl4_2),
% 2.01/0.62    inference(avatar_split_clause,[],[f44,f76,f81])).
% 2.01/0.62  fof(f44,plain,(
% 2.01/0.62    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK1)),
% 2.01/0.62    inference(cnf_transformation,[],[f36])).
% 2.01/0.62  fof(f79,plain,(
% 2.01/0.62    spl4_1 | spl4_2),
% 2.01/0.62    inference(avatar_split_clause,[],[f45,f76,f72])).
% 2.01/0.62  fof(f45,plain,(
% 2.01/0.62    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK2)),
% 2.01/0.62    inference(cnf_transformation,[],[f36])).
% 2.01/0.62  % SZS output end Proof for theBenchmark
% 2.01/0.62  % (8229)------------------------------
% 2.01/0.62  % (8229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.62  % (8229)Termination reason: Refutation
% 2.01/0.62  
% 2.01/0.62  % (8229)Memory used [KB]: 7675
% 2.01/0.62  % (8229)Time elapsed: 0.209 s
% 2.01/0.62  % (8229)------------------------------
% 2.01/0.62  % (8229)------------------------------
% 2.01/0.62  % (8212)Success in time 0.256 s
%------------------------------------------------------------------------------
