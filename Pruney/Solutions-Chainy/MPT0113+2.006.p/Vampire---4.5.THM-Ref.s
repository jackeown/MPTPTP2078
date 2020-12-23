%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:33 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 147 expanded)
%              Number of leaves         :   19 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :  143 ( 235 expanded)
%              Number of equality atoms :   31 (  86 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f857,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f58,f80,f220,f764,f773,f856])).

fof(f856,plain,
    ( spl3_3
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f848,f217,f55])).

fof(f55,plain,
    ( spl3_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f217,plain,
    ( spl3_10
  <=> k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f848,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_10 ),
    inference(resolution,[],[f577,f40])).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f27,f30])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f577,plain,
    ( ! [X3] :
        ( ~ r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X3)
        | r1_tarski(sK0,X3) )
    | ~ spl3_10 ),
    inference(superposition,[],[f91,f219])).

fof(f219,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f217])).

fof(f91,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(k2_xboole_0(X3,X2),X4)
      | r1_tarski(X2,X4) ) ),
    inference(superposition,[],[f38,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f773,plain,
    ( spl3_2
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f772,f761,f51])).

fof(f51,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f761,plain,
    ( spl3_12
  <=> r1_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f772,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_12 ),
    inference(resolution,[],[f763,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f763,plain,
    ( r1_xboole_0(sK2,sK0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f761])).

fof(f764,plain,
    ( spl3_12
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f754,f217,f761])).

fof(f754,plain,
    ( r1_xboole_0(sK2,sK0)
    | ~ spl3_10 ),
    inference(resolution,[],[f575,f241])).

fof(f241,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(superposition,[],[f102,f146])).

fof(f146,plain,(
    ! [X6] : k5_xboole_0(X6,k3_xboole_0(X6,k1_xboole_0)) = X6 ),
    inference(forward_demodulation,[],[f140,f66])).

fof(f66,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f28,f24])).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f140,plain,(
    ! [X6] : k5_xboole_0(X6,k3_xboole_0(X6,k1_xboole_0)) = k2_xboole_0(k1_xboole_0,X6) ),
    inference(superposition,[],[f42,f66])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f31,f30])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f102,plain,(
    ! [X2,X3,X1] : r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X3,k3_xboole_0(X3,X1))) ),
    inference(resolution,[],[f43,f40])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ) ),
    inference(definition_unfolding,[],[f37,f30])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f575,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
        | r1_xboole_0(X1,sK0) )
    | ~ spl3_10 ),
    inference(superposition,[],[f35,f219])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f220,plain,
    ( spl3_10
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f215,f77,f217])).

fof(f77,plain,
    ( spl3_5
  <=> sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f215,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK0)
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f214,f24])).

fof(f214,plain,
    ( k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK0) = k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k1_xboole_0)
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f210,f181])).

fof(f181,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f122,f161])).

fof(f161,plain,(
    ! [X3] : k3_xboole_0(X3,X3) = X3 ),
    inference(resolution,[],[f154,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
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

fof(f154,plain,(
    ! [X3] : r1_tarski(X3,X3) ),
    inference(superposition,[],[f40,f146])).

fof(f122,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(resolution,[],[f41,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f29,f30,f30])).

fof(f29,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_xboole_1)).

fof(f210,plain,
    ( k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK0) = k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK0))
    | ~ spl3_5 ),
    inference(superposition,[],[f42,f79])).

fof(f79,plain,
    ( sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f77])).

fof(f80,plain,
    ( spl3_5
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f74,f46,f77])).

fof(f46,plain,
    ( spl3_1
  <=> r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f74,plain,
    ( sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl3_1 ),
    inference(resolution,[],[f32,f48])).

fof(f48,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f58,plain,
    ( ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f22,f55,f51])).

fof(f22,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f49,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f39,f46])).

fof(f39,plain,(
    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f23,f30])).

fof(f23,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:27:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (5634)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.49  % (5654)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.51  % (5636)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (5651)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.52  % (5640)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (5644)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (5656)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (5659)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (5637)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (5648)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (5638)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (5657)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (5658)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.36/0.54  % (5660)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.36/0.54  % (5656)Refutation not found, incomplete strategy% (5656)------------------------------
% 1.36/0.54  % (5656)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (5649)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.36/0.54  % (5656)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (5656)Memory used [KB]: 10618
% 1.36/0.54  % (5656)Time elapsed: 0.129 s
% 1.36/0.54  % (5656)------------------------------
% 1.36/0.54  % (5656)------------------------------
% 1.36/0.54  % (5650)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.36/0.54  % (5652)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.36/0.54  % (5641)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.36/0.55  % (5635)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.36/0.55  % (5662)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.36/0.55  % (5645)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.49/0.55  % (5646)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.49/0.55  % (5643)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.49/0.55  % (5642)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.49/0.55  % (5639)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.49/0.55  % (5647)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.49/0.56  % (5663)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.49/0.56  % (5661)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.49/0.56  % (5655)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.49/0.56  % (5653)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.49/0.58  % (5650)Refutation found. Thanks to Tanya!
% 1.49/0.58  % SZS status Theorem for theBenchmark
% 1.49/0.58  % SZS output start Proof for theBenchmark
% 1.49/0.58  fof(f857,plain,(
% 1.49/0.58    $false),
% 1.49/0.58    inference(avatar_sat_refutation,[],[f49,f58,f80,f220,f764,f773,f856])).
% 1.49/0.58  fof(f856,plain,(
% 1.49/0.58    spl3_3 | ~spl3_10),
% 1.49/0.58    inference(avatar_split_clause,[],[f848,f217,f55])).
% 1.49/0.58  fof(f55,plain,(
% 1.49/0.58    spl3_3 <=> r1_tarski(sK0,sK1)),
% 1.49/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.49/0.58  fof(f217,plain,(
% 1.49/0.58    spl3_10 <=> k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK0)),
% 1.49/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.49/0.58  fof(f848,plain,(
% 1.49/0.58    r1_tarski(sK0,sK1) | ~spl3_10),
% 1.49/0.58    inference(resolution,[],[f577,f40])).
% 1.49/0.58  fof(f40,plain,(
% 1.49/0.58    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 1.49/0.58    inference(definition_unfolding,[],[f27,f30])).
% 1.49/0.58  fof(f30,plain,(
% 1.49/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.49/0.58    inference(cnf_transformation,[],[f3])).
% 1.49/0.58  fof(f3,axiom,(
% 1.49/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.49/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.49/0.58  fof(f27,plain,(
% 1.49/0.58    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.49/0.58    inference(cnf_transformation,[],[f7])).
% 1.49/0.58  fof(f7,axiom,(
% 1.49/0.58    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.49/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.49/0.58  fof(f577,plain,(
% 1.49/0.58    ( ! [X3] : (~r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X3) | r1_tarski(sK0,X3)) ) | ~spl3_10),
% 1.49/0.58    inference(superposition,[],[f91,f219])).
% 1.49/0.58  fof(f219,plain,(
% 1.49/0.58    k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK0) | ~spl3_10),
% 1.49/0.58    inference(avatar_component_clause,[],[f217])).
% 1.49/0.58  fof(f91,plain,(
% 1.49/0.58    ( ! [X4,X2,X3] : (~r1_tarski(k2_xboole_0(X3,X2),X4) | r1_tarski(X2,X4)) )),
% 1.49/0.58    inference(superposition,[],[f38,f28])).
% 1.49/0.58  fof(f28,plain,(
% 1.49/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.49/0.58    inference(cnf_transformation,[],[f1])).
% 1.49/0.58  fof(f1,axiom,(
% 1.49/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.49/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.49/0.58  fof(f38,plain,(
% 1.49/0.58    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.49/0.58    inference(cnf_transformation,[],[f21])).
% 1.49/0.58  fof(f21,plain,(
% 1.49/0.58    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.49/0.58    inference(ennf_transformation,[],[f4])).
% 1.49/0.58  fof(f4,axiom,(
% 1.49/0.58    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.49/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.49/0.58  fof(f773,plain,(
% 1.49/0.58    spl3_2 | ~spl3_12),
% 1.49/0.58    inference(avatar_split_clause,[],[f772,f761,f51])).
% 1.49/0.58  fof(f51,plain,(
% 1.49/0.58    spl3_2 <=> r1_xboole_0(sK0,sK2)),
% 1.49/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.49/0.58  fof(f761,plain,(
% 1.49/0.58    spl3_12 <=> r1_xboole_0(sK2,sK0)),
% 1.49/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.49/0.58  fof(f772,plain,(
% 1.49/0.58    r1_xboole_0(sK0,sK2) | ~spl3_12),
% 1.49/0.58    inference(resolution,[],[f763,f33])).
% 1.49/0.58  fof(f33,plain,(
% 1.49/0.58    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.49/0.58    inference(cnf_transformation,[],[f18])).
% 1.49/0.58  fof(f18,plain,(
% 1.49/0.58    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.49/0.58    inference(ennf_transformation,[],[f2])).
% 1.49/0.58  fof(f2,axiom,(
% 1.49/0.58    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.49/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.49/0.58  fof(f763,plain,(
% 1.49/0.58    r1_xboole_0(sK2,sK0) | ~spl3_12),
% 1.49/0.58    inference(avatar_component_clause,[],[f761])).
% 1.49/0.58  fof(f764,plain,(
% 1.49/0.58    spl3_12 | ~spl3_10),
% 1.49/0.58    inference(avatar_split_clause,[],[f754,f217,f761])).
% 1.49/0.58  fof(f754,plain,(
% 1.49/0.58    r1_xboole_0(sK2,sK0) | ~spl3_10),
% 1.49/0.58    inference(resolution,[],[f575,f241])).
% 1.49/0.58  fof(f241,plain,(
% 1.49/0.58    ( ! [X0,X1] : (r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.49/0.58    inference(superposition,[],[f102,f146])).
% 1.49/0.58  fof(f146,plain,(
% 1.49/0.58    ( ! [X6] : (k5_xboole_0(X6,k3_xboole_0(X6,k1_xboole_0)) = X6) )),
% 1.49/0.58    inference(forward_demodulation,[],[f140,f66])).
% 1.49/0.58  fof(f66,plain,(
% 1.49/0.58    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.49/0.58    inference(superposition,[],[f28,f24])).
% 1.49/0.58  fof(f24,plain,(
% 1.49/0.58    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.49/0.58    inference(cnf_transformation,[],[f5])).
% 1.49/0.58  fof(f5,axiom,(
% 1.49/0.58    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.49/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.49/0.58  fof(f140,plain,(
% 1.49/0.58    ( ! [X6] : (k5_xboole_0(X6,k3_xboole_0(X6,k1_xboole_0)) = k2_xboole_0(k1_xboole_0,X6)) )),
% 1.49/0.58    inference(superposition,[],[f42,f66])).
% 1.49/0.58  fof(f42,plain,(
% 1.49/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.49/0.58    inference(definition_unfolding,[],[f31,f30])).
% 1.49/0.58  fof(f31,plain,(
% 1.49/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.49/0.58    inference(cnf_transformation,[],[f8])).
% 1.49/0.58  fof(f8,axiom,(
% 1.49/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.49/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.49/0.58  fof(f102,plain,(
% 1.49/0.58    ( ! [X2,X3,X1] : (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X3,k3_xboole_0(X3,X1)))) )),
% 1.49/0.58    inference(resolution,[],[f43,f40])).
% 1.49/0.58  fof(f43,plain,(
% 1.49/0.58    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) )),
% 1.49/0.58    inference(definition_unfolding,[],[f37,f30])).
% 1.49/0.58  fof(f37,plain,(
% 1.49/0.58    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X2,X1))) )),
% 1.49/0.58    inference(cnf_transformation,[],[f20])).
% 1.49/0.58  fof(f20,plain,(
% 1.49/0.58    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.49/0.58    inference(ennf_transformation,[],[f12])).
% 1.49/0.58  fof(f12,axiom,(
% 1.49/0.58    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 1.49/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 1.49/0.58  fof(f575,plain,(
% 1.49/0.58    ( ! [X1] : (~r1_xboole_0(X1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | r1_xboole_0(X1,sK0)) ) | ~spl3_10),
% 1.49/0.58    inference(superposition,[],[f35,f219])).
% 1.49/0.58  fof(f35,plain,(
% 1.49/0.58    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 1.49/0.58    inference(cnf_transformation,[],[f19])).
% 1.49/0.58  fof(f19,plain,(
% 1.49/0.58    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.49/0.58    inference(ennf_transformation,[],[f10])).
% 1.49/0.58  fof(f10,axiom,(
% 1.49/0.58    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.49/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.49/0.58  fof(f220,plain,(
% 1.49/0.58    spl3_10 | ~spl3_5),
% 1.49/0.58    inference(avatar_split_clause,[],[f215,f77,f217])).
% 1.49/0.58  fof(f77,plain,(
% 1.49/0.58    spl3_5 <=> sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 1.49/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.49/0.58  fof(f215,plain,(
% 1.49/0.58    k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK0) | ~spl3_5),
% 1.49/0.58    inference(forward_demodulation,[],[f214,f24])).
% 1.49/0.58  fof(f214,plain,(
% 1.49/0.58    k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK0) = k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k1_xboole_0) | ~spl3_5),
% 1.49/0.58    inference(forward_demodulation,[],[f210,f181])).
% 1.49/0.58  fof(f181,plain,(
% 1.49/0.58    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.49/0.58    inference(backward_demodulation,[],[f122,f161])).
% 1.49/0.58  fof(f161,plain,(
% 1.49/0.58    ( ! [X3] : (k3_xboole_0(X3,X3) = X3) )),
% 1.49/0.58    inference(resolution,[],[f154,f32])).
% 1.49/0.58  fof(f32,plain,(
% 1.49/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.49/0.58    inference(cnf_transformation,[],[f17])).
% 1.49/0.58  fof(f17,plain,(
% 1.49/0.58    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.49/0.58    inference(ennf_transformation,[],[f6])).
% 1.49/0.58  fof(f6,axiom,(
% 1.49/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.49/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.49/0.58  fof(f154,plain,(
% 1.49/0.58    ( ! [X3] : (r1_tarski(X3,X3)) )),
% 1.49/0.58    inference(superposition,[],[f40,f146])).
% 1.49/0.58  fof(f122,plain,(
% 1.49/0.58    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 1.49/0.58    inference(resolution,[],[f41,f25])).
% 1.49/0.58  fof(f25,plain,(
% 1.49/0.58    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 1.49/0.58    inference(cnf_transformation,[],[f16])).
% 1.49/0.58  fof(f16,plain,(
% 1.49/0.58    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 1.49/0.58    inference(ennf_transformation,[],[f9])).
% 1.49/0.58  fof(f9,axiom,(
% 1.49/0.58    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.49/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 1.49/0.58  fof(f41,plain,(
% 1.49/0.58    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.49/0.58    inference(definition_unfolding,[],[f29,f30,f30])).
% 1.49/0.58  fof(f29,plain,(
% 1.49/0.58    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 1.49/0.58    inference(cnf_transformation,[],[f11])).
% 1.49/0.58  fof(f11,axiom,(
% 1.49/0.58    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 1.49/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_xboole_1)).
% 1.49/0.58  fof(f210,plain,(
% 1.49/0.58    k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK0) = k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK0)) | ~spl3_5),
% 1.49/0.58    inference(superposition,[],[f42,f79])).
% 1.49/0.58  fof(f79,plain,(
% 1.49/0.58    sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl3_5),
% 1.49/0.58    inference(avatar_component_clause,[],[f77])).
% 1.49/0.58  fof(f80,plain,(
% 1.49/0.58    spl3_5 | ~spl3_1),
% 1.49/0.58    inference(avatar_split_clause,[],[f74,f46,f77])).
% 1.49/0.58  fof(f46,plain,(
% 1.49/0.58    spl3_1 <=> r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 1.49/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.49/0.58  fof(f74,plain,(
% 1.49/0.58    sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl3_1),
% 1.49/0.58    inference(resolution,[],[f32,f48])).
% 1.49/0.58  fof(f48,plain,(
% 1.49/0.58    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl3_1),
% 1.49/0.58    inference(avatar_component_clause,[],[f46])).
% 1.49/0.58  fof(f58,plain,(
% 1.49/0.58    ~spl3_2 | ~spl3_3),
% 1.49/0.58    inference(avatar_split_clause,[],[f22,f55,f51])).
% 1.49/0.58  fof(f22,plain,(
% 1.49/0.58    ~r1_tarski(sK0,sK1) | ~r1_xboole_0(sK0,sK2)),
% 1.49/0.58    inference(cnf_transformation,[],[f15])).
% 1.49/0.58  fof(f15,plain,(
% 1.49/0.58    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.49/0.58    inference(ennf_transformation,[],[f14])).
% 1.49/0.58  fof(f14,negated_conjecture,(
% 1.49/0.58    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.49/0.58    inference(negated_conjecture,[],[f13])).
% 1.49/0.58  fof(f13,conjecture,(
% 1.49/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.49/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.49/0.58  fof(f49,plain,(
% 1.49/0.58    spl3_1),
% 1.49/0.58    inference(avatar_split_clause,[],[f39,f46])).
% 1.49/0.58  fof(f39,plain,(
% 1.49/0.58    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 1.49/0.58    inference(definition_unfolding,[],[f23,f30])).
% 1.49/0.58  fof(f23,plain,(
% 1.49/0.58    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 1.49/0.58    inference(cnf_transformation,[],[f15])).
% 1.49/0.58  % SZS output end Proof for theBenchmark
% 1.49/0.58  % (5650)------------------------------
% 1.49/0.58  % (5650)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.58  % (5650)Termination reason: Refutation
% 1.49/0.58  
% 1.49/0.58  % (5650)Memory used [KB]: 11129
% 1.49/0.58  % (5650)Time elapsed: 0.183 s
% 1.49/0.58  % (5650)------------------------------
% 1.49/0.58  % (5650)------------------------------
% 1.49/0.58  % (5633)Success in time 0.221 s
%------------------------------------------------------------------------------
