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
% DateTime   : Thu Dec  3 12:32:39 EST 2020

% Result     : Theorem 1.55s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 308 expanded)
%              Number of leaves         :   19 (  92 expanded)
%              Depth                    :   25
%              Number of atoms          :  157 ( 637 expanded)
%              Number of equality atoms :   44 ( 122 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7790,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f4231,f7789])).

fof(f7789,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f7788])).

fof(f7788,plain,
    ( $false
    | spl5_1 ),
    inference(trivial_inequality_removal,[],[f7787])).

fof(f7787,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl5_1 ),
    inference(superposition,[],[f7732,f727])).

fof(f727,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,sK0) ),
    inference(forward_demodulation,[],[f726,f78])).

fof(f78,plain,(
    sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f41,f49])).

fof(f49,plain,(
    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f32,f38])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f32,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f726,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) ),
    inference(resolution,[],[f51,f49])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f44,f38])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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

fof(f7732,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,sK0)
    | spl5_1 ),
    inference(backward_demodulation,[],[f4232,f7666])).

fof(f7666,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f2803,f78])).

fof(f2803,plain,(
    ! [X13] : k3_xboole_0(sK0,X13) = k3_xboole_0(sK0,k5_xboole_0(X13,k3_xboole_0(X13,sK2))) ),
    inference(forward_demodulation,[],[f2692,f34])).

fof(f34,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f2692,plain,(
    ! [X13] : k3_xboole_0(sK0,k5_xboole_0(X13,k3_xboole_0(X13,sK2))) = k5_xboole_0(k3_xboole_0(sK0,X13),k1_xboole_0) ),
    inference(superposition,[],[f2033,f1836])).

fof(f1836,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(X0,sK2)) ),
    inference(superposition,[],[f1662,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1662,plain,(
    ! [X42] : k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK2,X42)) ),
    inference(backward_demodulation,[],[f1408,f1652])).

fof(f1652,plain,(
    ! [X19] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X19) ),
    inference(forward_demodulation,[],[f1651,f1493])).

fof(f1493,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(sK2,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(resolution,[],[f1492,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f40,f35])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f1492,plain,(
    ! [X10] : r1_xboole_0(sK2,k3_xboole_0(k1_xboole_0,X10)) ),
    inference(resolution,[],[f1478,f339])).

fof(f339,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(resolution,[],[f331,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f331,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f209,f50])).

fof(f50,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f36,f38])).

fof(f36,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f209,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0)
      | r1_xboole_0(sK0,X0) ) ),
    inference(resolution,[],[f47,f49])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f1478,plain,(
    ! [X21,X22] :
      ( ~ r1_xboole_0(X22,sK0)
      | r1_xboole_0(X22,k3_xboole_0(k1_xboole_0,X21)) ) ),
    inference(superposition,[],[f48,f1408])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).

fof(f1651,plain,(
    ! [X19,X18] : k3_xboole_0(k1_xboole_0,X19) = k3_xboole_0(sK2,k3_xboole_0(k1_xboole_0,k3_xboole_0(X18,X19))) ),
    inference(forward_demodulation,[],[f1634,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f1634,plain,(
    ! [X19,X18] : k3_xboole_0(k1_xboole_0,X19) = k3_xboole_0(sK2,k3_xboole_0(k3_xboole_0(k1_xboole_0,X18),X19)) ),
    inference(superposition,[],[f46,f1493])).

fof(f1408,plain,(
    ! [X42] : k3_xboole_0(sK0,k3_xboole_0(sK2,X42)) = k3_xboole_0(k1_xboole_0,X42) ),
    inference(superposition,[],[f46,f338])).

fof(f338,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f331,f75])).

fof(f2033,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) ),
    inference(forward_demodulation,[],[f53,f46])).

fof(f53,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f45,f38,f38])).

fof(f45,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f4232,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | spl5_1 ),
    inference(resolution,[],[f57,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f43,f38])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f57,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl5_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f4231,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f4230])).

fof(f4230,plain,
    ( $false
    | spl5_2 ),
    inference(resolution,[],[f61,f331])).

fof(f61,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl5_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f62,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f33,f59,f55])).

fof(f33,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:34:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (17239)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.46  % (17244)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.46  % (17245)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.46  % (17234)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (17231)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (17236)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (17235)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (17241)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (17243)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (17233)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (17248)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.50  % (17246)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.50  % (17247)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  % (17230)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (17229)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.51  % (17240)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.51  % (17237)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.51  % (17238)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 1.55/0.60  % (17231)Refutation found. Thanks to Tanya!
% 1.55/0.60  % SZS status Theorem for theBenchmark
% 1.55/0.60  % SZS output start Proof for theBenchmark
% 1.55/0.60  fof(f7790,plain,(
% 1.55/0.60    $false),
% 1.55/0.60    inference(avatar_sat_refutation,[],[f62,f4231,f7789])).
% 1.55/0.60  fof(f7789,plain,(
% 1.55/0.60    spl5_1),
% 1.55/0.60    inference(avatar_contradiction_clause,[],[f7788])).
% 1.55/0.60  fof(f7788,plain,(
% 1.55/0.60    $false | spl5_1),
% 1.55/0.60    inference(trivial_inequality_removal,[],[f7787])).
% 1.55/0.60  fof(f7787,plain,(
% 1.55/0.60    k1_xboole_0 != k1_xboole_0 | spl5_1),
% 1.55/0.60    inference(superposition,[],[f7732,f727])).
% 1.55/0.60  fof(f727,plain,(
% 1.55/0.60    k1_xboole_0 = k5_xboole_0(sK0,sK0)),
% 1.55/0.60    inference(forward_demodulation,[],[f726,f78])).
% 1.55/0.60  fof(f78,plain,(
% 1.55/0.60    sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 1.55/0.60    inference(resolution,[],[f41,f49])).
% 1.55/0.60  fof(f49,plain,(
% 1.55/0.60    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 1.55/0.60    inference(definition_unfolding,[],[f32,f38])).
% 1.55/0.60  fof(f38,plain,(
% 1.55/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.55/0.60    inference(cnf_transformation,[],[f6])).
% 1.55/0.60  fof(f6,axiom,(
% 1.55/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.55/0.60  fof(f32,plain,(
% 1.55/0.60    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 1.55/0.60    inference(cnf_transformation,[],[f26])).
% 1.55/0.60  fof(f26,plain,(
% 1.55/0.60    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 1.55/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f25])).
% 1.55/0.60  fof(f25,plain,(
% 1.55/0.60    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 1.55/0.60    introduced(choice_axiom,[])).
% 1.55/0.60  fof(f17,plain,(
% 1.55/0.60    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.55/0.60    inference(ennf_transformation,[],[f15])).
% 1.55/0.60  fof(f15,negated_conjecture,(
% 1.55/0.60    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.55/0.60    inference(negated_conjecture,[],[f14])).
% 1.55/0.60  fof(f14,conjecture,(
% 1.55/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.55/0.60  fof(f41,plain,(
% 1.55/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.55/0.60    inference(cnf_transformation,[],[f20])).
% 1.55/0.60  fof(f20,plain,(
% 1.55/0.60    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.55/0.60    inference(ennf_transformation,[],[f8])).
% 1.55/0.60  fof(f8,axiom,(
% 1.55/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.55/0.60  fof(f726,plain,(
% 1.55/0.60    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))),
% 1.55/0.60    inference(resolution,[],[f51,f49])).
% 1.55/0.60  fof(f51,plain,(
% 1.55/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.55/0.60    inference(definition_unfolding,[],[f44,f38])).
% 1.55/0.60  fof(f44,plain,(
% 1.55/0.60    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f31])).
% 1.55/0.60  fof(f31,plain,(
% 1.55/0.60    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 1.55/0.60    inference(nnf_transformation,[],[f5])).
% 1.55/0.60  fof(f5,axiom,(
% 1.55/0.60    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.55/0.60  fof(f7732,plain,(
% 1.55/0.60    k1_xboole_0 != k5_xboole_0(sK0,sK0) | spl5_1),
% 1.55/0.60    inference(backward_demodulation,[],[f4232,f7666])).
% 1.55/0.60  fof(f7666,plain,(
% 1.55/0.60    sK0 = k3_xboole_0(sK0,sK1)),
% 1.55/0.60    inference(superposition,[],[f2803,f78])).
% 1.55/0.60  fof(f2803,plain,(
% 1.55/0.60    ( ! [X13] : (k3_xboole_0(sK0,X13) = k3_xboole_0(sK0,k5_xboole_0(X13,k3_xboole_0(X13,sK2)))) )),
% 1.55/0.60    inference(forward_demodulation,[],[f2692,f34])).
% 1.55/0.60  fof(f34,plain,(
% 1.55/0.60    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.55/0.60    inference(cnf_transformation,[],[f10])).
% 1.55/0.60  fof(f10,axiom,(
% 1.55/0.60    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.55/0.60  fof(f2692,plain,(
% 1.55/0.60    ( ! [X13] : (k3_xboole_0(sK0,k5_xboole_0(X13,k3_xboole_0(X13,sK2))) = k5_xboole_0(k3_xboole_0(sK0,X13),k1_xboole_0)) )),
% 1.55/0.60    inference(superposition,[],[f2033,f1836])).
% 1.55/0.60  fof(f1836,plain,(
% 1.55/0.60    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(X0,sK2))) )),
% 1.55/0.60    inference(superposition,[],[f1662,f37])).
% 1.55/0.60  fof(f37,plain,(
% 1.55/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f1])).
% 1.55/0.60  fof(f1,axiom,(
% 1.55/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.55/0.60  fof(f1662,plain,(
% 1.55/0.60    ( ! [X42] : (k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK2,X42))) )),
% 1.55/0.60    inference(backward_demodulation,[],[f1408,f1652])).
% 1.55/0.60  fof(f1652,plain,(
% 1.55/0.60    ( ! [X19] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X19)) )),
% 1.55/0.60    inference(forward_demodulation,[],[f1651,f1493])).
% 1.55/0.60  fof(f1493,plain,(
% 1.55/0.60    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(sK2,k3_xboole_0(k1_xboole_0,X0))) )),
% 1.55/0.60    inference(resolution,[],[f1492,f75])).
% 1.55/0.60  fof(f75,plain,(
% 1.55/0.60    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.55/0.60    inference(resolution,[],[f40,f35])).
% 1.55/0.60  fof(f35,plain,(
% 1.55/0.60    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.55/0.60    inference(cnf_transformation,[],[f28])).
% 1.55/0.60  fof(f28,plain,(
% 1.55/0.60    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 1.55/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f27])).
% 1.55/0.60  fof(f27,plain,(
% 1.55/0.60    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.55/0.60    introduced(choice_axiom,[])).
% 1.55/0.60  fof(f18,plain,(
% 1.55/0.60    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.55/0.60    inference(ennf_transformation,[],[f4])).
% 1.55/0.60  fof(f4,axiom,(
% 1.55/0.60    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.55/0.60  fof(f40,plain,(
% 1.55/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f30])).
% 1.55/0.60  fof(f30,plain,(
% 1.55/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.55/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f29])).
% 1.55/0.60  fof(f29,plain,(
% 1.55/0.60    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 1.55/0.60    introduced(choice_axiom,[])).
% 1.55/0.60  fof(f19,plain,(
% 1.55/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.55/0.60    inference(ennf_transformation,[],[f16])).
% 1.55/0.60  fof(f16,plain,(
% 1.55/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.55/0.60    inference(rectify,[],[f3])).
% 1.55/0.60  fof(f3,axiom,(
% 1.55/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.55/0.60  fof(f1492,plain,(
% 1.55/0.60    ( ! [X10] : (r1_xboole_0(sK2,k3_xboole_0(k1_xboole_0,X10))) )),
% 1.55/0.60    inference(resolution,[],[f1478,f339])).
% 1.55/0.60  fof(f339,plain,(
% 1.55/0.60    r1_xboole_0(sK2,sK0)),
% 1.55/0.60    inference(resolution,[],[f331,f42])).
% 1.55/0.60  fof(f42,plain,(
% 1.55/0.60    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f21])).
% 1.55/0.60  fof(f21,plain,(
% 1.55/0.60    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.55/0.60    inference(ennf_transformation,[],[f2])).
% 1.55/0.60  fof(f2,axiom,(
% 1.55/0.60    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.55/0.60  fof(f331,plain,(
% 1.55/0.60    r1_xboole_0(sK0,sK2)),
% 1.55/0.60    inference(resolution,[],[f209,f50])).
% 1.55/0.60  fof(f50,plain,(
% 1.55/0.60    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 1.55/0.60    inference(definition_unfolding,[],[f36,f38])).
% 1.55/0.60  fof(f36,plain,(
% 1.55/0.60    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f13])).
% 1.55/0.60  fof(f13,axiom,(
% 1.55/0.60    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.55/0.60  fof(f209,plain,(
% 1.55/0.60    ( ! [X0] : (~r1_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0) | r1_xboole_0(sK0,X0)) )),
% 1.55/0.60    inference(resolution,[],[f47,f49])).
% 1.55/0.60  fof(f47,plain,(
% 1.55/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f23])).
% 1.55/0.60  fof(f23,plain,(
% 1.55/0.60    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 1.55/0.60    inference(flattening,[],[f22])).
% 1.55/0.60  fof(f22,plain,(
% 1.55/0.60    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.55/0.60    inference(ennf_transformation,[],[f11])).
% 1.55/0.60  fof(f11,axiom,(
% 1.55/0.60    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 1.55/0.60  fof(f1478,plain,(
% 1.55/0.60    ( ! [X21,X22] : (~r1_xboole_0(X22,sK0) | r1_xboole_0(X22,k3_xboole_0(k1_xboole_0,X21))) )),
% 1.55/0.60    inference(superposition,[],[f48,f1408])).
% 1.55/0.60  fof(f48,plain,(
% 1.55/0.60    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f24])).
% 1.55/0.60  fof(f24,plain,(
% 1.55/0.60    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 1.55/0.60    inference(ennf_transformation,[],[f12])).
% 1.55/0.60  fof(f12,axiom,(
% 1.55/0.60    ! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).
% 1.55/0.60  fof(f1651,plain,(
% 1.55/0.60    ( ! [X19,X18] : (k3_xboole_0(k1_xboole_0,X19) = k3_xboole_0(sK2,k3_xboole_0(k1_xboole_0,k3_xboole_0(X18,X19)))) )),
% 1.55/0.60    inference(forward_demodulation,[],[f1634,f46])).
% 1.55/0.60  fof(f46,plain,(
% 1.55/0.60    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 1.55/0.60    inference(cnf_transformation,[],[f7])).
% 1.55/0.60  fof(f7,axiom,(
% 1.55/0.60    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 1.55/0.60  fof(f1634,plain,(
% 1.55/0.60    ( ! [X19,X18] : (k3_xboole_0(k1_xboole_0,X19) = k3_xboole_0(sK2,k3_xboole_0(k3_xboole_0(k1_xboole_0,X18),X19))) )),
% 1.55/0.60    inference(superposition,[],[f46,f1493])).
% 1.55/0.60  fof(f1408,plain,(
% 1.55/0.60    ( ! [X42] : (k3_xboole_0(sK0,k3_xboole_0(sK2,X42)) = k3_xboole_0(k1_xboole_0,X42)) )),
% 1.55/0.60    inference(superposition,[],[f46,f338])).
% 1.55/0.60  fof(f338,plain,(
% 1.55/0.60    k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 1.55/0.60    inference(resolution,[],[f331,f75])).
% 1.55/0.60  fof(f2033,plain,(
% 1.55/0.60    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2)))) )),
% 1.55/0.60    inference(forward_demodulation,[],[f53,f46])).
% 1.55/0.60  fof(f53,plain,(
% 1.55/0.60    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 1.55/0.60    inference(definition_unfolding,[],[f45,f38,f38])).
% 1.55/0.60  fof(f45,plain,(
% 1.55/0.60    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f9])).
% 1.55/0.60  fof(f9,axiom,(
% 1.55/0.60    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.55/0.60  fof(f4232,plain,(
% 1.55/0.60    k1_xboole_0 != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | spl5_1),
% 1.55/0.60    inference(resolution,[],[f57,f52])).
% 1.55/0.60  fof(f52,plain,(
% 1.55/0.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.55/0.60    inference(definition_unfolding,[],[f43,f38])).
% 1.55/0.60  fof(f43,plain,(
% 1.55/0.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f31])).
% 1.55/0.60  fof(f57,plain,(
% 1.55/0.60    ~r1_tarski(sK0,sK1) | spl5_1),
% 1.55/0.60    inference(avatar_component_clause,[],[f55])).
% 1.55/0.60  fof(f55,plain,(
% 1.55/0.60    spl5_1 <=> r1_tarski(sK0,sK1)),
% 1.55/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.55/0.60  fof(f4231,plain,(
% 1.55/0.60    spl5_2),
% 1.55/0.60    inference(avatar_contradiction_clause,[],[f4230])).
% 1.55/0.60  fof(f4230,plain,(
% 1.55/0.60    $false | spl5_2),
% 1.55/0.60    inference(resolution,[],[f61,f331])).
% 1.55/0.60  fof(f61,plain,(
% 1.55/0.60    ~r1_xboole_0(sK0,sK2) | spl5_2),
% 1.55/0.60    inference(avatar_component_clause,[],[f59])).
% 1.55/0.60  fof(f59,plain,(
% 1.55/0.60    spl5_2 <=> r1_xboole_0(sK0,sK2)),
% 1.55/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.55/0.60  fof(f62,plain,(
% 1.55/0.60    ~spl5_1 | ~spl5_2),
% 1.55/0.60    inference(avatar_split_clause,[],[f33,f59,f55])).
% 1.55/0.60  fof(f33,plain,(
% 1.55/0.60    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 1.55/0.60    inference(cnf_transformation,[],[f26])).
% 1.55/0.60  % SZS output end Proof for theBenchmark
% 1.55/0.60  % (17231)------------------------------
% 1.55/0.60  % (17231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.60  % (17231)Termination reason: Refutation
% 1.55/0.60  
% 1.55/0.60  % (17231)Memory used [KB]: 8315
% 1.55/0.60  % (17231)Time elapsed: 0.172 s
% 1.55/0.60  % (17231)------------------------------
% 1.55/0.60  % (17231)------------------------------
% 1.55/0.60  % (17225)Success in time 0.242 s
%------------------------------------------------------------------------------
