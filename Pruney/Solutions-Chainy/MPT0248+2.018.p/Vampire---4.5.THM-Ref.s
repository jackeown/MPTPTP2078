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
% DateTime   : Thu Dec  3 12:37:51 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 331 expanded)
%              Number of leaves         :   19 ( 116 expanded)
%              Depth                    :   16
%              Number of atoms          :  176 ( 639 expanded)
%              Number of equality atoms :  120 ( 562 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f127,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f73,f74,f94,f95,f126])).

fof(f126,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(trivial_inequality_removal,[],[f117])).

fof(f117,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(superposition,[],[f97,f113])).

fof(f113,plain,
    ( k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(superposition,[],[f110,f26])).

fof(f26,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f110,plain,
    ( k1_xboole_0 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f109,f26])).

fof(f109,plain,
    ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f108,f25])).

fof(f25,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f108,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f106,f76])).

fof(f76,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f29,f25])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f106,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(superposition,[],[f75,f99])).

fof(f99,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f98,f62])).

fof(f62,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f98,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2))
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f47,f67])).

fof(f67,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl3_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f47,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f21,f43,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f31,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f32,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f43,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f27,f41])).

fof(f27,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f21,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( ( k1_xboole_0 != sK2
        | sK1 != k1_tarski(sK0) )
      & ( sK2 != k1_tarski(sK0)
        | k1_xboole_0 != sK1 )
      & ( sK2 != k1_tarski(sK0)
        | sK1 != k1_tarski(sK0) )
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f75,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(X1,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) ),
    inference(forward_demodulation,[],[f50,f29])).

fof(f50,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) ),
    inference(definition_unfolding,[],[f34,f33,f33,f42])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f97,plain,
    ( k1_xboole_0 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | spl3_1
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f59,f67])).

fof(f59,plain,
    ( sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl3_1
  <=> sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f95,plain,
    ( spl3_4
    | spl3_2 ),
    inference(avatar_split_clause,[],[f93,f61,f70])).

fof(f70,plain,
    ( spl3_4
  <=> sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f93,plain,
    ( k1_xboole_0 = sK2
    | sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f53,f87])).

fof(f87,plain,(
    r1_tarski(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f85,f47])).

fof(f85,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) ),
    inference(superposition,[],[f48,f49])).

fof(f49,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f30,f42,f42])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f28,f42])).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k3_enumset1(X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f35,f43,f43])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f94,plain,
    ( spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f92,f66,f57])).

fof(f92,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f53,f84])).

fof(f84,plain,(
    r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f48,f47])).

fof(f74,plain,
    ( ~ spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f46,f70,f57])).

fof(f46,plain,
    ( sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f22,f43,f43])).

fof(f22,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f73,plain,
    ( ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f45,f70,f66])).

fof(f45,plain,
    ( sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f23,f43])).

fof(f23,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f18])).

fof(f64,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f44,f61,f57])).

fof(f44,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f24,f43])).

fof(f24,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.32  % Computer   : n020.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 18:54:22 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.18/0.48  % (32733)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.18/0.49  % (32742)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.18/0.50  % (32730)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.18/0.50  % (32742)Refutation found. Thanks to Tanya!
% 0.18/0.50  % SZS status Theorem for theBenchmark
% 0.18/0.50  % (32738)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.18/0.50  % (32750)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.18/0.50  % SZS output start Proof for theBenchmark
% 0.18/0.50  fof(f127,plain,(
% 0.18/0.50    $false),
% 0.18/0.50    inference(avatar_sat_refutation,[],[f64,f73,f74,f94,f95,f126])).
% 0.18/0.50  fof(f126,plain,(
% 0.18/0.50    spl3_1 | ~spl3_2 | ~spl3_3),
% 0.18/0.50    inference(avatar_contradiction_clause,[],[f125])).
% 0.18/0.50  fof(f125,plain,(
% 0.18/0.50    $false | (spl3_1 | ~spl3_2 | ~spl3_3)),
% 0.18/0.50    inference(trivial_inequality_removal,[],[f117])).
% 0.18/0.50  fof(f117,plain,(
% 0.18/0.50    k1_xboole_0 != k1_xboole_0 | (spl3_1 | ~spl3_2 | ~spl3_3)),
% 0.18/0.50    inference(superposition,[],[f97,f113])).
% 0.18/0.50  fof(f113,plain,(
% 0.18/0.50    k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | (~spl3_2 | ~spl3_3)),
% 0.18/0.50    inference(superposition,[],[f110,f26])).
% 0.18/0.50  fof(f26,plain,(
% 0.18/0.50    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.18/0.50    inference(cnf_transformation,[],[f6])).
% 0.18/0.50  fof(f6,axiom,(
% 0.18/0.50    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.18/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.18/0.50  fof(f110,plain,(
% 0.18/0.50    k1_xboole_0 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0) | (~spl3_2 | ~spl3_3)),
% 0.18/0.50    inference(forward_demodulation,[],[f109,f26])).
% 0.18/0.50  fof(f109,plain,(
% 0.18/0.50    k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl3_2 | ~spl3_3)),
% 0.18/0.50    inference(forward_demodulation,[],[f108,f25])).
% 0.18/0.50  fof(f25,plain,(
% 0.18/0.50    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.18/0.50    inference(cnf_transformation,[],[f4])).
% 0.18/0.50  fof(f4,axiom,(
% 0.18/0.50    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.18/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.18/0.50  fof(f108,plain,(
% 0.18/0.50    k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0) | (~spl3_2 | ~spl3_3)),
% 0.18/0.50    inference(forward_demodulation,[],[f106,f76])).
% 0.18/0.50  fof(f76,plain,(
% 0.18/0.50    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.18/0.50    inference(superposition,[],[f29,f25])).
% 0.18/0.50  fof(f29,plain,(
% 0.18/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.18/0.50    inference(cnf_transformation,[],[f2])).
% 0.18/0.50  fof(f2,axiom,(
% 0.18/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.18/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.18/0.50  fof(f106,plain,(
% 0.18/0.50    k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | (~spl3_2 | ~spl3_3)),
% 0.18/0.50    inference(superposition,[],[f75,f99])).
% 0.18/0.50  fof(f99,plain,(
% 0.18/0.50    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) | (~spl3_2 | ~spl3_3)),
% 0.18/0.50    inference(backward_demodulation,[],[f98,f62])).
% 0.18/0.50  fof(f62,plain,(
% 0.18/0.50    k1_xboole_0 = sK2 | ~spl3_2),
% 0.18/0.50    inference(avatar_component_clause,[],[f61])).
% 0.18/0.50  fof(f61,plain,(
% 0.18/0.50    spl3_2 <=> k1_xboole_0 = sK2),
% 0.18/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.18/0.50  fof(f98,plain,(
% 0.18/0.50    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2)) | ~spl3_3),
% 0.18/0.50    inference(backward_demodulation,[],[f47,f67])).
% 0.18/0.50  fof(f67,plain,(
% 0.18/0.50    k1_xboole_0 = sK1 | ~spl3_3),
% 0.18/0.50    inference(avatar_component_clause,[],[f66])).
% 0.18/0.50  fof(f66,plain,(
% 0.18/0.50    spl3_3 <=> k1_xboole_0 = sK1),
% 0.18/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.18/0.51  fof(f47,plain,(
% 0.18/0.51    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),
% 0.18/0.51    inference(definition_unfolding,[],[f21,f43,f42])).
% 0.18/0.51  fof(f42,plain,(
% 0.18/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.18/0.51    inference(definition_unfolding,[],[f31,f41])).
% 0.18/0.51  fof(f41,plain,(
% 0.18/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.18/0.51    inference(definition_unfolding,[],[f32,f40])).
% 0.18/0.51  fof(f40,plain,(
% 0.18/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.18/0.51    inference(definition_unfolding,[],[f38,f39])).
% 0.18/0.51  fof(f39,plain,(
% 0.18/0.51    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f11])).
% 0.18/0.51  fof(f11,axiom,(
% 0.18/0.51    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.18/0.51  fof(f38,plain,(
% 0.18/0.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f10])).
% 0.18/0.51  fof(f10,axiom,(
% 0.18/0.51    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.18/0.51  fof(f32,plain,(
% 0.18/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f9])).
% 0.18/0.51  fof(f9,axiom,(
% 0.18/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.18/0.51  fof(f31,plain,(
% 0.18/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.18/0.51    inference(cnf_transformation,[],[f13])).
% 0.18/0.51  fof(f13,axiom,(
% 0.18/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.18/0.51  fof(f43,plain,(
% 0.18/0.51    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.18/0.51    inference(definition_unfolding,[],[f27,f41])).
% 0.18/0.51  fof(f27,plain,(
% 0.18/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f8])).
% 0.18/0.51  fof(f8,axiom,(
% 0.18/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.18/0.51  fof(f21,plain,(
% 0.18/0.51    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.18/0.51    inference(cnf_transformation,[],[f18])).
% 0.18/0.51  fof(f18,plain,(
% 0.18/0.51    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.18/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f17])).
% 0.18/0.51  fof(f17,plain,(
% 0.18/0.51    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 0.18/0.51    introduced(choice_axiom,[])).
% 0.18/0.51  fof(f16,plain,(
% 0.18/0.51    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.18/0.51    inference(ennf_transformation,[],[f15])).
% 0.18/0.51  fof(f15,negated_conjecture,(
% 0.18/0.51    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.18/0.51    inference(negated_conjecture,[],[f14])).
% 0.18/0.51  fof(f14,conjecture,(
% 0.18/0.51    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 0.18/0.51  fof(f75,plain,(
% 0.18/0.51    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(X1,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))))) )),
% 0.18/0.51    inference(forward_demodulation,[],[f50,f29])).
% 0.18/0.51  fof(f50,plain,(
% 0.18/0.51    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1))) )),
% 0.18/0.51    inference(definition_unfolding,[],[f34,f33,f33,f42])).
% 0.18/0.51  fof(f33,plain,(
% 0.18/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.18/0.51    inference(cnf_transformation,[],[f3])).
% 0.18/0.51  fof(f3,axiom,(
% 0.18/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.18/0.51  fof(f34,plain,(
% 0.18/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f5])).
% 0.18/0.51  fof(f5,axiom,(
% 0.18/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.18/0.51  fof(f97,plain,(
% 0.18/0.51    k1_xboole_0 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | (spl3_1 | ~spl3_3)),
% 0.18/0.51    inference(backward_demodulation,[],[f59,f67])).
% 0.18/0.51  fof(f59,plain,(
% 0.18/0.51    sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | spl3_1),
% 0.18/0.51    inference(avatar_component_clause,[],[f57])).
% 0.18/0.51  fof(f57,plain,(
% 0.18/0.51    spl3_1 <=> sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.18/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.18/0.51  fof(f95,plain,(
% 0.18/0.51    spl3_4 | spl3_2),
% 0.18/0.51    inference(avatar_split_clause,[],[f93,f61,f70])).
% 0.18/0.51  fof(f70,plain,(
% 0.18/0.51    spl3_4 <=> sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.18/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.18/0.51  fof(f93,plain,(
% 0.18/0.51    k1_xboole_0 = sK2 | sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.18/0.51    inference(resolution,[],[f53,f87])).
% 0.18/0.51  fof(f87,plain,(
% 0.18/0.51    r1_tarski(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 0.18/0.51    inference(superposition,[],[f85,f47])).
% 0.18/0.51  fof(f85,plain,(
% 0.18/0.51    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)))) )),
% 0.18/0.51    inference(superposition,[],[f48,f49])).
% 0.18/0.51  fof(f49,plain,(
% 0.18/0.51    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) )),
% 0.18/0.51    inference(definition_unfolding,[],[f30,f42,f42])).
% 0.18/0.51  fof(f30,plain,(
% 0.18/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f1])).
% 0.18/0.51  fof(f1,axiom,(
% 0.18/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.18/0.51  fof(f48,plain,(
% 0.18/0.51    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 0.18/0.51    inference(definition_unfolding,[],[f28,f42])).
% 0.18/0.51  fof(f28,plain,(
% 0.18/0.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.18/0.51    inference(cnf_transformation,[],[f7])).
% 0.18/0.51  fof(f7,axiom,(
% 0.18/0.51    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.18/0.51  fof(f53,plain,(
% 0.18/0.51    ( ! [X0,X1] : (~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1)) | k1_xboole_0 = X0 | k3_enumset1(X1,X1,X1,X1,X1) = X0) )),
% 0.18/0.51    inference(definition_unfolding,[],[f35,f43,f43])).
% 0.18/0.51  fof(f35,plain,(
% 0.18/0.51    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.18/0.51    inference(cnf_transformation,[],[f20])).
% 0.18/0.51  fof(f20,plain,(
% 0.18/0.51    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.18/0.51    inference(flattening,[],[f19])).
% 0.18/0.51  fof(f19,plain,(
% 0.18/0.51    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.18/0.51    inference(nnf_transformation,[],[f12])).
% 0.18/0.51  fof(f12,axiom,(
% 0.18/0.51    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.18/0.51  fof(f94,plain,(
% 0.18/0.51    spl3_1 | spl3_3),
% 0.18/0.51    inference(avatar_split_clause,[],[f92,f66,f57])).
% 0.18/0.51  fof(f92,plain,(
% 0.18/0.51    k1_xboole_0 = sK1 | sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.18/0.51    inference(resolution,[],[f53,f84])).
% 0.18/0.51  fof(f84,plain,(
% 0.18/0.51    r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 0.18/0.51    inference(superposition,[],[f48,f47])).
% 0.18/0.51  fof(f74,plain,(
% 0.18/0.51    ~spl3_1 | ~spl3_4),
% 0.18/0.51    inference(avatar_split_clause,[],[f46,f70,f57])).
% 0.18/0.51  fof(f46,plain,(
% 0.18/0.51    sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.18/0.51    inference(definition_unfolding,[],[f22,f43,f43])).
% 0.18/0.51  fof(f22,plain,(
% 0.18/0.51    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 0.18/0.51    inference(cnf_transformation,[],[f18])).
% 0.18/0.51  fof(f73,plain,(
% 0.18/0.51    ~spl3_3 | ~spl3_4),
% 0.18/0.51    inference(avatar_split_clause,[],[f45,f70,f66])).
% 0.18/0.51  fof(f45,plain,(
% 0.18/0.51    sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK1),
% 0.18/0.51    inference(definition_unfolding,[],[f23,f43])).
% 0.18/0.51  fof(f23,plain,(
% 0.18/0.51    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 0.18/0.51    inference(cnf_transformation,[],[f18])).
% 0.18/0.51  fof(f64,plain,(
% 0.18/0.51    ~spl3_1 | ~spl3_2),
% 0.18/0.51    inference(avatar_split_clause,[],[f44,f61,f57])).
% 0.18/0.51  fof(f44,plain,(
% 0.18/0.51    k1_xboole_0 != sK2 | sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.18/0.51    inference(definition_unfolding,[],[f24,f43])).
% 0.18/0.51  fof(f24,plain,(
% 0.18/0.51    k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)),
% 0.18/0.51    inference(cnf_transformation,[],[f18])).
% 0.18/0.51  % SZS output end Proof for theBenchmark
% 0.18/0.51  % (32742)------------------------------
% 0.18/0.51  % (32742)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.51  % (32742)Termination reason: Refutation
% 0.18/0.51  
% 0.18/0.51  % (32742)Memory used [KB]: 6268
% 0.18/0.51  % (32742)Time elapsed: 0.109 s
% 0.18/0.51  % (32742)------------------------------
% 0.18/0.51  % (32742)------------------------------
% 0.18/0.51  % (32729)Success in time 0.168 s
%------------------------------------------------------------------------------
