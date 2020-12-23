%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 298 expanded)
%              Number of leaves         :   23 ( 117 expanded)
%              Depth                    :   11
%              Number of atoms          :  166 ( 468 expanded)
%              Number of equality atoms :   94 ( 354 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f182,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f64,f69,f74,f81,f99,f103,f147,f150,f152,f160,f181])).

fof(f181,plain,
    ( spl3_9
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f180,f157,f113])).

fof(f113,plain,
    ( spl3_9
  <=> k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f157,plain,
    ( spl3_14
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f180,plain,
    ( k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f173,f75])).

fof(f75,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f42,f20])).

fof(f20,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f42,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f21,f27])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f173,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_14 ),
    inference(backward_demodulation,[],[f159,f90])).

fof(f90,plain,(
    ! [X0] : k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f86,f75])).

fof(f86,plain,(
    ! [X0] : k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f45,f20])).

fof(f45,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f28,f36,f27])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f25,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f26,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f32,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f159,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f157])).

fof(f160,plain,
    ( spl3_14
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f155,f108,f71,f157])).

fof(f71,plain,
    ( spl3_5
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f108,plain,
    ( spl3_8
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f155,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f110,f72])).

fof(f72,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f110,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f108])).

fof(f152,plain,
    ( spl3_5
    | spl3_2
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f151,f96,f57,f71])).

fof(f57,plain,
    ( spl3_2
  <=> sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f96,plain,
    ( spl3_7
  <=> r1_tarski(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f151,plain,
    ( sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 = sK2
    | ~ spl3_7 ),
    inference(resolution,[],[f98,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
      | k3_enumset1(X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f29,f37,f37])).

fof(f37,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f22,f35])).

fof(f22,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f98,plain,
    ( r1_tarski(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f96])).

fof(f150,plain,
    ( spl3_8
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f149,f66,f52,f108])).

fof(f52,plain,
    ( spl3_1
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f66,plain,
    ( spl3_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f149,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2))
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f54,f67])).

fof(f67,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f54,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f147,plain,
    ( ~ spl3_9
    | spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f146,f66,f61,f113])).

fof(f61,plain,
    ( spl3_3
  <=> sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f146,plain,
    ( k1_xboole_0 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | spl3_3
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f63,f67])).

fof(f63,plain,
    ( sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f103,plain,
    ( spl3_4
    | spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f102,f78,f61,f66])).

fof(f78,plain,
    ( spl3_6
  <=> r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f102,plain,
    ( sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 = sK1
    | ~ spl3_6 ),
    inference(resolution,[],[f48,f80])).

fof(f80,plain,
    ( r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f78])).

fof(f99,plain,
    ( spl3_7
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f91,f52,f96])).

fof(f91,plain,
    ( r1_tarski(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl3_1 ),
    inference(superposition,[],[f82,f54])).

fof(f82,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) ),
    inference(superposition,[],[f43,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f24,f36,f36])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f23,f36])).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f81,plain,
    ( spl3_6
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f76,f52,f78])).

fof(f76,plain,
    ( r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl3_1 ),
    inference(superposition,[],[f43,f54])).

fof(f74,plain,
    ( ~ spl3_5
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f41,f61,f71])).

fof(f41,plain,
    ( sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f16,f37])).

fof(f16,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f69,plain,
    ( ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f40,f66,f57])).

fof(f40,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f17,f37])).

fof(f17,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f64,plain,
    ( ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f39,f61,f57])).

fof(f39,plain,
    ( sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f18,f37,f37])).

fof(f18,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f55,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f38,f52])).

fof(f38,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f19,f37,f36])).

fof(f19,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:00:45 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (31722)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (31730)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (31728)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (31727)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (31730)Refutation not found, incomplete strategy% (31730)------------------------------
% 0.22/0.52  % (31730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (31722)Refutation not found, incomplete strategy% (31722)------------------------------
% 0.22/0.52  % (31722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (31726)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (31730)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (31730)Memory used [KB]: 10746
% 0.22/0.52  % (31730)Time elapsed: 0.092 s
% 0.22/0.52  % (31730)------------------------------
% 0.22/0.52  % (31730)------------------------------
% 0.22/0.52  % (31722)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (31722)Memory used [KB]: 1663
% 0.22/0.52  % (31722)Time elapsed: 0.105 s
% 0.22/0.52  % (31722)------------------------------
% 0.22/0.52  % (31722)------------------------------
% 0.22/0.52  % (31744)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (31738)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.53  % (31738)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f182,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f55,f64,f69,f74,f81,f99,f103,f147,f150,f152,f160,f181])).
% 0.22/0.53  fof(f181,plain,(
% 0.22/0.53    spl3_9 | ~spl3_14),
% 0.22/0.53    inference(avatar_split_clause,[],[f180,f157,f113])).
% 0.22/0.53  fof(f113,plain,(
% 0.22/0.53    spl3_9 <=> k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.53  fof(f157,plain,(
% 0.22/0.53    spl3_14 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.53  fof(f180,plain,(
% 0.22/0.53    k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | ~spl3_14),
% 0.22/0.53    inference(forward_demodulation,[],[f173,f75])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.53    inference(forward_demodulation,[],[f42,f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 0.22/0.53    inference(definition_unfolding,[],[f21,f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.53  fof(f173,plain,(
% 0.22/0.53    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl3_14),
% 0.22/0.53    inference(backward_demodulation,[],[f159,f90])).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    ( ! [X0] : (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.53    inference(forward_demodulation,[],[f86,f75])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    ( ! [X0] : (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))) )),
% 0.22/0.53    inference(superposition,[],[f45,f20])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f28,f36,f27])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f25,f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f26,f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f32,f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,axiom,(
% 0.22/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.53  fof(f159,plain,(
% 0.22/0.53    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) | ~spl3_14),
% 0.22/0.53    inference(avatar_component_clause,[],[f157])).
% 0.22/0.53  fof(f160,plain,(
% 0.22/0.53    spl3_14 | ~spl3_5 | ~spl3_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f155,f108,f71,f157])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    spl3_5 <=> k1_xboole_0 = sK2),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    spl3_8 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.53  fof(f155,plain,(
% 0.22/0.53    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) | (~spl3_5 | ~spl3_8)),
% 0.22/0.53    inference(forward_demodulation,[],[f110,f72])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    k1_xboole_0 = sK2 | ~spl3_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f71])).
% 0.22/0.53  fof(f110,plain,(
% 0.22/0.53    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2)) | ~spl3_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f108])).
% 0.22/0.53  fof(f152,plain,(
% 0.22/0.53    spl3_5 | spl3_2 | ~spl3_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f151,f96,f57,f71])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    spl3_2 <=> sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.53  fof(f96,plain,(
% 0.22/0.53    spl3_7 <=> r1_tarski(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.53  fof(f151,plain,(
% 0.22/0.53    sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 = sK2 | ~spl3_7),
% 0.22/0.53    inference(resolution,[],[f98,f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1)) | k3_enumset1(X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 0.22/0.53    inference(definition_unfolding,[],[f29,f37,f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f22,f35])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    r1_tarski(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~spl3_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f96])).
% 0.22/0.53  fof(f150,plain,(
% 0.22/0.53    spl3_8 | ~spl3_1 | ~spl3_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f149,f66,f52,f108])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    spl3_1 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    spl3_4 <=> k1_xboole_0 = sK1),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.53  fof(f149,plain,(
% 0.22/0.53    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2)) | (~spl3_1 | ~spl3_4)),
% 0.22/0.53    inference(forward_demodulation,[],[f54,f67])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    k1_xboole_0 = sK1 | ~spl3_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f66])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2)) | ~spl3_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f52])).
% 0.22/0.53  fof(f147,plain,(
% 0.22/0.53    ~spl3_9 | spl3_3 | ~spl3_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f146,f66,f61,f113])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    spl3_3 <=> sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.53  fof(f146,plain,(
% 0.22/0.53    k1_xboole_0 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | (spl3_3 | ~spl3_4)),
% 0.22/0.53    inference(forward_demodulation,[],[f63,f67])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | spl3_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f61])).
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    spl3_4 | spl3_3 | ~spl3_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f102,f78,f61,f66])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    spl3_6 <=> r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.53  fof(f102,plain,(
% 0.22/0.53    sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 = sK1 | ~spl3_6),
% 0.22/0.53    inference(resolution,[],[f48,f80])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~spl3_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f78])).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    spl3_7 | ~spl3_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f91,f52,f96])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    r1_tarski(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~spl3_1),
% 0.22/0.53    inference(superposition,[],[f82,f54])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)))) )),
% 0.22/0.53    inference(superposition,[],[f43,f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f24,f36,f36])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f23,f36])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    spl3_6 | ~spl3_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f76,f52,f78])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~spl3_1),
% 0.22/0.53    inference(superposition,[],[f43,f54])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    ~spl3_5 | ~spl3_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f41,f61,f71])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK2),
% 0.22/0.53    inference(definition_unfolding,[],[f16,f37])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.22/0.53    inference(ennf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.22/0.53    inference(negated_conjecture,[],[f13])).
% 0.22/0.53  fof(f13,conjecture,(
% 0.22/0.53    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    ~spl3_2 | ~spl3_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f40,f66,f57])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    k1_xboole_0 != sK1 | sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.22/0.53    inference(definition_unfolding,[],[f17,f37])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    k1_xboole_0 != sK1 | sK2 != k1_tarski(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ~spl3_2 | ~spl3_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f39,f61,f57])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.22/0.53    inference(definition_unfolding,[],[f18,f37,f37])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    sK1 != k1_tarski(sK0) | sK2 != k1_tarski(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    spl3_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f38,f52])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),
% 0.22/0.53    inference(definition_unfolding,[],[f19,f37,f36])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (31738)------------------------------
% 0.22/0.53  % (31738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (31738)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (31738)Memory used [KB]: 10746
% 0.22/0.53  % (31738)Time elapsed: 0.109 s
% 0.22/0.53  % (31738)------------------------------
% 0.22/0.53  % (31738)------------------------------
% 0.22/0.53  % (31721)Success in time 0.163 s
%------------------------------------------------------------------------------
