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
% DateTime   : Thu Dec  3 12:37:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 390 expanded)
%              Number of leaves         :   14 ( 131 expanded)
%              Depth                    :   12
%              Number of atoms          :  122 ( 709 expanded)
%              Number of equality atoms :  108 ( 673 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f128,plain,(
    $false ),
    inference(global_subsumption,[],[f53,f54,f55,f108,f109,f127])).

fof(f127,plain,
    ( sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(forward_demodulation,[],[f126,f32])).

fof(f32,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f126,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k1_xboole_0)
    | sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(forward_demodulation,[],[f122,f57])).

fof(f57,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(definition_unfolding,[],[f31,f38])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f122,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK1)))
    | sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[],[f87,f109])).

fof(f87,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK1))) ),
    inference(superposition,[],[f60,f56])).

fof(f56,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f26,f52,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f36,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f46,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f46,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f33,f50])).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f26,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f20])).

fof(f20,plain,
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

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f60,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f39,f51,f38])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f109,plain,
    ( k1_xboole_0 = sK2
    | sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f63,f84])).

fof(f84,plain,(
    r1_tarski(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f80,f56])).

fof(f80,plain,(
    ! [X4,X3] : r1_tarski(X3,k3_tarski(k3_enumset1(X4,X4,X4,X4,X3))) ),
    inference(superposition,[],[f58,f59])).

fof(f59,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f35,f51,f51])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f34,f51])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k3_enumset1(X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f43,f52,f52])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f108,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f63,f73])).

fof(f73,plain,(
    r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f58,f56])).

fof(f55,plain,
    ( sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f27,f52,f52])).

fof(f27,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f54,plain,
    ( sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f28,f52])).

fof(f28,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f21])).

fof(f53,plain,
    ( sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f29,f52])).

fof(f29,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:31:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (6642)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.51  % (6659)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.51  % (6658)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.51  % (6658)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (6649)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.51  % (6652)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.51  % (6652)Refutation not found, incomplete strategy% (6652)------------------------------
% 0.20/0.51  % (6652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (6652)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (6652)Memory used [KB]: 10618
% 0.20/0.51  % (6652)Time elapsed: 0.111 s
% 0.20/0.51  % (6652)------------------------------
% 0.20/0.51  % (6652)------------------------------
% 1.25/0.52  % (6656)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.25/0.53  % SZS output start Proof for theBenchmark
% 1.25/0.53  fof(f128,plain,(
% 1.25/0.53    $false),
% 1.25/0.53    inference(global_subsumption,[],[f53,f54,f55,f108,f109,f127])).
% 1.25/0.53  fof(f127,plain,(
% 1.25/0.53    sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.25/0.53    inference(forward_demodulation,[],[f126,f32])).
% 1.25/0.53  fof(f32,plain,(
% 1.25/0.53    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.25/0.53    inference(cnf_transformation,[],[f7])).
% 1.25/0.53  fof(f7,axiom,(
% 1.25/0.53    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.25/0.53  fof(f126,plain,(
% 1.25/0.53    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k1_xboole_0) | sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.25/0.53    inference(forward_demodulation,[],[f122,f57])).
% 1.25/0.53  fof(f57,plain,(
% 1.25/0.53    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 1.25/0.53    inference(definition_unfolding,[],[f31,f38])).
% 1.25/0.53  fof(f38,plain,(
% 1.25/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.25/0.53    inference(cnf_transformation,[],[f3])).
% 1.25/0.53  fof(f3,axiom,(
% 1.25/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.25/0.53  fof(f31,plain,(
% 1.25/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f6])).
% 1.25/0.53  fof(f6,axiom,(
% 1.25/0.53    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 1.25/0.53  fof(f122,plain,(
% 1.25/0.53    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK1))) | sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.25/0.53    inference(superposition,[],[f87,f109])).
% 1.25/0.53  fof(f87,plain,(
% 1.25/0.53    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK1)))),
% 1.25/0.53    inference(superposition,[],[f60,f56])).
% 1.25/0.53  fof(f56,plain,(
% 1.25/0.53    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),
% 1.25/0.53    inference(definition_unfolding,[],[f26,f52,f51])).
% 1.25/0.53  fof(f51,plain,(
% 1.25/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.25/0.53    inference(definition_unfolding,[],[f36,f50])).
% 1.25/0.53  fof(f50,plain,(
% 1.25/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.25/0.53    inference(definition_unfolding,[],[f37,f49])).
% 1.25/0.53  fof(f49,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.25/0.53    inference(definition_unfolding,[],[f46,f48])).
% 1.25/0.53  fof(f48,plain,(
% 1.25/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f13])).
% 1.25/0.53  fof(f13,axiom,(
% 1.25/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.25/0.53  fof(f46,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f12])).
% 1.25/0.53  fof(f12,axiom,(
% 1.25/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.25/0.53  fof(f37,plain,(
% 1.25/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f11])).
% 1.25/0.53  fof(f11,axiom,(
% 1.25/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.25/0.53  fof(f36,plain,(
% 1.25/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.25/0.53    inference(cnf_transformation,[],[f15])).
% 1.25/0.53  fof(f15,axiom,(
% 1.25/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.25/0.53  fof(f52,plain,(
% 1.25/0.53    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.25/0.53    inference(definition_unfolding,[],[f33,f50])).
% 1.25/0.53  fof(f33,plain,(
% 1.25/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f10])).
% 1.25/0.53  fof(f10,axiom,(
% 1.25/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.25/0.53  fof(f26,plain,(
% 1.25/0.53    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.25/0.53    inference(cnf_transformation,[],[f21])).
% 1.25/0.53  fof(f21,plain,(
% 1.25/0.53    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.25/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f20])).
% 1.25/0.53  fof(f20,plain,(
% 1.25/0.53    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 1.25/0.53    introduced(choice_axiom,[])).
% 1.25/0.53  fof(f18,plain,(
% 1.25/0.53    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.25/0.53    inference(ennf_transformation,[],[f17])).
% 1.25/0.53  fof(f17,negated_conjecture,(
% 1.25/0.53    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.25/0.53    inference(negated_conjecture,[],[f16])).
% 1.25/0.53  fof(f16,conjecture,(
% 1.25/0.53    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.25/0.53  fof(f60,plain,(
% 1.25/0.53    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.25/0.53    inference(definition_unfolding,[],[f39,f51,f38])).
% 1.25/0.53  fof(f39,plain,(
% 1.25/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.25/0.53    inference(cnf_transformation,[],[f9])).
% 1.25/0.53  fof(f9,axiom,(
% 1.25/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.25/0.53  fof(f109,plain,(
% 1.25/0.53    k1_xboole_0 = sK2 | sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.25/0.53    inference(resolution,[],[f63,f84])).
% 1.25/0.53  fof(f84,plain,(
% 1.25/0.53    r1_tarski(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 1.25/0.53    inference(superposition,[],[f80,f56])).
% 1.25/0.53  fof(f80,plain,(
% 1.25/0.53    ( ! [X4,X3] : (r1_tarski(X3,k3_tarski(k3_enumset1(X4,X4,X4,X4,X3)))) )),
% 1.25/0.53    inference(superposition,[],[f58,f59])).
% 1.25/0.53  fof(f59,plain,(
% 1.25/0.53    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) )),
% 1.25/0.53    inference(definition_unfolding,[],[f35,f51,f51])).
% 1.25/0.53  fof(f35,plain,(
% 1.25/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f1])).
% 1.25/0.53  fof(f1,axiom,(
% 1.25/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.25/0.53  fof(f58,plain,(
% 1.25/0.53    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 1.25/0.53    inference(definition_unfolding,[],[f34,f51])).
% 1.25/0.53  fof(f34,plain,(
% 1.25/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.25/0.53    inference(cnf_transformation,[],[f8])).
% 1.25/0.53  fof(f8,axiom,(
% 1.25/0.53    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.25/0.53  fof(f63,plain,(
% 1.25/0.53    ( ! [X0,X1] : (~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1)) | k1_xboole_0 = X0 | k3_enumset1(X1,X1,X1,X1,X1) = X0) )),
% 1.25/0.53    inference(definition_unfolding,[],[f43,f52,f52])).
% 1.25/0.53  fof(f43,plain,(
% 1.25/0.53    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.25/0.53    inference(cnf_transformation,[],[f25])).
% 1.25/0.53  fof(f25,plain,(
% 1.25/0.53    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.25/0.53    inference(flattening,[],[f24])).
% 1.25/0.53  fof(f24,plain,(
% 1.25/0.53    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.25/0.53    inference(nnf_transformation,[],[f14])).
% 1.25/0.53  fof(f14,axiom,(
% 1.25/0.53    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.25/0.53  fof(f108,plain,(
% 1.25/0.53    k1_xboole_0 = sK1 | sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.25/0.53    inference(resolution,[],[f63,f73])).
% 1.25/0.53  fof(f73,plain,(
% 1.25/0.53    r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 1.25/0.53    inference(superposition,[],[f58,f56])).
% 1.25/0.53  fof(f55,plain,(
% 1.25/0.53    sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.25/0.53    inference(definition_unfolding,[],[f27,f52,f52])).
% 1.25/0.53  fof(f27,plain,(
% 1.25/0.53    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 1.25/0.53    inference(cnf_transformation,[],[f21])).
% 1.25/0.53  fof(f54,plain,(
% 1.25/0.53    sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK1),
% 1.25/0.53    inference(definition_unfolding,[],[f28,f52])).
% 1.25/0.53  fof(f28,plain,(
% 1.25/0.53    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 1.25/0.53    inference(cnf_transformation,[],[f21])).
% 1.25/0.53  fof(f53,plain,(
% 1.25/0.53    sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK2),
% 1.25/0.53    inference(definition_unfolding,[],[f29,f52])).
% 1.25/0.53  fof(f29,plain,(
% 1.25/0.53    k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)),
% 1.25/0.53    inference(cnf_transformation,[],[f21])).
% 1.25/0.53  % SZS output end Proof for theBenchmark
% 1.25/0.53  % (6658)------------------------------
% 1.25/0.53  % (6658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.53  % (6658)Termination reason: Refutation
% 1.25/0.53  
% 1.25/0.53  % (6658)Memory used [KB]: 6268
% 1.25/0.53  % (6658)Time elapsed: 0.084 s
% 1.25/0.53  % (6658)------------------------------
% 1.25/0.53  % (6658)------------------------------
% 1.25/0.53  % (6627)Success in time 0.173 s
%------------------------------------------------------------------------------
