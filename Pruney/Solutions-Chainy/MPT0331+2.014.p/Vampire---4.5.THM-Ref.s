%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:06 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 125 expanded)
%              Number of leaves         :   18 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :  136 ( 269 expanded)
%              Number of equality atoms :   33 (  68 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f148,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f109,f139,f145,f147])).

fof(f147,plain,(
    ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | ~ spl5_6 ),
    inference(resolution,[],[f106,f25])).

fof(f25,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1))
    & ~ r2_hidden(sK1,sK2)
    & ~ r2_hidden(sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) )
   => ( sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1))
      & ~ r2_hidden(sK1,sK2)
      & ~ r2_hidden(sK0,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
      & ~ r2_hidden(X1,X2)
      & ~ r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
          & ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(f106,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl5_6
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f145,plain,
    ( spl5_5
    | spl5_6
    | spl5_3 ),
    inference(avatar_split_clause,[],[f97,f82,f104,f100])).

fof(f100,plain,
    ( spl5_5
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f82,plain,
    ( spl5_3
  <=> r1_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f97,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | spl5_3 ),
    inference(resolution,[],[f96,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f31,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f35,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(f96,plain,
    ( ~ r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)
    | spl5_3 ),
    inference(resolution,[],[f92,f84])).

fof(f84,plain,
    ( ~ r1_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f92,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(X3,X2)
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f50,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X1,X0))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f34,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f139,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | spl5_4 ),
    inference(resolution,[],[f132,f48])).

fof(f48,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f42,f41])).

fof(f41,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f27,f32])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f27,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f42,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f29,f32])).

fof(f29,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f132,plain,
    ( ~ r1_xboole_0(sK2,k1_xboole_0)
    | spl5_4 ),
    inference(trivial_inequality_removal,[],[f129])).

fof(f129,plain,
    ( sK2 != sK2
    | ~ r1_xboole_0(sK2,k1_xboole_0)
    | spl5_4 ),
    inference(superposition,[],[f88,f70])).

fof(f70,plain,(
    ! [X13] :
      ( k5_xboole_0(X13,k1_xboole_0) = X13
      | ~ r1_xboole_0(X13,k1_xboole_0) ) ),
    inference(superposition,[],[f41,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f34,f28])).

fof(f28,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f20])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f88,plain,
    ( sK2 != k5_xboole_0(sK2,k1_xboole_0)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl5_4
  <=> sK2 = k5_xboole_0(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f109,plain,(
    ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | ~ spl5_5 ),
    inference(resolution,[],[f102,f24])).

fof(f24,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f102,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f100])).

fof(f89,plain,
    ( ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f72,f86,f82])).

fof(f72,plain,
    ( sK2 != k5_xboole_0(sK2,k1_xboole_0)
    | ~ r1_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) ),
    inference(superposition,[],[f40,f49])).

fof(f40,plain,(
    sK2 != k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f26,f32,f39])).

fof(f26,plain,(
    sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:00:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (798326786)
% 0.13/0.37  ipcrm: permission denied for id (798359555)
% 0.13/0.37  ipcrm: permission denied for id (798392325)
% 0.13/0.37  ipcrm: permission denied for id (798425095)
% 0.13/0.38  ipcrm: permission denied for id (798523403)
% 0.13/0.38  ipcrm: permission denied for id (798621713)
% 0.13/0.39  ipcrm: permission denied for id (798687252)
% 0.13/0.39  ipcrm: permission denied for id (798785559)
% 0.20/0.40  ipcrm: permission denied for id (798916636)
% 0.20/0.40  ipcrm: permission denied for id (799047713)
% 0.20/0.40  ipcrm: permission denied for id (799080482)
% 0.20/0.41  ipcrm: permission denied for id (799211558)
% 0.20/0.41  ipcrm: permission denied for id (799277096)
% 0.20/0.41  ipcrm: permission denied for id (799342634)
% 0.20/0.42  ipcrm: permission denied for id (799375403)
% 0.20/0.42  ipcrm: permission denied for id (799408173)
% 0.20/0.42  ipcrm: permission denied for id (799440942)
% 0.20/0.43  ipcrm: permission denied for id (799506482)
% 0.20/0.43  ipcrm: permission denied for id (799539251)
% 0.20/0.43  ipcrm: permission denied for id (799637559)
% 0.20/0.44  ipcrm: permission denied for id (799801404)
% 0.20/0.44  ipcrm: permission denied for id (799866942)
% 0.20/0.44  ipcrm: permission denied for id (799965249)
% 0.20/0.45  ipcrm: permission denied for id (800030787)
% 0.20/0.45  ipcrm: permission denied for id (800063558)
% 0.20/0.46  ipcrm: permission denied for id (800161865)
% 0.20/0.46  ipcrm: permission denied for id (800227404)
% 0.20/0.46  ipcrm: permission denied for id (800260173)
% 0.20/0.46  ipcrm: permission denied for id (800292942)
% 0.20/0.47  ipcrm: permission denied for id (800489556)
% 0.20/0.48  ipcrm: permission denied for id (800620634)
% 0.20/0.48  ipcrm: permission denied for id (800653404)
% 0.20/0.48  ipcrm: permission denied for id (800718941)
% 0.20/0.48  ipcrm: permission denied for id (800784479)
% 0.20/0.49  ipcrm: permission denied for id (800850017)
% 0.20/0.49  ipcrm: permission denied for id (800882786)
% 0.20/0.49  ipcrm: permission denied for id (800915555)
% 0.20/0.49  ipcrm: permission denied for id (800948325)
% 0.20/0.50  ipcrm: permission denied for id (800981096)
% 0.20/0.50  ipcrm: permission denied for id (801079406)
% 0.33/0.51  ipcrm: permission denied for id (801210484)
% 0.33/0.52  ipcrm: permission denied for id (801374329)
% 0.37/0.60  % (16100)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.37/0.60  % (16091)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.37/0.60  % (16091)Refutation found. Thanks to Tanya!
% 0.37/0.60  % SZS status Theorem for theBenchmark
% 0.37/0.60  % SZS output start Proof for theBenchmark
% 0.37/0.60  fof(f148,plain,(
% 0.37/0.60    $false),
% 0.37/0.60    inference(avatar_sat_refutation,[],[f89,f109,f139,f145,f147])).
% 0.37/0.60  fof(f147,plain,(
% 0.37/0.60    ~spl5_6),
% 0.37/0.60    inference(avatar_contradiction_clause,[],[f146])).
% 0.37/0.60  fof(f146,plain,(
% 0.37/0.60    $false | ~spl5_6),
% 0.37/0.60    inference(resolution,[],[f106,f25])).
% 0.37/0.60  fof(f25,plain,(
% 0.37/0.60    ~r2_hidden(sK1,sK2)),
% 0.37/0.60    inference(cnf_transformation,[],[f19])).
% 0.37/0.60  fof(f19,plain,(
% 0.37/0.60    sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1)) & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)),
% 0.37/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f18])).
% 0.37/0.60  fof(f18,plain,(
% 0.37/0.60    ? [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) => (sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1)) & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2))),
% 0.37/0.60    introduced(choice_axiom,[])).
% 0.37/0.60  fof(f14,plain,(
% 0.37/0.60    ? [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 0.37/0.60    inference(ennf_transformation,[],[f12])).
% 0.37/0.60  fof(f12,negated_conjecture,(
% 0.37/0.60    ~! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 0.37/0.60    inference(negated_conjecture,[],[f11])).
% 0.37/0.60  fof(f11,conjecture,(
% 0.37/0.60    ! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 0.37/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).
% 0.37/0.60  fof(f106,plain,(
% 0.37/0.60    r2_hidden(sK1,sK2) | ~spl5_6),
% 0.37/0.60    inference(avatar_component_clause,[],[f104])).
% 0.37/0.60  fof(f104,plain,(
% 0.37/0.60    spl5_6 <=> r2_hidden(sK1,sK2)),
% 0.37/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.37/0.60  fof(f145,plain,(
% 0.37/0.60    spl5_5 | spl5_6 | spl5_3),
% 0.37/0.60    inference(avatar_split_clause,[],[f97,f82,f104,f100])).
% 0.37/0.60  fof(f100,plain,(
% 0.37/0.60    spl5_5 <=> r2_hidden(sK0,sK2)),
% 0.37/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.37/0.60  fof(f82,plain,(
% 0.37/0.60    spl5_3 <=> r1_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))),
% 0.37/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.37/0.60  fof(f97,plain,(
% 0.37/0.60    r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | spl5_3),
% 0.37/0.60    inference(resolution,[],[f96,f43])).
% 0.37/0.60  fof(f43,plain,(
% 0.37/0.60    ( ! [X2,X0,X1] : (r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 0.37/0.60    inference(definition_unfolding,[],[f36,f39])).
% 0.37/0.60  fof(f39,plain,(
% 0.37/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.37/0.60    inference(definition_unfolding,[],[f31,f38])).
% 0.37/0.60  fof(f38,plain,(
% 0.37/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.37/0.60    inference(definition_unfolding,[],[f35,f37])).
% 0.37/0.60  fof(f37,plain,(
% 0.37/0.60    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.37/0.60    inference(cnf_transformation,[],[f9])).
% 0.37/0.60  fof(f9,axiom,(
% 0.37/0.60    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.37/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.37/0.60  fof(f35,plain,(
% 0.37/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.37/0.60    inference(cnf_transformation,[],[f8])).
% 0.37/0.60  fof(f8,axiom,(
% 0.37/0.60    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.37/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.37/0.60  fof(f31,plain,(
% 0.37/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.37/0.60    inference(cnf_transformation,[],[f7])).
% 0.37/0.60  fof(f7,axiom,(
% 0.37/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.37/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.37/0.60  fof(f36,plain,(
% 0.37/0.60    ( ! [X2,X0,X1] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 0.37/0.60    inference(cnf_transformation,[],[f17])).
% 0.37/0.60  fof(f17,plain,(
% 0.37/0.60    ! [X0,X1,X2] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 0.37/0.60    inference(ennf_transformation,[],[f10])).
% 0.37/0.60  fof(f10,axiom,(
% 0.37/0.60    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 0.37/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).
% 0.37/0.60  fof(f96,plain,(
% 0.37/0.60    ~r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) | spl5_3),
% 0.37/0.60    inference(resolution,[],[f92,f84])).
% 0.37/0.60  fof(f84,plain,(
% 0.37/0.60    ~r1_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | spl5_3),
% 0.37/0.60    inference(avatar_component_clause,[],[f82])).
% 0.37/0.60  fof(f92,plain,(
% 0.37/0.60    ( ! [X2,X3] : (r1_xboole_0(X3,X2) | ~r1_xboole_0(X2,X3)) )),
% 0.37/0.60    inference(resolution,[],[f50,f33])).
% 0.37/0.60  fof(f33,plain,(
% 0.37/0.60    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.37/0.60    inference(cnf_transformation,[],[f23])).
% 0.37/0.60  fof(f23,plain,(
% 0.37/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.37/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f22])).
% 0.37/0.60  fof(f22,plain,(
% 0.37/0.60    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.37/0.60    introduced(choice_axiom,[])).
% 0.37/0.60  fof(f16,plain,(
% 0.37/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.37/0.60    inference(ennf_transformation,[],[f13])).
% 0.37/0.60  fof(f13,plain,(
% 0.37/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.37/0.60    inference(rectify,[],[f2])).
% 0.37/0.60  fof(f2,axiom,(
% 0.37/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.37/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.37/0.60  fof(f50,plain,(
% 0.37/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X1,X0)) | ~r1_xboole_0(X0,X1)) )),
% 0.37/0.60    inference(superposition,[],[f34,f30])).
% 0.37/0.60  fof(f30,plain,(
% 0.37/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.37/0.60    inference(cnf_transformation,[],[f1])).
% 0.37/0.60  fof(f1,axiom,(
% 0.37/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.37/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.37/0.60  fof(f34,plain,(
% 0.37/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.37/0.60    inference(cnf_transformation,[],[f23])).
% 0.37/0.60  fof(f139,plain,(
% 0.37/0.60    spl5_4),
% 0.37/0.60    inference(avatar_contradiction_clause,[],[f137])).
% 0.37/0.60  fof(f137,plain,(
% 0.37/0.60    $false | spl5_4),
% 0.37/0.60    inference(resolution,[],[f132,f48])).
% 0.37/0.60  fof(f48,plain,(
% 0.37/0.60    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.37/0.60    inference(superposition,[],[f42,f41])).
% 0.37/0.60  fof(f41,plain,(
% 0.37/0.60    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 0.37/0.60    inference(definition_unfolding,[],[f27,f32])).
% 0.37/0.60  fof(f32,plain,(
% 0.37/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.37/0.60    inference(cnf_transformation,[],[f4])).
% 0.37/0.60  fof(f4,axiom,(
% 0.37/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.37/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.37/0.60  fof(f27,plain,(
% 0.37/0.60    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.37/0.60    inference(cnf_transformation,[],[f5])).
% 0.37/0.60  fof(f5,axiom,(
% 0.37/0.60    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.37/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.37/0.60  fof(f42,plain,(
% 0.37/0.60    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 0.37/0.60    inference(definition_unfolding,[],[f29,f32])).
% 0.37/0.60  fof(f29,plain,(
% 0.37/0.60    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.37/0.60    inference(cnf_transformation,[],[f6])).
% 0.37/0.60  fof(f6,axiom,(
% 0.37/0.60    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.37/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.37/0.60  fof(f132,plain,(
% 0.37/0.60    ~r1_xboole_0(sK2,k1_xboole_0) | spl5_4),
% 0.37/0.60    inference(trivial_inequality_removal,[],[f129])).
% 0.37/0.60  fof(f129,plain,(
% 0.37/0.60    sK2 != sK2 | ~r1_xboole_0(sK2,k1_xboole_0) | spl5_4),
% 0.37/0.60    inference(superposition,[],[f88,f70])).
% 0.37/0.60  fof(f70,plain,(
% 0.37/0.60    ( ! [X13] : (k5_xboole_0(X13,k1_xboole_0) = X13 | ~r1_xboole_0(X13,k1_xboole_0)) )),
% 0.37/0.60    inference(superposition,[],[f41,f49])).
% 0.37/0.60  fof(f49,plain,(
% 0.37/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.37/0.60    inference(resolution,[],[f34,f28])).
% 0.37/0.60  fof(f28,plain,(
% 0.37/0.60    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.37/0.60    inference(cnf_transformation,[],[f21])).
% 0.37/0.60  fof(f21,plain,(
% 0.37/0.60    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.37/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f20])).
% 0.37/0.60  fof(f20,plain,(
% 0.37/0.60    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.37/0.60    introduced(choice_axiom,[])).
% 0.37/0.60  fof(f15,plain,(
% 0.37/0.60    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.37/0.60    inference(ennf_transformation,[],[f3])).
% 0.37/0.60  fof(f3,axiom,(
% 0.37/0.60    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.37/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.37/0.60  fof(f88,plain,(
% 0.37/0.60    sK2 != k5_xboole_0(sK2,k1_xboole_0) | spl5_4),
% 0.37/0.60    inference(avatar_component_clause,[],[f86])).
% 0.37/0.60  fof(f86,plain,(
% 0.37/0.60    spl5_4 <=> sK2 = k5_xboole_0(sK2,k1_xboole_0)),
% 0.37/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.37/0.60  fof(f109,plain,(
% 0.37/0.60    ~spl5_5),
% 0.37/0.60    inference(avatar_contradiction_clause,[],[f108])).
% 0.37/0.60  fof(f108,plain,(
% 0.37/0.60    $false | ~spl5_5),
% 0.37/0.60    inference(resolution,[],[f102,f24])).
% 0.37/0.60  fof(f24,plain,(
% 0.37/0.60    ~r2_hidden(sK0,sK2)),
% 0.37/0.60    inference(cnf_transformation,[],[f19])).
% 0.37/0.60  fof(f102,plain,(
% 0.37/0.60    r2_hidden(sK0,sK2) | ~spl5_5),
% 0.37/0.60    inference(avatar_component_clause,[],[f100])).
% 0.37/0.60  fof(f89,plain,(
% 0.37/0.60    ~spl5_3 | ~spl5_4),
% 0.37/0.60    inference(avatar_split_clause,[],[f72,f86,f82])).
% 0.37/0.60  fof(f72,plain,(
% 0.37/0.60    sK2 != k5_xboole_0(sK2,k1_xboole_0) | ~r1_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))),
% 0.37/0.60    inference(superposition,[],[f40,f49])).
% 0.37/0.60  fof(f40,plain,(
% 0.37/0.60    sK2 != k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))),
% 0.37/0.60    inference(definition_unfolding,[],[f26,f32,f39])).
% 0.37/0.60  fof(f26,plain,(
% 0.37/0.60    sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1))),
% 0.37/0.60    inference(cnf_transformation,[],[f19])).
% 0.37/0.60  % SZS output end Proof for theBenchmark
% 0.37/0.60  % (16091)------------------------------
% 0.37/0.60  % (16091)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.37/0.60  % (16091)Termination reason: Refutation
% 0.37/0.60  
% 0.37/0.60  % (16091)Memory used [KB]: 6140
% 0.37/0.60  % (16091)Time elapsed: 0.028 s
% 0.37/0.60  % (16091)------------------------------
% 0.37/0.60  % (16091)------------------------------
% 0.37/0.60  % (15862)Success in time 0.246 s
%------------------------------------------------------------------------------
