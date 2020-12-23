%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:18 EST 2020

% Result     : Theorem 2.77s
% Output     : Refutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 124 expanded)
%              Number of leaves         :   19 (  40 expanded)
%              Depth                    :   13
%              Number of atoms          :  162 ( 238 expanded)
%              Number of equality atoms :   55 (  85 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (13360)Termination reason: Refutation not found, incomplete strategy

% (13360)Memory used [KB]: 10618
% (13360)Time elapsed: 0.090 s
% (13360)------------------------------
% (13360)------------------------------
fof(f2080,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f95,f277,f2067])).

fof(f2067,plain,
    ( spl3_3
    | ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f2066])).

fof(f2066,plain,
    ( $false
    | spl3_3
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f2064,f313])).

fof(f313,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f97,f298])).

fof(f298,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f118,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f118,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)) ),
    inference(unit_resulting_resolution,[],[f83,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).

fof(f83,plain,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f42,f38])).

fof(f38,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f42,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f97,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(k1_xboole_0,X1)) ),
    inference(unit_resulting_resolution,[],[f82,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f82,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f42,f37])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f2064,plain,
    ( r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1),k1_xboole_0)
    | spl3_3
    | ~ spl3_6 ),
    inference(backward_demodulation,[],[f276,f2051])).

fof(f2051,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)
    | spl3_3 ),
    inference(unit_resulting_resolution,[],[f94,f1695,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_enumset1(X1,X1,X1))
      | k1_xboole_0 = X0
      | k1_enumset1(X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f53,f39,f39])).

fof(f39,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(f1695,plain,(
    ! [X6,X7] : r1_tarski(k3_xboole_0(X6,X7),X6) ),
    inference(forward_demodulation,[],[f1684,f163])).

fof(f163,plain,(
    ! [X2] : k5_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f162,f38])).

fof(f162,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f155,f37])).

fof(f155,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k4_xboole_0(k1_xboole_0,X2)) ),
    inference(superposition,[],[f62,f38])).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) ),
    inference(definition_unfolding,[],[f44,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f1684,plain,(
    ! [X6,X7] : r1_tarski(k3_xboole_0(X6,X7),k5_xboole_0(X6,k1_xboole_0)) ),
    inference(superposition,[],[f216,f316])).

fof(f316,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(unit_resulting_resolution,[],[f141,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X0)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f59,f41])).

fof(f141,plain,(
    ! [X10,X11,X9] : r1_xboole_0(k3_xboole_0(X9,k4_xboole_0(X10,X11)),X11) ),
    inference(superposition,[],[f42,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f216,plain,(
    ! [X2,X3,X1] : r1_tarski(k3_xboole_0(X1,X2),k5_xboole_0(X3,k3_xboole_0(X1,k4_xboole_0(X2,X3)))) ),
    inference(superposition,[],[f132,f56])).

fof(f132,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) ),
    inference(unit_resulting_resolution,[],[f68,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k5_xboole_0(X2,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f58,f43])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f68,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f94,plain,
    ( k1_enumset1(sK0,sK0,sK0) != k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl3_3
  <=> k1_enumset1(sK0,sK0,sK0) = k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f276,plain,
    ( r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f274])).

fof(f274,plain,
    ( spl3_6
  <=> r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f277,plain,
    ( spl3_6
    | spl3_2 ),
    inference(avatar_split_clause,[],[f125,f78,f274])).

fof(f78,plain,
    ( spl3_2
  <=> r1_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f125,plain,
    ( r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1))
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f80,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f80,plain,
    ( ~ r1_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f95,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f60,f92])).

fof(f60,plain,(
    k1_enumset1(sK0,sK0,sK0) != k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f36,f39,f39])).

fof(f36,plain,(
    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)
    & ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1)
        & ~ r1_xboole_0(k1_tarski(X0),X1) )
   => ( k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)
      & ~ r1_xboole_0(k1_tarski(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1)
      & ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)
        | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_zfmisc_1)).

fof(f81,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f61,f78])).

fof(f61,plain,(
    ~ r1_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f35,f39])).

fof(f35,plain,(
    ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:34:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.23/0.56  % (13327)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.23/0.56  % (13336)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.23/0.56  % (13328)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.23/0.57  % (13335)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.23/0.57  % (13343)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.23/0.58  % (13344)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.23/0.58  % (13344)Refutation not found, incomplete strategy% (13344)------------------------------
% 0.23/0.58  % (13344)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.58  % (13344)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.58  
% 0.23/0.58  % (13344)Memory used [KB]: 10618
% 0.23/0.58  % (13344)Time elapsed: 0.148 s
% 0.23/0.58  % (13344)------------------------------
% 0.23/0.58  % (13344)------------------------------
% 0.23/0.58  % (13336)Refutation not found, incomplete strategy% (13336)------------------------------
% 0.23/0.58  % (13336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.58  % (13336)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.58  
% 0.23/0.58  % (13336)Memory used [KB]: 10618
% 0.23/0.58  % (13336)Time elapsed: 0.151 s
% 0.23/0.58  % (13336)------------------------------
% 0.23/0.58  % (13336)------------------------------
% 1.75/0.61  % (13330)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.75/0.61  % (13333)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.75/0.61  % (13320)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.75/0.61  % (13323)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.75/0.61  % (13326)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.75/0.61  % (13325)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.75/0.61  % (13324)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.75/0.61  % (13338)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.75/0.61  % (13341)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.75/0.62  % (13345)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.75/0.62  % (13337)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.75/0.62  % (13332)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.75/0.62  % (13346)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.75/0.62  % (13349)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.75/0.62  % (13322)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.75/0.62  % (13321)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.75/0.62  % (13337)Refutation not found, incomplete strategy% (13337)------------------------------
% 1.75/0.62  % (13337)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.62  % (13348)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.75/0.62  % (13329)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.93/0.62  % (13345)Refutation not found, incomplete strategy% (13345)------------------------------
% 1.93/0.62  % (13345)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.93/0.63  % (13338)Refutation not found, incomplete strategy% (13338)------------------------------
% 1.93/0.63  % (13338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.93/0.63  % (13346)Refutation not found, incomplete strategy% (13346)------------------------------
% 1.93/0.63  % (13346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.93/0.63  % (13330)Refutation not found, incomplete strategy% (13330)------------------------------
% 1.93/0.63  % (13330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.93/0.63  % (13338)Termination reason: Refutation not found, incomplete strategy
% 1.93/0.63  
% 1.93/0.63  % (13338)Memory used [KB]: 1663
% 1.93/0.63  % (13338)Time elapsed: 0.189 s
% 1.93/0.63  % (13338)------------------------------
% 1.93/0.63  % (13338)------------------------------
% 1.93/0.63  % (13342)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.93/0.63  % (13339)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.93/0.63  % (13346)Termination reason: Refutation not found, incomplete strategy
% 1.93/0.63  % (13337)Termination reason: Refutation not found, incomplete strategy
% 1.93/0.63  
% 1.93/0.63  % (13337)Memory used [KB]: 1663
% 1.93/0.63  % (13337)Time elapsed: 0.145 s
% 1.93/0.63  % (13337)------------------------------
% 1.93/0.63  % (13337)------------------------------
% 1.93/0.63  
% 1.93/0.63  % (13346)Memory used [KB]: 6140
% 1.93/0.63  % (13346)Time elapsed: 0.191 s
% 1.93/0.63  % (13346)------------------------------
% 1.93/0.63  % (13346)------------------------------
% 1.93/0.63  % (13345)Termination reason: Refutation not found, incomplete strategy
% 1.93/0.63  
% 1.93/0.63  % (13345)Memory used [KB]: 6140
% 1.93/0.63  % (13345)Time elapsed: 0.146 s
% 1.93/0.63  % (13345)------------------------------
% 1.93/0.63  % (13345)------------------------------
% 1.93/0.63  % (13334)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.93/0.63  % (13321)Refutation not found, incomplete strategy% (13321)------------------------------
% 1.93/0.63  % (13321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.93/0.63  % (13321)Termination reason: Refutation not found, incomplete strategy
% 1.93/0.63  
% 1.93/0.63  % (13321)Memory used [KB]: 1663
% 1.93/0.63  % (13321)Time elapsed: 0.157 s
% 1.93/0.63  % (13321)------------------------------
% 1.93/0.63  % (13321)------------------------------
% 1.93/0.63  % (13334)Refutation not found, incomplete strategy% (13334)------------------------------
% 1.93/0.63  % (13334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.93/0.63  % (13334)Termination reason: Refutation not found, incomplete strategy
% 1.93/0.63  
% 1.93/0.63  % (13334)Memory used [KB]: 1663
% 1.93/0.63  % (13334)Time elapsed: 0.201 s
% 1.93/0.63  % (13334)------------------------------
% 1.93/0.63  % (13334)------------------------------
% 1.93/0.64  % (13330)Termination reason: Refutation not found, incomplete strategy
% 1.93/0.64  
% 1.93/0.64  % (13330)Memory used [KB]: 10618
% 1.93/0.64  % (13330)Time elapsed: 0.189 s
% 1.93/0.64  % (13330)------------------------------
% 1.93/0.64  % (13330)------------------------------
% 1.93/0.64  % (13348)Refutation not found, incomplete strategy% (13348)------------------------------
% 1.93/0.64  % (13348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.93/0.64  % (13348)Termination reason: Refutation not found, incomplete strategy
% 1.93/0.64  
% 1.93/0.64  % (13348)Memory used [KB]: 10746
% 1.93/0.64  % (13348)Time elapsed: 0.200 s
% 1.93/0.64  % (13348)------------------------------
% 1.93/0.64  % (13348)------------------------------
% 1.93/0.64  % (13347)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.93/0.64  % (13340)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.93/0.64  % (13347)Refutation not found, incomplete strategy% (13347)------------------------------
% 1.93/0.64  % (13347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.93/0.64  % (13347)Termination reason: Refutation not found, incomplete strategy
% 1.93/0.64  
% 1.93/0.64  % (13347)Memory used [KB]: 6140
% 1.93/0.64  % (13347)Time elapsed: 0.207 s
% 1.93/0.64  % (13347)------------------------------
% 1.93/0.64  % (13347)------------------------------
% 1.93/0.64  % (13349)Refutation not found, incomplete strategy% (13349)------------------------------
% 1.93/0.64  % (13349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.93/0.64  % (13349)Termination reason: Refutation not found, incomplete strategy
% 1.93/0.64  
% 1.93/0.64  % (13349)Memory used [KB]: 1663
% 1.93/0.64  % (13349)Time elapsed: 0.211 s
% 1.93/0.64  % (13349)------------------------------
% 1.93/0.64  % (13349)------------------------------
% 1.93/0.64  % (13331)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.93/0.64  % (13331)Refutation not found, incomplete strategy% (13331)------------------------------
% 1.93/0.64  % (13331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.93/0.64  % (13331)Termination reason: Refutation not found, incomplete strategy
% 1.93/0.64  
% 1.93/0.64  % (13331)Memory used [KB]: 6268
% 1.93/0.64  % (13331)Time elapsed: 0.211 s
% 1.93/0.64  % (13331)------------------------------
% 1.93/0.64  % (13331)------------------------------
% 2.21/0.71  % (13355)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.54/0.75  % (13361)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.54/0.75  % (13356)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.54/0.75  % (13357)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.54/0.76  % (13354)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.54/0.76  % (13359)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.54/0.76  % (13322)Refutation not found, incomplete strategy% (13322)------------------------------
% 2.54/0.76  % (13322)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.54/0.76  % (13322)Termination reason: Refutation not found, incomplete strategy
% 2.54/0.76  
% 2.54/0.76  % (13322)Memory used [KB]: 6268
% 2.54/0.76  % (13322)Time elapsed: 0.297 s
% 2.54/0.76  % (13322)------------------------------
% 2.54/0.76  % (13322)------------------------------
% 2.54/0.77  % (13357)Refutation not found, incomplete strategy% (13357)------------------------------
% 2.54/0.77  % (13357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.54/0.77  % (13357)Termination reason: Refutation not found, incomplete strategy
% 2.54/0.77  
% 2.54/0.77  % (13357)Memory used [KB]: 10618
% 2.54/0.77  % (13357)Time elapsed: 0.111 s
% 2.54/0.77  % (13357)------------------------------
% 2.54/0.77  % (13357)------------------------------
% 2.54/0.77  % (13363)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.54/0.77  % (13362)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.54/0.77  % (13363)Refutation not found, incomplete strategy% (13363)------------------------------
% 2.54/0.77  % (13363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.54/0.77  % (13363)Termination reason: Refutation not found, incomplete strategy
% 2.54/0.77  
% 2.54/0.77  % (13363)Memory used [KB]: 10746
% 2.54/0.77  % (13363)Time elapsed: 0.108 s
% 2.54/0.77  % (13363)------------------------------
% 2.54/0.77  % (13363)------------------------------
% 2.54/0.77  % (13365)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 2.54/0.77  % (13364)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 2.77/0.78  % (13360)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.77/0.78  % (13358)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.77/0.78  % (13323)Refutation not found, incomplete strategy% (13323)------------------------------
% 2.77/0.78  % (13323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.77/0.78  % (13323)Termination reason: Refutation not found, incomplete strategy
% 2.77/0.78  
% 2.77/0.78  % (13323)Memory used [KB]: 6140
% 2.77/0.78  % (13323)Time elapsed: 0.336 s
% 2.77/0.78  % (13323)------------------------------
% 2.77/0.78  % (13323)------------------------------
% 2.77/0.78  % (13358)Refutation not found, incomplete strategy% (13358)------------------------------
% 2.77/0.78  % (13358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.77/0.78  % (13340)Refutation found. Thanks to Tanya!
% 2.77/0.78  % SZS status Theorem for theBenchmark
% 2.77/0.78  % (13360)Refutation not found, incomplete strategy% (13360)------------------------------
% 2.77/0.78  % (13360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.77/0.78  % (13358)Termination reason: Refutation not found, incomplete strategy
% 2.77/0.78  
% 2.77/0.78  % (13358)Memory used [KB]: 10618
% 2.77/0.78  % (13358)Time elapsed: 0.122 s
% 2.77/0.78  % (13358)------------------------------
% 2.77/0.78  % (13358)------------------------------
% 2.77/0.78  % SZS output start Proof for theBenchmark
% 2.77/0.78  % (13360)Termination reason: Refutation not found, incomplete strategy
% 2.77/0.78  
% 2.77/0.78  % (13360)Memory used [KB]: 10618
% 2.77/0.78  % (13360)Time elapsed: 0.090 s
% 2.77/0.78  % (13360)------------------------------
% 2.77/0.78  % (13360)------------------------------
% 2.77/0.78  fof(f2080,plain,(
% 2.77/0.78    $false),
% 2.77/0.78    inference(avatar_sat_refutation,[],[f81,f95,f277,f2067])).
% 2.77/0.78  fof(f2067,plain,(
% 2.77/0.78    spl3_3 | ~spl3_6),
% 2.77/0.78    inference(avatar_contradiction_clause,[],[f2066])).
% 2.77/0.78  fof(f2066,plain,(
% 2.77/0.78    $false | (spl3_3 | ~spl3_6)),
% 2.77/0.78    inference(subsumption_resolution,[],[f2064,f313])).
% 2.77/0.78  fof(f313,plain,(
% 2.77/0.78    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 2.77/0.78    inference(backward_demodulation,[],[f97,f298])).
% 2.77/0.78  fof(f298,plain,(
% 2.77/0.78    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 2.77/0.78    inference(unit_resulting_resolution,[],[f118,f41])).
% 2.77/0.78  fof(f41,plain,(
% 2.77/0.78    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 2.77/0.78    inference(cnf_transformation,[],[f21])).
% 2.77/0.78  fof(f21,plain,(
% 2.77/0.78    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 2.77/0.78    inference(ennf_transformation,[],[f10])).
% 2.77/0.78  fof(f10,axiom,(
% 2.77/0.78    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 2.77/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 2.77/0.78  fof(f118,plain,(
% 2.77/0.78    ( ! [X0,X1] : (r1_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1))) )),
% 2.77/0.78    inference(unit_resulting_resolution,[],[f83,f59])).
% 2.77/0.78  fof(f59,plain,(
% 2.77/0.78    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1)) )),
% 2.77/0.78    inference(cnf_transformation,[],[f25])).
% 2.77/0.78  fof(f25,plain,(
% 2.77/0.78    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 2.77/0.78    inference(ennf_transformation,[],[f11])).
% 2.77/0.78  fof(f11,axiom,(
% 2.77/0.78    ! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 2.77/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).
% 2.77/0.78  fof(f83,plain,(
% 2.77/0.78    ( ! [X1] : (r1_xboole_0(X1,k1_xboole_0)) )),
% 2.77/0.78    inference(superposition,[],[f42,f38])).
% 2.77/0.78  fof(f38,plain,(
% 2.77/0.78    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.77/0.78    inference(cnf_transformation,[],[f6])).
% 2.77/0.78  fof(f6,axiom,(
% 2.77/0.78    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.77/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 2.77/0.78  fof(f42,plain,(
% 2.77/0.78    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.77/0.78    inference(cnf_transformation,[],[f12])).
% 2.77/0.78  fof(f12,axiom,(
% 2.77/0.78    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.77/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 2.77/0.78  fof(f97,plain,(
% 2.77/0.78    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(k1_xboole_0,X1))) )),
% 2.77/0.78    inference(unit_resulting_resolution,[],[f82,f46])).
% 2.77/0.78  fof(f46,plain,(
% 2.77/0.78    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 2.77/0.78    inference(cnf_transformation,[],[f29])).
% 2.77/0.78  fof(f29,plain,(
% 2.77/0.78    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.77/0.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f28])).
% 2.77/0.78  fof(f28,plain,(
% 2.77/0.78    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 2.77/0.78    introduced(choice_axiom,[])).
% 2.77/0.78  fof(f22,plain,(
% 2.77/0.78    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.77/0.78    inference(ennf_transformation,[],[f19])).
% 2.77/0.78  fof(f19,plain,(
% 2.77/0.78    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.77/0.78    inference(rectify,[],[f2])).
% 2.77/0.78  fof(f2,axiom,(
% 2.77/0.78    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.77/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.77/0.78  fof(f82,plain,(
% 2.77/0.78    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 2.77/0.78    inference(superposition,[],[f42,f37])).
% 2.77/0.78  fof(f37,plain,(
% 2.77/0.78    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.77/0.78    inference(cnf_transformation,[],[f9])).
% 2.77/0.78  fof(f9,axiom,(
% 2.77/0.78    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 2.77/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 2.77/0.78  fof(f2064,plain,(
% 2.77/0.78    r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1),k1_xboole_0) | (spl3_3 | ~spl3_6)),
% 2.77/0.78    inference(backward_demodulation,[],[f276,f2051])).
% 2.77/0.78  fof(f2051,plain,(
% 2.77/0.78    k1_xboole_0 = k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) | spl3_3),
% 2.77/0.78    inference(unit_resulting_resolution,[],[f94,f1695,f65])).
% 2.77/0.78  fof(f65,plain,(
% 2.77/0.78    ( ! [X0,X1] : (~r1_tarski(X0,k1_enumset1(X1,X1,X1)) | k1_xboole_0 = X0 | k1_enumset1(X1,X1,X1) = X0) )),
% 2.77/0.78    inference(definition_unfolding,[],[f53,f39,f39])).
% 2.77/0.78  fof(f39,plain,(
% 2.77/0.78    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 2.77/0.78    inference(cnf_transformation,[],[f15])).
% 2.77/0.78  fof(f15,axiom,(
% 2.77/0.78    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0)),
% 2.77/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).
% 2.77/0.78  fof(f53,plain,(
% 2.77/0.78    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 2.77/0.78    inference(cnf_transformation,[],[f34])).
% 2.77/0.78  fof(f34,plain,(
% 2.77/0.78    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.77/0.78    inference(flattening,[],[f33])).
% 2.77/0.78  fof(f33,plain,(
% 2.77/0.78    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.77/0.78    inference(nnf_transformation,[],[f16])).
% 2.77/0.78  fof(f16,axiom,(
% 2.77/0.78    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.77/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).
% 2.77/0.78  fof(f1695,plain,(
% 2.77/0.78    ( ! [X6,X7] : (r1_tarski(k3_xboole_0(X6,X7),X6)) )),
% 2.77/0.78    inference(forward_demodulation,[],[f1684,f163])).
% 2.77/0.78  fof(f163,plain,(
% 2.77/0.78    ( ! [X2] : (k5_xboole_0(X2,k1_xboole_0) = X2) )),
% 2.77/0.78    inference(forward_demodulation,[],[f162,f38])).
% 2.77/0.78  fof(f162,plain,(
% 2.77/0.78    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k1_xboole_0)) )),
% 2.77/0.78    inference(forward_demodulation,[],[f155,f37])).
% 2.77/0.78  fof(f155,plain,(
% 2.77/0.78    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k4_xboole_0(k1_xboole_0,X2))) )),
% 2.77/0.78    inference(superposition,[],[f62,f38])).
% 2.77/0.78  fof(f62,plain,(
% 2.77/0.78    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) )),
% 2.77/0.78    inference(definition_unfolding,[],[f44,f43])).
% 2.77/0.78  fof(f43,plain,(
% 2.77/0.78    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.77/0.78    inference(cnf_transformation,[],[f14])).
% 2.77/0.78  fof(f14,axiom,(
% 2.77/0.78    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.77/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.77/0.78  fof(f44,plain,(
% 2.77/0.78    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 2.77/0.78    inference(cnf_transformation,[],[f7])).
% 2.77/0.78  fof(f7,axiom,(
% 2.77/0.78    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 2.77/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 2.77/0.78  fof(f1684,plain,(
% 2.77/0.78    ( ! [X6,X7] : (r1_tarski(k3_xboole_0(X6,X7),k5_xboole_0(X6,k1_xboole_0))) )),
% 2.77/0.78    inference(superposition,[],[f216,f316])).
% 2.77/0.78  fof(f316,plain,(
% 2.77/0.78    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.77/0.78    inference(unit_resulting_resolution,[],[f141,f119])).
% 2.77/0.78  fof(f119,plain,(
% 2.77/0.78    ( ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X0) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.77/0.78    inference(resolution,[],[f59,f41])).
% 2.77/0.78  fof(f141,plain,(
% 2.77/0.78    ( ! [X10,X11,X9] : (r1_xboole_0(k3_xboole_0(X9,k4_xboole_0(X10,X11)),X11)) )),
% 2.77/0.78    inference(superposition,[],[f42,f56])).
% 2.77/0.78  fof(f56,plain,(
% 2.77/0.78    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 2.77/0.78    inference(cnf_transformation,[],[f8])).
% 2.77/0.78  fof(f8,axiom,(
% 2.77/0.78    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 2.77/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 2.77/0.78  fof(f216,plain,(
% 2.77/0.78    ( ! [X2,X3,X1] : (r1_tarski(k3_xboole_0(X1,X2),k5_xboole_0(X3,k3_xboole_0(X1,k4_xboole_0(X2,X3))))) )),
% 2.77/0.78    inference(superposition,[],[f132,f56])).
% 2.77/0.78  fof(f132,plain,(
% 2.77/0.78    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) )),
% 2.77/0.78    inference(unit_resulting_resolution,[],[f68,f66])).
% 2.77/0.78  fof(f66,plain,(
% 2.77/0.78    ( ! [X2,X0,X1] : (r1_tarski(X0,k5_xboole_0(X2,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X1)) )),
% 2.77/0.78    inference(definition_unfolding,[],[f58,f43])).
% 2.77/0.78  fof(f58,plain,(
% 2.77/0.78    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.77/0.78    inference(cnf_transformation,[],[f24])).
% 2.77/0.78  fof(f24,plain,(
% 2.77/0.78    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.77/0.78    inference(ennf_transformation,[],[f4])).
% 2.77/0.78  fof(f4,axiom,(
% 2.77/0.78    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 2.77/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 2.77/0.78  fof(f68,plain,(
% 2.77/0.78    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.77/0.78    inference(equality_resolution,[],[f49])).
% 2.77/0.78  fof(f49,plain,(
% 2.77/0.78    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.77/0.78    inference(cnf_transformation,[],[f31])).
% 2.77/0.78  fof(f31,plain,(
% 2.77/0.78    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.77/0.78    inference(flattening,[],[f30])).
% 2.77/0.78  fof(f30,plain,(
% 2.77/0.78    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.77/0.78    inference(nnf_transformation,[],[f3])).
% 2.77/0.78  fof(f3,axiom,(
% 2.77/0.78    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.77/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.77/0.78  fof(f94,plain,(
% 2.77/0.78    k1_enumset1(sK0,sK0,sK0) != k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) | spl3_3),
% 2.77/0.78    inference(avatar_component_clause,[],[f92])).
% 2.77/0.78  fof(f92,plain,(
% 2.77/0.78    spl3_3 <=> k1_enumset1(sK0,sK0,sK0) = k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)),
% 2.77/0.78    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.77/0.78  fof(f276,plain,(
% 2.77/0.78    r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)) | ~spl3_6),
% 2.77/0.78    inference(avatar_component_clause,[],[f274])).
% 2.77/0.78  fof(f274,plain,(
% 2.77/0.78    spl3_6 <=> r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1))),
% 2.77/0.78    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 2.77/0.78  fof(f277,plain,(
% 2.77/0.78    spl3_6 | spl3_2),
% 2.77/0.78    inference(avatar_split_clause,[],[f125,f78,f274])).
% 2.77/0.78  fof(f78,plain,(
% 2.77/0.78    spl3_2 <=> r1_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)),
% 2.77/0.78    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.77/0.78  fof(f125,plain,(
% 2.77/0.78    r2_hidden(sK2(k1_enumset1(sK0,sK0,sK0),sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)) | spl3_2),
% 2.77/0.78    inference(unit_resulting_resolution,[],[f80,f45])).
% 2.77/0.78  fof(f45,plain,(
% 2.77/0.78    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 2.77/0.78    inference(cnf_transformation,[],[f29])).
% 2.77/0.78  fof(f80,plain,(
% 2.77/0.78    ~r1_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) | spl3_2),
% 2.77/0.78    inference(avatar_component_clause,[],[f78])).
% 2.77/0.78  fof(f95,plain,(
% 2.77/0.78    ~spl3_3),
% 2.77/0.78    inference(avatar_split_clause,[],[f60,f92])).
% 2.77/0.78  fof(f60,plain,(
% 2.77/0.78    k1_enumset1(sK0,sK0,sK0) != k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)),
% 2.77/0.78    inference(definition_unfolding,[],[f36,f39,f39])).
% 2.77/0.78  fof(f36,plain,(
% 2.77/0.78    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)),
% 2.77/0.78    inference(cnf_transformation,[],[f27])).
% 2.77/0.78  fof(f27,plain,(
% 2.77/0.78    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) & ~r1_xboole_0(k1_tarski(sK0),sK1)),
% 2.77/0.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f26])).
% 2.77/0.78  fof(f26,plain,(
% 2.77/0.78    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1) & ~r1_xboole_0(k1_tarski(X0),X1)) => (k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) & ~r1_xboole_0(k1_tarski(sK0),sK1))),
% 2.77/0.78    introduced(choice_axiom,[])).
% 2.77/0.78  fof(f20,plain,(
% 2.77/0.78    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1) & ~r1_xboole_0(k1_tarski(X0),X1))),
% 2.77/0.78    inference(ennf_transformation,[],[f18])).
% 2.77/0.78  fof(f18,negated_conjecture,(
% 2.77/0.78    ~! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1))),
% 2.77/0.78    inference(negated_conjecture,[],[f17])).
% 2.77/0.78  fof(f17,conjecture,(
% 2.77/0.78    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1))),
% 2.77/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_zfmisc_1)).
% 2.77/0.78  fof(f81,plain,(
% 2.77/0.78    ~spl3_2),
% 2.77/0.78    inference(avatar_split_clause,[],[f61,f78])).
% 2.77/0.78  fof(f61,plain,(
% 2.77/0.78    ~r1_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)),
% 2.77/0.78    inference(definition_unfolding,[],[f35,f39])).
% 2.77/0.78  fof(f35,plain,(
% 2.77/0.78    ~r1_xboole_0(k1_tarski(sK0),sK1)),
% 2.77/0.78    inference(cnf_transformation,[],[f27])).
% 2.77/0.78  % SZS output end Proof for theBenchmark
% 2.77/0.78  % (13340)------------------------------
% 2.77/0.78  % (13340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.77/0.78  % (13340)Termination reason: Refutation
% 2.77/0.78  
% 2.77/0.78  % (13340)Memory used [KB]: 12281
% 2.77/0.78  % (13340)Time elapsed: 0.341 s
% 2.77/0.78  % (13340)------------------------------
% 2.77/0.78  % (13340)------------------------------
% 2.77/0.79  % (13319)Success in time 0.422 s
%------------------------------------------------------------------------------
