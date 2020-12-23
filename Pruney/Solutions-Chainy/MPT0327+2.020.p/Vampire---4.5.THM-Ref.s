%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 248 expanded)
%              Number of leaves         :   18 (  89 expanded)
%              Depth                    :   12
%              Number of atoms          :  135 ( 333 expanded)
%              Number of equality atoms :   57 ( 232 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f162,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f63,f82,f89,f148,f157,f161])).

fof(f161,plain,
    ( ~ spl2_1
    | spl2_8 ),
    inference(avatar_contradiction_clause,[],[f159])).

fof(f159,plain,
    ( $false
    | ~ spl2_1
    | spl2_8 ),
    inference(unit_resulting_resolution,[],[f52,f156,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f40])).

fof(f40,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f29,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f156,plain,
    ( ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | spl2_8 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl2_8
  <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f52,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl2_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f157,plain,
    ( ~ spl2_8
    | spl2_7 ),
    inference(avatar_split_clause,[],[f152,f144,f154])).

fof(f144,plain,
    ( spl2_7
  <=> sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f152,plain,
    ( ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | spl2_7 ),
    inference(trivial_inequality_removal,[],[f151])).

fof(f151,plain,
    ( sK1 != sK1
    | ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | spl2_7 ),
    inference(forward_demodulation,[],[f150,f112])).

fof(f112,plain,(
    ! [X4] : k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X4)) = X4 ),
    inference(superposition,[],[f107,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f25,f39,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f36,f38])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f107,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(global_subsumption,[],[f47,f90])).

fof(f90,plain,(
    ! [X0] :
      ( k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0
      | ~ r1_tarski(X0,X0) ) ),
    inference(superposition,[],[f76,f44])).

fof(f44,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f26,f39])).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f76,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_enumset1(X1,X1,X1,X0)) = k3_tarski(k2_enumset1(X1,X1,X1,k1_xboole_0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f42,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f42,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f24,f39,f39])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f47,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f150,plain,
    ( sK1 != k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1))
    | ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | spl2_7 ),
    inference(forward_demodulation,[],[f149,f43])).

fof(f149,plain,
    ( sK1 != k3_tarski(k2_enumset1(sK1,sK1,sK1,k1_xboole_0))
    | ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | spl2_7 ),
    inference(superposition,[],[f146,f76])).

fof(f146,plain,
    ( sK1 != k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | spl2_7 ),
    inference(avatar_component_clause,[],[f144])).

fof(f148,plain,
    ( ~ spl2_7
    | spl2_6 ),
    inference(avatar_split_clause,[],[f142,f86,f144])).

fof(f86,plain,
    ( spl2_6
  <=> sK1 = k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f142,plain,
    ( sK1 != k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | spl2_6 ),
    inference(superposition,[],[f88,f43])).

fof(f88,plain,
    ( sK1 != k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f89,plain,
    ( ~ spl2_6
    | spl2_5 ),
    inference(avatar_split_clause,[],[f84,f78,f86])).

% (24123)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
fof(f78,plain,
    ( spl2_5
  <=> sK1 = k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f84,plain,
    ( sK1 != k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | spl2_5 ),
    inference(superposition,[],[f80,f42])).

fof(f80,plain,
    ( sK1 != k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f82,plain,
    ( ~ spl2_5
    | spl2_2 ),
    inference(avatar_split_clause,[],[f75,f60,f78])).

fof(f60,plain,
    ( spl2_2
  <=> sK1 = k3_tarski(k2_enumset1(k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f75,plain,
    ( sK1 != k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
    | spl2_2 ),
    inference(superposition,[],[f62,f43])).

fof(f62,plain,
    ( sK1 != k3_tarski(k2_enumset1(k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f63,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f41,f60])).

fof(f41,plain,(
    sK1 != k3_tarski(k2_enumset1(k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(definition_unfolding,[],[f23,f39,f40,f40])).

fof(f23,plain,(
    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

fof(f53,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f22,f50])).

fof(f22,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:36:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (24113)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.49  % (24136)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.49  % (24128)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.50  % (24120)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.50  % (24136)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (24132)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f162,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f53,f63,f82,f89,f148,f157,f161])).
% 0.21/0.52  fof(f161,plain,(
% 0.21/0.52    ~spl2_1 | spl2_8),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f159])).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    $false | (~spl2_1 | spl2_8)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f52,f156,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f28,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f29,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f35,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.21/0.52    inference(nnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    ~r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | spl2_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f154])).
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    spl2_8 <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    r2_hidden(sK0,sK1) | ~spl2_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    spl2_1 <=> r2_hidden(sK0,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.52  fof(f157,plain,(
% 0.21/0.52    ~spl2_8 | spl2_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f152,f144,f154])).
% 0.21/0.52  fof(f144,plain,(
% 0.21/0.52    spl2_7 <=> sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    ~r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | spl2_7),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f151])).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    sK1 != sK1 | ~r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | spl2_7),
% 0.21/0.52    inference(forward_demodulation,[],[f150,f112])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    ( ! [X4] : (k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X4)) = X4) )),
% 0.21/0.52    inference(superposition,[],[f107,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X1,X1,X1,X0))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f25,f39,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f36,f38])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0) )),
% 0.21/0.52    inference(global_subsumption,[],[f47,f90])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0 | ~r1_tarski(X0,X0)) )),
% 0.21/0.52    inference(superposition,[],[f76,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f26,f39])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.52    inference(rectify,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X1,X1,X1,X0)) = k3_tarski(k2_enumset1(X1,X1,X1,k1_xboole_0)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(superposition,[],[f42,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.52    inference(nnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X1,X0)))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f24,f39,f39])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(flattening,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    sK1 != k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1)) | ~r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | spl2_7),
% 0.21/0.52    inference(forward_demodulation,[],[f149,f43])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    sK1 != k3_tarski(k2_enumset1(sK1,sK1,sK1,k1_xboole_0)) | ~r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | spl2_7),
% 0.21/0.52    inference(superposition,[],[f146,f76])).
% 0.21/0.52  fof(f146,plain,(
% 0.21/0.52    sK1 != k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | spl2_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f144])).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    ~spl2_7 | spl2_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f142,f86,f144])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    spl2_6 <=> sK1 = k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.52  fof(f142,plain,(
% 0.21/0.52    sK1 != k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | spl2_6),
% 0.21/0.52    inference(superposition,[],[f88,f43])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    sK1 != k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | spl2_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f86])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    ~spl2_6 | spl2_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f84,f78,f86])).
% 0.21/0.52  % (24123)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    spl2_5 <=> sK1 = k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    sK1 != k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | spl2_5),
% 0.21/0.52    inference(superposition,[],[f80,f42])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    sK1 != k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) | spl2_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f78])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    ~spl2_5 | spl2_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f75,f60,f78])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    spl2_2 <=> sK1 = k3_tarski(k2_enumset1(k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    sK1 != k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) | spl2_2),
% 0.21/0.52    inference(superposition,[],[f62,f43])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    sK1 != k3_tarski(k2_enumset1(k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))) | spl2_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f60])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ~spl2_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f41,f60])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    sK1 != k3_tarski(k2_enumset1(k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.21/0.52    inference(definition_unfolding,[],[f23,f39,f40,f40])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 0.21/0.52    inference(negated_conjecture,[],[f12])).
% 0.21/0.52  fof(f12,conjecture,(
% 0.21/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    spl2_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f22,f50])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    r2_hidden(sK0,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (24136)------------------------------
% 0.21/0.52  % (24136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (24136)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (24136)Memory used [KB]: 10746
% 0.21/0.52  % (24136)Time elapsed: 0.099 s
% 0.21/0.52  % (24136)------------------------------
% 0.21/0.52  % (24136)------------------------------
% 0.21/0.52  % (24110)Success in time 0.156 s
%------------------------------------------------------------------------------
