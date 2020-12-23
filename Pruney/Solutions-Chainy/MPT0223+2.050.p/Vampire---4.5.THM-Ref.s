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
% DateTime   : Thu Dec  3 12:35:57 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 112 expanded)
%              Number of leaves         :   17 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :  248 ( 308 expanded)
%              Number of equality atoms :  137 ( 186 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f118,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f83,f92,f100,f106,f117])).

fof(f117,plain,(
    ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f65,f91])).

fof(f91,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl5_4
  <=> ! [X0] : ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f65,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f33,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f33,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK2(X0,X1,X2,X3) != X2
              & sK2(X0,X1,X2,X3) != X1
              & sK2(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
          & ( sK2(X0,X1,X2,X3) = X2
            | sK2(X0,X1,X2,X3) = X1
            | sK2(X0,X1,X2,X3) = X0
            | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f20])).

fof(f20,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK2(X0,X1,X2,X3) != X2
            & sK2(X0,X1,X2,X3) != X1
            & sK2(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
        & ( sK2(X0,X1,X2,X3) = X2
          | sK2(X0,X1,X2,X3) = X1
          | sK2(X0,X1,X2,X3) = X0
          | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f106,plain,
    ( spl5_1
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | spl5_1
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f77,f99,f73])).

fof(f73,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f38,f49])).

fof(f49,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f42,f47])).

fof(f42,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f43,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f99,plain,
    ( r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl5_5
  <=> r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f77,plain,
    ( sK0 != sK1
    | spl5_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl5_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f100,plain,
    ( spl5_5
    | spl5_3 ),
    inference(avatar_split_clause,[],[f95,f86,f97])).

fof(f86,plain,
    ( spl5_3
  <=> r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f95,plain,
    ( r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | spl5_3 ),
    inference(resolution,[],[f63,f88])).

fof(f88,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f49])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f92,plain,
    ( ~ spl5_3
    | spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f84,f80,f90,f86])).

fof(f80,plain,
    ( spl5_2
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f84,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
        | ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) )
    | ~ spl5_2 ),
    inference(superposition,[],[f45,f82])).

fof(f82,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

% (8196)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f83,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f50,f80])).

fof(f50,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f28,f49,f49,f49])).

fof(f28,plain,(
    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( sK0 != sK1
    & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

fof(f78,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f29,f75])).

fof(f29,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:53:32 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.32/0.55  % (8204)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.32/0.55  % (8212)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.32/0.56  % (8212)Refutation found. Thanks to Tanya!
% 1.32/0.56  % SZS status Theorem for theBenchmark
% 1.55/0.56  % SZS output start Proof for theBenchmark
% 1.55/0.56  fof(f118,plain,(
% 1.55/0.56    $false),
% 1.55/0.56    inference(avatar_sat_refutation,[],[f78,f83,f92,f100,f106,f117])).
% 1.55/0.56  fof(f117,plain,(
% 1.55/0.56    ~spl5_4),
% 1.55/0.56    inference(avatar_contradiction_clause,[],[f110])).
% 1.55/0.56  fof(f110,plain,(
% 1.55/0.56    $false | ~spl5_4),
% 1.55/0.56    inference(unit_resulting_resolution,[],[f65,f91])).
% 1.55/0.56  fof(f91,plain,(
% 1.55/0.56    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))) ) | ~spl5_4),
% 1.55/0.56    inference(avatar_component_clause,[],[f90])).
% 1.55/0.56  fof(f90,plain,(
% 1.55/0.56    spl5_4 <=> ! [X0] : ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.55/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.55/0.56  fof(f65,plain,(
% 1.55/0.56    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 1.55/0.56    inference(equality_resolution,[],[f64])).
% 1.55/0.56  fof(f64,plain,(
% 1.55/0.56    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 1.55/0.56    inference(equality_resolution,[],[f55])).
% 1.55/0.56  fof(f55,plain,(
% 1.55/0.56    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.55/0.56    inference(definition_unfolding,[],[f33,f47])).
% 1.55/0.56  fof(f47,plain,(
% 1.55/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f6])).
% 1.55/0.56  fof(f6,axiom,(
% 1.55/0.56    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.55/0.56  fof(f33,plain,(
% 1.55/0.56    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.55/0.56    inference(cnf_transformation,[],[f21])).
% 1.55/0.56  fof(f21,plain,(
% 1.55/0.56    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.55/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f20])).
% 1.55/0.56  fof(f20,plain,(
% 1.55/0.56    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 1.55/0.56    introduced(choice_axiom,[])).
% 1.55/0.56  fof(f19,plain,(
% 1.55/0.56    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.55/0.56    inference(rectify,[],[f18])).
% 1.55/0.56  fof(f18,plain,(
% 1.55/0.56    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.55/0.56    inference(flattening,[],[f17])).
% 1.55/0.56  fof(f17,plain,(
% 1.55/0.56    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.55/0.56    inference(nnf_transformation,[],[f12])).
% 1.55/0.56  fof(f12,plain,(
% 1.55/0.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.55/0.56    inference(ennf_transformation,[],[f2])).
% 1.55/0.56  fof(f2,axiom,(
% 1.55/0.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.55/0.56  fof(f106,plain,(
% 1.55/0.56    spl5_1 | ~spl5_5),
% 1.55/0.56    inference(avatar_contradiction_clause,[],[f101])).
% 1.55/0.56  fof(f101,plain,(
% 1.55/0.56    $false | (spl5_1 | ~spl5_5)),
% 1.55/0.56    inference(unit_resulting_resolution,[],[f77,f99,f73])).
% 1.55/0.56  fof(f73,plain,(
% 1.55/0.56    ( ! [X0,X3] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) | X0 = X3) )),
% 1.55/0.56    inference(equality_resolution,[],[f62])).
% 1.55/0.56  fof(f62,plain,(
% 1.55/0.56    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.55/0.56    inference(definition_unfolding,[],[f38,f49])).
% 1.55/0.56  fof(f49,plain,(
% 1.55/0.56    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.55/0.56    inference(definition_unfolding,[],[f43,f48])).
% 1.55/0.56  fof(f48,plain,(
% 1.55/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.55/0.56    inference(definition_unfolding,[],[f42,f47])).
% 1.55/0.56  fof(f42,plain,(
% 1.55/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f5])).
% 1.55/0.56  fof(f5,axiom,(
% 1.55/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.55/0.56  fof(f43,plain,(
% 1.55/0.56    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f4])).
% 1.55/0.56  fof(f4,axiom,(
% 1.55/0.56    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.55/0.56  fof(f38,plain,(
% 1.55/0.56    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.55/0.56    inference(cnf_transformation,[],[f25])).
% 1.55/0.56  fof(f25,plain,(
% 1.55/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.55/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).
% 1.55/0.56  fof(f24,plain,(
% 1.55/0.56    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 1.55/0.56    introduced(choice_axiom,[])).
% 1.55/0.56  fof(f23,plain,(
% 1.55/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.55/0.56    inference(rectify,[],[f22])).
% 1.55/0.56  fof(f22,plain,(
% 1.55/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.55/0.56    inference(nnf_transformation,[],[f3])).
% 1.55/0.56  fof(f3,axiom,(
% 1.55/0.56    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.55/0.56  fof(f99,plain,(
% 1.55/0.56    r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl5_5),
% 1.55/0.56    inference(avatar_component_clause,[],[f97])).
% 1.55/0.56  fof(f97,plain,(
% 1.55/0.56    spl5_5 <=> r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.55/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.55/0.56  fof(f77,plain,(
% 1.55/0.56    sK0 != sK1 | spl5_1),
% 1.55/0.56    inference(avatar_component_clause,[],[f75])).
% 1.55/0.56  fof(f75,plain,(
% 1.55/0.56    spl5_1 <=> sK0 = sK1),
% 1.55/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.55/0.56  fof(f100,plain,(
% 1.55/0.56    spl5_5 | spl5_3),
% 1.55/0.56    inference(avatar_split_clause,[],[f95,f86,f97])).
% 1.55/0.56  fof(f86,plain,(
% 1.55/0.56    spl5_3 <=> r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.55/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.55/0.56  fof(f95,plain,(
% 1.55/0.56    r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | spl5_3),
% 1.55/0.56    inference(resolution,[],[f63,f88])).
% 1.55/0.56  fof(f88,plain,(
% 1.55/0.56    ~r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | spl5_3),
% 1.55/0.56    inference(avatar_component_clause,[],[f86])).
% 1.55/0.56  fof(f63,plain,(
% 1.55/0.56    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.55/0.56    inference(definition_unfolding,[],[f46,f49])).
% 1.55/0.56  fof(f46,plain,(
% 1.55/0.56    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f14])).
% 1.55/0.56  fof(f14,plain,(
% 1.55/0.56    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.55/0.56    inference(ennf_transformation,[],[f7])).
% 1.55/0.56  fof(f7,axiom,(
% 1.55/0.56    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.55/0.56  fof(f92,plain,(
% 1.55/0.56    ~spl5_3 | spl5_4 | ~spl5_2),
% 1.55/0.56    inference(avatar_split_clause,[],[f84,f80,f90,f86])).
% 1.55/0.56  fof(f80,plain,(
% 1.55/0.56    spl5_2 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.55/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.55/0.56  fof(f84,plain,(
% 1.55/0.56    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))) ) | ~spl5_2),
% 1.55/0.56    inference(superposition,[],[f45,f82])).
% 1.55/0.56  fof(f82,plain,(
% 1.55/0.56    k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl5_2),
% 1.55/0.56    inference(avatar_component_clause,[],[f80])).
% 1.55/0.56  fof(f45,plain,(
% 1.55/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f27])).
% 1.55/0.56  % (8196)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.55/0.56  fof(f27,plain,(
% 1.55/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.55/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f26])).
% 1.55/0.56  fof(f26,plain,(
% 1.55/0.56    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 1.55/0.56    introduced(choice_axiom,[])).
% 1.55/0.56  fof(f13,plain,(
% 1.55/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.55/0.56    inference(ennf_transformation,[],[f10])).
% 1.55/0.56  fof(f10,plain,(
% 1.55/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.55/0.56    inference(rectify,[],[f1])).
% 1.55/0.56  fof(f1,axiom,(
% 1.55/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.55/0.56  fof(f83,plain,(
% 1.55/0.56    spl5_2),
% 1.55/0.56    inference(avatar_split_clause,[],[f50,f80])).
% 1.55/0.56  fof(f50,plain,(
% 1.55/0.56    k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.55/0.56    inference(definition_unfolding,[],[f28,f49,f49,f49])).
% 1.55/0.56  fof(f28,plain,(
% 1.55/0.56    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.55/0.56    inference(cnf_transformation,[],[f16])).
% 1.55/0.56  fof(f16,plain,(
% 1.55/0.56    sK0 != sK1 & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.55/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f15])).
% 1.55/0.56  fof(f15,plain,(
% 1.55/0.56    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.55/0.56    introduced(choice_axiom,[])).
% 1.55/0.56  fof(f11,plain,(
% 1.55/0.56    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.55/0.56    inference(ennf_transformation,[],[f9])).
% 1.55/0.56  fof(f9,negated_conjecture,(
% 1.55/0.56    ~! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.55/0.56    inference(negated_conjecture,[],[f8])).
% 1.55/0.56  fof(f8,conjecture,(
% 1.55/0.56    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).
% 1.55/0.56  fof(f78,plain,(
% 1.55/0.56    ~spl5_1),
% 1.55/0.56    inference(avatar_split_clause,[],[f29,f75])).
% 1.55/0.56  fof(f29,plain,(
% 1.55/0.56    sK0 != sK1),
% 1.55/0.56    inference(cnf_transformation,[],[f16])).
% 1.55/0.56  % SZS output end Proof for theBenchmark
% 1.55/0.56  % (8212)------------------------------
% 1.55/0.56  % (8212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.56  % (8212)Termination reason: Refutation
% 1.55/0.56  
% 1.55/0.56  % (8212)Memory used [KB]: 10746
% 1.55/0.56  % (8212)Time elapsed: 0.084 s
% 1.55/0.56  % (8212)------------------------------
% 1.55/0.56  % (8212)------------------------------
% 1.55/0.57  % (8188)Success in time 0.206 s
%------------------------------------------------------------------------------
