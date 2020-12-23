%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:42 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   64 (  90 expanded)
%              Number of leaves         :   16 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :  241 ( 323 expanded)
%              Number of equality atoms :  122 ( 166 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f447,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f64,f69,f433,f441,f446])).

fof(f446,plain,
    ( spl6_1
    | spl6_2
    | ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f442])).

fof(f442,plain,
    ( $false
    | spl6_1
    | spl6_2
    | ~ spl6_5 ),
    inference(unit_resulting_resolution,[],[f63,f58,f440,f51])).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK3(X0,X1,X2) != X1
              & sK3(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( sK3(X0,X1,X2) = X1
            | sK3(X0,X1,X2) = X0
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK3(X0,X1,X2) != X1
            & sK3(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( sK3(X0,X1,X2) = X1
          | sK3(X0,X1,X2) = X0
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f15])).

% (13931)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% (13942)Refutation not found, incomplete strategy% (13942)------------------------------
% (13942)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (13942)Termination reason: Refutation not found, incomplete strategy

% (13942)Memory used [KB]: 1663
% (13942)Time elapsed: 0.117 s
% (13942)------------------------------
% (13942)------------------------------
fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f440,plain,
    ( r2_hidden(sK0,k2_tarski(sK1,sK2))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f438])).

fof(f438,plain,
    ( spl6_5
  <=> r2_hidden(sK0,k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f58,plain,
    ( sK0 != sK1
    | spl6_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl6_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f63,plain,
    ( sK0 != sK2
    | spl6_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl6_2
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f441,plain,
    ( spl6_5
    | spl6_4 ),
    inference(avatar_split_clause,[],[f435,f430,f438])).

fof(f430,plain,
    ( spl6_4
  <=> r1_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f435,plain,
    ( r2_hidden(sK0,k2_tarski(sK1,sK2))
    | spl6_4 ),
    inference(resolution,[],[f432,f103])).

fof(f103,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(X2,k1_tarski(X3))
      | r2_hidden(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,(
    ! [X2,X3] :
      ( r2_hidden(X3,X2)
      | r1_xboole_0(X2,k1_tarski(X3))
      | r1_xboole_0(X2,k1_tarski(X3)) ) ),
    inference(superposition,[],[f42,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( sK5(X0,k1_tarski(X1)) = X1
      | r1_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(resolution,[],[f43,f54])).

fof(f54,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f20,plain,(
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

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f12,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f432,plain,
    ( ~ r1_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))
    | spl6_4 ),
    inference(avatar_component_clause,[],[f430])).

fof(f433,plain,
    ( ~ spl6_4
    | spl6_3 ),
    inference(avatar_split_clause,[],[f428,f66,f430])).

fof(f66,plain,
    ( spl6_3
  <=> k2_tarski(sK1,sK2) = k4_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f428,plain,
    ( ~ r1_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))
    | spl6_3 ),
    inference(trivial_inequality_removal,[],[f425])).

fof(f425,plain,
    ( k2_tarski(sK1,sK2) != k2_tarski(sK1,sK2)
    | ~ r1_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))
    | spl6_3 ),
    inference(superposition,[],[f68,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_xboole_0(k2_tarski(X2,X0),k1_tarski(X1)),k1_tarski(X2))
      | ~ r1_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(superposition,[],[f36,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0)) ),
    inference(definition_unfolding,[],[f41,f35,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

fof(f68,plain,
    ( k2_tarski(sK1,sK2) != k4_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)),k1_tarski(sK0))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f69,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f45,f66])).

fof(f45,plain,(
    k2_tarski(sK1,sK2) != k4_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)),k1_tarski(sK0)) ),
    inference(definition_unfolding,[],[f28,f35])).

fof(f28,plain,(
    k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0)) != k2_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0)) != k2_tarski(sK1,sK2)
    & sK0 != sK2
    & sK0 != sK1 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
        & X0 != X2
        & X0 != X1 )
   => ( k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0)) != k2_tarski(sK1,sK2)
      & sK0 != sK2
      & sK0 != sK1 ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
      & X0 != X2
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
          & X0 != X2
          & X0 != X1 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
        & X0 != X2
        & X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t136_enumset1)).

fof(f64,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f27,f61])).

fof(f27,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f14])).

fof(f59,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f26,f56])).

fof(f26,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n021.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:40:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (13951)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.50  % (13943)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.50  % (13935)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.51  % (13942)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.52  % (13928)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (13932)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (13936)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.52  % (13934)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (13951)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f447,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f59,f64,f69,f433,f441,f446])).
% 0.22/0.53  fof(f446,plain,(
% 0.22/0.53    spl6_1 | spl6_2 | ~spl6_5),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f442])).
% 0.22/0.53  fof(f442,plain,(
% 0.22/0.53    $false | (spl6_1 | spl6_2 | ~spl6_5)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f63,f58,f440,f51])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_tarski(X0,X1)) | X0 = X4 | X1 = X4) )),
% 0.22/0.53    inference(equality_resolution,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.22/0.53    inference(rectify,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.22/0.53    inference(flattening,[],[f15])).
% 0.22/0.53  % (13931)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.53  % (13942)Refutation not found, incomplete strategy% (13942)------------------------------
% 0.22/0.53  % (13942)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (13942)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (13942)Memory used [KB]: 1663
% 0.22/0.53  % (13942)Time elapsed: 0.117 s
% 0.22/0.53  % (13942)------------------------------
% 0.22/0.53  % (13942)------------------------------
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.22/0.53    inference(nnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.22/0.53  fof(f440,plain,(
% 0.22/0.53    r2_hidden(sK0,k2_tarski(sK1,sK2)) | ~spl6_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f438])).
% 0.22/0.53  fof(f438,plain,(
% 0.22/0.53    spl6_5 <=> r2_hidden(sK0,k2_tarski(sK1,sK2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    sK0 != sK1 | spl6_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f56])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    spl6_1 <=> sK0 = sK1),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    sK0 != sK2 | spl6_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f61])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    spl6_2 <=> sK0 = sK2),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.53  fof(f441,plain,(
% 0.22/0.53    spl6_5 | spl6_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f435,f430,f438])).
% 0.22/0.53  fof(f430,plain,(
% 0.22/0.53    spl6_4 <=> r1_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.53  fof(f435,plain,(
% 0.22/0.53    r2_hidden(sK0,k2_tarski(sK1,sK2)) | spl6_4),
% 0.22/0.53    inference(resolution,[],[f432,f103])).
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    ( ! [X2,X3] : (r1_xboole_0(X2,k1_tarski(X3)) | r2_hidden(X3,X2)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f100])).
% 0.22/0.53  fof(f100,plain,(
% 0.22/0.53    ( ! [X2,X3] : (r2_hidden(X3,X2) | r1_xboole_0(X2,k1_tarski(X3)) | r1_xboole_0(X2,k1_tarski(X3))) )),
% 0.22/0.53    inference(superposition,[],[f42,f72])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sK5(X0,k1_tarski(X1)) = X1 | r1_xboole_0(X0,k1_tarski(X1))) )),
% 0.22/0.53    inference(resolution,[],[f43,f54])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.22/0.53    inference(equality_resolution,[],[f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.53    inference(rectify,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f12,f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,plain,(
% 0.22/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.53    inference(rectify,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f432,plain,(
% 0.22/0.53    ~r1_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0)) | spl6_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f430])).
% 0.22/0.53  fof(f433,plain,(
% 0.22/0.53    ~spl6_4 | spl6_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f428,f66,f430])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    spl6_3 <=> k2_tarski(sK1,sK2) = k4_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)),k1_tarski(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.53  fof(f428,plain,(
% 0.22/0.53    ~r1_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0)) | spl6_3),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f425])).
% 0.22/0.53  fof(f425,plain,(
% 0.22/0.53    k2_tarski(sK1,sK2) != k2_tarski(sK1,sK2) | ~r1_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0)) | spl6_3),
% 0.22/0.53    inference(superposition,[],[f68,f111])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = k4_xboole_0(k2_xboole_0(k2_tarski(X2,X0),k1_tarski(X1)),k1_tarski(X2)) | ~r1_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.22/0.53    inference(superposition,[],[f36,f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f41,f35,f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    k2_tarski(sK1,sK2) != k4_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)),k1_tarski(sK0)) | spl6_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f66])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    ~spl6_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f45,f66])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    k2_tarski(sK1,sK2) != k4_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)),k1_tarski(sK0))),
% 0.22/0.53    inference(definition_unfolding,[],[f28,f35])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0)) != k2_tarski(sK1,sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0)) != k2_tarski(sK1,sK2) & sK0 != sK2 & sK0 != sK1),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ? [X0,X1,X2] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2) & X0 != X2 & X0 != X1) => (k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0)) != k2_tarski(sK1,sK2) & sK0 != sK2 & sK0 != sK1)),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    ? [X0,X1,X2] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2) & X0 != X2 & X0 != X1)),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1,X2] : ~(k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2) & X0 != X2 & X0 != X1)),
% 0.22/0.53    inference(negated_conjecture,[],[f7])).
% 0.22/0.53  fof(f7,conjecture,(
% 0.22/0.53    ! [X0,X1,X2] : ~(k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2) & X0 != X2 & X0 != X1)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t136_enumset1)).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ~spl6_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f27,f61])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    sK0 != sK2),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ~spl6_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f26,f56])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    sK0 != sK1),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (13951)------------------------------
% 0.22/0.53  % (13951)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (13951)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (13951)Memory used [KB]: 11001
% 0.22/0.53  % (13951)Time elapsed: 0.072 s
% 0.22/0.53  % (13951)------------------------------
% 0.22/0.53  % (13951)------------------------------
% 0.22/0.54  % (13927)Success in time 0.172 s
%------------------------------------------------------------------------------
