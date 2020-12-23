%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 109 expanded)
%              Number of leaves         :   14 (  32 expanded)
%              Depth                    :   15
%              Number of atoms          :  267 ( 451 expanded)
%              Number of equality atoms :  148 ( 273 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f187,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f73,f78,f171,f174,f186])).

fof(f186,plain,
    ( spl4_1
    | spl4_2
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | spl4_1
    | spl4_2
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f184,f67])).

fof(f67,plain,
    ( sK0 != sK2
    | spl4_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl4_1
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f184,plain,
    ( sK0 = sK2
    | spl4_2
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f179,f72])).

fof(f72,plain,
    ( sK0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl4_2
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f179,plain,
    ( sK0 = sK1
    | sK0 = sK2
    | ~ spl4_7 ),
    inference(resolution,[],[f154,f115])).

fof(f115,plain,
    ( r2_hidden(sK0,k2_tarski(sK1,sK2))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl4_7
  <=> r2_hidden(sK0,k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_tarski(X0,X1))
      | X0 = X2
      | X1 = X2 ) ),
    inference(duplicate_literal_removal,[],[f153])).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_tarski(X0,X1))
      | X0 = X2
      | X0 = X2
      | X1 = X2 ) ),
    inference(superposition,[],[f63,f35])).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f63,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k1_enumset1(X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK3(X0,X1,X2,X3) != X2
              & sK3(X0,X1,X2,X3) != X1
              & sK3(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( sK3(X0,X1,X2,X3) = X2
            | sK3(X0,X1,X2,X3) = X1
            | sK3(X0,X1,X2,X3) = X0
            | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).

fof(f27,plain,(
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
     => ( ( ( sK3(X0,X1,X2,X3) != X2
            & sK3(X0,X1,X2,X3) != X1
            & sK3(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( sK3(X0,X1,X2,X3) = X2
          | sK3(X0,X1,X2,X3) = X1
          | sK3(X0,X1,X2,X3) = X0
          | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f174,plain,
    ( spl4_6
    | spl4_7
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f172,f75,f113,f109])).

fof(f109,plain,
    ( spl4_6
  <=> k1_xboole_0 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f75,plain,
    ( spl4_3
  <=> r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f172,plain,
    ( r2_hidden(sK0,k2_tarski(sK1,sK2))
    | k1_xboole_0 = k1_tarski(sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f77,f99])).

fof(f99,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_tarski(X2),X3)
      | r2_hidden(X2,X3)
      | k1_xboole_0 = k1_tarski(X2) ) ),
    inference(superposition,[],[f97,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f97,plain,(
    ! [X2,X1] :
      ( k1_tarski(X1) = k4_xboole_0(k1_tarski(X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(forward_demodulation,[],[f56,f36])).

fof(f36,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f56,plain,(
    ! [X2,X1] :
      ( k1_tarski(X1) = k4_xboole_0(k2_tarski(X1,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | X0 != X1
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

fof(f77,plain,
    ( r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f171,plain,(
    ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f169,f54])).

fof(f54,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f169,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f165,f111])).

fof(f111,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f109])).

fof(f165,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski(sK0))
    | ~ spl4_6 ),
    inference(resolution,[],[f156,f82])).

fof(f82,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(superposition,[],[f79,f36])).

fof(f79,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f62,f35])).

fof(f62,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k1_enumset1(X5,X1,X2)) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f156,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,X0)
        | ~ r1_tarski(k1_xboole_0,X0) )
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f155])).

fof(f155,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | ~ r2_hidden(sK0,X0)
        | ~ r1_tarski(k1_xboole_0,X0) )
    | ~ spl4_6 ),
    inference(superposition,[],[f126,f38])).

fof(f126,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,X1)
        | ~ r2_hidden(sK0,X1) )
    | ~ spl4_6 ),
    inference(superposition,[],[f95,f111])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(superposition,[],[f39,f36])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f78,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f29,f75])).

fof(f29,plain,(
    r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( sK0 != sK2
    & sK0 != sK1
    & r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) )
   => ( sK0 != sK2
      & sK0 != sK1
      & r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & X0 != X1
      & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X2
          & X0 != X1
          & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

fof(f73,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f30,f70])).

fof(f30,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f18])).

fof(f68,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f31,f65])).

fof(f31,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:18:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.54  % (4152)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.54  % (4146)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.55  % (4152)Refutation not found, incomplete strategy% (4152)------------------------------
% 0.22/0.55  % (4152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (4152)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (4152)Memory used [KB]: 1663
% 0.22/0.55  % (4152)Time elapsed: 0.110 s
% 0.22/0.55  % (4152)------------------------------
% 0.22/0.55  % (4152)------------------------------
% 0.22/0.55  % (4146)Refutation not found, incomplete strategy% (4146)------------------------------
% 0.22/0.55  % (4146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (4146)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (4146)Memory used [KB]: 10618
% 0.22/0.55  % (4146)Time elapsed: 0.116 s
% 0.22/0.55  % (4146)------------------------------
% 0.22/0.55  % (4146)------------------------------
% 0.22/0.55  % (4144)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.55  % (4163)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (4144)Refutation not found, incomplete strategy% (4144)------------------------------
% 0.22/0.55  % (4144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (4144)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (4144)Memory used [KB]: 10746
% 0.22/0.55  % (4144)Time elapsed: 0.118 s
% 0.22/0.55  % (4144)------------------------------
% 0.22/0.55  % (4144)------------------------------
% 0.22/0.55  % (4163)Refutation not found, incomplete strategy% (4163)------------------------------
% 0.22/0.55  % (4163)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (4163)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (4163)Memory used [KB]: 1663
% 0.22/0.55  % (4163)Time elapsed: 0.125 s
% 0.22/0.55  % (4163)------------------------------
% 0.22/0.55  % (4163)------------------------------
% 0.22/0.55  % (4137)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.55  % (4155)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.56  % (4155)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f187,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(avatar_sat_refutation,[],[f68,f73,f78,f171,f174,f186])).
% 0.22/0.56  fof(f186,plain,(
% 0.22/0.56    spl4_1 | spl4_2 | ~spl4_7),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f185])).
% 0.22/0.56  fof(f185,plain,(
% 0.22/0.56    $false | (spl4_1 | spl4_2 | ~spl4_7)),
% 0.22/0.56    inference(subsumption_resolution,[],[f184,f67])).
% 0.22/0.56  fof(f67,plain,(
% 0.22/0.56    sK0 != sK2 | spl4_1),
% 0.22/0.56    inference(avatar_component_clause,[],[f65])).
% 0.22/0.56  fof(f65,plain,(
% 0.22/0.56    spl4_1 <=> sK0 = sK2),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.56  fof(f184,plain,(
% 0.22/0.56    sK0 = sK2 | (spl4_2 | ~spl4_7)),
% 0.22/0.56    inference(subsumption_resolution,[],[f179,f72])).
% 0.22/0.56  fof(f72,plain,(
% 0.22/0.56    sK0 != sK1 | spl4_2),
% 0.22/0.56    inference(avatar_component_clause,[],[f70])).
% 0.22/0.56  fof(f70,plain,(
% 0.22/0.56    spl4_2 <=> sK0 = sK1),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.56  fof(f179,plain,(
% 0.22/0.56    sK0 = sK1 | sK0 = sK2 | ~spl4_7),
% 0.22/0.56    inference(resolution,[],[f154,f115])).
% 0.22/0.56  fof(f115,plain,(
% 0.22/0.56    r2_hidden(sK0,k2_tarski(sK1,sK2)) | ~spl4_7),
% 0.22/0.56    inference(avatar_component_clause,[],[f113])).
% 0.22/0.56  fof(f113,plain,(
% 0.22/0.56    spl4_7 <=> r2_hidden(sK0,k2_tarski(sK1,sK2))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.56  fof(f154,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_tarski(X0,X1)) | X0 = X2 | X1 = X2) )),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f153])).
% 0.22/0.56  fof(f153,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_tarski(X0,X1)) | X0 = X2 | X0 = X2 | X1 = X2) )),
% 0.22/0.56    inference(superposition,[],[f63,f35])).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.56  fof(f63,plain,(
% 0.22/0.56    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k1_enumset1(X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 0.22/0.56    inference(equality_resolution,[],[f43])).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.22/0.56    inference(cnf_transformation,[],[f28])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.22/0.56    inference(rectify,[],[f25])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.22/0.56    inference(flattening,[],[f24])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.22/0.56    inference(nnf_transformation,[],[f16])).
% 0.22/0.56  fof(f16,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.22/0.56    inference(ennf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 0.22/0.56  fof(f174,plain,(
% 0.22/0.56    spl4_6 | spl4_7 | ~spl4_3),
% 0.22/0.56    inference(avatar_split_clause,[],[f172,f75,f113,f109])).
% 0.22/0.56  fof(f109,plain,(
% 0.22/0.56    spl4_6 <=> k1_xboole_0 = k1_tarski(sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.56  fof(f75,plain,(
% 0.22/0.56    spl4_3 <=> r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.56  fof(f172,plain,(
% 0.22/0.56    r2_hidden(sK0,k2_tarski(sK1,sK2)) | k1_xboole_0 = k1_tarski(sK0) | ~spl4_3),
% 0.22/0.56    inference(resolution,[],[f77,f99])).
% 0.22/0.56  fof(f99,plain,(
% 0.22/0.56    ( ! [X2,X3] : (~r1_tarski(k1_tarski(X2),X3) | r2_hidden(X2,X3) | k1_xboole_0 = k1_tarski(X2)) )),
% 0.22/0.56    inference(superposition,[],[f97,f38])).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f21])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.22/0.56    inference(nnf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.56  fof(f97,plain,(
% 0.22/0.56    ( ! [X2,X1] : (k1_tarski(X1) = k4_xboole_0(k1_tarski(X1),X2) | r2_hidden(X1,X2)) )),
% 0.22/0.56    inference(forward_demodulation,[],[f56,f36])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    ( ! [X2,X1] : (k1_tarski(X1) = k4_xboole_0(k2_tarski(X1,X1),X2) | r2_hidden(X1,X2)) )),
% 0.22/0.56    inference(equality_resolution,[],[f42])).
% 0.22/0.56  fof(f42,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | X0 != X1 | r2_hidden(X0,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f23])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | (X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.22/0.56    inference(flattening,[],[f22])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | ((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2))) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.22/0.56    inference(nnf_transformation,[],[f12])).
% 0.22/0.57  fof(f12,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).
% 0.22/0.57  fof(f77,plain,(
% 0.22/0.57    r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)) | ~spl4_3),
% 0.22/0.57    inference(avatar_component_clause,[],[f75])).
% 0.22/0.57  fof(f171,plain,(
% 0.22/0.57    ~spl4_6),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f170])).
% 0.22/0.57  fof(f170,plain,(
% 0.22/0.57    $false | ~spl4_6),
% 0.22/0.57    inference(subsumption_resolution,[],[f169,f54])).
% 0.22/0.57  fof(f54,plain,(
% 0.22/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.57    inference(equality_resolution,[],[f33])).
% 0.22/0.57  fof(f33,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.57    inference(cnf_transformation,[],[f20])).
% 0.22/0.57  fof(f20,plain,(
% 0.22/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.57    inference(flattening,[],[f19])).
% 0.22/0.57  fof(f19,plain,(
% 0.22/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.57    inference(nnf_transformation,[],[f1])).
% 0.22/0.57  fof(f1,axiom,(
% 0.22/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.57  fof(f169,plain,(
% 0.22/0.57    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~spl4_6),
% 0.22/0.57    inference(forward_demodulation,[],[f165,f111])).
% 0.22/0.57  fof(f111,plain,(
% 0.22/0.57    k1_xboole_0 = k1_tarski(sK0) | ~spl4_6),
% 0.22/0.57    inference(avatar_component_clause,[],[f109])).
% 0.22/0.57  fof(f165,plain,(
% 0.22/0.57    ~r1_tarski(k1_xboole_0,k1_tarski(sK0)) | ~spl4_6),
% 0.22/0.57    inference(resolution,[],[f156,f82])).
% 0.22/0.57  fof(f82,plain,(
% 0.22/0.57    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 0.22/0.57    inference(superposition,[],[f79,f36])).
% 0.22/0.57  fof(f79,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 0.22/0.57    inference(superposition,[],[f62,f35])).
% 0.22/0.57  fof(f62,plain,(
% 0.22/0.57    ( ! [X2,X5,X1] : (r2_hidden(X5,k1_enumset1(X5,X1,X2))) )),
% 0.22/0.57    inference(equality_resolution,[],[f61])).
% 0.22/0.57  fof(f61,plain,(
% 0.22/0.57    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X5,X1,X2) != X3) )),
% 0.22/0.57    inference(equality_resolution,[],[f44])).
% 0.22/0.57  fof(f44,plain,(
% 0.22/0.57    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 0.22/0.57    inference(cnf_transformation,[],[f28])).
% 0.22/0.57  fof(f156,plain,(
% 0.22/0.57    ( ! [X0] : (~r2_hidden(sK0,X0) | ~r1_tarski(k1_xboole_0,X0)) ) | ~spl4_6),
% 0.22/0.57    inference(trivial_inequality_removal,[],[f155])).
% 0.22/0.57  fof(f155,plain,(
% 0.22/0.57    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~r2_hidden(sK0,X0) | ~r1_tarski(k1_xboole_0,X0)) ) | ~spl4_6),
% 0.22/0.57    inference(superposition,[],[f126,f38])).
% 0.22/0.57  fof(f126,plain,(
% 0.22/0.57    ( ! [X1] : (k1_xboole_0 != k4_xboole_0(k1_xboole_0,X1) | ~r2_hidden(sK0,X1)) ) | ~spl4_6),
% 0.22/0.57    inference(superposition,[],[f95,f111])).
% 0.22/0.57  fof(f95,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.57    inference(superposition,[],[f39,f36])).
% 0.22/0.57  fof(f39,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f23])).
% 0.22/0.57  fof(f78,plain,(
% 0.22/0.57    spl4_3),
% 0.22/0.57    inference(avatar_split_clause,[],[f29,f75])).
% 0.22/0.57  fof(f29,plain,(
% 0.22/0.57    r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2))),
% 0.22/0.57    inference(cnf_transformation,[],[f18])).
% 0.22/0.57  fof(f18,plain,(
% 0.22/0.57    sK0 != sK2 & sK0 != sK1 & r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17])).
% 0.22/0.57  fof(f17,plain,(
% 0.22/0.57    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))) => (sK0 != sK2 & sK0 != sK1 & r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f15,plain,(
% 0.22/0.57    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 0.22/0.57    inference(ennf_transformation,[],[f14])).
% 0.22/0.57  fof(f14,negated_conjecture,(
% 0.22/0.57    ~! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 0.22/0.57    inference(negated_conjecture,[],[f13])).
% 0.22/0.57  fof(f13,conjecture,(
% 0.22/0.57    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).
% 0.22/0.57  fof(f73,plain,(
% 0.22/0.57    ~spl4_2),
% 0.22/0.57    inference(avatar_split_clause,[],[f30,f70])).
% 0.22/0.57  fof(f30,plain,(
% 0.22/0.57    sK0 != sK1),
% 0.22/0.57    inference(cnf_transformation,[],[f18])).
% 0.22/0.57  fof(f68,plain,(
% 0.22/0.57    ~spl4_1),
% 0.22/0.57    inference(avatar_split_clause,[],[f31,f65])).
% 0.22/0.57  fof(f31,plain,(
% 0.22/0.57    sK0 != sK2),
% 0.22/0.57    inference(cnf_transformation,[],[f18])).
% 0.22/0.57  % SZS output end Proof for theBenchmark
% 0.22/0.57  % (4155)------------------------------
% 0.22/0.57  % (4155)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (4155)Termination reason: Refutation
% 0.22/0.57  
% 0.22/0.57  % (4155)Memory used [KB]: 6268
% 0.22/0.57  % (4155)Time elapsed: 0.128 s
% 0.22/0.57  % (4155)------------------------------
% 0.22/0.57  % (4155)------------------------------
% 0.22/0.57  % (4133)Success in time 0.208 s
%------------------------------------------------------------------------------
