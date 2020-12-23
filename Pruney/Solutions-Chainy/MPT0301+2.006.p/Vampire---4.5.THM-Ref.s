%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:53 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 224 expanded)
%              Number of leaves         :   19 (  72 expanded)
%              Depth                    :   15
%              Number of atoms          :  307 ( 810 expanded)
%              Number of equality atoms :  113 ( 322 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (16416)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (16390)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% (16418)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% (16397)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% (16407)Refutation not found, incomplete strategy% (16407)------------------------------
% (16407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (16407)Termination reason: Refutation not found, incomplete strategy

% (16407)Memory used [KB]: 10618
% (16407)Time elapsed: 0.123 s
% (16407)------------------------------
% (16407)------------------------------
% (16414)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (16415)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% (16398)Refutation not found, incomplete strategy% (16398)------------------------------
% (16398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (16398)Termination reason: Refutation not found, incomplete strategy

% (16398)Memory used [KB]: 10746
% (16398)Time elapsed: 0.128 s
% (16398)------------------------------
% (16398)------------------------------
% (16409)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (16399)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (16419)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% (16390)Refutation not found, incomplete strategy% (16390)------------------------------
% (16390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f218,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f114,f119,f120,f168,f185,f203,f210,f217])).

fof(f217,plain,
    ( spl13_3
    | ~ spl13_4 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | spl13_3
    | ~ spl13_4 ),
    inference(subsumption_resolution,[],[f212,f118])).

fof(f118,plain,
    ( k1_xboole_0 != sK0
    | spl13_3 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl13_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f212,plain,
    ( k1_xboole_0 = sK0
    | ~ spl13_4 ),
    inference(resolution,[],[f199,f58])).

fof(f58,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f199,plain,
    ( ! [X6] : ~ r2_hidden(X6,sK0)
    | ~ spl13_4 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl13_4
  <=> ! [X6] : ~ r2_hidden(X6,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f210,plain,
    ( spl13_2
    | ~ spl13_5 ),
    inference(avatar_contradiction_clause,[],[f209])).

fof(f209,plain,
    ( $false
    | spl13_2
    | ~ spl13_5 ),
    inference(subsumption_resolution,[],[f205,f113])).

fof(f113,plain,
    ( k1_xboole_0 != sK1
    | spl13_2 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl13_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f205,plain,
    ( k1_xboole_0 = sK1
    | ~ spl13_5 ),
    inference(resolution,[],[f202,f58])).

fof(f202,plain,
    ( ! [X7] : ~ r2_hidden(X7,sK1)
    | ~ spl13_5 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl13_5
  <=> ! [X7] : ~ r2_hidden(X7,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).

fof(f203,plain,
    ( spl13_4
    | spl13_5
    | ~ spl13_1 ),
    inference(avatar_split_clause,[],[f196,f107,f201,f198])).

fof(f107,plain,
    ( spl13_1
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f196,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(X7,sK1)
        | ~ r2_hidden(X6,sK0) )
    | ~ spl13_1 ),
    inference(subsumption_resolution,[],[f195,f138])).

% (16411)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f138,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f137,f131])).

% (16413)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f131,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f125,f59])).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f125,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f67,f56])).

fof(f56,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f137,plain,(
    ! [X2,X1] : ~ r2_hidden(X1,k3_xboole_0(k1_xboole_0,X2)) ),
    inference(resolution,[],[f135,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f135,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(trivial_inequality_removal,[],[f133])).

fof(f133,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f69,f131])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f195,plain,
    ( ! [X6,X7] :
        ( r2_hidden(k4_tarski(X6,X7),k1_xboole_0)
        | ~ r2_hidden(X7,sK1)
        | ~ r2_hidden(X6,sK0) )
    | ~ spl13_1 ),
    inference(superposition,[],[f102,f108])).

fof(f108,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl13_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f102,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK6(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( sK6(X0,X1,X2) = k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2))
              & r2_hidden(sK8(X0,X1,X2),X1)
              & r2_hidden(sK7(X0,X1,X2),X0) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK9(X0,X1,X8),sK10(X0,X1,X8)) = X8
                & r2_hidden(sK10(X0,X1,X8),X1)
                & r2_hidden(sK9(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10])],[f46,f49,f48,f47])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k4_tarski(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k4_tarski(X4,X5) != sK6(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK6(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK6(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK6(X0,X1,X2) = k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2))
        & r2_hidden(sK8(X0,X1,X2),X1)
        & r2_hidden(sK7(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK9(X0,X1,X8),sK10(X0,X1,X8)) = X8
        & r2_hidden(sK10(X0,X1,X8),X1)
        & r2_hidden(sK9(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k4_tarski(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k4_tarski(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f185,plain,
    ( spl13_1
    | ~ spl13_3 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | spl13_1
    | ~ spl13_3 ),
    inference(trivial_inequality_removal,[],[f183])).

fof(f183,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl13_1
    | ~ spl13_3 ),
    inference(superposition,[],[f169,f177])).

fof(f177,plain,(
    ! [X3] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X3) ),
    inference(resolution,[],[f175,f58])).

fof(f175,plain,(
    ! [X4,X3] : ~ r2_hidden(X3,k2_zfmisc_1(k1_xboole_0,X4)) ),
    inference(resolution,[],[f105,f138])).

fof(f105,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK9(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK9(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f169,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | spl13_1
    | ~ spl13_3 ),
    inference(forward_demodulation,[],[f109,f117])).

fof(f117,plain,
    ( k1_xboole_0 = sK0
    | ~ spl13_3 ),
    inference(avatar_component_clause,[],[f116])).

fof(f109,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | spl13_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f168,plain,
    ( spl13_1
    | ~ spl13_2 ),
    inference(avatar_contradiction_clause,[],[f167])).

fof(f167,plain,
    ( $false
    | spl13_1
    | ~ spl13_2 ),
    inference(trivial_inequality_removal,[],[f166])).

fof(f166,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl13_1
    | ~ spl13_2 ),
    inference(superposition,[],[f121,f162])).

fof(f162,plain,(
    ! [X3] : k1_xboole_0 = k2_zfmisc_1(X3,k1_xboole_0) ),
    inference(resolution,[],[f160,f58])).

fof(f160,plain,(
    ! [X4,X3] : ~ r2_hidden(X3,k2_zfmisc_1(X4,k1_xboole_0)) ),
    inference(resolution,[],[f104,f138])).

fof(f104,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK10(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK10(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f121,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | spl13_1
    | ~ spl13_2 ),
    inference(forward_demodulation,[],[f109,f112])).

fof(f112,plain,
    ( k1_xboole_0 = sK1
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f111])).

fof(f120,plain,
    ( spl13_1
    | spl13_3
    | spl13_2 ),
    inference(avatar_split_clause,[],[f53,f111,f116,f107])).

fof(f53,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ( k1_xboole_0 != sK1
        & k1_xboole_0 != sK0 )
      | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( ( ( k1_xboole_0 != X1
            & k1_xboole_0 != X0 )
          | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) )
   => ( ( ( k1_xboole_0 != sK1
          & k1_xboole_0 != sK0 )
        | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) )
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 = sK0
        | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f119,plain,
    ( ~ spl13_1
    | ~ spl13_3 ),
    inference(avatar_split_clause,[],[f54,f116,f107])).

fof(f54,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f114,plain,
    ( ~ spl13_1
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f55,f111,f107])).

fof(f55,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:11:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (16391)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.21/0.52  % (16406)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.21/0.52  % (16394)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.21/0.52  % (16408)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.21/0.52  % (16393)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.21/0.52  % (16403)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.21/0.52  % (16412)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.21/0.53  % (16404)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.21/0.53  % (16400)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.21/0.53  % (16398)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.21/0.53  % (16400)Refutation not found, incomplete strategy% (16400)------------------------------
% 1.21/0.53  % (16400)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.53  % (16400)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.53  
% 1.21/0.53  % (16400)Memory used [KB]: 10618
% 1.21/0.53  % (16400)Time elapsed: 0.119 s
% 1.21/0.53  % (16400)------------------------------
% 1.21/0.53  % (16400)------------------------------
% 1.21/0.53  % (16407)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.21/0.53  % (16396)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.21/0.53  % (16392)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.33/0.53  % (16417)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.33/0.53  % (16392)Refutation not found, incomplete strategy% (16392)------------------------------
% 1.33/0.53  % (16392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.53  % (16392)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.53  
% 1.33/0.53  % (16392)Memory used [KB]: 10746
% 1.33/0.53  % (16392)Time elapsed: 0.125 s
% 1.33/0.53  % (16392)------------------------------
% 1.33/0.53  % (16392)------------------------------
% 1.33/0.54  % (16395)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.33/0.54  % (16410)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.33/0.54  % (16393)Refutation found. Thanks to Tanya!
% 1.33/0.54  % SZS status Theorem for theBenchmark
% 1.33/0.54  % SZS output start Proof for theBenchmark
% 1.33/0.54  % (16416)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.33/0.54  % (16390)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.33/0.54  % (16418)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.33/0.54  % (16397)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.33/0.54  % (16407)Refutation not found, incomplete strategy% (16407)------------------------------
% 1.33/0.54  % (16407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (16407)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (16407)Memory used [KB]: 10618
% 1.33/0.54  % (16407)Time elapsed: 0.123 s
% 1.33/0.54  % (16407)------------------------------
% 1.33/0.54  % (16407)------------------------------
% 1.33/0.54  % (16414)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.33/0.54  % (16415)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.33/0.54  % (16398)Refutation not found, incomplete strategy% (16398)------------------------------
% 1.33/0.54  % (16398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (16398)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (16398)Memory used [KB]: 10746
% 1.33/0.54  % (16398)Time elapsed: 0.128 s
% 1.33/0.54  % (16398)------------------------------
% 1.33/0.54  % (16398)------------------------------
% 1.33/0.54  % (16409)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.33/0.54  % (16399)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.33/0.54  % (16419)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.33/0.55  % (16390)Refutation not found, incomplete strategy% (16390)------------------------------
% 1.33/0.55  % (16390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.55  fof(f218,plain,(
% 1.33/0.55    $false),
% 1.33/0.55    inference(avatar_sat_refutation,[],[f114,f119,f120,f168,f185,f203,f210,f217])).
% 1.33/0.55  fof(f217,plain,(
% 1.33/0.55    spl13_3 | ~spl13_4),
% 1.33/0.55    inference(avatar_contradiction_clause,[],[f216])).
% 1.33/0.55  fof(f216,plain,(
% 1.33/0.55    $false | (spl13_3 | ~spl13_4)),
% 1.33/0.55    inference(subsumption_resolution,[],[f212,f118])).
% 1.33/0.55  fof(f118,plain,(
% 1.33/0.55    k1_xboole_0 != sK0 | spl13_3),
% 1.33/0.55    inference(avatar_component_clause,[],[f116])).
% 1.33/0.55  fof(f116,plain,(
% 1.33/0.55    spl13_3 <=> k1_xboole_0 = sK0),
% 1.33/0.55    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).
% 1.33/0.55  fof(f212,plain,(
% 1.33/0.55    k1_xboole_0 = sK0 | ~spl13_4),
% 1.33/0.55    inference(resolution,[],[f199,f58])).
% 1.33/0.55  fof(f58,plain,(
% 1.33/0.55    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 1.33/0.55    inference(cnf_transformation,[],[f31])).
% 1.33/0.55  fof(f31,plain,(
% 1.33/0.55    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 1.33/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f30])).
% 1.33/0.55  fof(f30,plain,(
% 1.33/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 1.33/0.55    introduced(choice_axiom,[])).
% 1.33/0.55  fof(f20,plain,(
% 1.33/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.33/0.55    inference(ennf_transformation,[],[f4])).
% 1.33/0.55  fof(f4,axiom,(
% 1.33/0.55    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.33/0.55  fof(f199,plain,(
% 1.33/0.55    ( ! [X6] : (~r2_hidden(X6,sK0)) ) | ~spl13_4),
% 1.33/0.55    inference(avatar_component_clause,[],[f198])).
% 1.33/0.55  fof(f198,plain,(
% 1.33/0.55    spl13_4 <=> ! [X6] : ~r2_hidden(X6,sK0)),
% 1.33/0.55    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).
% 1.33/0.55  fof(f210,plain,(
% 1.33/0.55    spl13_2 | ~spl13_5),
% 1.33/0.55    inference(avatar_contradiction_clause,[],[f209])).
% 1.33/0.55  fof(f209,plain,(
% 1.33/0.55    $false | (spl13_2 | ~spl13_5)),
% 1.33/0.55    inference(subsumption_resolution,[],[f205,f113])).
% 1.33/0.55  fof(f113,plain,(
% 1.33/0.55    k1_xboole_0 != sK1 | spl13_2),
% 1.33/0.55    inference(avatar_component_clause,[],[f111])).
% 1.33/0.55  fof(f111,plain,(
% 1.33/0.55    spl13_2 <=> k1_xboole_0 = sK1),
% 1.33/0.55    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).
% 1.33/0.55  fof(f205,plain,(
% 1.33/0.55    k1_xboole_0 = sK1 | ~spl13_5),
% 1.33/0.55    inference(resolution,[],[f202,f58])).
% 1.33/0.55  fof(f202,plain,(
% 1.33/0.55    ( ! [X7] : (~r2_hidden(X7,sK1)) ) | ~spl13_5),
% 1.33/0.55    inference(avatar_component_clause,[],[f201])).
% 1.33/0.55  fof(f201,plain,(
% 1.33/0.55    spl13_5 <=> ! [X7] : ~r2_hidden(X7,sK1)),
% 1.33/0.55    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).
% 1.33/0.55  fof(f203,plain,(
% 1.33/0.55    spl13_4 | spl13_5 | ~spl13_1),
% 1.33/0.55    inference(avatar_split_clause,[],[f196,f107,f201,f198])).
% 1.33/0.55  fof(f107,plain,(
% 1.33/0.55    spl13_1 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 1.33/0.55    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).
% 1.33/0.55  fof(f196,plain,(
% 1.33/0.55    ( ! [X6,X7] : (~r2_hidden(X7,sK1) | ~r2_hidden(X6,sK0)) ) | ~spl13_1),
% 1.33/0.55    inference(subsumption_resolution,[],[f195,f138])).
% 1.33/0.55  % (16411)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.33/0.55  fof(f138,plain,(
% 1.33/0.55    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 1.33/0.55    inference(forward_demodulation,[],[f137,f131])).
% 1.33/0.55  % (16413)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.33/0.55  fof(f131,plain,(
% 1.33/0.55    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.33/0.55    inference(resolution,[],[f125,f59])).
% 1.33/0.55  fof(f59,plain,(
% 1.33/0.55    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f6])).
% 1.33/0.55  fof(f6,axiom,(
% 1.33/0.55    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.33/0.55  fof(f125,plain,(
% 1.33/0.55    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.33/0.55    inference(resolution,[],[f67,f56])).
% 1.33/0.55  fof(f56,plain,(
% 1.33/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f7])).
% 1.33/0.55  fof(f7,axiom,(
% 1.33/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.33/0.55  fof(f67,plain,(
% 1.33/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f35])).
% 1.33/0.55  fof(f35,plain,(
% 1.33/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.33/0.55    inference(flattening,[],[f34])).
% 1.33/0.55  fof(f34,plain,(
% 1.33/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.33/0.55    inference(nnf_transformation,[],[f5])).
% 1.33/0.55  fof(f5,axiom,(
% 1.33/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.33/0.55  fof(f137,plain,(
% 1.33/0.55    ( ! [X2,X1] : (~r2_hidden(X1,k3_xboole_0(k1_xboole_0,X2))) )),
% 1.33/0.55    inference(resolution,[],[f135,f63])).
% 1.33/0.55  fof(f63,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.33/0.55    inference(cnf_transformation,[],[f33])).
% 1.33/0.55  fof(f33,plain,(
% 1.33/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.33/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f32])).
% 1.33/0.55  fof(f32,plain,(
% 1.33/0.55    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 1.33/0.55    introduced(choice_axiom,[])).
% 1.33/0.55  fof(f21,plain,(
% 1.33/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.33/0.55    inference(ennf_transformation,[],[f18])).
% 1.33/0.55  fof(f18,plain,(
% 1.33/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.33/0.55    inference(rectify,[],[f3])).
% 1.33/0.55  fof(f3,axiom,(
% 1.33/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.33/0.55  fof(f135,plain,(
% 1.33/0.55    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 1.33/0.55    inference(trivial_inequality_removal,[],[f133])).
% 1.33/0.55  fof(f133,plain,(
% 1.33/0.55    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,X0)) )),
% 1.33/0.55    inference(superposition,[],[f69,f131])).
% 1.33/0.55  fof(f69,plain,(
% 1.33/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f36])).
% 1.33/0.55  fof(f36,plain,(
% 1.33/0.55    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.33/0.55    inference(nnf_transformation,[],[f2])).
% 1.33/0.55  fof(f2,axiom,(
% 1.33/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.33/0.55  fof(f195,plain,(
% 1.33/0.55    ( ! [X6,X7] : (r2_hidden(k4_tarski(X6,X7),k1_xboole_0) | ~r2_hidden(X7,sK1) | ~r2_hidden(X6,sK0)) ) | ~spl13_1),
% 1.33/0.55    inference(superposition,[],[f102,f108])).
% 1.33/0.55  fof(f108,plain,(
% 1.33/0.55    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl13_1),
% 1.33/0.55    inference(avatar_component_clause,[],[f107])).
% 1.33/0.55  fof(f102,plain,(
% 1.33/0.55    ( ! [X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0)) )),
% 1.33/0.55    inference(equality_resolution,[],[f101])).
% 1.33/0.55  fof(f101,plain,(
% 1.33/0.55    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),X2) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.33/0.55    inference(equality_resolution,[],[f80])).
% 1.33/0.55  fof(f80,plain,(
% 1.33/0.55    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.33/0.55    inference(cnf_transformation,[],[f50])).
% 1.33/0.55  fof(f50,plain,(
% 1.33/0.55    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK6(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((sK6(X0,X1,X2) = k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)) & r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),X0)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK9(X0,X1,X8),sK10(X0,X1,X8)) = X8 & r2_hidden(sK10(X0,X1,X8),X1) & r2_hidden(sK9(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.33/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10])],[f46,f49,f48,f47])).
% 1.33/0.55  fof(f47,plain,(
% 1.33/0.55    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK6(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK6(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 1.33/0.55    introduced(choice_axiom,[])).
% 1.33/0.55  fof(f48,plain,(
% 1.33/0.55    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK6(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK6(X0,X1,X2) = k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)) & r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),X0)))),
% 1.33/0.55    introduced(choice_axiom,[])).
% 1.33/0.55  fof(f49,plain,(
% 1.33/0.55    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK9(X0,X1,X8),sK10(X0,X1,X8)) = X8 & r2_hidden(sK10(X0,X1,X8),X1) & r2_hidden(sK9(X0,X1,X8),X0)))),
% 1.33/0.55    introduced(choice_axiom,[])).
% 1.33/0.55  fof(f46,plain,(
% 1.33/0.55    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.33/0.55    inference(rectify,[],[f45])).
% 1.33/0.55  fof(f45,plain,(
% 1.33/0.55    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.33/0.55    inference(nnf_transformation,[],[f11])).
% 1.33/0.55  fof(f11,axiom,(
% 1.33/0.55    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.33/0.55  fof(f185,plain,(
% 1.33/0.55    spl13_1 | ~spl13_3),
% 1.33/0.55    inference(avatar_contradiction_clause,[],[f184])).
% 1.33/0.55  fof(f184,plain,(
% 1.33/0.55    $false | (spl13_1 | ~spl13_3)),
% 1.33/0.55    inference(trivial_inequality_removal,[],[f183])).
% 1.33/0.55  fof(f183,plain,(
% 1.33/0.55    k1_xboole_0 != k1_xboole_0 | (spl13_1 | ~spl13_3)),
% 1.33/0.55    inference(superposition,[],[f169,f177])).
% 1.33/0.55  fof(f177,plain,(
% 1.33/0.55    ( ! [X3] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X3)) )),
% 1.33/0.55    inference(resolution,[],[f175,f58])).
% 1.33/0.55  fof(f175,plain,(
% 1.33/0.55    ( ! [X4,X3] : (~r2_hidden(X3,k2_zfmisc_1(k1_xboole_0,X4))) )),
% 1.33/0.55    inference(resolution,[],[f105,f138])).
% 1.33/0.55  fof(f105,plain,(
% 1.33/0.55    ( ! [X0,X8,X1] : (r2_hidden(sK9(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 1.33/0.55    inference(equality_resolution,[],[f77])).
% 1.33/0.55  fof(f77,plain,(
% 1.33/0.55    ( ! [X2,X0,X8,X1] : (r2_hidden(sK9(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.33/0.55    inference(cnf_transformation,[],[f50])).
% 1.33/0.55  fof(f169,plain,(
% 1.33/0.55    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) | (spl13_1 | ~spl13_3)),
% 1.33/0.55    inference(forward_demodulation,[],[f109,f117])).
% 1.33/0.55  fof(f117,plain,(
% 1.33/0.55    k1_xboole_0 = sK0 | ~spl13_3),
% 1.33/0.55    inference(avatar_component_clause,[],[f116])).
% 1.33/0.55  fof(f109,plain,(
% 1.33/0.55    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | spl13_1),
% 1.33/0.55    inference(avatar_component_clause,[],[f107])).
% 1.33/0.55  fof(f168,plain,(
% 1.33/0.55    spl13_1 | ~spl13_2),
% 1.33/0.55    inference(avatar_contradiction_clause,[],[f167])).
% 1.33/0.55  fof(f167,plain,(
% 1.33/0.55    $false | (spl13_1 | ~spl13_2)),
% 1.33/0.55    inference(trivial_inequality_removal,[],[f166])).
% 1.33/0.55  fof(f166,plain,(
% 1.33/0.55    k1_xboole_0 != k1_xboole_0 | (spl13_1 | ~spl13_2)),
% 1.33/0.55    inference(superposition,[],[f121,f162])).
% 1.33/0.55  fof(f162,plain,(
% 1.33/0.55    ( ! [X3] : (k1_xboole_0 = k2_zfmisc_1(X3,k1_xboole_0)) )),
% 1.33/0.55    inference(resolution,[],[f160,f58])).
% 1.33/0.55  fof(f160,plain,(
% 1.33/0.55    ( ! [X4,X3] : (~r2_hidden(X3,k2_zfmisc_1(X4,k1_xboole_0))) )),
% 1.33/0.55    inference(resolution,[],[f104,f138])).
% 1.33/0.55  fof(f104,plain,(
% 1.33/0.55    ( ! [X0,X8,X1] : (r2_hidden(sK10(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 1.33/0.55    inference(equality_resolution,[],[f78])).
% 1.33/0.55  fof(f78,plain,(
% 1.33/0.55    ( ! [X2,X0,X8,X1] : (r2_hidden(sK10(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.33/0.55    inference(cnf_transformation,[],[f50])).
% 1.33/0.55  fof(f121,plain,(
% 1.33/0.55    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | (spl13_1 | ~spl13_2)),
% 1.33/0.55    inference(forward_demodulation,[],[f109,f112])).
% 1.33/0.55  fof(f112,plain,(
% 1.33/0.55    k1_xboole_0 = sK1 | ~spl13_2),
% 1.33/0.55    inference(avatar_component_clause,[],[f111])).
% 1.33/0.55  fof(f120,plain,(
% 1.33/0.55    spl13_1 | spl13_3 | spl13_2),
% 1.33/0.55    inference(avatar_split_clause,[],[f53,f111,f116,f107])).
% 1.33/0.55  fof(f53,plain,(
% 1.33/0.55    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 1.33/0.55    inference(cnf_transformation,[],[f29])).
% 1.33/0.55  fof(f29,plain,(
% 1.33/0.55    ((k1_xboole_0 != sK1 & k1_xboole_0 != sK0) | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)) & (k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1))),
% 1.33/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f28])).
% 1.33/0.55  fof(f28,plain,(
% 1.33/0.55    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1))) => (((k1_xboole_0 != sK1 & k1_xboole_0 != sK0) | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)) & (k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)))),
% 1.33/0.55    introduced(choice_axiom,[])).
% 1.33/0.55  fof(f27,plain,(
% 1.33/0.55    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 1.33/0.55    inference(flattening,[],[f26])).
% 1.33/0.55  fof(f26,plain,(
% 1.33/0.55    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 1.33/0.55    inference(nnf_transformation,[],[f19])).
% 1.33/0.55  fof(f19,plain,(
% 1.33/0.55    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.33/0.55    inference(ennf_transformation,[],[f17])).
% 1.33/0.55  fof(f17,negated_conjecture,(
% 1.33/0.55    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.33/0.55    inference(negated_conjecture,[],[f16])).
% 1.33/0.55  fof(f16,conjecture,(
% 1.33/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.33/0.55  fof(f119,plain,(
% 1.33/0.55    ~spl13_1 | ~spl13_3),
% 1.33/0.55    inference(avatar_split_clause,[],[f54,f116,f107])).
% 1.33/0.55  fof(f54,plain,(
% 1.33/0.55    k1_xboole_0 != sK0 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 1.33/0.55    inference(cnf_transformation,[],[f29])).
% 1.33/0.55  fof(f114,plain,(
% 1.33/0.55    ~spl13_1 | ~spl13_2),
% 1.33/0.55    inference(avatar_split_clause,[],[f55,f111,f107])).
% 1.33/0.55  fof(f55,plain,(
% 1.33/0.55    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 1.33/0.55    inference(cnf_transformation,[],[f29])).
% 1.33/0.55  % SZS output end Proof for theBenchmark
% 1.33/0.55  % (16393)------------------------------
% 1.33/0.55  % (16393)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.55  % (16393)Termination reason: Refutation
% 1.33/0.55  
% 1.33/0.55  % (16393)Memory used [KB]: 10746
% 1.33/0.55  % (16393)Time elapsed: 0.131 s
% 1.33/0.55  % (16393)------------------------------
% 1.33/0.55  % (16393)------------------------------
% 1.33/0.55  % (16389)Success in time 0.19 s
%------------------------------------------------------------------------------
