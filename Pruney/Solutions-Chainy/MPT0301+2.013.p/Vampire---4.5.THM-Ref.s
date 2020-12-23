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
% DateTime   : Thu Dec  3 12:41:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 126 expanded)
%              Number of leaves         :   11 (  38 expanded)
%              Depth                    :   16
%              Number of atoms          :  234 ( 575 expanded)
%              Number of equality atoms :  122 ( 279 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f164,plain,(
    $false ),
    inference(subsumption_resolution,[],[f144,f163])).

% (26090)Refutation not found, incomplete strategy% (26090)------------------------------
% (26090)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26090)Termination reason: Refutation not found, incomplete strategy

% (26090)Memory used [KB]: 10618
% (26090)Time elapsed: 0.103 s
% (26090)------------------------------
% (26090)------------------------------
% (26105)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% (26106)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (26093)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (26103)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (26100)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (26109)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% (26097)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% (26095)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (26092)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (26094)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (26092)Refutation not found, incomplete strategy% (26092)------------------------------
% (26092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26092)Termination reason: Refutation not found, incomplete strategy

% (26092)Memory used [KB]: 10618
% (26092)Time elapsed: 0.133 s
% (26092)------------------------------
% (26092)------------------------------
% (26084)Refutation not found, incomplete strategy% (26084)------------------------------
% (26084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26084)Termination reason: Refutation not found, incomplete strategy

% (26084)Memory used [KB]: 10618
% (26084)Time elapsed: 0.129 s
% (26084)------------------------------
% (26084)------------------------------
% (26110)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% (26108)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f163,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f162])).

fof(f162,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X1,X0) ) ),
    inference(superposition,[],[f39,f78])).

fof(f78,plain,(
    ! [X8,X9] :
      ( k2_xboole_0(k1_tarski(sK8(X9,X8,sK3(k2_zfmisc_1(X8,X9)))),X9) = X9
      | k1_xboole_0 = k2_zfmisc_1(X8,X9) ) ),
    inference(resolution,[],[f70,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1,sK3(k2_zfmisc_1(X1,X0))),X0)
      | k1_xboole_0 = k2_zfmisc_1(X1,X0) ) ),
    inference(resolution,[],[f67,f58])).

fof(f58,plain,(
    ! [X0,X1] : sP0(X1,X0,k2_zfmisc_1(X0,X1)) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f10,f18])).

fof(f18,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(sK8(X0,X1,sK3(X2)),X0)
      | k1_xboole_0 = X2 ) ),
    inference(resolution,[],[f44,f38])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f44,plain,(
    ! [X2,X0,X8,X1] :
      ( ~ r2_hidden(X8,X2)
      | r2_hidden(sK8(X0,X1,X8),X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK4(X0,X1,X2)
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X1) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( sK4(X0,X1,X2) = k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2))
              & r2_hidden(sK6(X0,X1,X2),X0)
              & r2_hidden(sK5(X0,X1,X2),X1) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X0)
                  | ~ r2_hidden(X9,X1) ) )
            & ( ( k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8
                & r2_hidden(sK8(X0,X1,X8),X0)
                & r2_hidden(sK7(X0,X1,X8),X1) )
              | ~ r2_hidden(X8,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f27,f30,f29,f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X1) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k4_tarski(X6,X7) = X3
                & r2_hidden(X7,X0)
                & r2_hidden(X6,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k4_tarski(X4,X5) != sK4(X0,X1,X2)
              | ~ r2_hidden(X5,X0)
              | ~ r2_hidden(X4,X1) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK4(X0,X1,X2)
              & r2_hidden(X7,X0)
              & r2_hidden(X6,X1) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK4(X0,X1,X2)
          & r2_hidden(X7,X0)
          & r2_hidden(X6,X1) )
     => ( sK4(X0,X1,X2) = k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2))
        & r2_hidden(sK6(X0,X1,X2),X0)
        & r2_hidden(sK5(X0,X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X0)
          & r2_hidden(X11,X1) )
     => ( k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8
        & r2_hidden(sK8(X0,X1,X8),X0)
        & r2_hidden(sK7(X0,X1,X8),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X0)
                  | ~ r2_hidden(X4,X1) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k4_tarski(X6,X7) = X3
                  & r2_hidden(X7,X0)
                  & r2_hidden(X6,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X0)
                  | ~ r2_hidden(X9,X1) ) )
            & ( ? [X11,X12] :
                  ( k4_tarski(X11,X12) = X8
                  & r2_hidden(X12,X0)
                  & r2_hidden(X11,X1) )
              | ~ r2_hidden(X8,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f144,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f105,f134])).

fof(f134,plain,(
    k1_xboole_0 != sK1 ),
    inference(subsumption_resolution,[],[f60,f133])).

fof(f133,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0) ),
    inference(equality_resolution,[],[f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X1,X0) ) ),
    inference(superposition,[],[f39,f74])).

fof(f74,plain,(
    ! [X8,X9] :
      ( k2_xboole_0(k1_tarski(sK7(X9,X8,sK3(k2_zfmisc_1(X8,X9)))),X8) = X8
      | k1_xboole_0 = k2_zfmisc_1(X8,X9) ) ),
    inference(resolution,[],[f68,f41])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1,sK3(k2_zfmisc_1(X1,X0))),X1)
      | k1_xboole_0 = k2_zfmisc_1(X1,X0) ) ),
    inference(resolution,[],[f66,f58])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(sK7(X0,X1,sK3(X2)),X1)
      | k1_xboole_0 = X2 ) ),
    inference(resolution,[],[f43,f38])).

fof(f43,plain,(
    ! [X2,X0,X8,X1] :
      ( ~ r2_hidden(X8,X2)
      | r2_hidden(sK7(X0,X1,X8),X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f60,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK2) ),
    inference(inner_rewriting,[],[f34])).

fof(f34,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( ( k1_xboole_0 != sK2
        & k1_xboole_0 != sK1 )
      | k1_xboole_0 != k2_zfmisc_1(sK1,sK2) )
    & ( k1_xboole_0 = sK2
      | k1_xboole_0 = sK1
      | k1_xboole_0 = k2_zfmisc_1(sK1,sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f21,f22])).

% (26101)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f22,plain,
    ( ? [X0,X1] :
        ( ( ( k1_xboole_0 != X1
            & k1_xboole_0 != X0 )
          | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) )
   => ( ( ( k1_xboole_0 != sK2
          & k1_xboole_0 != sK1 )
        | k1_xboole_0 != k2_zfmisc_1(sK1,sK2) )
      & ( k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = k2_zfmisc_1(sK1,sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f105,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK1,k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f104])).

fof(f104,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k2_zfmisc_1(sK1,k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f59,f100])).

fof(f100,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f99,f39])).

fof(f99,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_xboole_0(k1_tarski(k4_tarski(sK3(sK1),sK3(sK2))),k1_xboole_0) ),
    inference(resolution,[],[f94,f41])).

fof(f94,plain,
    ( r2_hidden(k4_tarski(sK3(sK1),sK3(sK2)),k1_xboole_0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f93])).

fof(f93,plain,
    ( r2_hidden(k4_tarski(sK3(sK1),sK3(sK2)),k1_xboole_0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f85,f33])).

fof(f33,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK2)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f23])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0),sK3(X1)),k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f82,f38])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(k4_tarski(sK3(X2),X0),k2_zfmisc_1(X2,X1))
      | k1_xboole_0 = X2 ) ),
    inference(resolution,[],[f80,f38])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X0,X1)
      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ) ),
    inference(resolution,[],[f57,f58])).

fof(f57,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X10,X0)
      | ~ r2_hidden(X9,X1)
      | r2_hidden(k4_tarski(X9,X10),X2) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X0)
      | ~ r2_hidden(X9,X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f59,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != k2_zfmisc_1(sK1,k1_xboole_0) ),
    inference(inner_rewriting,[],[f35])).

fof(f35,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != k2_zfmisc_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:36:32 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (26082)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.49  % (26091)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.49  % (26099)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.50  % (26082)Refutation not found, incomplete strategy% (26082)------------------------------
% 0.21/0.50  % (26082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (26082)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (26082)Memory used [KB]: 1663
% 0.21/0.50  % (26082)Time elapsed: 0.085 s
% 0.21/0.50  % (26082)------------------------------
% 0.21/0.50  % (26082)------------------------------
% 0.21/0.50  % (26090)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.50  % (26091)Refutation not found, incomplete strategy% (26091)------------------------------
% 0.21/0.50  % (26091)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (26091)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (26091)Memory used [KB]: 10618
% 0.21/0.50  % (26091)Time elapsed: 0.102 s
% 0.21/0.50  % (26091)------------------------------
% 0.21/0.50  % (26091)------------------------------
% 0.21/0.50  % (26099)Refutation not found, incomplete strategy% (26099)------------------------------
% 0.21/0.50  % (26099)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (26099)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (26099)Memory used [KB]: 10618
% 0.21/0.50  % (26099)Time elapsed: 0.097 s
% 0.21/0.50  % (26099)------------------------------
% 0.21/0.50  % (26099)------------------------------
% 0.21/0.50  % (26096)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.50  % (26098)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (26085)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (26087)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (26086)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (26084)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (26104)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (26089)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (26083)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (26089)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f144,f163])).
% 0.21/0.51  % (26090)Refutation not found, incomplete strategy% (26090)------------------------------
% 0.21/0.51  % (26090)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (26090)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (26090)Memory used [KB]: 10618
% 0.21/0.51  % (26090)Time elapsed: 0.103 s
% 0.21/0.51  % (26090)------------------------------
% 0.21/0.51  % (26090)------------------------------
% 0.21/0.52  % (26105)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (26106)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (26093)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (26103)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (26100)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (26109)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (26097)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (26095)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (26092)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (26094)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (26092)Refutation not found, incomplete strategy% (26092)------------------------------
% 0.21/0.53  % (26092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (26092)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (26092)Memory used [KB]: 10618
% 0.21/0.53  % (26092)Time elapsed: 0.133 s
% 0.21/0.53  % (26092)------------------------------
% 0.21/0.53  % (26092)------------------------------
% 0.21/0.53  % (26084)Refutation not found, incomplete strategy% (26084)------------------------------
% 0.21/0.53  % (26084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (26084)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (26084)Memory used [KB]: 10618
% 0.21/0.53  % (26084)Time elapsed: 0.129 s
% 0.21/0.53  % (26084)------------------------------
% 0.21/0.53  % (26084)------------------------------
% 0.21/0.53  % (26110)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (26108)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  fof(f163,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f162])).
% 0.21/0.53  fof(f162,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X1,X0)) )),
% 0.21/0.53    inference(superposition,[],[f39,f78])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    ( ! [X8,X9] : (k2_xboole_0(k1_tarski(sK8(X9,X8,sK3(k2_zfmisc_1(X8,X9)))),X9) = X9 | k1_xboole_0 = k2_zfmisc_1(X8,X9)) )),
% 0.21/0.53    inference(resolution,[],[f70,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k2_xboole_0(k1_tarski(X0),X1) = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1,sK3(k2_zfmisc_1(X1,X0))),X0) | k1_xboole_0 = k2_zfmisc_1(X1,X0)) )),
% 0.21/0.53    inference(resolution,[],[f67,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X0,X1] : (sP0(X1,X0,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.53    inference(equality_resolution,[],[f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_zfmisc_1(X0,X1) != X2))),
% 0.21/0.53    inference(nnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 0.21/0.53    inference(definition_folding,[],[f10,f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(sK8(X0,X1,sK3(X2)),X0) | k1_xboole_0 = X2) )),
% 0.21/0.53    inference(resolution,[],[f44,f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X2,X0,X8,X1] : (~r2_hidden(X8,X2) | r2_hidden(sK8(X0,X1,X8),X0) | ~sP0(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((! [X4,X5] : (k4_tarski(X4,X5) != sK4(X0,X1,X2) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((sK4(X0,X1,X2) = k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) & r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK5(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X0) | ~r2_hidden(X9,X1))) & ((k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8 & r2_hidden(sK8(X0,X1,X8),X0) & r2_hidden(sK7(X0,X1,X8),X1)) | ~r2_hidden(X8,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f27,f30,f29,f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X0) & r2_hidden(X6,X1)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK4(X0,X1,X2) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK4(X0,X1,X2) & r2_hidden(X7,X0) & r2_hidden(X6,X1)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK4(X0,X1,X2) & r2_hidden(X7,X0) & r2_hidden(X6,X1)) => (sK4(X0,X1,X2) = k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) & r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK5(X0,X1,X2),X1)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X0) & r2_hidden(X11,X1)) => (k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8 & r2_hidden(sK8(X0,X1,X8),X0) & r2_hidden(sK7(X0,X1,X8),X1)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X0) & r2_hidden(X6,X1)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X0) | ~r2_hidden(X9,X1))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X0) & r2_hidden(X11,X1)) | ~r2_hidden(X8,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.53    inference(rectify,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.21/0.53    inference(nnf_transformation,[],[f18])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.21/0.53  fof(f144,plain,(
% 0.21/0.53    k1_xboole_0 != k2_zfmisc_1(sK1,k1_xboole_0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f105,f134])).
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    k1_xboole_0 != sK1),
% 0.21/0.53    inference(subsumption_resolution,[],[f60,f133])).
% 0.21/0.53  fof(f133,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f132])).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X1,X0)) )),
% 0.21/0.53    inference(superposition,[],[f39,f74])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ( ! [X8,X9] : (k2_xboole_0(k1_tarski(sK7(X9,X8,sK3(k2_zfmisc_1(X8,X9)))),X8) = X8 | k1_xboole_0 = k2_zfmisc_1(X8,X9)) )),
% 0.21/0.53    inference(resolution,[],[f68,f41])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1,sK3(k2_zfmisc_1(X1,X0))),X1) | k1_xboole_0 = k2_zfmisc_1(X1,X0)) )),
% 0.21/0.53    inference(resolution,[],[f66,f58])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(sK7(X0,X1,sK3(X2)),X1) | k1_xboole_0 = X2) )),
% 0.21/0.53    inference(resolution,[],[f43,f38])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X2,X0,X8,X1] : (~r2_hidden(X8,X2) | r2_hidden(sK7(X0,X1,X8),X1) | ~sP0(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK2)),
% 0.21/0.53    inference(inner_rewriting,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(sK1,sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ((k1_xboole_0 != sK2 & k1_xboole_0 != sK1) | k1_xboole_0 != k2_zfmisc_1(sK1,sK2)) & (k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = k2_zfmisc_1(sK1,sK2))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f21,f22])).
% 0.21/0.53  % (26101)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1))) => (((k1_xboole_0 != sK2 & k1_xboole_0 != sK1) | k1_xboole_0 != k2_zfmisc_1(sK1,sK2)) & (k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.21/0.53    inference(flattening,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.21/0.53    inference(nnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.53    inference(negated_conjecture,[],[f13])).
% 0.21/0.53  fof(f13,conjecture,(
% 0.21/0.53    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    k1_xboole_0 != k2_zfmisc_1(sK1,k1_xboole_0) | k1_xboole_0 = sK1),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f104])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k2_zfmisc_1(sK1,k1_xboole_0) | k1_xboole_0 = sK1),
% 0.21/0.53    inference(superposition,[],[f59,f100])).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 0.21/0.53    inference(subsumption_resolution,[],[f99,f39])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = k2_xboole_0(k1_tarski(k4_tarski(sK3(sK1),sK3(sK2))),k1_xboole_0)),
% 0.21/0.53    inference(resolution,[],[f94,f41])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK3(sK1),sK3(sK2)),k1_xboole_0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f93])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK3(sK1),sK3(sK2)),k1_xboole_0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2),
% 0.21/0.53    inference(superposition,[],[f85,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    k1_xboole_0 = k2_zfmisc_1(sK1,sK2) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK3(X0),sK3(X1)),k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.21/0.53    inference(resolution,[],[f82,f38])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(k4_tarski(sK3(X2),X0),k2_zfmisc_1(X2,X1)) | k1_xboole_0 = X2) )),
% 0.21/0.53    inference(resolution,[],[f80,f38])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(X2,X3) | ~r2_hidden(X0,X1) | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1))) )),
% 0.21/0.53    inference(resolution,[],[f57,f58])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X2,X0,X10,X1,X9] : (~sP0(X0,X1,X2) | ~r2_hidden(X10,X0) | ~r2_hidden(X9,X1) | r2_hidden(k4_tarski(X9,X10),X2)) )),
% 0.21/0.53    inference(equality_resolution,[],[f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X0) | ~r2_hidden(X9,X1) | ~sP0(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    k1_xboole_0 != sK2 | k1_xboole_0 != k2_zfmisc_1(sK1,k1_xboole_0)),
% 0.21/0.53    inference(inner_rewriting,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    k1_xboole_0 != sK2 | k1_xboole_0 != k2_zfmisc_1(sK1,sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (26089)------------------------------
% 0.21/0.53  % (26089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (26089)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (26089)Memory used [KB]: 6396
% 0.21/0.53  % (26089)Time elapsed: 0.114 s
% 0.21/0.53  % (26089)------------------------------
% 0.21/0.53  % (26089)------------------------------
% 0.21/0.53  % (26104)Refutation not found, incomplete strategy% (26104)------------------------------
% 0.21/0.53  % (26104)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (26104)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (26104)Memory used [KB]: 10746
% 0.21/0.53  % (26104)Time elapsed: 0.082 s
% 0.21/0.53  % (26104)------------------------------
% 0.21/0.53  % (26104)------------------------------
% 0.21/0.53  % (26081)Success in time 0.175 s
%------------------------------------------------------------------------------
