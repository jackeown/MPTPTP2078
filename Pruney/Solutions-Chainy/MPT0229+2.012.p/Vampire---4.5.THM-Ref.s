%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:31 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 143 expanded)
%              Number of leaves         :   14 (  44 expanded)
%              Depth                    :   15
%              Number of atoms          :  218 ( 397 expanded)
%              Number of equality atoms :  145 ( 294 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f115,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f99,f114])).

fof(f114,plain,(
    ~ spl3_1 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f112,f26])).

fof(f26,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( sK0 != sK1
    & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & r1_tarski(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_zfmisc_1)).

fof(f112,plain,
    ( sK0 = sK1
    | ~ spl3_1 ),
    inference(duplicate_literal_removal,[],[f111])).

fof(f111,plain,
    ( sK0 = sK1
    | sK0 = sK1
    | sK0 = sK1
    | ~ spl3_1 ),
    inference(resolution,[],[f104,f71])).

fof(f71,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f38,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f36,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f38,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).

fof(f23,plain,(
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

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f104,plain,
    ( r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl3_1 ),
    inference(superposition,[],[f70,f81])).

fof(f81,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl3_1
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f70,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f39,f46])).

fof(f39,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f99,plain,(
    ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f98])).

fof(f98,plain,
    ( $false
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f97,f27])).

fof(f27,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f97,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_2 ),
    inference(resolution,[],[f93,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f93,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_2 ),
    inference(superposition,[],[f64,f85])).

fof(f85,plain,
    ( k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl3_2
  <=> k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f64,plain,(
    ! [X1] : ~ r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f35,f48,f48])).

fof(f48,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f28,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f29,f46])).

fof(f29,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( X0 = X1
        & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

fof(f86,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f76,f83,f79])).

fof(f76,plain,
    ( k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    inference(resolution,[],[f52,f49])).

fof(f49,plain,(
    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f25,f48,f48])).

fof(f25,plain,(
    r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k3_enumset1(X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f32,f48,f48])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:09:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (14670)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.51  % (14695)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.51  % (14670)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 1.20/0.52  % (14677)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.20/0.52  % (14672)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.20/0.52  % SZS output start Proof for theBenchmark
% 1.20/0.52  fof(f115,plain,(
% 1.20/0.52    $false),
% 1.20/0.52    inference(avatar_sat_refutation,[],[f86,f99,f114])).
% 1.20/0.52  fof(f114,plain,(
% 1.20/0.52    ~spl3_1),
% 1.20/0.52    inference(avatar_contradiction_clause,[],[f113])).
% 1.20/0.52  fof(f113,plain,(
% 1.20/0.52    $false | ~spl3_1),
% 1.20/0.52    inference(subsumption_resolution,[],[f112,f26])).
% 1.20/0.52  fof(f26,plain,(
% 1.20/0.52    sK0 != sK1),
% 1.20/0.52    inference(cnf_transformation,[],[f16])).
% 1.20/0.52  fof(f16,plain,(
% 1.20/0.52    sK0 != sK1 & r1_tarski(k1_tarski(sK0),k1_tarski(sK1))),
% 1.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f15])).
% 1.20/0.52  fof(f15,plain,(
% 1.20/0.52    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.20/0.52    introduced(choice_axiom,[])).
% 1.20/0.52  fof(f12,plain,(
% 1.20/0.52    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 1.20/0.52    inference(ennf_transformation,[],[f11])).
% 1.20/0.52  fof(f11,negated_conjecture,(
% 1.20/0.52    ~! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.20/0.52    inference(negated_conjecture,[],[f10])).
% 1.20/0.52  fof(f10,conjecture,(
% 1.20/0.52    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_zfmisc_1)).
% 1.20/0.52  fof(f112,plain,(
% 1.20/0.52    sK0 = sK1 | ~spl3_1),
% 1.20/0.52    inference(duplicate_literal_removal,[],[f111])).
% 1.20/0.52  fof(f111,plain,(
% 1.20/0.52    sK0 = sK1 | sK0 = sK1 | sK0 = sK1 | ~spl3_1),
% 1.20/0.52    inference(resolution,[],[f104,f71])).
% 1.20/0.52  fof(f71,plain,(
% 1.20/0.52    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 1.20/0.52    inference(equality_resolution,[],[f61])).
% 1.20/0.52  fof(f61,plain,(
% 1.20/0.52    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 1.20/0.52    inference(definition_unfolding,[],[f38,f46])).
% 1.20/0.52  fof(f46,plain,(
% 1.20/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.20/0.52    inference(definition_unfolding,[],[f36,f37])).
% 1.20/0.52  fof(f37,plain,(
% 1.20/0.52    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f7])).
% 1.20/0.52  fof(f7,axiom,(
% 1.20/0.52    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.20/0.52  fof(f36,plain,(
% 1.20/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f6])).
% 1.20/0.52  fof(f6,axiom,(
% 1.20/0.52    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.20/0.52  fof(f38,plain,(
% 1.20/0.52    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.20/0.52    inference(cnf_transformation,[],[f24])).
% 1.20/0.52  fof(f24,plain,(
% 1.20/0.52    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).
% 1.20/0.52  fof(f23,plain,(
% 1.20/0.52    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 1.20/0.52    introduced(choice_axiom,[])).
% 1.20/0.52  fof(f22,plain,(
% 1.20/0.52    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.20/0.52    inference(rectify,[],[f21])).
% 1.20/0.52  fof(f21,plain,(
% 1.20/0.52    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.20/0.52    inference(flattening,[],[f20])).
% 1.20/0.52  fof(f20,plain,(
% 1.20/0.52    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.20/0.52    inference(nnf_transformation,[],[f14])).
% 1.20/0.52  fof(f14,plain,(
% 1.20/0.52    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.20/0.52    inference(ennf_transformation,[],[f3])).
% 1.20/0.52  fof(f3,axiom,(
% 1.20/0.52    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.20/0.52  fof(f104,plain,(
% 1.20/0.52    r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~spl3_1),
% 1.20/0.52    inference(superposition,[],[f70,f81])).
% 1.20/0.52  fof(f81,plain,(
% 1.20/0.52    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) | ~spl3_1),
% 1.20/0.52    inference(avatar_component_clause,[],[f79])).
% 1.20/0.52  fof(f79,plain,(
% 1.20/0.52    spl3_1 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_enumset1(sK1,sK1,sK1,sK1,sK1)),
% 1.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.20/0.52  fof(f70,plain,(
% 1.20/0.52    ( ! [X2,X5,X1] : (r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2))) )),
% 1.20/0.52    inference(equality_resolution,[],[f69])).
% 1.20/0.52  fof(f69,plain,(
% 1.20/0.52    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X5,X5,X5,X1,X2) != X3) )),
% 1.20/0.52    inference(equality_resolution,[],[f60])).
% 1.20/0.52  fof(f60,plain,(
% 1.20/0.52    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 1.20/0.52    inference(definition_unfolding,[],[f39,f46])).
% 1.20/0.52  fof(f39,plain,(
% 1.20/0.52    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.20/0.52    inference(cnf_transformation,[],[f24])).
% 1.20/0.52  fof(f99,plain,(
% 1.20/0.52    ~spl3_2),
% 1.20/0.52    inference(avatar_contradiction_clause,[],[f98])).
% 1.20/0.52  fof(f98,plain,(
% 1.20/0.52    $false | ~spl3_2),
% 1.20/0.52    inference(subsumption_resolution,[],[f97,f27])).
% 1.20/0.52  fof(f27,plain,(
% 1.20/0.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.20/0.52    inference(cnf_transformation,[],[f1])).
% 1.20/0.52  fof(f1,axiom,(
% 1.20/0.52    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.20/0.52  fof(f97,plain,(
% 1.20/0.52    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl3_2),
% 1.20/0.52    inference(resolution,[],[f93,f31])).
% 1.20/0.52  fof(f31,plain,(
% 1.20/0.52    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 1.20/0.52    inference(cnf_transformation,[],[f17])).
% 1.20/0.52  fof(f17,plain,(
% 1.20/0.52    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.20/0.52    inference(nnf_transformation,[],[f2])).
% 1.20/0.52  fof(f2,axiom,(
% 1.20/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.20/0.52  fof(f93,plain,(
% 1.20/0.52    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl3_2),
% 1.20/0.52    inference(superposition,[],[f64,f85])).
% 1.20/0.52  fof(f85,plain,(
% 1.20/0.52    k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | ~spl3_2),
% 1.20/0.52    inference(avatar_component_clause,[],[f83])).
% 1.20/0.52  fof(f83,plain,(
% 1.20/0.52    spl3_2 <=> k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.20/0.52  fof(f64,plain,(
% 1.20/0.52    ( ! [X1] : (~r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1))) )),
% 1.20/0.52    inference(equality_resolution,[],[f53])).
% 1.20/0.52  fof(f53,plain,(
% 1.20/0.52    ( ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1))) )),
% 1.20/0.52    inference(definition_unfolding,[],[f35,f48,f48])).
% 1.20/0.52  fof(f48,plain,(
% 1.20/0.52    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.20/0.52    inference(definition_unfolding,[],[f28,f47])).
% 1.20/0.52  fof(f47,plain,(
% 1.20/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.20/0.52    inference(definition_unfolding,[],[f29,f46])).
% 1.20/0.52  fof(f29,plain,(
% 1.20/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f5])).
% 1.20/0.52  fof(f5,axiom,(
% 1.20/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.20/0.52  fof(f28,plain,(
% 1.20/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f4])).
% 1.20/0.52  fof(f4,axiom,(
% 1.20/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.20/0.52  fof(f35,plain,(
% 1.20/0.52    ( ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.20/0.52    inference(cnf_transformation,[],[f13])).
% 1.20/0.52  fof(f13,plain,(
% 1.20/0.52    ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.20/0.52    inference(ennf_transformation,[],[f9])).
% 1.20/0.52  fof(f9,axiom,(
% 1.20/0.52    ! [X0,X1] : ~(X0 = X1 & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).
% 1.20/0.52  fof(f86,plain,(
% 1.20/0.52    spl3_1 | spl3_2),
% 1.20/0.52    inference(avatar_split_clause,[],[f76,f83,f79])).
% 1.20/0.52  fof(f76,plain,(
% 1.20/0.52    k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_enumset1(sK1,sK1,sK1,sK1,sK1)),
% 1.20/0.52    inference(resolution,[],[f52,f49])).
% 1.20/0.52  fof(f49,plain,(
% 1.20/0.52    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 1.20/0.52    inference(definition_unfolding,[],[f25,f48,f48])).
% 1.20/0.52  fof(f25,plain,(
% 1.20/0.52    r1_tarski(k1_tarski(sK0),k1_tarski(sK1))),
% 1.20/0.52    inference(cnf_transformation,[],[f16])).
% 1.20/0.52  fof(f52,plain,(
% 1.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1)) | k1_xboole_0 = X0 | k3_enumset1(X1,X1,X1,X1,X1) = X0) )),
% 1.20/0.52    inference(definition_unfolding,[],[f32,f48,f48])).
% 1.20/0.52  fof(f32,plain,(
% 1.20/0.52    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.20/0.52    inference(cnf_transformation,[],[f19])).
% 1.20/0.52  fof(f19,plain,(
% 1.20/0.52    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.20/0.52    inference(flattening,[],[f18])).
% 1.20/0.52  fof(f18,plain,(
% 1.20/0.52    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.20/0.52    inference(nnf_transformation,[],[f8])).
% 1.20/0.52  fof(f8,axiom,(
% 1.20/0.52    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.20/0.52  % SZS output end Proof for theBenchmark
% 1.20/0.52  % (14670)------------------------------
% 1.20/0.52  % (14670)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.52  % (14670)Termination reason: Refutation
% 1.20/0.52  
% 1.20/0.52  % (14670)Memory used [KB]: 10746
% 1.20/0.52  % (14670)Time elapsed: 0.105 s
% 1.20/0.52  % (14670)------------------------------
% 1.20/0.52  % (14670)------------------------------
% 1.20/0.52  % (14665)Success in time 0.158 s
%------------------------------------------------------------------------------
