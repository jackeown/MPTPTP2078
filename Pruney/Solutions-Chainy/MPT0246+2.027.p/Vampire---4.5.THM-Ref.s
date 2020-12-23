%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:48 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 277 expanded)
%              Number of leaves         :   16 (  84 expanded)
%              Depth                    :   17
%              Number of atoms          :  172 ( 761 expanded)
%              Number of equality atoms :   49 ( 419 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f110,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f103,f109])).

fof(f109,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f107,f58])).

fof(f58,plain,(
    r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f57,f31])).

fof(f31,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ! [X2] :
        ( sK1 = X2
        | ~ r2_hidden(X2,sK0) )
    & k1_xboole_0 != sK0
    & sK0 != k1_tarski(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( X1 = X2
            | ~ r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 )
   => ( ! [X2] :
          ( sK1 = X2
          | ~ r2_hidden(X2,sK0) )
      & k1_xboole_0 != sK0
      & sK0 != k1_tarski(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ~ r2_hidden(X2,X0) )
      & k1_xboole_0 != X0
      & k1_tarski(X1) != X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ~ ( X1 != X2
                & r2_hidden(X2,X0) )
          & k1_xboole_0 != X0
          & k1_tarski(X1) != X0 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f57,plain,
    ( r2_hidden(sK1,sK0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f34,f56])).

fof(f56,plain,(
    sK1 = sK2(sK0) ),
    inference(subsumption_resolution,[],[f52,f31])).

fof(f52,plain,
    ( sK1 = sK2(sK0)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f32,f34])).

fof(f32,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | sK1 = X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f107,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl5_1 ),
    inference(resolution,[],[f84,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f47])).

fof(f47,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f33,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f84,plain,
    ( r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl5_1
  <=> r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f103,plain,(
    ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f102])).

fof(f102,plain,
    ( $false
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f101,f69])).

fof(f69,plain,(
    r2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    inference(subsumption_resolution,[],[f68,f48])).

fof(f48,plain,(
    sK0 != k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f30,f47])).

fof(f30,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f68,plain,
    ( sK0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | r2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    inference(resolution,[],[f60,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f60,plain,(
    r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    inference(resolution,[],[f58,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f41,f47])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f101,plain,
    ( ~ r2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f100,f88])).

fof(f88,plain,
    ( r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl5_2
  <=> r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f100,plain,
    ( ~ r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ r2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    inference(superposition,[],[f43,f71])).

fof(f71,plain,(
    sK1 = sK4(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    inference(resolution,[],[f55,f69])).

fof(f55,plain,(
    ! [X2] :
      ( ~ r2_xboole_0(X2,sK0)
      | sK1 = sK4(X2,sK0) ) ),
    inference(resolution,[],[f32,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r2_hidden(sK4(X0,X1),X0)
        & r2_hidden(sK4(X0,X1),X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(sK4(X0,X1),X0)
        & r2_hidden(sK4(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f89,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f79,f86,f82])).

fof(f79,plain,
    ( r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
    | r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    inference(superposition,[],[f36,f72])).

fof(f72,plain,(
    sK1 = sK3(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    inference(resolution,[],[f63,f58])).

fof(f63,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | sK1 = sK3(k2_enumset1(X0,X0,X0,X0),sK0) ) ),
    inference(resolution,[],[f53,f51])).

fof(f53,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,sK0)
      | sK1 = sK3(X0,sK0) ) ),
    inference(resolution,[],[f32,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:35:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (12545)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.19/0.52  % (12544)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.19/0.53  % (12546)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.19/0.53  % (12554)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.19/0.53  % (12546)Refutation found. Thanks to Tanya!
% 1.19/0.53  % SZS status Theorem for theBenchmark
% 1.19/0.53  % (12562)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.19/0.53  % (12539)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.19/0.53  % (12538)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.19/0.54  % (12552)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.19/0.54  % (12561)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.19/0.54  % SZS output start Proof for theBenchmark
% 1.19/0.54  fof(f110,plain,(
% 1.19/0.54    $false),
% 1.19/0.54    inference(avatar_sat_refutation,[],[f89,f103,f109])).
% 1.19/0.54  fof(f109,plain,(
% 1.19/0.54    ~spl5_1),
% 1.19/0.54    inference(avatar_contradiction_clause,[],[f108])).
% 1.19/0.54  fof(f108,plain,(
% 1.19/0.54    $false | ~spl5_1),
% 1.19/0.54    inference(subsumption_resolution,[],[f107,f58])).
% 1.19/0.54  fof(f58,plain,(
% 1.19/0.54    r2_hidden(sK1,sK0)),
% 1.19/0.54    inference(subsumption_resolution,[],[f57,f31])).
% 1.19/0.54  fof(f31,plain,(
% 1.19/0.54    k1_xboole_0 != sK0),
% 1.19/0.54    inference(cnf_transformation,[],[f22])).
% 1.19/0.54  fof(f22,plain,(
% 1.19/0.54    ! [X2] : (sK1 = X2 | ~r2_hidden(X2,sK0)) & k1_xboole_0 != sK0 & sK0 != k1_tarski(sK1)),
% 1.19/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f21])).
% 1.19/0.54  fof(f21,plain,(
% 1.19/0.54    ? [X0,X1] : (! [X2] : (X1 = X2 | ~r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0) => (! [X2] : (sK1 = X2 | ~r2_hidden(X2,sK0)) & k1_xboole_0 != sK0 & sK0 != k1_tarski(sK1))),
% 1.19/0.54    introduced(choice_axiom,[])).
% 1.19/0.54  fof(f14,plain,(
% 1.19/0.54    ? [X0,X1] : (! [X2] : (X1 = X2 | ~r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.19/0.54    inference(ennf_transformation,[],[f11])).
% 1.19/0.54  fof(f11,negated_conjecture,(
% 1.19/0.54    ~! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.19/0.54    inference(negated_conjecture,[],[f10])).
% 1.19/0.54  fof(f10,conjecture,(
% 1.19/0.54    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 1.19/0.54  fof(f57,plain,(
% 1.19/0.54    r2_hidden(sK1,sK0) | k1_xboole_0 = sK0),
% 1.19/0.54    inference(superposition,[],[f34,f56])).
% 1.19/0.54  fof(f56,plain,(
% 1.19/0.54    sK1 = sK2(sK0)),
% 1.19/0.54    inference(subsumption_resolution,[],[f52,f31])).
% 1.19/0.54  fof(f52,plain,(
% 1.19/0.54    sK1 = sK2(sK0) | k1_xboole_0 = sK0),
% 1.19/0.54    inference(resolution,[],[f32,f34])).
% 1.19/0.54  fof(f32,plain,(
% 1.19/0.54    ( ! [X2] : (~r2_hidden(X2,sK0) | sK1 = X2) )),
% 1.19/0.54    inference(cnf_transformation,[],[f22])).
% 1.19/0.54  fof(f34,plain,(
% 1.19/0.54    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 1.19/0.54    inference(cnf_transformation,[],[f24])).
% 1.19/0.54  fof(f24,plain,(
% 1.19/0.54    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 1.19/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f23])).
% 1.19/0.54  fof(f23,plain,(
% 1.19/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 1.19/0.54    introduced(choice_axiom,[])).
% 1.19/0.54  fof(f15,plain,(
% 1.19/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.19/0.54    inference(ennf_transformation,[],[f4])).
% 1.19/0.54  fof(f4,axiom,(
% 1.19/0.54    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.19/0.54  fof(f107,plain,(
% 1.19/0.54    ~r2_hidden(sK1,sK0) | ~spl5_1),
% 1.19/0.54    inference(resolution,[],[f84,f51])).
% 1.19/0.54  fof(f51,plain,(
% 1.19/0.54    ( ! [X0,X1] : (~r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.19/0.54    inference(definition_unfolding,[],[f44,f47])).
% 1.19/0.54  fof(f47,plain,(
% 1.19/0.54    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.19/0.54    inference(definition_unfolding,[],[f33,f46])).
% 1.19/0.54  fof(f46,plain,(
% 1.19/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.19/0.54    inference(definition_unfolding,[],[f35,f45])).
% 1.19/0.54  fof(f45,plain,(
% 1.19/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.19/0.54    inference(cnf_transformation,[],[f7])).
% 1.19/0.54  fof(f7,axiom,(
% 1.19/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.19/0.54  fof(f35,plain,(
% 1.19/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.19/0.54    inference(cnf_transformation,[],[f6])).
% 1.19/0.54  fof(f6,axiom,(
% 1.19/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.19/0.54  fof(f33,plain,(
% 1.19/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.19/0.54    inference(cnf_transformation,[],[f5])).
% 1.19/0.54  fof(f5,axiom,(
% 1.19/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.19/0.54  fof(f44,plain,(
% 1.19/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 1.19/0.54    inference(cnf_transformation,[],[f20])).
% 1.19/0.54  fof(f20,plain,(
% 1.19/0.54    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 1.19/0.54    inference(ennf_transformation,[],[f9])).
% 1.19/0.54  fof(f9,axiom,(
% 1.19/0.54    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 1.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 1.19/0.54  fof(f84,plain,(
% 1.19/0.54    r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | ~spl5_1),
% 1.19/0.54    inference(avatar_component_clause,[],[f82])).
% 1.19/0.54  fof(f82,plain,(
% 1.19/0.54    spl5_1 <=> r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 1.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.19/0.54  fof(f103,plain,(
% 1.19/0.54    ~spl5_2),
% 1.19/0.54    inference(avatar_contradiction_clause,[],[f102])).
% 1.19/0.54  fof(f102,plain,(
% 1.19/0.54    $false | ~spl5_2),
% 1.19/0.54    inference(subsumption_resolution,[],[f101,f69])).
% 1.19/0.54  fof(f69,plain,(
% 1.19/0.54    r2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 1.19/0.54    inference(subsumption_resolution,[],[f68,f48])).
% 1.19/0.54  fof(f48,plain,(
% 1.19/0.54    sK0 != k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.19/0.54    inference(definition_unfolding,[],[f30,f47])).
% 1.19/0.54  fof(f30,plain,(
% 1.19/0.54    sK0 != k1_tarski(sK1)),
% 1.19/0.54    inference(cnf_transformation,[],[f22])).
% 1.19/0.54  fof(f68,plain,(
% 1.19/0.54    sK0 = k2_enumset1(sK1,sK1,sK1,sK1) | r2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 1.19/0.54    inference(resolution,[],[f60,f39])).
% 1.19/0.54  fof(f39,plain,(
% 1.19/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 1.19/0.54    inference(cnf_transformation,[],[f18])).
% 1.19/0.54  fof(f18,plain,(
% 1.19/0.54    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 1.19/0.54    inference(flattening,[],[f17])).
% 1.19/0.54  fof(f17,plain,(
% 1.19/0.54    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 1.19/0.54    inference(ennf_transformation,[],[f13])).
% 1.19/0.54  fof(f13,plain,(
% 1.19/0.54    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 1.19/0.54    inference(unused_predicate_definition_removal,[],[f1])).
% 1.19/0.54  fof(f1,axiom,(
% 1.19/0.54    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 1.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 1.19/0.54  fof(f60,plain,(
% 1.19/0.54    r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 1.19/0.54    inference(resolution,[],[f58,f49])).
% 1.19/0.54  fof(f49,plain,(
% 1.19/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)) )),
% 1.19/0.54    inference(definition_unfolding,[],[f41,f47])).
% 1.19/0.54  fof(f41,plain,(
% 1.19/0.54    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.19/0.54    inference(cnf_transformation,[],[f27])).
% 1.19/0.54  fof(f27,plain,(
% 1.19/0.54    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.19/0.54    inference(nnf_transformation,[],[f8])).
% 1.19/0.54  fof(f8,axiom,(
% 1.19/0.54    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.19/0.54  fof(f101,plain,(
% 1.19/0.54    ~r2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | ~spl5_2),
% 1.19/0.54    inference(subsumption_resolution,[],[f100,f88])).
% 1.19/0.54  fof(f88,plain,(
% 1.19/0.54    r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl5_2),
% 1.19/0.54    inference(avatar_component_clause,[],[f86])).
% 1.19/0.54  fof(f86,plain,(
% 1.19/0.54    spl5_2 <=> r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.19/0.54  fof(f100,plain,(
% 1.19/0.54    ~r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) | ~r2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 1.19/0.54    inference(superposition,[],[f43,f71])).
% 1.19/0.54  fof(f71,plain,(
% 1.19/0.54    sK1 = sK4(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 1.19/0.54    inference(resolution,[],[f55,f69])).
% 1.19/0.54  fof(f55,plain,(
% 1.19/0.54    ( ! [X2] : (~r2_xboole_0(X2,sK0) | sK1 = sK4(X2,sK0)) )),
% 1.19/0.54    inference(resolution,[],[f32,f42])).
% 1.19/0.54  fof(f42,plain,(
% 1.19/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | ~r2_xboole_0(X0,X1)) )),
% 1.19/0.54    inference(cnf_transformation,[],[f29])).
% 1.19/0.54  fof(f29,plain,(
% 1.19/0.54    ! [X0,X1] : ((~r2_hidden(sK4(X0,X1),X0) & r2_hidden(sK4(X0,X1),X1)) | ~r2_xboole_0(X0,X1))),
% 1.19/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f28])).
% 1.19/0.54  fof(f28,plain,(
% 1.19/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) => (~r2_hidden(sK4(X0,X1),X0) & r2_hidden(sK4(X0,X1),X1)))),
% 1.19/0.54    introduced(choice_axiom,[])).
% 1.19/0.54  fof(f19,plain,(
% 1.19/0.54    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 1.19/0.54    inference(ennf_transformation,[],[f3])).
% 1.19/0.54  fof(f3,axiom,(
% 1.19/0.54    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 1.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).
% 1.19/0.54  fof(f43,plain,(
% 1.19/0.54    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X0) | ~r2_xboole_0(X0,X1)) )),
% 1.19/0.54    inference(cnf_transformation,[],[f29])).
% 1.19/0.54  fof(f89,plain,(
% 1.19/0.54    spl5_1 | spl5_2),
% 1.19/0.54    inference(avatar_split_clause,[],[f79,f86,f82])).
% 1.19/0.54  fof(f79,plain,(
% 1.19/0.54    r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) | r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 1.19/0.54    inference(superposition,[],[f36,f72])).
% 1.19/0.54  fof(f72,plain,(
% 1.19/0.54    sK1 = sK3(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 1.19/0.54    inference(resolution,[],[f63,f58])).
% 1.19/0.54  fof(f63,plain,(
% 1.19/0.54    ( ! [X0] : (~r2_hidden(X0,sK0) | sK1 = sK3(k2_enumset1(X0,X0,X0,X0),sK0)) )),
% 1.19/0.54    inference(resolution,[],[f53,f51])).
% 1.19/0.54  fof(f53,plain,(
% 1.19/0.54    ( ! [X0] : (r1_xboole_0(X0,sK0) | sK1 = sK3(X0,sK0)) )),
% 1.19/0.54    inference(resolution,[],[f32,f37])).
% 1.19/0.54  fof(f37,plain,(
% 1.19/0.54    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.19/0.54    inference(cnf_transformation,[],[f26])).
% 1.19/0.54  fof(f26,plain,(
% 1.19/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.19/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f25])).
% 1.19/0.54  fof(f25,plain,(
% 1.19/0.54    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.19/0.54    introduced(choice_axiom,[])).
% 1.19/0.54  fof(f16,plain,(
% 1.19/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.19/0.54    inference(ennf_transformation,[],[f12])).
% 1.19/0.54  fof(f12,plain,(
% 1.19/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.19/0.54    inference(rectify,[],[f2])).
% 1.19/0.54  fof(f2,axiom,(
% 1.19/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.19/0.54  fof(f36,plain,(
% 1.19/0.54    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.19/0.54    inference(cnf_transformation,[],[f26])).
% 1.19/0.54  % SZS output end Proof for theBenchmark
% 1.19/0.54  % (12546)------------------------------
% 1.19/0.54  % (12546)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.54  % (12546)Termination reason: Refutation
% 1.19/0.54  
% 1.19/0.54  % (12546)Memory used [KB]: 10746
% 1.19/0.54  % (12546)Time elapsed: 0.108 s
% 1.19/0.54  % (12546)------------------------------
% 1.19/0.54  % (12546)------------------------------
% 1.19/0.54  % (12543)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.19/0.54  % (12537)Success in time 0.17 s
%------------------------------------------------------------------------------
