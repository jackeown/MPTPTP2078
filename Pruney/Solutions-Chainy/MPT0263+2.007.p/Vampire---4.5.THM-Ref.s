%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:12 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 115 expanded)
%              Number of leaves         :   15 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :  163 ( 259 expanded)
%              Number of equality atoms :   57 ( 100 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f556,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f131,f138,f324,f490,f552])).

fof(f552,plain,
    ( ~ spl7_2
    | spl7_3
    | ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f551])).

fof(f551,plain,
    ( $false
    | ~ spl7_2
    | spl7_3
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f538,f323])).

fof(f323,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | spl7_3 ),
    inference(avatar_component_clause,[],[f321])).

% (4300)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
fof(f321,plain,
    ( spl7_3
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f538,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f412,f501])).

fof(f501,plain,
    ( sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f489,f115])).

% (4314)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
fof(f115,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f69,f90])).

fof(f90,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f55,f89])).

fof(f89,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f57,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f55,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).

fof(f38,plain,(
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

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f489,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f487])).

fof(f487,plain,
    ( spl7_6
  <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f412,plain,
    ( k2_enumset1(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) = k4_xboole_0(k2_enumset1(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),k4_xboole_0(k2_enumset1(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),sK1))
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f137,f137,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | k2_enumset1(X0,X0,X0,X2) = k4_xboole_0(k2_enumset1(X0,X0,X0,X2),k4_xboole_0(k2_enumset1(X0,X0,X0,X2),X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f74,f89,f59,f89])).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_zfmisc_1)).

fof(f137,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl7_2
  <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f490,plain,
    ( spl7_6
    | spl7_1 ),
    inference(avatar_split_clause,[],[f132,f128,f487])).

fof(f128,plain,
    ( spl7_1
  <=> r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f132,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0))
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f130,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
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

fof(f130,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f128])).

fof(f324,plain,(
    ~ spl7_3 ),
    inference(avatar_split_clause,[],[f91,f321])).

fof(f91,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f51,f90,f59,f90])).

fof(f51,plain,(
    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)
    & ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1)
        & ~ r1_xboole_0(k1_tarski(X0),X1) )
   => ( k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)
      & ~ r1_xboole_0(k1_tarski(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1)
      & ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)
        | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).

fof(f138,plain,
    ( spl7_2
    | spl7_1 ),
    inference(avatar_split_clause,[],[f133,f128,f135])).

fof(f133,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK1)
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f130,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f131,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f92,f128])).

fof(f92,plain,(
    ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f50,f90])).

fof(f50,plain,(
    ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n004.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:32:23 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.51  % (4293)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.16/0.52  % (4309)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.16/0.52  % (4301)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.16/0.52  % (4292)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.16/0.53  % (4291)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.16/0.53  % (4297)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.28/0.54  % (4294)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.28/0.54  % (4295)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.28/0.54  % (4316)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.28/0.54  % (4315)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.28/0.55  % (4316)Refutation not found, incomplete strategy% (4316)------------------------------
% 1.28/0.55  % (4316)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.55  % (4316)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.55  
% 1.28/0.55  % (4316)Memory used [KB]: 6268
% 1.28/0.55  % (4316)Time elapsed: 0.127 s
% 1.28/0.55  % (4316)------------------------------
% 1.28/0.55  % (4316)------------------------------
% 1.28/0.55  % (4315)Refutation not found, incomplete strategy% (4315)------------------------------
% 1.28/0.55  % (4315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.55  % (4315)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.55  
% 1.28/0.55  % (4315)Memory used [KB]: 6268
% 1.28/0.55  % (4315)Time elapsed: 0.127 s
% 1.28/0.55  % (4315)------------------------------
% 1.28/0.55  % (4315)------------------------------
% 1.28/0.55  % (4302)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.28/0.55  % (4289)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.28/0.55  % (4298)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.28/0.55  % (4317)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.28/0.55  % (4318)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.28/0.55  % (4307)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.28/0.55  % (4307)Refutation not found, incomplete strategy% (4307)------------------------------
% 1.28/0.55  % (4307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.55  % (4307)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.55  
% 1.28/0.55  % (4307)Memory used [KB]: 1663
% 1.28/0.55  % (4307)Time elapsed: 0.140 s
% 1.28/0.55  % (4307)------------------------------
% 1.28/0.55  % (4307)------------------------------
% 1.28/0.55  % (4299)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.28/0.56  % (4308)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.28/0.56  % (4310)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.28/0.56  % (4290)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.28/0.56  % (4311)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.28/0.56  % (4305)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.28/0.56  % (4305)Refutation not found, incomplete strategy% (4305)------------------------------
% 1.28/0.56  % (4305)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.56  % (4305)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.56  
% 1.28/0.56  % (4305)Memory used [KB]: 10618
% 1.28/0.56  % (4305)Time elapsed: 0.141 s
% 1.28/0.56  % (4305)------------------------------
% 1.28/0.56  % (4305)------------------------------
% 1.28/0.56  % (4313)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.28/0.56  % (4309)Refutation found. Thanks to Tanya!
% 1.28/0.56  % SZS status Theorem for theBenchmark
% 1.28/0.56  % SZS output start Proof for theBenchmark
% 1.28/0.56  fof(f556,plain,(
% 1.28/0.56    $false),
% 1.28/0.56    inference(avatar_sat_refutation,[],[f131,f138,f324,f490,f552])).
% 1.28/0.56  fof(f552,plain,(
% 1.28/0.56    ~spl7_2 | spl7_3 | ~spl7_6),
% 1.28/0.56    inference(avatar_contradiction_clause,[],[f551])).
% 1.28/0.56  fof(f551,plain,(
% 1.28/0.56    $false | (~spl7_2 | spl7_3 | ~spl7_6)),
% 1.28/0.56    inference(subsumption_resolution,[],[f538,f323])).
% 1.28/0.56  fof(f323,plain,(
% 1.28/0.56    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | spl7_3),
% 1.28/0.56    inference(avatar_component_clause,[],[f321])).
% 1.28/0.56  % (4300)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.28/0.56  fof(f321,plain,(
% 1.28/0.56    spl7_3 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))),
% 1.28/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.28/0.56  fof(f538,plain,(
% 1.28/0.56    k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | (~spl7_2 | ~spl7_6)),
% 1.28/0.56    inference(backward_demodulation,[],[f412,f501])).
% 1.28/0.56  fof(f501,plain,(
% 1.28/0.56    sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl7_6),
% 1.28/0.56    inference(unit_resulting_resolution,[],[f489,f115])).
% 1.28/0.56  % (4314)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.28/0.56  fof(f115,plain,(
% 1.28/0.56    ( ! [X0,X3] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) | X0 = X3) )),
% 1.28/0.56    inference(equality_resolution,[],[f103])).
% 1.28/0.56  fof(f103,plain,(
% 1.28/0.56    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.28/0.56    inference(definition_unfolding,[],[f69,f90])).
% 1.28/0.56  fof(f90,plain,(
% 1.28/0.56    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.28/0.56    inference(definition_unfolding,[],[f55,f89])).
% 1.28/0.56  fof(f89,plain,(
% 1.28/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.28/0.56    inference(definition_unfolding,[],[f57,f73])).
% 1.28/0.56  fof(f73,plain,(
% 1.28/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.28/0.56    inference(cnf_transformation,[],[f16])).
% 1.28/0.56  fof(f16,axiom,(
% 1.28/0.56    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.28/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.28/0.56  fof(f57,plain,(
% 1.28/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.28/0.56    inference(cnf_transformation,[],[f15])).
% 1.28/0.56  fof(f15,axiom,(
% 1.28/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.28/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.28/0.56  fof(f55,plain,(
% 1.28/0.56    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.28/0.56    inference(cnf_transformation,[],[f14])).
% 1.28/0.56  fof(f14,axiom,(
% 1.28/0.56    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.28/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.28/0.56  fof(f69,plain,(
% 1.28/0.56    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.28/0.56    inference(cnf_transformation,[],[f39])).
% 1.28/0.56  fof(f39,plain,(
% 1.28/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.28/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).
% 1.28/0.56  fof(f38,plain,(
% 1.28/0.56    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 1.28/0.56    introduced(choice_axiom,[])).
% 1.28/0.56  fof(f37,plain,(
% 1.28/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.28/0.56    inference(rectify,[],[f36])).
% 1.28/0.56  fof(f36,plain,(
% 1.28/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.28/0.56    inference(nnf_transformation,[],[f13])).
% 1.28/0.56  fof(f13,axiom,(
% 1.28/0.56    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.28/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.28/0.56  fof(f489,plain,(
% 1.28/0.56    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl7_6),
% 1.28/0.56    inference(avatar_component_clause,[],[f487])).
% 1.28/0.56  fof(f487,plain,(
% 1.28/0.56    spl7_6 <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.28/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.28/0.56  fof(f412,plain,(
% 1.28/0.56    k2_enumset1(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) = k4_xboole_0(k2_enumset1(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),k4_xboole_0(k2_enumset1(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),sK1)) | ~spl7_2),
% 1.28/0.56    inference(unit_resulting_resolution,[],[f137,f137,f104])).
% 1.28/0.56  fof(f104,plain,(
% 1.28/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | k2_enumset1(X0,X0,X0,X2) = k4_xboole_0(k2_enumset1(X0,X0,X0,X2),k4_xboole_0(k2_enumset1(X0,X0,X0,X2),X1)) | ~r2_hidden(X0,X1)) )),
% 1.28/0.56    inference(definition_unfolding,[],[f74,f89,f59,f89])).
% 1.28/0.56  fof(f59,plain,(
% 1.28/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.28/0.56    inference(cnf_transformation,[],[f9])).
% 1.28/0.56  fof(f9,axiom,(
% 1.28/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.28/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.28/0.56  fof(f74,plain,(
% 1.28/0.56    ( ! [X2,X0,X1] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 1.28/0.56    inference(cnf_transformation,[],[f26])).
% 1.28/0.56  fof(f26,plain,(
% 1.28/0.56    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1))),
% 1.28/0.56    inference(flattening,[],[f25])).
% 1.28/0.56  fof(f25,plain,(
% 1.28/0.56    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | (~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)))),
% 1.28/0.56    inference(ennf_transformation,[],[f17])).
% 1.28/0.56  fof(f17,axiom,(
% 1.28/0.56    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1))),
% 1.28/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_zfmisc_1)).
% 1.28/0.56  fof(f137,plain,(
% 1.28/0.56    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK1) | ~spl7_2),
% 1.28/0.56    inference(avatar_component_clause,[],[f135])).
% 1.28/0.56  fof(f135,plain,(
% 1.28/0.56    spl7_2 <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK1)),
% 1.28/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.28/0.56  fof(f490,plain,(
% 1.28/0.56    spl7_6 | spl7_1),
% 1.28/0.56    inference(avatar_split_clause,[],[f132,f128,f487])).
% 1.28/0.56  fof(f128,plain,(
% 1.28/0.56    spl7_1 <=> r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.28/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.28/0.56  fof(f132,plain,(
% 1.28/0.56    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_enumset1(sK0,sK0,sK0,sK0)) | spl7_1),
% 1.28/0.56    inference(unit_resulting_resolution,[],[f130,f62])).
% 1.28/0.56  fof(f62,plain,(
% 1.28/0.56    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.28/0.56    inference(cnf_transformation,[],[f33])).
% 1.28/0.56  fof(f33,plain,(
% 1.28/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.28/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f32])).
% 1.28/0.56  fof(f32,plain,(
% 1.28/0.56    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.28/0.56    introduced(choice_axiom,[])).
% 1.28/0.56  fof(f24,plain,(
% 1.28/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.28/0.56    inference(ennf_transformation,[],[f21])).
% 1.28/0.56  fof(f21,plain,(
% 1.28/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.28/0.56    inference(rectify,[],[f4])).
% 1.28/0.56  fof(f4,axiom,(
% 1.28/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.28/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.28/0.56  fof(f130,plain,(
% 1.28/0.56    ~r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | spl7_1),
% 1.28/0.56    inference(avatar_component_clause,[],[f128])).
% 1.28/0.56  fof(f324,plain,(
% 1.28/0.56    ~spl7_3),
% 1.28/0.56    inference(avatar_split_clause,[],[f91,f321])).
% 1.28/0.56  fof(f91,plain,(
% 1.28/0.56    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))),
% 1.28/0.56    inference(definition_unfolding,[],[f51,f90,f59,f90])).
% 1.28/0.56  fof(f51,plain,(
% 1.28/0.56    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)),
% 1.28/0.56    inference(cnf_transformation,[],[f29])).
% 1.28/0.56  fof(f29,plain,(
% 1.28/0.56    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) & ~r1_xboole_0(k1_tarski(sK0),sK1)),
% 1.28/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f28])).
% 1.28/0.56  fof(f28,plain,(
% 1.28/0.56    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1) & ~r1_xboole_0(k1_tarski(X0),X1)) => (k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) & ~r1_xboole_0(k1_tarski(sK0),sK1))),
% 1.28/0.56    introduced(choice_axiom,[])).
% 1.28/0.56  fof(f22,plain,(
% 1.28/0.56    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1) & ~r1_xboole_0(k1_tarski(X0),X1))),
% 1.28/0.56    inference(ennf_transformation,[],[f19])).
% 1.28/0.56  fof(f19,negated_conjecture,(
% 1.28/0.56    ~! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1))),
% 1.28/0.56    inference(negated_conjecture,[],[f18])).
% 1.28/0.56  fof(f18,conjecture,(
% 1.28/0.56    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1))),
% 1.28/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).
% 1.28/0.56  fof(f138,plain,(
% 1.28/0.56    spl7_2 | spl7_1),
% 1.28/0.56    inference(avatar_split_clause,[],[f133,f128,f135])).
% 1.28/0.56  fof(f133,plain,(
% 1.28/0.56    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK1) | spl7_1),
% 1.28/0.56    inference(unit_resulting_resolution,[],[f130,f63])).
% 1.28/0.56  fof(f63,plain,(
% 1.28/0.56    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.28/0.56    inference(cnf_transformation,[],[f33])).
% 1.28/0.56  fof(f131,plain,(
% 1.28/0.56    ~spl7_1),
% 1.28/0.56    inference(avatar_split_clause,[],[f92,f128])).
% 1.28/0.56  fof(f92,plain,(
% 1.28/0.56    ~r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.28/0.56    inference(definition_unfolding,[],[f50,f90])).
% 1.28/0.56  fof(f50,plain,(
% 1.28/0.56    ~r1_xboole_0(k1_tarski(sK0),sK1)),
% 1.28/0.56    inference(cnf_transformation,[],[f29])).
% 1.28/0.56  % SZS output end Proof for theBenchmark
% 1.28/0.56  % (4309)------------------------------
% 1.28/0.56  % (4309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.56  % (4309)Termination reason: Refutation
% 1.28/0.56  
% 1.28/0.56  % (4309)Memory used [KB]: 11257
% 1.28/0.56  % (4309)Time elapsed: 0.117 s
% 1.28/0.56  % (4309)------------------------------
% 1.28/0.56  % (4309)------------------------------
% 1.28/0.56  % (4303)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.28/0.56  % (4288)Success in time 0.196 s
%------------------------------------------------------------------------------
