%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   54 (  85 expanded)
%              Number of leaves         :   14 (  32 expanded)
%              Depth                    :   13
%              Number of atoms          :  215 ( 331 expanded)
%              Number of equality atoms :   62 (  94 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f142,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f59,f81,f87,f140,f141])).

fof(f141,plain,
    ( sK0 != sK2(sK1,k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))
    | r2_hidden(sK0,k2_tarski(sK0,sK0))
    | ~ r2_hidden(sK2(sK1,k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f140,plain,
    ( ~ spl4_5
    | ~ spl4_1
    | spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f135,f84,f56,f51,f137])).

fof(f137,plain,
    ( spl4_5
  <=> r2_hidden(sK0,k2_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f51,plain,
    ( spl4_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f56,plain,
    ( spl4_2
  <=> k2_tarski(sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f84,plain,
    ( spl4_4
  <=> sK0 = sK2(sK1,k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f135,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k2_tarski(sK0,sK0))
    | spl4_2
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f134,f86])).

fof(f86,plain,
    ( sK0 = sK2(sK1,k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f134,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK0))
    | ~ r2_hidden(sK2(sK1,k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)),sK1)
    | spl4_2
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f133,f86])).

fof(f133,plain,
    ( ~ r2_hidden(sK2(sK1,k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))
    | ~ r2_hidden(sK2(sK1,k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)),sK1)
    | spl4_2 ),
    inference(duplicate_literal_removal,[],[f132])).

fof(f132,plain,
    ( ~ r2_hidden(sK2(sK1,k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))
    | ~ r2_hidden(sK2(sK1,k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)),sK1)
    | ~ r2_hidden(sK2(sK1,k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))
    | spl4_2 ),
    inference(equality_resolution,[],[f121])).

fof(f121,plain,
    ( ! [X0] :
        ( k2_tarski(sK0,sK0) != X0
        | ~ r2_hidden(sK2(sK1,k2_tarski(sK0,sK0),X0),k2_tarski(sK0,sK0))
        | ~ r2_hidden(sK2(sK1,k2_tarski(sK0,sK0),X0),sK1)
        | ~ r2_hidden(sK2(sK1,k2_tarski(sK0,sK0),X0),X0) )
    | spl4_2 ),
    inference(superposition,[],[f58,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f26,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f13])).

fof(f13,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f58,plain,
    ( k2_tarski(sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK0,sK0)))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f87,plain,
    ( spl4_4
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f82,f78,f84])).

fof(f78,plain,
    ( spl4_3
  <=> r2_hidden(sK2(sK1,k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f82,plain,
    ( sK0 = sK2(sK1,k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))
    | ~ spl4_3 ),
    inference(resolution,[],[f80,f49])).

fof(f49,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_tarski(X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f27,f32])).

fof(f32,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f17])).

fof(f17,plain,(
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

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f80,plain,
    ( r2_hidden(sK2(sK1,k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f81,plain,
    ( spl4_3
    | spl4_2 ),
    inference(avatar_split_clause,[],[f76,f56,f78])).

fof(f76,plain,
    ( r2_hidden(sK2(sK1,k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))
    | spl4_2 ),
    inference(duplicate_literal_removal,[],[f75])).

fof(f75,plain,
    ( r2_hidden(sK2(sK1,k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))
    | r2_hidden(sK2(sK1,k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))
    | spl4_2 ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,
    ( ! [X0] :
        ( k2_tarski(sK0,sK0) != X0
        | r2_hidden(sK2(sK1,k2_tarski(sK0,sK0),X0),k2_tarski(sK0,sK0))
        | r2_hidden(sK2(sK1,k2_tarski(sK0,sK0),X0),X0) )
    | spl4_2 ),
    inference(superposition,[],[f58,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f25,f31])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f59,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f33,f56])).

fof(f33,plain,(
    k2_tarski(sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK0,sK0))) ),
    inference(definition_unfolding,[],[f20,f32,f31,f32])).

fof(f20,plain,(
    k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k3_xboole_0(X1,k1_tarski(X0))
        & r2_hidden(X0,X1) )
   => ( k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k3_xboole_0(X1,k1_tarski(X0))
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_zfmisc_1)).

fof(f54,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f19,f51])).

fof(f19,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:31:01 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (30104)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.51  % (30096)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.51  % (30088)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.52  % (30085)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (30086)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (30084)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.52  % (30083)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  % (30081)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (30104)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f142,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f54,f59,f81,f87,f140,f141])).
% 0.22/0.52  fof(f141,plain,(
% 0.22/0.52    sK0 != sK2(sK1,k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)) | r2_hidden(sK0,k2_tarski(sK0,sK0)) | ~r2_hidden(sK2(sK1,k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))),
% 0.22/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.52  fof(f140,plain,(
% 0.22/0.52    ~spl4_5 | ~spl4_1 | spl4_2 | ~spl4_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f135,f84,f56,f51,f137])).
% 0.22/0.52  fof(f137,plain,(
% 0.22/0.52    spl4_5 <=> r2_hidden(sK0,k2_tarski(sK0,sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    spl4_1 <=> r2_hidden(sK0,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    spl4_2 <=> k2_tarski(sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK0,sK0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    spl4_4 <=> sK0 = sK2(sK1,k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.52  fof(f135,plain,(
% 0.22/0.52    ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k2_tarski(sK0,sK0)) | (spl4_2 | ~spl4_4)),
% 0.22/0.52    inference(forward_demodulation,[],[f134,f86])).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    sK0 = sK2(sK1,k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)) | ~spl4_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f84])).
% 0.22/0.52  fof(f134,plain,(
% 0.22/0.52    ~r2_hidden(sK0,k2_tarski(sK0,sK0)) | ~r2_hidden(sK2(sK1,k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)),sK1) | (spl4_2 | ~spl4_4)),
% 0.22/0.52    inference(forward_demodulation,[],[f133,f86])).
% 0.22/0.52  fof(f133,plain,(
% 0.22/0.52    ~r2_hidden(sK2(sK1,k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) | ~r2_hidden(sK2(sK1,k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)),sK1) | spl4_2),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f132])).
% 0.22/0.52  fof(f132,plain,(
% 0.22/0.52    ~r2_hidden(sK2(sK1,k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) | ~r2_hidden(sK2(sK1,k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)),sK1) | ~r2_hidden(sK2(sK1,k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) | spl4_2),
% 0.22/0.52    inference(equality_resolution,[],[f121])).
% 0.22/0.52  fof(f121,plain,(
% 0.22/0.52    ( ! [X0] : (k2_tarski(sK0,sK0) != X0 | ~r2_hidden(sK2(sK1,k2_tarski(sK0,sK0),X0),k2_tarski(sK0,sK0)) | ~r2_hidden(sK2(sK1,k2_tarski(sK0,sK0),X0),sK1) | ~r2_hidden(sK2(sK1,k2_tarski(sK0,sK0),X0),X0)) ) | spl4_2),
% 0.22/0.52    inference(superposition,[],[f58,f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f26,f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.52    inference(rectify,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.52    inference(flattening,[],[f10])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.52    inference(nnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    k2_tarski(sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK0,sK0))) | spl4_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f56])).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    spl4_4 | ~spl4_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f82,f78,f84])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    spl4_3 <=> r2_hidden(sK2(sK1,k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    sK0 = sK2(sK1,k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)) | ~spl4_3),
% 0.22/0.52    inference(resolution,[],[f80,f49])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    ( ! [X0,X3] : (~r2_hidden(X3,k2_tarski(X0,X0)) | X0 = X3) )),
% 0.22/0.52    inference(equality_resolution,[],[f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 0.22/0.52    inference(definition_unfolding,[],[f27,f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.52    inference(rectify,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    r2_hidden(sK2(sK1,k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) | ~spl4_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f78])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    spl4_3 | spl4_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f76,f56,f78])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    r2_hidden(sK2(sK1,k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) | spl4_2),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f75])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    r2_hidden(sK2(sK1,k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) | r2_hidden(sK2(sK1,k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) | spl4_2),
% 0.22/0.52    inference(equality_resolution,[],[f68])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    ( ! [X0] : (k2_tarski(sK0,sK0) != X0 | r2_hidden(sK2(sK1,k2_tarski(sK0,sK0),X0),k2_tarski(sK0,sK0)) | r2_hidden(sK2(sK1,k2_tarski(sK0,sK0),X0),X0)) ) | spl4_2),
% 0.22/0.52    inference(superposition,[],[f58,f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f25,f31])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ~spl4_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f33,f56])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    k2_tarski(sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK0,sK0)))),
% 0.22/0.52    inference(definition_unfolding,[],[f20,f32,f31,f32])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0))),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,plain,(
% 0.22/0.52    k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0)) & r2_hidden(sK0,sK1)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f8])).
% 0.22/0.52  fof(f8,plain,(
% 0.22/0.52    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(X1,k1_tarski(X0)) & r2_hidden(X0,X1)) => (k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0)) & r2_hidden(sK0,sK1))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f7,plain,(
% 0.22/0.52    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(X1,k1_tarski(X0)) & r2_hidden(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 0.22/0.52    inference(negated_conjecture,[],[f5])).
% 0.22/0.52  fof(f5,conjecture,(
% 0.22/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_zfmisc_1)).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    spl4_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f19,f51])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    r2_hidden(sK0,sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (30104)------------------------------
% 0.22/0.52  % (30104)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (30104)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (30104)Memory used [KB]: 10746
% 0.22/0.52  % (30104)Time elapsed: 0.063 s
% 0.22/0.52  % (30104)------------------------------
% 0.22/0.52  % (30104)------------------------------
% 0.22/0.53  % (30080)Success in time 0.159 s
%------------------------------------------------------------------------------
