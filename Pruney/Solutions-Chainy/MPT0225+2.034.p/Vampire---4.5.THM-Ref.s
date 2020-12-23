%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:10 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 115 expanded)
%              Number of leaves         :   10 (  36 expanded)
%              Depth                    :   16
%              Number of atoms          :  228 ( 657 expanded)
%              Number of equality atoms :   88 ( 210 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f159,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f51,f117,f133,f140,f158])).

fof(f158,plain,(
    ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f40,f146])).

fof(f146,plain,
    ( ! [X4] : ~ r2_hidden(X4,k1_tarski(sK0))
    | ~ spl4_4 ),
    inference(duplicate_literal_removal,[],[f145])).

fof(f145,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_tarski(sK0))
        | ~ r2_hidden(X4,k1_tarski(sK0)) )
    | ~ spl4_4 ),
    inference(superposition,[],[f37,f139])).

fof(f139,plain,
    ( k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl4_4
  <=> k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f37,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f15])).

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f40,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f19])).

fof(f19,plain,(
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

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f140,plain,
    ( spl4_4
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f135,f47,f43,f137])).

fof(f43,plain,
    ( spl4_1
  <=> k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f47,plain,
    ( spl4_2
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f135,plain,
    ( k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f44,f49])).

fof(f49,plain,
    ( sK0 = sK1
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f44,plain,
    ( k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f133,plain,
    ( spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f129,f114,f47])).

fof(f114,plain,
    ( spl4_3
  <=> r2_hidden(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f129,plain,
    ( sK0 = sK1
    | ~ spl4_3 ),
    inference(resolution,[],[f116,f41])).

fof(f41,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f116,plain,
    ( r2_hidden(sK1,k1_tarski(sK0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f114])).

fof(f117,plain,
    ( spl4_3
    | spl4_1 ),
    inference(avatar_split_clause,[],[f112,f43,f114])).

fof(f112,plain,
    ( r2_hidden(sK1,k1_tarski(sK0))
    | spl4_1 ),
    inference(trivial_inequality_removal,[],[f106])).

fof(f106,plain,
    ( k1_tarski(sK0) != k1_tarski(sK0)
    | r2_hidden(sK1,k1_tarski(sK0))
    | spl4_1 ),
    inference(superposition,[],[f45,f94])).

fof(f94,plain,(
    ! [X8,X9] :
      ( k4_xboole_0(X8,k1_tarski(X9)) = X8
      | r2_hidden(X9,X8) ) ),
    inference(duplicate_literal_removal,[],[f93])).

fof(f93,plain,(
    ! [X8,X9] :
      ( r2_hidden(X9,X8)
      | k4_xboole_0(X8,k1_tarski(X9)) = X8
      | k4_xboole_0(X8,k1_tarski(X9)) = X8 ) ),
    inference(superposition,[],[f61,f78])).

fof(f78,plain,(
    ! [X4,X3] :
      ( sK2(X3,k1_tarski(X4),X3) = X4
      | k4_xboole_0(X3,k1_tarski(X4)) = X3 ) ),
    inference(resolution,[],[f75,f41])).

fof(f75,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK2(X3,X4,X3),X4)
      | k4_xboole_0(X3,X4) = X3 ) ),
    inference(subsumption_resolution,[],[f73,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f73,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK2(X3,X4,X3),X4)
      | ~ r2_hidden(sK2(X3,X4,X3),X3)
      | k4_xboole_0(X3,X4) = X3 ) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK2(X3,X4,X3),X4)
      | ~ r2_hidden(sK2(X3,X4,X3),X3)
      | k4_xboole_0(X3,X4) = X3
      | k4_xboole_0(X3,X4) = X3 ) ),
    inference(resolution,[],[f28,f61])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1,X0),X0)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(factoring,[],[f26])).

fof(f45,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f51,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f21,f47,f43])).

fof(f21,plain,
    ( sK0 != sK1
    | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ( sK0 = sK1
      | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) )
    & ( sK0 != sK1
      | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1] :
        ( ( X0 = X1
          | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
        & ( X0 != X1
          | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) )
   => ( ( sK0 = sK1
        | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) )
      & ( sK0 != sK1
        | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( X0 = X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
      & ( X0 != X1
        | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <~> X0 != X1 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      <=> X0 != X1 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f50,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f22,f47,f43])).

fof(f22,plain,
    ( sK0 = sK1
    | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:04:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.23/0.50  % (15452)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.51  % (15450)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.23/0.51  % (15465)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.23/0.51  % (15449)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.23/0.52  % (15462)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.23/0.52  % (15464)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.23/0.52  % (15458)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.23/0.52  % (15454)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.23/0.52  % (15457)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.23/0.53  % (15448)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.23/0.53  % (15457)Refutation not found, incomplete strategy% (15457)------------------------------
% 0.23/0.53  % (15457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (15457)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (15457)Memory used [KB]: 6140
% 0.23/0.53  % (15457)Time elapsed: 0.111 s
% 0.23/0.53  % (15457)------------------------------
% 0.23/0.53  % (15457)------------------------------
% 0.23/0.53  % (15474)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.23/0.53  % (15446)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.23/0.53  % (15470)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.23/0.53  % (15451)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.23/0.53  % (15470)Refutation not found, incomplete strategy% (15470)------------------------------
% 0.23/0.53  % (15470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (15470)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (15470)Memory used [KB]: 10618
% 0.23/0.53  % (15470)Time elapsed: 0.114 s
% 0.23/0.53  % (15470)------------------------------
% 0.23/0.53  % (15470)------------------------------
% 0.23/0.53  % (15456)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.23/0.53  % (15459)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.23/0.53  % (15464)Refutation not found, incomplete strategy% (15464)------------------------------
% 0.23/0.53  % (15464)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (15467)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.23/0.54  % (15464)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (15464)Memory used [KB]: 1663
% 0.23/0.54  % (15464)Time elapsed: 0.111 s
% 0.23/0.54  % (15464)------------------------------
% 0.23/0.54  % (15464)------------------------------
% 0.23/0.54  % (15453)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.23/0.54  % (15467)Refutation found. Thanks to Tanya!
% 0.23/0.54  % SZS status Theorem for theBenchmark
% 0.23/0.54  % SZS output start Proof for theBenchmark
% 0.23/0.54  fof(f159,plain,(
% 0.23/0.54    $false),
% 0.23/0.54    inference(avatar_sat_refutation,[],[f50,f51,f117,f133,f140,f158])).
% 0.23/0.54  fof(f158,plain,(
% 0.23/0.54    ~spl4_4),
% 0.23/0.54    inference(avatar_contradiction_clause,[],[f149])).
% 0.23/0.54  fof(f149,plain,(
% 0.23/0.54    $false | ~spl4_4),
% 0.23/0.54    inference(unit_resulting_resolution,[],[f40,f146])).
% 0.23/0.54  fof(f146,plain,(
% 0.23/0.54    ( ! [X4] : (~r2_hidden(X4,k1_tarski(sK0))) ) | ~spl4_4),
% 0.23/0.54    inference(duplicate_literal_removal,[],[f145])).
% 0.23/0.54  fof(f145,plain,(
% 0.23/0.54    ( ! [X4] : (~r2_hidden(X4,k1_tarski(sK0)) | ~r2_hidden(X4,k1_tarski(sK0))) ) | ~spl4_4),
% 0.23/0.54    inference(superposition,[],[f37,f139])).
% 0.23/0.54  fof(f139,plain,(
% 0.23/0.54    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) | ~spl4_4),
% 0.23/0.54    inference(avatar_component_clause,[],[f137])).
% 0.23/0.54  fof(f137,plain,(
% 0.23/0.54    spl4_4 <=> k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 0.23/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.23/0.54  fof(f37,plain,(
% 0.23/0.54    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.23/0.54    inference(equality_resolution,[],[f24])).
% 0.23/0.54  fof(f24,plain,(
% 0.23/0.54    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.23/0.54    inference(cnf_transformation,[],[f16])).
% 0.23/0.54  fof(f16,plain,(
% 0.23/0.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.23/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f15])).
% 0.23/0.54  fof(f15,plain,(
% 0.23/0.54    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.23/0.54    introduced(choice_axiom,[])).
% 0.23/0.54  fof(f14,plain,(
% 0.23/0.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.23/0.54    inference(rectify,[],[f13])).
% 0.23/0.54  fof(f13,plain,(
% 0.23/0.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.23/0.54    inference(flattening,[],[f12])).
% 0.23/0.54  fof(f12,plain,(
% 0.23/0.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.23/0.54    inference(nnf_transformation,[],[f1])).
% 0.23/0.54  fof(f1,axiom,(
% 0.23/0.54    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.23/0.54  fof(f40,plain,(
% 0.23/0.54    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 0.23/0.54    inference(equality_resolution,[],[f39])).
% 0.23/0.54  fof(f39,plain,(
% 0.23/0.54    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 0.23/0.54    inference(equality_resolution,[],[f30])).
% 0.23/0.54  fof(f30,plain,(
% 0.23/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.23/0.54    inference(cnf_transformation,[],[f20])).
% 0.23/0.54  fof(f20,plain,(
% 0.23/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.23/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f19])).
% 0.23/0.54  fof(f19,plain,(
% 0.23/0.54    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 0.23/0.54    introduced(choice_axiom,[])).
% 0.23/0.54  fof(f18,plain,(
% 0.23/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.23/0.54    inference(rectify,[],[f17])).
% 0.23/0.54  fof(f17,plain,(
% 0.23/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.23/0.54    inference(nnf_transformation,[],[f2])).
% 0.23/0.54  fof(f2,axiom,(
% 0.23/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.23/0.54  fof(f140,plain,(
% 0.23/0.54    spl4_4 | ~spl4_1 | ~spl4_2),
% 0.23/0.54    inference(avatar_split_clause,[],[f135,f47,f43,f137])).
% 0.23/0.54  fof(f43,plain,(
% 0.23/0.54    spl4_1 <=> k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.23/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.23/0.54  fof(f47,plain,(
% 0.23/0.54    spl4_2 <=> sK0 = sK1),
% 0.23/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.23/0.54  fof(f135,plain,(
% 0.23/0.54    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) | (~spl4_1 | ~spl4_2)),
% 0.23/0.54    inference(forward_demodulation,[],[f44,f49])).
% 0.23/0.54  fof(f49,plain,(
% 0.23/0.54    sK0 = sK1 | ~spl4_2),
% 0.23/0.54    inference(avatar_component_clause,[],[f47])).
% 0.23/0.54  fof(f44,plain,(
% 0.23/0.54    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | ~spl4_1),
% 0.23/0.54    inference(avatar_component_clause,[],[f43])).
% 0.23/0.54  fof(f133,plain,(
% 0.23/0.54    spl4_2 | ~spl4_3),
% 0.23/0.54    inference(avatar_split_clause,[],[f129,f114,f47])).
% 0.23/0.54  fof(f114,plain,(
% 0.23/0.54    spl4_3 <=> r2_hidden(sK1,k1_tarski(sK0))),
% 0.23/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.23/0.54  fof(f129,plain,(
% 0.23/0.54    sK0 = sK1 | ~spl4_3),
% 0.23/0.54    inference(resolution,[],[f116,f41])).
% 0.23/0.54  fof(f41,plain,(
% 0.23/0.54    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.23/0.54    inference(equality_resolution,[],[f29])).
% 0.23/0.54  fof(f29,plain,(
% 0.23/0.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.23/0.54    inference(cnf_transformation,[],[f20])).
% 0.23/0.54  fof(f116,plain,(
% 0.23/0.54    r2_hidden(sK1,k1_tarski(sK0)) | ~spl4_3),
% 0.23/0.54    inference(avatar_component_clause,[],[f114])).
% 0.23/0.54  fof(f117,plain,(
% 0.23/0.54    spl4_3 | spl4_1),
% 0.23/0.54    inference(avatar_split_clause,[],[f112,f43,f114])).
% 0.23/0.54  fof(f112,plain,(
% 0.23/0.54    r2_hidden(sK1,k1_tarski(sK0)) | spl4_1),
% 0.23/0.54    inference(trivial_inequality_removal,[],[f106])).
% 0.23/0.54  fof(f106,plain,(
% 0.23/0.54    k1_tarski(sK0) != k1_tarski(sK0) | r2_hidden(sK1,k1_tarski(sK0)) | spl4_1),
% 0.23/0.54    inference(superposition,[],[f45,f94])).
% 0.23/0.54  fof(f94,plain,(
% 0.23/0.54    ( ! [X8,X9] : (k4_xboole_0(X8,k1_tarski(X9)) = X8 | r2_hidden(X9,X8)) )),
% 0.23/0.54    inference(duplicate_literal_removal,[],[f93])).
% 0.23/0.54  fof(f93,plain,(
% 0.23/0.54    ( ! [X8,X9] : (r2_hidden(X9,X8) | k4_xboole_0(X8,k1_tarski(X9)) = X8 | k4_xboole_0(X8,k1_tarski(X9)) = X8) )),
% 0.23/0.54    inference(superposition,[],[f61,f78])).
% 0.23/0.54  fof(f78,plain,(
% 0.23/0.54    ( ! [X4,X3] : (sK2(X3,k1_tarski(X4),X3) = X4 | k4_xboole_0(X3,k1_tarski(X4)) = X3) )),
% 0.23/0.54    inference(resolution,[],[f75,f41])).
% 0.23/0.54  fof(f75,plain,(
% 0.23/0.54    ( ! [X4,X3] : (r2_hidden(sK2(X3,X4,X3),X4) | k4_xboole_0(X3,X4) = X3) )),
% 0.23/0.54    inference(subsumption_resolution,[],[f73,f26])).
% 0.23/0.54  fof(f26,plain,(
% 0.23/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 0.23/0.54    inference(cnf_transformation,[],[f16])).
% 0.23/0.54  fof(f73,plain,(
% 0.23/0.54    ( ! [X4,X3] : (r2_hidden(sK2(X3,X4,X3),X4) | ~r2_hidden(sK2(X3,X4,X3),X3) | k4_xboole_0(X3,X4) = X3) )),
% 0.23/0.54    inference(duplicate_literal_removal,[],[f71])).
% 0.23/0.54  fof(f71,plain,(
% 0.23/0.54    ( ! [X4,X3] : (r2_hidden(sK2(X3,X4,X3),X4) | ~r2_hidden(sK2(X3,X4,X3),X3) | k4_xboole_0(X3,X4) = X3 | k4_xboole_0(X3,X4) = X3) )),
% 0.23/0.54    inference(resolution,[],[f28,f61])).
% 0.23/0.54  fof(f28,plain,(
% 0.23/0.54    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 0.23/0.54    inference(cnf_transformation,[],[f16])).
% 0.23/0.54  fof(f61,plain,(
% 0.23/0.54    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0) )),
% 0.23/0.54    inference(factoring,[],[f26])).
% 0.23/0.54  fof(f45,plain,(
% 0.23/0.54    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | spl4_1),
% 0.23/0.54    inference(avatar_component_clause,[],[f43])).
% 0.23/0.54  fof(f51,plain,(
% 0.23/0.54    spl4_1 | ~spl4_2),
% 0.23/0.54    inference(avatar_split_clause,[],[f21,f47,f43])).
% 0.23/0.54  fof(f21,plain,(
% 0.23/0.54    sK0 != sK1 | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.23/0.54    inference(cnf_transformation,[],[f11])).
% 0.23/0.54  fof(f11,plain,(
% 0.23/0.54    (sK0 = sK1 | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) & (sK0 != sK1 | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.23/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).
% 0.23/0.54  fof(f10,plain,(
% 0.23/0.54    ? [X0,X1] : ((X0 = X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) & (X0 != X1 | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) => ((sK0 = sK1 | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) & (sK0 != sK1 | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))))),
% 0.23/0.54    introduced(choice_axiom,[])).
% 0.23/0.54  fof(f9,plain,(
% 0.23/0.54    ? [X0,X1] : ((X0 = X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) & (X0 != X1 | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.23/0.54    inference(nnf_transformation,[],[f8])).
% 0.23/0.54  fof(f8,plain,(
% 0.23/0.54    ? [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <~> X0 != X1)),
% 0.23/0.54    inference(ennf_transformation,[],[f7])).
% 0.23/0.54  fof(f7,negated_conjecture,(
% 0.23/0.54    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.23/0.54    inference(negated_conjecture,[],[f6])).
% 0.23/0.54  fof(f6,conjecture,(
% 0.23/0.54    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.23/0.54  fof(f50,plain,(
% 0.23/0.54    ~spl4_1 | spl4_2),
% 0.23/0.54    inference(avatar_split_clause,[],[f22,f47,f43])).
% 0.23/0.54  fof(f22,plain,(
% 0.23/0.54    sK0 = sK1 | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.23/0.54    inference(cnf_transformation,[],[f11])).
% 0.23/0.54  % SZS output end Proof for theBenchmark
% 0.23/0.54  % (15467)------------------------------
% 0.23/0.54  % (15467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (15467)Termination reason: Refutation
% 0.23/0.54  
% 0.23/0.54  % (15467)Memory used [KB]: 6268
% 0.23/0.54  % (15467)Time elapsed: 0.084 s
% 0.23/0.54  % (15467)------------------------------
% 0.23/0.54  % (15467)------------------------------
% 0.23/0.54  % (15472)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.23/0.54  % (15445)Success in time 0.164 s
%------------------------------------------------------------------------------
