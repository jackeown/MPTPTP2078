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
% DateTime   : Thu Dec  3 12:40:08 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   54 (  70 expanded)
%              Number of leaves         :   14 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :  177 ( 213 expanded)
%              Number of equality atoms :   60 (  62 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f108,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f48,f65,f73,f85,f96,f107])).

fof(f107,plain,(
    ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f106])).

fof(f106,plain,
    ( $false
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f102,f37])).

fof(f37,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f102,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK1))
    | ~ spl4_7 ),
    inference(resolution,[],[f95,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f95,plain,
    ( r1_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl4_7
  <=> r1_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f96,plain,
    ( spl4_7
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f89,f82,f93])).

fof(f82,plain,
    ( spl4_6
  <=> r1_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f89,plain,
    ( r1_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))
    | ~ spl4_6 ),
    inference(resolution,[],[f84,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f84,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f82])).

fof(f85,plain,
    ( spl4_6
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f74,f71,f45,f82])).

fof(f45,plain,
    ( spl4_2
  <=> r1_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f71,plain,
    ( spl4_5
  <=> ! [X1] :
        ( ~ r1_xboole_0(X1,sK2)
        | r1_xboole_0(X1,k1_tarski(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f74,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK0))
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(resolution,[],[f72,f47])).

fof(f47,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f72,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,sK2)
        | r1_xboole_0(X1,k1_tarski(sK0)) )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f73,plain,
    ( spl4_5
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f69,f62,f71])).

fof(f62,plain,
    ( spl4_4
  <=> sK2 = k2_xboole_0(k1_tarski(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f69,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,sK2)
        | r1_xboole_0(X1,k1_tarski(sK0)) )
    | ~ spl4_4 ),
    inference(superposition,[],[f26,f64])).

fof(f64,plain,
    ( sK2 = k2_xboole_0(k1_tarski(sK0),sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f65,plain,
    ( spl4_4
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f56,f40,f62])).

fof(f40,plain,
    ( spl4_1
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f56,plain,
    ( sK2 = k2_xboole_0(k1_tarski(sK0),sK2)
    | ~ spl4_1 ),
    inference(resolution,[],[f22,f42])).

fof(f42,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f48,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f20,f45])).

fof(f20,plain,(
    r1_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( r2_hidden(sK0,sK2)
    & r1_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) )
   => ( r2_hidden(sK0,sK2)
      & r1_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( r2_hidden(X0,X2)
      & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r2_hidden(X0,X2)
          & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f43,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f21,f40])).

fof(f21,plain,(
    r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f14])).
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
% 0.14/0.35  % DateTime   : Tue Dec  1 12:47:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (8147)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.31/0.54  % (8144)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.31/0.55  % (8146)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.31/0.55  % (8153)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.31/0.55  % (8154)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.31/0.55  % (8145)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.31/0.55  % (8144)Refutation found. Thanks to Tanya!
% 1.31/0.55  % SZS status Theorem for theBenchmark
% 1.31/0.56  % (8148)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.31/0.56  % (8148)Refutation not found, incomplete strategy% (8148)------------------------------
% 1.31/0.56  % (8148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.56  % (8148)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.56  
% 1.31/0.56  % (8148)Memory used [KB]: 10490
% 1.31/0.56  % (8148)Time elapsed: 0.127 s
% 1.31/0.56  % (8148)------------------------------
% 1.31/0.56  % (8148)------------------------------
% 1.31/0.56  % (8161)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.56/0.56  % (8160)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.56/0.56  % (8151)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.56/0.56  % (8149)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.56/0.56  % (8164)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.56/0.56  % SZS output start Proof for theBenchmark
% 1.56/0.56  fof(f108,plain,(
% 1.56/0.56    $false),
% 1.56/0.56    inference(avatar_sat_refutation,[],[f43,f48,f65,f73,f85,f96,f107])).
% 1.56/0.56  fof(f107,plain,(
% 1.56/0.56    ~spl4_7),
% 1.56/0.56    inference(avatar_contradiction_clause,[],[f106])).
% 1.56/0.56  fof(f106,plain,(
% 1.56/0.56    $false | ~spl4_7),
% 1.56/0.56    inference(subsumption_resolution,[],[f102,f37])).
% 1.56/0.56  fof(f37,plain,(
% 1.56/0.56    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 1.56/0.56    inference(equality_resolution,[],[f36])).
% 1.56/0.56  fof(f36,plain,(
% 1.56/0.56    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 1.56/0.56    inference(equality_resolution,[],[f29])).
% 1.56/0.56  fof(f29,plain,(
% 1.56/0.56    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.56/0.56    inference(cnf_transformation,[],[f19])).
% 1.56/0.56  fof(f19,plain,(
% 1.56/0.56    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.56/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).
% 1.56/0.56  fof(f18,plain,(
% 1.56/0.56    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.56/0.56    introduced(choice_axiom,[])).
% 1.56/0.56  fof(f17,plain,(
% 1.56/0.56    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.56/0.56    inference(rectify,[],[f16])).
% 1.56/0.56  fof(f16,plain,(
% 1.56/0.56    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.56/0.56    inference(flattening,[],[f15])).
% 1.56/0.56  fof(f15,plain,(
% 1.56/0.56    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.56/0.56    inference(nnf_transformation,[],[f3])).
% 1.56/0.56  fof(f3,axiom,(
% 1.56/0.56    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.56/0.56  fof(f102,plain,(
% 1.56/0.56    ~r2_hidden(sK0,k2_tarski(sK0,sK1)) | ~spl4_7),
% 1.56/0.56    inference(resolution,[],[f95,f24])).
% 1.56/0.56  fof(f24,plain,(
% 1.56/0.56    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f11])).
% 1.56/0.56  fof(f11,plain,(
% 1.56/0.56    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 1.56/0.56    inference(ennf_transformation,[],[f4])).
% 1.56/0.56  fof(f4,axiom,(
% 1.56/0.56    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 1.56/0.56  fof(f95,plain,(
% 1.56/0.56    r1_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) | ~spl4_7),
% 1.56/0.56    inference(avatar_component_clause,[],[f93])).
% 1.56/0.56  fof(f93,plain,(
% 1.56/0.56    spl4_7 <=> r1_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.56/0.56  fof(f96,plain,(
% 1.56/0.56    spl4_7 | ~spl4_6),
% 1.56/0.56    inference(avatar_split_clause,[],[f89,f82,f93])).
% 1.56/0.56  fof(f82,plain,(
% 1.56/0.56    spl4_6 <=> r1_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK0))),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.56/0.56  fof(f89,plain,(
% 1.56/0.56    r1_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) | ~spl4_6),
% 1.56/0.56    inference(resolution,[],[f84,f23])).
% 1.56/0.56  fof(f23,plain,(
% 1.56/0.56    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f10])).
% 1.56/0.56  fof(f10,plain,(
% 1.56/0.56    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.56/0.56    inference(ennf_transformation,[],[f1])).
% 1.56/0.56  fof(f1,axiom,(
% 1.56/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.56/0.56  fof(f84,plain,(
% 1.56/0.56    r1_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK0)) | ~spl4_6),
% 1.56/0.56    inference(avatar_component_clause,[],[f82])).
% 1.56/0.56  fof(f85,plain,(
% 1.56/0.56    spl4_6 | ~spl4_2 | ~spl4_5),
% 1.56/0.56    inference(avatar_split_clause,[],[f74,f71,f45,f82])).
% 1.56/0.56  fof(f45,plain,(
% 1.56/0.56    spl4_2 <=> r1_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.56/0.56  fof(f71,plain,(
% 1.56/0.56    spl4_5 <=> ! [X1] : (~r1_xboole_0(X1,sK2) | r1_xboole_0(X1,k1_tarski(sK0)))),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.56/0.56  fof(f74,plain,(
% 1.56/0.56    r1_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK0)) | (~spl4_2 | ~spl4_5)),
% 1.56/0.56    inference(resolution,[],[f72,f47])).
% 1.56/0.56  fof(f47,plain,(
% 1.56/0.56    r1_xboole_0(k2_tarski(sK0,sK1),sK2) | ~spl4_2),
% 1.56/0.56    inference(avatar_component_clause,[],[f45])).
% 1.56/0.56  fof(f72,plain,(
% 1.56/0.56    ( ! [X1] : (~r1_xboole_0(X1,sK2) | r1_xboole_0(X1,k1_tarski(sK0))) ) | ~spl4_5),
% 1.56/0.56    inference(avatar_component_clause,[],[f71])).
% 1.56/0.56  fof(f73,plain,(
% 1.56/0.56    spl4_5 | ~spl4_4),
% 1.56/0.56    inference(avatar_split_clause,[],[f69,f62,f71])).
% 1.56/0.56  fof(f62,plain,(
% 1.56/0.56    spl4_4 <=> sK2 = k2_xboole_0(k1_tarski(sK0),sK2)),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.56/0.56  fof(f69,plain,(
% 1.56/0.56    ( ! [X1] : (~r1_xboole_0(X1,sK2) | r1_xboole_0(X1,k1_tarski(sK0))) ) | ~spl4_4),
% 1.56/0.56    inference(superposition,[],[f26,f64])).
% 1.56/0.56  fof(f64,plain,(
% 1.56/0.56    sK2 = k2_xboole_0(k1_tarski(sK0),sK2) | ~spl4_4),
% 1.56/0.56    inference(avatar_component_clause,[],[f62])).
% 1.56/0.56  fof(f26,plain,(
% 1.56/0.56    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f12])).
% 1.56/0.56  fof(f12,plain,(
% 1.56/0.56    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.56/0.56    inference(ennf_transformation,[],[f2])).
% 1.56/0.56  fof(f2,axiom,(
% 1.56/0.56    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.56/0.56  fof(f65,plain,(
% 1.56/0.56    spl4_4 | ~spl4_1),
% 1.56/0.56    inference(avatar_split_clause,[],[f56,f40,f62])).
% 1.56/0.56  fof(f40,plain,(
% 1.56/0.56    spl4_1 <=> r2_hidden(sK0,sK2)),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.56/0.56  fof(f56,plain,(
% 1.56/0.56    sK2 = k2_xboole_0(k1_tarski(sK0),sK2) | ~spl4_1),
% 1.56/0.56    inference(resolution,[],[f22,f42])).
% 1.56/0.56  fof(f42,plain,(
% 1.56/0.56    r2_hidden(sK0,sK2) | ~spl4_1),
% 1.56/0.56    inference(avatar_component_clause,[],[f40])).
% 1.56/0.56  fof(f22,plain,(
% 1.56/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k2_xboole_0(k1_tarski(X0),X1) = X1) )),
% 1.56/0.56    inference(cnf_transformation,[],[f9])).
% 1.56/0.56  fof(f9,plain,(
% 1.56/0.56    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 1.56/0.56    inference(ennf_transformation,[],[f5])).
% 1.56/0.56  fof(f5,axiom,(
% 1.56/0.56    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 1.56/0.56  fof(f48,plain,(
% 1.56/0.56    spl4_2),
% 1.56/0.56    inference(avatar_split_clause,[],[f20,f45])).
% 1.56/0.56  fof(f20,plain,(
% 1.56/0.56    r1_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.56/0.56    inference(cnf_transformation,[],[f14])).
% 1.56/0.56  fof(f14,plain,(
% 1.56/0.56    r2_hidden(sK0,sK2) & r1_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.56/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f13])).
% 1.56/0.56  fof(f13,plain,(
% 1.56/0.56    ? [X0,X1,X2] : (r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2)) => (r2_hidden(sK0,sK2) & r1_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 1.56/0.56    introduced(choice_axiom,[])).
% 1.56/0.56  fof(f8,plain,(
% 1.56/0.56    ? [X0,X1,X2] : (r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 1.56/0.56    inference(ennf_transformation,[],[f7])).
% 1.56/0.56  fof(f7,negated_conjecture,(
% 1.56/0.56    ~! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 1.56/0.56    inference(negated_conjecture,[],[f6])).
% 1.56/0.56  fof(f6,conjecture,(
% 1.56/0.56    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 1.56/0.56  fof(f43,plain,(
% 1.56/0.56    spl4_1),
% 1.56/0.56    inference(avatar_split_clause,[],[f21,f40])).
% 1.56/0.56  fof(f21,plain,(
% 1.56/0.56    r2_hidden(sK0,sK2)),
% 1.56/0.56    inference(cnf_transformation,[],[f14])).
% 1.56/0.56  % SZS output end Proof for theBenchmark
% 1.56/0.56  % (8144)------------------------------
% 1.56/0.56  % (8144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.56  % (8144)Termination reason: Refutation
% 1.56/0.56  
% 1.56/0.56  % (8144)Memory used [KB]: 6140
% 1.56/0.56  % (8144)Time elapsed: 0.132 s
% 1.56/0.56  % (8144)------------------------------
% 1.56/0.56  % (8144)------------------------------
% 1.56/0.56  % (8163)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.56/0.57  % (8141)Success in time 0.2 s
%------------------------------------------------------------------------------
