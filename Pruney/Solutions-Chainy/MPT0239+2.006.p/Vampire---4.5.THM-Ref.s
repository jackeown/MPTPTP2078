%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:37 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 128 expanded)
%              Number of leaves         :   10 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :  191 ( 475 expanded)
%              Number of equality atoms :   78 ( 234 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f84,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f57,f58,f66,f81,f83])).

fof(f83,plain,
    ( spl5_2
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f82])).

fof(f82,plain,
    ( $false
    | spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f79,f77])).

fof(f77,plain,
    ( ~ r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | spl5_2 ),
    inference(extensionality_resolution,[],[f37,f47])).

fof(f47,plain,
    ( sK0 != sK2
    | spl5_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl5_2
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f37,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f21,f20])).

fof(f20,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_enumset1)).

fof(f21,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f13])).

fof(f13,plain,(
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

fof(f12,plain,(
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
    inference(rectify,[],[f11])).

fof(f11,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f79,plain,
    ( r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ spl5_4 ),
    inference(resolution,[],[f56,f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f56,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl5_4
  <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f81,plain,
    ( spl5_3
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f80])).

% (24397)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
fof(f80,plain,
    ( $false
    | spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f78,f69])).

fof(f69,plain,
    ( ~ r2_hidden(sK1,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
    | spl5_3 ),
    inference(extensionality_resolution,[],[f37,f51])).

fof(f51,plain,
    ( sK1 != sK3
    | spl5_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl5_3
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f78,plain,
    ( r2_hidden(sK1,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
    | ~ spl5_4 ),
    inference(resolution,[],[f56,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f66,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f65])).

fof(f65,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f64,f36])).

fof(f36,plain,(
    ! [X3] : r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f22,f20])).

fof(f22,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f64,plain,
    ( ~ r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | spl5_1 ),
    inference(subsumption_resolution,[],[f63,f36])).

fof(f63,plain,
    ( ~ r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | ~ r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | spl5_1 ),
    inference(resolution,[],[f43,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f43,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl5_1
  <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f58,plain,
    ( spl5_4
    | spl5_2 ),
    inference(avatar_split_clause,[],[f30,f45,f54])).

fof(f30,plain,
    ( sK0 = sK2
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) ),
    inference(definition_unfolding,[],[f17,f20,f20])).

fof(f17,plain,
    ( sK0 = sK2
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ( sK1 != sK3
      | sK0 != sK2
      | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) )
    & ( ( sK1 = sK3
        & sK0 = sK2 )
      | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | X0 != X2
          | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) )
        & ( ( X1 = X3
            & X0 = X2 )
          | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) )
   => ( ( sK1 != sK3
        | sK0 != sK2
        | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) )
      & ( ( sK1 = sK3
          & sK0 = sK2 )
        | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) ) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) )
      & ( ( X1 = X3
          & X0 = X2 )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) )
      & ( ( X1 = X3
          & X0 = X2 )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
    <~> ( X1 = X3
        & X0 = X2 ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
      <=> ( X1 = X3
          & X0 = X2 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
    <=> ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_zfmisc_1)).

fof(f57,plain,
    ( spl5_4
    | spl5_3 ),
    inference(avatar_split_clause,[],[f29,f49,f54])).

fof(f29,plain,
    ( sK1 = sK3
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) ),
    inference(definition_unfolding,[],[f18,f20,f20])).

fof(f18,plain,
    ( sK1 = sK3
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f10])).

fof(f52,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f39,f49,f45,f41])).

fof(f39,plain,
    ( sK1 != sK3
    | sK0 != sK2
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(inner_rewriting,[],[f38])).

fof(f38,plain,
    ( sK1 != sK3
    | sK0 != sK2
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(inner_rewriting,[],[f28])).

fof(f28,plain,
    ( sK1 != sK3
    | sK0 != sK2
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) ),
    inference(definition_unfolding,[],[f19,f20,f20])).

fof(f19,plain,
    ( sK1 != sK3
    | sK0 != sK2
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:36:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.34/0.55  % (24398)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.34/0.55  % (24412)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.34/0.56  % (24405)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.34/0.56  % (24396)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.34/0.56  % (24396)Refutation found. Thanks to Tanya!
% 1.34/0.56  % SZS status Theorem for theBenchmark
% 1.34/0.56  % SZS output start Proof for theBenchmark
% 1.34/0.56  fof(f84,plain,(
% 1.34/0.56    $false),
% 1.34/0.56    inference(avatar_sat_refutation,[],[f52,f57,f58,f66,f81,f83])).
% 1.34/0.56  fof(f83,plain,(
% 1.34/0.56    spl5_2 | ~spl5_4),
% 1.34/0.56    inference(avatar_contradiction_clause,[],[f82])).
% 1.34/0.56  fof(f82,plain,(
% 1.34/0.56    $false | (spl5_2 | ~spl5_4)),
% 1.34/0.56    inference(subsumption_resolution,[],[f79,f77])).
% 1.34/0.56  fof(f77,plain,(
% 1.34/0.56    ~r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | spl5_2),
% 1.34/0.56    inference(extensionality_resolution,[],[f37,f47])).
% 1.34/0.56  fof(f47,plain,(
% 1.34/0.56    sK0 != sK2 | spl5_2),
% 1.34/0.56    inference(avatar_component_clause,[],[f45])).
% 1.34/0.56  fof(f45,plain,(
% 1.34/0.56    spl5_2 <=> sK0 = sK2),
% 1.34/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.34/0.56  fof(f37,plain,(
% 1.34/0.56    ( ! [X0,X3] : (~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) | X0 = X3) )),
% 1.34/0.56    inference(equality_resolution,[],[f34])).
% 1.34/0.56  fof(f34,plain,(
% 1.34/0.56    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 1.34/0.56    inference(definition_unfolding,[],[f21,f20])).
% 1.34/0.56  fof(f20,plain,(
% 1.34/0.56    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.34/0.56    inference(cnf_transformation,[],[f2])).
% 1.34/0.56  fof(f2,axiom,(
% 1.34/0.56    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_enumset1)).
% 1.34/0.56  fof(f21,plain,(
% 1.34/0.56    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.34/0.56    inference(cnf_transformation,[],[f14])).
% 1.34/0.56  fof(f14,plain,(
% 1.34/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.34/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f13])).
% 1.34/0.56  fof(f13,plain,(
% 1.34/0.56    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 1.34/0.56    introduced(choice_axiom,[])).
% 1.34/0.56  fof(f12,plain,(
% 1.34/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.34/0.56    inference(rectify,[],[f11])).
% 1.34/0.56  fof(f11,plain,(
% 1.34/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.34/0.56    inference(nnf_transformation,[],[f1])).
% 1.34/0.56  fof(f1,axiom,(
% 1.34/0.56    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.34/0.56  fof(f79,plain,(
% 1.34/0.56    r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | ~spl5_4),
% 1.34/0.56    inference(resolution,[],[f56,f25])).
% 1.34/0.56  fof(f25,plain,(
% 1.34/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 1.34/0.56    inference(cnf_transformation,[],[f16])).
% 1.34/0.56  fof(f16,plain,(
% 1.34/0.56    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.34/0.56    inference(flattening,[],[f15])).
% 1.34/0.56  fof(f15,plain,(
% 1.34/0.56    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.34/0.56    inference(nnf_transformation,[],[f3])).
% 1.34/0.56  fof(f3,axiom,(
% 1.34/0.56    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.34/0.56  fof(f56,plain,(
% 1.34/0.56    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) | ~spl5_4),
% 1.34/0.56    inference(avatar_component_clause,[],[f54])).
% 1.34/0.56  fof(f54,plain,(
% 1.34/0.56    spl5_4 <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))),
% 1.34/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.34/0.56  fof(f81,plain,(
% 1.34/0.56    spl5_3 | ~spl5_4),
% 1.34/0.56    inference(avatar_contradiction_clause,[],[f80])).
% 1.34/0.56  % (24397)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.34/0.56  fof(f80,plain,(
% 1.34/0.56    $false | (spl5_3 | ~spl5_4)),
% 1.34/0.56    inference(subsumption_resolution,[],[f78,f69])).
% 1.34/0.56  fof(f69,plain,(
% 1.34/0.56    ~r2_hidden(sK1,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) | spl5_3),
% 1.34/0.56    inference(extensionality_resolution,[],[f37,f51])).
% 1.34/0.56  fof(f51,plain,(
% 1.34/0.56    sK1 != sK3 | spl5_3),
% 1.34/0.56    inference(avatar_component_clause,[],[f49])).
% 1.34/0.56  fof(f49,plain,(
% 1.34/0.56    spl5_3 <=> sK1 = sK3),
% 1.34/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.34/0.56  fof(f78,plain,(
% 1.34/0.56    r2_hidden(sK1,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) | ~spl5_4),
% 1.34/0.56    inference(resolution,[],[f56,f26])).
% 1.34/0.56  fof(f26,plain,(
% 1.34/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 1.34/0.56    inference(cnf_transformation,[],[f16])).
% 1.34/0.56  fof(f66,plain,(
% 1.34/0.56    spl5_1),
% 1.34/0.56    inference(avatar_contradiction_clause,[],[f65])).
% 1.34/0.56  fof(f65,plain,(
% 1.34/0.56    $false | spl5_1),
% 1.34/0.56    inference(subsumption_resolution,[],[f64,f36])).
% 1.34/0.56  fof(f36,plain,(
% 1.34/0.56    ( ! [X3] : (r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) )),
% 1.34/0.56    inference(equality_resolution,[],[f35])).
% 1.34/0.56  fof(f35,plain,(
% 1.34/0.56    ( ! [X3,X1] : (r2_hidden(X3,X1) | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1) )),
% 1.34/0.56    inference(equality_resolution,[],[f33])).
% 1.34/0.56  fof(f33,plain,(
% 1.34/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 1.34/0.56    inference(definition_unfolding,[],[f22,f20])).
% 1.34/0.56  fof(f22,plain,(
% 1.34/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.34/0.56    inference(cnf_transformation,[],[f14])).
% 1.34/0.56  fof(f64,plain,(
% 1.34/0.56    ~r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | spl5_1),
% 1.34/0.56    inference(subsumption_resolution,[],[f63,f36])).
% 1.34/0.56  fof(f63,plain,(
% 1.34/0.56    ~r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | ~r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | spl5_1),
% 1.34/0.56    inference(resolution,[],[f43,f27])).
% 1.34/0.56  fof(f27,plain,(
% 1.34/0.56    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 1.34/0.56    inference(cnf_transformation,[],[f16])).
% 1.34/0.56  fof(f43,plain,(
% 1.34/0.56    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) | spl5_1),
% 1.34/0.56    inference(avatar_component_clause,[],[f41])).
% 1.34/0.56  fof(f41,plain,(
% 1.34/0.56    spl5_1 <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 1.34/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.34/0.56  fof(f58,plain,(
% 1.34/0.56    spl5_4 | spl5_2),
% 1.34/0.56    inference(avatar_split_clause,[],[f30,f45,f54])).
% 1.34/0.56  fof(f30,plain,(
% 1.34/0.56    sK0 = sK2 | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))),
% 1.34/0.56    inference(definition_unfolding,[],[f17,f20,f20])).
% 1.34/0.56  fof(f17,plain,(
% 1.34/0.56    sK0 = sK2 | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3)))),
% 1.34/0.56    inference(cnf_transformation,[],[f10])).
% 1.34/0.56  fof(f10,plain,(
% 1.34/0.56    (sK1 != sK3 | sK0 != sK2 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3)))) & ((sK1 = sK3 & sK0 = sK2) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))))),
% 1.34/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f9])).
% 1.34/0.56  fof(f9,plain,(
% 1.34/0.56    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))) & ((X1 = X3 & X0 = X2) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))))) => ((sK1 != sK3 | sK0 != sK2 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3)))) & ((sK1 = sK3 & sK0 = sK2) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3)))))),
% 1.34/0.56    introduced(choice_axiom,[])).
% 1.34/0.56  fof(f8,plain,(
% 1.34/0.56    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))) & ((X1 = X3 & X0 = X2) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))))),
% 1.34/0.56    inference(flattening,[],[f7])).
% 1.34/0.56  fof(f7,plain,(
% 1.34/0.56    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))) & ((X1 = X3 & X0 = X2) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))))),
% 1.34/0.56    inference(nnf_transformation,[],[f6])).
% 1.34/0.56  fof(f6,plain,(
% 1.34/0.56    ? [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) <~> (X1 = X3 & X0 = X2))),
% 1.34/0.56    inference(ennf_transformation,[],[f5])).
% 1.34/0.56  fof(f5,negated_conjecture,(
% 1.34/0.56    ~! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) <=> (X1 = X3 & X0 = X2))),
% 1.34/0.56    inference(negated_conjecture,[],[f4])).
% 1.34/0.56  fof(f4,conjecture,(
% 1.34/0.56    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) <=> (X1 = X3 & X0 = X2))),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_zfmisc_1)).
% 1.34/0.56  fof(f57,plain,(
% 1.34/0.56    spl5_4 | spl5_3),
% 1.34/0.56    inference(avatar_split_clause,[],[f29,f49,f54])).
% 1.34/0.56  fof(f29,plain,(
% 1.34/0.56    sK1 = sK3 | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))),
% 1.34/0.56    inference(definition_unfolding,[],[f18,f20,f20])).
% 1.34/0.56  fof(f18,plain,(
% 1.34/0.56    sK1 = sK3 | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3)))),
% 1.34/0.56    inference(cnf_transformation,[],[f10])).
% 1.34/0.56  fof(f52,plain,(
% 1.34/0.56    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 1.34/0.56    inference(avatar_split_clause,[],[f39,f49,f45,f41])).
% 1.34/0.56  fof(f39,plain,(
% 1.34/0.56    sK1 != sK3 | sK0 != sK2 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 1.34/0.56    inference(inner_rewriting,[],[f38])).
% 1.34/0.56  fof(f38,plain,(
% 1.34/0.56    sK1 != sK3 | sK0 != sK2 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 1.34/0.56    inference(inner_rewriting,[],[f28])).
% 1.34/0.56  fof(f28,plain,(
% 1.34/0.56    sK1 != sK3 | sK0 != sK2 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))),
% 1.34/0.56    inference(definition_unfolding,[],[f19,f20,f20])).
% 1.34/0.56  fof(f19,plain,(
% 1.34/0.56    sK1 != sK3 | sK0 != sK2 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3)))),
% 1.34/0.56    inference(cnf_transformation,[],[f10])).
% 1.34/0.56  % SZS output end Proof for theBenchmark
% 1.34/0.56  % (24396)------------------------------
% 1.34/0.56  % (24396)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.56  % (24396)Termination reason: Refutation
% 1.34/0.56  
% 1.34/0.56  % (24396)Memory used [KB]: 10746
% 1.34/0.56  % (24396)Time elapsed: 0.126 s
% 1.34/0.56  % (24396)------------------------------
% 1.34/0.56  % (24396)------------------------------
% 1.34/0.56  % (24406)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.34/0.56  % (24389)Success in time 0.194 s
%------------------------------------------------------------------------------
