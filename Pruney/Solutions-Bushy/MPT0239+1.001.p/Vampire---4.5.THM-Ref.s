%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0239+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 101 expanded)
%              Number of leaves         :    9 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :  174 ( 434 expanded)
%              Number of equality atoms :   70 ( 204 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f127,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f48,f49,f76,f117,f126])).

fof(f126,plain,
    ( spl5_2
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f121,f38])).

fof(f38,plain,
    ( sK0 != sK2
    | spl5_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl5_2
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f121,plain,
    ( sK0 = sK2
    | ~ spl5_4 ),
    inference(resolution,[],[f99,f28])).

fof(f28,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f11,f12])).

fof(f12,plain,(
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

% (15641)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% (15640)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% (15636)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% (15656)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% (15657)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% (15654)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% (15650)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% (15652)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% (15634)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% (15653)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% (15645)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% (15649)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% (15632)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% (15633)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% (15637)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% (15638)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
fof(f11,plain,(
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
    inference(rectify,[],[f10])).

% (15643)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
fof(f10,plain,(
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

fof(f99,plain,
    ( r2_hidden(sK0,k1_tarski(sK2))
    | ~ spl5_4 ),
    inference(resolution,[],[f47,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f47,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl5_4
  <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f117,plain,
    ( spl5_3
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f112,f42])).

fof(f42,plain,
    ( sK1 != sK3
    | spl5_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl5_3
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f112,plain,
    ( sK1 = sK3
    | ~ spl5_4 ),
    inference(resolution,[],[f98,f28])).

fof(f98,plain,
    ( r2_hidden(sK1,k1_tarski(sK3))
    | ~ spl5_4 ),
    inference(resolution,[],[f47,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f76,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f70])).

fof(f70,plain,
    ( $false
    | spl5_1 ),
    inference(resolution,[],[f61,f34])).

fof(f34,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl5_1
  <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f61,plain,(
    ! [X0,X1] : r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1))) ),
    inference(resolution,[],[f57,f27])).

fof(f27,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X1))) ) ),
    inference(resolution,[],[f25,f27])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f49,plain,
    ( spl5_4
    | spl5_2 ),
    inference(avatar_split_clause,[],[f16,f36,f45])).

fof(f16,plain,
    ( sK0 = sK2
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( ( sK1 != sK3
      | sK0 != sK2
      | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) )
    & ( ( sK1 = sK3
        & sK0 = sK2 )
      | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).

% (15637)Refutation not found, incomplete strategy% (15637)------------------------------
% (15637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15639)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% (15637)Termination reason: Refutation not found, incomplete strategy

% (15637)Memory used [KB]: 6140
% (15637)Time elapsed: 0.058 s
% (15637)------------------------------
% (15637)------------------------------
% (15635)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% (15646)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (15647)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
fof(f8,plain,
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

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) )
      & ( ( X1 = X3
          & X0 = X2 )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) )
      & ( ( X1 = X3
          & X0 = X2 )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
    <~> ( X1 = X3
        & X0 = X2 ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
      <=> ( X1 = X3
          & X0 = X2 ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
    <=> ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_zfmisc_1)).

fof(f48,plain,
    ( spl5_4
    | spl5_3 ),
    inference(avatar_split_clause,[],[f17,f40,f45])).

fof(f17,plain,
    ( sK1 = sK3
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f9])).

fof(f43,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f30,f40,f36,f32])).

fof(f30,plain,
    ( sK1 != sK3
    | sK0 != sK2
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(inner_rewriting,[],[f29])).

fof(f29,plain,
    ( sK1 != sK3
    | sK0 != sK2
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK1))) ),
    inference(inner_rewriting,[],[f18])).

fof(f18,plain,
    ( sK1 != sK3
    | sK0 != sK2
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f9])).

%------------------------------------------------------------------------------
