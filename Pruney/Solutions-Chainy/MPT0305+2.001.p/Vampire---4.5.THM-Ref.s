%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:04 EST 2020

% Result     : Theorem 3.37s
% Output     : Refutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 142 expanded)
%              Number of leaves         :   10 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :  148 ( 512 expanded)
%              Number of equality atoms :   11 (  42 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6057,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f312,f4297,f5788,f6056])).

fof(f6056,plain,
    ( spl9_154
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f6055,f309,f4121])).

fof(f4121,plain,
    ( spl9_154
  <=> ! [X1] : ~ r2_hidden(X1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_154])])).

fof(f309,plain,
    ( spl9_2
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f6055,plain,
    ( ! [X4] : ~ r2_hidden(X4,sK0)
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f6034,f317])).

fof(f317,plain,(
    ~ r2_hidden(sK4(sK1,sK2),sK2) ),
    inference(resolution,[],[f130,f173])).

fof(f173,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f97,f98])).

fof(f98,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f130,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,
    ( ~ r1_tarski(sK1,sK2)
    & ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2))
      | r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0)) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f67,f89])).

fof(f89,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 )
   => ( ~ r1_tarski(sK1,sK2)
      & ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2))
        | r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0)) )
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X1,X2)
      & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f64])).

fof(f64,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ r1_tarski(X1,X2)
          & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
            | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f63])).

fof(f63,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f6034,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK0)
        | r2_hidden(sK4(sK1,sK2),sK2) )
    | ~ spl9_2 ),
    inference(resolution,[],[f453,f4350])).

fof(f4350,plain,
    ( ! [X35,X36] :
        ( ~ r2_hidden(k4_tarski(X35,X36),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X36,sK2) )
    | ~ spl9_2 ),
    inference(resolution,[],[f4305,f226])).

fof(f226,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f127])).

fof(f127,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f126])).

fof(f126,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f4305,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(sK0,sK2))
        | ~ r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) )
    | ~ spl9_2 ),
    inference(resolution,[],[f311,f171])).

fof(f171,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f99])).

fof(f311,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2))
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f309])).

fof(f453,plain,(
    ! [X6,X5] :
      ( r2_hidden(k4_tarski(X5,sK4(sK1,sK2)),k2_zfmisc_1(X6,sK1))
      | ~ r2_hidden(X5,X6) ) ),
    inference(resolution,[],[f316,f227])).

fof(f227,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f127])).

fof(f316,plain,(
    r2_hidden(sK4(sK1,sK2),sK1) ),
    inference(resolution,[],[f130,f172])).

fof(f172,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f99])).

fof(f5788,plain,
    ( spl9_154
    | ~ spl9_1 ),
    inference(avatar_split_clause,[],[f5787,f305,f4121])).

fof(f305,plain,
    ( spl9_1
  <=> r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f5787,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f5764,f317])).

fof(f5764,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(sK4(sK1,sK2),sK2) )
    | ~ spl9_1 ),
    inference(resolution,[],[f452,f3467])).

fof(f3467,plain,
    ( ! [X33,X34] :
        ( ~ r2_hidden(k4_tarski(X33,X34),k2_zfmisc_1(sK1,sK0))
        | r2_hidden(X33,sK2) )
    | ~ spl9_1 ),
    inference(resolution,[],[f3389,f225])).

fof(f225,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f127])).

fof(f3389,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(sK2,sK0))
        | ~ r2_hidden(X0,k2_zfmisc_1(sK1,sK0)) )
    | ~ spl9_1 ),
    inference(resolution,[],[f307,f171])).

fof(f307,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0))
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f305])).

fof(f452,plain,(
    ! [X4,X3] :
      ( r2_hidden(k4_tarski(sK4(sK1,sK2),X3),k2_zfmisc_1(sK1,X4))
      | ~ r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f316,f227])).

fof(f4297,plain,(
    ~ spl9_154 ),
    inference(avatar_contradiction_clause,[],[f4284])).

fof(f4284,plain,
    ( $false
    | ~ spl9_154 ),
    inference(resolution,[],[f4122,f374])).

fof(f374,plain,(
    r2_hidden(sK4(sK0,k1_xboole_0),sK0) ),
    inference(resolution,[],[f319,f172])).

fof(f319,plain,(
    ~ r1_tarski(sK0,k1_xboole_0) ),
    inference(resolution,[],[f244,f251])).

fof(f251,plain,(
    ! [X0] :
      ( sQ8_eqProxy(k1_xboole_0,X0)
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(equality_proxy_replacement,[],[f140,f241])).

fof(f241,plain,(
    ! [X1,X0] :
      ( sQ8_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ8_eqProxy])])).

fof(f140,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f244,plain,(
    ~ sQ8_eqProxy(k1_xboole_0,sK0) ),
    inference(equality_proxy_replacement,[],[f128,f241])).

fof(f128,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f90])).

fof(f4122,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK0)
    | ~ spl9_154 ),
    inference(avatar_component_clause,[],[f4121])).

fof(f312,plain,
    ( spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f129,f309,f305])).

fof(f129,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2))
    | r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f90])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:21:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.49  % (12065)lrs+11_4_av=off:gsp=input_only:irw=on:lma=on:nm=0:nwc=1.2:stl=30:sd=2:ss=axioms:sp=reverse_arity:urr=on:updr=off_8 on theBenchmark
% 0.21/0.50  % (12082)ott+11_4:1_awrs=converge:awrsf=16:acc=model:add=large:afr=on:afp=4000:afq=1.4:amm=off:br=off:cond=fast:fde=none:gsp=input_only:nm=64:nwc=2:nicw=on:sd=3:ss=axioms:s2a=on:sac=on:sp=frequency:urr=on:updr=off_70 on theBenchmark
% 0.21/0.51  % (12060)lrs-11_3_av=off:bs=unit_only:bsr=on:cond=on:gsp=input_only:gs=on:gsem=on:lma=on:nm=2:nwc=1:stl=30:sd=3:ss=axioms:st=1.2:sos=all:sp=reverse_arity:urr=on:updr=off_11 on theBenchmark
% 0.21/0.52  % (12074)dis+4_2_av=off:bs=on:fsr=off:gsp=input_only:newcnf=on:nwc=1:sd=3:ss=axioms:st=3.0:sos=all:sp=reverse_arity:urr=ec_only:updr=off_127 on theBenchmark
% 0.21/0.52  % (12067)dis+1004_1_aac=none:acc=on:afp=40000:afq=1.2:anc=none:cond=on:fde=unused:gs=on:gsem=off:irw=on:nm=32:nwc=2:sd=1:ss=axioms:sos=theory:sp=reverse_arity:urr=ec_only_17 on theBenchmark
% 0.21/0.52  % (12073)dis+10_5:4_add=off:afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sd=3:ss=axioms:st=3.0:sos=all:sp=occurrence:urr=on:updr=off_15 on theBenchmark
% 0.21/0.52  % (12069)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_11 on theBenchmark
% 0.21/0.52  % (12061)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.52  % (12077)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (12084)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (12076)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.52  % (12071)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_3 on theBenchmark
% 0.21/0.52  % (12083)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_157 on theBenchmark
% 0.21/0.53  % (12090)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.53  % (12068)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_6 on theBenchmark
% 1.34/0.53  % (12087)dis+11_2_add=large:afr=on:anc=none:gs=on:gsem=on:lwlo=on:nm=16:nwc=1:sd=1:ss=axioms:st=3.0:sos=on_4 on theBenchmark
% 1.34/0.53  % (12067)Refutation not found, incomplete strategy% (12067)------------------------------
% 1.34/0.53  % (12067)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (12067)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.53  
% 1.34/0.53  % (12067)Memory used [KB]: 10746
% 1.34/0.53  % (12067)Time elapsed: 0.107 s
% 1.34/0.53  % (12067)------------------------------
% 1.34/0.53  % (12067)------------------------------
% 1.34/0.53  % (12063)lrs+2_5:4_av=off:bce=on:cond=fast:ep=R:fde=none:gs=on:lcm=reverse:lwlo=on:nwc=1:stl=30:sd=1:ss=axioms:sos=all:sp=occurrence_8 on theBenchmark
% 1.34/0.53  % (12064)dis+4_8:1_add=large:afp=100000:afq=1.4:ep=RST:fde=unused:gsp=input_only:lcm=predicate:nwc=1:sos=all:sp=occurrence:updr=off:uhcvi=on_33 on theBenchmark
% 1.34/0.54  % (12085)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.34/0.54  % (12075)dis+1002_5_av=off:cond=on:gs=on:lma=on:nm=2:nwc=1:sd=3:ss=axioms:st=1.5:sos=on:updr=off_4 on theBenchmark
% 1.34/0.54  % (12079)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_11 on theBenchmark
% 1.34/0.54  % (12075)Refutation not found, incomplete strategy% (12075)------------------------------
% 1.34/0.54  % (12075)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (12075)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (12075)Memory used [KB]: 6268
% 1.34/0.54  % (12075)Time elapsed: 0.140 s
% 1.34/0.54  % (12075)------------------------------
% 1.34/0.54  % (12075)------------------------------
% 1.34/0.54  % (12072)dis+1010_2:3_afr=on:afp=40000:afq=1.4:amm=off:anc=none:lma=on:nm=16:nwc=1:sp=occurrence:updr=off:uhcvi=on_34 on theBenchmark
% 1.34/0.54  % (12062)lrs+1002_8:1_av=off:cond=on:gsp=input_only:gs=on:irw=on:lma=on:nm=0:nwc=1.7:stl=30:sd=2:ss=axioms:sos=on:sp=occurrence:urr=on_41 on theBenchmark
% 1.34/0.54  % (12080)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_6 on theBenchmark
% 1.34/0.54  % (12085)Refutation not found, incomplete strategy% (12085)------------------------------
% 1.34/0.54  % (12085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (12085)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (12085)Memory used [KB]: 10746
% 1.34/0.54  % (12085)Time elapsed: 0.143 s
% 1.34/0.54  % (12085)------------------------------
% 1.34/0.54  % (12085)------------------------------
% 1.34/0.54  % (12086)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_88 on theBenchmark
% 1.51/0.55  % (12089)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_4 on theBenchmark
% 1.51/0.55  % (12088)ott+11_8:1_av=off:bs=on:bce=on:fde=none:gsp=input_only:gs=on:gsem=on:irw=on:lcm=predicate:nm=6:nwc=1.5:sd=2:ss=axioms:st=1.2:sos=theory:urr=on:updr=off_49 on theBenchmark
% 1.51/0.56  % (12081)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=2.0:amm=sco:anc=none:gs=on:gsem=off:lma=on:lwlo=on:nm=4:nwc=10:stl=30:sd=3:ss=axioms:sos=all:sac=on_49 on theBenchmark
% 1.51/0.56  % (12078)lrs-2_3:2_av=off:bce=on:cond=on:gsp=input_only:gs=on:gsem=on:lcm=predicate:lma=on:newcnf=on:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off:uhcvi=on_62 on theBenchmark
% 1.51/0.56  % (12070)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_6 on theBenchmark
% 1.51/0.58  % (12087)Refutation not found, incomplete strategy% (12087)------------------------------
% 1.51/0.58  % (12087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.58  % (12087)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.58  
% 1.51/0.58  % (12087)Memory used [KB]: 11001
% 1.51/0.58  % (12087)Time elapsed: 0.176 s
% 1.51/0.58  % (12087)------------------------------
% 1.51/0.58  % (12087)------------------------------
% 2.06/0.65  % (12097)ott+1_5:1_acc=on:add=off:afr=on:afp=100000:afq=1.1:amm=sco:anc=none:lcm=predicate:nm=16:nwc=1.1:sd=1:ss=axioms:st=3.0:sos=on:sac=on:updr=off_18 on theBenchmark
% 2.06/0.67  % (12096)dis+1011_8:1_aac=none:acc=on:afp=1000:afq=1.4:amm=off:anc=all:bs=unit_only:bce=on:ccuc=small_ones:fsr=off:fde=unused:gsp=input_only:gs=on:gsem=off:lma=on:nm=16:nwc=2.5:sd=4:ss=axioms:st=1.5:sos=all:uhcvi=on_65 on theBenchmark
% 2.39/0.68  % (12068)Refutation not found, incomplete strategy% (12068)------------------------------
% 2.39/0.68  % (12068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.39/0.68  % (12068)Termination reason: Refutation not found, incomplete strategy
% 2.39/0.68  
% 2.39/0.68  % (12068)Memory used [KB]: 6268
% 2.39/0.68  % (12068)Time elapsed: 0.249 s
% 2.39/0.68  % (12068)------------------------------
% 2.39/0.68  % (12068)------------------------------
% 2.39/0.68  % (12098)lrs+1002_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:cond=fast:fde=none:gs=on:gsem=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence_8 on theBenchmark
% 2.39/0.70  % (12098)Refutation not found, incomplete strategy% (12098)------------------------------
% 2.39/0.70  % (12098)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.39/0.70  % (12098)Termination reason: Refutation not found, incomplete strategy
% 2.39/0.70  
% 2.39/0.70  % (12098)Memory used [KB]: 10746
% 2.39/0.70  % (12098)Time elapsed: 0.126 s
% 2.39/0.70  % (12098)------------------------------
% 2.39/0.70  % (12098)------------------------------
% 2.39/0.72  % (12105)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_4 on theBenchmark
% 3.37/0.83  % (12064)Refutation found. Thanks to Tanya!
% 3.37/0.83  % SZS status Theorem for theBenchmark
% 3.37/0.83  % SZS output start Proof for theBenchmark
% 3.37/0.83  fof(f6057,plain,(
% 3.37/0.83    $false),
% 3.37/0.83    inference(avatar_sat_refutation,[],[f312,f4297,f5788,f6056])).
% 3.37/0.83  fof(f6056,plain,(
% 3.37/0.83    spl9_154 | ~spl9_2),
% 3.37/0.83    inference(avatar_split_clause,[],[f6055,f309,f4121])).
% 3.37/0.83  fof(f4121,plain,(
% 3.37/0.83    spl9_154 <=> ! [X1] : ~r2_hidden(X1,sK0)),
% 3.37/0.83    introduced(avatar_definition,[new_symbols(naming,[spl9_154])])).
% 3.37/0.83  fof(f309,plain,(
% 3.37/0.83    spl9_2 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2))),
% 3.37/0.83    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 3.37/0.83  fof(f6055,plain,(
% 3.37/0.83    ( ! [X4] : (~r2_hidden(X4,sK0)) ) | ~spl9_2),
% 3.37/0.83    inference(subsumption_resolution,[],[f6034,f317])).
% 3.37/0.83  fof(f317,plain,(
% 3.37/0.83    ~r2_hidden(sK4(sK1,sK2),sK2)),
% 3.37/0.83    inference(resolution,[],[f130,f173])).
% 3.37/0.83  fof(f173,plain,(
% 3.37/0.83    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK4(X0,X1),X1)) )),
% 3.37/0.83    inference(cnf_transformation,[],[f99])).
% 3.37/0.83  fof(f99,plain,(
% 3.37/0.83    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.37/0.83    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f97,f98])).
% 3.37/0.83  fof(f98,plain,(
% 3.37/0.83    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 3.37/0.83    introduced(choice_axiom,[])).
% 3.37/0.83  fof(f97,plain,(
% 3.37/0.83    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.37/0.83    inference(rectify,[],[f96])).
% 3.37/0.83  fof(f96,plain,(
% 3.37/0.83    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.37/0.83    inference(nnf_transformation,[],[f77])).
% 3.37/0.83  fof(f77,plain,(
% 3.37/0.83    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.37/0.83    inference(ennf_transformation,[],[f3])).
% 3.37/0.83  fof(f3,axiom,(
% 3.37/0.83    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.37/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 3.37/0.83  fof(f130,plain,(
% 3.37/0.83    ~r1_tarski(sK1,sK2)),
% 3.37/0.83    inference(cnf_transformation,[],[f90])).
% 3.37/0.83  fof(f90,plain,(
% 3.37/0.83    ~r1_tarski(sK1,sK2) & (r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2)) | r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0))) & k1_xboole_0 != sK0),
% 3.37/0.83    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f67,f89])).
% 3.37/0.83  fof(f89,plain,(
% 3.37/0.83    ? [X0,X1,X2] : (~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0) => (~r1_tarski(sK1,sK2) & (r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2)) | r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0))) & k1_xboole_0 != sK0)),
% 3.37/0.83    introduced(choice_axiom,[])).
% 3.37/0.83  fof(f67,plain,(
% 3.37/0.83    ? [X0,X1,X2] : (~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 3.37/0.83    inference(ennf_transformation,[],[f64])).
% 3.37/0.83  fof(f64,negated_conjecture,(
% 3.37/0.83    ~! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 3.37/0.83    inference(negated_conjecture,[],[f63])).
% 3.37/0.83  fof(f63,conjecture,(
% 3.37/0.83    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 3.37/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 3.37/0.83  fof(f6034,plain,(
% 3.37/0.83    ( ! [X4] : (~r2_hidden(X4,sK0) | r2_hidden(sK4(sK1,sK2),sK2)) ) | ~spl9_2),
% 3.37/0.83    inference(resolution,[],[f453,f4350])).
% 3.37/0.83  fof(f4350,plain,(
% 3.37/0.83    ( ! [X35,X36] : (~r2_hidden(k4_tarski(X35,X36),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X36,sK2)) ) | ~spl9_2),
% 3.37/0.83    inference(resolution,[],[f4305,f226])).
% 3.37/0.83  fof(f226,plain,(
% 3.37/0.83    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 3.37/0.83    inference(cnf_transformation,[],[f127])).
% 3.37/0.83  fof(f127,plain,(
% 3.37/0.83    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.37/0.83    inference(flattening,[],[f126])).
% 3.37/0.83  fof(f126,plain,(
% 3.37/0.83    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.37/0.83    inference(nnf_transformation,[],[f43])).
% 3.37/0.83  fof(f43,axiom,(
% 3.37/0.83    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 3.37/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 3.37/0.83  fof(f4305,plain,(
% 3.37/0.83    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK0,sK2)) | ~r2_hidden(X0,k2_zfmisc_1(sK0,sK1))) ) | ~spl9_2),
% 3.37/0.83    inference(resolution,[],[f311,f171])).
% 3.37/0.83  fof(f171,plain,(
% 3.37/0.83    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.37/0.83    inference(cnf_transformation,[],[f99])).
% 3.37/0.83  fof(f311,plain,(
% 3.37/0.83    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2)) | ~spl9_2),
% 3.37/0.83    inference(avatar_component_clause,[],[f309])).
% 3.37/0.83  fof(f453,plain,(
% 3.37/0.83    ( ! [X6,X5] : (r2_hidden(k4_tarski(X5,sK4(sK1,sK2)),k2_zfmisc_1(X6,sK1)) | ~r2_hidden(X5,X6)) )),
% 3.37/0.83    inference(resolution,[],[f316,f227])).
% 3.37/0.83  fof(f227,plain,(
% 3.37/0.83    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 3.37/0.83    inference(cnf_transformation,[],[f127])).
% 3.37/0.83  fof(f316,plain,(
% 3.37/0.83    r2_hidden(sK4(sK1,sK2),sK1)),
% 3.37/0.83    inference(resolution,[],[f130,f172])).
% 3.37/0.83  fof(f172,plain,(
% 3.37/0.83    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 3.37/0.83    inference(cnf_transformation,[],[f99])).
% 3.37/0.83  fof(f5788,plain,(
% 3.37/0.83    spl9_154 | ~spl9_1),
% 3.37/0.83    inference(avatar_split_clause,[],[f5787,f305,f4121])).
% 3.37/0.83  fof(f305,plain,(
% 3.37/0.83    spl9_1 <=> r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0))),
% 3.37/0.83    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 3.37/0.83  fof(f5787,plain,(
% 3.37/0.83    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl9_1),
% 3.37/0.83    inference(subsumption_resolution,[],[f5764,f317])).
% 3.37/0.83  fof(f5764,plain,(
% 3.37/0.83    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(sK4(sK1,sK2),sK2)) ) | ~spl9_1),
% 3.37/0.83    inference(resolution,[],[f452,f3467])).
% 3.37/0.83  fof(f3467,plain,(
% 3.37/0.83    ( ! [X33,X34] : (~r2_hidden(k4_tarski(X33,X34),k2_zfmisc_1(sK1,sK0)) | r2_hidden(X33,sK2)) ) | ~spl9_1),
% 3.37/0.83    inference(resolution,[],[f3389,f225])).
% 3.37/0.83  fof(f225,plain,(
% 3.37/0.83    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 3.37/0.83    inference(cnf_transformation,[],[f127])).
% 3.37/0.83  fof(f3389,plain,(
% 3.37/0.83    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK2,sK0)) | ~r2_hidden(X0,k2_zfmisc_1(sK1,sK0))) ) | ~spl9_1),
% 3.37/0.83    inference(resolution,[],[f307,f171])).
% 3.37/0.83  fof(f307,plain,(
% 3.37/0.83    r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0)) | ~spl9_1),
% 3.37/0.83    inference(avatar_component_clause,[],[f305])).
% 3.37/0.83  fof(f452,plain,(
% 3.37/0.83    ( ! [X4,X3] : (r2_hidden(k4_tarski(sK4(sK1,sK2),X3),k2_zfmisc_1(sK1,X4)) | ~r2_hidden(X3,X4)) )),
% 3.37/0.83    inference(resolution,[],[f316,f227])).
% 3.37/0.83  fof(f4297,plain,(
% 3.37/0.83    ~spl9_154),
% 3.37/0.83    inference(avatar_contradiction_clause,[],[f4284])).
% 3.37/0.83  fof(f4284,plain,(
% 3.37/0.83    $false | ~spl9_154),
% 3.37/0.83    inference(resolution,[],[f4122,f374])).
% 3.37/0.83  fof(f374,plain,(
% 3.37/0.83    r2_hidden(sK4(sK0,k1_xboole_0),sK0)),
% 3.37/0.83    inference(resolution,[],[f319,f172])).
% 3.37/0.83  fof(f319,plain,(
% 3.37/0.83    ~r1_tarski(sK0,k1_xboole_0)),
% 3.37/0.83    inference(resolution,[],[f244,f251])).
% 3.37/0.83  fof(f251,plain,(
% 3.37/0.83    ( ! [X0] : (sQ8_eqProxy(k1_xboole_0,X0) | ~r1_tarski(X0,k1_xboole_0)) )),
% 3.37/0.83    inference(equality_proxy_replacement,[],[f140,f241])).
% 3.37/0.83  fof(f241,plain,(
% 3.37/0.83    ! [X1,X0] : (sQ8_eqProxy(X0,X1) <=> X0 = X1)),
% 3.37/0.83    introduced(equality_proxy_definition,[new_symbols(naming,[sQ8_eqProxy])])).
% 3.37/0.83  fof(f140,plain,(
% 3.37/0.83    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 3.37/0.83    inference(cnf_transformation,[],[f69])).
% 3.37/0.83  fof(f69,plain,(
% 3.37/0.83    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 3.37/0.83    inference(ennf_transformation,[],[f26])).
% 3.37/0.83  fof(f26,axiom,(
% 3.37/0.83    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 3.37/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 3.37/0.83  fof(f244,plain,(
% 3.37/0.83    ~sQ8_eqProxy(k1_xboole_0,sK0)),
% 3.37/0.83    inference(equality_proxy_replacement,[],[f128,f241])).
% 3.37/0.83  fof(f128,plain,(
% 3.37/0.83    k1_xboole_0 != sK0),
% 3.37/0.83    inference(cnf_transformation,[],[f90])).
% 3.37/0.83  fof(f4122,plain,(
% 3.37/0.83    ( ! [X1] : (~r2_hidden(X1,sK0)) ) | ~spl9_154),
% 3.37/0.83    inference(avatar_component_clause,[],[f4121])).
% 3.37/0.83  fof(f312,plain,(
% 3.37/0.83    spl9_1 | spl9_2),
% 3.37/0.83    inference(avatar_split_clause,[],[f129,f309,f305])).
% 3.37/0.83  fof(f129,plain,(
% 3.37/0.83    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2)) | r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0))),
% 3.37/0.83    inference(cnf_transformation,[],[f90])).
% 3.37/0.83  % SZS output end Proof for theBenchmark
% 3.37/0.83  % (12064)------------------------------
% 3.37/0.83  % (12064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.37/0.83  % (12064)Termination reason: Refutation
% 3.37/0.83  
% 3.37/0.83  % (12064)Memory used [KB]: 8699
% 3.37/0.83  % (12064)Time elapsed: 0.428 s
% 3.37/0.83  % (12064)------------------------------
% 3.37/0.83  % (12064)------------------------------
% 3.37/0.84  % (12059)Success in time 0.477 s
%------------------------------------------------------------------------------
