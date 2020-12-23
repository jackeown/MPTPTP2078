%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:42 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   44 (  72 expanded)
%              Number of leaves         :   14 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :  154 ( 225 expanded)
%              Number of equality atoms :   49 ( 106 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f394,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f140,f381,f385])).

fof(f385,plain,(
    ~ spl6_17 ),
    inference(avatar_contradiction_clause,[],[f384])).

fof(f384,plain,
    ( $false
    | ~ spl6_17 ),
    inference(resolution,[],[f380,f48])).

fof(f48,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f23,f39])).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f23,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f380,plain,
    ( r2_hidden(k4_tarski(sK4(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f379])).

fof(f379,plain,
    ( spl6_17
  <=> r2_hidden(k4_tarski(sK4(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f381,plain,
    ( spl6_17
    | spl6_2 ),
    inference(avatar_split_clause,[],[f376,f45,f379])).

fof(f45,plain,
    ( spl6_2
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f376,plain,
    ( r2_hidden(k4_tarski(sK4(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | spl6_2 ),
    inference(trivial_inequality_removal,[],[f375])).

fof(f375,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(k4_tarski(sK4(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | spl6_2 ),
    inference(superposition,[],[f46,f198])).

fof(f198,plain,(
    ! [X3] :
      ( k1_xboole_0 = k2_relat_1(X3)
      | r2_hidden(k4_tarski(sK4(X3,k1_xboole_0),sK3(X3,k1_xboole_0)),X3) ) ),
    inference(resolution,[],[f30,f48])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f15,f18,f17,f16])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f46,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f140,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f122,f42])).

fof(f42,plain,
    ( spl6_1
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f122,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f102,f48])).

fof(f102,plain,(
    ! [X3] :
      ( r2_hidden(k4_tarski(sK0(X3,k1_xboole_0),sK1(X3,k1_xboole_0)),X3)
      | k1_xboole_0 = k1_relat_1(X3) ) ),
    inference(resolution,[],[f26,f48])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK0(X0,X1),X3),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12,f11,f10])).

fof(f10,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK0(X0,X1),X3),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK0(X0,X1),X4),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK0(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f47,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f22,f45,f42])).

fof(f22,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:55:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.23/0.48  % (14088)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.23/0.49  % (14088)Refutation found. Thanks to Tanya!
% 0.23/0.49  % SZS status Theorem for theBenchmark
% 0.23/0.49  % (14097)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.23/0.50  % (14096)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.23/0.50  % (14097)Refutation not found, incomplete strategy% (14097)------------------------------
% 0.23/0.50  % (14097)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.50  % (14097)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.50  
% 0.23/0.50  % (14097)Memory used [KB]: 6140
% 0.23/0.50  % (14097)Time elapsed: 0.006 s
% 0.23/0.50  % (14097)------------------------------
% 0.23/0.50  % (14097)------------------------------
% 0.23/0.50  % (14090)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.23/0.50  % (14089)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.23/0.50  % (14082)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.23/0.50  % (14082)Refutation not found, incomplete strategy% (14082)------------------------------
% 0.23/0.50  % (14082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.50  % (14082)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.50  
% 0.23/0.50  % (14082)Memory used [KB]: 6140
% 0.23/0.50  % (14082)Time elapsed: 0.074 s
% 0.23/0.50  % (14082)------------------------------
% 0.23/0.50  % (14082)------------------------------
% 0.23/0.51  % SZS output start Proof for theBenchmark
% 0.23/0.51  fof(f394,plain,(
% 0.23/0.51    $false),
% 0.23/0.51    inference(avatar_sat_refutation,[],[f47,f140,f381,f385])).
% 0.23/0.51  fof(f385,plain,(
% 0.23/0.51    ~spl6_17),
% 0.23/0.51    inference(avatar_contradiction_clause,[],[f384])).
% 0.23/0.51  fof(f384,plain,(
% 0.23/0.51    $false | ~spl6_17),
% 0.23/0.51    inference(resolution,[],[f380,f48])).
% 0.23/0.51  fof(f48,plain,(
% 0.23/0.51    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.23/0.51    inference(superposition,[],[f23,f39])).
% 0.23/0.51  fof(f39,plain,(
% 0.23/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.23/0.51    inference(equality_resolution,[],[f34])).
% 0.23/0.51  fof(f34,plain,(
% 0.23/0.51    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.23/0.51    inference(cnf_transformation,[],[f21])).
% 0.23/0.51  fof(f21,plain,(
% 0.23/0.51    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.23/0.51    inference(flattening,[],[f20])).
% 0.23/0.51  fof(f20,plain,(
% 0.23/0.51    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.23/0.51    inference(nnf_transformation,[],[f1])).
% 0.23/0.51  fof(f1,axiom,(
% 0.23/0.51    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.23/0.51  fof(f23,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.23/0.51    inference(cnf_transformation,[],[f2])).
% 0.23/0.51  fof(f2,axiom,(
% 0.23/0.51    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.23/0.51  fof(f380,plain,(
% 0.23/0.51    r2_hidden(k4_tarski(sK4(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | ~spl6_17),
% 0.23/0.51    inference(avatar_component_clause,[],[f379])).
% 0.23/0.51  fof(f379,plain,(
% 0.23/0.51    spl6_17 <=> r2_hidden(k4_tarski(sK4(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k1_xboole_0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.23/0.51  fof(f381,plain,(
% 0.23/0.51    spl6_17 | spl6_2),
% 0.23/0.51    inference(avatar_split_clause,[],[f376,f45,f379])).
% 0.23/0.51  fof(f45,plain,(
% 0.23/0.51    spl6_2 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.23/0.51  fof(f376,plain,(
% 0.23/0.51    r2_hidden(k4_tarski(sK4(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | spl6_2),
% 0.23/0.51    inference(trivial_inequality_removal,[],[f375])).
% 0.23/0.51  fof(f375,plain,(
% 0.23/0.51    k1_xboole_0 != k1_xboole_0 | r2_hidden(k4_tarski(sK4(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | spl6_2),
% 0.23/0.51    inference(superposition,[],[f46,f198])).
% 0.23/0.51  fof(f198,plain,(
% 0.23/0.51    ( ! [X3] : (k1_xboole_0 = k2_relat_1(X3) | r2_hidden(k4_tarski(sK4(X3,k1_xboole_0),sK3(X3,k1_xboole_0)),X3)) )),
% 0.23/0.51    inference(resolution,[],[f30,f48])).
% 0.23/0.51  fof(f30,plain,(
% 0.23/0.51    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | k2_relat_1(X0) = X1) )),
% 0.23/0.51    inference(cnf_transformation,[],[f19])).
% 0.23/0.51  fof(f19,plain,(
% 0.23/0.51    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.23/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f15,f18,f17,f16])).
% 0.23/0.51  fof(f16,plain,(
% 0.23/0.51    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.23/0.51    introduced(choice_axiom,[])).
% 0.23/0.51  fof(f17,plain,(
% 0.23/0.51    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) => r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0))),
% 0.23/0.51    introduced(choice_axiom,[])).
% 0.23/0.51  fof(f18,plain,(
% 0.23/0.51    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0))),
% 0.23/0.51    introduced(choice_axiom,[])).
% 0.23/0.51  fof(f15,plain,(
% 0.23/0.51    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.23/0.51    inference(rectify,[],[f14])).
% 0.23/0.51  fof(f14,plain,(
% 0.23/0.51    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.23/0.51    inference(nnf_transformation,[],[f4])).
% 0.23/0.51  fof(f4,axiom,(
% 0.23/0.51    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 0.23/0.51  fof(f46,plain,(
% 0.23/0.51    k1_xboole_0 != k2_relat_1(k1_xboole_0) | spl6_2),
% 0.23/0.51    inference(avatar_component_clause,[],[f45])).
% 0.23/0.51  fof(f140,plain,(
% 0.23/0.51    spl6_1),
% 0.23/0.51    inference(avatar_split_clause,[],[f122,f42])).
% 0.23/0.51  fof(f42,plain,(
% 0.23/0.51    spl6_1 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.23/0.51  fof(f122,plain,(
% 0.23/0.51    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.23/0.51    inference(resolution,[],[f102,f48])).
% 0.23/0.51  fof(f102,plain,(
% 0.23/0.51    ( ! [X3] : (r2_hidden(k4_tarski(sK0(X3,k1_xboole_0),sK1(X3,k1_xboole_0)),X3) | k1_xboole_0 = k1_relat_1(X3)) )),
% 0.23/0.51    inference(resolution,[],[f26,f48])).
% 0.23/0.51  fof(f26,plain,(
% 0.23/0.51    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) | k1_relat_1(X0) = X1) )),
% 0.23/0.51    inference(cnf_transformation,[],[f13])).
% 0.23/0.51  fof(f13,plain,(
% 0.23/0.51    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK0(X0,X1),X3),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.23/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12,f11,f10])).
% 0.23/0.51  fof(f10,plain,(
% 0.23/0.51    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK0(X0,X1),X3),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK0(X0,X1),X4),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 0.23/0.51    introduced(choice_axiom,[])).
% 0.23/0.51  fof(f11,plain,(
% 0.23/0.51    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK0(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0))),
% 0.23/0.51    introduced(choice_axiom,[])).
% 0.23/0.51  fof(f12,plain,(
% 0.23/0.51    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0))),
% 0.23/0.51    introduced(choice_axiom,[])).
% 0.23/0.51  fof(f9,plain,(
% 0.23/0.51    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.23/0.51    inference(rectify,[],[f8])).
% 0.23/0.51  fof(f8,plain,(
% 0.23/0.51    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.23/0.51    inference(nnf_transformation,[],[f3])).
% 0.23/0.51  fof(f3,axiom,(
% 0.23/0.51    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.23/0.51  fof(f47,plain,(
% 0.23/0.51    ~spl6_1 | ~spl6_2),
% 0.23/0.51    inference(avatar_split_clause,[],[f22,f45,f42])).
% 0.23/0.51  fof(f22,plain,(
% 0.23/0.51    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.23/0.51    inference(cnf_transformation,[],[f7])).
% 0.23/0.51  fof(f7,plain,(
% 0.23/0.51    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.23/0.51    inference(ennf_transformation,[],[f6])).
% 0.23/0.51  fof(f6,negated_conjecture,(
% 0.23/0.51    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 0.23/0.51    inference(negated_conjecture,[],[f5])).
% 0.23/0.51  fof(f5,conjecture,(
% 0.23/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.23/0.51  % SZS output end Proof for theBenchmark
% 0.23/0.51  % (14088)------------------------------
% 0.23/0.51  % (14088)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.51  % (14088)Termination reason: Refutation
% 0.23/0.51  
% 0.23/0.51  % (14088)Memory used [KB]: 10874
% 0.23/0.51  % (14088)Time elapsed: 0.066 s
% 0.23/0.51  % (14088)------------------------------
% 0.23/0.51  % (14088)------------------------------
% 0.23/0.51  % (14081)Success in time 0.146 s
%------------------------------------------------------------------------------
