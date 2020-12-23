%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 158 expanded)
%              Number of leaves         :    9 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :  163 ( 490 expanded)
%              Number of equality atoms :   28 ( 139 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f137,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f62,f87,f112,f121,f136])).

fof(f136,plain,
    ( ~ spl4_1
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f133,f22])).

fof(f22,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( sK0 != sK1
    & k2_zfmisc_1(sK0,sK0) = k2_zfmisc_1(sK1,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f9])).

fof(f9,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1) )
   => ( sK0 != sK1
      & k2_zfmisc_1(sK0,sK0) = k2_zfmisc_1(sK1,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_zfmisc_1)).

fof(f133,plain,
    ( sK0 = sK1
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(resolution,[],[f113,f122])).

fof(f122,plain,
    ( ! [X5] : ~ r2_hidden(X5,sK1)
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f57,f43])).

fof(f43,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl4_1
  <=> ! [X1] : ~ r2_hidden(X1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f57,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,sK1)
        | r2_hidden(X5,sK0) )
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f56])).

% (20745)Refutation not found, incomplete strategy% (20745)------------------------------
% (20745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (20745)Termination reason: Refutation not found, incomplete strategy

% (20745)Memory used [KB]: 1663
% (20745)Time elapsed: 0.096 s
% (20745)------------------------------
% (20745)------------------------------
fof(f56,plain,
    ( spl4_3
  <=> ! [X5] :
        ( ~ r2_hidden(X5,sK1)
        | r2_hidden(X5,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f113,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(X0,sK0),X0)
        | sK0 = X0 )
    | ~ spl4_1 ),
    inference(resolution,[],[f43,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r2_hidden(sK2(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f12])).

fof(f12,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f121,plain,
    ( ~ spl4_1
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f115,f22])).

fof(f115,plain,
    ( sK0 = sK1
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(resolution,[],[f43,f89])).

fof(f89,plain,
    ( ! [X1] :
        ( r2_hidden(sK2(X1,sK1),X1)
        | sK1 = X1 )
    | ~ spl4_4 ),
    inference(resolution,[],[f60,f23])).

fof(f60,plain,
    ( ! [X4] : ~ r2_hidden(X4,sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl4_4
  <=> ! [X4] : ~ r2_hidden(X4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f112,plain,
    ( spl4_1
    | spl4_1
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f111,f59,f42,f42])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f50,f60])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f38,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f38,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK0))
      | r2_hidden(X3,sK1) ) ),
    inference(superposition,[],[f32,f21])).

fof(f21,plain,(
    k2_zfmisc_1(sK0,sK0) = k2_zfmisc_1(sK1,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f87,plain,
    ( ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f86])).

fof(f86,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f85,f83])).

fof(f83,plain,
    ( r2_hidden(sK2(sK0,sK1),sK0)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f78,f22])).

fof(f78,plain,
    ( r2_hidden(sK2(sK0,sK1),sK0)
    | sK0 = sK1
    | ~ spl4_3 ),
    inference(factoring,[],[f64])).

fof(f64,plain,
    ( ! [X1] :
        ( r2_hidden(sK2(X1,sK1),sK0)
        | r2_hidden(sK2(X1,sK1),X1)
        | sK1 = X1 )
    | ~ spl4_3 ),
    inference(resolution,[],[f57,f23])).

fof(f85,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),sK0)
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f84,f22])).

fof(f84,plain,
    ( sK0 = sK1
    | ~ r2_hidden(sK2(sK0,sK1),sK0)
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(resolution,[],[f83,f48])).

fof(f48,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(X0,sK1),sK0)
        | sK1 = X0
        | ~ r2_hidden(sK2(X0,sK1),X0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f46,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | X0 = X1
      | ~ r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f46,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl4_2
  <=> ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f62,plain,
    ( spl4_4
    | spl4_3 ),
    inference(avatar_split_clause,[],[f54,f56,f59])).

% (20749)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f54,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,sK1)
      | ~ r2_hidden(X7,sK1)
      | r2_hidden(X6,sK0) ) ),
    inference(resolution,[],[f39,f32])).

fof(f39,plain,(
    ! [X4,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK0))
      | ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(superposition,[],[f33,f21])).

fof(f47,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f40,f45,f42])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f37,f33])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK0))
      | r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f31,f21])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:03:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (20753)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.50  % (20767)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.50  % (20768)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.50  % (20755)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.50  % (20753)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % (20751)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (20745)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f137,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f47,f62,f87,f112,f121,f136])).
% 0.20/0.51  fof(f136,plain,(
% 0.20/0.51    ~spl4_1 | ~spl4_3),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f135])).
% 0.20/0.51  fof(f135,plain,(
% 0.20/0.51    $false | (~spl4_1 | ~spl4_3)),
% 0.20/0.51    inference(subsumption_resolution,[],[f133,f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    sK0 != sK1),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    sK0 != sK1 & k2_zfmisc_1(sK0,sK0) = k2_zfmisc_1(sK1,sK1)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f9])).
% 0.20/0.51  fof(f9,plain,(
% 0.20/0.51    ? [X0,X1] : (X0 != X1 & k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1)) => (sK0 != sK1 & k2_zfmisc_1(sK0,sK0) = k2_zfmisc_1(sK1,sK1))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f7,plain,(
% 0.20/0.51    ? [X0,X1] : (X0 != X1 & k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1] : (k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1) => X0 = X1)),
% 0.20/0.51    inference(negated_conjecture,[],[f5])).
% 0.20/0.51  fof(f5,conjecture,(
% 0.20/0.51    ! [X0,X1] : (k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1) => X0 = X1)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_zfmisc_1)).
% 0.20/0.51  fof(f133,plain,(
% 0.20/0.51    sK0 = sK1 | (~spl4_1 | ~spl4_3)),
% 0.20/0.51    inference(resolution,[],[f113,f122])).
% 0.20/0.51  fof(f122,plain,(
% 0.20/0.51    ( ! [X5] : (~r2_hidden(X5,sK1)) ) | (~spl4_1 | ~spl4_3)),
% 0.20/0.51    inference(subsumption_resolution,[],[f57,f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ( ! [X1] : (~r2_hidden(X1,sK0)) ) | ~spl4_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    spl4_1 <=> ! [X1] : ~r2_hidden(X1,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    ( ! [X5] : (~r2_hidden(X5,sK1) | r2_hidden(X5,sK0)) ) | ~spl4_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f56])).
% 0.20/0.51  % (20745)Refutation not found, incomplete strategy% (20745)------------------------------
% 0.20/0.51  % (20745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (20745)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (20745)Memory used [KB]: 1663
% 0.20/0.51  % (20745)Time elapsed: 0.096 s
% 0.20/0.51  % (20745)------------------------------
% 0.20/0.51  % (20745)------------------------------
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    spl4_3 <=> ! [X5] : (~r2_hidden(X5,sK1) | r2_hidden(X5,sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.51  fof(f113,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(sK2(X0,sK0),X0) | sK0 = X0) ) | ~spl4_1),
% 0.20/0.51    inference(resolution,[],[f43,f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0) | X0 = X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(sK2(X0,X1),X0)) & (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0))))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(sK2(X0,X1),X0)) & (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 0.20/0.51    inference(nnf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,plain,(
% 0.20/0.51    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 0.20/0.51  fof(f121,plain,(
% 0.20/0.51    ~spl4_1 | ~spl4_4),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f120])).
% 0.20/0.51  fof(f120,plain,(
% 0.20/0.51    $false | (~spl4_1 | ~spl4_4)),
% 0.20/0.51    inference(subsumption_resolution,[],[f115,f22])).
% 0.20/0.51  fof(f115,plain,(
% 0.20/0.51    sK0 = sK1 | (~spl4_1 | ~spl4_4)),
% 0.20/0.51    inference(resolution,[],[f43,f89])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    ( ! [X1] : (r2_hidden(sK2(X1,sK1),X1) | sK1 = X1) ) | ~spl4_4),
% 0.20/0.51    inference(resolution,[],[f60,f23])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    ( ! [X4] : (~r2_hidden(X4,sK1)) ) | ~spl4_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f59])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    spl4_4 <=> ! [X4] : ~r2_hidden(X4,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.51  fof(f112,plain,(
% 0.20/0.51    spl4_1 | spl4_1 | ~spl4_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f111,f59,f42,f42])).
% 0.20/0.51  fof(f111,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~r2_hidden(X1,sK0)) ) | ~spl4_4),
% 0.20/0.51    inference(subsumption_resolution,[],[f50,f60])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0) | ~r2_hidden(X1,sK0)) )),
% 0.20/0.51    inference(resolution,[],[f38,f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.20/0.51    inference(flattening,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.20/0.51    inference(nnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK0)) | r2_hidden(X3,sK1)) )),
% 0.20/0.51    inference(superposition,[],[f32,f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    k2_zfmisc_1(sK0,sK0) = k2_zfmisc_1(sK1,sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    ~spl4_2 | ~spl4_3),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f86])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    $false | (~spl4_2 | ~spl4_3)),
% 0.20/0.51    inference(subsumption_resolution,[],[f85,f83])).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    r2_hidden(sK2(sK0,sK1),sK0) | ~spl4_3),
% 0.20/0.51    inference(subsumption_resolution,[],[f78,f22])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    r2_hidden(sK2(sK0,sK1),sK0) | sK0 = sK1 | ~spl4_3),
% 0.20/0.51    inference(factoring,[],[f64])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    ( ! [X1] : (r2_hidden(sK2(X1,sK1),sK0) | r2_hidden(sK2(X1,sK1),X1) | sK1 = X1) ) | ~spl4_3),
% 0.20/0.51    inference(resolution,[],[f57,f23])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    ~r2_hidden(sK2(sK0,sK1),sK0) | (~spl4_2 | ~spl4_3)),
% 0.20/0.51    inference(subsumption_resolution,[],[f84,f22])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    sK0 = sK1 | ~r2_hidden(sK2(sK0,sK1),sK0) | (~spl4_2 | ~spl4_3)),
% 0.20/0.51    inference(resolution,[],[f83,f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(sK2(X0,sK1),sK0) | sK1 = X0 | ~r2_hidden(sK2(X0,sK1),X0)) ) | ~spl4_2),
% 0.20/0.51    inference(resolution,[],[f46,f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | X0 = X1 | ~r2_hidden(sK2(X0,X1),X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl4_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    spl4_2 <=> ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    spl4_4 | spl4_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f54,f56,f59])).
% 0.20/0.51  % (20749)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    ( ! [X6,X7] : (~r2_hidden(X6,sK1) | ~r2_hidden(X7,sK1) | r2_hidden(X6,sK0)) )),
% 0.20/0.51    inference(resolution,[],[f39,f32])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK0)) | ~r2_hidden(X5,sK1) | ~r2_hidden(X4,sK1)) )),
% 0.20/0.51    inference(superposition,[],[f33,f21])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    spl4_1 | spl4_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f40,f45,f42])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(X0,sK1) | ~r2_hidden(X1,sK0) | ~r2_hidden(X0,sK0)) )),
% 0.20/0.51    inference(resolution,[],[f37,f33])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK0)) | r2_hidden(X0,sK1)) )),
% 0.20/0.51    inference(superposition,[],[f31,f21])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (20753)------------------------------
% 0.20/0.51  % (20753)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (20753)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (20753)Memory used [KB]: 10746
% 0.20/0.51  % (20753)Time elapsed: 0.090 s
% 0.20/0.51  % (20753)------------------------------
% 0.20/0.51  % (20753)------------------------------
% 0.20/0.51  % (20744)Success in time 0.155 s
%------------------------------------------------------------------------------
