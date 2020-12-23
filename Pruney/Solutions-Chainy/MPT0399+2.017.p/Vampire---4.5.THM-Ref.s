%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:09 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   52 (  84 expanded)
%              Number of leaves         :   17 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :  170 ( 295 expanded)
%              Number of equality atoms :   42 (  75 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f79,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f48,f58,f71,f75,f76,f78])).

fof(f78,plain,(
    ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f77])).

fof(f77,plain,
    ( $false
    | ~ spl5_3 ),
    inference(resolution,[],[f54,f49])).

fof(f49,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f25,f39])).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f25,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f54,plain,
    ( r2_hidden(sK1(k1_xboole_0),k1_xboole_0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl5_3
  <=> r2_hidden(sK1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f76,plain,
    ( k1_xboole_0 != k3_tarski(sK0)
    | sK0 != k3_tarski(sK0)
    | k1_xboole_0 = sK0 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f75,plain,
    ( spl5_6
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f67,f56,f73])).

fof(f73,plain,
    ( spl5_6
  <=> sK0 = k3_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f56,plain,
    ( spl5_4
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f67,plain,
    ( sK0 = k3_tarski(sK0)
    | ~ spl5_4 ),
    inference(resolution,[],[f64,f57])).

fof(f57,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f64,plain,
    ( ! [X3] :
        ( r2_hidden(sK2(sK0,X3),X3)
        | k3_tarski(sK0) = X3 )
    | ~ spl5_4 ),
    inference(resolution,[],[f31,f57])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | k3_tarski(X0) = X1
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK2(X0,X1),X3) )
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( ( r2_hidden(sK3(X0,X1),X0)
              & r2_hidden(sK2(X0,X1),sK3(X0,X1)) )
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK4(X0,X5),X0)
                & r2_hidden(X5,sK4(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f16,f19,f18,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK2(X0,X1),X3) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK2(X0,X1),X4) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(sK2(X0,X1),X4) )
     => ( r2_hidden(sK3(X0,X1),X0)
        & r2_hidden(sK2(X0,X1),sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK4(X0,X5),X0)
        & r2_hidden(X5,sK4(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(f71,plain,
    ( spl5_5
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f66,f56,f69])).

fof(f69,plain,
    ( spl5_5
  <=> k1_xboole_0 = k3_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f66,plain,
    ( k1_xboole_0 = k3_tarski(sK0)
    | ~ spl5_4 ),
    inference(resolution,[],[f64,f49])).

fof(f58,plain,
    ( spl5_3
    | spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f51,f46,f56,f53])).

fof(f46,plain,
    ( spl5_2
  <=> r1_setfam_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f51,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(sK1(k1_xboole_0),k1_xboole_0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f26,f47])).

fof(f47,plain,
    ( r1_setfam_1(sK0,k1_xboole_0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_setfam_1(X0,X1)
      | ~ r2_hidden(X2,X0)
      | r2_hidden(sK1(X1),X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(sK1(X1),X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f13])).

fof(f13,plain,(
    ! [X1] :
      ( ? [X3] : r2_hidden(X3,X1)
     => r2_hidden(sK1(X1),X1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] : r2_hidden(X3,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] : ~ r2_hidden(X3,X1)
            & r2_hidden(X2,X0) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f48,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f23,f46])).

fof(f23,plain,(
    r1_setfam_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( k1_xboole_0 != sK0
    & r1_setfam_1(sK0,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f11])).

fof(f11,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & r1_setfam_1(X0,k1_xboole_0) )
   => ( k1_xboole_0 != sK0
      & r1_setfam_1(sK0,k1_xboole_0) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & r1_setfam_1(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( r1_setfam_1(X0,k1_xboole_0)
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( r1_setfam_1(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).

fof(f44,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f24,f42])).

fof(f42,plain,
    ( spl5_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f24,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:27:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (30303)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.48  % (30305)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.48  % (30290)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (30290)Refutation not found, incomplete strategy% (30290)------------------------------
% 0.20/0.48  % (30290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (30290)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (30290)Memory used [KB]: 6012
% 0.20/0.48  % (30290)Time elapsed: 0.065 s
% 0.20/0.48  % (30290)------------------------------
% 0.20/0.48  % (30290)------------------------------
% 0.20/0.49  % (30295)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (30298)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.49  % (30299)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  % (30296)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.49  % (30296)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f44,f48,f58,f71,f75,f76,f78])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    ~spl5_3),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f77])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    $false | ~spl5_3),
% 0.20/0.49    inference(resolution,[],[f54,f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.49    inference(superposition,[],[f25,f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.20/0.49    inference(flattening,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.20/0.49    inference(nnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    r2_hidden(sK1(k1_xboole_0),k1_xboole_0) | ~spl5_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f53])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    spl5_3 <=> r2_hidden(sK1(k1_xboole_0),k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    k1_xboole_0 != k3_tarski(sK0) | sK0 != k3_tarski(sK0) | k1_xboole_0 = sK0),
% 0.20/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    spl5_6 | ~spl5_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f67,f56,f73])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    spl5_6 <=> sK0 = k3_tarski(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    spl5_4 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    sK0 = k3_tarski(sK0) | ~spl5_4),
% 0.20/0.49    inference(resolution,[],[f64,f57])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl5_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f56])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    ( ! [X3] : (r2_hidden(sK2(sK0,X3),X3) | k3_tarski(sK0) = X3) ) | ~spl5_4),
% 0.20/0.49    inference(resolution,[],[f31,f57])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | k3_tarski(X0) = X1 | r2_hidden(sK2(X0,X1),X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK2(X0,X1),X3)) | ~r2_hidden(sK2(X0,X1),X1)) & ((r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),sK3(X0,X1))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK4(X0,X5),X0) & r2_hidden(X5,sK4(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f16,f19,f18,f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK2(X0,X1),X3)) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK2(X0,X1),X4)) | r2_hidden(sK2(X0,X1),X1))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK2(X0,X1),X4)) => (r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),sK3(X0,X1))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK4(X0,X5),X0) & r2_hidden(X5,sK4(X0,X5))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 0.20/0.49    inference(rectify,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 0.20/0.49    inference(nnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    spl5_5 | ~spl5_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f66,f56,f69])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    spl5_5 <=> k1_xboole_0 = k3_tarski(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    k1_xboole_0 = k3_tarski(sK0) | ~spl5_4),
% 0.20/0.49    inference(resolution,[],[f64,f49])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    spl5_3 | spl5_4 | ~spl5_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f51,f46,f56,f53])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    spl5_2 <=> r1_setfam_1(sK0,k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(sK1(k1_xboole_0),k1_xboole_0)) ) | ~spl5_2),
% 0.20/0.49    inference(resolution,[],[f26,f47])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    r1_setfam_1(sK0,k1_xboole_0) | ~spl5_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f46])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_setfam_1(X0,X1) | ~r2_hidden(X2,X0) | r2_hidden(sK1(X1),X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0,X1] : (! [X2] : (r2_hidden(sK1(X1),X1) | ~r2_hidden(X2,X0)) | ~r1_setfam_1(X0,X1))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X1] : (? [X3] : r2_hidden(X3,X1) => r2_hidden(sK1(X1),X1))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ! [X0,X1] : (! [X2] : (? [X3] : r2_hidden(X3,X1) | ~r2_hidden(X2,X0)) | ~r1_setfam_1(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,plain,(
% 0.20/0.49    ! [X0,X1] : (r1_setfam_1(X0,X1) => ! [X2] : ~(! [X3] : ~r2_hidden(X3,X1) & r2_hidden(X2,X0)))),
% 0.20/0.49    inference(pure_predicate_removal,[],[f7])).
% 0.20/0.49  fof(f7,plain,(
% 0.20/0.49    ! [X0,X1] : (r1_setfam_1(X0,X1) => ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.20/0.49    inference(unused_predicate_definition_removal,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    spl5_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f23,f46])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    r1_setfam_1(sK0,k1_xboole_0)),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    k1_xboole_0 != sK0 & r1_setfam_1(sK0,k1_xboole_0)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ? [X0] : (k1_xboole_0 != X0 & r1_setfam_1(X0,k1_xboole_0)) => (k1_xboole_0 != sK0 & r1_setfam_1(sK0,k1_xboole_0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f9,plain,(
% 0.20/0.49    ? [X0] : (k1_xboole_0 != X0 & r1_setfam_1(X0,k1_xboole_0))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,negated_conjecture,(
% 0.20/0.49    ~! [X0] : (r1_setfam_1(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.49    inference(negated_conjecture,[],[f5])).
% 0.20/0.49  fof(f5,conjecture,(
% 0.20/0.49    ! [X0] : (r1_setfam_1(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ~spl5_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f24,f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    spl5_1 <=> k1_xboole_0 = sK0),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    k1_xboole_0 != sK0),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (30296)------------------------------
% 0.20/0.49  % (30296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (30296)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (30296)Memory used [KB]: 10618
% 0.20/0.49  % (30296)Time elapsed: 0.049 s
% 0.20/0.49  % (30296)------------------------------
% 0.20/0.49  % (30296)------------------------------
% 0.20/0.50  % (30293)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (30294)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.50  % (30304)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.50  % (30293)Refutation not found, incomplete strategy% (30293)------------------------------
% 0.20/0.50  % (30293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (30293)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (30293)Memory used [KB]: 10490
% 0.20/0.50  % (30293)Time elapsed: 0.095 s
% 0.20/0.50  % (30293)------------------------------
% 0.20/0.50  % (30293)------------------------------
% 0.20/0.50  % (30308)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.50  % (30309)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.50  % (30291)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (30310)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (30292)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.50  % (30291)Refutation not found, incomplete strategy% (30291)------------------------------
% 0.20/0.50  % (30291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (30291)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (30291)Memory used [KB]: 10618
% 0.20/0.50  % (30291)Time elapsed: 0.094 s
% 0.20/0.50  % (30291)------------------------------
% 0.20/0.50  % (30291)------------------------------
% 0.20/0.50  % (30310)Refutation not found, incomplete strategy% (30310)------------------------------
% 0.20/0.50  % (30310)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (30310)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (30310)Memory used [KB]: 10490
% 0.20/0.50  % (30310)Time elapsed: 0.096 s
% 0.20/0.50  % (30310)------------------------------
% 0.20/0.50  % (30310)------------------------------
% 0.20/0.51  % (30289)Success in time 0.151 s
%------------------------------------------------------------------------------
