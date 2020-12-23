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
% DateTime   : Thu Dec  3 12:45:39 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   63 (  89 expanded)
%              Number of leaves         :   20 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :  142 ( 185 expanded)
%              Number of equality atoms :   19 (  30 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f187,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f56,f62,f84,f109,f185,f186])).

% (22741)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
fof(f186,plain,
    ( k1_xboole_0 != sK1
    | ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f185,plain,
    ( spl3_1
    | spl3_19
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f178,f81,f181,f48])).

fof(f48,plain,
    ( spl3_1
  <=> m1_subset_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f181,plain,
    ( spl3_19
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f81,plain,
    ( spl3_6
  <=> m1_subset_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

% (22737)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
fof(f178,plain,
    ( k1_xboole_0 = sK1
    | m1_subset_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_zfmisc_1(sK1))
    | ~ spl3_6 ),
    inference(resolution,[],[f83,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k1_xboole_0 = X0
      | m1_subset_1(k3_enumset1(X1,X1,X1,X1,X1),k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f39,f44])).

fof(f44,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f30,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f33,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f30,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

% (22743)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ( k1_xboole_0 != X0
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

fof(f83,plain,
    ( m1_subset_1(sK0,sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f81])).

fof(f109,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f103,f106])).

fof(f106,plain,
    ( spl3_10
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f103,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f29,f28,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f28,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f29,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f84,plain,
    ( spl3_6
    | ~ spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f70,f59,f53,f81])).

fof(f53,plain,
    ( spl3_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f59,plain,
    ( spl3_3
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f70,plain,
    ( m1_subset_1(sK0,sK1)
    | ~ spl3_2
    | spl3_3 ),
    inference(unit_resulting_resolution,[],[f61,f55,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f55,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f61,plain,
    ( ~ v1_xboole_0(sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f62,plain,
    ( ~ spl3_3
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f57,f53,f59])).

fof(f57,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f55,f31])).

fof(f31,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f56,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f26,f53])).

fof(f26,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
        & r2_hidden(X0,X1) )
   => ( ~ m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(f51,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f45,f48])).

fof(f45,plain,(
    ~ m1_subset_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_zfmisc_1(sK1)) ),
    inference(definition_unfolding,[],[f27,f44])).

fof(f27,plain,(
    ~ m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:25:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (22728)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  % (22734)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (22734)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f187,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f51,f56,f62,f84,f109,f185,f186])).
% 0.22/0.47  % (22741)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.47  fof(f186,plain,(
% 0.22/0.47    k1_xboole_0 != sK1 | ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(sK1)),
% 0.22/0.47    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.47  fof(f185,plain,(
% 0.22/0.47    spl3_1 | spl3_19 | ~spl3_6),
% 0.22/0.47    inference(avatar_split_clause,[],[f178,f81,f181,f48])).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    spl3_1 <=> m1_subset_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_zfmisc_1(sK1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.47  fof(f181,plain,(
% 0.22/0.47    spl3_19 <=> k1_xboole_0 = sK1),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.47  fof(f81,plain,(
% 0.22/0.47    spl3_6 <=> m1_subset_1(sK0,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.47  % (22737)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.47  fof(f178,plain,(
% 0.22/0.47    k1_xboole_0 = sK1 | m1_subset_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_zfmisc_1(sK1)) | ~spl3_6),
% 0.22/0.47    inference(resolution,[],[f83,f46])).
% 0.22/0.47  fof(f46,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k1_xboole_0 = X0 | m1_subset_1(k3_enumset1(X1,X1,X1,X1,X1),k1_zfmisc_1(X0))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f39,f44])).
% 0.22/0.47  fof(f44,plain,(
% 0.22/0.47    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.22/0.47    inference(definition_unfolding,[],[f30,f43])).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.22/0.47    inference(definition_unfolding,[],[f33,f42])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.22/0.47    inference(definition_unfolding,[],[f40,f41])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,axiom,(
% 0.22/0.47    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.47  % (22743)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0))),
% 0.22/0.47    inference(flattening,[],[f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ! [X0,X1] : ((m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X1,X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,axiom,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(X1,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).
% 0.22/0.47  fof(f83,plain,(
% 0.22/0.47    m1_subset_1(sK0,sK1) | ~spl3_6),
% 0.22/0.47    inference(avatar_component_clause,[],[f81])).
% 0.22/0.47  fof(f109,plain,(
% 0.22/0.47    spl3_10),
% 0.22/0.47    inference(avatar_split_clause,[],[f103,f106])).
% 0.22/0.47  fof(f106,plain,(
% 0.22/0.47    spl3_10 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.47  fof(f103,plain,(
% 0.22/0.47    v1_xboole_0(k1_xboole_0)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f29,f28,f38])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.22/0.47    inference(flattening,[],[f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.47  fof(f84,plain,(
% 0.22/0.47    spl3_6 | ~spl3_2 | spl3_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f70,f59,f53,f81])).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    spl3_2 <=> r2_hidden(sK0,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.47  fof(f59,plain,(
% 0.22/0.47    spl3_3 <=> v1_xboole_0(sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.47  fof(f70,plain,(
% 0.22/0.47    m1_subset_1(sK0,sK1) | (~spl3_2 | spl3_3)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f61,f55,f35])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f25])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.22/0.47    inference(nnf_transformation,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,axiom,(
% 0.22/0.47    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.22/0.47  fof(f55,plain,(
% 0.22/0.47    r2_hidden(sK0,sK1) | ~spl3_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f53])).
% 0.22/0.47  fof(f61,plain,(
% 0.22/0.47    ~v1_xboole_0(sK1) | spl3_3),
% 0.22/0.47    inference(avatar_component_clause,[],[f59])).
% 0.22/0.47  fof(f62,plain,(
% 0.22/0.47    ~spl3_3 | ~spl3_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f57,f53,f59])).
% 0.22/0.47  fof(f57,plain,(
% 0.22/0.47    ~v1_xboole_0(sK1) | ~spl3_2),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f55,f31])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f24])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.47    inference(rectify,[],[f21])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.47    inference(nnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.47  fof(f56,plain,(
% 0.22/0.47    spl3_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f26,f53])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    r2_hidden(sK0,sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ~m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) & r2_hidden(sK0,sK1)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ? [X0,X1] : (~m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) & r2_hidden(X0,X1)) => (~m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) & r2_hidden(sK0,sK1))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ? [X0,X1] : (~m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) & r2_hidden(X0,X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.22/0.47    inference(negated_conjecture,[],[f11])).
% 0.22/0.47  fof(f11,conjecture,(
% 0.22/0.47    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).
% 0.22/0.47  fof(f51,plain,(
% 0.22/0.47    ~spl3_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f45,f48])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    ~m1_subset_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_zfmisc_1(sK1))),
% 0.22/0.47    inference(definition_unfolding,[],[f27,f44])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ~m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))),
% 0.22/0.47    inference(cnf_transformation,[],[f20])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (22734)------------------------------
% 0.22/0.47  % (22734)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (22734)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (22734)Memory used [KB]: 6140
% 0.22/0.47  % (22734)Time elapsed: 0.062 s
% 0.22/0.47  % (22734)------------------------------
% 0.22/0.47  % (22734)------------------------------
% 0.22/0.48  % (22727)Success in time 0.115 s
%------------------------------------------------------------------------------
