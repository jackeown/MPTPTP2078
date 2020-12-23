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
% DateTime   : Thu Dec  3 12:43:45 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 131 expanded)
%              Number of leaves         :   12 (  35 expanded)
%              Depth                    :   13
%              Number of atoms          :  183 ( 439 expanded)
%              Number of equality atoms :   39 (  97 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f234,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f177,f233])).

fof(f233,plain,(
    ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f232])).

fof(f232,plain,
    ( $false
    | ~ spl4_5 ),
    inference(trivial_inequality_removal,[],[f231])).

fof(f231,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl4_5 ),
    inference(superposition,[],[f27,f210])).

fof(f210,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_5 ),
    inference(resolution,[],[f188,f44])).

fof(f44,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f31,f42])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f31,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f188,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(X0,sK1),X0)
        | sK1 = X0 )
    | ~ spl4_5 ),
    inference(resolution,[],[f186,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK3(X0,X1),X1)
          | ~ r2_hidden(sK3(X0,X1),X0) )
        & ( r2_hidden(sK3(X0,X1),X1)
          | r2_hidden(sK3(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1),X1)
          | ~ r2_hidden(sK3(X0,X1),X0) )
        & ( r2_hidden(sK3(X0,X1),X1)
          | r2_hidden(sK3(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f186,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl4_5 ),
    inference(duplicate_literal_removal,[],[f184])).

fof(f184,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl4_5 ),
    inference(resolution,[],[f84,f28])).

fof(f28,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,sK0)
      | ~ r2_hidden(X2,sK1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK1)
        | ~ m1_subset_1(X2,sK0) )
    & k1_xboole_0 != sK1
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,X0) )
        & k1_xboole_0 != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ! [X2] :
          ( ~ r2_hidden(X2,sK1)
          | ~ m1_subset_1(X2,sK0) )
      & k1_xboole_0 != sK1
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ~ ( ! [X2] :
                ( m1_subset_1(X2,X0)
               => ~ r2_hidden(X2,X1) )
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

fof(f84,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,sK0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl4_5
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | m1_subset_1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f27,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f177,plain,(
    ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f176])).

fof(f176,plain,
    ( $false
    | ~ spl4_4 ),
    inference(trivial_inequality_removal,[],[f175])).

fof(f175,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl4_4 ),
    inference(superposition,[],[f27,f163])).

fof(f163,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f142,f140])).

fof(f140,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_4 ),
    inference(resolution,[],[f109,f44])).

fof(f109,plain,
    ( ! [X3] :
        ( r2_hidden(sK3(X3,sK0),X3)
        | sK0 = X3 )
    | ~ spl4_4 ),
    inference(resolution,[],[f37,f89])).

fof(f89,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f77,f29])).

fof(f29,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
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

fof(f77,plain,
    ( v1_xboole_0(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl4_4
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f142,plain,
    ( sK0 = sK1
    | ~ spl4_4 ),
    inference(resolution,[],[f109,f93])).

fof(f93,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f89,f79])).

fof(f79,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f36,f26])).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f85,plain,
    ( spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f81,f83,f75])).

fof(f81,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | m1_subset_1(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f79,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

% (9515)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% (9507)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% (9520)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% (9499)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% (9518)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (9510)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (9511)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (9513)Termination reason: Refutation not found, incomplete strategy

% (9513)Memory used [KB]: 1663
% (9513)Time elapsed: 0.141 s
% (9513)------------------------------
% (9513)------------------------------
% (9512)Refutation not found, incomplete strategy% (9512)------------------------------
% (9512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (9512)Termination reason: Refutation not found, incomplete strategy

% (9512)Memory used [KB]: 10746
% (9512)Time elapsed: 0.118 s
% (9512)------------------------------
% (9512)------------------------------
fof(f20,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:24:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.49  % (9500)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.50  % (9509)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.50  % (9509)Refutation not found, incomplete strategy% (9509)------------------------------
% 0.22/0.50  % (9509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (9509)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (9509)Memory used [KB]: 10618
% 0.22/0.50  % (9509)Time elapsed: 0.085 s
% 0.22/0.50  % (9509)------------------------------
% 0.22/0.50  % (9509)------------------------------
% 0.22/0.52  % (9503)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (9501)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (9502)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (9506)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (9498)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (9493)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (9492)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (9494)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (9508)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (9517)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (9494)Refutation not found, incomplete strategy% (9494)------------------------------
% 0.22/0.54  % (9494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (9495)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (9494)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (9494)Memory used [KB]: 10746
% 0.22/0.54  % (9494)Time elapsed: 0.128 s
% 0.22/0.54  % (9494)------------------------------
% 0.22/0.54  % (9494)------------------------------
% 0.22/0.54  % (9512)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (9504)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.32/0.54  % (9497)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.32/0.54  % (9496)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.32/0.54  % (9514)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.32/0.54  % (9504)Refutation found. Thanks to Tanya!
% 1.32/0.54  % SZS status Theorem for theBenchmark
% 1.32/0.54  % (9521)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.32/0.54  % (9514)Refutation not found, incomplete strategy% (9514)------------------------------
% 1.32/0.54  % (9514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (9514)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (9514)Memory used [KB]: 10746
% 1.32/0.54  % (9514)Time elapsed: 0.099 s
% 1.32/0.54  % (9514)------------------------------
% 1.32/0.54  % (9514)------------------------------
% 1.32/0.55  % (9519)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.32/0.55  % (9505)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.32/0.55  % (9513)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.32/0.55  % (9516)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.32/0.55  % (9513)Refutation not found, incomplete strategy% (9513)------------------------------
% 1.32/0.55  % (9513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % SZS output start Proof for theBenchmark
% 1.32/0.55  fof(f234,plain,(
% 1.32/0.55    $false),
% 1.32/0.55    inference(avatar_sat_refutation,[],[f85,f177,f233])).
% 1.32/0.55  fof(f233,plain,(
% 1.32/0.55    ~spl4_5),
% 1.32/0.55    inference(avatar_contradiction_clause,[],[f232])).
% 1.32/0.55  fof(f232,plain,(
% 1.32/0.55    $false | ~spl4_5),
% 1.32/0.55    inference(trivial_inequality_removal,[],[f231])).
% 1.32/0.55  fof(f231,plain,(
% 1.32/0.55    k1_xboole_0 != k1_xboole_0 | ~spl4_5),
% 1.32/0.55    inference(superposition,[],[f27,f210])).
% 1.32/0.55  fof(f210,plain,(
% 1.32/0.55    k1_xboole_0 = sK1 | ~spl4_5),
% 1.32/0.55    inference(resolution,[],[f188,f44])).
% 1.32/0.55  fof(f44,plain,(
% 1.32/0.55    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.32/0.55    inference(superposition,[],[f31,f42])).
% 1.32/0.55  fof(f42,plain,(
% 1.32/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.32/0.55    inference(equality_resolution,[],[f41])).
% 1.32/0.55  fof(f41,plain,(
% 1.32/0.55    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 1.32/0.55    inference(cnf_transformation,[],[f25])).
% 1.32/0.55  fof(f25,plain,(
% 1.32/0.55    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.32/0.55    inference(flattening,[],[f24])).
% 1.32/0.55  fof(f24,plain,(
% 1.32/0.55    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.32/0.55    inference(nnf_transformation,[],[f3])).
% 1.32/0.55  fof(f3,axiom,(
% 1.32/0.55    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.32/0.55  fof(f31,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 1.32/0.55    inference(cnf_transformation,[],[f4])).
% 1.32/0.55  fof(f4,axiom,(
% 1.32/0.55    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 1.32/0.55  fof(f188,plain,(
% 1.32/0.55    ( ! [X0] : (r2_hidden(sK3(X0,sK1),X0) | sK1 = X0) ) | ~spl4_5),
% 1.32/0.55    inference(resolution,[],[f186,f37])).
% 1.32/0.55  fof(f37,plain,(
% 1.32/0.55    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | X0 = X1 | r2_hidden(sK3(X0,X1),X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f23])).
% 1.32/0.55  fof(f23,plain,(
% 1.32/0.55    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK3(X0,X1),X1) | ~r2_hidden(sK3(X0,X1),X0)) & (r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0))))),
% 1.32/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).
% 1.32/0.55  fof(f22,plain,(
% 1.32/0.55    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK3(X0,X1),X1) | ~r2_hidden(sK3(X0,X1),X0)) & (r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0))))),
% 1.32/0.55    introduced(choice_axiom,[])).
% 1.32/0.55  fof(f21,plain,(
% 1.32/0.55    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 1.32/0.55    inference(nnf_transformation,[],[f13])).
% 1.32/0.55  fof(f13,plain,(
% 1.32/0.55    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.32/0.55    inference(ennf_transformation,[],[f2])).
% 1.32/0.55  fof(f2,axiom,(
% 1.32/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 1.32/0.55  fof(f186,plain,(
% 1.32/0.55    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | ~spl4_5),
% 1.32/0.55    inference(duplicate_literal_removal,[],[f184])).
% 1.32/0.55  fof(f184,plain,(
% 1.32/0.55    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,sK1)) ) | ~spl4_5),
% 1.32/0.55    inference(resolution,[],[f84,f28])).
% 1.32/0.55  fof(f28,plain,(
% 1.32/0.55    ( ! [X2] : (~m1_subset_1(X2,sK0) | ~r2_hidden(X2,sK1)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f15])).
% 1.32/0.55  fof(f15,plain,(
% 1.32/0.55    ! [X2] : (~r2_hidden(X2,sK1) | ~m1_subset_1(X2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.32/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f14])).
% 1.32/0.55  fof(f14,plain,(
% 1.32/0.55    ? [X0,X1] : (! [X2] : (~r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (! [X2] : (~r2_hidden(X2,sK1) | ~m1_subset_1(X2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.32/0.55    introduced(choice_axiom,[])).
% 1.32/0.55  fof(f10,plain,(
% 1.32/0.55    ? [X0,X1] : (! [X2] : (~r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.32/0.55    inference(flattening,[],[f9])).
% 1.32/0.55  fof(f9,plain,(
% 1.32/0.55    ? [X0,X1] : ((! [X2] : (~r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.32/0.55    inference(ennf_transformation,[],[f8])).
% 1.32/0.55  fof(f8,negated_conjecture,(
% 1.32/0.55    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 1.32/0.55    inference(negated_conjecture,[],[f7])).
% 1.32/0.55  fof(f7,conjecture,(
% 1.32/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).
% 1.32/0.55  fof(f84,plain,(
% 1.32/0.55    ( ! [X0] : (m1_subset_1(X0,sK0) | ~r2_hidden(X0,sK1)) ) | ~spl4_5),
% 1.32/0.55    inference(avatar_component_clause,[],[f83])).
% 1.32/0.55  fof(f83,plain,(
% 1.32/0.55    spl4_5 <=> ! [X0] : (~r2_hidden(X0,sK1) | m1_subset_1(X0,sK0))),
% 1.32/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.32/0.55  fof(f27,plain,(
% 1.32/0.55    k1_xboole_0 != sK1),
% 1.32/0.55    inference(cnf_transformation,[],[f15])).
% 1.32/0.55  fof(f177,plain,(
% 1.32/0.55    ~spl4_4),
% 1.32/0.55    inference(avatar_contradiction_clause,[],[f176])).
% 1.32/0.55  fof(f176,plain,(
% 1.32/0.55    $false | ~spl4_4),
% 1.32/0.55    inference(trivial_inequality_removal,[],[f175])).
% 1.32/0.55  fof(f175,plain,(
% 1.32/0.55    k1_xboole_0 != k1_xboole_0 | ~spl4_4),
% 1.32/0.55    inference(superposition,[],[f27,f163])).
% 1.32/0.55  fof(f163,plain,(
% 1.32/0.55    k1_xboole_0 = sK1 | ~spl4_4),
% 1.32/0.55    inference(forward_demodulation,[],[f142,f140])).
% 1.32/0.55  fof(f140,plain,(
% 1.32/0.55    k1_xboole_0 = sK0 | ~spl4_4),
% 1.32/0.55    inference(resolution,[],[f109,f44])).
% 1.32/0.55  fof(f109,plain,(
% 1.32/0.55    ( ! [X3] : (r2_hidden(sK3(X3,sK0),X3) | sK0 = X3) ) | ~spl4_4),
% 1.32/0.55    inference(resolution,[],[f37,f89])).
% 1.32/0.55  fof(f89,plain,(
% 1.32/0.55    ( ! [X2] : (~r2_hidden(X2,sK0)) ) | ~spl4_4),
% 1.32/0.55    inference(resolution,[],[f77,f29])).
% 1.32/0.55  fof(f29,plain,(
% 1.32/0.55    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f19])).
% 1.32/0.55  fof(f19,plain,(
% 1.32/0.55    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.32/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).
% 1.32/0.55  fof(f18,plain,(
% 1.32/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 1.32/0.55    introduced(choice_axiom,[])).
% 1.32/0.55  fof(f17,plain,(
% 1.32/0.55    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.32/0.55    inference(rectify,[],[f16])).
% 1.32/0.55  fof(f16,plain,(
% 1.32/0.55    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.32/0.55    inference(nnf_transformation,[],[f1])).
% 1.32/0.55  fof(f1,axiom,(
% 1.32/0.55    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.32/0.55  fof(f77,plain,(
% 1.32/0.55    v1_xboole_0(sK0) | ~spl4_4),
% 1.32/0.55    inference(avatar_component_clause,[],[f75])).
% 1.32/0.55  fof(f75,plain,(
% 1.32/0.55    spl4_4 <=> v1_xboole_0(sK0)),
% 1.32/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.32/0.55  fof(f142,plain,(
% 1.32/0.55    sK0 = sK1 | ~spl4_4),
% 1.32/0.55    inference(resolution,[],[f109,f93])).
% 1.32/0.55  fof(f93,plain,(
% 1.32/0.55    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | ~spl4_4),
% 1.32/0.55    inference(resolution,[],[f89,f79])).
% 1.32/0.55  fof(f79,plain,(
% 1.32/0.55    ( ! [X0] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1)) )),
% 1.32/0.55    inference(resolution,[],[f36,f26])).
% 1.32/0.55  fof(f26,plain,(
% 1.32/0.55    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.32/0.55    inference(cnf_transformation,[],[f15])).
% 1.32/0.55  fof(f36,plain,(
% 1.32/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f12])).
% 1.32/0.55  fof(f12,plain,(
% 1.32/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.32/0.55    inference(ennf_transformation,[],[f6])).
% 1.32/0.55  fof(f6,axiom,(
% 1.32/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.32/0.55  fof(f85,plain,(
% 1.32/0.55    spl4_4 | spl4_5),
% 1.32/0.55    inference(avatar_split_clause,[],[f81,f83,f75])).
% 1.32/0.55  fof(f81,plain,(
% 1.32/0.55    ( ! [X0] : (~r2_hidden(X0,sK1) | m1_subset_1(X0,sK0) | v1_xboole_0(sK0)) )),
% 1.32/0.55    inference(resolution,[],[f79,f33])).
% 1.32/0.55  fof(f33,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f20])).
% 1.32/0.55  % (9515)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.32/0.55  % (9507)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.32/0.55  % (9520)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.32/0.55  % (9499)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.32/0.55  % (9518)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.32/0.55  % (9510)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.32/0.55  % (9511)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.32/0.56  % (9513)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.56  
% 1.32/0.56  % (9513)Memory used [KB]: 1663
% 1.32/0.56  % (9513)Time elapsed: 0.141 s
% 1.32/0.56  % (9513)------------------------------
% 1.32/0.56  % (9513)------------------------------
% 1.32/0.56  % (9512)Refutation not found, incomplete strategy% (9512)------------------------------
% 1.32/0.56  % (9512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.56  % (9512)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.56  
% 1.32/0.56  % (9512)Memory used [KB]: 10746
% 1.32/0.56  % (9512)Time elapsed: 0.118 s
% 1.32/0.56  % (9512)------------------------------
% 1.32/0.56  % (9512)------------------------------
% 1.32/0.56  fof(f20,plain,(
% 1.32/0.56    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.32/0.56    inference(nnf_transformation,[],[f11])).
% 1.32/0.56  fof(f11,plain,(
% 1.32/0.56    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.32/0.56    inference(ennf_transformation,[],[f5])).
% 1.32/0.56  fof(f5,axiom,(
% 1.32/0.56    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.32/0.56  % SZS output end Proof for theBenchmark
% 1.32/0.56  % (9504)------------------------------
% 1.32/0.56  % (9504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.56  % (9504)Termination reason: Refutation
% 1.32/0.56  
% 1.32/0.56  % (9504)Memory used [KB]: 6268
% 1.32/0.56  % (9504)Time elapsed: 0.122 s
% 1.32/0.56  % (9504)------------------------------
% 1.32/0.56  % (9504)------------------------------
% 1.32/0.56  % (9488)Success in time 0.184 s
%------------------------------------------------------------------------------
