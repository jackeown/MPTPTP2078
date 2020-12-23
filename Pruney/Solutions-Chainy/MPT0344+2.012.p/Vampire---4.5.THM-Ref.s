%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:44 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 117 expanded)
%              Number of leaves         :   15 (  35 expanded)
%              Depth                    :   13
%              Number of atoms          :  225 ( 424 expanded)
%              Number of equality atoms :   22 (  43 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f191,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f158,f179,f190])).

fof(f190,plain,(
    ~ spl6_1 ),
    inference(avatar_contradiction_clause,[],[f189])).

fof(f189,plain,
    ( $false
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f185,f32])).

fof(f32,plain,(
    k1_xboole_0 != sK1 ),
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

fof(f185,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_1 ),
    inference(resolution,[],[f182,f37])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f20])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f182,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK1)
    | ~ spl6_1 ),
    inference(resolution,[],[f59,f35])).

fof(f35,plain,(
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

fof(f59,plain,
    ( v1_xboole_0(sK1)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl6_1
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f179,plain,(
    spl6_13 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | spl6_13 ),
    inference(resolution,[],[f169,f34])).

fof(f34,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f169,plain,
    ( ! [X0] : ~ r1_tarski(X0,sK0)
    | spl6_13 ),
    inference(resolution,[],[f168,f49])).

fof(f49,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK5(X0,X1),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r1_tarski(sK5(X0,X1),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK5(X0,X1),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( r1_tarski(sK5(X0,X1),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

% (16170)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f168,plain,
    ( ! [X2] : ~ r2_hidden(X2,k1_zfmisc_1(sK0))
    | spl6_13 ),
    inference(resolution,[],[f165,f35])).

fof(f165,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | spl6_13 ),
    inference(subsumption_resolution,[],[f164,f31])).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f164,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | spl6_13 ),
    inference(resolution,[],[f161,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f161,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(sK0))
    | spl6_13 ),
    inference(resolution,[],[f157,f50])).

fof(f50,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f157,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl6_13 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl6_13
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f158,plain,
    ( spl6_1
    | ~ spl6_13
    | spl6_2 ),
    inference(avatar_split_clause,[],[f150,f61,f155,f57])).

fof(f61,plain,
    ( spl6_2
  <=> r2_hidden(sK2(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f150,plain,
    ( ~ r1_tarski(sK1,sK0)
    | v1_xboole_0(sK1)
    | spl6_2 ),
    inference(resolution,[],[f91,f36])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f91,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK2(sK1),X3)
        | ~ r1_tarski(X3,sK0) )
    | spl6_2 ),
    inference(resolution,[],[f42,f63])).

fof(f63,plain,
    ( ~ r2_hidden(sK2(sK1),sK0)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

% (16168)Refutation not found, incomplete strategy% (16168)------------------------------
% (16168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f64,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f53,f61,f57])).

fof(f53,plain,
    ( ~ r2_hidden(sK2(sK1),sK0)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f52,f36])).

fof(f52,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f51,f33])).

fof(f33,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,sK0)
      | ~ r2_hidden(X2,sK1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f39,f35])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.15  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n023.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 16:08:36 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.58  % (16168)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.58  % (16163)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.59  % (16163)Refutation found. Thanks to Tanya!
% 0.22/0.59  % SZS status Theorem for theBenchmark
% 0.22/0.59  % (16176)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.60  % (16171)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.60  % SZS output start Proof for theBenchmark
% 0.22/0.60  fof(f191,plain,(
% 0.22/0.60    $false),
% 0.22/0.60    inference(avatar_sat_refutation,[],[f64,f158,f179,f190])).
% 0.22/0.60  fof(f190,plain,(
% 0.22/0.60    ~spl6_1),
% 0.22/0.60    inference(avatar_contradiction_clause,[],[f189])).
% 0.22/0.60  fof(f189,plain,(
% 0.22/0.60    $false | ~spl6_1),
% 0.22/0.60    inference(subsumption_resolution,[],[f185,f32])).
% 0.22/0.60  fof(f32,plain,(
% 0.22/0.60    k1_xboole_0 != sK1),
% 0.22/0.60    inference(cnf_transformation,[],[f15])).
% 0.22/0.60  fof(f15,plain,(
% 0.22/0.60    ! [X2] : (~r2_hidden(X2,sK1) | ~m1_subset_1(X2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f14])).
% 0.22/0.60  fof(f14,plain,(
% 0.22/0.60    ? [X0,X1] : (! [X2] : (~r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (! [X2] : (~r2_hidden(X2,sK1) | ~m1_subset_1(X2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.22/0.60    introduced(choice_axiom,[])).
% 0.22/0.60  fof(f10,plain,(
% 0.22/0.60    ? [X0,X1] : (! [X2] : (~r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.60    inference(flattening,[],[f9])).
% 0.22/0.60  fof(f9,plain,(
% 0.22/0.60    ? [X0,X1] : ((! [X2] : (~r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.60    inference(ennf_transformation,[],[f8])).
% 0.22/0.60  fof(f8,negated_conjecture,(
% 0.22/0.60    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 0.22/0.60    inference(negated_conjecture,[],[f7])).
% 0.22/0.60  fof(f7,conjecture,(
% 0.22/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).
% 0.22/0.60  fof(f185,plain,(
% 0.22/0.60    k1_xboole_0 = sK1 | ~spl6_1),
% 0.22/0.60    inference(resolution,[],[f182,f37])).
% 0.22/0.60  fof(f37,plain,(
% 0.22/0.60    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.60    inference(cnf_transformation,[],[f21])).
% 0.22/0.60  fof(f21,plain,(
% 0.22/0.60    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.22/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f20])).
% 0.22/0.60  fof(f20,plain,(
% 0.22/0.60    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.22/0.60    introduced(choice_axiom,[])).
% 0.22/0.60  fof(f11,plain,(
% 0.22/0.60    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.60    inference(ennf_transformation,[],[f3])).
% 0.22/0.60  fof(f3,axiom,(
% 0.22/0.60    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.60  fof(f182,plain,(
% 0.22/0.60    ( ! [X2] : (~r2_hidden(X2,sK1)) ) | ~spl6_1),
% 0.22/0.60    inference(resolution,[],[f59,f35])).
% 0.22/0.60  fof(f35,plain,(
% 0.22/0.60    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f19])).
% 0.22/0.60  fof(f19,plain,(
% 0.22/0.60    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).
% 0.22/0.60  fof(f18,plain,(
% 0.22/0.60    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.22/0.60    introduced(choice_axiom,[])).
% 0.22/0.60  fof(f17,plain,(
% 0.22/0.60    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.60    inference(rectify,[],[f16])).
% 0.22/0.60  fof(f16,plain,(
% 0.22/0.60    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.60    inference(nnf_transformation,[],[f1])).
% 0.22/0.60  fof(f1,axiom,(
% 0.22/0.60    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.60  fof(f59,plain,(
% 0.22/0.60    v1_xboole_0(sK1) | ~spl6_1),
% 0.22/0.60    inference(avatar_component_clause,[],[f57])).
% 0.22/0.60  fof(f57,plain,(
% 0.22/0.60    spl6_1 <=> v1_xboole_0(sK1)),
% 0.22/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.60  fof(f179,plain,(
% 0.22/0.60    spl6_13),
% 0.22/0.60    inference(avatar_contradiction_clause,[],[f174])).
% 0.22/0.60  fof(f174,plain,(
% 0.22/0.60    $false | spl6_13),
% 0.22/0.60    inference(resolution,[],[f169,f34])).
% 0.22/0.60  fof(f34,plain,(
% 0.22/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f4])).
% 0.22/0.60  fof(f4,axiom,(
% 0.22/0.60    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.60  fof(f169,plain,(
% 0.22/0.60    ( ! [X0] : (~r1_tarski(X0,sK0)) ) | spl6_13),
% 0.22/0.60    inference(resolution,[],[f168,f49])).
% 0.22/0.60  fof(f49,plain,(
% 0.22/0.60    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.22/0.60    inference(equality_resolution,[],[f46])).
% 0.22/0.60  fof(f46,plain,(
% 0.22/0.60    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.22/0.60    inference(cnf_transformation,[],[f30])).
% 0.22/0.60  fof(f30,plain,(
% 0.22/0.60    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK5(X0,X1),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r1_tarski(sK5(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f29])).
% 0.22/0.60  fof(f29,plain,(
% 0.22/0.60    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK5(X0,X1),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r1_tarski(sK5(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 0.22/0.60    introduced(choice_axiom,[])).
% 0.22/0.60  fof(f28,plain,(
% 0.22/0.60    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.60    inference(rectify,[],[f27])).
% 0.22/0.60  fof(f27,plain,(
% 0.22/0.60    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.60    inference(nnf_transformation,[],[f5])).
% 0.22/0.60  fof(f5,axiom,(
% 0.22/0.60    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.22/0.60  % (16170)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.60  fof(f168,plain,(
% 0.22/0.60    ( ! [X2] : (~r2_hidden(X2,k1_zfmisc_1(sK0))) ) | spl6_13),
% 0.22/0.60    inference(resolution,[],[f165,f35])).
% 0.22/0.60  fof(f165,plain,(
% 0.22/0.60    v1_xboole_0(k1_zfmisc_1(sK0)) | spl6_13),
% 0.22/0.60    inference(subsumption_resolution,[],[f164,f31])).
% 0.22/0.60  fof(f31,plain,(
% 0.22/0.60    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.60    inference(cnf_transformation,[],[f15])).
% 0.22/0.60  fof(f164,plain,(
% 0.22/0.60    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | spl6_13),
% 0.22/0.60    inference(resolution,[],[f161,f38])).
% 0.22/0.60  fof(f38,plain,(
% 0.22/0.60    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f22])).
% 0.22/0.60  fof(f22,plain,(
% 0.22/0.60    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.22/0.60    inference(nnf_transformation,[],[f12])).
% 0.22/0.60  fof(f12,plain,(
% 0.22/0.60    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.22/0.60    inference(ennf_transformation,[],[f6])).
% 0.22/0.60  fof(f6,axiom,(
% 0.22/0.60    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.22/0.60  fof(f161,plain,(
% 0.22/0.60    ~r2_hidden(sK1,k1_zfmisc_1(sK0)) | spl6_13),
% 0.22/0.60    inference(resolution,[],[f157,f50])).
% 0.22/0.60  fof(f50,plain,(
% 0.22/0.60    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 0.22/0.60    inference(equality_resolution,[],[f45])).
% 0.22/0.60  fof(f45,plain,(
% 0.22/0.60    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.22/0.60    inference(cnf_transformation,[],[f30])).
% 0.22/0.60  fof(f157,plain,(
% 0.22/0.60    ~r1_tarski(sK1,sK0) | spl6_13),
% 0.22/0.60    inference(avatar_component_clause,[],[f155])).
% 0.22/0.60  fof(f155,plain,(
% 0.22/0.60    spl6_13 <=> r1_tarski(sK1,sK0)),
% 0.22/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.22/0.60  fof(f158,plain,(
% 0.22/0.60    spl6_1 | ~spl6_13 | spl6_2),
% 0.22/0.60    inference(avatar_split_clause,[],[f150,f61,f155,f57])).
% 0.22/0.60  fof(f61,plain,(
% 0.22/0.60    spl6_2 <=> r2_hidden(sK2(sK1),sK0)),
% 0.22/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.60  fof(f150,plain,(
% 0.22/0.60    ~r1_tarski(sK1,sK0) | v1_xboole_0(sK1) | spl6_2),
% 0.22/0.60    inference(resolution,[],[f91,f36])).
% 0.22/0.60  fof(f36,plain,(
% 0.22/0.60    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f19])).
% 0.22/0.60  fof(f91,plain,(
% 0.22/0.60    ( ! [X3] : (~r2_hidden(sK2(sK1),X3) | ~r1_tarski(X3,sK0)) ) | spl6_2),
% 0.22/0.60    inference(resolution,[],[f42,f63])).
% 0.22/0.60  fof(f63,plain,(
% 0.22/0.60    ~r2_hidden(sK2(sK1),sK0) | spl6_2),
% 0.22/0.60    inference(avatar_component_clause,[],[f61])).
% 0.22/0.60  fof(f42,plain,(
% 0.22/0.60    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f26])).
% 0.22/0.60  % (16168)Refutation not found, incomplete strategy% (16168)------------------------------
% 0.22/0.60  % (16168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.60  fof(f26,plain,(
% 0.22/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).
% 0.22/0.60  fof(f25,plain,(
% 0.22/0.60    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.22/0.60    introduced(choice_axiom,[])).
% 0.22/0.60  fof(f24,plain,(
% 0.22/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.60    inference(rectify,[],[f23])).
% 0.22/0.60  fof(f23,plain,(
% 0.22/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.60    inference(nnf_transformation,[],[f13])).
% 0.22/0.60  fof(f13,plain,(
% 0.22/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.60    inference(ennf_transformation,[],[f2])).
% 0.22/0.60  fof(f2,axiom,(
% 0.22/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.60  fof(f64,plain,(
% 0.22/0.60    spl6_1 | ~spl6_2),
% 0.22/0.60    inference(avatar_split_clause,[],[f53,f61,f57])).
% 0.22/0.60  fof(f53,plain,(
% 0.22/0.60    ~r2_hidden(sK2(sK1),sK0) | v1_xboole_0(sK1)),
% 0.22/0.60    inference(resolution,[],[f52,f36])).
% 0.22/0.60  fof(f52,plain,(
% 0.22/0.60    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) )),
% 0.22/0.60    inference(resolution,[],[f51,f33])).
% 0.22/0.60  fof(f33,plain,(
% 0.22/0.60    ( ! [X2] : (~m1_subset_1(X2,sK0) | ~r2_hidden(X2,sK1)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f15])).
% 0.22/0.60  fof(f51,plain,(
% 0.22/0.60    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) )),
% 0.22/0.60    inference(subsumption_resolution,[],[f39,f35])).
% 0.22/0.60  fof(f39,plain,(
% 0.22/0.60    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f22])).
% 0.22/0.60  % SZS output end Proof for theBenchmark
% 0.22/0.60  % (16163)------------------------------
% 0.22/0.60  % (16163)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.60  % (16163)Termination reason: Refutation
% 0.22/0.60  
% 0.22/0.60  % (16163)Memory used [KB]: 10746
% 0.22/0.60  % (16163)Time elapsed: 0.148 s
% 0.22/0.60  % (16163)------------------------------
% 0.22/0.60  % (16163)------------------------------
% 0.22/0.60  % (16186)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.60  % (16170)Refutation not found, incomplete strategy% (16170)------------------------------
% 0.22/0.60  % (16170)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.60  % (16170)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.60  
% 0.22/0.60  % (16170)Memory used [KB]: 10618
% 0.22/0.60  % (16170)Time elapsed: 0.158 s
% 0.22/0.60  % (16170)------------------------------
% 0.22/0.60  % (16170)------------------------------
% 0.22/0.60  % (16168)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.60  
% 0.22/0.60  % (16168)Memory used [KB]: 10746
% 0.22/0.60  % (16168)Time elapsed: 0.157 s
% 0.22/0.60  % (16168)------------------------------
% 0.22/0.60  % (16168)------------------------------
% 0.22/0.60  % (16159)Success in time 0.225 s
%------------------------------------------------------------------------------
