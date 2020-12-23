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
% DateTime   : Thu Dec  3 12:43:45 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 337 expanded)
%              Number of leaves         :   13 (  91 expanded)
%              Depth                    :   19
%              Number of atoms          :  229 (1224 expanded)
%              Number of equality atoms :   36 ( 286 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f190,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f109,f113,f189])).

fof(f189,plain,
    ( spl4_4
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f188])).

fof(f188,plain,
    ( $false
    | spl4_4
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f187,f186])).

fof(f186,plain,
    ( ! [X0] : r1_tarski(sK1,X0)
    | spl4_4
    | ~ spl4_7 ),
    inference(resolution,[],[f183,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f183,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | spl4_4
    | ~ spl4_7 ),
    inference(resolution,[],[f176,f28])).

fof(f28,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,sK0)
      | ~ r2_hidden(X2,sK1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK1)
        | ~ m1_subset_1(X2,sK0) )
    & k1_xboole_0 != sK1
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f16])).

fof(f16,plain,
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

fof(f176,plain,
    ( ! [X2] : m1_subset_1(X2,sK0)
    | spl4_4
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f174,f76])).

fof(f76,plain,
    ( ~ v1_xboole_0(sK0)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl4_4
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f174,plain,
    ( ! [X2] :
        ( m1_subset_1(X2,sK0)
        | v1_xboole_0(sK0) )
    | ~ spl4_7 ),
    inference(resolution,[],[f171,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f171,plain,
    ( ! [X8] : r2_hidden(X8,sK0)
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f169,f147])).

fof(f147,plain,
    ( ! [X0,X1] :
        ( r1_tarski(sK1,X0)
        | r1_tarski(X0,X1) )
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f118,f137])).

fof(f137,plain,
    ( ! [X0] : k1_tarski(X0) = sK1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f136,f27])).

% (11934)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f27,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f17])).

fof(f136,plain,
    ( ! [X0] :
        ( k1_tarski(X0) = sK1
        | k1_xboole_0 = sK1 )
    | ~ spl4_7 ),
    inference(duplicate_literal_removal,[],[f135])).

fof(f135,plain,
    ( ! [X0] :
        ( k1_tarski(X0) = sK1
        | k1_xboole_0 = sK1
        | k1_tarski(X0) = sK1 )
    | ~ spl4_7 ),
    inference(resolution,[],[f132,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( sK3(X0,X1) != X1
        & r2_hidden(sK3(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK3(X0,X1) != X1
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(f132,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(sK1,X0),sK1)
        | k1_tarski(X0) = sK1 )
    | ~ spl4_7 ),
    inference(resolution,[],[f112,f28])).

fof(f112,plain,
    ( ! [X4] :
        ( m1_subset_1(sK3(sK1,X4),sK0)
        | sK1 = k1_tarski(X4) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl4_7
  <=> ! [X4] :
        ( sK1 = k1_tarski(X4)
        | m1_subset_1(sK3(sK1,X4),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f118,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(sK2(X0,X1)),X0)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f38,f35])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(f169,plain,
    ( ! [X8] :
        ( ~ r1_tarski(sK1,sK1)
        | r2_hidden(X8,sK0) )
    | ~ spl4_7 ),
    inference(resolution,[],[f138,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f26,f33])).

fof(f33,plain,(
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

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f138,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,X1)
        | ~ r1_tarski(sK1,X1) )
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f37,f137])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f187,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl4_4
    | ~ spl4_7 ),
    inference(resolution,[],[f183,f138])).

fof(f113,plain,
    ( spl4_4
    | spl4_7 ),
    inference(avatar_split_clause,[],[f88,f111,f74])).

fof(f88,plain,(
    ! [X4] :
      ( sK1 = k1_tarski(X4)
      | m1_subset_1(sK3(sK1,X4),sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f66,f30])).

fof(f66,plain,(
    ! [X1] :
      ( r2_hidden(sK3(sK1,X1),sK0)
      | k1_tarski(X1) = sK1 ) ),
    inference(subsumption_resolution,[],[f65,f27])).

fof(f65,plain,(
    ! [X1] :
      ( r2_hidden(sK3(sK1,X1),sK0)
      | k1_xboole_0 = sK1
      | k1_tarski(X1) = sK1 ) ),
    inference(resolution,[],[f42,f40])).

fof(f109,plain,
    ( ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(resolution,[],[f98,f75])).

fof(f75,plain,
    ( v1_xboole_0(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f98,plain,
    ( ! [X0] : ~ v1_xboole_0(X0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(resolution,[],[f96,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f96,plain,
    ( ! [X0,X1] : r2_hidden(X0,X1)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f92,f79])).

fof(f79,plain,
    ( ! [X0] : r1_tarski(sK1,X0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl4_5
  <=> ! [X0] : r1_tarski(sK1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f92,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK1,X1)
        | r2_hidden(X0,X1) )
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f37,f89])).

fof(f89,plain,
    ( ! [X0] : k1_tarski(X0) = sK1
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f85,f75])).

fof(f85,plain,(
    ! [X0] :
      ( k1_tarski(X0) = sK1
      | ~ v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f66,f39])).

fof(f80,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f68,f78,f74])).

fof(f68,plain,(
    ! [X0] :
      ( r1_tarski(sK1,X0)
      | ~ v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f64,f39])).

fof(f64,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK1,X0),sK0)
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f42,f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 12:31:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.52  % (11929)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.23/0.52  % (11905)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.23/0.52  % (11914)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.19/0.52  % (11913)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.19/0.52  % (11910)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.19/0.53  % (11913)Refutation found. Thanks to Tanya!
% 1.19/0.53  % SZS status Theorem for theBenchmark
% 1.19/0.53  % (11912)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.19/0.53  % SZS output start Proof for theBenchmark
% 1.19/0.53  fof(f190,plain,(
% 1.19/0.53    $false),
% 1.19/0.53    inference(avatar_sat_refutation,[],[f80,f109,f113,f189])).
% 1.19/0.53  fof(f189,plain,(
% 1.19/0.53    spl4_4 | ~spl4_7),
% 1.19/0.53    inference(avatar_contradiction_clause,[],[f188])).
% 1.19/0.53  fof(f188,plain,(
% 1.19/0.53    $false | (spl4_4 | ~spl4_7)),
% 1.19/0.53    inference(subsumption_resolution,[],[f187,f186])).
% 1.19/0.53  fof(f186,plain,(
% 1.19/0.53    ( ! [X0] : (r1_tarski(sK1,X0)) ) | (spl4_4 | ~spl4_7)),
% 1.19/0.53    inference(resolution,[],[f183,f35])).
% 1.19/0.53  fof(f35,plain,(
% 1.19/0.53    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f22])).
% 1.19/0.53  fof(f22,plain,(
% 1.19/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.19/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).
% 1.19/0.53  fof(f21,plain,(
% 1.19/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 1.19/0.53    introduced(choice_axiom,[])).
% 1.19/0.53  fof(f20,plain,(
% 1.19/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.19/0.53    inference(rectify,[],[f19])).
% 1.19/0.53  fof(f19,plain,(
% 1.19/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.19/0.53    inference(nnf_transformation,[],[f13])).
% 1.19/0.53  fof(f13,plain,(
% 1.19/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.19/0.53    inference(ennf_transformation,[],[f1])).
% 1.19/0.53  fof(f1,axiom,(
% 1.19/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.19/0.53  fof(f183,plain,(
% 1.19/0.53    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | (spl4_4 | ~spl4_7)),
% 1.19/0.53    inference(resolution,[],[f176,f28])).
% 1.19/0.53  fof(f28,plain,(
% 1.19/0.53    ( ! [X2] : (~m1_subset_1(X2,sK0) | ~r2_hidden(X2,sK1)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f17])).
% 1.19/0.53  fof(f17,plain,(
% 1.19/0.53    ! [X2] : (~r2_hidden(X2,sK1) | ~m1_subset_1(X2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.19/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f16])).
% 1.19/0.53  fof(f16,plain,(
% 1.19/0.53    ? [X0,X1] : (! [X2] : (~r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (! [X2] : (~r2_hidden(X2,sK1) | ~m1_subset_1(X2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.19/0.53    introduced(choice_axiom,[])).
% 1.19/0.53  fof(f10,plain,(
% 1.19/0.53    ? [X0,X1] : (! [X2] : (~r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.19/0.53    inference(flattening,[],[f9])).
% 1.19/0.53  fof(f9,plain,(
% 1.19/0.53    ? [X0,X1] : ((! [X2] : (~r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.19/0.53    inference(ennf_transformation,[],[f8])).
% 1.19/0.53  fof(f8,negated_conjecture,(
% 1.19/0.53    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 1.19/0.53    inference(negated_conjecture,[],[f7])).
% 1.19/0.53  fof(f7,conjecture,(
% 1.19/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).
% 1.19/0.53  fof(f176,plain,(
% 1.19/0.53    ( ! [X2] : (m1_subset_1(X2,sK0)) ) | (spl4_4 | ~spl4_7)),
% 1.19/0.53    inference(subsumption_resolution,[],[f174,f76])).
% 1.19/0.53  fof(f76,plain,(
% 1.19/0.53    ~v1_xboole_0(sK0) | spl4_4),
% 1.19/0.53    inference(avatar_component_clause,[],[f74])).
% 1.19/0.53  fof(f74,plain,(
% 1.19/0.53    spl4_4 <=> v1_xboole_0(sK0)),
% 1.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.19/0.53  fof(f174,plain,(
% 1.19/0.53    ( ! [X2] : (m1_subset_1(X2,sK0) | v1_xboole_0(sK0)) ) | ~spl4_7),
% 1.19/0.53    inference(resolution,[],[f171,f30])).
% 1.19/0.53  fof(f30,plain,(
% 1.19/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f18])).
% 1.19/0.53  fof(f18,plain,(
% 1.19/0.53    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.19/0.53    inference(nnf_transformation,[],[f11])).
% 1.19/0.53  fof(f11,plain,(
% 1.19/0.53    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.19/0.53    inference(ennf_transformation,[],[f5])).
% 1.19/0.53  fof(f5,axiom,(
% 1.19/0.53    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.19/0.53  fof(f171,plain,(
% 1.19/0.53    ( ! [X8] : (r2_hidden(X8,sK0)) ) | ~spl4_7),
% 1.19/0.53    inference(subsumption_resolution,[],[f169,f147])).
% 1.19/0.53  fof(f147,plain,(
% 1.19/0.53    ( ! [X0,X1] : (r1_tarski(sK1,X0) | r1_tarski(X0,X1)) ) | ~spl4_7),
% 1.19/0.53    inference(backward_demodulation,[],[f118,f137])).
% 1.19/0.53  fof(f137,plain,(
% 1.19/0.53    ( ! [X0] : (k1_tarski(X0) = sK1) ) | ~spl4_7),
% 1.19/0.53    inference(subsumption_resolution,[],[f136,f27])).
% 1.19/0.53  % (11934)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.19/0.53  fof(f27,plain,(
% 1.19/0.53    k1_xboole_0 != sK1),
% 1.19/0.53    inference(cnf_transformation,[],[f17])).
% 1.19/0.53  fof(f136,plain,(
% 1.19/0.53    ( ! [X0] : (k1_tarski(X0) = sK1 | k1_xboole_0 = sK1) ) | ~spl4_7),
% 1.19/0.53    inference(duplicate_literal_removal,[],[f135])).
% 1.19/0.53  fof(f135,plain,(
% 1.19/0.53    ( ! [X0] : (k1_tarski(X0) = sK1 | k1_xboole_0 = sK1 | k1_tarski(X0) = sK1) ) | ~spl4_7),
% 1.19/0.53    inference(resolution,[],[f132,f40])).
% 1.19/0.53  fof(f40,plain,(
% 1.19/0.53    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.19/0.53    inference(cnf_transformation,[],[f25])).
% 1.19/0.53  fof(f25,plain,(
% 1.19/0.53    ! [X0,X1] : ((sK3(X0,X1) != X1 & r2_hidden(sK3(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 1.19/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f24])).
% 1.19/0.53  fof(f24,plain,(
% 1.19/0.53    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK3(X0,X1) != X1 & r2_hidden(sK3(X0,X1),X0)))),
% 1.19/0.53    introduced(choice_axiom,[])).
% 1.19/0.53  fof(f15,plain,(
% 1.19/0.53    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 1.19/0.53    inference(ennf_transformation,[],[f3])).
% 1.19/0.53  fof(f3,axiom,(
% 1.19/0.53    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).
% 1.19/0.53  fof(f132,plain,(
% 1.19/0.53    ( ! [X0] : (~r2_hidden(sK3(sK1,X0),sK1) | k1_tarski(X0) = sK1) ) | ~spl4_7),
% 1.19/0.53    inference(resolution,[],[f112,f28])).
% 1.19/0.53  fof(f112,plain,(
% 1.19/0.53    ( ! [X4] : (m1_subset_1(sK3(sK1,X4),sK0) | sK1 = k1_tarski(X4)) ) | ~spl4_7),
% 1.19/0.53    inference(avatar_component_clause,[],[f111])).
% 1.19/0.53  fof(f111,plain,(
% 1.19/0.53    spl4_7 <=> ! [X4] : (sK1 = k1_tarski(X4) | m1_subset_1(sK3(sK1,X4),sK0))),
% 1.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.19/0.53  fof(f118,plain,(
% 1.19/0.53    ( ! [X0,X1] : (r1_tarski(k1_tarski(sK2(X0,X1)),X0) | r1_tarski(X0,X1)) )),
% 1.19/0.53    inference(resolution,[],[f38,f35])).
% 1.19/0.53  fof(f38,plain,(
% 1.19/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f23])).
% 1.19/0.53  fof(f23,plain,(
% 1.19/0.53    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.19/0.53    inference(nnf_transformation,[],[f4])).
% 1.19/0.53  fof(f4,axiom,(
% 1.19/0.53    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).
% 1.19/0.53  fof(f169,plain,(
% 1.19/0.53    ( ! [X8] : (~r1_tarski(sK1,sK1) | r2_hidden(X8,sK0)) ) | ~spl4_7),
% 1.19/0.53    inference(resolution,[],[f138,f42])).
% 1.19/0.53  fof(f42,plain,(
% 1.19/0.53    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK0)) )),
% 1.19/0.53    inference(resolution,[],[f26,f33])).
% 1.19/0.53  fof(f33,plain,(
% 1.19/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f12])).
% 1.19/0.53  fof(f12,plain,(
% 1.19/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.19/0.53    inference(ennf_transformation,[],[f6])).
% 1.19/0.53  fof(f6,axiom,(
% 1.19/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.19/0.53  fof(f26,plain,(
% 1.19/0.53    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.19/0.53    inference(cnf_transformation,[],[f17])).
% 1.19/0.53  fof(f138,plain,(
% 1.19/0.53    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(sK1,X1)) ) | ~spl4_7),
% 1.19/0.53    inference(backward_demodulation,[],[f37,f137])).
% 1.19/0.53  fof(f37,plain,(
% 1.19/0.53    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f23])).
% 1.19/0.53  fof(f187,plain,(
% 1.19/0.53    ~r1_tarski(sK1,sK1) | (spl4_4 | ~spl4_7)),
% 1.19/0.53    inference(resolution,[],[f183,f138])).
% 1.19/0.53  fof(f113,plain,(
% 1.19/0.53    spl4_4 | spl4_7),
% 1.19/0.53    inference(avatar_split_clause,[],[f88,f111,f74])).
% 1.19/0.53  fof(f88,plain,(
% 1.19/0.53    ( ! [X4] : (sK1 = k1_tarski(X4) | m1_subset_1(sK3(sK1,X4),sK0) | v1_xboole_0(sK0)) )),
% 1.19/0.53    inference(resolution,[],[f66,f30])).
% 1.19/0.53  fof(f66,plain,(
% 1.19/0.53    ( ! [X1] : (r2_hidden(sK3(sK1,X1),sK0) | k1_tarski(X1) = sK1) )),
% 1.19/0.53    inference(subsumption_resolution,[],[f65,f27])).
% 1.19/0.53  fof(f65,plain,(
% 1.19/0.53    ( ! [X1] : (r2_hidden(sK3(sK1,X1),sK0) | k1_xboole_0 = sK1 | k1_tarski(X1) = sK1) )),
% 1.19/0.53    inference(resolution,[],[f42,f40])).
% 1.19/0.53  fof(f109,plain,(
% 1.19/0.53    ~spl4_4 | ~spl4_5),
% 1.19/0.53    inference(avatar_contradiction_clause,[],[f108])).
% 1.19/0.53  fof(f108,plain,(
% 1.19/0.53    $false | (~spl4_4 | ~spl4_5)),
% 1.19/0.53    inference(resolution,[],[f98,f75])).
% 1.19/0.53  fof(f75,plain,(
% 1.19/0.53    v1_xboole_0(sK0) | ~spl4_4),
% 1.19/0.53    inference(avatar_component_clause,[],[f74])).
% 1.19/0.53  fof(f98,plain,(
% 1.19/0.53    ( ! [X0] : (~v1_xboole_0(X0)) ) | (~spl4_4 | ~spl4_5)),
% 1.19/0.53    inference(resolution,[],[f96,f39])).
% 1.19/0.53  fof(f39,plain,(
% 1.19/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v1_xboole_0(X1)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f14])).
% 1.19/0.53  fof(f14,plain,(
% 1.19/0.53    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 1.19/0.53    inference(ennf_transformation,[],[f2])).
% 1.19/0.53  fof(f2,axiom,(
% 1.19/0.53    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).
% 1.19/0.53  fof(f96,plain,(
% 1.19/0.53    ( ! [X0,X1] : (r2_hidden(X0,X1)) ) | (~spl4_4 | ~spl4_5)),
% 1.19/0.53    inference(subsumption_resolution,[],[f92,f79])).
% 1.19/0.53  fof(f79,plain,(
% 1.19/0.53    ( ! [X0] : (r1_tarski(sK1,X0)) ) | ~spl4_5),
% 1.19/0.53    inference(avatar_component_clause,[],[f78])).
% 1.19/0.53  fof(f78,plain,(
% 1.19/0.53    spl4_5 <=> ! [X0] : r1_tarski(sK1,X0)),
% 1.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.19/0.53  fof(f92,plain,(
% 1.19/0.53    ( ! [X0,X1] : (~r1_tarski(sK1,X1) | r2_hidden(X0,X1)) ) | ~spl4_4),
% 1.19/0.53    inference(backward_demodulation,[],[f37,f89])).
% 1.19/0.53  fof(f89,plain,(
% 1.19/0.53    ( ! [X0] : (k1_tarski(X0) = sK1) ) | ~spl4_4),
% 1.19/0.53    inference(subsumption_resolution,[],[f85,f75])).
% 1.19/0.53  fof(f85,plain,(
% 1.19/0.53    ( ! [X0] : (k1_tarski(X0) = sK1 | ~v1_xboole_0(sK0)) )),
% 1.19/0.53    inference(resolution,[],[f66,f39])).
% 1.19/0.53  fof(f80,plain,(
% 1.19/0.53    ~spl4_4 | spl4_5),
% 1.19/0.53    inference(avatar_split_clause,[],[f68,f78,f74])).
% 1.19/0.53  fof(f68,plain,(
% 1.19/0.53    ( ! [X0] : (r1_tarski(sK1,X0) | ~v1_xboole_0(sK0)) )),
% 1.19/0.53    inference(resolution,[],[f64,f39])).
% 1.19/0.53  fof(f64,plain,(
% 1.19/0.53    ( ! [X0] : (r2_hidden(sK2(sK1,X0),sK0) | r1_tarski(sK1,X0)) )),
% 1.19/0.53    inference(resolution,[],[f42,f35])).
% 1.19/0.53  % SZS output end Proof for theBenchmark
% 1.19/0.53  % (11913)------------------------------
% 1.19/0.53  % (11913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.53  % (11913)Termination reason: Refutation
% 1.19/0.53  
% 1.19/0.53  % (11913)Memory used [KB]: 10746
% 1.19/0.53  % (11913)Time elapsed: 0.109 s
% 1.19/0.53  % (11913)------------------------------
% 1.19/0.53  % (11913)------------------------------
% 1.19/0.53  % (11909)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.19/0.53  % (11921)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.19/0.53  % (11906)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.34/0.54  % (11922)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.34/0.54  % (11917)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.34/0.54  % (11904)Success in time 0.166 s
%------------------------------------------------------------------------------
