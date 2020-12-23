%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:31 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   66 (  95 expanded)
%              Number of leaves         :   14 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :  200 ( 313 expanded)
%              Number of equality atoms :   30 (  44 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f201,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f85,f180,f194,f200])).

fof(f200,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f199])).

fof(f199,plain,
    ( $false
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f198,f26])).

fof(f26,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
    & k1_xboole_0 != sK0
    & m1_subset_1(sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
        & k1_xboole_0 != X0
        & m1_subset_1(X1,X0) )
   => ( ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
      & k1_xboole_0 != sK0
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      & k1_xboole_0 != X0
      & m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      & k1_xboole_0 != X0
      & m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,X0)
       => ( k1_xboole_0 != X0
         => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ( k1_xboole_0 != X0
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

fof(f198,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_1 ),
    inference(resolution,[],[f50,f38])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f50,plain,
    ( v1_xboole_0(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl4_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f194,plain,
    ( spl4_1
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f193])).

fof(f193,plain,
    ( $false
    | spl4_1
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f181,f80])).

fof(f80,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl4_4
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f181,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK0))
    | spl4_1 ),
    inference(subsumption_resolution,[],[f122,f65])).

fof(f65,plain,
    ( ~ v1_xboole_0(sK3(sK0))
    | spl4_1 ),
    inference(resolution,[],[f49,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK3(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f20])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_subset_1)).

fof(f49,plain,
    ( ~ v1_xboole_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f122,plain,
    ( v1_xboole_0(sK3(sK0))
    | ~ v1_xboole_0(k1_zfmisc_1(sK0))
    | spl4_1 ),
    inference(resolution,[],[f64,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f64,plain,
    ( m1_subset_1(sK3(sK0),k1_zfmisc_1(sK0))
    | spl4_1 ),
    inference(resolution,[],[f49,f32])).

fof(f32,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f180,plain,
    ( ~ spl4_2
    | spl4_5 ),
    inference(avatar_contradiction_clause,[],[f179])).

fof(f179,plain,
    ( $false
    | ~ spl4_2
    | spl4_5 ),
    inference(subsumption_resolution,[],[f177,f110])).

fof(f110,plain,
    ( ~ r1_tarski(k1_tarski(sK1),sK0)
    | spl4_5 ),
    inference(resolution,[],[f84,f43])).

fof(f43,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f84,plain,
    ( ~ r2_hidden(k1_tarski(sK1),k1_zfmisc_1(sK0))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl4_5
  <=> r2_hidden(k1_tarski(sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f177,plain,
    ( r1_tarski(k1_tarski(sK1),sK0)
    | ~ spl4_2 ),
    inference(trivial_inequality_removal,[],[f176])).

fof(f176,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_tarski(sK1),sK0)
    | ~ spl4_2 ),
    inference(superposition,[],[f36,f67])).

fof(f67,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f54,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).

fof(f54,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl4_2
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f85,plain,
    ( spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f73,f82,f78])).

fof(f73,plain,
    ( ~ r2_hidden(k1_tarski(sK1),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f27,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f27,plain,(
    ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f55,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f45,f52,f48])).

fof(f45,plain,
    ( r2_hidden(sK1,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f25,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f25,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:42:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.43  % (7905)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.19/0.43  % (7905)Refutation found. Thanks to Tanya!
% 0.19/0.43  % SZS status Theorem for theBenchmark
% 0.19/0.43  % SZS output start Proof for theBenchmark
% 0.19/0.43  fof(f201,plain,(
% 0.19/0.43    $false),
% 0.19/0.43    inference(avatar_sat_refutation,[],[f55,f85,f180,f194,f200])).
% 0.19/0.43  fof(f200,plain,(
% 0.19/0.43    ~spl4_1),
% 0.19/0.43    inference(avatar_contradiction_clause,[],[f199])).
% 0.19/0.43  fof(f199,plain,(
% 0.19/0.43    $false | ~spl4_1),
% 0.19/0.43    inference(subsumption_resolution,[],[f198,f26])).
% 0.19/0.43  fof(f26,plain,(
% 0.19/0.43    k1_xboole_0 != sK0),
% 0.19/0.43    inference(cnf_transformation,[],[f15])).
% 0.19/0.43  fof(f15,plain,(
% 0.19/0.43    ~m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) & k1_xboole_0 != sK0 & m1_subset_1(sK1,sK0)),
% 0.19/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f14])).
% 0.19/0.43  fof(f14,plain,(
% 0.19/0.43    ? [X0,X1] : (~m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X1,X0)) => (~m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) & k1_xboole_0 != sK0 & m1_subset_1(sK1,sK0))),
% 0.19/0.43    introduced(choice_axiom,[])).
% 0.19/0.43  fof(f10,plain,(
% 0.19/0.43    ? [X0,X1] : (~m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X1,X0))),
% 0.19/0.43    inference(flattening,[],[f9])).
% 0.19/0.43  fof(f9,plain,(
% 0.19/0.43    ? [X0,X1] : ((~m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) & k1_xboole_0 != X0) & m1_subset_1(X1,X0))),
% 0.19/0.43    inference(ennf_transformation,[],[f8])).
% 0.19/0.43  fof(f8,negated_conjecture,(
% 0.19/0.43    ~! [X0,X1] : (m1_subset_1(X1,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))))),
% 0.19/0.43    inference(negated_conjecture,[],[f7])).
% 0.19/0.43  fof(f7,conjecture,(
% 0.19/0.43    ! [X0,X1] : (m1_subset_1(X1,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))))),
% 0.19/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).
% 0.19/0.43  fof(f198,plain,(
% 0.19/0.43    k1_xboole_0 = sK0 | ~spl4_1),
% 0.19/0.43    inference(resolution,[],[f50,f38])).
% 0.19/0.43  fof(f38,plain,(
% 0.19/0.43    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f12])).
% 0.19/0.43  fof(f12,plain,(
% 0.19/0.43    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.19/0.43    inference(ennf_transformation,[],[f1])).
% 0.19/0.43  fof(f1,axiom,(
% 0.19/0.43    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.19/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.19/0.43  fof(f50,plain,(
% 0.19/0.43    v1_xboole_0(sK0) | ~spl4_1),
% 0.19/0.43    inference(avatar_component_clause,[],[f48])).
% 0.19/0.43  fof(f48,plain,(
% 0.19/0.43    spl4_1 <=> v1_xboole_0(sK0)),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.19/0.43  fof(f194,plain,(
% 0.19/0.43    spl4_1 | ~spl4_4),
% 0.19/0.43    inference(avatar_contradiction_clause,[],[f193])).
% 0.19/0.43  fof(f193,plain,(
% 0.19/0.43    $false | (spl4_1 | ~spl4_4)),
% 0.19/0.43    inference(subsumption_resolution,[],[f181,f80])).
% 0.19/0.43  fof(f80,plain,(
% 0.19/0.43    v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl4_4),
% 0.19/0.43    inference(avatar_component_clause,[],[f78])).
% 0.19/0.43  fof(f78,plain,(
% 0.19/0.43    spl4_4 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.19/0.43  fof(f181,plain,(
% 0.19/0.43    ~v1_xboole_0(k1_zfmisc_1(sK0)) | spl4_1),
% 0.19/0.43    inference(subsumption_resolution,[],[f122,f65])).
% 0.19/0.43  fof(f65,plain,(
% 0.19/0.43    ~v1_xboole_0(sK3(sK0)) | spl4_1),
% 0.19/0.43    inference(resolution,[],[f49,f33])).
% 0.19/0.43  fof(f33,plain,(
% 0.19/0.43    ( ! [X0] : (~v1_xboole_0(sK3(X0)) | v1_xboole_0(X0)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f21])).
% 0.19/0.43  fof(f21,plain,(
% 0.19/0.43    ! [X0] : ((~v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.19/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f20])).
% 0.19/0.43  fof(f20,plain,(
% 0.19/0.43    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (~v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(X0))))),
% 0.19/0.43    introduced(choice_axiom,[])).
% 0.19/0.43  fof(f11,plain,(
% 0.19/0.43    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.19/0.43    inference(ennf_transformation,[],[f6])).
% 0.19/0.43  fof(f6,axiom,(
% 0.19/0.43    ! [X0] : (~v1_xboole_0(X0) => ? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.19/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_subset_1)).
% 0.19/0.43  fof(f49,plain,(
% 0.19/0.43    ~v1_xboole_0(sK0) | spl4_1),
% 0.19/0.43    inference(avatar_component_clause,[],[f48])).
% 0.19/0.43  fof(f122,plain,(
% 0.19/0.43    v1_xboole_0(sK3(sK0)) | ~v1_xboole_0(k1_zfmisc_1(sK0)) | spl4_1),
% 0.19/0.43    inference(resolution,[],[f64,f41])).
% 0.19/0.43  fof(f41,plain,(
% 0.19/0.43    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f24])).
% 0.19/0.43  fof(f24,plain,(
% 0.19/0.43    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.19/0.43    inference(nnf_transformation,[],[f13])).
% 0.19/0.43  fof(f13,plain,(
% 0.19/0.43    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.19/0.43    inference(ennf_transformation,[],[f5])).
% 0.19/0.43  fof(f5,axiom,(
% 0.19/0.43    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.19/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.19/0.43  fof(f64,plain,(
% 0.19/0.43    m1_subset_1(sK3(sK0),k1_zfmisc_1(sK0)) | spl4_1),
% 0.19/0.43    inference(resolution,[],[f49,f32])).
% 0.19/0.43  fof(f32,plain,(
% 0.19/0.43    ( ! [X0] : (m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) | v1_xboole_0(X0)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f21])).
% 0.19/0.43  fof(f180,plain,(
% 0.19/0.43    ~spl4_2 | spl4_5),
% 0.19/0.43    inference(avatar_contradiction_clause,[],[f179])).
% 0.19/0.43  fof(f179,plain,(
% 0.19/0.43    $false | (~spl4_2 | spl4_5)),
% 0.19/0.43    inference(subsumption_resolution,[],[f177,f110])).
% 0.19/0.43  fof(f110,plain,(
% 0.19/0.43    ~r1_tarski(k1_tarski(sK1),sK0) | spl4_5),
% 0.19/0.43    inference(resolution,[],[f84,f43])).
% 0.19/0.43  fof(f43,plain,(
% 0.19/0.43    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.19/0.43    inference(equality_resolution,[],[f29])).
% 0.19/0.43  fof(f29,plain,(
% 0.19/0.43    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.19/0.43    inference(cnf_transformation,[],[f19])).
% 0.19/0.43  fof(f19,plain,(
% 0.19/0.43    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.19/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).
% 0.19/0.43  fof(f18,plain,(
% 0.19/0.43    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 0.19/0.43    introduced(choice_axiom,[])).
% 0.19/0.43  fof(f17,plain,(
% 0.19/0.43    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.19/0.43    inference(rectify,[],[f16])).
% 0.19/0.43  fof(f16,plain,(
% 0.19/0.43    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.19/0.43    inference(nnf_transformation,[],[f3])).
% 0.19/0.43  fof(f3,axiom,(
% 0.19/0.43    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.19/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.19/0.43  fof(f84,plain,(
% 0.19/0.43    ~r2_hidden(k1_tarski(sK1),k1_zfmisc_1(sK0)) | spl4_5),
% 0.19/0.43    inference(avatar_component_clause,[],[f82])).
% 0.19/0.43  fof(f82,plain,(
% 0.19/0.43    spl4_5 <=> r2_hidden(k1_tarski(sK1),k1_zfmisc_1(sK0))),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.19/0.43  fof(f177,plain,(
% 0.19/0.43    r1_tarski(k1_tarski(sK1),sK0) | ~spl4_2),
% 0.19/0.43    inference(trivial_inequality_removal,[],[f176])).
% 0.19/0.43  fof(f176,plain,(
% 0.19/0.43    k1_xboole_0 != k1_xboole_0 | r1_tarski(k1_tarski(sK1),sK0) | ~spl4_2),
% 0.19/0.43    inference(superposition,[],[f36,f67])).
% 0.19/0.43  fof(f67,plain,(
% 0.19/0.43    k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),sK0) | ~spl4_2),
% 0.19/0.43    inference(resolution,[],[f54,f35])).
% 0.19/0.43  fof(f35,plain,(
% 0.19/0.43    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f22])).
% 0.19/0.43  fof(f22,plain,(
% 0.19/0.43    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)))),
% 0.19/0.43    inference(nnf_transformation,[],[f4])).
% 0.19/0.43  fof(f4,axiom,(
% 0.19/0.43    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.19/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).
% 0.19/0.43  fof(f54,plain,(
% 0.19/0.43    r2_hidden(sK1,sK0) | ~spl4_2),
% 0.19/0.43    inference(avatar_component_clause,[],[f52])).
% 0.19/0.43  fof(f52,plain,(
% 0.19/0.43    spl4_2 <=> r2_hidden(sK1,sK0)),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.19/0.43  fof(f36,plain,(
% 0.19/0.43    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f23])).
% 0.19/0.43  fof(f23,plain,(
% 0.19/0.43    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.19/0.43    inference(nnf_transformation,[],[f2])).
% 0.19/0.43  fof(f2,axiom,(
% 0.19/0.43    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.19/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.19/0.43  fof(f85,plain,(
% 0.19/0.43    spl4_4 | ~spl4_5),
% 0.19/0.43    inference(avatar_split_clause,[],[f73,f82,f78])).
% 0.19/0.43  fof(f73,plain,(
% 0.19/0.43    ~r2_hidden(k1_tarski(sK1),k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.19/0.43    inference(resolution,[],[f27,f40])).
% 0.19/0.43  fof(f40,plain,(
% 0.19/0.43    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f24])).
% 0.19/0.43  fof(f27,plain,(
% 0.19/0.43    ~m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))),
% 0.19/0.43    inference(cnf_transformation,[],[f15])).
% 0.19/0.43  fof(f55,plain,(
% 0.19/0.43    spl4_1 | spl4_2),
% 0.19/0.43    inference(avatar_split_clause,[],[f45,f52,f48])).
% 0.19/0.43  fof(f45,plain,(
% 0.19/0.43    r2_hidden(sK1,sK0) | v1_xboole_0(sK0)),
% 0.19/0.43    inference(resolution,[],[f25,f39])).
% 0.19/0.43  fof(f39,plain,(
% 0.19/0.43    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f24])).
% 0.19/0.43  fof(f25,plain,(
% 0.19/0.43    m1_subset_1(sK1,sK0)),
% 0.19/0.43    inference(cnf_transformation,[],[f15])).
% 0.19/0.43  % SZS output end Proof for theBenchmark
% 0.19/0.43  % (7905)------------------------------
% 0.19/0.43  % (7905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.43  % (7905)Termination reason: Refutation
% 0.19/0.43  
% 0.19/0.43  % (7905)Memory used [KB]: 6140
% 0.19/0.43  % (7905)Time elapsed: 0.031 s
% 0.19/0.43  % (7905)------------------------------
% 0.19/0.43  % (7905)------------------------------
% 0.19/0.43  % (7885)Success in time 0.086 s
%------------------------------------------------------------------------------
