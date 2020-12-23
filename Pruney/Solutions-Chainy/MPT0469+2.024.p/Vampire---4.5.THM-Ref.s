%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 106 expanded)
%              Number of leaves         :   22 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :  174 ( 284 expanded)
%              Number of equality atoms :   48 (  82 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f112,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f59,f64,f69,f82,f89,f95,f111])).

fof(f111,plain,
    ( spl6_2
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f109,f87,f53])).

fof(f53,plain,
    ( spl6_2
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f87,plain,
    ( spl6_7
  <=> ! [X3] : ~ r2_hidden(X3,k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f109,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl6_7 ),
    inference(resolution,[],[f88,f34])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f17])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f88,plain,
    ( ! [X3] : ~ r2_hidden(X3,k2_relat_1(k1_xboole_0))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f87])).

fof(f95,plain,
    ( ~ spl6_5
    | spl6_6 ),
    inference(avatar_split_clause,[],[f93,f84,f67])).

fof(f67,plain,
    ( spl6_5
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f84,plain,
    ( spl6_6
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f93,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_6 ),
    inference(resolution,[],[f85,f32])).

fof(f32,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f85,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f84])).

fof(f89,plain,
    ( ~ spl6_6
    | spl6_7 ),
    inference(avatar_split_clause,[],[f80,f87,f84])).

fof(f80,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f76,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f19])).

fof(f19,plain,(
    ! [X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
     => r2_hidden(sK1(X1),k1_relat_1(X1)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).

fof(f76,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f46,f71])).

fof(f71,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f35,f47])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f35,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f46,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f25,f24,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f82,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f79,f50])).

fof(f50,plain,
    ( spl6_1
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f79,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f76,f34])).

fof(f69,plain,
    ( spl6_5
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f65,f62,f57,f67])).

fof(f57,plain,
    ( spl6_3
  <=> v1_xboole_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f62,plain,
    ( spl6_4
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f65,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(superposition,[],[f58,f63])).

fof(f63,plain,
    ( k1_xboole_0 = sK5
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f58,plain,
    ( v1_xboole_0(sK5)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f64,plain,
    ( spl6_4
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f60,f57,f62])).

fof(f60,plain,
    ( k1_xboole_0 = sK5
    | ~ spl6_3 ),
    inference(resolution,[],[f33,f58])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f59,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f44,f57])).

fof(f44,plain,(
    v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    v1_xboole_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f2,f29])).

fof(f29,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK5) ),
    introduced(choice_axiom,[])).

fof(f2,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f55,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f31,f53,f50])).

fof(f31,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.33  % Computer   : n003.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 14:07:42 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.20/0.42  % (15788)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.42  % (15780)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.43  % (15780)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f112,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f55,f59,f64,f69,f82,f89,f95,f111])).
% 0.20/0.43  fof(f111,plain,(
% 0.20/0.43    spl6_2 | ~spl6_7),
% 0.20/0.43    inference(avatar_split_clause,[],[f109,f87,f53])).
% 0.20/0.43  fof(f53,plain,(
% 0.20/0.43    spl6_2 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.43  fof(f87,plain,(
% 0.20/0.43    spl6_7 <=> ! [X3] : ~r2_hidden(X3,k2_relat_1(k1_xboole_0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.43  fof(f109,plain,(
% 0.20/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl6_7),
% 0.20/0.43    inference(resolution,[],[f88,f34])).
% 0.20/0.43  fof(f34,plain,(
% 0.20/0.43    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f18])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f17])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.43    inference(ennf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.43  fof(f88,plain,(
% 0.20/0.43    ( ! [X3] : (~r2_hidden(X3,k2_relat_1(k1_xboole_0))) ) | ~spl6_7),
% 0.20/0.43    inference(avatar_component_clause,[],[f87])).
% 0.20/0.43  fof(f95,plain,(
% 0.20/0.43    ~spl6_5 | spl6_6),
% 0.20/0.43    inference(avatar_split_clause,[],[f93,f84,f67])).
% 0.20/0.43  fof(f67,plain,(
% 0.20/0.43    spl6_5 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.43  fof(f84,plain,(
% 0.20/0.43    spl6_6 <=> v1_relat_1(k1_xboole_0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.43  fof(f93,plain,(
% 0.20/0.43    ~v1_xboole_0(k1_xboole_0) | spl6_6),
% 0.20/0.43    inference(resolution,[],[f85,f32])).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f12])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,axiom,(
% 0.20/0.43    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.20/0.43  fof(f85,plain,(
% 0.20/0.43    ~v1_relat_1(k1_xboole_0) | spl6_6),
% 0.20/0.43    inference(avatar_component_clause,[],[f84])).
% 0.20/0.43  fof(f89,plain,(
% 0.20/0.43    ~spl6_6 | spl6_7),
% 0.20/0.43    inference(avatar_split_clause,[],[f80,f87,f84])).
% 0.20/0.43  fof(f80,plain,(
% 0.20/0.43    ( ! [X3] : (~r2_hidden(X3,k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) )),
% 0.20/0.43    inference(resolution,[],[f76,f36])).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r2_hidden(sK1(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f20])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    ! [X0,X1] : (r2_hidden(sK1(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f19])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ! [X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(sK1(X1),k1_relat_1(X1)))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ! [X0,X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(flattening,[],[f15])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,axiom,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k1_relat_1(X1)) & r2_hidden(X0,k2_relat_1(X1))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).
% 0.20/0.43  fof(f76,plain,(
% 0.20/0.43    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0))) )),
% 0.20/0.43    inference(resolution,[],[f46,f71])).
% 0.20/0.43  fof(f71,plain,(
% 0.20/0.43    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.43    inference(superposition,[],[f35,f47])).
% 0.20/0.43  fof(f47,plain,(
% 0.20/0.43    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.43    inference(equality_resolution,[],[f43])).
% 0.20/0.43  fof(f43,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.20/0.43    inference(cnf_transformation,[],[f28])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.43    inference(flattening,[],[f27])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.43    inference(nnf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.20/0.43  fof(f46,plain,(
% 0.20/0.43    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 0.20/0.43    inference(equality_resolution,[],[f37])).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 0.20/0.43    inference(cnf_transformation,[],[f26])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f25,f24,f23])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.20/0.43    inference(rectify,[],[f21])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.20/0.43    inference(nnf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,axiom,(
% 0.20/0.43    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.20/0.43  fof(f82,plain,(
% 0.20/0.43    spl6_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f79,f50])).
% 0.20/0.43  fof(f50,plain,(
% 0.20/0.43    spl6_1 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.43  fof(f79,plain,(
% 0.20/0.43    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.43    inference(resolution,[],[f76,f34])).
% 0.20/0.43  fof(f69,plain,(
% 0.20/0.43    spl6_5 | ~spl6_3 | ~spl6_4),
% 0.20/0.43    inference(avatar_split_clause,[],[f65,f62,f57,f67])).
% 0.20/0.43  fof(f57,plain,(
% 0.20/0.43    spl6_3 <=> v1_xboole_0(sK5)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.43  fof(f62,plain,(
% 0.20/0.43    spl6_4 <=> k1_xboole_0 = sK5),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.43  fof(f65,plain,(
% 0.20/0.43    v1_xboole_0(k1_xboole_0) | (~spl6_3 | ~spl6_4)),
% 0.20/0.43    inference(superposition,[],[f58,f63])).
% 0.20/0.43  fof(f63,plain,(
% 0.20/0.43    k1_xboole_0 = sK5 | ~spl6_4),
% 0.20/0.43    inference(avatar_component_clause,[],[f62])).
% 0.20/0.43  fof(f58,plain,(
% 0.20/0.43    v1_xboole_0(sK5) | ~spl6_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f57])).
% 0.20/0.43  fof(f64,plain,(
% 0.20/0.43    spl6_4 | ~spl6_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f60,f57,f62])).
% 0.20/0.43  fof(f60,plain,(
% 0.20/0.43    k1_xboole_0 = sK5 | ~spl6_3),
% 0.20/0.43    inference(resolution,[],[f33,f58])).
% 0.20/0.43  fof(f33,plain,(
% 0.20/0.43    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f13])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.43  fof(f59,plain,(
% 0.20/0.43    spl6_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f44,f57])).
% 0.20/0.43  fof(f44,plain,(
% 0.20/0.43    v1_xboole_0(sK5)),
% 0.20/0.43    inference(cnf_transformation,[],[f30])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    v1_xboole_0(sK5)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f2,f29])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK5)),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ? [X0] : v1_xboole_0(X0)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).
% 0.20/0.43  fof(f55,plain,(
% 0.20/0.43    ~spl6_1 | ~spl6_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f31,f53,f50])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.20/0.43    inference(cnf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.20/0.43    inference(ennf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,negated_conjecture,(
% 0.20/0.43    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 0.20/0.43    inference(negated_conjecture,[],[f9])).
% 0.20/0.43  fof(f9,conjecture,(
% 0.20/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (15780)------------------------------
% 0.20/0.43  % (15780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (15780)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (15780)Memory used [KB]: 10618
% 0.20/0.43  % (15780)Time elapsed: 0.008 s
% 0.20/0.43  % (15780)------------------------------
% 0.20/0.43  % (15780)------------------------------
% 0.20/0.44  % (15771)Success in time 0.089 s
%------------------------------------------------------------------------------
