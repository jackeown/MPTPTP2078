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
% DateTime   : Thu Dec  3 12:45:31 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   63 (  88 expanded)
%              Number of leaves         :   16 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :  190 ( 272 expanded)
%              Number of equality atoms :   25 (  42 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f198,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f90,f126,f186,f197])).

fof(f197,plain,
    ( ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f196,f87,f83])).

fof(f83,plain,
    ( spl5_4
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f87,plain,
    ( spl5_5
  <=> r2_hidden(k2_enumset1(sK1,sK1,sK1,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f196,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl5_5 ),
    inference(resolution,[],[f88,f32])).

fof(f32,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f88,plain,
    ( r2_hidden(k2_enumset1(sK1,sK1,sK1,sK1),k1_zfmisc_1(sK0))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f186,plain,
    ( ~ spl5_2
    | spl5_5 ),
    inference(avatar_split_clause,[],[f185,f87,f66])).

fof(f66,plain,
    ( spl5_2
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f185,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl5_5 ),
    inference(duplicate_literal_removal,[],[f183])).

fof(f183,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ r2_hidden(sK1,sK0)
    | spl5_5 ),
    inference(resolution,[],[f112,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f45,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f112,plain,
    ( ~ r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | spl5_5 ),
    inference(resolution,[],[f89,f51])).

fof(f51,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f89,plain,
    ( ~ r2_hidden(k2_enumset1(sK1,sK1,sK1,sK1),k1_zfmisc_1(sK0))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f126,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f79,f62])).

fof(f62,plain,
    ( spl5_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f79,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(resolution,[],[f54,f55])).

fof(f55,plain,(
    ! [X0] :
      ( sQ4_eqProxy(k1_xboole_0,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f31,f53])).

fof(f53,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f54,plain,(
    ~ sQ4_eqProxy(k1_xboole_0,sK0) ),
    inference(equality_proxy_replacement,[],[f28,f53])).

fof(f28,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
    & k1_xboole_0 != sK0
    & m1_subset_1(sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
        & k1_xboole_0 != X0
        & m1_subset_1(X1,X0) )
   => ( ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
      & k1_xboole_0 != sK0
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      & k1_xboole_0 != X0
      & m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      & k1_xboole_0 != X0
      & m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,X0)
       => ( k1_xboole_0 != X0
         => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ( k1_xboole_0 != X0
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

fof(f90,plain,
    ( spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f80,f87,f83])).

fof(f80,plain,
    ( ~ r2_hidden(k2_enumset1(sK1,sK1,sK1,sK1),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f47,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f47,plain,(
    ~ m1_subset_1(k2_enumset1(sK1,sK1,sK1,sK1),k1_zfmisc_1(sK0)) ),
    inference(definition_unfolding,[],[f29,f46])).

fof(f46,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f30,f34])).

fof(f30,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f29,plain,(
    ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f15])).

% (7814)Termination reason: Refutation not found, incomplete strategy

% (7814)Memory used [KB]: 10618
% (7814)Time elapsed: 0.077 s
% (7814)------------------------------
% (7814)------------------------------
fof(f69,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f59,f66,f62])).

fof(f59,plain,
    ( r2_hidden(sK1,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f27,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f27,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.11/0.32  % Computer   : n016.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 11:00:34 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.19/0.43  % (7830)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.43  % (7821)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.43  % (7814)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.44  % (7814)Refutation not found, incomplete strategy% (7814)------------------------------
% 0.19/0.44  % (7814)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.44  % (7821)Refutation found. Thanks to Tanya!
% 0.19/0.44  % SZS status Theorem for theBenchmark
% 0.19/0.44  % SZS output start Proof for theBenchmark
% 0.19/0.44  fof(f198,plain,(
% 0.19/0.44    $false),
% 0.19/0.44    inference(avatar_sat_refutation,[],[f69,f90,f126,f186,f197])).
% 0.19/0.44  fof(f197,plain,(
% 0.19/0.44    ~spl5_4 | ~spl5_5),
% 0.19/0.44    inference(avatar_split_clause,[],[f196,f87,f83])).
% 0.19/0.44  fof(f83,plain,(
% 0.19/0.44    spl5_4 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.19/0.44  fof(f87,plain,(
% 0.19/0.44    spl5_5 <=> r2_hidden(k2_enumset1(sK1,sK1,sK1,sK1),k1_zfmisc_1(sK0))),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.19/0.44  fof(f196,plain,(
% 0.19/0.44    ~v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl5_5),
% 0.19/0.44    inference(resolution,[],[f88,f32])).
% 0.19/0.44  fof(f32,plain,(
% 0.19/0.44    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f19])).
% 0.19/0.44  fof(f19,plain,(
% 0.19/0.44    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.19/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).
% 0.19/0.44  fof(f18,plain,(
% 0.19/0.44    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.19/0.44    introduced(choice_axiom,[])).
% 0.19/0.44  fof(f17,plain,(
% 0.19/0.44    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.19/0.44    inference(rectify,[],[f16])).
% 0.19/0.44  fof(f16,plain,(
% 0.19/0.44    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.19/0.44    inference(nnf_transformation,[],[f1])).
% 0.19/0.44  fof(f1,axiom,(
% 0.19/0.44    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.19/0.44  fof(f88,plain,(
% 0.19/0.44    r2_hidden(k2_enumset1(sK1,sK1,sK1,sK1),k1_zfmisc_1(sK0)) | ~spl5_5),
% 0.19/0.44    inference(avatar_component_clause,[],[f87])).
% 0.19/0.44  fof(f186,plain,(
% 0.19/0.44    ~spl5_2 | spl5_5),
% 0.19/0.44    inference(avatar_split_clause,[],[f185,f87,f66])).
% 0.19/0.44  fof(f66,plain,(
% 0.19/0.44    spl5_2 <=> r2_hidden(sK1,sK0)),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.19/0.44  fof(f185,plain,(
% 0.19/0.44    ~r2_hidden(sK1,sK0) | spl5_5),
% 0.19/0.44    inference(duplicate_literal_removal,[],[f183])).
% 0.19/0.44  fof(f183,plain,(
% 0.19/0.44    ~r2_hidden(sK1,sK0) | ~r2_hidden(sK1,sK0) | spl5_5),
% 0.19/0.44    inference(resolution,[],[f112,f48])).
% 0.19/0.44  fof(f48,plain,(
% 0.19/0.44    ( ! [X2,X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.19/0.44    inference(definition_unfolding,[],[f45,f34])).
% 0.19/0.44  fof(f34,plain,(
% 0.19/0.44    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f4])).
% 0.19/0.44  fof(f4,axiom,(
% 0.19/0.44    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).
% 0.19/0.44  fof(f45,plain,(
% 0.19/0.44    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f26])).
% 0.19/0.44  fof(f26,plain,(
% 0.19/0.44    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.19/0.44    inference(flattening,[],[f25])).
% 0.19/0.44  fof(f25,plain,(
% 0.19/0.44    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.19/0.44    inference(nnf_transformation,[],[f6])).
% 0.19/0.44  fof(f6,axiom,(
% 0.19/0.44    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.19/0.44  fof(f112,plain,(
% 0.19/0.44    ~r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | spl5_5),
% 0.19/0.44    inference(resolution,[],[f89,f51])).
% 0.19/0.44  fof(f51,plain,(
% 0.19/0.44    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.19/0.44    inference(equality_resolution,[],[f40])).
% 0.19/0.44  fof(f40,plain,(
% 0.19/0.44    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.19/0.44    inference(cnf_transformation,[],[f24])).
% 0.19/0.44  fof(f24,plain,(
% 0.19/0.44    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.19/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f23])).
% 0.19/0.44  fof(f23,plain,(
% 0.19/0.44    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.19/0.44    introduced(choice_axiom,[])).
% 0.19/0.44  fof(f22,plain,(
% 0.19/0.44    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.19/0.44    inference(rectify,[],[f21])).
% 0.19/0.44  fof(f21,plain,(
% 0.19/0.44    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.19/0.44    inference(nnf_transformation,[],[f5])).
% 0.19/0.44  fof(f5,axiom,(
% 0.19/0.44    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.19/0.44  fof(f89,plain,(
% 0.19/0.44    ~r2_hidden(k2_enumset1(sK1,sK1,sK1,sK1),k1_zfmisc_1(sK0)) | spl5_5),
% 0.19/0.44    inference(avatar_component_clause,[],[f87])).
% 0.19/0.44  fof(f126,plain,(
% 0.19/0.44    ~spl5_1),
% 0.19/0.44    inference(avatar_split_clause,[],[f79,f62])).
% 0.19/0.44  fof(f62,plain,(
% 0.19/0.44    spl5_1 <=> v1_xboole_0(sK0)),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.19/0.44  fof(f79,plain,(
% 0.19/0.44    ~v1_xboole_0(sK0)),
% 0.19/0.44    inference(resolution,[],[f54,f55])).
% 0.19/0.44  fof(f55,plain,(
% 0.19/0.44    ( ! [X0] : (sQ4_eqProxy(k1_xboole_0,X0) | ~v1_xboole_0(X0)) )),
% 0.19/0.44    inference(equality_proxy_replacement,[],[f31,f53])).
% 0.19/0.44  fof(f53,plain,(
% 0.19/0.44    ! [X1,X0] : (sQ4_eqProxy(X0,X1) <=> X0 = X1)),
% 0.19/0.44    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).
% 0.19/0.44  fof(f31,plain,(
% 0.19/0.44    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f12])).
% 0.19/0.44  fof(f12,plain,(
% 0.19/0.44    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.19/0.44    inference(ennf_transformation,[],[f2])).
% 0.19/0.44  fof(f2,axiom,(
% 0.19/0.44    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.19/0.44  fof(f54,plain,(
% 0.19/0.44    ~sQ4_eqProxy(k1_xboole_0,sK0)),
% 0.19/0.44    inference(equality_proxy_replacement,[],[f28,f53])).
% 0.19/0.44  fof(f28,plain,(
% 0.19/0.44    k1_xboole_0 != sK0),
% 0.19/0.44    inference(cnf_transformation,[],[f15])).
% 0.19/0.44  fof(f15,plain,(
% 0.19/0.44    ~m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) & k1_xboole_0 != sK0 & m1_subset_1(sK1,sK0)),
% 0.19/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f14])).
% 0.19/0.44  fof(f14,plain,(
% 0.19/0.44    ? [X0,X1] : (~m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X1,X0)) => (~m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) & k1_xboole_0 != sK0 & m1_subset_1(sK1,sK0))),
% 0.19/0.44    introduced(choice_axiom,[])).
% 0.19/0.44  fof(f11,plain,(
% 0.19/0.44    ? [X0,X1] : (~m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X1,X0))),
% 0.19/0.44    inference(flattening,[],[f10])).
% 0.19/0.44  fof(f10,plain,(
% 0.19/0.44    ? [X0,X1] : ((~m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) & k1_xboole_0 != X0) & m1_subset_1(X1,X0))),
% 0.19/0.44    inference(ennf_transformation,[],[f9])).
% 0.19/0.44  fof(f9,negated_conjecture,(
% 0.19/0.44    ~! [X0,X1] : (m1_subset_1(X1,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))))),
% 0.19/0.44    inference(negated_conjecture,[],[f8])).
% 0.19/0.44  fof(f8,conjecture,(
% 0.19/0.44    ! [X0,X1] : (m1_subset_1(X1,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).
% 0.19/0.44  fof(f90,plain,(
% 0.19/0.44    spl5_4 | ~spl5_5),
% 0.19/0.44    inference(avatar_split_clause,[],[f80,f87,f83])).
% 0.19/0.44  fof(f80,plain,(
% 0.19/0.44    ~r2_hidden(k2_enumset1(sK1,sK1,sK1,sK1),k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.19/0.44    inference(resolution,[],[f47,f36])).
% 0.19/0.44  fof(f36,plain,(
% 0.19/0.44    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f20])).
% 0.19/0.44  fof(f20,plain,(
% 0.19/0.44    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.19/0.44    inference(nnf_transformation,[],[f13])).
% 0.19/0.44  fof(f13,plain,(
% 0.19/0.44    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.19/0.44    inference(ennf_transformation,[],[f7])).
% 0.19/0.44  fof(f7,axiom,(
% 0.19/0.44    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.19/0.44  fof(f47,plain,(
% 0.19/0.44    ~m1_subset_1(k2_enumset1(sK1,sK1,sK1,sK1),k1_zfmisc_1(sK0))),
% 0.19/0.44    inference(definition_unfolding,[],[f29,f46])).
% 0.19/0.44  fof(f46,plain,(
% 0.19/0.44    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.19/0.44    inference(definition_unfolding,[],[f30,f34])).
% 0.19/0.44  fof(f30,plain,(
% 0.19/0.44    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f3])).
% 0.19/0.44  fof(f3,axiom,(
% 0.19/0.44    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.19/0.44  fof(f29,plain,(
% 0.19/0.44    ~m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))),
% 0.19/0.44    inference(cnf_transformation,[],[f15])).
% 0.19/0.44  % (7814)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.44  
% 0.19/0.44  % (7814)Memory used [KB]: 10618
% 0.19/0.44  % (7814)Time elapsed: 0.077 s
% 0.19/0.44  % (7814)------------------------------
% 0.19/0.44  % (7814)------------------------------
% 0.19/0.44  fof(f69,plain,(
% 0.19/0.44    spl5_1 | spl5_2),
% 0.19/0.44    inference(avatar_split_clause,[],[f59,f66,f62])).
% 0.19/0.44  fof(f59,plain,(
% 0.19/0.44    r2_hidden(sK1,sK0) | v1_xboole_0(sK0)),
% 0.19/0.44    inference(resolution,[],[f27,f35])).
% 0.19/0.44  fof(f35,plain,(
% 0.19/0.44    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f20])).
% 0.19/0.44  fof(f27,plain,(
% 0.19/0.44    m1_subset_1(sK1,sK0)),
% 0.19/0.44    inference(cnf_transformation,[],[f15])).
% 0.19/0.44  % SZS output end Proof for theBenchmark
% 0.19/0.44  % (7821)------------------------------
% 0.19/0.44  % (7821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.44  % (7821)Termination reason: Refutation
% 0.19/0.44  
% 0.19/0.44  % (7821)Memory used [KB]: 6268
% 0.19/0.44  % (7821)Time elapsed: 0.058 s
% 0.19/0.44  % (7821)------------------------------
% 0.19/0.44  % (7821)------------------------------
% 0.19/0.44  % (7803)Success in time 0.108 s
%------------------------------------------------------------------------------
