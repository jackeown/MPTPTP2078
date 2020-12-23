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
% DateTime   : Thu Dec  3 12:44:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 124 expanded)
%              Number of leaves         :   19 (  55 expanded)
%              Depth                    :    7
%              Number of atoms          :  165 ( 339 expanded)
%              Number of equality atoms :   21 (  38 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f156,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f39,f44,f49,f66,f67,f84,f85,f103,f105,f119,f155])).

fof(f155,plain,
    ( ~ spl3_9
    | spl3_1
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f154,f101,f57,f36,f31,f88])).

fof(f88,plain,
    ( spl3_9
  <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f31,plain,
    ( spl3_1
  <=> r1_tarski(k3_subset_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f36,plain,
    ( spl3_2
  <=> r1_tarski(k3_subset_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f57,plain,
    ( spl3_5
  <=> sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f101,plain,
    ( spl3_12
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f154,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),sK1)
    | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f151,f59])).

fof(f59,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f151,plain,
    ( ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,k3_subset_1(sK0,sK1)))
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(resolution,[],[f102,f38])).

fof(f38,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f102,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,X0)) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f101])).

fof(f119,plain,
    ( spl3_11
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f118,f80,f97])).

fof(f97,plain,
    ( spl3_11
  <=> m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f80,plain,
    ( spl3_8
  <=> k3_subset_1(sK0,sK2) = k6_subset_1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f118,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_8 ),
    inference(superposition,[],[f22,f82])).

fof(f82,plain,
    ( k3_subset_1(sK0,sK2) = k6_subset_1(sK0,sK2)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f80])).

fof(f22,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f105,plain,
    ( spl3_9
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f104,f75,f88])).

fof(f75,plain,
    ( spl3_7
  <=> k3_subset_1(sK0,sK1) = k6_subset_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f104,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_7 ),
    inference(superposition,[],[f22,f77])).

fof(f77,plain,
    ( k3_subset_1(sK0,sK1) = k6_subset_1(sK0,sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f75])).

fof(f103,plain,
    ( ~ spl3_11
    | spl3_12
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f95,f62,f101,f97])).

fof(f62,plain,
    ( spl3_6
  <=> sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f95,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,X0))
        | ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) )
    | ~ spl3_6 ),
    inference(superposition,[],[f27,f64])).

fof(f64,plain,
    ( sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f62])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | r1_tarski(X2,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

% (7888)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

fof(f85,plain,
    ( spl3_7
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f72,f46,f75])).

fof(f46,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f72,plain,
    ( k3_subset_1(sK0,sK1) = k6_subset_1(sK0,sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f29,f48])).

fof(f48,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f25,f23])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f84,plain,
    ( spl3_8
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f71,f41,f80])).

fof(f41,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f71,plain,
    ( k3_subset_1(sK0,sK2) = k6_subset_1(sK0,sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f29,f43])).

fof(f43,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f67,plain,
    ( spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f54,f46,f57])).

fof(f54,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl3_4 ),
    inference(resolution,[],[f26,f48])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f66,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f53,f41,f62])).

fof(f53,plain,
    ( sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))
    | ~ spl3_3 ),
    inference(resolution,[],[f26,f43])).

fof(f49,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f18,f46])).

fof(f18,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),sK1)
    & r1_tarski(k3_subset_1(sK0,sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f16,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
            & r1_tarski(k3_subset_1(X0,X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(sK0,X2),sK1)
          & r1_tarski(k3_subset_1(sK0,sK1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

% (7889)Termination reason: Refutation not found, incomplete strategy

fof(f16,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k3_subset_1(sK0,X2),sK1)
        & r1_tarski(k3_subset_1(sK0,sK1),X2)
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ~ r1_tarski(k3_subset_1(sK0,sK2),sK1)
      & r1_tarski(k3_subset_1(sK0,sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

% (7889)Memory used [KB]: 10618
% (7889)Time elapsed: 0.052 s
% (7889)------------------------------
% (7889)------------------------------
fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
          & r1_tarski(k3_subset_1(X0,X1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
          & r1_tarski(k3_subset_1(X0,X1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(k3_subset_1(X0,X1),X2)
             => r1_tarski(k3_subset_1(X0,X2),X1) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(k3_subset_1(X0,X1),X2)
           => r1_tarski(k3_subset_1(X0,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_subset_1)).

fof(f44,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f19,f41])).

fof(f19,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f39,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f20,f36])).

fof(f20,plain,(
    r1_tarski(k3_subset_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f34,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f21,f31])).

fof(f21,plain,(
    ~ r1_tarski(k3_subset_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:06:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (7890)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (7884)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (7883)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (7889)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (7884)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (7882)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (7889)Refutation not found, incomplete strategy% (7889)------------------------------
% 0.21/0.47  % (7889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (7880)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (7881)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (7891)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f34,f39,f44,f49,f66,f67,f84,f85,f103,f105,f119,f155])).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    ~spl3_9 | spl3_1 | ~spl3_2 | ~spl3_5 | ~spl3_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f154,f101,f57,f36,f31,f88])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    spl3_9 <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    spl3_1 <=> r1_tarski(k3_subset_1(sK0,sK2),sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    spl3_2 <=> r1_tarski(k3_subset_1(sK0,sK1),sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    spl3_5 <=> sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    spl3_12 <=> ! [X0] : (~r1_tarski(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,X0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    r1_tarski(k3_subset_1(sK0,sK2),sK1) | ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | (~spl3_2 | ~spl3_5 | ~spl3_12)),
% 0.21/0.48    inference(forward_demodulation,[],[f151,f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | ~spl3_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f57])).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,k3_subset_1(sK0,sK1))) | (~spl3_2 | ~spl3_12)),
% 0.21/0.48    inference(resolution,[],[f102,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    r1_tarski(k3_subset_1(sK0,sK1),sK2) | ~spl3_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f36])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,X0))) ) | ~spl3_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f101])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    spl3_11 | ~spl3_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f118,f80,f97])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    spl3_11 <=> m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    spl3_8 <=> k3_subset_1(sK0,sK2) = k6_subset_1(sK0,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | ~spl3_8),
% 0.21/0.48    inference(superposition,[],[f22,f82])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    k3_subset_1(sK0,sK2) = k6_subset_1(sK0,sK2) | ~spl3_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f80])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    spl3_9 | ~spl3_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f104,f75,f88])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    spl3_7 <=> k3_subset_1(sK0,sK1) = k6_subset_1(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_7),
% 0.21/0.48    inference(superposition,[],[f22,f77])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    k3_subset_1(sK0,sK1) = k6_subset_1(sK0,sK1) | ~spl3_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f75])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    ~spl3_11 | spl3_12 | ~spl3_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f95,f62,f101,f97])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    spl3_6 <=> sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(X0,sK2) | r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,X0)) | ~m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) ) | ~spl3_6),
% 0.21/0.48    inference(superposition,[],[f27,f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) | ~spl3_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f62])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X1,k3_subset_1(X0,X2)) | r1_tarski(X2,k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  % (7888)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(flattening,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : ((r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    spl3_7 | ~spl3_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f72,f46,f75])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    k3_subset_1(sK0,sK1) = k6_subset_1(sK0,sK1) | ~spl3_4),
% 0.21/0.48    inference(resolution,[],[f29,f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f46])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f25,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    spl3_8 | ~spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f71,f41,f80])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    k3_subset_1(sK0,sK2) = k6_subset_1(sK0,sK2) | ~spl3_3),
% 0.21/0.48    inference(resolution,[],[f29,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl3_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f41])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    spl3_5 | ~spl3_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f54,f46,f57])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | ~spl3_4),
% 0.21/0.48    inference(resolution,[],[f26,f48])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    spl3_6 | ~spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f53,f41,f62])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) | ~spl3_3),
% 0.21/0.48    inference(resolution,[],[f26,f43])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    spl3_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f18,f46])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    (~r1_tarski(k3_subset_1(sK0,sK2),sK1) & r1_tarski(k3_subset_1(sK0,sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f16,f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,X2),X1) & r1_tarski(k3_subset_1(X0,X1),X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(k3_subset_1(sK0,X2),sK1) & r1_tarski(k3_subset_1(sK0,sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  % (7889)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ? [X2] : (~r1_tarski(k3_subset_1(sK0,X2),sK1) & r1_tarski(k3_subset_1(sK0,sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (~r1_tarski(k3_subset_1(sK0,sK2),sK1) & r1_tarski(k3_subset_1(sK0,sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  % (7889)Memory used [KB]: 10618
% 0.21/0.48  % (7889)Time elapsed: 0.052 s
% 0.21/0.48  % (7889)------------------------------
% 0.21/0.48  % (7889)------------------------------
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,X2),X1) & r1_tarski(k3_subset_1(X0,X1),X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(flattening,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),X1) & r1_tarski(k3_subset_1(X0,X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X2) => r1_tarski(k3_subset_1(X0,X2),X1))))),
% 0.21/0.48    inference(negated_conjecture,[],[f7])).
% 0.21/0.48  fof(f7,conjecture,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X2) => r1_tarski(k3_subset_1(X0,X2),X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_subset_1)).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f19,f41])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f20,f36])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    r1_tarski(k3_subset_1(sK0,sK1),sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ~spl3_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f21,f31])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ~r1_tarski(k3_subset_1(sK0,sK2),sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (7884)------------------------------
% 0.21/0.48  % (7884)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (7884)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (7884)Memory used [KB]: 6140
% 0.21/0.48  % (7884)Time elapsed: 0.054 s
% 0.21/0.48  % (7884)------------------------------
% 0.21/0.48  % (7884)------------------------------
% 0.21/0.48  % (7877)Success in time 0.121 s
%------------------------------------------------------------------------------
