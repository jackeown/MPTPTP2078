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
% DateTime   : Thu Dec  3 13:11:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 122 expanded)
%              Number of leaves         :   24 (  57 expanded)
%              Depth                    :    6
%              Number of atoms          :  223 ( 325 expanded)
%              Number of equality atoms :   31 (  46 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f131,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f41,f46,f50,f54,f58,f66,f74,f79,f85,f91,f103,f113,f116,f128,f130])).

fof(f130,plain,
    ( ~ spl2_3
    | ~ spl2_19 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_19 ),
    inference(resolution,[],[f127,f45])).

fof(f45,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl2_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f127,plain,
    ( ! [X1] : ~ v1_xboole_0(X1)
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl2_19
  <=> ! [X1] : ~ v1_xboole_0(X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f128,plain,
    ( spl2_19
    | ~ spl2_4
    | ~ spl2_10
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f124,f106,f72,f48,f126])).

fof(f48,plain,
    ( spl2_4
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f72,plain,
    ( spl2_10
  <=> ! [X1,X0,X2] :
        ( ~ v1_xboole_0(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f106,plain,
    ( spl2_16
  <=> r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f124,plain,
    ( ! [X1] : ~ v1_xboole_0(X1)
    | ~ spl2_4
    | ~ spl2_10
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f118,f49])).

fof(f49,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f118,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
        | ~ v1_xboole_0(X1) )
    | ~ spl2_10
    | ~ spl2_16 ),
    inference(resolution,[],[f108,f73])).

fof(f73,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ v1_xboole_0(X2) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f72])).

fof(f108,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f106])).

fof(f116,plain,
    ( spl2_1
    | ~ spl2_13
    | ~ spl2_17 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | spl2_1
    | ~ spl2_13
    | ~ spl2_17 ),
    inference(subsumption_resolution,[],[f114,f90])).

fof(f90,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl2_13
  <=> k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f114,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,k1_xboole_0)
    | spl2_1
    | ~ spl2_17 ),
    inference(superposition,[],[f35,f112])).

fof(f112,plain,
    ( k1_xboole_0 = k1_struct_0(sK0)
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl2_17
  <=> k1_xboole_0 = k1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f35,plain,
    ( k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl2_1
  <=> k1_struct_0(sK0) = k1_tops_1(sK0,k1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f113,plain,
    ( spl2_16
    | spl2_17
    | ~ spl2_4
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f104,f101,f48,f110,f106])).

fof(f101,plain,
    ( spl2_15
  <=> ! [X0] :
        ( k1_struct_0(sK0) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK1(sK0,X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f104,plain,
    ( k1_xboole_0 = k1_struct_0(sK0)
    | r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl2_4
    | ~ spl2_15 ),
    inference(resolution,[],[f102,f49])).

fof(f102,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_struct_0(sK0) = X0
        | r2_hidden(sK1(sK0,X0),X0) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f101])).

fof(f103,plain,
    ( spl2_15
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f99,f56,f38,f101])).

fof(f38,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f56,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( r2_hidden(sK1(X0,X1),X1)
        | k1_struct_0(X0) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f99,plain,
    ( ! [X0] :
        ( k1_struct_0(sK0) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK1(sK0,X0),X0) )
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(resolution,[],[f57,f40])).

fof(f40,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f57,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | k1_struct_0(X0) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | r2_hidden(sK1(X0,X1),X1) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f56])).

fof(f91,plain,
    ( spl2_13
    | ~ spl2_8
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f86,f82,f64,f88])).

fof(f64,plain,
    ( spl2_8
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f82,plain,
    ( spl2_12
  <=> r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f86,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)
    | ~ spl2_8
    | ~ spl2_12 ),
    inference(resolution,[],[f84,f65])).

fof(f65,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f64])).

fof(f84,plain,
    ( r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f82])).

fof(f85,plain,
    ( spl2_12
    | ~ spl2_4
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f80,f77,f48,f82])).

fof(f77,plain,
    ( spl2_11
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k1_tops_1(sK0,X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f80,plain,
    ( r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl2_4
    | ~ spl2_11 ),
    inference(resolution,[],[f78,f49])).

fof(f78,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k1_tops_1(sK0,X0),X0) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f77])).

fof(f79,plain,
    ( spl2_11
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f75,f52,f38,f77])).

fof(f52,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( r1_tarski(k1_tops_1(X0,X1),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f75,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k1_tops_1(sK0,X0),X0) )
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(resolution,[],[f53,f40])).

fof(f53,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | r1_tarski(k1_tops_1(X0,X1),X1) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f74,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f31,f72])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f66,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f29,f64])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f58,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f28,f56])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | k1_struct_0(X0) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(sK1(X0,X1),X1)
            & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) )
          | k1_struct_0(X0) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | k1_struct_0(X0) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | k1_struct_0(X0) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ r2_hidden(X2,X1) )
              & k1_struct_0(X0) != X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_pre_topc)).

fof(f54,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f26,f52])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f50,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f25,f48])).

fof(f25,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f46,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f24,f43])).

fof(f24,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f41,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f22,f38])).

fof(f22,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( k1_struct_0(X0) != k1_tops_1(X0,k1_struct_0(X0))
        & l1_pre_topc(X0) )
   => ( k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0))
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( k1_struct_0(X0) != k1_tops_1(X0,k1_struct_0(X0))
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tops_1)).

fof(f36,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f23,f33])).

fof(f23,plain,(
    k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n003.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 19:15:57 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.41  % (17224)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.42  % (17225)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.42  % (17224)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f131,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f36,f41,f46,f50,f54,f58,f66,f74,f79,f85,f91,f103,f113,f116,f128,f130])).
% 0.21/0.42  fof(f130,plain,(
% 0.21/0.42    ~spl2_3 | ~spl2_19),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f129])).
% 0.21/0.42  fof(f129,plain,(
% 0.21/0.42    $false | (~spl2_3 | ~spl2_19)),
% 0.21/0.42    inference(resolution,[],[f127,f45])).
% 0.21/0.42  fof(f45,plain,(
% 0.21/0.42    v1_xboole_0(k1_xboole_0) | ~spl2_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f43])).
% 0.21/0.42  fof(f43,plain,(
% 0.21/0.42    spl2_3 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.42  fof(f127,plain,(
% 0.21/0.42    ( ! [X1] : (~v1_xboole_0(X1)) ) | ~spl2_19),
% 0.21/0.42    inference(avatar_component_clause,[],[f126])).
% 0.21/0.42  fof(f126,plain,(
% 0.21/0.42    spl2_19 <=> ! [X1] : ~v1_xboole_0(X1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.21/0.42  fof(f128,plain,(
% 0.21/0.42    spl2_19 | ~spl2_4 | ~spl2_10 | ~spl2_16),
% 0.21/0.42    inference(avatar_split_clause,[],[f124,f106,f72,f48,f126])).
% 0.21/0.42  fof(f48,plain,(
% 0.21/0.42    spl2_4 <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.42  fof(f72,plain,(
% 0.21/0.42    spl2_10 <=> ! [X1,X0,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.42  fof(f106,plain,(
% 0.21/0.42    spl2_16 <=> r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.42  fof(f124,plain,(
% 0.21/0.42    ( ! [X1] : (~v1_xboole_0(X1)) ) | (~spl2_4 | ~spl2_10 | ~spl2_16)),
% 0.21/0.42    inference(subsumption_resolution,[],[f118,f49])).
% 0.21/0.42  fof(f49,plain,(
% 0.21/0.42    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl2_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f48])).
% 0.21/0.42  fof(f118,plain,(
% 0.21/0.42    ( ! [X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) | ~v1_xboole_0(X1)) ) | (~spl2_10 | ~spl2_16)),
% 0.21/0.42    inference(resolution,[],[f108,f73])).
% 0.21/0.42  fof(f73,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) ) | ~spl2_10),
% 0.21/0.42    inference(avatar_component_clause,[],[f72])).
% 0.21/0.42  fof(f108,plain,(
% 0.21/0.42    r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0) | ~spl2_16),
% 0.21/0.42    inference(avatar_component_clause,[],[f106])).
% 0.21/0.42  fof(f116,plain,(
% 0.21/0.42    spl2_1 | ~spl2_13 | ~spl2_17),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f115])).
% 0.21/0.42  fof(f115,plain,(
% 0.21/0.42    $false | (spl2_1 | ~spl2_13 | ~spl2_17)),
% 0.21/0.42    inference(subsumption_resolution,[],[f114,f90])).
% 0.21/0.42  fof(f90,plain,(
% 0.21/0.42    k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) | ~spl2_13),
% 0.21/0.42    inference(avatar_component_clause,[],[f88])).
% 0.21/0.42  fof(f88,plain,(
% 0.21/0.42    spl2_13 <=> k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.42  fof(f114,plain,(
% 0.21/0.42    k1_xboole_0 != k1_tops_1(sK0,k1_xboole_0) | (spl2_1 | ~spl2_17)),
% 0.21/0.42    inference(superposition,[],[f35,f112])).
% 0.21/0.42  fof(f112,plain,(
% 0.21/0.42    k1_xboole_0 = k1_struct_0(sK0) | ~spl2_17),
% 0.21/0.42    inference(avatar_component_clause,[],[f110])).
% 0.21/0.42  fof(f110,plain,(
% 0.21/0.42    spl2_17 <=> k1_xboole_0 = k1_struct_0(sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0)) | spl2_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f33])).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    spl2_1 <=> k1_struct_0(sK0) = k1_tops_1(sK0,k1_struct_0(sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.42  fof(f113,plain,(
% 0.21/0.42    spl2_16 | spl2_17 | ~spl2_4 | ~spl2_15),
% 0.21/0.42    inference(avatar_split_clause,[],[f104,f101,f48,f110,f106])).
% 0.21/0.42  fof(f101,plain,(
% 0.21/0.42    spl2_15 <=> ! [X0] : (k1_struct_0(sK0) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1(sK0,X0),X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.42  fof(f104,plain,(
% 0.21/0.42    k1_xboole_0 = k1_struct_0(sK0) | r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0) | (~spl2_4 | ~spl2_15)),
% 0.21/0.42    inference(resolution,[],[f102,f49])).
% 0.21/0.42  fof(f102,plain,(
% 0.21/0.42    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_struct_0(sK0) = X0 | r2_hidden(sK1(sK0,X0),X0)) ) | ~spl2_15),
% 0.21/0.42    inference(avatar_component_clause,[],[f101])).
% 0.21/0.42  fof(f103,plain,(
% 0.21/0.42    spl2_15 | ~spl2_2 | ~spl2_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f99,f56,f38,f101])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    spl2_2 <=> l1_pre_topc(sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.42  fof(f56,plain,(
% 0.21/0.42    spl2_6 <=> ! [X1,X0] : (r2_hidden(sK1(X0,X1),X1) | k1_struct_0(X0) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.42  fof(f99,plain,(
% 0.21/0.42    ( ! [X0] : (k1_struct_0(sK0) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1(sK0,X0),X0)) ) | (~spl2_2 | ~spl2_6)),
% 0.21/0.42    inference(resolution,[],[f57,f40])).
% 0.21/0.42  fof(f40,plain,(
% 0.21/0.42    l1_pre_topc(sK0) | ~spl2_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f38])).
% 0.21/0.42  fof(f57,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~l1_pre_topc(X0) | k1_struct_0(X0) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(sK1(X0,X1),X1)) ) | ~spl2_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f56])).
% 0.21/0.42  fof(f91,plain,(
% 0.21/0.42    spl2_13 | ~spl2_8 | ~spl2_12),
% 0.21/0.42    inference(avatar_split_clause,[],[f86,f82,f64,f88])).
% 0.21/0.42  fof(f64,plain,(
% 0.21/0.42    spl2_8 <=> ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.42  fof(f82,plain,(
% 0.21/0.42    spl2_12 <=> r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.42  fof(f86,plain,(
% 0.21/0.42    k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) | (~spl2_8 | ~spl2_12)),
% 0.21/0.42    inference(resolution,[],[f84,f65])).
% 0.21/0.42  fof(f65,plain,(
% 0.21/0.42    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl2_8),
% 0.21/0.42    inference(avatar_component_clause,[],[f64])).
% 0.21/0.42  fof(f84,plain,(
% 0.21/0.42    r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0) | ~spl2_12),
% 0.21/0.42    inference(avatar_component_clause,[],[f82])).
% 0.21/0.42  fof(f85,plain,(
% 0.21/0.42    spl2_12 | ~spl2_4 | ~spl2_11),
% 0.21/0.42    inference(avatar_split_clause,[],[f80,f77,f48,f82])).
% 0.21/0.42  fof(f77,plain,(
% 0.21/0.42    spl2_11 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.42  fof(f80,plain,(
% 0.21/0.42    r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0) | (~spl2_4 | ~spl2_11)),
% 0.21/0.42    inference(resolution,[],[f78,f49])).
% 0.21/0.42  fof(f78,plain,(
% 0.21/0.42    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),X0)) ) | ~spl2_11),
% 0.21/0.42    inference(avatar_component_clause,[],[f77])).
% 0.21/0.42  fof(f79,plain,(
% 0.21/0.42    spl2_11 | ~spl2_2 | ~spl2_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f75,f52,f38,f77])).
% 0.21/0.42  fof(f52,plain,(
% 0.21/0.42    spl2_5 <=> ! [X1,X0] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.42  fof(f75,plain,(
% 0.21/0.42    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),X0)) ) | (~spl2_2 | ~spl2_5)),
% 0.21/0.42    inference(resolution,[],[f53,f40])).
% 0.21/0.42  fof(f53,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) ) | ~spl2_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f52])).
% 0.21/0.42  fof(f74,plain,(
% 0.21/0.42    spl2_10),
% 0.21/0.42    inference(avatar_split_clause,[],[f31,f72])).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f17])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.42  fof(f66,plain,(
% 0.21/0.42    spl2_8),
% 0.21/0.42    inference(avatar_split_clause,[],[f29,f64])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    spl2_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f28,f56])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | k1_struct_0(X0) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f21])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : ((r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))) | k1_struct_0(X0) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f20])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ! [X1,X0] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | k1_struct_0(X0) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.42    inference(flattening,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : ((? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | k1_struct_0(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,axiom,(
% 0.21/0.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~r2_hidden(X2,X1)) & k1_struct_0(X0) != X1)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_pre_topc)).
% 0.21/0.42  fof(f54,plain,(
% 0.21/0.42    spl2_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f26,f52])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,axiom,(
% 0.21/0.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 0.21/0.42  fof(f50,plain,(
% 0.21/0.42    spl2_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f25,f48])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    spl2_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f24,f43])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    v1_xboole_0(k1_xboole_0)),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    v1_xboole_0(k1_xboole_0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.42  fof(f41,plain,(
% 0.21/0.42    spl2_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f22,f38])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    l1_pre_topc(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f19])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0)) & l1_pre_topc(sK0)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f18])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ? [X0] : (k1_struct_0(X0) != k1_tops_1(X0,k1_struct_0(X0)) & l1_pre_topc(X0)) => (k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0)) & l1_pre_topc(sK0))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ? [X0] : (k1_struct_0(X0) != k1_tops_1(X0,k1_struct_0(X0)) & l1_pre_topc(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,negated_conjecture,(
% 0.21/0.42    ~! [X0] : (l1_pre_topc(X0) => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)))),
% 0.21/0.42    inference(negated_conjecture,[],[f8])).
% 0.21/0.42  fof(f8,conjecture,(
% 0.21/0.42    ! [X0] : (l1_pre_topc(X0) => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tops_1)).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    ~spl2_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f23,f33])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0))),
% 0.21/0.42    inference(cnf_transformation,[],[f19])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (17224)------------------------------
% 0.21/0.42  % (17224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (17224)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (17224)Memory used [KB]: 10618
% 0.21/0.42  % (17224)Time elapsed: 0.007 s
% 0.21/0.42  % (17224)------------------------------
% 0.21/0.42  % (17224)------------------------------
% 0.21/0.42  % (17218)Success in time 0.064 s
%------------------------------------------------------------------------------
