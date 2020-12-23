%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 140 expanded)
%              Number of leaves         :   25 (  67 expanded)
%              Depth                    :    7
%              Number of atoms          :  252 ( 482 expanded)
%              Number of equality atoms :   18 (  26 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f170,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f43,f48,f58,f62,f66,f76,f80,f84,f101,f108,f127,f132,f159,f163,f168])).

fof(f168,plain,
    ( ~ spl3_6
    | spl3_21
    | ~ spl3_23 ),
    inference(avatar_contradiction_clause,[],[f167])).

fof(f167,plain,
    ( $false
    | ~ spl3_6
    | spl3_21
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f147,f165])).

fof(f165,plain,
    ( ! [X0] : v1_tops_2(k4_xboole_0(sK1,X0),sK0)
    | ~ spl3_6
    | ~ spl3_23 ),
    inference(unit_resulting_resolution,[],[f61,f162])).

fof(f162,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | v1_tops_2(X0,sK0) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl3_23
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | v1_tops_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f61,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl3_6
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

% (703)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% (712)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% (726)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% (718)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
fof(f147,plain,
    ( ~ v1_tops_2(k4_xboole_0(sK1,sK2),sK0)
    | spl3_21 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl3_21
  <=> v1_tops_2(k4_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f163,plain,
    ( ~ spl3_1
    | spl3_23
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_13
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f138,f130,f99,f64,f45,f40,f161,f35])).

fof(f35,plain,
    ( spl3_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f40,plain,
    ( spl3_2
  <=> v1_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f45,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f64,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f99,plain,
    ( spl3_13
  <=> ! [X1,X0,X2] :
        ( v1_tops_2(X1,X0)
        | ~ v1_tops_2(X2,X0)
        | ~ r1_tarski(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f130,plain,
    ( spl3_19
  <=> ! [X0] : m1_subset_1(k3_xboole_0(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f138,plain,
    ( ! [X0] :
        ( ~ v1_tops_2(sK1,sK0)
        | ~ r1_tarski(X0,sK1)
        | v1_tops_2(X0,sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_13
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f102,f137])).

fof(f137,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X0,sK1) )
    | ~ spl3_7
    | ~ spl3_19 ),
    inference(superposition,[],[f131,f65])).

fof(f65,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f64])).

fof(f131,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f130])).

fof(f102,plain,
    ( ! [X0] :
        ( ~ v1_tops_2(sK1,sK0)
        | ~ r1_tarski(X0,sK1)
        | v1_tops_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_3
    | ~ spl3_13 ),
    inference(resolution,[],[f100,f47])).

fof(f47,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f100,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ v1_tops_2(X2,X0)
        | ~ r1_tarski(X1,X2)
        | v1_tops_2(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f99])).

fof(f159,plain,
    ( ~ spl3_3
    | ~ spl3_21
    | spl3_5
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f97,f82,f55,f145,f45])).

fof(f55,plain,
    ( spl3_5
  <=> v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f82,plain,
    ( spl3_11
  <=> ! [X1,X0,X2] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f97,plain,
    ( ~ v1_tops_2(k4_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl3_5
    | ~ spl3_11 ),
    inference(superposition,[],[f57,f83])).

fof(f83,plain,
    ( ! [X2,X0,X1] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f82])).

fof(f57,plain,
    ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f55])).

fof(f132,plain,
    ( spl3_19
    | ~ spl3_14
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f128,f125,f106,f130])).

fof(f106,plain,
    ( spl3_14
  <=> ! [X0] : k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK1) = k3_xboole_0(X0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f125,plain,
    ( spl3_18
  <=> ! [X0] : m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f128,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_14
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f126,f107])).

fof(f107,plain,
    ( ! [X0] : k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK1) = k3_xboole_0(X0,sK1)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f106])).

fof(f126,plain,
    ( ! [X0] : m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f125])).

fof(f127,plain,
    ( spl3_18
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f89,f74,f45,f125])).

fof(f74,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f89,plain,
    ( ! [X0] : m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f47,f75])).

fof(f75,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f74])).

fof(f108,plain,
    ( spl3_14
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f91,f78,f45,f106])).

fof(f78,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] :
        ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f91,plain,
    ( ! [X0] : k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK1) = k3_xboole_0(X0,sK1)
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f47,f79])).

fof(f79,plain,
    ( ! [X2,X0,X1] :
        ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f78])).

fof(f101,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f27,f99])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ v1_tops_2(X2,X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(X1,X0)
              | ~ v1_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(X1,X0)
              | ~ v1_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v1_tops_2(X2,X0)
                  & r1_tarski(X1,X2) )
               => v1_tops_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tops_2)).

fof(f84,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f33,f82])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f80,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f32,f78])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f76,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f31,f74])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f66,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f30,f64])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f62,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f28,f60])).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f58,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f26,f55])).

fof(f26,plain,(
    ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    & v1_tops_2(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f20,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
                & v1_tops_2(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0)
              & v1_tops_2(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0)
            & v1_tops_2(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ? [X2] :
          ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0)
          & v1_tops_2(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X2] :
        ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0)
        & v1_tops_2(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
      & v1_tops_2(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( v1_tops_2(X1,X0)
                 => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( v1_tops_2(X1,X0)
               => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tops_2)).

fof(f48,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f23,f45])).

fof(f23,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f25,f40])).

fof(f25,plain,(
    v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f38,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f22,f35])).

fof(f22,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:24:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (713)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (711)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (725)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (721)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (724)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (720)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  % (723)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (711)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f38,f43,f48,f58,f62,f66,f76,f80,f84,f101,f108,f127,f132,f159,f163,f168])).
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    ~spl3_6 | spl3_21 | ~spl3_23),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f167])).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    $false | (~spl3_6 | spl3_21 | ~spl3_23)),
% 0.21/0.49    inference(subsumption_resolution,[],[f147,f165])).
% 0.21/0.49  fof(f165,plain,(
% 0.21/0.49    ( ! [X0] : (v1_tops_2(k4_xboole_0(sK1,X0),sK0)) ) | (~spl3_6 | ~spl3_23)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f61,f162])).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(X0,sK1) | v1_tops_2(X0,sK0)) ) | ~spl3_23),
% 0.21/0.49    inference(avatar_component_clause,[],[f161])).
% 0.21/0.49  fof(f161,plain,(
% 0.21/0.49    spl3_23 <=> ! [X0] : (~r1_tarski(X0,sK1) | v1_tops_2(X0,sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl3_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    spl3_6 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.49  % (703)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (712)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (726)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (718)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  fof(f147,plain,(
% 0.21/0.49    ~v1_tops_2(k4_xboole_0(sK1,sK2),sK0) | spl3_21),
% 0.21/0.49    inference(avatar_component_clause,[],[f145])).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    spl3_21 <=> v1_tops_2(k4_xboole_0(sK1,sK2),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    ~spl3_1 | spl3_23 | ~spl3_2 | ~spl3_3 | ~spl3_7 | ~spl3_13 | ~spl3_19),
% 0.21/0.49    inference(avatar_split_clause,[],[f138,f130,f99,f64,f45,f40,f161,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    spl3_1 <=> l1_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    spl3_2 <=> v1_tops_2(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    spl3_7 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    spl3_13 <=> ! [X1,X0,X2] : (v1_tops_2(X1,X0) | ~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    spl3_19 <=> ! [X0] : m1_subset_1(k3_xboole_0(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_tops_2(sK1,sK0) | ~r1_tarski(X0,sK1) | v1_tops_2(X0,sK0) | ~l1_pre_topc(sK0)) ) | (~spl3_3 | ~spl3_7 | ~spl3_13 | ~spl3_19)),
% 0.21/0.49    inference(subsumption_resolution,[],[f102,f137])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X0,sK1)) ) | (~spl3_7 | ~spl3_19)),
% 0.21/0.49    inference(superposition,[],[f131,f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | ~spl3_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f64])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(k3_xboole_0(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl3_19),
% 0.21/0.49    inference(avatar_component_clause,[],[f130])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_tops_2(sK1,sK0) | ~r1_tarski(X0,sK1) | v1_tops_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)) ) | (~spl3_3 | ~spl3_13)),
% 0.21/0.49    inference(resolution,[],[f100,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f45])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2) | v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) ) | ~spl3_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f99])).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    ~spl3_3 | ~spl3_21 | spl3_5 | ~spl3_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f97,f82,f55,f145,f45])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    spl3_5 <=> v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    spl3_11 <=> ! [X1,X0,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    ~v1_tops_2(k4_xboole_0(sK1,sK2),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (spl3_5 | ~spl3_11)),
% 0.21/0.49    inference(superposition,[],[f57,f83])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f82])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) | spl3_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f55])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    spl3_19 | ~spl3_14 | ~spl3_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f128,f125,f106,f130])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    spl3_14 <=> ! [X0] : k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK1) = k3_xboole_0(X0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    spl3_18 <=> ! [X0] : m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k3_xboole_0(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | (~spl3_14 | ~spl3_18)),
% 0.21/0.50    inference(forward_demodulation,[],[f126,f107])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    ( ! [X0] : (k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK1) = k3_xboole_0(X0,sK1)) ) | ~spl3_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f106])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl3_18),
% 0.21/0.50    inference(avatar_component_clause,[],[f125])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    spl3_18 | ~spl3_3 | ~spl3_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f89,f74,f45,f125])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    spl3_9 <=> ! [X1,X0,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | (~spl3_3 | ~spl3_9)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f47,f75])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) ) | ~spl3_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f74])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    spl3_14 | ~spl3_3 | ~spl3_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f91,f78,f45,f106])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    spl3_10 <=> ! [X1,X0,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    ( ! [X0] : (k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK1) = k3_xboole_0(X0,sK1)) ) | (~spl3_3 | ~spl3_10)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f47,f79])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) ) | ~spl3_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f78])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    spl3_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f27,f99])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v1_tops_2(X1,X0) | ~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (v1_tops_2(X1,X0) | ~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((v1_tops_2(X1,X0) | (~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_tops_2(X2,X0) & r1_tarski(X1,X2)) => v1_tops_2(X1,X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tops_2)).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    spl3_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f33,f82])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    spl3_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f32,f78])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    spl3_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f31,f74])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    spl3_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f30,f64])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    spl3_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f28,f60])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ~spl3_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f26,f55])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ((~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v1_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f20,f19,f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v1_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ? [X1] : (? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v1_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0) & v1_tops_2(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0) & v1_tops_2(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v1_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,negated_conjecture,(
% 0.21/0.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 0.21/0.50    inference(negated_conjecture,[],[f8])).
% 0.21/0.50  fof(f8,conjecture,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tops_2)).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    spl3_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f23,f45])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f25,f40])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    v1_tops_2(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    spl3_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f22,f35])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    l1_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (711)------------------------------
% 0.21/0.50  % (711)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (711)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (711)Memory used [KB]: 6140
% 0.21/0.50  % (711)Time elapsed: 0.056 s
% 0.21/0.50  % (711)------------------------------
% 0.21/0.50  % (711)------------------------------
% 0.21/0.50  % (702)Success in time 0.132 s
%------------------------------------------------------------------------------
