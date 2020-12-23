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
% DateTime   : Thu Dec  3 13:12:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 260 expanded)
%              Number of leaves         :   27 (  90 expanded)
%              Depth                    :   12
%              Number of atoms          :  415 ( 792 expanded)
%              Number of equality atoms :   51 ( 105 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f411,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f83,f99,f104,f109,f114,f138,f153,f174,f186,f194,f278,f330,f352,f373,f386,f410])).

fof(f410,plain,
    ( spl3_5
    | ~ spl3_20
    | ~ spl3_30 ),
    inference(avatar_contradiction_clause,[],[f409])).

fof(f409,plain,
    ( $false
    | spl3_5
    | ~ spl3_20
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f408,f108])).

fof(f108,plain,
    ( k1_xboole_0 != sK1
    | spl3_5 ),
    inference(avatar_component_clause,[],[f106])).

% (30535)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f106,plain,
    ( spl3_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f408,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_20
    | ~ spl3_30 ),
    inference(backward_demodulation,[],[f277,f407])).

fof(f407,plain,
    ( k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f399,f50])).

% (30537)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (30536)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f50,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f399,plain,
    ( k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_30 ),
    inference(superposition,[],[f62,f351])).

fof(f351,plain,
    ( k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f349])).

fof(f349,plain,
    ( spl3_30
  <=> k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f277,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f275])).

fof(f275,plain,
    ( spl3_20
  <=> sK1 = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f386,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | spl3_32 ),
    inference(avatar_contradiction_clause,[],[f385])).

fof(f385,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | spl3_32 ),
    inference(subsumption_resolution,[],[f384,f50])).

fof(f384,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_1
    | ~ spl3_2
    | spl3_32 ),
    inference(subsumption_resolution,[],[f383,f48])).

fof(f48,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f383,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_1
    | ~ spl3_2
    | spl3_32 ),
    inference(resolution,[],[f372,f88])).

fof(f88,plain,
    ( ! [X1] :
        ( v3_pre_topc(X1,sK0)
        | ~ v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f85,f82])).

fof(f82,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl3_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f85,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(X1)
        | v3_pre_topc(X1,sK0) )
    | ~ spl3_1 ),
    inference(resolution,[],[f77,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).

fof(f77,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl3_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f372,plain,
    ( ~ v3_pre_topc(k1_xboole_0,sK0)
    | spl3_32 ),
    inference(avatar_component_clause,[],[f370])).

fof(f370,plain,
    ( spl3_32
  <=> v3_pre_topc(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f373,plain,
    ( ~ spl3_32
    | spl3_29 ),
    inference(avatar_split_clause,[],[f363,f345,f370])).

% (30512)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f345,plain,
    ( spl3_29
  <=> v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_xboole_0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f363,plain,
    ( ~ v3_pre_topc(k1_xboole_0,sK0)
    | spl3_29 ),
    inference(subsumption_resolution,[],[f361,f50])).

fof(f361,plain,
    ( ~ v3_pre_topc(k1_xboole_0,sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_29 ),
    inference(superposition,[],[f347,f62])).

fof(f347,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_xboole_0)),sK0)
    | spl3_29 ),
    inference(avatar_component_clause,[],[f345])).

fof(f352,plain,
    ( ~ spl3_29
    | spl3_30
    | ~ spl3_2
    | ~ spl3_8
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f331,f322,f150,f80,f349,f345])).

fof(f150,plain,
    ( spl3_8
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f322,plain,
    ( spl3_27
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f331,plain,
    ( k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_xboole_0)),sK0)
    | ~ spl3_2
    | ~ spl3_8
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f156,f323])).

fof(f323,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f322])).

fof(f156,plain,
    ( k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_xboole_0)),sK0)
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(superposition,[],[f152,f118])).

fof(f118,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,X0) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) )
    | ~ spl3_2 ),
    inference(duplicate_literal_removal,[],[f117])).

fof(f117,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0 )
    | ~ spl3_2 ),
    inference(resolution,[],[f90,f94])).

fof(f94,plain,
    ( ! [X4] :
        ( ~ v4_pre_topc(X4,sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X4) = X4 )
    | ~ spl3_2 ),
    inference(resolution,[],[f82,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f90,plain,
    ( ! [X0] :
        ( v4_pre_topc(X0,sK0)
        | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_2 ),
    inference(resolution,[],[f82,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

fof(f152,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f150])).

fof(f330,plain,(
    spl3_27 ),
    inference(avatar_contradiction_clause,[],[f329])).

fof(f329,plain,
    ( $false
    | spl3_27 ),
    inference(subsumption_resolution,[],[f326,f50])).

fof(f326,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_27 ),
    inference(resolution,[],[f324,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f324,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_27 ),
    inference(avatar_component_clause,[],[f322])).

fof(f278,plain,
    ( spl3_20
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f229,f183,f111,f275])).

fof(f111,plain,
    ( spl3_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f183,plain,
    ( spl3_12
  <=> k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f229,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f222,f113])).

fof(f113,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f111])).

fof(f222,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_12 ),
    inference(superposition,[],[f62,f185])).

fof(f185,plain,
    ( k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f183])).

fof(f194,plain,
    ( ~ spl3_3
    | ~ spl3_6
    | spl3_11 ),
    inference(avatar_contradiction_clause,[],[f193])).

fof(f193,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_6
    | spl3_11 ),
    inference(subsumption_resolution,[],[f192,f113])).

fof(f192,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3
    | spl3_11 ),
    inference(subsumption_resolution,[],[f190,f98])).

fof(f98,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl3_3
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f190,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_11 ),
    inference(superposition,[],[f181,f62])).

fof(f181,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl3_11
  <=> v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f186,plain,
    ( ~ spl3_11
    | spl3_12
    | ~ spl3_2
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f175,f166,f135,f80,f183,f179])).

fof(f135,plain,
    ( spl3_7
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f166,plain,
    ( spl3_10
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f175,plain,
    ( k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),sK1)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ spl3_2
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f139,f167])).

fof(f167,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f166])).

fof(f139,plain,
    ( k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),sK1)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(superposition,[],[f137,f118])).

% (30510)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f137,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f135])).

fof(f174,plain,
    ( ~ spl3_6
    | spl3_10 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | ~ spl3_6
    | spl3_10 ),
    inference(subsumption_resolution,[],[f170,f113])).

fof(f170,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_10 ),
    inference(resolution,[],[f168,f61])).

fof(f168,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f166])).

fof(f153,plain,
    ( spl3_8
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f145,f80,f75,f150])).

fof(f145,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f144,f50])).

fof(f144,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(resolution,[],[f132,f48])).

fof(f132,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))
        | ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(resolution,[],[f123,f87])).

fof(f87,plain,
    ( ! [X0] :
        ( v3_tops_1(X0,sK0)
        | ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f84,f82])).

fof(f84,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(X0)
        | v3_tops_1(X0,sK0) )
    | ~ spl3_1 ),
    inference(resolution,[],[f77,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | v3_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

% (30510)Refutation not found, incomplete strategy% (30510)------------------------------
% (30510)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (30510)Termination reason: Refutation not found, incomplete strategy

% (30510)Memory used [KB]: 1663
% (30510)Time elapsed: 0.132 s
% (30510)------------------------------
% (30510)------------------------------
fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v3_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_tops_1)).

fof(f123,plain,
    ( ! [X0] :
        ( ~ v3_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) )
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f121,f61])).

fof(f121,plain,
    ( ! [X0] :
        ( ~ v3_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_2 ),
    inference(resolution,[],[f93,f92])).

fof(f92,plain,
    ( ! [X2] :
        ( ~ v1_tops_1(X2,sK0)
        | k2_pre_topc(sK0,X2) = k2_struct_0(sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_2 ),
    inference(resolution,[],[f82,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k2_struct_0(X0)
      | ~ v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

fof(f93,plain,
    ( ! [X3] :
        ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),X3),sK0)
        | ~ v3_tops_1(X3,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_2 ),
    inference(resolution,[],[f82,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tops_1(X1,X0)
      | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

% (30519)Refutation not found, incomplete strategy% (30519)------------------------------
% (30519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (30519)Termination reason: Refutation not found, incomplete strategy

% (30519)Memory used [KB]: 10618
% (30519)Time elapsed: 0.036 s
% (30519)------------------------------
% (30519)------------------------------
fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_tops_1)).

% (30511)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f138,plain,
    ( spl3_7
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f133,f111,f101,f80,f135])).

fof(f101,plain,
    ( spl3_4
  <=> v3_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f133,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f130,f113])).

fof(f130,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(resolution,[],[f123,f103])).

fof(f103,plain,
    ( v3_tops_1(sK1,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f101])).

fof(f114,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f42,f111])).

% (30518)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f42,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v3_tops_1(X1,X0)
                & v3_pre_topc(X1,X0) )
             => k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tops_1(X1,X0)
              & v3_pre_topc(X1,X0) )
           => k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_tops_1)).

fof(f109,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f45,f106])).

fof(f45,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f22])).

fof(f104,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f44,f101])).

fof(f44,plain,(
    v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f99,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f43,f96])).

fof(f43,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f83,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f47,f80])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f78,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f46,f75])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n003.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:11:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (30539)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.52  % (30531)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.52  % (30515)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (30531)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (30533)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (30519)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (30513)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f411,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f78,f83,f99,f104,f109,f114,f138,f153,f174,f186,f194,f278,f330,f352,f373,f386,f410])).
% 0.22/0.54  fof(f410,plain,(
% 0.22/0.54    spl3_5 | ~spl3_20 | ~spl3_30),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f409])).
% 0.22/0.54  fof(f409,plain,(
% 0.22/0.54    $false | (spl3_5 | ~spl3_20 | ~spl3_30)),
% 0.22/0.54    inference(subsumption_resolution,[],[f408,f108])).
% 0.22/0.54  fof(f108,plain,(
% 0.22/0.54    k1_xboole_0 != sK1 | spl3_5),
% 0.22/0.54    inference(avatar_component_clause,[],[f106])).
% 0.22/0.54  % (30535)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  fof(f106,plain,(
% 0.22/0.54    spl3_5 <=> k1_xboole_0 = sK1),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.54  fof(f408,plain,(
% 0.22/0.54    k1_xboole_0 = sK1 | (~spl3_20 | ~spl3_30)),
% 0.22/0.54    inference(backward_demodulation,[],[f277,f407])).
% 0.22/0.54  fof(f407,plain,(
% 0.22/0.54    k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)) | ~spl3_30),
% 0.22/0.54    inference(subsumption_resolution,[],[f399,f50])).
% 0.22/0.54  % (30537)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (30536)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.54  fof(f399,plain,(
% 0.22/0.54    k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_30),
% 0.22/0.54    inference(superposition,[],[f62,f351])).
% 0.22/0.54  fof(f351,plain,(
% 0.22/0.54    k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) | ~spl3_30),
% 0.22/0.54    inference(avatar_component_clause,[],[f349])).
% 0.22/0.54  fof(f349,plain,(
% 0.22/0.54    spl3_30 <=> k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.22/0.54  fof(f277,plain,(
% 0.22/0.54    sK1 = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)) | ~spl3_20),
% 0.22/0.54    inference(avatar_component_clause,[],[f275])).
% 0.22/0.54  fof(f275,plain,(
% 0.22/0.54    spl3_20 <=> sK1 = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.54  fof(f386,plain,(
% 0.22/0.54    ~spl3_1 | ~spl3_2 | spl3_32),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f385])).
% 0.22/0.54  fof(f385,plain,(
% 0.22/0.54    $false | (~spl3_1 | ~spl3_2 | spl3_32)),
% 0.22/0.54    inference(subsumption_resolution,[],[f384,f50])).
% 0.22/0.54  fof(f384,plain,(
% 0.22/0.54    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_1 | ~spl3_2 | spl3_32)),
% 0.22/0.54    inference(subsumption_resolution,[],[f383,f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    v1_xboole_0(k1_xboole_0)),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    v1_xboole_0(k1_xboole_0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.54  fof(f383,plain,(
% 0.22/0.54    ~v1_xboole_0(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_1 | ~spl3_2 | spl3_32)),
% 0.22/0.54    inference(resolution,[],[f372,f88])).
% 0.22/0.54  fof(f88,plain,(
% 0.22/0.54    ( ! [X1] : (v3_pre_topc(X1,sK0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_1 | ~spl3_2)),
% 0.22/0.54    inference(subsumption_resolution,[],[f85,f82])).
% 0.22/0.54  fof(f82,plain,(
% 0.22/0.54    l1_pre_topc(sK0) | ~spl3_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f80])).
% 0.22/0.54  fof(f80,plain,(
% 0.22/0.54    spl3_2 <=> l1_pre_topc(sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    ( ! [X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_xboole_0(X1) | v3_pre_topc(X1,sK0)) ) | ~spl3_1),
% 0.22/0.54    inference(resolution,[],[f77,f59])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | v3_pre_topc(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (v3_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,axiom,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v3_pre_topc(X1,X0))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).
% 0.22/0.54  fof(f77,plain,(
% 0.22/0.54    v2_pre_topc(sK0) | ~spl3_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f75])).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    spl3_1 <=> v2_pre_topc(sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.54  fof(f372,plain,(
% 0.22/0.54    ~v3_pre_topc(k1_xboole_0,sK0) | spl3_32),
% 0.22/0.54    inference(avatar_component_clause,[],[f370])).
% 0.22/0.54  fof(f370,plain,(
% 0.22/0.54    spl3_32 <=> v3_pre_topc(k1_xboole_0,sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.22/0.54  fof(f373,plain,(
% 0.22/0.54    ~spl3_32 | spl3_29),
% 0.22/0.54    inference(avatar_split_clause,[],[f363,f345,f370])).
% 0.22/0.54  % (30512)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  fof(f345,plain,(
% 0.22/0.54    spl3_29 <=> v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_xboole_0)),sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.22/0.54  fof(f363,plain,(
% 0.22/0.54    ~v3_pre_topc(k1_xboole_0,sK0) | spl3_29),
% 0.22/0.54    inference(subsumption_resolution,[],[f361,f50])).
% 0.22/0.54  fof(f361,plain,(
% 0.22/0.54    ~v3_pre_topc(k1_xboole_0,sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_29),
% 0.22/0.54    inference(superposition,[],[f347,f62])).
% 0.22/0.54  fof(f347,plain,(
% 0.22/0.54    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_xboole_0)),sK0) | spl3_29),
% 0.22/0.54    inference(avatar_component_clause,[],[f345])).
% 0.22/0.54  fof(f352,plain,(
% 0.22/0.54    ~spl3_29 | spl3_30 | ~spl3_2 | ~spl3_8 | ~spl3_27),
% 0.22/0.54    inference(avatar_split_clause,[],[f331,f322,f150,f80,f349,f345])).
% 0.22/0.54  fof(f150,plain,(
% 0.22/0.54    spl3_8 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.54  fof(f322,plain,(
% 0.22/0.54    spl3_27 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.22/0.54  fof(f331,plain,(
% 0.22/0.54    k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_xboole_0)),sK0) | (~spl3_2 | ~spl3_8 | ~spl3_27)),
% 0.22/0.54    inference(subsumption_resolution,[],[f156,f323])).
% 0.22/0.54  fof(f323,plain,(
% 0.22/0.54    m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_27),
% 0.22/0.54    inference(avatar_component_clause,[],[f322])).
% 0.22/0.54  fof(f156,plain,(
% 0.22/0.54    k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_xboole_0)),sK0) | (~spl3_2 | ~spl3_8)),
% 0.22/0.54    inference(superposition,[],[f152,f118])).
% 0.22/0.54  fof(f118,plain,(
% 0.22/0.54    ( ! [X0] : (k2_pre_topc(sK0,X0) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)) ) | ~spl3_2),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f117])).
% 0.22/0.54  fof(f117,plain,(
% 0.22/0.54    ( ! [X0] : (~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0) ) | ~spl3_2),
% 0.22/0.54    inference(resolution,[],[f90,f94])).
% 0.22/0.54  fof(f94,plain,(
% 0.22/0.54    ( ! [X4] : (~v4_pre_topc(X4,sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X4) = X4) ) | ~spl3_2),
% 0.22/0.54    inference(resolution,[],[f82,f53])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.22/0.54  fof(f90,plain,(
% 0.22/0.54    ( ! [X0] : (v4_pre_topc(X0,sK0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_2),
% 0.22/0.54    inference(resolution,[],[f82,f57])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).
% 0.22/0.54  fof(f152,plain,(
% 0.22/0.54    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)) | ~spl3_8),
% 0.22/0.54    inference(avatar_component_clause,[],[f150])).
% 0.22/0.54  fof(f330,plain,(
% 0.22/0.54    spl3_27),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f329])).
% 0.22/0.54  fof(f329,plain,(
% 0.22/0.54    $false | spl3_27),
% 0.22/0.54    inference(subsumption_resolution,[],[f326,f50])).
% 0.22/0.54  fof(f326,plain,(
% 0.22/0.54    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_27),
% 0.22/0.54    inference(resolution,[],[f324,f61])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.22/0.54  fof(f324,plain,(
% 0.22/0.54    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_27),
% 0.22/0.54    inference(avatar_component_clause,[],[f322])).
% 0.22/0.54  fof(f278,plain,(
% 0.22/0.54    spl3_20 | ~spl3_6 | ~spl3_12),
% 0.22/0.54    inference(avatar_split_clause,[],[f229,f183,f111,f275])).
% 0.22/0.54  fof(f111,plain,(
% 0.22/0.54    spl3_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.54  fof(f183,plain,(
% 0.22/0.54    spl3_12 <=> k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.54  fof(f229,plain,(
% 0.22/0.54    sK1 = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)) | (~spl3_6 | ~spl3_12)),
% 0.22/0.54    inference(subsumption_resolution,[],[f222,f113])).
% 0.22/0.54  fof(f113,plain,(
% 0.22/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_6),
% 0.22/0.54    inference(avatar_component_clause,[],[f111])).
% 0.22/0.54  fof(f222,plain,(
% 0.22/0.54    sK1 = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_12),
% 0.22/0.54    inference(superposition,[],[f62,f185])).
% 0.22/0.54  fof(f185,plain,(
% 0.22/0.54    k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),sK1) | ~spl3_12),
% 0.22/0.54    inference(avatar_component_clause,[],[f183])).
% 0.22/0.54  fof(f194,plain,(
% 0.22/0.54    ~spl3_3 | ~spl3_6 | spl3_11),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f193])).
% 0.22/0.54  fof(f193,plain,(
% 0.22/0.54    $false | (~spl3_3 | ~spl3_6 | spl3_11)),
% 0.22/0.54    inference(subsumption_resolution,[],[f192,f113])).
% 0.22/0.54  fof(f192,plain,(
% 0.22/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_3 | spl3_11)),
% 0.22/0.54    inference(subsumption_resolution,[],[f190,f98])).
% 0.22/0.54  fof(f98,plain,(
% 0.22/0.54    v3_pre_topc(sK1,sK0) | ~spl3_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f96])).
% 0.22/0.54  fof(f96,plain,(
% 0.22/0.54    spl3_3 <=> v3_pre_topc(sK1,sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.54  fof(f190,plain,(
% 0.22/0.54    ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_11),
% 0.22/0.54    inference(superposition,[],[f181,f62])).
% 0.22/0.54  fof(f181,plain,(
% 0.22/0.54    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0) | spl3_11),
% 0.22/0.54    inference(avatar_component_clause,[],[f179])).
% 0.22/0.54  fof(f179,plain,(
% 0.22/0.54    spl3_11 <=> v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.54  fof(f186,plain,(
% 0.22/0.54    ~spl3_11 | spl3_12 | ~spl3_2 | ~spl3_7 | ~spl3_10),
% 0.22/0.54    inference(avatar_split_clause,[],[f175,f166,f135,f80,f183,f179])).
% 0.22/0.54  fof(f135,plain,(
% 0.22/0.54    spl3_7 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.54  fof(f166,plain,(
% 0.22/0.54    spl3_10 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.54  fof(f175,plain,(
% 0.22/0.54    k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),sK1) | ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0) | (~spl3_2 | ~spl3_7 | ~spl3_10)),
% 0.22/0.54    inference(subsumption_resolution,[],[f139,f167])).
% 0.22/0.54  fof(f167,plain,(
% 0.22/0.54    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_10),
% 0.22/0.54    inference(avatar_component_clause,[],[f166])).
% 0.22/0.54  fof(f139,plain,(
% 0.22/0.54    k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),sK1) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0) | (~spl3_2 | ~spl3_7)),
% 0.22/0.54    inference(superposition,[],[f137,f118])).
% 0.22/0.54  % (30510)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  fof(f137,plain,(
% 0.22/0.54    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl3_7),
% 0.22/0.54    inference(avatar_component_clause,[],[f135])).
% 0.22/0.54  fof(f174,plain,(
% 0.22/0.54    ~spl3_6 | spl3_10),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f173])).
% 0.22/0.54  fof(f173,plain,(
% 0.22/0.54    $false | (~spl3_6 | spl3_10)),
% 0.22/0.54    inference(subsumption_resolution,[],[f170,f113])).
% 0.22/0.54  fof(f170,plain,(
% 0.22/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_10),
% 0.22/0.54    inference(resolution,[],[f168,f61])).
% 0.22/0.54  fof(f168,plain,(
% 0.22/0.54    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_10),
% 0.22/0.54    inference(avatar_component_clause,[],[f166])).
% 0.22/0.54  fof(f153,plain,(
% 0.22/0.54    spl3_8 | ~spl3_1 | ~spl3_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f145,f80,f75,f150])).
% 0.22/0.54  fof(f145,plain,(
% 0.22/0.54    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)) | (~spl3_1 | ~spl3_2)),
% 0.22/0.54    inference(subsumption_resolution,[],[f144,f50])).
% 0.22/0.54  fof(f144,plain,(
% 0.22/0.54    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_1 | ~spl3_2)),
% 0.22/0.54    inference(resolution,[],[f132,f48])).
% 0.22/0.54  fof(f132,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_xboole_0(X0) | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_1 | ~spl3_2)),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f131])).
% 0.22/0.54  fof(f131,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) | ~v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_1 | ~spl3_2)),
% 0.22/0.54    inference(resolution,[],[f123,f87])).
% 0.22/0.54  fof(f87,plain,(
% 0.22/0.54    ( ! [X0] : (v3_tops_1(X0,sK0) | ~v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_1 | ~spl3_2)),
% 0.22/0.54    inference(subsumption_resolution,[],[f84,f82])).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_xboole_0(X0) | v3_tops_1(X0,sK0)) ) | ~spl3_1),
% 0.22/0.54    inference(resolution,[],[f77,f60])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | v3_tops_1(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f32])).
% 0.22/0.54  % (30510)Refutation not found, incomplete strategy% (30510)------------------------------
% 0.22/0.54  % (30510)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (30510)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (30510)Memory used [KB]: 1663
% 0.22/0.54  % (30510)Time elapsed: 0.132 s
% 0.22/0.54  % (30510)------------------------------
% 0.22/0.54  % (30510)------------------------------
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (v3_tops_1(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,axiom,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v3_tops_1(X1,X0))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_tops_1)).
% 0.22/0.54  fof(f123,plain,(
% 0.22/0.54    ( ! [X0] : (~v3_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) ) | ~spl3_2),
% 0.22/0.54    inference(subsumption_resolution,[],[f121,f61])).
% 0.22/0.54  fof(f121,plain,(
% 0.22/0.54    ( ! [X0] : (~v3_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_2),
% 0.22/0.54    inference(resolution,[],[f93,f92])).
% 0.22/0.54  fof(f92,plain,(
% 0.22/0.54    ( ! [X2] : (~v1_tops_1(X2,sK0) | k2_pre_topc(sK0,X2) = k2_struct_0(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_2),
% 0.22/0.54    inference(resolution,[],[f82,f56])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).
% 0.22/0.54  fof(f93,plain,(
% 0.22/0.54    ( ! [X3] : (v1_tops_1(k3_subset_1(u1_struct_0(sK0),X3),sK0) | ~v3_tops_1(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_2),
% 0.22/0.54    inference(resolution,[],[f82,f54])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tops_1(X1,X0) | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  % (30519)Refutation not found, incomplete strategy% (30519)------------------------------
% 0.22/0.54  % (30519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (30519)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (30519)Memory used [KB]: 10618
% 0.22/0.54  % (30519)Time elapsed: 0.036 s
% 0.22/0.54  % (30519)------------------------------
% 0.22/0.54  % (30519)------------------------------
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_tops_1)).
% 0.22/0.54  % (30511)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  fof(f138,plain,(
% 0.22/0.54    spl3_7 | ~spl3_2 | ~spl3_4 | ~spl3_6),
% 0.22/0.54    inference(avatar_split_clause,[],[f133,f111,f101,f80,f135])).
% 0.22/0.54  fof(f101,plain,(
% 0.22/0.54    spl3_4 <=> v3_tops_1(sK1,sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.54  fof(f133,plain,(
% 0.22/0.54    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl3_2 | ~spl3_4 | ~spl3_6)),
% 0.22/0.54    inference(subsumption_resolution,[],[f130,f113])).
% 0.22/0.54  fof(f130,plain,(
% 0.22/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl3_2 | ~spl3_4)),
% 0.22/0.54    inference(resolution,[],[f123,f103])).
% 0.22/0.54  fof(f103,plain,(
% 0.22/0.54    v3_tops_1(sK1,sK0) | ~spl3_4),
% 0.22/0.54    inference(avatar_component_clause,[],[f101])).
% 0.22/0.54  fof(f114,plain,(
% 0.22/0.54    spl3_6),
% 0.22/0.54    inference(avatar_split_clause,[],[f42,f111])).
% 0.22/0.54  % (30518)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : ((k1_xboole_0 != X1 & (v3_tops_1(X1,X0) & v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,negated_conjecture,(
% 0.22/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tops_1(X1,X0) & v3_pre_topc(X1,X0)) => k1_xboole_0 = X1)))),
% 0.22/0.54    inference(negated_conjecture,[],[f19])).
% 0.22/0.54  fof(f19,conjecture,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tops_1(X1,X0) & v3_pre_topc(X1,X0)) => k1_xboole_0 = X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_tops_1)).
% 0.22/0.54  fof(f109,plain,(
% 0.22/0.54    ~spl3_5),
% 0.22/0.54    inference(avatar_split_clause,[],[f45,f106])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    k1_xboole_0 != sK1),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f104,plain,(
% 0.22/0.54    spl3_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f44,f101])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    v3_tops_1(sK1,sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f99,plain,(
% 0.22/0.54    spl3_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f43,f96])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    v3_pre_topc(sK1,sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f83,plain,(
% 0.22/0.54    spl3_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f47,f80])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    l1_pre_topc(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    spl3_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f46,f75])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    v2_pre_topc(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (30517)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (30531)------------------------------
% 0.22/0.54  % (30531)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (30531)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (30531)Memory used [KB]: 11001
% 0.22/0.54  % (30531)Time elapsed: 0.126 s
% 0.22/0.54  % (30531)------------------------------
% 0.22/0.54  % (30531)------------------------------
% 0.22/0.55  % (30508)Success in time 0.185 s
%------------------------------------------------------------------------------
