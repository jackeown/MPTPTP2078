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
% DateTime   : Thu Dec  3 13:21:37 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  180 (10311 expanded)
%              Number of leaves         :   22 (2719 expanded)
%              Depth                    :   48
%              Number of atoms          :  707 (78915 expanded)
%              Number of equality atoms :   84 (1710 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f317,plain,(
    $false ),
    inference(subsumption_resolution,[],[f316,f299])).

fof(f299,plain,(
    l1_struct_0(sK2(sK0,sK1)) ),
    inference(resolution,[],[f282,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

% (26044)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f282,plain,(
    l1_pre_topc(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f172,f278])).

fof(f278,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f277,f64])).

fof(f64,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f53])).

% (26048)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f53,plain,
    ( ( ~ v1_zfmisc_1(sK1)
      | ~ v2_tex_2(sK1,sK0) )
    & ( v1_zfmisc_1(sK1)
      | v2_tex_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & ~ v1_xboole_0(sK1)
    & l1_pre_topc(sK0)
    & v2_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f50,f52,f51])).

fof(f51,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_zfmisc_1(X1)
              | ~ v2_tex_2(X1,X0) )
            & ( v1_zfmisc_1(X1)
              | v2_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,sK0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK0)
      & v2_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X1] :
        ( ( ~ v1_zfmisc_1(X1)
          | ~ v2_tex_2(X1,sK0) )
        & ( v1_zfmisc_1(X1)
          | v2_tex_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & ~ v1_xboole_0(X1) )
   => ( ( ~ v1_zfmisc_1(sK1)
        | ~ v2_tex_2(sK1,sK0) )
      & ( v1_zfmisc_1(sK1)
        | v2_tex_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

% (26054)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v2_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

fof(f277,plain,
    ( v2_tex_2(sK1,sK0)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f276,f65])).

fof(f65,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f53])).

fof(f276,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tex_2(sK1,sK0)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f262,f80])).

fof(f80,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f57,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
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

fof(f262,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(sK1),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tex_2(sK1,sK0) ) ),
    inference(resolution,[],[f254,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f32])).

% (26050)Refutation not found, incomplete strategy% (26050)------------------------------
% (26050)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26050)Termination reason: Refutation not found, incomplete strategy

% (26050)Memory used [KB]: 10746
% (26050)Time elapsed: 0.099 s
% (26050)------------------------------
% (26050)------------------------------
fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f254,plain,
    ( ~ m1_subset_1(sK3(sK1),u1_struct_0(sK0))
    | v2_tex_2(sK1,sK0) ),
    inference(backward_demodulation,[],[f118,f251])).

fof(f251,plain,(
    sK1 = k1_tarski(sK3(sK1)) ),
    inference(subsumption_resolution,[],[f250,f64])).

fof(f250,plain,
    ( sK1 = k1_tarski(sK3(sK1))
    | v1_xboole_0(sK1) ),
    inference(duplicate_literal_removal,[],[f249])).

fof(f249,plain,
    ( sK1 = k1_tarski(sK3(sK1))
    | sK1 = k1_tarski(sK3(sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f248,f80])).

fof(f248,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | sK1 = k1_tarski(sK3(sK1))
      | k1_tarski(X0) = sK1 ) ),
    inference(subsumption_resolution,[],[f246,f81])).

fof(f81,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f246,plain,(
    ! [X0] :
      ( k1_tarski(X0) = sK1
      | v1_xboole_0(k1_tarski(X0))
      | sK1 = k1_tarski(sK3(sK1))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f245,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f245,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(sK1))
      | sK1 = X1
      | v1_xboole_0(X1)
      | sK1 = k1_tarski(sK3(sK1)) ) ),
    inference(subsumption_resolution,[],[f244,f189])).

fof(f189,plain,
    ( l1_struct_0(sK2(sK0,sK1))
    | sK1 = k1_tarski(sK3(sK1)) ),
    inference(resolution,[],[f185,f85])).

fof(f185,plain,
    ( l1_pre_topc(sK2(sK0,sK1))
    | sK1 = k1_tarski(sK3(sK1)) ),
    inference(subsumption_resolution,[],[f184,f64])).

fof(f184,plain,
    ( l1_pre_topc(sK2(sK0,sK1))
    | sK1 = k1_tarski(sK3(sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f183,f80])).

% (26051)Refutation not found, incomplete strategy% (26051)------------------------------
% (26051)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26051)Termination reason: Refutation not found, incomplete strategy

% (26051)Memory used [KB]: 10618
% (26051)Time elapsed: 0.067 s
% (26051)------------------------------
% (26051)------------------------------
fof(f183,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | l1_pre_topc(sK2(sK0,sK1))
      | k1_tarski(X0) = sK1 ) ),
    inference(subsumption_resolution,[],[f181,f81])).

fof(f181,plain,(
    ! [X0] :
      ( k1_tarski(X0) = sK1
      | v1_xboole_0(k1_tarski(X0))
      | l1_pre_topc(sK2(sK0,sK1))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f180,f76])).

fof(f180,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
      | sK1 = X0
      | v1_xboole_0(X0)
      | l1_pre_topc(sK2(sK0,sK1)) ) ),
    inference(resolution,[],[f174,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f174,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | l1_pre_topc(sK2(sK0,sK1))
      | sK1 = X0
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f173,f64])).

fof(f173,plain,(
    ! [X0] :
      ( l1_pre_topc(sK2(sK0,sK1))
      | ~ r1_tarski(X0,sK1)
      | sK1 = X0
      | v1_xboole_0(sK1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f170,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | ~ r1_tarski(X0,X1)
      | X0 = X1
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f170,plain,
    ( v1_zfmisc_1(sK1)
    | l1_pre_topc(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f165,f63])).

fof(f63,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f165,plain,
    ( v1_zfmisc_1(sK1)
    | l1_pre_topc(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f163,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f163,plain,
    ( m1_pre_topc(sK2(sK0,sK1),sK0)
    | v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f161,f66])).

fof(f66,plain,
    ( v2_tex_2(sK1,sK0)
    | v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f161,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | m1_pre_topc(sK2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f158,f64])).

fof(f158,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_xboole_0(sK1)
    | m1_pre_topc(sK2(sK0,sK1),sK0) ),
    inference(resolution,[],[f157,f65])).

fof(f157,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | v1_xboole_0(X0)
      | m1_pre_topc(sK2(sK0,X0),sK0) ) ),
    inference(subsumption_resolution,[],[f156,f60])).

fof(f60,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f156,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | m1_pre_topc(sK2(sK0,X0),sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f155,f61])).

fof(f61,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f155,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | m1_pre_topc(sK2(sK0,X0),sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f72,f63])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | m1_pre_topc(sK2(X0,X1),X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK2(X0,X1)) = X1
            & m1_pre_topc(sK2(X0,X1),X0)
            & v1_tdlat_3(sK2(X0,X1))
            & ~ v2_struct_0(sK2(X0,X1)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f54])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_tdlat_3(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK2(X0,X1)) = X1
        & m1_pre_topc(sK2(X0,X1),X0)
        & v1_tdlat_3(sK2(X0,X1))
        & ~ v2_struct_0(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).

fof(f244,plain,(
    ! [X1] :
      ( sK1 = k1_tarski(sK3(sK1))
      | sK1 = X1
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK1))
      | ~ l1_struct_0(sK2(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f242,f243])).

fof(f243,plain,(
    ! [X0] :
      ( sK1 = k1_tarski(sK3(sK1))
      | sK1 = X0
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
      | v2_struct_0(sK2(sK0,sK1)) ) ),
    inference(duplicate_literal_removal,[],[f241])).

fof(f241,plain,(
    ! [X0] :
      ( sK1 = k1_tarski(sK3(sK1))
      | sK1 = X0
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
      | v2_struct_0(sK2(sK0,sK1))
      | sK1 = k1_tarski(sK3(sK1)) ) ),
    inference(resolution,[],[f240,f196])).

fof(f196,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | v2_struct_0(sK2(sK0,sK1))
    | sK1 = k1_tarski(sK3(sK1)) ),
    inference(subsumption_resolution,[],[f195,f64])).

fof(f195,plain,
    ( sK1 = k1_tarski(sK3(sK1))
    | v2_struct_0(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f194,f80])).

fof(f194,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k1_tarski(X0) = sK1
      | v2_struct_0(sK2(sK0,sK1))
      | v7_struct_0(sK2(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f192,f81])).

fof(f192,plain,(
    ! [X0] :
      ( v7_struct_0(sK2(sK0,sK1))
      | k1_tarski(X0) = sK1
      | v1_xboole_0(k1_tarski(X0))
      | v2_struct_0(sK2(sK0,sK1))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f191,f76])).

fof(f191,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
      | v7_struct_0(sK2(sK0,sK1))
      | sK1 = X0
      | v1_xboole_0(X0)
      | v2_struct_0(sK2(sK0,sK1)) ) ),
    inference(resolution,[],[f178,f78])).

fof(f178,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | v2_struct_0(sK2(sK0,sK1))
      | v7_struct_0(sK2(sK0,sK1))
      | sK1 = X0
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f177,f64])).

fof(f177,plain,(
    ! [X0] :
      ( v7_struct_0(sK2(sK0,sK1))
      | v2_struct_0(sK2(sK0,sK1))
      | ~ r1_tarski(X0,sK1)
      | sK1 = X0
      | v1_xboole_0(sK1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f171,f69])).

fof(f171,plain,
    ( v1_zfmisc_1(sK1)
    | v7_struct_0(sK2(sK0,sK1))
    | v2_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f169,f170])).

fof(f169,plain,
    ( v1_zfmisc_1(sK1)
    | v7_struct_0(sK2(sK0,sK1))
    | v2_struct_0(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f141,f168])).

fof(f168,plain,
    ( v2_tdlat_3(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1) ),
    inference(subsumption_resolution,[],[f167,f60])).

fof(f167,plain,
    ( v1_zfmisc_1(sK1)
    | v2_tdlat_3(sK2(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f166,f62])).

fof(f62,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f166,plain,
    ( v1_zfmisc_1(sK1)
    | v2_tdlat_3(sK2(sK0,sK1))
    | ~ v2_tdlat_3(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f164,f63])).

fof(f164,plain,
    ( v1_zfmisc_1(sK1)
    | v2_tdlat_3(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f163,f91])).

% (26045)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f91,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_tdlat_3(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f82,f84])).

fof(f84,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).

fof(f82,plain,(
    ! [X0,X1] :
      ( v2_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_tdlat_3(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tdlat_3)).

fof(f141,plain,
    ( ~ v2_tdlat_3(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1)
    | v7_struct_0(sK2(sK0,sK1))
    | v2_struct_0(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK2(sK0,sK1)) ),
    inference(resolution,[],[f140,f92])).

fof(f92,plain,(
    ! [X0] :
      ( ~ v1_tdlat_3(X0)
      | ~ v2_tdlat_3(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f87,f84])).

fof(f87,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( v2_tdlat_3(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_pre_topc(X0)
          & v7_struct_0(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_1)).

fof(f140,plain,
    ( v1_tdlat_3(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f138,f66])).

fof(f138,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_tdlat_3(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f135,f64])).

fof(f135,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_xboole_0(sK1)
    | v1_tdlat_3(sK2(sK0,sK1)) ),
    inference(resolution,[],[f134,f65])).

fof(f134,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | v1_xboole_0(X0)
      | v1_tdlat_3(sK2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f133,f60])).

fof(f133,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | v1_tdlat_3(sK2(sK0,X0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f132,f61])).

fof(f132,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | v1_tdlat_3(sK2(sK0,X0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f71,f63])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | v1_tdlat_3(sK2(X0,X1))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f240,plain,(
    ! [X0] :
      ( ~ v7_struct_0(sK2(sK0,sK1))
      | sK1 = k1_tarski(sK3(sK1))
      | sK1 = X0
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK1)) ) ),
    inference(resolution,[],[f237,f78])).

fof(f237,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | sK1 = k1_tarski(sK3(sK1))
      | ~ v7_struct_0(sK2(sK0,sK1))
      | sK1 = X0
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f236,f64])).

fof(f236,plain,(
    ! [X0] :
      ( ~ v7_struct_0(sK2(sK0,sK1))
      | sK1 = k1_tarski(sK3(sK1))
      | ~ r1_tarski(X0,sK1)
      | sK1 = X0
      | v1_xboole_0(sK1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f234,f69])).

fof(f234,plain,
    ( v1_zfmisc_1(sK1)
    | ~ v7_struct_0(sK2(sK0,sK1))
    | sK1 = k1_tarski(sK3(sK1)) ),
    inference(subsumption_resolution,[],[f233,f189])).

fof(f233,plain,
    ( v1_zfmisc_1(sK1)
    | ~ l1_struct_0(sK2(sK0,sK1))
    | ~ v7_struct_0(sK2(sK0,sK1))
    | sK1 = k1_tarski(sK3(sK1)) ),
    inference(superposition,[],[f68,f232])).

fof(f232,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | sK1 = k1_tarski(sK3(sK1)) ),
    inference(subsumption_resolution,[],[f231,f64])).

fof(f231,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | sK1 = k1_tarski(sK3(sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f230,f80])).

fof(f230,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | sK1 = u1_struct_0(sK2(sK0,sK1))
      | k1_tarski(X0) = sK1 ) ),
    inference(subsumption_resolution,[],[f228,f81])).

fof(f228,plain,(
    ! [X0] :
      ( k1_tarski(X0) = sK1
      | v1_xboole_0(k1_tarski(X0))
      | sK1 = u1_struct_0(sK2(sK0,sK1))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f227,f76])).

fof(f227,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
      | sK1 = X0
      | v1_xboole_0(X0)
      | sK1 = u1_struct_0(sK2(sK0,sK1)) ) ),
    inference(resolution,[],[f226,f78])).

fof(f226,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | sK1 = u1_struct_0(sK2(sK0,sK1))
      | sK1 = X0
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f225,f64])).

fof(f225,plain,(
    ! [X0] :
      ( sK1 = u1_struct_0(sK2(sK0,sK1))
      | ~ r1_tarski(X0,sK1)
      | sK1 = X0
      | v1_xboole_0(sK1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f223,f69])).

fof(f223,plain,
    ( v1_zfmisc_1(sK1)
    | sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    inference(resolution,[],[f221,f66])).

fof(f221,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f218,f64])).

fof(f218,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_xboole_0(sK1)
    | sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    inference(resolution,[],[f217,f65])).

fof(f217,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | v1_xboole_0(X0)
      | u1_struct_0(sK2(sK0,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f216,f60])).

fof(f216,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | u1_struct_0(sK2(sK0,X0)) = X0
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f213,f63])).

fof(f213,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | ~ l1_pre_topc(sK0)
      | u1_struct_0(sK2(sK0,X0)) = X0
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f73,f61])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | u1_struct_0(sK2(X0,X1)) = X1
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f68,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f242,plain,(
    ! [X1] :
      ( sK1 = k1_tarski(sK3(sK1))
      | sK1 = X1
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK1))
      | ~ v2_struct_0(sK2(sK0,sK1))
      | ~ l1_struct_0(sK2(sK0,sK1)) ) ),
    inference(resolution,[],[f240,f89])).

fof(f89,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ( v2_struct_0(X0)
       => v7_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_struct_0)).

fof(f118,plain,
    ( v2_tex_2(k1_tarski(sK3(sK1)),sK0)
    | ~ m1_subset_1(sK3(sK1),u1_struct_0(sK0)) ),
    inference(superposition,[],[f117,f107])).

fof(f107,plain,(
    k6_domain_1(u1_struct_0(sK0),sK3(sK1)) = k1_tarski(sK3(sK1)) ),
    inference(subsumption_resolution,[],[f104,f64])).

fof(f104,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK3(sK1)) = k1_tarski(sK3(sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f103,f65])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k6_domain_1(X0,sK3(X1)) = k1_tarski(sK3(X1))
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f102,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f102,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k6_domain_1(X0,sK3(X1)) = k1_tarski(sK3(X1))
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f96,f80])).

fof(f96,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X3,X4)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
      | k6_domain_1(X2,X3) = k1_tarski(X3) ) ),
    inference(resolution,[],[f90,f75])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f117,plain,(
    ! [X0] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f116,f60])).

fof(f116,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f115,f61])).

fof(f115,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f74,f63])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

fof(f172,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | l1_pre_topc(sK2(sK0,sK1)) ),
    inference(resolution,[],[f170,f67])).

fof(f67,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f316,plain,(
    ~ l1_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f315,f314])).

fof(f314,plain,(
    v2_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f283,f308])).

fof(f308,plain,(
    ~ v7_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f307,f299])).

fof(f307,plain,
    ( ~ l1_struct_0(sK2(sK0,sK1))
    | ~ v7_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f306,f279])).

fof(f279,plain,(
    ~ v1_zfmisc_1(sK1) ),
    inference(subsumption_resolution,[],[f67,f278])).

fof(f306,plain,
    ( v1_zfmisc_1(sK1)
    | ~ l1_struct_0(sK2(sK0,sK1))
    | ~ v7_struct_0(sK2(sK0,sK1)) ),
    inference(superposition,[],[f68,f284])).

fof(f284,plain,(
    sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f221,f278])).

fof(f283,plain,
    ( v2_struct_0(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f176,f278])).

fof(f176,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v2_struct_0(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1)) ),
    inference(resolution,[],[f171,f67])).

fof(f315,plain,
    ( ~ v2_struct_0(sK2(sK0,sK1))
    | ~ l1_struct_0(sK2(sK0,sK1)) ),
    inference(resolution,[],[f308,f89])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:17:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (26047)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.50  % (26047)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (26043)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.51  % (26051)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.51  % (26050)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.51  % (26049)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f317,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(subsumption_resolution,[],[f316,f299])).
% 0.22/0.51  fof(f299,plain,(
% 0.22/0.51    l1_struct_0(sK2(sK0,sK1))),
% 0.22/0.51    inference(resolution,[],[f282,f85])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  % (26044)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.51  fof(f282,plain,(
% 0.22/0.51    l1_pre_topc(sK2(sK0,sK1))),
% 0.22/0.51    inference(subsumption_resolution,[],[f172,f278])).
% 0.22/0.51  fof(f278,plain,(
% 0.22/0.51    v2_tex_2(sK1,sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f277,f64])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ~v1_xboole_0(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f53])).
% 0.22/0.51  % (26048)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ((~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f50,f52,f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    ? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f22])).
% 0.22/0.51  % (26054)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,negated_conjecture,(
% 0.22/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.22/0.51    inference(negated_conjecture,[],[f18])).
% 0.22/0.51  fof(f18,conjecture,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).
% 0.22/0.51  fof(f277,plain,(
% 0.22/0.51    v2_tex_2(sK1,sK0) | v1_xboole_0(sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f276,f65])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    inference(cnf_transformation,[],[f53])).
% 0.22/0.51  fof(f276,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(sK1,sK0) | v1_xboole_0(sK1)),
% 0.22/0.51    inference(resolution,[],[f262,f80])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f59])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f57,f58])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.51    inference(rectify,[],[f56])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.51    inference(nnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.51  fof(f262,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(sK3(sK1),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(sK1,sK0)) )),
% 0.22/0.51    inference(resolution,[],[f254,f75])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.51    inference(flattening,[],[f32])).
% 0.22/0.51  % (26050)Refutation not found, incomplete strategy% (26050)------------------------------
% 0.22/0.51  % (26050)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (26050)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (26050)Memory used [KB]: 10746
% 0.22/0.51  % (26050)Time elapsed: 0.099 s
% 0.22/0.51  % (26050)------------------------------
% 0.22/0.51  % (26050)------------------------------
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.51  fof(f254,plain,(
% 0.22/0.51    ~m1_subset_1(sK3(sK1),u1_struct_0(sK0)) | v2_tex_2(sK1,sK0)),
% 0.22/0.51    inference(backward_demodulation,[],[f118,f251])).
% 0.22/0.51  fof(f251,plain,(
% 0.22/0.51    sK1 = k1_tarski(sK3(sK1))),
% 0.22/0.51    inference(subsumption_resolution,[],[f250,f64])).
% 0.22/0.51  fof(f250,plain,(
% 0.22/0.51    sK1 = k1_tarski(sK3(sK1)) | v1_xboole_0(sK1)),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f249])).
% 0.22/0.51  fof(f249,plain,(
% 0.22/0.51    sK1 = k1_tarski(sK3(sK1)) | sK1 = k1_tarski(sK3(sK1)) | v1_xboole_0(sK1)),
% 0.22/0.51    inference(resolution,[],[f248,f80])).
% 0.22/0.51  fof(f248,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,sK1) | sK1 = k1_tarski(sK3(sK1)) | k1_tarski(X0) = sK1) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f246,f81])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.22/0.51  fof(f246,plain,(
% 0.22/0.51    ( ! [X0] : (k1_tarski(X0) = sK1 | v1_xboole_0(k1_tarski(X0)) | sK1 = k1_tarski(sK3(sK1)) | ~r2_hidden(X0,sK1)) )),
% 0.22/0.51    inference(resolution,[],[f245,f76])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 0.22/0.51  fof(f245,plain,(
% 0.22/0.51    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(sK1)) | sK1 = X1 | v1_xboole_0(X1) | sK1 = k1_tarski(sK3(sK1))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f244,f189])).
% 0.22/0.51  fof(f189,plain,(
% 0.22/0.51    l1_struct_0(sK2(sK0,sK1)) | sK1 = k1_tarski(sK3(sK1))),
% 0.22/0.51    inference(resolution,[],[f185,f85])).
% 0.22/0.51  fof(f185,plain,(
% 0.22/0.51    l1_pre_topc(sK2(sK0,sK1)) | sK1 = k1_tarski(sK3(sK1))),
% 0.22/0.51    inference(subsumption_resolution,[],[f184,f64])).
% 0.22/0.51  fof(f184,plain,(
% 0.22/0.51    l1_pre_topc(sK2(sK0,sK1)) | sK1 = k1_tarski(sK3(sK1)) | v1_xboole_0(sK1)),
% 0.22/0.51    inference(resolution,[],[f183,f80])).
% 0.22/0.51  % (26051)Refutation not found, incomplete strategy% (26051)------------------------------
% 0.22/0.51  % (26051)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (26051)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (26051)Memory used [KB]: 10618
% 0.22/0.51  % (26051)Time elapsed: 0.067 s
% 0.22/0.51  % (26051)------------------------------
% 0.22/0.51  % (26051)------------------------------
% 0.22/0.51  fof(f183,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,sK1) | l1_pre_topc(sK2(sK0,sK1)) | k1_tarski(X0) = sK1) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f181,f81])).
% 0.22/0.51  fof(f181,plain,(
% 0.22/0.51    ( ! [X0] : (k1_tarski(X0) = sK1 | v1_xboole_0(k1_tarski(X0)) | l1_pre_topc(sK2(sK0,sK1)) | ~r2_hidden(X0,sK1)) )),
% 0.22/0.51    inference(resolution,[],[f180,f76])).
% 0.22/0.51  fof(f180,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | sK1 = X0 | v1_xboole_0(X0) | l1_pre_topc(sK2(sK0,sK1))) )),
% 0.22/0.51    inference(resolution,[],[f174,f78])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.22/0.51    inference(unused_predicate_definition_removal,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.51  fof(f174,plain,(
% 0.22/0.51    ( ! [X0] : (~r1_tarski(X0,sK1) | l1_pre_topc(sK2(sK0,sK1)) | sK1 = X0 | v1_xboole_0(X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f173,f64])).
% 0.22/0.51  fof(f173,plain,(
% 0.22/0.51    ( ! [X0] : (l1_pre_topc(sK2(sK0,sK1)) | ~r1_tarski(X0,sK1) | sK1 = X0 | v1_xboole_0(sK1) | v1_xboole_0(X0)) )),
% 0.22/0.51    inference(resolution,[],[f170,f69])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | ~r1_tarski(X0,X1) | X0 = X1 | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.51    inference(flattening,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,axiom,(
% 0.22/0.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 0.22/0.51  fof(f170,plain,(
% 0.22/0.51    v1_zfmisc_1(sK1) | l1_pre_topc(sK2(sK0,sK1))),
% 0.22/0.51    inference(subsumption_resolution,[],[f165,f63])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    l1_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f53])).
% 0.22/0.51  fof(f165,plain,(
% 0.22/0.51    v1_zfmisc_1(sK1) | l1_pre_topc(sK2(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.22/0.51    inference(resolution,[],[f163,f83])).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.51  fof(f163,plain,(
% 0.22/0.51    m1_pre_topc(sK2(sK0,sK1),sK0) | v1_zfmisc_1(sK1)),
% 0.22/0.51    inference(resolution,[],[f161,f66])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    v2_tex_2(sK1,sK0) | v1_zfmisc_1(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f53])).
% 0.22/0.52  fof(f161,plain,(
% 0.22/0.52    ~v2_tex_2(sK1,sK0) | m1_pre_topc(sK2(sK0,sK1),sK0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f158,f64])).
% 0.22/0.52  fof(f158,plain,(
% 0.22/0.52    ~v2_tex_2(sK1,sK0) | v1_xboole_0(sK1) | m1_pre_topc(sK2(sK0,sK1),sK0)),
% 0.22/0.52    inference(resolution,[],[f157,f65])).
% 0.22/0.52  fof(f157,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | v1_xboole_0(X0) | m1_pre_topc(sK2(sK0,X0),sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f156,f60])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ~v2_struct_0(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f53])).
% 0.22/0.52  fof(f156,plain,(
% 0.22/0.52    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | m1_pre_topc(sK2(sK0,X0),sK0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f155,f61])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    v2_pre_topc(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f53])).
% 0.22/0.52  fof(f155,plain,(
% 0.22/0.52    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | m1_pre_topc(sK2(sK0,X0),sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(resolution,[],[f72,f63])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | m1_pre_topc(sK2(X0,X1),X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f55])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_tdlat_3(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f54])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_tdlat_3(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 0.22/0.52    inference(pure_predicate_removal,[],[f16])).
% 0.22/0.52  fof(f16,axiom,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).
% 0.22/0.52  fof(f244,plain,(
% 0.22/0.52    ( ! [X1] : (sK1 = k1_tarski(sK3(sK1)) | sK1 = X1 | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK1)) | ~l1_struct_0(sK2(sK0,sK1))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f242,f243])).
% 0.22/0.52  fof(f243,plain,(
% 0.22/0.52    ( ! [X0] : (sK1 = k1_tarski(sK3(sK1)) | sK1 = X0 | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK1)) | v2_struct_0(sK2(sK0,sK1))) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f241])).
% 0.22/0.52  fof(f241,plain,(
% 0.22/0.52    ( ! [X0] : (sK1 = k1_tarski(sK3(sK1)) | sK1 = X0 | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK1)) | v2_struct_0(sK2(sK0,sK1)) | sK1 = k1_tarski(sK3(sK1))) )),
% 0.22/0.52    inference(resolution,[],[f240,f196])).
% 0.22/0.52  fof(f196,plain,(
% 0.22/0.52    v7_struct_0(sK2(sK0,sK1)) | v2_struct_0(sK2(sK0,sK1)) | sK1 = k1_tarski(sK3(sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f195,f64])).
% 0.22/0.52  fof(f195,plain,(
% 0.22/0.52    sK1 = k1_tarski(sK3(sK1)) | v2_struct_0(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | v1_xboole_0(sK1)),
% 0.22/0.52    inference(resolution,[],[f194,f80])).
% 0.22/0.52  fof(f194,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_tarski(X0) = sK1 | v2_struct_0(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f192,f81])).
% 0.22/0.52  fof(f192,plain,(
% 0.22/0.52    ( ! [X0] : (v7_struct_0(sK2(sK0,sK1)) | k1_tarski(X0) = sK1 | v1_xboole_0(k1_tarski(X0)) | v2_struct_0(sK2(sK0,sK1)) | ~r2_hidden(X0,sK1)) )),
% 0.22/0.52    inference(resolution,[],[f191,f76])).
% 0.22/0.52  fof(f191,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | v7_struct_0(sK2(sK0,sK1)) | sK1 = X0 | v1_xboole_0(X0) | v2_struct_0(sK2(sK0,sK1))) )),
% 0.22/0.52    inference(resolution,[],[f178,f78])).
% 0.22/0.52  fof(f178,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(X0,sK1) | v2_struct_0(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | sK1 = X0 | v1_xboole_0(X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f177,f64])).
% 0.22/0.52  fof(f177,plain,(
% 0.22/0.52    ( ! [X0] : (v7_struct_0(sK2(sK0,sK1)) | v2_struct_0(sK2(sK0,sK1)) | ~r1_tarski(X0,sK1) | sK1 = X0 | v1_xboole_0(sK1) | v1_xboole_0(X0)) )),
% 0.22/0.52    inference(resolution,[],[f171,f69])).
% 0.22/0.52  fof(f171,plain,(
% 0.22/0.52    v1_zfmisc_1(sK1) | v7_struct_0(sK2(sK0,sK1)) | v2_struct_0(sK2(sK0,sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f169,f170])).
% 0.22/0.52  fof(f169,plain,(
% 0.22/0.52    v1_zfmisc_1(sK1) | v7_struct_0(sK2(sK0,sK1)) | v2_struct_0(sK2(sK0,sK1)) | ~l1_pre_topc(sK2(sK0,sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f141,f168])).
% 0.22/0.52  fof(f168,plain,(
% 0.22/0.52    v2_tdlat_3(sK2(sK0,sK1)) | v1_zfmisc_1(sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f167,f60])).
% 0.22/0.52  fof(f167,plain,(
% 0.22/0.52    v1_zfmisc_1(sK1) | v2_tdlat_3(sK2(sK0,sK1)) | v2_struct_0(sK0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f166,f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    v2_tdlat_3(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f53])).
% 0.22/0.52  fof(f166,plain,(
% 0.22/0.52    v1_zfmisc_1(sK1) | v2_tdlat_3(sK2(sK0,sK1)) | ~v2_tdlat_3(sK0) | v2_struct_0(sK0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f164,f63])).
% 0.22/0.52  fof(f164,plain,(
% 0.22/0.52    v1_zfmisc_1(sK1) | v2_tdlat_3(sK2(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | v2_struct_0(sK0)),
% 0.22/0.52    inference(resolution,[],[f163,f91])).
% 0.22/0.52  % (26045)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_tdlat_3(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f82,f84])).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    ( ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(flattening,[],[f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,axiom,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_tdlat_3(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tdlat_3)).
% 0.22/0.52  fof(f141,plain,(
% 0.22/0.52    ~v2_tdlat_3(sK2(sK0,sK1)) | v1_zfmisc_1(sK1) | v7_struct_0(sK2(sK0,sK1)) | v2_struct_0(sK2(sK0,sK1)) | ~l1_pre_topc(sK2(sK0,sK1))),
% 0.22/0.52    inference(resolution,[],[f140,f92])).
% 0.22/0.52  fof(f92,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_tdlat_3(X0) | ~v2_tdlat_3(X0) | v7_struct_0(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f87,f84])).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    ( ! [X0] : (v7_struct_0(X0) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ! [X0] : ((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(flattening,[],[f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ! [X0] : (((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | (~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => ((v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_1)).
% 0.22/0.52  fof(f140,plain,(
% 0.22/0.52    v1_tdlat_3(sK2(sK0,sK1)) | v1_zfmisc_1(sK1)),
% 0.22/0.52    inference(resolution,[],[f138,f66])).
% 0.22/0.52  fof(f138,plain,(
% 0.22/0.52    ~v2_tex_2(sK1,sK0) | v1_tdlat_3(sK2(sK0,sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f135,f64])).
% 0.22/0.52  fof(f135,plain,(
% 0.22/0.52    ~v2_tex_2(sK1,sK0) | v1_xboole_0(sK1) | v1_tdlat_3(sK2(sK0,sK1))),
% 0.22/0.52    inference(resolution,[],[f134,f65])).
% 0.22/0.52  fof(f134,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | v1_xboole_0(X0) | v1_tdlat_3(sK2(sK0,X0))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f133,f60])).
% 0.22/0.52  fof(f133,plain,(
% 0.22/0.52    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | v1_tdlat_3(sK2(sK0,X0)) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f132,f61])).
% 0.22/0.52  fof(f132,plain,(
% 0.22/0.52    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | v1_tdlat_3(sK2(sK0,X0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(resolution,[],[f71,f63])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | v1_tdlat_3(sK2(X0,X1)) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f55])).
% 0.22/0.52  fof(f240,plain,(
% 0.22/0.52    ( ! [X0] : (~v7_struct_0(sK2(sK0,sK1)) | sK1 = k1_tarski(sK3(sK1)) | sK1 = X0 | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK1))) )),
% 0.22/0.52    inference(resolution,[],[f237,f78])).
% 0.22/0.52  fof(f237,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(X0,sK1) | sK1 = k1_tarski(sK3(sK1)) | ~v7_struct_0(sK2(sK0,sK1)) | sK1 = X0 | v1_xboole_0(X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f236,f64])).
% 0.22/0.52  fof(f236,plain,(
% 0.22/0.52    ( ! [X0] : (~v7_struct_0(sK2(sK0,sK1)) | sK1 = k1_tarski(sK3(sK1)) | ~r1_tarski(X0,sK1) | sK1 = X0 | v1_xboole_0(sK1) | v1_xboole_0(X0)) )),
% 0.22/0.52    inference(resolution,[],[f234,f69])).
% 0.22/0.52  fof(f234,plain,(
% 0.22/0.52    v1_zfmisc_1(sK1) | ~v7_struct_0(sK2(sK0,sK1)) | sK1 = k1_tarski(sK3(sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f233,f189])).
% 0.22/0.52  fof(f233,plain,(
% 0.22/0.52    v1_zfmisc_1(sK1) | ~l1_struct_0(sK2(sK0,sK1)) | ~v7_struct_0(sK2(sK0,sK1)) | sK1 = k1_tarski(sK3(sK1))),
% 0.22/0.52    inference(superposition,[],[f68,f232])).
% 0.22/0.52  fof(f232,plain,(
% 0.22/0.52    sK1 = u1_struct_0(sK2(sK0,sK1)) | sK1 = k1_tarski(sK3(sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f231,f64])).
% 0.22/0.52  fof(f231,plain,(
% 0.22/0.52    sK1 = u1_struct_0(sK2(sK0,sK1)) | sK1 = k1_tarski(sK3(sK1)) | v1_xboole_0(sK1)),
% 0.22/0.52    inference(resolution,[],[f230,f80])).
% 0.22/0.52  fof(f230,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,sK1) | sK1 = u1_struct_0(sK2(sK0,sK1)) | k1_tarski(X0) = sK1) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f228,f81])).
% 0.22/0.52  fof(f228,plain,(
% 0.22/0.52    ( ! [X0] : (k1_tarski(X0) = sK1 | v1_xboole_0(k1_tarski(X0)) | sK1 = u1_struct_0(sK2(sK0,sK1)) | ~r2_hidden(X0,sK1)) )),
% 0.22/0.52    inference(resolution,[],[f227,f76])).
% 0.22/0.52  fof(f227,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | sK1 = X0 | v1_xboole_0(X0) | sK1 = u1_struct_0(sK2(sK0,sK1))) )),
% 0.22/0.52    inference(resolution,[],[f226,f78])).
% 0.22/0.52  fof(f226,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(X0,sK1) | sK1 = u1_struct_0(sK2(sK0,sK1)) | sK1 = X0 | v1_xboole_0(X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f225,f64])).
% 0.22/0.52  fof(f225,plain,(
% 0.22/0.52    ( ! [X0] : (sK1 = u1_struct_0(sK2(sK0,sK1)) | ~r1_tarski(X0,sK1) | sK1 = X0 | v1_xboole_0(sK1) | v1_xboole_0(X0)) )),
% 0.22/0.52    inference(resolution,[],[f223,f69])).
% 0.22/0.52  fof(f223,plain,(
% 0.22/0.52    v1_zfmisc_1(sK1) | sK1 = u1_struct_0(sK2(sK0,sK1))),
% 0.22/0.52    inference(resolution,[],[f221,f66])).
% 0.22/0.52  fof(f221,plain,(
% 0.22/0.52    ~v2_tex_2(sK1,sK0) | sK1 = u1_struct_0(sK2(sK0,sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f218,f64])).
% 0.22/0.52  fof(f218,plain,(
% 0.22/0.52    ~v2_tex_2(sK1,sK0) | v1_xboole_0(sK1) | sK1 = u1_struct_0(sK2(sK0,sK1))),
% 0.22/0.52    inference(resolution,[],[f217,f65])).
% 0.22/0.52  fof(f217,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | v1_xboole_0(X0) | u1_struct_0(sK2(sK0,X0)) = X0) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f216,f60])).
% 0.22/0.52  fof(f216,plain,(
% 0.22/0.52    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | u1_struct_0(sK2(sK0,X0)) = X0 | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f213,f63])).
% 0.22/0.52  fof(f213,plain,(
% 0.22/0.52    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | ~l1_pre_topc(sK0) | u1_struct_0(sK2(sK0,X0)) = X0 | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(resolution,[],[f73,f61])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | u1_struct_0(sK2(X0,X1)) = X1 | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f55])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).
% 0.22/0.52  fof(f242,plain,(
% 0.22/0.52    ( ! [X1] : (sK1 = k1_tarski(sK3(sK1)) | sK1 = X1 | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK1)) | ~v2_struct_0(sK2(sK0,sK1)) | ~l1_struct_0(sK2(sK0,sK1))) )),
% 0.22/0.52    inference(resolution,[],[f240,f89])).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    ( ! [X0] : (v7_struct_0(X0) | ~v2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f46])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    ! [X0] : (v7_struct_0(X0) | ~v2_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f45])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    ! [X0] : ((v7_struct_0(X0) | ~v2_struct_0(X0)) | ~l1_struct_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0] : (l1_struct_0(X0) => (v2_struct_0(X0) => v7_struct_0(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_struct_0)).
% 0.22/0.52  fof(f118,plain,(
% 0.22/0.52    v2_tex_2(k1_tarski(sK3(sK1)),sK0) | ~m1_subset_1(sK3(sK1),u1_struct_0(sK0))),
% 0.22/0.52    inference(superposition,[],[f117,f107])).
% 0.22/0.52  fof(f107,plain,(
% 0.22/0.52    k6_domain_1(u1_struct_0(sK0),sK3(sK1)) = k1_tarski(sK3(sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f104,f64])).
% 0.22/0.52  fof(f104,plain,(
% 0.22/0.52    k6_domain_1(u1_struct_0(sK0),sK3(sK1)) = k1_tarski(sK3(sK1)) | v1_xboole_0(sK1)),
% 0.22/0.52    inference(resolution,[],[f103,f65])).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k6_domain_1(X0,sK3(X1)) = k1_tarski(sK3(X1)) | v1_xboole_0(X1)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f102,f77])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.22/0.52  fof(f102,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k6_domain_1(X0,sK3(X1)) = k1_tarski(sK3(X1)) | v1_xboole_0(X1)) )),
% 0.22/0.52    inference(resolution,[],[f96,f80])).
% 0.22/0.52  fof(f96,plain,(
% 0.22/0.52    ( ! [X4,X2,X3] : (~r2_hidden(X3,X4) | v1_xboole_0(X2) | ~m1_subset_1(X4,k1_zfmisc_1(X2)) | k6_domain_1(X2,X3) = k1_tarski(X3)) )),
% 0.22/0.52    inference(resolution,[],[f90,f75])).
% 0.22/0.52  fof(f90,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1) | v1_xboole_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f48])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.52    inference(flattening,[],[f47])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,axiom,(
% 0.22/0.52    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.22/0.52  fof(f117,plain,(
% 0.22/0.52    ( ! [X0] : (v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f116,f60])).
% 0.22/0.52  fof(f116,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f115,f61])).
% 0.22/0.52  fof(f115,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(resolution,[],[f74,f63])).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,axiom,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).
% 0.22/0.52  fof(f172,plain,(
% 0.22/0.52    ~v2_tex_2(sK1,sK0) | l1_pre_topc(sK2(sK0,sK1))),
% 0.22/0.52    inference(resolution,[],[f170,f67])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    ~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f53])).
% 0.22/0.52  fof(f316,plain,(
% 0.22/0.52    ~l1_struct_0(sK2(sK0,sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f315,f314])).
% 0.22/0.52  fof(f314,plain,(
% 0.22/0.52    v2_struct_0(sK2(sK0,sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f283,f308])).
% 0.22/0.52  fof(f308,plain,(
% 0.22/0.52    ~v7_struct_0(sK2(sK0,sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f307,f299])).
% 0.22/0.52  fof(f307,plain,(
% 0.22/0.52    ~l1_struct_0(sK2(sK0,sK1)) | ~v7_struct_0(sK2(sK0,sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f306,f279])).
% 0.22/0.52  fof(f279,plain,(
% 0.22/0.52    ~v1_zfmisc_1(sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f67,f278])).
% 0.22/0.52  fof(f306,plain,(
% 0.22/0.52    v1_zfmisc_1(sK1) | ~l1_struct_0(sK2(sK0,sK1)) | ~v7_struct_0(sK2(sK0,sK1))),
% 0.22/0.52    inference(superposition,[],[f68,f284])).
% 0.22/0.52  fof(f284,plain,(
% 0.22/0.52    sK1 = u1_struct_0(sK2(sK0,sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f221,f278])).
% 0.22/0.52  fof(f283,plain,(
% 0.22/0.52    v2_struct_0(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f176,f278])).
% 0.22/0.52  fof(f176,plain,(
% 0.22/0.52    ~v2_tex_2(sK1,sK0) | v2_struct_0(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1))),
% 0.22/0.52    inference(resolution,[],[f171,f67])).
% 0.22/0.52  fof(f315,plain,(
% 0.22/0.52    ~v2_struct_0(sK2(sK0,sK1)) | ~l1_struct_0(sK2(sK0,sK1))),
% 0.22/0.52    inference(resolution,[],[f308,f89])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (26047)------------------------------
% 0.22/0.52  % (26047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (26047)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (26047)Memory used [KB]: 6396
% 0.22/0.52  % (26047)Time elapsed: 0.102 s
% 0.22/0.52  % (26047)------------------------------
% 0.22/0.52  % (26047)------------------------------
% 0.22/0.52  % (26063)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.52  % (26071)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.52  % (26041)Success in time 0.149 s
%------------------------------------------------------------------------------
