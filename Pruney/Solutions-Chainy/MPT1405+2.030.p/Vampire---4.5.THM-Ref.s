%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 156 expanded)
%              Number of leaves         :   22 (  70 expanded)
%              Depth                    :    8
%              Number of atoms          :  250 ( 460 expanded)
%              Number of equality atoms :   13 (  17 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f191,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f52,f57,f62,f68,f74,f80,f86,f92,f138,f149,f174])).

fof(f174,plain,
    ( spl2_18
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f173,f89,f77,f49,f146])).

fof(f146,plain,
    ( spl2_18
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f49,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f77,plain,
    ( spl2_7
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f89,plain,
    ( spl2_9
  <=> k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f173,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f154,f91])).

fof(f91,plain,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f89])).

fof(f154,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_2
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f51,f79,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

% (18557)Refutation not found, incomplete strategy% (18557)------------------------------
% (18557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (18557)Termination reason: Refutation not found, incomplete strategy

% (18557)Memory used [KB]: 6140
% (18557)Time elapsed: 0.070 s
% (18557)------------------------------
% (18557)------------------------------
% (18551)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).

fof(f79,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f77])).

fof(f51,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f149,plain,
    ( ~ spl2_18
    | ~ spl2_2
    | ~ spl2_6
    | spl2_16 ),
    inference(avatar_split_clause,[],[f143,f135,f71,f49,f146])).

fof(f71,plain,
    ( spl2_6
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f135,plain,
    ( spl2_16
  <=> r1_tarski(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f143,plain,
    ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_2
    | ~ spl2_6
    | spl2_16 ),
    inference(unit_resulting_resolution,[],[f51,f73,f137,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(f137,plain,
    ( ~ r1_tarski(sK1,k2_struct_0(sK0))
    | spl2_16 ),
    inference(avatar_component_clause,[],[f135])).

fof(f73,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f71])).

fof(f138,plain,
    ( ~ spl2_16
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f133,f83,f71,f59,f54,f49,f44,f135])).

fof(f44,plain,
    ( spl2_1
  <=> m2_connsp_2(k2_struct_0(sK0),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f54,plain,
    ( spl2_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f59,plain,
    ( spl2_4
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f83,plain,
    ( spl2_8
  <=> k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f133,plain,
    ( ~ r1_tarski(sK1,k2_struct_0(sK0))
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f131,f85])).

fof(f85,plain,
    ( k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f83])).

fof(f131,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,k2_struct_0(sK0)))
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f61,f56,f46,f51,f73,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m2_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_connsp_2(X2,X0,X1)
                  | ~ r1_tarski(X1,k1_tops_1(X0,X2)) )
                & ( r1_tarski(X1,k1_tops_1(X0,X2))
                  | ~ m2_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).

fof(f46,plain,
    ( ~ m2_connsp_2(k2_struct_0(sK0),sK0,sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f56,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f61,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f92,plain,
    ( spl2_9
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f87,f65,f49,f89])).

fof(f65,plain,
    ( spl2_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f87,plain,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f67,f51,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

% (18562)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_pre_topc)).

fof(f67,plain,
    ( l1_struct_0(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f65])).

fof(f86,plain,
    ( spl2_8
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f81,f59,f54,f83])).

fof(f81,plain,
    ( k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f61,f56,f35])).

fof(f35,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

% (18558)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).

fof(f80,plain,
    ( spl2_7
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f75,f49,f77])).

fof(f75,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f51,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f74,plain,
    ( spl2_6
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f69,f65,f71])).

fof(f69,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f67,f37])).

fof(f37,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f68,plain,
    ( spl2_5
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f63,f54,f65])).

fof(f63,plain,
    ( l1_struct_0(sK0)
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f56,f42])).

fof(f42,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f62,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f29,f59])).

fof(f29,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ m2_connsp_2(k2_struct_0(sK0),sK0,sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(sK0),sK0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ~ m2_connsp_2(k2_struct_0(sK0),sK0,X1)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ m2_connsp_2(k2_struct_0(sK0),sK0,sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_connsp_2)).

fof(f57,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f30,f54])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f52,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f31,f49])).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f47,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f32,f44])).

fof(f32,plain,(
    ~ m2_connsp_2(k2_struct_0(sK0),sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n021.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:00:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (18556)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.50  % (18573)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.50  % (18565)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.50  % (18567)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.51  % (18568)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.51  % (18554)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.51  % (18556)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (18570)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.51  % (18550)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.51  % (18552)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.51  % (18573)Refutation not found, incomplete strategy% (18573)------------------------------
% 0.22/0.51  % (18573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (18573)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (18573)Memory used [KB]: 10618
% 0.22/0.51  % (18573)Time elapsed: 0.057 s
% 0.22/0.51  % (18573)------------------------------
% 0.22/0.51  % (18573)------------------------------
% 0.22/0.51  % (18569)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.51  % (18557)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (18564)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f191,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f47,f52,f57,f62,f68,f74,f80,f86,f92,f138,f149,f174])).
% 0.22/0.51  fof(f174,plain,(
% 0.22/0.51    spl2_18 | ~spl2_2 | ~spl2_7 | ~spl2_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f173,f89,f77,f49,f146])).
% 1.19/0.51  fof(f146,plain,(
% 1.19/0.51    spl2_18 <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)),k3_subset_1(u1_struct_0(sK0),sK1))),
% 1.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 1.19/0.51  fof(f49,plain,(
% 1.19/0.51    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.19/0.51  fof(f77,plain,(
% 1.19/0.51    spl2_7 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 1.19/0.51  fof(f89,plain,(
% 1.19/0.51    spl2_9 <=> k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1))),
% 1.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 1.19/0.51  fof(f173,plain,(
% 1.19/0.51    r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)),k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl2_2 | ~spl2_7 | ~spl2_9)),
% 1.19/0.51    inference(forward_demodulation,[],[f154,f91])).
% 1.19/0.51  fof(f91,plain,(
% 1.19/0.51    k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_9),
% 1.19/0.51    inference(avatar_component_clause,[],[f89])).
% 1.19/0.51  fof(f154,plain,(
% 1.19/0.51    r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl2_2 | ~spl2_7)),
% 1.19/0.51    inference(unit_resulting_resolution,[],[f51,f79,f40])).
% 1.19/0.51  fof(f40,plain,(
% 1.19/0.51    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.19/0.51    inference(cnf_transformation,[],[f21])).
% 1.19/0.51  fof(f21,plain,(
% 1.19/0.51    ! [X0,X1] : (! [X2] : (r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.19/0.51    inference(ennf_transformation,[],[f3])).
% 1.19/0.51  % (18557)Refutation not found, incomplete strategy% (18557)------------------------------
% 1.19/0.51  % (18557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.51  % (18557)Termination reason: Refutation not found, incomplete strategy
% 1.19/0.51  
% 1.19/0.51  % (18557)Memory used [KB]: 6140
% 1.19/0.51  % (18557)Time elapsed: 0.070 s
% 1.19/0.51  % (18557)------------------------------
% 1.19/0.51  % (18557)------------------------------
% 1.19/0.51  % (18551)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 1.19/0.52  fof(f3,axiom,(
% 1.19/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 1.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).
% 1.19/0.52  fof(f79,plain,(
% 1.19/0.52    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_7),
% 1.19/0.52    inference(avatar_component_clause,[],[f77])).
% 1.19/0.52  fof(f51,plain,(
% 1.19/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 1.19/0.52    inference(avatar_component_clause,[],[f49])).
% 1.19/0.52  fof(f149,plain,(
% 1.19/0.52    ~spl2_18 | ~spl2_2 | ~spl2_6 | spl2_16),
% 1.19/0.52    inference(avatar_split_clause,[],[f143,f135,f71,f49,f146])).
% 1.19/0.52  fof(f71,plain,(
% 1.19/0.52    spl2_6 <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.19/0.52  fof(f135,plain,(
% 1.19/0.52    spl2_16 <=> r1_tarski(sK1,k2_struct_0(sK0))),
% 1.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 1.19/0.52  fof(f143,plain,(
% 1.19/0.52    ~r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)),k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl2_2 | ~spl2_6 | spl2_16)),
% 1.19/0.52    inference(unit_resulting_resolution,[],[f51,f73,f137,f39])).
% 1.19/0.52  fof(f39,plain,(
% 1.19/0.52    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.19/0.52    inference(cnf_transformation,[],[f28])).
% 1.19/0.52  fof(f28,plain,(
% 1.19/0.52    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.19/0.52    inference(nnf_transformation,[],[f20])).
% 1.19/0.52  fof(f20,plain,(
% 1.19/0.52    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.19/0.52    inference(ennf_transformation,[],[f2])).
% 1.19/0.52  fof(f2,axiom,(
% 1.19/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 1.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).
% 1.19/0.52  fof(f137,plain,(
% 1.19/0.52    ~r1_tarski(sK1,k2_struct_0(sK0)) | spl2_16),
% 1.19/0.52    inference(avatar_component_clause,[],[f135])).
% 1.19/0.52  fof(f73,plain,(
% 1.19/0.52    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_6),
% 1.19/0.52    inference(avatar_component_clause,[],[f71])).
% 1.19/0.52  fof(f138,plain,(
% 1.19/0.52    ~spl2_16 | spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_6 | ~spl2_8),
% 1.19/0.52    inference(avatar_split_clause,[],[f133,f83,f71,f59,f54,f49,f44,f135])).
% 1.19/0.52  fof(f44,plain,(
% 1.19/0.52    spl2_1 <=> m2_connsp_2(k2_struct_0(sK0),sK0,sK1)),
% 1.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.19/0.52  fof(f54,plain,(
% 1.19/0.52    spl2_3 <=> l1_pre_topc(sK0)),
% 1.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.19/0.52  fof(f59,plain,(
% 1.19/0.52    spl2_4 <=> v2_pre_topc(sK0)),
% 1.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.19/0.52  fof(f83,plain,(
% 1.19/0.52    spl2_8 <=> k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0))),
% 1.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 1.19/0.52  fof(f133,plain,(
% 1.19/0.52    ~r1_tarski(sK1,k2_struct_0(sK0)) | (spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_6 | ~spl2_8)),
% 1.19/0.52    inference(forward_demodulation,[],[f131,f85])).
% 1.19/0.52  fof(f85,plain,(
% 1.19/0.52    k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0)) | ~spl2_8),
% 1.19/0.52    inference(avatar_component_clause,[],[f83])).
% 1.19/0.52  fof(f131,plain,(
% 1.19/0.52    ~r1_tarski(sK1,k1_tops_1(sK0,k2_struct_0(sK0))) | (spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_6)),
% 1.19/0.52    inference(unit_resulting_resolution,[],[f61,f56,f46,f51,f73,f34])).
% 1.19/0.52  fof(f34,plain,(
% 1.19/0.52    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m2_connsp_2(X2,X0,X1)) )),
% 1.19/0.52    inference(cnf_transformation,[],[f27])).
% 1.19/0.52  fof(f27,plain,(
% 1.19/0.52    ! [X0] : (! [X1] : (! [X2] : (((m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2))) & (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.19/0.52    inference(nnf_transformation,[],[f15])).
% 1.19/0.52  fof(f15,plain,(
% 1.19/0.52    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.19/0.52    inference(flattening,[],[f14])).
% 1.19/0.52  fof(f14,plain,(
% 1.19/0.52    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.19/0.52    inference(ennf_transformation,[],[f8])).
% 1.19/0.52  fof(f8,axiom,(
% 1.19/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 1.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).
% 1.19/0.52  fof(f46,plain,(
% 1.19/0.52    ~m2_connsp_2(k2_struct_0(sK0),sK0,sK1) | spl2_1),
% 1.19/0.52    inference(avatar_component_clause,[],[f44])).
% 1.19/0.52  fof(f56,plain,(
% 1.19/0.52    l1_pre_topc(sK0) | ~spl2_3),
% 1.19/0.52    inference(avatar_component_clause,[],[f54])).
% 1.19/0.52  fof(f61,plain,(
% 1.19/0.52    v2_pre_topc(sK0) | ~spl2_4),
% 1.19/0.52    inference(avatar_component_clause,[],[f59])).
% 1.19/0.52  fof(f92,plain,(
% 1.19/0.52    spl2_9 | ~spl2_2 | ~spl2_5),
% 1.19/0.52    inference(avatar_split_clause,[],[f87,f65,f49,f89])).
% 1.19/0.52  fof(f65,plain,(
% 1.19/0.52    spl2_5 <=> l1_struct_0(sK0)),
% 1.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.19/0.52  fof(f87,plain,(
% 1.19/0.52    k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl2_2 | ~spl2_5)),
% 1.19/0.52    inference(unit_resulting_resolution,[],[f67,f51,f36])).
% 1.19/0.52  fof(f36,plain,(
% 1.19/0.52    ( ! [X0,X1] : (k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 1.19/0.52    inference(cnf_transformation,[],[f18])).
% 1.19/0.52  % (18562)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 1.19/0.52  fof(f18,plain,(
% 1.19/0.52    ! [X0] : (! [X1] : (k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 1.19/0.52    inference(ennf_transformation,[],[f6])).
% 1.19/0.52  fof(f6,axiom,(
% 1.19/0.52    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1))))),
% 1.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_pre_topc)).
% 1.19/0.52  fof(f67,plain,(
% 1.19/0.52    l1_struct_0(sK0) | ~spl2_5),
% 1.19/0.52    inference(avatar_component_clause,[],[f65])).
% 1.19/0.52  fof(f86,plain,(
% 1.19/0.52    spl2_8 | ~spl2_3 | ~spl2_4),
% 1.19/0.52    inference(avatar_split_clause,[],[f81,f59,f54,f83])).
% 1.19/0.52  fof(f81,plain,(
% 1.19/0.52    k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0)) | (~spl2_3 | ~spl2_4)),
% 1.19/0.52    inference(unit_resulting_resolution,[],[f61,f56,f35])).
% 1.19/0.52  fof(f35,plain,(
% 1.19/0.52    ( ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.19/0.52    inference(cnf_transformation,[],[f17])).
% 1.19/0.52  fof(f17,plain,(
% 1.19/0.52    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.19/0.52    inference(flattening,[],[f16])).
% 1.19/0.52  fof(f16,plain,(
% 1.19/0.52    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.19/0.52    inference(ennf_transformation,[],[f7])).
% 1.19/0.52  % (18558)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 1.19/0.52  fof(f7,axiom,(
% 1.19/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 1.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).
% 1.19/0.52  fof(f80,plain,(
% 1.19/0.52    spl2_7 | ~spl2_2),
% 1.19/0.52    inference(avatar_split_clause,[],[f75,f49,f77])).
% 1.19/0.52  fof(f75,plain,(
% 1.19/0.52    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 1.19/0.52    inference(unit_resulting_resolution,[],[f51,f41])).
% 1.19/0.52  fof(f41,plain,(
% 1.19/0.52    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.19/0.52    inference(cnf_transformation,[],[f22])).
% 1.19/0.52  fof(f22,plain,(
% 1.19/0.52    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.19/0.52    inference(ennf_transformation,[],[f1])).
% 1.19/0.52  fof(f1,axiom,(
% 1.19/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.19/0.52  fof(f74,plain,(
% 1.19/0.52    spl2_6 | ~spl2_5),
% 1.19/0.52    inference(avatar_split_clause,[],[f69,f65,f71])).
% 1.19/0.52  fof(f69,plain,(
% 1.19/0.52    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_5),
% 1.19/0.52    inference(unit_resulting_resolution,[],[f67,f37])).
% 1.19/0.52  fof(f37,plain,(
% 1.19/0.52    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 1.19/0.52    inference(cnf_transformation,[],[f19])).
% 1.19/0.52  fof(f19,plain,(
% 1.19/0.52    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 1.19/0.52    inference(ennf_transformation,[],[f4])).
% 1.19/0.52  fof(f4,axiom,(
% 1.19/0.52    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).
% 1.19/0.52  fof(f68,plain,(
% 1.19/0.52    spl2_5 | ~spl2_3),
% 1.19/0.52    inference(avatar_split_clause,[],[f63,f54,f65])).
% 1.19/0.52  fof(f63,plain,(
% 1.19/0.52    l1_struct_0(sK0) | ~spl2_3),
% 1.19/0.52    inference(unit_resulting_resolution,[],[f56,f42])).
% 1.19/0.52  fof(f42,plain,(
% 1.19/0.52    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.19/0.52    inference(cnf_transformation,[],[f23])).
% 1.19/0.52  fof(f23,plain,(
% 1.19/0.52    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.19/0.52    inference(ennf_transformation,[],[f5])).
% 1.19/0.52  fof(f5,axiom,(
% 1.19/0.52    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.19/0.52  fof(f62,plain,(
% 1.19/0.52    spl2_4),
% 1.19/0.52    inference(avatar_split_clause,[],[f29,f59])).
% 1.19/0.52  fof(f29,plain,(
% 1.19/0.52    v2_pre_topc(sK0)),
% 1.19/0.52    inference(cnf_transformation,[],[f26])).
% 1.19/0.52  fof(f26,plain,(
% 1.19/0.52    (~m2_connsp_2(k2_struct_0(sK0),sK0,sK1) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f25,f24])).
% 1.19/0.52  fof(f24,plain,(
% 1.19/0.52    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~m2_connsp_2(k2_struct_0(sK0),sK0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.19/0.52    introduced(choice_axiom,[])).
% 1.19/0.52  fof(f25,plain,(
% 1.19/0.52    ? [X1] : (~m2_connsp_2(k2_struct_0(sK0),sK0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~m2_connsp_2(k2_struct_0(sK0),sK0,sK1) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.19/0.52    introduced(choice_axiom,[])).
% 1.19/0.52  fof(f13,plain,(
% 1.19/0.52    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.19/0.52    inference(flattening,[],[f12])).
% 1.19/0.52  fof(f12,plain,(
% 1.19/0.52    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.19/0.52    inference(ennf_transformation,[],[f11])).
% 1.19/0.52  fof(f11,plain,(
% 1.19/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 1.19/0.52    inference(pure_predicate_removal,[],[f10])).
% 1.19/0.52  fof(f10,negated_conjecture,(
% 1.19/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 1.19/0.52    inference(negated_conjecture,[],[f9])).
% 1.19/0.52  fof(f9,conjecture,(
% 1.19/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 1.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_connsp_2)).
% 1.19/0.52  fof(f57,plain,(
% 1.19/0.52    spl2_3),
% 1.19/0.52    inference(avatar_split_clause,[],[f30,f54])).
% 1.19/0.52  fof(f30,plain,(
% 1.19/0.52    l1_pre_topc(sK0)),
% 1.19/0.52    inference(cnf_transformation,[],[f26])).
% 1.19/0.52  fof(f52,plain,(
% 1.19/0.52    spl2_2),
% 1.19/0.52    inference(avatar_split_clause,[],[f31,f49])).
% 1.19/0.52  fof(f31,plain,(
% 1.19/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.19/0.52    inference(cnf_transformation,[],[f26])).
% 1.19/0.52  fof(f47,plain,(
% 1.19/0.52    ~spl2_1),
% 1.19/0.52    inference(avatar_split_clause,[],[f32,f44])).
% 1.19/0.52  fof(f32,plain,(
% 1.19/0.52    ~m2_connsp_2(k2_struct_0(sK0),sK0,sK1)),
% 1.19/0.52    inference(cnf_transformation,[],[f26])).
% 1.19/0.52  % SZS output end Proof for theBenchmark
% 1.19/0.52  % (18556)------------------------------
% 1.19/0.52  % (18556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.52  % (18556)Termination reason: Refutation
% 1.19/0.52  
% 1.19/0.52  % (18556)Memory used [KB]: 10746
% 1.19/0.52  % (18556)Time elapsed: 0.099 s
% 1.19/0.52  % (18556)------------------------------
% 1.19/0.52  % (18556)------------------------------
% 1.19/0.52  % (18560)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 1.19/0.52  % (18558)Refutation not found, incomplete strategy% (18558)------------------------------
% 1.19/0.52  % (18558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.52  % (18549)Success in time 0.156 s
%------------------------------------------------------------------------------
