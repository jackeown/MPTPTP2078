%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 936 expanded)
%              Number of leaves         :   14 ( 332 expanded)
%              Depth                    :   29
%              Number of atoms          :  339 (5595 expanded)
%              Number of equality atoms :   50 ( 991 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f237,plain,(
    $false ),
    inference(subsumption_resolution,[],[f236,f59])).

fof(f59,plain,(
    ! [X0] : ~ v1_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f39,f40])).

fof(f40,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f39,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).

fof(f236,plain,(
    v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f235,f34])).

fof(f34,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ v1_tex_2(sK2,sK0)
    & v1_tex_2(sK1,sK0)
    & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    & m1_pre_topc(sK2,sK0)
    & m1_pre_topc(sK1,sK0)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f23,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tex_2(X2,X0)
                & v1_tex_2(X1,X0)
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & m1_pre_topc(X2,X0) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,sK0)
              & v1_tex_2(X1,sK0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,sK0) )
          & m1_pre_topc(X1,sK0) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v1_tex_2(X2,sK0)
            & v1_tex_2(X1,sK0)
            & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
            & m1_pre_topc(X2,sK0) )
        & m1_pre_topc(X1,sK0) )
   => ( ? [X2] :
          ( ~ v1_tex_2(X2,sK0)
          & v1_tex_2(sK1,sK0)
          & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
          & m1_pre_topc(X2,sK0) )
      & m1_pre_topc(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( ~ v1_tex_2(X2,sK0)
        & v1_tex_2(sK1,sK0)
        & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        & m1_pre_topc(X2,sK0) )
   => ( ~ v1_tex_2(sK2,sK0)
      & v1_tex_2(sK1,sK0)
      & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      & m1_pre_topc(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( ( v1_tex_2(X1,X0)
                    & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                 => v1_tex_2(X2,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

% (23309)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% (23307)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% (23311)Refutation not found, incomplete strategy% (23311)------------------------------
% (23311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23311)Termination reason: Refutation not found, incomplete strategy

% (23311)Memory used [KB]: 6396
% (23311)Time elapsed: 0.103 s
% (23311)------------------------------
% (23311)------------------------------
% (23304)Termination reason: Refutation not found, incomplete strategy

% (23304)Memory used [KB]: 10618
% (23304)Time elapsed: 0.094 s
% (23304)------------------------------
% (23304)------------------------------
fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( ( v1_tex_2(X1,X0)
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
               => v1_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_tex_2)).

fof(f235,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f234,f37])).

fof(f37,plain,(
    v1_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f234,plain,
    ( ~ v1_tex_2(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f232,f118])).

fof(f118,plain,(
    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f115,f117])).

fof(f117,plain,(
    u1_struct_0(sK2) = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f116,f109])).

fof(f109,plain,(
    ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f108,f33])).

fof(f33,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f108,plain,
    ( ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f107,f35])).

fof(f35,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f107,plain,
    ( ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f106,f38])).

fof(f38,plain,(
    ~ v1_tex_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f106,plain,
    ( ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))
    | v1_tex_2(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f49,f83])).

fof(f83,plain,(
    u1_struct_0(sK2) = sK3(sK0,sK2) ),
    inference(subsumption_resolution,[],[f82,f33])).

fof(f82,plain,
    ( u1_struct_0(sK2) = sK3(sK0,sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f81,f35])).

fof(f81,plain,
    ( u1_struct_0(sK2) = sK3(sK0,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f48,f38])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | u1_struct_0(X1) = sK3(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & u1_struct_0(X1) = sK3(X0,X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK3(X0,X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v1_subset_1(X2,u1_struct_0(X0))
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f116,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK0)
    | v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f115,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f115,plain,(
    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f114,f33])).

fof(f114,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f113,f35])).

fof(f113,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f111,f38])).

% (23316)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
fof(f111,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tex_2(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f47,f83])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f232,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_tex_2(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(superposition,[],[f223,f168])).

fof(f168,plain,(
    u1_struct_0(sK1) = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f167,f61])).

fof(f61,plain,(
    l1_pre_topc(sK1) ),
    inference(resolution,[],[f60,f34])).

fof(f60,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f44,f33])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f167,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK0)
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f165,f104])).

fof(f104,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(subsumption_resolution,[],[f103,f62])).

fof(f62,plain,(
    l1_pre_topc(sK2) ),
    inference(resolution,[],[f60,f35])).

fof(f103,plain,
    ( m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f102,f41])).

fof(f41,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f102,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | m1_pre_topc(sK2,sK1) ),
    inference(subsumption_resolution,[],[f99,f61])).

fof(f99,plain,
    ( ~ l1_pre_topc(sK1)
    | m1_pre_topc(sK2,sK1)
    | ~ m1_pre_topc(sK2,sK2) ),
    inference(resolution,[],[f74,f71])).

fof(f71,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ m1_pre_topc(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f70,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f62,f44])).

fof(f70,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ m1_pre_topc(X0,sK2)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f69,f62])).

fof(f69,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ m1_pre_topc(X0,sK2)
      | ~ l1_pre_topc(sK2)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f42,f36])).

fof(f36,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f74,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X2)
      | m1_pre_topc(sK2,X2) ) ),
    inference(resolution,[],[f43,f62])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | m1_pre_topc(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f165,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK0)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f164,f126])).

fof(f126,plain,(
    ! [X1] :
      ( r1_tarski(u1_struct_0(sK0),u1_struct_0(X1))
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(superposition,[],[f45,f117])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f164,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))
    | u1_struct_0(sK1) = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f163,f61])).

fof(f163,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK0)
    | ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f161,f41])).

fof(f161,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | u1_struct_0(sK1) = u1_struct_0(sK0)
    | ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(resolution,[],[f139,f96])).

fof(f96,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ m1_pre_topc(sK1,sK1) ),
    inference(subsumption_resolution,[],[f95,f61])).

fof(f95,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(duplicate_literal_removal,[],[f94])).

fof(f94,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f92,f42])).

fof(f92,plain,
    ( ~ m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | m1_pre_topc(sK1,sK2) ),
    inference(subsumption_resolution,[],[f90,f62])).

fof(f90,plain,
    ( ~ m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK2)
    | m1_pre_topc(sK1,sK2) ),
    inference(superposition,[],[f73,f36])).

fof(f73,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | m1_pre_topc(sK1,X1) ) ),
    inference(resolution,[],[f43,f61])).

fof(f139,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(X0))
      | u1_struct_0(X0) = u1_struct_0(sK0) ) ),
    inference(resolution,[],[f133,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f133,plain,(
    ! [X2] :
      ( r1_tarski(u1_struct_0(X2),u1_struct_0(sK0))
      | ~ m1_pre_topc(X2,sK2) ) ),
    inference(subsumption_resolution,[],[f127,f62])).

fof(f127,plain,(
    ! [X2] :
      ( r1_tarski(u1_struct_0(X2),u1_struct_0(sK0))
      | ~ m1_pre_topc(X2,sK2)
      | ~ l1_pre_topc(sK2) ) ),
    inference(superposition,[],[f45,f117])).

fof(f223,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_tex_2(X0,sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v1_subset_1(u1_struct_0(X0),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f55,f33])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( v1_subset_1(X3,u1_struct_0(X0))
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:27:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (23303)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.49  % (23310)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.49  % (23311)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (23301)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (23304)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (23302)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (23321)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.50  % (23318)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.50  % (23313)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.50  % (23301)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (23304)Refutation not found, incomplete strategy% (23304)------------------------------
% 0.21/0.50  % (23304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (23305)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (23319)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (23320)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (23308)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (23306)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (23322)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.51  % (23300)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (23299)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (23315)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.51  % (23298)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f237,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f236,f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_subset_1(X0,X0)) )),
% 0.21/0.52    inference(backward_demodulation,[],[f39,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).
% 0.21/0.52  fof(f236,plain,(
% 0.21/0.52    v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))),
% 0.21/0.52    inference(subsumption_resolution,[],[f235,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    m1_pre_topc(sK1,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ((~v1_tex_2(sK2,sK0) & v1_tex_2(sK1,sK0) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_pre_topc(sK2,sK0)) & m1_pre_topc(sK1,sK0)) & l1_pre_topc(sK0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f23,f22,f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tex_2(X2,sK0) & v1_tex_2(X1,sK0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(X1,sK0)) & l1_pre_topc(sK0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ? [X1] : (? [X2] : (~v1_tex_2(X2,sK0) & v1_tex_2(X1,sK0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(X1,sK0)) => (? [X2] : (~v1_tex_2(X2,sK0) & v1_tex_2(sK1,sK0) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(sK1,sK0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ? [X2] : (~v1_tex_2(X2,sK0) & v1_tex_2(sK1,sK0) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_pre_topc(X2,sK0)) => (~v1_tex_2(sK2,sK0) & v1_tex_2(sK1,sK0) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_pre_topc(sK2,sK0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : ((~v1_tex_2(X2,X0) & (v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,negated_conjecture,(
% 0.21/0.52    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ((v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) => v1_tex_2(X2,X0)))))),
% 0.21/0.52    inference(negated_conjecture,[],[f10])).
% 0.21/0.52  % (23309)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (23307)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (23311)Refutation not found, incomplete strategy% (23311)------------------------------
% 0.21/0.52  % (23311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (23311)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (23311)Memory used [KB]: 6396
% 0.21/0.52  % (23311)Time elapsed: 0.103 s
% 0.21/0.52  % (23311)------------------------------
% 0.21/0.52  % (23311)------------------------------
% 0.21/0.52  % (23304)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (23304)Memory used [KB]: 10618
% 0.21/0.52  % (23304)Time elapsed: 0.094 s
% 0.21/0.52  % (23304)------------------------------
% 0.21/0.52  % (23304)------------------------------
% 0.21/0.52  fof(f10,conjecture,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ((v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) => v1_tex_2(X2,X0)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_tex_2)).
% 0.21/0.52  fof(f235,plain,(
% 0.21/0.52    ~m1_pre_topc(sK1,sK0) | v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))),
% 0.21/0.52    inference(subsumption_resolution,[],[f234,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    v1_tex_2(sK1,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f234,plain,(
% 0.21/0.52    ~v1_tex_2(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))),
% 0.21/0.52    inference(subsumption_resolution,[],[f232,f118])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    inference(backward_demodulation,[],[f115,f117])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    u1_struct_0(sK2) = u1_struct_0(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f116,f109])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    ~v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))),
% 0.21/0.52    inference(subsumption_resolution,[],[f108,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    l1_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    ~v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f107,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    m1_pre_topc(sK2,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    ~v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0)) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f106,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ~v1_tex_2(sK2,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    ~v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0)) | v1_tex_2(sK2,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.52    inference(superposition,[],[f49,f83])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    u1_struct_0(sK2) = sK3(sK0,sK2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f82,f33])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    u1_struct_0(sK2) = sK3(sK0,sK2) | ~l1_pre_topc(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f81,f35])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    u1_struct_0(sK2) = sK3(sK0,sK2) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.52    inference(resolution,[],[f48,f38])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_tex_2(X1,X0) | u1_struct_0(X1) = sK3(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK3(X0,X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK3(X0,X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(rectify,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    u1_struct_0(sK2) = u1_struct_0(sK0) | v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))),
% 0.21/0.52    inference(resolution,[],[f115,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(nnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f114,f33])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f113,f35])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f111,f38])).
% 0.21/0.52  % (23316)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tex_2(sK2,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.52    inference(superposition,[],[f47,f83])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f232,plain,(
% 0.21/0.52    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tex_2(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))),
% 0.21/0.52    inference(superposition,[],[f223,f168])).
% 0.21/0.52  fof(f168,plain,(
% 0.21/0.52    u1_struct_0(sK1) = u1_struct_0(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f167,f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    l1_pre_topc(sK1)),
% 0.21/0.52    inference(resolution,[],[f60,f34])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) )),
% 0.21/0.52    inference(resolution,[],[f44,f33])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.52  fof(f167,plain,(
% 0.21/0.52    u1_struct_0(sK1) = u1_struct_0(sK0) | ~l1_pre_topc(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f165,f104])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    m1_pre_topc(sK2,sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f103,f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    l1_pre_topc(sK2)),
% 0.21/0.52    inference(resolution,[],[f60,f35])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    m1_pre_topc(sK2,sK1) | ~l1_pre_topc(sK2)),
% 0.21/0.52    inference(resolution,[],[f102,f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    ~m1_pre_topc(sK2,sK2) | m1_pre_topc(sK2,sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f99,f61])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    ~l1_pre_topc(sK1) | m1_pre_topc(sK2,sK1) | ~m1_pre_topc(sK2,sK2)),
% 0.21/0.52    inference(resolution,[],[f74,f71])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    ( ! [X0] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_pre_topc(X0,sK2)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f70,f65])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_pre_topc(X0,sK2) | l1_pre_topc(X0)) )),
% 0.21/0.52    inference(resolution,[],[f62,f44])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    ( ! [X0] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_pre_topc(X0,sK2) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f69,f62])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ( ! [X0] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_pre_topc(X0,sK2) | ~l1_pre_topc(sK2) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(superposition,[],[f42,f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    ( ! [X2] : (~m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X2) | m1_pre_topc(sK2,X2)) )),
% 0.21/0.52    inference(resolution,[],[f43,f62])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | m1_pre_topc(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f165,plain,(
% 0.21/0.52    u1_struct_0(sK1) = u1_struct_0(sK0) | ~m1_pre_topc(sK2,sK1) | ~l1_pre_topc(sK1)),
% 0.21/0.52    inference(resolution,[],[f164,f126])).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(X1)) )),
% 0.21/0.52    inference(superposition,[],[f45,f117])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) | u1_struct_0(sK1) = u1_struct_0(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f163,f61])).
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    u1_struct_0(sK1) = u1_struct_0(sK0) | ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1)),
% 0.21/0.52    inference(resolution,[],[f161,f41])).
% 0.21/0.52  fof(f161,plain,(
% 0.21/0.52    ~m1_pre_topc(sK1,sK1) | u1_struct_0(sK1) = u1_struct_0(sK0) | ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.52    inference(resolution,[],[f139,f96])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    m1_pre_topc(sK1,sK2) | ~m1_pre_topc(sK1,sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f95,f61])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    m1_pre_topc(sK1,sK2) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1)),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f94])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    m1_pre_topc(sK1,sK2) | ~m1_pre_topc(sK1,sK1) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK1)),
% 0.21/0.52    inference(resolution,[],[f92,f42])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    ~m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | m1_pre_topc(sK1,sK2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f90,f62])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    ~m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK2) | m1_pre_topc(sK1,sK2)),
% 0.21/0.52    inference(superposition,[],[f73,f36])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ( ! [X1] : (~m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | m1_pre_topc(sK1,X1)) )),
% 0.21/0.52    inference(resolution,[],[f43,f61])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_pre_topc(X0,sK2) | ~r1_tarski(u1_struct_0(sK0),u1_struct_0(X0)) | u1_struct_0(X0) = u1_struct_0(sK0)) )),
% 0.21/0.52    inference(resolution,[],[f133,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(flattening,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    ( ! [X2] : (r1_tarski(u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_pre_topc(X2,sK2)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f127,f62])).
% 0.21/0.52  fof(f127,plain,(
% 0.21/0.52    ( ! [X2] : (r1_tarski(u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_pre_topc(X2,sK2) | ~l1_pre_topc(sK2)) )),
% 0.21/0.52    inference(superposition,[],[f45,f117])).
% 0.21/0.52  fof(f223,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tex_2(X0,sK0) | ~m1_pre_topc(X0,sK0) | v1_subset_1(u1_struct_0(X0),u1_struct_0(sK0))) )),
% 0.21/0.52    inference(resolution,[],[f55,f33])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))) )),
% 0.21/0.52    inference(equality_resolution,[],[f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (23301)------------------------------
% 0.21/0.52  % (23301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (23301)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (23301)Memory used [KB]: 6268
% 0.21/0.52  % (23301)Time elapsed: 0.101 s
% 0.21/0.52  % (23301)------------------------------
% 0.21/0.52  % (23301)------------------------------
% 0.21/0.52  % (23297)Success in time 0.165 s
%------------------------------------------------------------------------------
