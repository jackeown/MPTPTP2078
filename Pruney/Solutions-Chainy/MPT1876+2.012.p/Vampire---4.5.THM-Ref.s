%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:37 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :  158 (1766 expanded)
%              Number of leaves         :   22 ( 476 expanded)
%              Depth                    :   33
%              Number of atoms          :  637 (14790 expanded)
%              Number of equality atoms :   21 ( 116 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f641,plain,(
    $false ),
    inference(subsumption_resolution,[],[f640,f146])).

fof(f146,plain,(
    r2_hidden(sK3(sK1),sK1) ),
    inference(resolution,[],[f66,f88])).

fof(f88,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f54,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
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

fof(f66,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f47,f49,f48])).

fof(f48,plain,
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

fof(f49,plain,
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

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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

fof(f640,plain,(
    ~ r2_hidden(sK3(sK1),sK1) ),
    inference(subsumption_resolution,[],[f623,f383])).

fof(f383,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f382,f69])).

fof(f69,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f382,plain,
    ( v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f381,f62])).

fof(f62,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f381,plain,
    ( v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f380,f63])).

% (31875)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f63,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f380,plain,
    ( v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f379,f65])).

fof(f65,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f379,plain,
    ( v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f378,f66])).

fof(f378,plain,
    ( v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f377,f67])).

fof(f67,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f50])).

fof(f377,plain,
    ( v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f376])).

fof(f376,plain,
    ( v1_zfmisc_1(sK1)
    | v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f287,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK2(X0,X1)) = X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK2(X0,X1)) = X1
            & m1_pre_topc(sK2(X0,X1),X0)
            & v1_tdlat_3(sK2(X0,X1))
            & v1_pre_topc(sK2(X0,X1))
            & ~ v2_struct_0(sK2(X0,X1)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f51])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_tdlat_3(X2)
          & v1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK2(X0,X1)) = X1
        & m1_pre_topc(sK2(X0,X1),X0)
        & v1_tdlat_3(sK2(X0,X1))
        & v1_pre_topc(sK2(X0,X1))
        & ~ v2_struct_0(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

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

fof(f287,plain,
    ( v1_zfmisc_1(u1_struct_0(sK2(sK0,sK1)))
    | v1_zfmisc_1(sK1) ),
    inference(subsumption_resolution,[],[f285,f268])).

fof(f268,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1) ),
    inference(subsumption_resolution,[],[f267,f194])).

fof(f194,plain,
    ( ~ v2_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1) ),
    inference(subsumption_resolution,[],[f193,f62])).

fof(f193,plain,
    ( v1_zfmisc_1(sK1)
    | ~ v2_struct_0(sK2(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f192,f63])).

fof(f192,plain,
    ( v1_zfmisc_1(sK1)
    | ~ v2_struct_0(sK2(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f191,f65])).

fof(f191,plain,
    ( v1_zfmisc_1(sK1)
    | ~ v2_struct_0(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f190,f66])).

fof(f190,plain,
    ( v1_zfmisc_1(sK1)
    | ~ v2_struct_0(sK2(sK0,sK1))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f186,f67])).

fof(f186,plain,
    ( v1_zfmisc_1(sK1)
    | ~ v2_struct_0(sK2(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f68,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f68,plain,
    ( v2_tex_2(sK1,sK0)
    | v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f267,plain,
    ( v1_zfmisc_1(sK1)
    | v7_struct_0(sK2(sK0,sK1))
    | v2_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f266,f264])).

fof(f264,plain,
    ( v2_pre_topc(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1) ),
    inference(subsumption_resolution,[],[f255,f251])).

fof(f251,plain,
    ( v2_tdlat_3(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f204,f109])).

fof(f109,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_tdlat_3(X0) ) ),
    inference(subsumption_resolution,[],[f108,f63])).

fof(f108,plain,(
    ! [X0] :
      ( v2_tdlat_3(X0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f107,f64])).

fof(f64,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f107,plain,(
    ! [X0] :
      ( v2_tdlat_3(X0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ v2_tdlat_3(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f98,f65])).

fof(f98,plain,(
    ! [X0] :
      ( v2_tdlat_3(X0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_tdlat_3(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f62,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v2_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

% (31890)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
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

fof(f204,plain,
    ( m1_pre_topc(sK2(sK0,sK1),sK0)
    | v1_zfmisc_1(sK1) ),
    inference(subsumption_resolution,[],[f203,f62])).

fof(f203,plain,
    ( v1_zfmisc_1(sK1)
    | m1_pre_topc(sK2(sK0,sK1),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f202,f63])).

fof(f202,plain,
    ( v1_zfmisc_1(sK1)
    | m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f201,f65])).

fof(f201,plain,
    ( v1_zfmisc_1(sK1)
    | m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f200,f66])).

fof(f200,plain,
    ( v1_zfmisc_1(sK1)
    | m1_pre_topc(sK2(sK0,sK1),sK0)
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f188,f67])).

fof(f188,plain,
    ( v1_zfmisc_1(sK1)
    | m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f68,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK2(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f255,plain,
    ( v1_zfmisc_1(sK1)
    | v2_pre_topc(sK2(sK0,sK1))
    | ~ v2_tdlat_3(sK2(sK0,sK1)) ),
    inference(resolution,[],[f250,f74])).

fof(f74,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f250,plain,
    ( l1_pre_topc(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f204,f133])).

fof(f133,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f65,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f266,plain,
    ( v1_zfmisc_1(sK1)
    | v7_struct_0(sK2(sK0,sK1))
    | ~ v2_pre_topc(sK2(sK0,sK1))
    | v2_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f265,f199])).

fof(f199,plain,
    ( v1_tdlat_3(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1) ),
    inference(subsumption_resolution,[],[f198,f62])).

fof(f198,plain,
    ( v1_zfmisc_1(sK1)
    | v1_tdlat_3(sK2(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f197,f63])).

fof(f197,plain,
    ( v1_zfmisc_1(sK1)
    | v1_tdlat_3(sK2(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f196,f65])).

fof(f196,plain,
    ( v1_zfmisc_1(sK1)
    | v1_tdlat_3(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f195,f66])).

fof(f195,plain,
    ( v1_zfmisc_1(sK1)
    | v1_tdlat_3(sK2(sK0,sK1))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f187,f67])).

fof(f187,plain,
    ( v1_zfmisc_1(sK1)
    | v1_tdlat_3(sK2(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f68,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f265,plain,
    ( v1_zfmisc_1(sK1)
    | v7_struct_0(sK2(sK0,sK1))
    | ~ v1_tdlat_3(sK2(sK0,sK1))
    | ~ v2_pre_topc(sK2(sK0,sK1))
    | v2_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f256,f251])).

fof(f256,plain,
    ( v1_zfmisc_1(sK1)
    | v7_struct_0(sK2(sK0,sK1))
    | ~ v2_tdlat_3(sK2(sK0,sK1))
    | ~ v1_tdlat_3(sK2(sK0,sK1))
    | ~ v2_pre_topc(sK2(sK0,sK1))
    | v2_struct_0(sK2(sK0,sK1)) ),
    inference(resolution,[],[f250,f76])).

fof(f76,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

fof(f285,plain,
    ( v1_zfmisc_1(sK1)
    | v1_zfmisc_1(u1_struct_0(sK2(sK0,sK1)))
    | ~ v7_struct_0(sK2(sK0,sK1)) ),
    inference(resolution,[],[f254,f86])).

fof(f86,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f254,plain,
    ( l1_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f250,f73])).

fof(f73,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f623,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ r2_hidden(sK3(sK1),sK1) ),
    inference(superposition,[],[f618,f396])).

fof(f396,plain,(
    sK1 = k1_tarski(sK3(sK1)) ),
    inference(resolution,[],[f238,f384])).

fof(f384,plain,(
    v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f383,f68])).

fof(f238,plain,
    ( ~ v1_zfmisc_1(sK1)
    | sK1 = k1_tarski(sK3(sK1)) ),
    inference(subsumption_resolution,[],[f237,f70])).

fof(f70,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f237,plain,
    ( sK1 = k1_tarski(sK3(sK1))
    | ~ v1_zfmisc_1(sK1)
    | v1_xboole_0(k1_tarski(sK3(sK1))) ),
    inference(subsumption_resolution,[],[f236,f66])).

fof(f236,plain,
    ( sK1 = k1_tarski(sK3(sK1))
    | ~ v1_zfmisc_1(sK1)
    | v1_xboole_0(sK1)
    | v1_xboole_0(k1_tarski(sK3(sK1))) ),
    inference(resolution,[],[f231,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f231,plain,(
    r1_tarski(k1_tarski(sK3(sK1)),sK1) ),
    inference(resolution,[],[f158,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f158,plain,(
    m1_subset_1(k1_tarski(sK3(sK1)),k1_zfmisc_1(sK1)) ),
    inference(backward_demodulation,[],[f156,f157])).

fof(f157,plain,(
    k6_domain_1(sK1,sK3(sK1)) = k1_tarski(sK3(sK1)) ),
    inference(subsumption_resolution,[],[f155,f66])).

fof(f155,plain,
    ( k6_domain_1(sK1,sK3(sK1)) = k1_tarski(sK3(sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f152,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
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

fof(f152,plain,(
    m1_subset_1(sK3(sK1),sK1) ),
    inference(resolution,[],[f146,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f156,plain,(
    m1_subset_1(k6_domain_1(sK1,sK3(sK1)),k1_zfmisc_1(sK1)) ),
    inference(subsumption_resolution,[],[f154,f66])).

fof(f154,plain,
    ( m1_subset_1(k6_domain_1(sK1,sK3(sK1)),k1_zfmisc_1(sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f152,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f618,plain,(
    ! [X0] :
      ( v2_tex_2(k1_tarski(X0),sK0)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f617,f354])).

fof(f354,plain,(
    ! [X2] :
      ( m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,sK1) ) ),
    inference(resolution,[],[f183,f89])).

fof(f183,plain,(
    ! [X0] :
      ( r2_hidden(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f163,f92])).

fof(f92,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

% (31901)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f60,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f58,f59])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f163,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f67,f95])).

fof(f617,plain,(
    ! [X0] :
      ( v2_tex_2(k1_tarski(X0),sK0)
      | ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f600,f299])).

fof(f299,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f298,f163])).

fof(f298,plain,(
    ! [X3] :
      ( ~ r1_tarski(sK1,X3)
      | ~ v1_xboole_0(X3) ) ),
    inference(resolution,[],[f151,f87])).

fof(f87,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f151,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK1),X0)
      | ~ r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f146,f92])).

fof(f600,plain,(
    ! [X0] :
      ( v2_tex_2(k1_tarski(X0),sK0)
      | ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f372,f90])).

fof(f372,plain,(
    ! [X0] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f371,f62])).

fof(f371,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f370,f63])).

fof(f370,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f367,f65])).

fof(f367,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f354,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:49:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (31878)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (31894)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (31886)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (31877)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (31882)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (31894)Refutation not found, incomplete strategy% (31894)------------------------------
% 0.21/0.52  % (31894)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31894)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31894)Memory used [KB]: 10746
% 0.21/0.52  % (31894)Time elapsed: 0.108 s
% 0.21/0.52  % (31894)------------------------------
% 0.21/0.52  % (31894)------------------------------
% 0.21/0.52  % (31882)Refutation not found, incomplete strategy% (31882)------------------------------
% 0.21/0.52  % (31882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31882)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31882)Memory used [KB]: 10618
% 0.21/0.52  % (31882)Time elapsed: 0.106 s
% 0.21/0.52  % (31882)------------------------------
% 0.21/0.52  % (31882)------------------------------
% 0.21/0.52  % (31895)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (31887)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.28/0.53  % (31895)Refutation found. Thanks to Tanya!
% 1.28/0.53  % SZS status Theorem for theBenchmark
% 1.28/0.53  % (31898)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.28/0.53  % (31883)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.28/0.54  % (31874)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.28/0.54  % (31883)Refutation not found, incomplete strategy% (31883)------------------------------
% 1.28/0.54  % (31883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (31883)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (31883)Memory used [KB]: 10618
% 1.28/0.54  % (31883)Time elapsed: 0.112 s
% 1.28/0.54  % (31883)------------------------------
% 1.28/0.54  % (31883)------------------------------
% 1.28/0.54  % (31874)Refutation not found, incomplete strategy% (31874)------------------------------
% 1.28/0.54  % (31874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (31874)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (31874)Memory used [KB]: 10746
% 1.28/0.54  % (31874)Time elapsed: 0.128 s
% 1.28/0.54  % (31874)------------------------------
% 1.28/0.54  % (31874)------------------------------
% 1.28/0.54  % (31872)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.28/0.54  % (31899)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.39/0.54  % (31891)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.39/0.55  % SZS output start Proof for theBenchmark
% 1.39/0.55  fof(f641,plain,(
% 1.39/0.55    $false),
% 1.39/0.55    inference(subsumption_resolution,[],[f640,f146])).
% 1.39/0.55  fof(f146,plain,(
% 1.39/0.55    r2_hidden(sK3(sK1),sK1)),
% 1.39/0.55    inference(resolution,[],[f66,f88])).
% 1.39/0.55  fof(f88,plain,(
% 1.39/0.55    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f56])).
% 1.39/0.55  fof(f56,plain,(
% 1.39/0.55    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.39/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f54,f55])).
% 1.39/0.55  fof(f55,plain,(
% 1.39/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.39/0.55    introduced(choice_axiom,[])).
% 1.39/0.55  fof(f54,plain,(
% 1.39/0.55    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.39/0.55    inference(rectify,[],[f53])).
% 1.39/0.55  fof(f53,plain,(
% 1.39/0.55    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.39/0.55    inference(nnf_transformation,[],[f1])).
% 1.39/0.55  fof(f1,axiom,(
% 1.39/0.55    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.39/0.55  fof(f66,plain,(
% 1.39/0.55    ~v1_xboole_0(sK1)),
% 1.39/0.55    inference(cnf_transformation,[],[f50])).
% 1.39/0.55  fof(f50,plain,(
% 1.39/0.55    ((~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.39/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f47,f49,f48])).
% 1.39/0.55  fof(f48,plain,(
% 1.39/0.55    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.39/0.55    introduced(choice_axiom,[])).
% 1.39/0.55  fof(f49,plain,(
% 1.39/0.55    ? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1))),
% 1.39/0.55    introduced(choice_axiom,[])).
% 1.39/0.55  fof(f47,plain,(
% 1.39/0.55    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.39/0.55    inference(flattening,[],[f46])).
% 1.39/0.55  fof(f46,plain,(
% 1.39/0.55    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.39/0.55    inference(nnf_transformation,[],[f21])).
% 1.39/0.55  fof(f21,plain,(
% 1.39/0.55    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.39/0.55    inference(flattening,[],[f20])).
% 1.39/0.55  fof(f20,plain,(
% 1.39/0.55    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.39/0.55    inference(ennf_transformation,[],[f19])).
% 1.39/0.55  fof(f19,negated_conjecture,(
% 1.39/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.39/0.55    inference(negated_conjecture,[],[f18])).
% 1.39/0.55  fof(f18,conjecture,(
% 1.39/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).
% 1.39/0.55  fof(f640,plain,(
% 1.39/0.55    ~r2_hidden(sK3(sK1),sK1)),
% 1.39/0.55    inference(subsumption_resolution,[],[f623,f383])).
% 1.39/0.55  fof(f383,plain,(
% 1.39/0.55    ~v2_tex_2(sK1,sK0)),
% 1.39/0.55    inference(subsumption_resolution,[],[f382,f69])).
% 1.39/0.55  fof(f69,plain,(
% 1.39/0.55    ~v2_tex_2(sK1,sK0) | ~v1_zfmisc_1(sK1)),
% 1.39/0.55    inference(cnf_transformation,[],[f50])).
% 1.39/0.55  fof(f382,plain,(
% 1.39/0.55    v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)),
% 1.39/0.55    inference(subsumption_resolution,[],[f381,f62])).
% 1.39/0.55  fof(f62,plain,(
% 1.39/0.55    ~v2_struct_0(sK0)),
% 1.39/0.55    inference(cnf_transformation,[],[f50])).
% 1.39/0.55  fof(f381,plain,(
% 1.39/0.55    v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0) | v2_struct_0(sK0)),
% 1.39/0.55    inference(subsumption_resolution,[],[f380,f63])).
% 1.39/0.55  % (31875)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.39/0.55  fof(f63,plain,(
% 1.39/0.55    v2_pre_topc(sK0)),
% 1.39/0.55    inference(cnf_transformation,[],[f50])).
% 1.39/0.55  fof(f380,plain,(
% 1.39/0.55    v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.39/0.55    inference(subsumption_resolution,[],[f379,f65])).
% 1.39/0.55  fof(f65,plain,(
% 1.39/0.55    l1_pre_topc(sK0)),
% 1.39/0.55    inference(cnf_transformation,[],[f50])).
% 1.39/0.55  fof(f379,plain,(
% 1.39/0.55    v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.39/0.55    inference(subsumption_resolution,[],[f378,f66])).
% 1.39/0.55  fof(f378,plain,(
% 1.39/0.55    v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.39/0.55    inference(subsumption_resolution,[],[f377,f67])).
% 1.39/0.55  fof(f67,plain,(
% 1.39/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.39/0.55    inference(cnf_transformation,[],[f50])).
% 1.39/0.55  fof(f377,plain,(
% 1.39/0.55    v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.39/0.55    inference(duplicate_literal_removal,[],[f376])).
% 1.39/0.55  fof(f376,plain,(
% 1.39/0.55    v1_zfmisc_1(sK1) | v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.39/0.55    inference(superposition,[],[f287,f85])).
% 1.39/0.55  fof(f85,plain,(
% 1.39/0.55    ( ! [X0,X1] : (u1_struct_0(sK2(X0,X1)) = X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f52])).
% 1.39/0.55  fof(f52,plain,(
% 1.39/0.55    ! [X0] : (! [X1] : ((u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_tdlat_3(sK2(X0,X1)) & v1_pre_topc(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.39/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f51])).
% 1.39/0.55  fof(f51,plain,(
% 1.39/0.55    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_tdlat_3(sK2(X0,X1)) & v1_pre_topc(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))))),
% 1.39/0.55    introduced(choice_axiom,[])).
% 1.39/0.55  fof(f37,plain,(
% 1.39/0.55    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.39/0.55    inference(flattening,[],[f36])).
% 1.39/0.55  fof(f36,plain,(
% 1.39/0.55    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.39/0.55    inference(ennf_transformation,[],[f16])).
% 1.39/0.55  fof(f16,axiom,(
% 1.39/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).
% 1.39/0.55  fof(f287,plain,(
% 1.39/0.55    v1_zfmisc_1(u1_struct_0(sK2(sK0,sK1))) | v1_zfmisc_1(sK1)),
% 1.39/0.55    inference(subsumption_resolution,[],[f285,f268])).
% 1.39/0.55  fof(f268,plain,(
% 1.39/0.55    v7_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(sK1)),
% 1.39/0.55    inference(subsumption_resolution,[],[f267,f194])).
% 1.39/0.55  fof(f194,plain,(
% 1.39/0.55    ~v2_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(sK1)),
% 1.39/0.55    inference(subsumption_resolution,[],[f193,f62])).
% 1.39/0.55  fof(f193,plain,(
% 1.39/0.55    v1_zfmisc_1(sK1) | ~v2_struct_0(sK2(sK0,sK1)) | v2_struct_0(sK0)),
% 1.39/0.55    inference(subsumption_resolution,[],[f192,f63])).
% 1.39/0.55  fof(f192,plain,(
% 1.39/0.55    v1_zfmisc_1(sK1) | ~v2_struct_0(sK2(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.39/0.55    inference(subsumption_resolution,[],[f191,f65])).
% 1.39/0.55  fof(f191,plain,(
% 1.39/0.55    v1_zfmisc_1(sK1) | ~v2_struct_0(sK2(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.39/0.55    inference(subsumption_resolution,[],[f190,f66])).
% 1.39/0.55  fof(f190,plain,(
% 1.39/0.55    v1_zfmisc_1(sK1) | ~v2_struct_0(sK2(sK0,sK1)) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.39/0.55    inference(subsumption_resolution,[],[f186,f67])).
% 1.39/0.55  fof(f186,plain,(
% 1.39/0.55    v1_zfmisc_1(sK1) | ~v2_struct_0(sK2(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.39/0.55    inference(resolution,[],[f68,f81])).
% 1.39/0.55  fof(f81,plain,(
% 1.39/0.55    ( ! [X0,X1] : (~v2_struct_0(sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f52])).
% 1.39/0.55  fof(f68,plain,(
% 1.39/0.55    v2_tex_2(sK1,sK0) | v1_zfmisc_1(sK1)),
% 1.39/0.55    inference(cnf_transformation,[],[f50])).
% 1.39/0.55  fof(f267,plain,(
% 1.39/0.55    v1_zfmisc_1(sK1) | v7_struct_0(sK2(sK0,sK1)) | v2_struct_0(sK2(sK0,sK1))),
% 1.39/0.55    inference(subsumption_resolution,[],[f266,f264])).
% 1.39/0.55  fof(f264,plain,(
% 1.39/0.55    v2_pre_topc(sK2(sK0,sK1)) | v1_zfmisc_1(sK1)),
% 1.39/0.55    inference(subsumption_resolution,[],[f255,f251])).
% 1.39/0.55  fof(f251,plain,(
% 1.39/0.55    v2_tdlat_3(sK2(sK0,sK1)) | v1_zfmisc_1(sK1)),
% 1.39/0.55    inference(resolution,[],[f204,f109])).
% 1.39/0.55  fof(f109,plain,(
% 1.39/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_tdlat_3(X0)) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f108,f63])).
% 1.39/0.55  fof(f108,plain,(
% 1.39/0.55    ( ! [X0] : (v2_tdlat_3(X0) | ~m1_pre_topc(X0,sK0) | ~v2_pre_topc(sK0)) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f107,f64])).
% 1.39/0.55  fof(f64,plain,(
% 1.39/0.55    v2_tdlat_3(sK0)),
% 1.39/0.55    inference(cnf_transformation,[],[f50])).
% 1.39/0.55  fof(f107,plain,(
% 1.39/0.55    ( ! [X0] : (v2_tdlat_3(X0) | ~m1_pre_topc(X0,sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0)) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f98,f65])).
% 1.39/0.55  fof(f98,plain,(
% 1.39/0.55    ( ! [X0] : (v2_tdlat_3(X0) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0)) )),
% 1.39/0.55    inference(resolution,[],[f62,f79])).
% 1.39/0.55  fof(f79,plain,(
% 1.39/0.55    ( ! [X0,X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f33])).
% 1.39/0.55  fof(f33,plain,(
% 1.39/0.55    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.39/0.55    inference(flattening,[],[f32])).
% 1.39/0.55  fof(f32,plain,(
% 1.39/0.55    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.39/0.55    inference(ennf_transformation,[],[f14])).
% 1.39/0.55  % (31890)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.39/0.55  fof(f14,axiom,(
% 1.39/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_tdlat_3(X1)))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tdlat_3)).
% 1.39/0.55  fof(f204,plain,(
% 1.39/0.55    m1_pre_topc(sK2(sK0,sK1),sK0) | v1_zfmisc_1(sK1)),
% 1.39/0.55    inference(subsumption_resolution,[],[f203,f62])).
% 1.39/0.55  fof(f203,plain,(
% 1.39/0.55    v1_zfmisc_1(sK1) | m1_pre_topc(sK2(sK0,sK1),sK0) | v2_struct_0(sK0)),
% 1.39/0.55    inference(subsumption_resolution,[],[f202,f63])).
% 1.39/0.55  fof(f202,plain,(
% 1.39/0.55    v1_zfmisc_1(sK1) | m1_pre_topc(sK2(sK0,sK1),sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.39/0.55    inference(subsumption_resolution,[],[f201,f65])).
% 1.39/0.55  fof(f201,plain,(
% 1.39/0.55    v1_zfmisc_1(sK1) | m1_pre_topc(sK2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.39/0.55    inference(subsumption_resolution,[],[f200,f66])).
% 1.39/0.55  fof(f200,plain,(
% 1.39/0.55    v1_zfmisc_1(sK1) | m1_pre_topc(sK2(sK0,sK1),sK0) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.39/0.55    inference(subsumption_resolution,[],[f188,f67])).
% 1.39/0.55  fof(f188,plain,(
% 1.39/0.55    v1_zfmisc_1(sK1) | m1_pre_topc(sK2(sK0,sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.39/0.55    inference(resolution,[],[f68,f84])).
% 1.39/0.55  fof(f84,plain,(
% 1.39/0.55    ( ! [X0,X1] : (m1_pre_topc(sK2(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f52])).
% 1.39/0.55  fof(f255,plain,(
% 1.39/0.55    v1_zfmisc_1(sK1) | v2_pre_topc(sK2(sK0,sK1)) | ~v2_tdlat_3(sK2(sK0,sK1))),
% 1.39/0.55    inference(resolution,[],[f250,f74])).
% 1.39/0.55  fof(f74,plain,(
% 1.39/0.55    ( ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f28])).
% 1.39/0.55  fof(f28,plain,(
% 1.39/0.55    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 1.39/0.55    inference(flattening,[],[f27])).
% 1.39/0.55  fof(f27,plain,(
% 1.39/0.55    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 1.39/0.55    inference(ennf_transformation,[],[f12])).
% 1.39/0.55  fof(f12,axiom,(
% 1.39/0.55    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).
% 1.39/0.55  fof(f250,plain,(
% 1.39/0.55    l1_pre_topc(sK2(sK0,sK1)) | v1_zfmisc_1(sK1)),
% 1.39/0.55    inference(resolution,[],[f204,f133])).
% 1.39/0.55  fof(f133,plain,(
% 1.39/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) )),
% 1.39/0.55    inference(resolution,[],[f65,f78])).
% 1.39/0.55  fof(f78,plain,(
% 1.39/0.55    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f31])).
% 1.39/0.55  fof(f31,plain,(
% 1.39/0.55    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.39/0.55    inference(ennf_transformation,[],[f8])).
% 1.39/0.55  fof(f8,axiom,(
% 1.39/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.39/0.55  fof(f266,plain,(
% 1.39/0.55    v1_zfmisc_1(sK1) | v7_struct_0(sK2(sK0,sK1)) | ~v2_pre_topc(sK2(sK0,sK1)) | v2_struct_0(sK2(sK0,sK1))),
% 1.39/0.55    inference(subsumption_resolution,[],[f265,f199])).
% 1.39/0.55  fof(f199,plain,(
% 1.39/0.55    v1_tdlat_3(sK2(sK0,sK1)) | v1_zfmisc_1(sK1)),
% 1.39/0.55    inference(subsumption_resolution,[],[f198,f62])).
% 1.39/0.55  fof(f198,plain,(
% 1.39/0.55    v1_zfmisc_1(sK1) | v1_tdlat_3(sK2(sK0,sK1)) | v2_struct_0(sK0)),
% 1.39/0.55    inference(subsumption_resolution,[],[f197,f63])).
% 1.39/0.55  fof(f197,plain,(
% 1.39/0.55    v1_zfmisc_1(sK1) | v1_tdlat_3(sK2(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.39/0.55    inference(subsumption_resolution,[],[f196,f65])).
% 1.39/0.55  fof(f196,plain,(
% 1.39/0.55    v1_zfmisc_1(sK1) | v1_tdlat_3(sK2(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.39/0.55    inference(subsumption_resolution,[],[f195,f66])).
% 1.39/0.55  fof(f195,plain,(
% 1.39/0.55    v1_zfmisc_1(sK1) | v1_tdlat_3(sK2(sK0,sK1)) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.39/0.55    inference(subsumption_resolution,[],[f187,f67])).
% 1.39/0.55  fof(f187,plain,(
% 1.39/0.55    v1_zfmisc_1(sK1) | v1_tdlat_3(sK2(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.39/0.55    inference(resolution,[],[f68,f83])).
% 1.39/0.55  fof(f83,plain,(
% 1.39/0.55    ( ! [X0,X1] : (v1_tdlat_3(sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f52])).
% 1.39/0.55  fof(f265,plain,(
% 1.39/0.55    v1_zfmisc_1(sK1) | v7_struct_0(sK2(sK0,sK1)) | ~v1_tdlat_3(sK2(sK0,sK1)) | ~v2_pre_topc(sK2(sK0,sK1)) | v2_struct_0(sK2(sK0,sK1))),
% 1.39/0.55    inference(subsumption_resolution,[],[f256,f251])).
% 1.39/0.55  fof(f256,plain,(
% 1.39/0.55    v1_zfmisc_1(sK1) | v7_struct_0(sK2(sK0,sK1)) | ~v2_tdlat_3(sK2(sK0,sK1)) | ~v1_tdlat_3(sK2(sK0,sK1)) | ~v2_pre_topc(sK2(sK0,sK1)) | v2_struct_0(sK2(sK0,sK1))),
% 1.39/0.55    inference(resolution,[],[f250,f76])).
% 1.39/0.55  fof(f76,plain,(
% 1.39/0.55    ( ! [X0] : (v7_struct_0(X0) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f30])).
% 1.39/0.55  fof(f30,plain,(
% 1.39/0.55    ! [X0] : ((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.39/0.55    inference(flattening,[],[f29])).
% 1.39/0.55  fof(f29,plain,(
% 1.39/0.55    ! [X0] : (((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | (~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.39/0.55    inference(ennf_transformation,[],[f13])).
% 1.39/0.55  fof(f13,axiom,(
% 1.39/0.55    ! [X0] : (l1_pre_topc(X0) => ((v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0))))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_1)).
% 1.39/0.55  fof(f285,plain,(
% 1.39/0.55    v1_zfmisc_1(sK1) | v1_zfmisc_1(u1_struct_0(sK2(sK0,sK1))) | ~v7_struct_0(sK2(sK0,sK1))),
% 1.39/0.55    inference(resolution,[],[f254,f86])).
% 1.39/0.55  fof(f86,plain,(
% 1.39/0.55    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f39])).
% 1.39/0.55  fof(f39,plain,(
% 1.39/0.55    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 1.39/0.55    inference(flattening,[],[f38])).
% 1.39/0.55  fof(f38,plain,(
% 1.39/0.55    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 1.39/0.55    inference(ennf_transformation,[],[f9])).
% 1.39/0.55  fof(f9,axiom,(
% 1.39/0.55    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).
% 1.39/0.55  fof(f254,plain,(
% 1.39/0.55    l1_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(sK1)),
% 1.39/0.55    inference(resolution,[],[f250,f73])).
% 1.39/0.55  fof(f73,plain,(
% 1.39/0.55    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f26])).
% 1.39/0.55  fof(f26,plain,(
% 1.39/0.55    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.39/0.55    inference(ennf_transformation,[],[f7])).
% 1.39/0.55  fof(f7,axiom,(
% 1.39/0.55    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.39/0.55  fof(f623,plain,(
% 1.39/0.55    v2_tex_2(sK1,sK0) | ~r2_hidden(sK3(sK1),sK1)),
% 1.39/0.55    inference(superposition,[],[f618,f396])).
% 1.39/0.55  fof(f396,plain,(
% 1.39/0.55    sK1 = k1_tarski(sK3(sK1))),
% 1.39/0.55    inference(resolution,[],[f238,f384])).
% 1.39/0.55  fof(f384,plain,(
% 1.39/0.55    v1_zfmisc_1(sK1)),
% 1.39/0.55    inference(resolution,[],[f383,f68])).
% 1.39/0.55  fof(f238,plain,(
% 1.39/0.55    ~v1_zfmisc_1(sK1) | sK1 = k1_tarski(sK3(sK1))),
% 1.39/0.55    inference(subsumption_resolution,[],[f237,f70])).
% 1.39/0.55  fof(f70,plain,(
% 1.39/0.55    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 1.39/0.55    inference(cnf_transformation,[],[f3])).
% 1.39/0.55  fof(f3,axiom,(
% 1.39/0.55    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 1.39/0.55  fof(f237,plain,(
% 1.39/0.55    sK1 = k1_tarski(sK3(sK1)) | ~v1_zfmisc_1(sK1) | v1_xboole_0(k1_tarski(sK3(sK1)))),
% 1.39/0.55    inference(subsumption_resolution,[],[f236,f66])).
% 1.39/0.55  fof(f236,plain,(
% 1.39/0.55    sK1 = k1_tarski(sK3(sK1)) | ~v1_zfmisc_1(sK1) | v1_xboole_0(sK1) | v1_xboole_0(k1_tarski(sK3(sK1)))),
% 1.39/0.55    inference(resolution,[],[f231,f71])).
% 1.39/0.55  fof(f71,plain,(
% 1.39/0.55    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f23])).
% 1.39/0.55  fof(f23,plain,(
% 1.39/0.55    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.39/0.55    inference(flattening,[],[f22])).
% 1.39/0.55  fof(f22,plain,(
% 1.39/0.55    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.39/0.55    inference(ennf_transformation,[],[f15])).
% 1.39/0.55  fof(f15,axiom,(
% 1.39/0.55    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 1.39/0.55  fof(f231,plain,(
% 1.39/0.55    r1_tarski(k1_tarski(sK3(sK1)),sK1)),
% 1.39/0.55    inference(resolution,[],[f158,f95])).
% 1.39/0.55  fof(f95,plain,(
% 1.39/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.39/0.55    inference(cnf_transformation,[],[f61])).
% 1.39/0.55  fof(f61,plain,(
% 1.39/0.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.39/0.55    inference(nnf_transformation,[],[f5])).
% 1.39/0.55  fof(f5,axiom,(
% 1.39/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.39/0.55  fof(f158,plain,(
% 1.39/0.55    m1_subset_1(k1_tarski(sK3(sK1)),k1_zfmisc_1(sK1))),
% 1.39/0.55    inference(backward_demodulation,[],[f156,f157])).
% 1.39/0.55  fof(f157,plain,(
% 1.39/0.55    k6_domain_1(sK1,sK3(sK1)) = k1_tarski(sK3(sK1))),
% 1.39/0.55    inference(subsumption_resolution,[],[f155,f66])).
% 1.39/0.55  fof(f155,plain,(
% 1.39/0.55    k6_domain_1(sK1,sK3(sK1)) = k1_tarski(sK3(sK1)) | v1_xboole_0(sK1)),
% 1.39/0.55    inference(resolution,[],[f152,f90])).
% 1.39/0.55  fof(f90,plain,(
% 1.39/0.55    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f42])).
% 1.39/0.55  fof(f42,plain,(
% 1.39/0.55    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.39/0.55    inference(flattening,[],[f41])).
% 1.39/0.55  fof(f41,plain,(
% 1.39/0.55    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.39/0.55    inference(ennf_transformation,[],[f11])).
% 1.39/0.55  fof(f11,axiom,(
% 1.39/0.55    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.39/0.55  fof(f152,plain,(
% 1.39/0.55    m1_subset_1(sK3(sK1),sK1)),
% 1.39/0.55    inference(resolution,[],[f146,f89])).
% 1.39/0.55  fof(f89,plain,(
% 1.39/0.55    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f40])).
% 1.39/0.55  fof(f40,plain,(
% 1.39/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.39/0.55    inference(ennf_transformation,[],[f4])).
% 1.39/0.55  fof(f4,axiom,(
% 1.39/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 1.39/0.55  fof(f156,plain,(
% 1.39/0.55    m1_subset_1(k6_domain_1(sK1,sK3(sK1)),k1_zfmisc_1(sK1))),
% 1.39/0.55    inference(subsumption_resolution,[],[f154,f66])).
% 1.39/0.55  fof(f154,plain,(
% 1.39/0.55    m1_subset_1(k6_domain_1(sK1,sK3(sK1)),k1_zfmisc_1(sK1)) | v1_xboole_0(sK1)),
% 1.39/0.55    inference(resolution,[],[f152,f91])).
% 1.39/0.55  fof(f91,plain,(
% 1.39/0.55    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f44])).
% 1.39/0.55  fof(f44,plain,(
% 1.39/0.55    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.39/0.55    inference(flattening,[],[f43])).
% 1.39/0.55  fof(f43,plain,(
% 1.39/0.55    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.39/0.55    inference(ennf_transformation,[],[f10])).
% 1.39/0.55  fof(f10,axiom,(
% 1.39/0.55    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 1.39/0.55  fof(f618,plain,(
% 1.39/0.55    ( ! [X0] : (v2_tex_2(k1_tarski(X0),sK0) | ~r2_hidden(X0,sK1)) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f617,f354])).
% 1.39/0.55  fof(f354,plain,(
% 1.39/0.55    ( ! [X2] : (m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,sK1)) )),
% 1.39/0.55    inference(resolution,[],[f183,f89])).
% 1.39/0.55  fof(f183,plain,(
% 1.39/0.55    ( ! [X0] : (r2_hidden(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1)) )),
% 1.39/0.55    inference(resolution,[],[f163,f92])).
% 1.39/0.55  fof(f92,plain,(
% 1.39/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f60])).
% 1.39/0.55  % (31901)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.39/0.55  fof(f60,plain,(
% 1.39/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.39/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f58,f59])).
% 1.39/0.55  fof(f59,plain,(
% 1.39/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.39/0.55    introduced(choice_axiom,[])).
% 1.39/0.55  fof(f58,plain,(
% 1.39/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.39/0.55    inference(rectify,[],[f57])).
% 1.39/0.55  fof(f57,plain,(
% 1.39/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.39/0.55    inference(nnf_transformation,[],[f45])).
% 1.39/0.55  fof(f45,plain,(
% 1.39/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.39/0.55    inference(ennf_transformation,[],[f2])).
% 1.39/0.55  fof(f2,axiom,(
% 1.39/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.39/0.55  fof(f163,plain,(
% 1.39/0.55    r1_tarski(sK1,u1_struct_0(sK0))),
% 1.39/0.55    inference(resolution,[],[f67,f95])).
% 1.39/0.55  fof(f617,plain,(
% 1.39/0.55    ( ! [X0] : (v2_tex_2(k1_tarski(X0),sK0) | ~r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f600,f299])).
% 1.39/0.55  fof(f299,plain,(
% 1.39/0.55    ~v1_xboole_0(u1_struct_0(sK0))),
% 1.39/0.55    inference(resolution,[],[f298,f163])).
% 1.39/0.55  fof(f298,plain,(
% 1.39/0.55    ( ! [X3] : (~r1_tarski(sK1,X3) | ~v1_xboole_0(X3)) )),
% 1.39/0.55    inference(resolution,[],[f151,f87])).
% 1.39/0.55  fof(f87,plain,(
% 1.39/0.55    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f56])).
% 1.39/0.55  fof(f151,plain,(
% 1.39/0.55    ( ! [X0] : (r2_hidden(sK3(sK1),X0) | ~r1_tarski(sK1,X0)) )),
% 1.39/0.55    inference(resolution,[],[f146,f92])).
% 1.39/0.55  fof(f600,plain,(
% 1.39/0.55    ( ! [X0] : (v2_tex_2(k1_tarski(X0),sK0) | ~r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))) )),
% 1.39/0.55    inference(superposition,[],[f372,f90])).
% 1.39/0.55  fof(f372,plain,(
% 1.39/0.55    ( ! [X0] : (v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0) | ~r2_hidden(X0,sK1)) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f371,f62])).
% 1.39/0.55  fof(f371,plain,(
% 1.39/0.55    ( ! [X0] : (~r2_hidden(X0,sK1) | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0) | v2_struct_0(sK0)) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f370,f63])).
% 1.39/0.55  fof(f370,plain,(
% 1.39/0.55    ( ! [X0] : (~r2_hidden(X0,sK1) | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f367,f65])).
% 1.39/0.55  fof(f367,plain,(
% 1.39/0.55    ( ! [X0] : (~r2_hidden(X0,sK1) | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.39/0.55    inference(resolution,[],[f354,f80])).
% 1.39/0.55  fof(f80,plain,(
% 1.39/0.55    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f35])).
% 1.39/0.55  fof(f35,plain,(
% 1.39/0.55    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.39/0.55    inference(flattening,[],[f34])).
% 1.39/0.55  fof(f34,plain,(
% 1.39/0.55    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.39/0.55    inference(ennf_transformation,[],[f17])).
% 1.39/0.55  fof(f17,axiom,(
% 1.39/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).
% 1.39/0.55  % SZS output end Proof for theBenchmark
% 1.39/0.55  % (31895)------------------------------
% 1.39/0.55  % (31895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (31895)Termination reason: Refutation
% 1.39/0.55  
% 1.39/0.55  % (31895)Memory used [KB]: 1918
% 1.39/0.55  % (31895)Time elapsed: 0.076 s
% 1.39/0.55  % (31895)------------------------------
% 1.39/0.55  % (31895)------------------------------
% 1.39/0.55  % (31871)Success in time 0.186 s
%------------------------------------------------------------------------------
