%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:38 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :  186 (7000 expanded)
%              Number of leaves         :   25 (1894 expanded)
%              Depth                    :   43
%              Number of atoms          :  788 (58532 expanded)
%              Number of equality atoms :  101 (1112 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f690,plain,(
    $false ),
    inference(global_subsumption,[],[f639,f689])).

fof(f689,plain,(
    ~ l1_pre_topc(sK3(sK0,sK1)) ),
    inference(resolution,[],[f688,f89])).

fof(f89,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f688,plain,(
    ~ l1_struct_0(sK3(sK0,sK1)) ),
    inference(global_subsumption,[],[f648,f636,f687])).

fof(f687,plain,
    ( v1_zfmisc_1(sK1)
    | ~ l1_struct_0(sK3(sK0,sK1))
    | ~ v7_struct_0(sK3(sK0,sK1)) ),
    inference(superposition,[],[f106,f650])).

fof(f650,plain,(
    sK1 = u1_struct_0(sK3(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f516,f635])).

fof(f635,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(global_subsumption,[],[f84,f83,f82,f79,f634])).

fof(f634,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f633,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK2(X0,X1)) = X1
            & m1_pre_topc(sK2(X0,X1),X0)
            & ~ v2_struct_0(sK2(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f63])).

fof(f63,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK2(X0,X1)) = X1
        & m1_pre_topc(sK2(X0,X1),X0)
        & ~ v2_struct_0(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tsep_1)).

fof(f633,plain,
    ( v2_struct_0(sK2(sK0,sK1))
    | v2_tex_2(sK1,sK0) ),
    inference(global_subsumption,[],[f550,f632])).

fof(f632,plain,
    ( v2_struct_0(sK2(sK0,sK1))
    | v2_tex_2(sK1,sK0)
    | ~ r2_hidden(sK4(sK1),sK1) ),
    inference(resolution,[],[f624,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f624,plain,
    ( ~ m1_subset_1(sK4(sK1),sK1)
    | v2_struct_0(sK2(sK0,sK1))
    | v2_tex_2(sK1,sK0) ),
    inference(resolution,[],[f546,f318])).

fof(f318,plain,(
    ! [X0] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK2(sK0,sK1))
      | ~ m1_subset_1(X0,sK1) ) ),
    inference(global_subsumption,[],[f83,f317])).

fof(f317,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | v2_struct_0(sK2(sK0,sK1))
      | m1_subset_1(X0,u1_struct_0(sK0))
      | v1_xboole_0(sK1) ) ),
    inference(forward_demodulation,[],[f315,f259])).

fof(f259,plain,(
    sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    inference(global_subsumption,[],[f83,f257])).

fof(f257,plain,
    ( v1_xboole_0(sK1)
    | sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    inference(resolution,[],[f256,f84])).

fof(f256,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | u1_struct_0(sK2(sK0,X0)) = X0 ) ),
    inference(global_subsumption,[],[f79,f253])).

fof(f253,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | u1_struct_0(sK2(sK0,X0)) = X0
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f99,f82])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | u1_struct_0(sK2(X0,X1)) = X1
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f315,plain,(
    ! [X0] :
      ( v2_struct_0(sK2(sK0,sK1))
      | m1_subset_1(X0,u1_struct_0(sK0))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK2(sK0,sK1))) ) ),
    inference(resolution,[],[f252,f84])).

fof(f252,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK2(sK0,X1))
      | m1_subset_1(X0,u1_struct_0(sK0))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK2(sK0,X1))) ) ),
    inference(resolution,[],[f251,f212])).

fof(f212,plain,(
    ! [X0] :
      ( m1_pre_topc(sK2(sK0,X0),sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(global_subsumption,[],[f79,f211])).

fof(f211,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | m1_pre_topc(sK2(sK0,X0),sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f98,f82])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | m1_pre_topc(sK2(X0,X1),X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f251,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,sK0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f79,f248])).

fof(f248,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f96,f82])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

fof(f546,plain,
    ( ~ m1_subset_1(sK4(sK1),u1_struct_0(sK0))
    | v2_tex_2(sK1,sK0) ),
    inference(backward_demodulation,[],[f341,f541])).

fof(f541,plain,(
    sK1 = k1_tarski(sK4(sK1)) ),
    inference(global_subsumption,[],[f83,f540])).

fof(f540,plain,
    ( sK1 = k1_tarski(sK4(sK1))
    | v1_xboole_0(sK1) ),
    inference(duplicate_literal_removal,[],[f537])).

fof(f537,plain,
    ( sK1 = k1_tarski(sK4(sK1))
    | sK1 = k1_tarski(sK4(sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f536,f108])).

fof(f108,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f68,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f67])).

fof(f67,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f536,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k1_tarski(X0) = sK1
      | sK1 = k1_tarski(sK4(sK1)) ) ),
    inference(global_subsumption,[],[f87,f535])).

fof(f535,plain,(
    ! [X0] :
      ( sK1 = k1_tarski(sK4(sK1))
      | k1_tarski(X0) = sK1
      | v1_xboole_0(k1_tarski(X0))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f534,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

% (5951)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
fof(f534,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | sK1 = k1_tarski(sK4(sK1))
      | sK1 = X0
      | v1_xboole_0(X0) ) ),
    inference(global_subsumption,[],[f83,f533])).

fof(f533,plain,(
    ! [X0] :
      ( sK1 = k1_tarski(sK4(sK1))
      | ~ r1_tarski(X0,sK1)
      | sK1 = X0
      | v1_xboole_0(sK1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f532,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | ~ r1_tarski(X0,X1)
      | X0 = X1
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f532,plain,
    ( v1_zfmisc_1(sK1)
    | sK1 = k1_tarski(sK4(sK1)) ),
    inference(resolution,[],[f531,f85])).

fof(f85,plain,
    ( v2_tex_2(sK1,sK0)
    | v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f59,f61,f60])).

fof(f60,plain,
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

fof(f61,plain,
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

fof(f59,plain,(
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
    inference(flattening,[],[f58])).

fof(f58,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
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
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

fof(f531,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | sK1 = k1_tarski(sK4(sK1)) ),
    inference(duplicate_literal_removal,[],[f530])).

fof(f530,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | sK1 = k1_tarski(sK4(sK1))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(resolution,[],[f529,f491])).

fof(f491,plain,
    ( l1_pre_topc(sK3(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(global_subsumption,[],[f83,f490])).

fof(f490,plain,
    ( v1_xboole_0(sK1)
    | ~ v2_tex_2(sK1,sK0)
    | l1_pre_topc(sK3(sK0,sK1)) ),
    inference(resolution,[],[f475,f84])).

fof(f475,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X3)
      | ~ v2_tex_2(X3,sK0)
      | l1_pre_topc(sK3(sK0,X3)) ) ),
    inference(resolution,[],[f472,f126])).

fof(f126,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f94,f82])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f472,plain,(
    ! [X0] :
      ( m1_pre_topc(sK3(sK0,X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | ~ v2_tex_2(X0,sK0) ) ),
    inference(global_subsumption,[],[f82,f79,f469])).

fof(f469,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | ~ l1_pre_topc(sK0)
      | m1_pre_topc(sK3(sK0,X0),sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f104,f80])).

fof(f80,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f62])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(sK3(X0,X1),X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK3(X0,X1)) = X1
            & m1_pre_topc(sK3(X0,X1),X0)
            & v1_tdlat_3(sK3(X0,X1))
            & ~ v2_struct_0(sK3(X0,X1)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f46,f65])).

fof(f65,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_tdlat_3(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK3(X0,X1)) = X1
        & m1_pre_topc(sK3(X0,X1),X0)
        & v1_tdlat_3(sK3(X0,X1))
        & ~ v2_struct_0(sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(pure_predicate_removal,[],[f20])).

fof(f20,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tex_2)).

fof(f529,plain,
    ( ~ l1_pre_topc(sK3(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0)
    | sK1 = k1_tarski(sK4(sK1)) ),
    inference(resolution,[],[f528,f89])).

fof(f528,plain,
    ( ~ l1_struct_0(sK3(sK0,sK1))
    | sK1 = k1_tarski(sK4(sK1))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(global_subsumption,[],[f86,f527])).

fof(f527,plain,
    ( ~ l1_struct_0(sK3(sK0,sK1))
    | v1_zfmisc_1(sK1)
    | sK1 = k1_tarski(sK4(sK1))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(resolution,[],[f526,f503])).

fof(f503,plain,
    ( v7_struct_0(sK3(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(global_subsumption,[],[f84,f83,f82,f80,f79,f502])).

fof(f502,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v7_struct_0(sK3(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f501])).

fof(f501,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v7_struct_0(sK3(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f495,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK3(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f495,plain,
    ( v2_struct_0(sK3(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0)
    | v7_struct_0(sK3(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f485,f491])).

fof(f485,plain,
    ( v7_struct_0(sK3(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0)
    | v2_struct_0(sK3(sK0,sK1))
    | ~ l1_pre_topc(sK3(sK0,sK1)) ),
    inference(global_subsumption,[],[f397,f482])).

fof(f482,plain,
    ( v2_tdlat_3(sK3(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(global_subsumption,[],[f83,f481])).

fof(f481,plain,
    ( v1_xboole_0(sK1)
    | ~ v2_tex_2(sK1,sK0)
    | v2_tdlat_3(sK3(sK0,sK1)) ),
    inference(resolution,[],[f474,f84])).

fof(f474,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X2)
      | ~ v2_tex_2(X2,sK0)
      | v2_tdlat_3(sK3(sK0,X2)) ) ),
    inference(resolution,[],[f472,f157])).

fof(f157,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_tdlat_3(X0) ) ),
    inference(global_subsumption,[],[f82,f81,f79,f154])).

fof(f154,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_tdlat_3(sK0)
      | v2_tdlat_3(X0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f100,f80])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | v2_tdlat_3(X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_tdlat_3(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_tdlat_3)).

fof(f81,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f62])).

fof(f397,plain,
    ( ~ v2_tdlat_3(sK3(sK0,sK1))
    | v7_struct_0(sK3(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0)
    | v2_struct_0(sK3(sK0,sK1))
    | ~ l1_pre_topc(sK3(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f396])).

fof(f396,plain,
    ( ~ v2_tdlat_3(sK3(sK0,sK1))
    | v7_struct_0(sK3(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0)
    | v2_struct_0(sK3(sK0,sK1))
    | ~ l1_pre_topc(sK3(sK0,sK1))
    | ~ v2_tdlat_3(sK3(sK0,sK1))
    | ~ l1_pre_topc(sK3(sK0,sK1)) ),
    inference(resolution,[],[f388,f90])).

fof(f90,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).

fof(f388,plain,
    ( ~ v2_pre_topc(sK3(sK0,sK1))
    | ~ v2_tdlat_3(sK3(sK0,sK1))
    | v7_struct_0(sK3(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0)
    | v2_struct_0(sK3(sK0,sK1))
    | ~ l1_pre_topc(sK3(sK0,sK1)) ),
    inference(resolution,[],[f387,f92])).

fof(f92,plain,(
    ! [X0] :
      ( ~ v1_tdlat_3(X0)
      | ~ v2_tdlat_3(X0)
      | v7_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( v2_tdlat_3(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_pre_topc(X0)
          & v7_struct_0(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_1)).

% (5948)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
fof(f387,plain,
    ( v1_tdlat_3(sK3(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(global_subsumption,[],[f83,f385])).

fof(f385,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_xboole_0(sK1)
    | v1_tdlat_3(sK3(sK0,sK1)) ),
    inference(resolution,[],[f384,f84])).

fof(f384,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | v1_xboole_0(X0)
      | v1_tdlat_3(sK3(sK0,X0)) ) ),
    inference(global_subsumption,[],[f82,f79,f381])).

fof(f381,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | ~ l1_pre_topc(sK0)
      | v1_tdlat_3(sK3(sK0,X0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f103,f80])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v1_tdlat_3(sK3(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f526,plain,
    ( ~ v7_struct_0(sK3(sK0,sK1))
    | ~ l1_struct_0(sK3(sK0,sK1))
    | v1_zfmisc_1(sK1)
    | sK1 = k1_tarski(sK4(sK1)) ),
    inference(superposition,[],[f106,f525])).

fof(f525,plain,
    ( sK1 = u1_struct_0(sK3(sK0,sK1))
    | sK1 = k1_tarski(sK4(sK1)) ),
    inference(global_subsumption,[],[f83,f522])).

fof(f522,plain,
    ( sK1 = k1_tarski(sK4(sK1))
    | sK1 = u1_struct_0(sK3(sK0,sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f521,f108])).

fof(f521,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k1_tarski(X0) = sK1
      | sK1 = u1_struct_0(sK3(sK0,sK1)) ) ),
    inference(global_subsumption,[],[f87,f520])).

fof(f520,plain,(
    ! [X0] :
      ( sK1 = u1_struct_0(sK3(sK0,sK1))
      | k1_tarski(X0) = sK1
      | v1_xboole_0(k1_tarski(X0))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f519,f120])).

fof(f519,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | sK1 = u1_struct_0(sK3(sK0,sK1))
      | sK1 = X0
      | v1_xboole_0(X0) ) ),
    inference(global_subsumption,[],[f83,f518])).

fof(f518,plain,(
    ! [X0] :
      ( sK1 = u1_struct_0(sK3(sK0,sK1))
      | ~ r1_tarski(X0,sK1)
      | sK1 = X0
      | v1_xboole_0(sK1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f517,f88])).

fof(f517,plain,
    ( v1_zfmisc_1(sK1)
    | sK1 = u1_struct_0(sK3(sK0,sK1)) ),
    inference(resolution,[],[f516,f85])).

fof(f86,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f62])).

fof(f87,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f341,plain,
    ( v2_tex_2(k1_tarski(sK4(sK1)),sK0)
    | ~ m1_subset_1(sK4(sK1),u1_struct_0(sK0)) ),
    inference(superposition,[],[f222,f340])).

fof(f340,plain,(
    k1_tarski(sK4(sK1)) = k6_domain_1(u1_struct_0(sK0),sK4(sK1)) ),
    inference(global_subsumption,[],[f83,f338])).

fof(f338,plain,
    ( k1_tarski(sK4(sK1)) = k6_domain_1(u1_struct_0(sK0),sK4(sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f333,f84])).

fof(f333,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_tarski(sK4(sK1)) = k6_domain_1(u1_struct_0(sK0),sK4(sK1))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f332,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f332,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_tarski(sK4(sK1)) = k6_domain_1(u1_struct_0(sK0),sK4(sK1)) ),
    inference(global_subsumption,[],[f84,f83,f82,f79,f331])).

fof(f331,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_tarski(sK4(sK1)) = k6_domain_1(u1_struct_0(sK0),sK4(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f330,f97])).

fof(f330,plain,
    ( v2_struct_0(sK2(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | k1_tarski(sK4(sK1)) = k6_domain_1(u1_struct_0(sK0),sK4(sK1)) ),
    inference(global_subsumption,[],[f83,f326])).

fof(f326,plain,
    ( k1_tarski(sK4(sK1)) = k6_domain_1(u1_struct_0(sK0),sK4(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | v2_struct_0(sK2(sK0,sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f323,f108])).

fof(f323,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k1_tarski(X0) = k6_domain_1(u1_struct_0(sK0),X0)
      | v1_xboole_0(u1_struct_0(sK0))
      | v2_struct_0(sK2(sK0,sK1)) ) ),
    inference(resolution,[],[f319,f109])).

fof(f319,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | v2_struct_0(sK2(sK0,sK1))
      | k1_tarski(X0) = k6_domain_1(u1_struct_0(sK0),X0)
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f318,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f222,plain,(
    ! [X0] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f82,f79,f219])).

fof(f219,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f101,f80])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

fof(f550,plain,(
    r2_hidden(sK4(sK1),sK1) ),
    inference(superposition,[],[f122,f541])).

fof(f122,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f121])).

fof(f121,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f116])).

fof(f116,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK6(X0,X1) != X0
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sK6(X0,X1) = X0
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f75,f76])).

fof(f76,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK6(X0,X1) != X0
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sK6(X0,X1) = X0
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f79,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f62])).

fof(f82,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f62])).

fof(f83,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f62])).

fof(f84,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f62])).

fof(f516,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | sK1 = u1_struct_0(sK3(sK0,sK1)) ),
    inference(global_subsumption,[],[f83,f515])).

fof(f515,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_xboole_0(sK1)
    | sK1 = u1_struct_0(sK3(sK0,sK1)) ),
    inference(resolution,[],[f479,f84])).

fof(f479,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | v1_xboole_0(X0)
      | u1_struct_0(sK3(sK0,X0)) = X0 ) ),
    inference(global_subsumption,[],[f82,f79,f476])).

fof(f476,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | ~ l1_pre_topc(sK0)
      | u1_struct_0(sK3(sK0,X0)) = X0
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f105,f80])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | u1_struct_0(sK3(X0,X1)) = X1
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f106,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f636,plain,(
    ~ v1_zfmisc_1(sK1) ),
    inference(subsumption_resolution,[],[f86,f635])).

fof(f648,plain,(
    v7_struct_0(sK3(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f503,f635])).

fof(f639,plain,(
    l1_pre_topc(sK3(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f491,f635])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:36:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (5941)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (5945)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.49  % (5940)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.49  % (5941)Refutation not found, incomplete strategy% (5941)------------------------------
% 0.21/0.49  % (5941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (5941)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (5941)Memory used [KB]: 6140
% 0.21/0.49  % (5941)Time elapsed: 0.078 s
% 0.21/0.49  % (5941)------------------------------
% 0.21/0.49  % (5941)------------------------------
% 0.21/0.50  % (5931)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (5938)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.50  % (5928)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (5933)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (5933)Refutation not found, incomplete strategy% (5933)------------------------------
% 0.21/0.51  % (5933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (5933)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (5933)Memory used [KB]: 6140
% 0.21/0.51  % (5933)Time elapsed: 0.095 s
% 0.21/0.51  % (5933)------------------------------
% 0.21/0.51  % (5933)------------------------------
% 0.21/0.51  % (5943)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (5935)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (5950)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (5942)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (5935)Refutation not found, incomplete strategy% (5935)------------------------------
% 0.21/0.52  % (5935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (5935)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (5935)Memory used [KB]: 1791
% 0.21/0.52  % (5935)Time elapsed: 0.117 s
% 0.21/0.52  % (5935)------------------------------
% 0.21/0.52  % (5935)------------------------------
% 0.21/0.53  % (5928)Refutation not found, incomplete strategy% (5928)------------------------------
% 0.21/0.53  % (5928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (5928)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (5928)Memory used [KB]: 10746
% 0.21/0.53  % (5928)Time elapsed: 0.094 s
% 0.21/0.53  % (5928)------------------------------
% 0.21/0.53  % (5928)------------------------------
% 0.21/0.53  % (5939)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.53  % (5939)Refutation not found, incomplete strategy% (5939)------------------------------
% 0.21/0.53  % (5939)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (5939)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (5939)Memory used [KB]: 10618
% 0.21/0.53  % (5939)Time elapsed: 0.123 s
% 0.21/0.53  % (5939)------------------------------
% 0.21/0.53  % (5939)------------------------------
% 1.40/0.53  % (5954)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.40/0.54  % (5949)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.40/0.54  % (5929)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.40/0.54  % (5934)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.40/0.54  % (5932)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.40/0.54  % (5940)Refutation found. Thanks to Tanya!
% 1.40/0.54  % SZS status Theorem for theBenchmark
% 1.40/0.54  % SZS output start Proof for theBenchmark
% 1.40/0.54  fof(f690,plain,(
% 1.40/0.54    $false),
% 1.40/0.54    inference(global_subsumption,[],[f639,f689])).
% 1.40/0.54  fof(f689,plain,(
% 1.40/0.54    ~l1_pre_topc(sK3(sK0,sK1))),
% 1.40/0.54    inference(resolution,[],[f688,f89])).
% 1.40/0.54  fof(f89,plain,(
% 1.40/0.54    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f30])).
% 1.40/0.54  fof(f30,plain,(
% 1.40/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.40/0.54    inference(ennf_transformation,[],[f10])).
% 1.40/0.54  fof(f10,axiom,(
% 1.40/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.40/0.54  fof(f688,plain,(
% 1.40/0.54    ~l1_struct_0(sK3(sK0,sK1))),
% 1.40/0.54    inference(global_subsumption,[],[f648,f636,f687])).
% 1.40/0.54  fof(f687,plain,(
% 1.40/0.54    v1_zfmisc_1(sK1) | ~l1_struct_0(sK3(sK0,sK1)) | ~v7_struct_0(sK3(sK0,sK1))),
% 1.40/0.54    inference(superposition,[],[f106,f650])).
% 1.40/0.54  fof(f650,plain,(
% 1.40/0.54    sK1 = u1_struct_0(sK3(sK0,sK1))),
% 1.40/0.54    inference(subsumption_resolution,[],[f516,f635])).
% 1.40/0.54  fof(f635,plain,(
% 1.40/0.54    v2_tex_2(sK1,sK0)),
% 1.40/0.54    inference(global_subsumption,[],[f84,f83,f82,f79,f634])).
% 1.40/0.54  fof(f634,plain,(
% 1.40/0.54    v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.40/0.54    inference(resolution,[],[f633,f97])).
% 1.40/0.54  fof(f97,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~v2_struct_0(sK2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f64])).
% 1.40/0.54  fof(f64,plain,(
% 1.40/0.54    ! [X0] : (! [X1] : ((u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & ~v2_struct_0(sK2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.40/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f63])).
% 1.40/0.54  fof(f63,plain,(
% 1.40/0.54    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & ~v2_struct_0(sK2(X0,X1))))),
% 1.40/0.54    introduced(choice_axiom,[])).
% 1.40/0.54  fof(f40,plain,(
% 1.40/0.54    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.40/0.54    inference(flattening,[],[f39])).
% 1.40/0.54  fof(f39,plain,(
% 1.40/0.54    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.40/0.54    inference(ennf_transformation,[],[f25])).
% 1.40/0.54  fof(f25,plain,(
% 1.40/0.54    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2))))),
% 1.40/0.54    inference(pure_predicate_removal,[],[f18])).
% 1.40/0.54  fof(f18,axiom,(
% 1.40/0.54    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tsep_1)).
% 1.40/0.54  fof(f633,plain,(
% 1.40/0.54    v2_struct_0(sK2(sK0,sK1)) | v2_tex_2(sK1,sK0)),
% 1.40/0.54    inference(global_subsumption,[],[f550,f632])).
% 1.40/0.54  fof(f632,plain,(
% 1.40/0.54    v2_struct_0(sK2(sK0,sK1)) | v2_tex_2(sK1,sK0) | ~r2_hidden(sK4(sK1),sK1)),
% 1.40/0.54    inference(resolution,[],[f624,f109])).
% 1.40/0.54  fof(f109,plain,(
% 1.40/0.54    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f49])).
% 1.40/0.54  fof(f49,plain,(
% 1.40/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.40/0.54    inference(ennf_transformation,[],[f6])).
% 1.40/0.54  fof(f6,axiom,(
% 1.40/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.40/0.54  fof(f624,plain,(
% 1.40/0.54    ~m1_subset_1(sK4(sK1),sK1) | v2_struct_0(sK2(sK0,sK1)) | v2_tex_2(sK1,sK0)),
% 1.40/0.54    inference(resolution,[],[f546,f318])).
% 1.40/0.54  fof(f318,plain,(
% 1.40/0.54    ( ! [X0] : (m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK2(sK0,sK1)) | ~m1_subset_1(X0,sK1)) )),
% 1.40/0.54    inference(global_subsumption,[],[f83,f317])).
% 1.40/0.54  fof(f317,plain,(
% 1.40/0.54    ( ! [X0] : (~m1_subset_1(X0,sK1) | v2_struct_0(sK2(sK0,sK1)) | m1_subset_1(X0,u1_struct_0(sK0)) | v1_xboole_0(sK1)) )),
% 1.40/0.54    inference(forward_demodulation,[],[f315,f259])).
% 1.40/0.54  fof(f259,plain,(
% 1.40/0.54    sK1 = u1_struct_0(sK2(sK0,sK1))),
% 1.40/0.54    inference(global_subsumption,[],[f83,f257])).
% 1.40/0.54  fof(f257,plain,(
% 1.40/0.54    v1_xboole_0(sK1) | sK1 = u1_struct_0(sK2(sK0,sK1))),
% 1.40/0.54    inference(resolution,[],[f256,f84])).
% 1.40/0.54  fof(f256,plain,(
% 1.40/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | u1_struct_0(sK2(sK0,X0)) = X0) )),
% 1.40/0.54    inference(global_subsumption,[],[f79,f253])).
% 1.40/0.54  fof(f253,plain,(
% 1.40/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | u1_struct_0(sK2(sK0,X0)) = X0 | v2_struct_0(sK0)) )),
% 1.40/0.54    inference(resolution,[],[f99,f82])).
% 1.40/0.54  fof(f99,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | u1_struct_0(sK2(X0,X1)) = X1 | v2_struct_0(X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f64])).
% 1.40/0.54  fof(f315,plain,(
% 1.40/0.54    ( ! [X0] : (v2_struct_0(sK2(sK0,sK1)) | m1_subset_1(X0,u1_struct_0(sK0)) | v1_xboole_0(sK1) | ~m1_subset_1(X0,u1_struct_0(sK2(sK0,sK1)))) )),
% 1.40/0.54    inference(resolution,[],[f252,f84])).
% 1.40/0.54  fof(f252,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK2(sK0,X1)) | m1_subset_1(X0,u1_struct_0(sK0)) | v1_xboole_0(X1) | ~m1_subset_1(X0,u1_struct_0(sK2(sK0,X1)))) )),
% 1.40/0.54    inference(resolution,[],[f251,f212])).
% 1.40/0.54  fof(f212,plain,(
% 1.40/0.54    ( ! [X0] : (m1_pre_topc(sK2(sK0,X0),sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.40/0.54    inference(global_subsumption,[],[f79,f211])).
% 1.40/0.54  fof(f211,plain,(
% 1.40/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | m1_pre_topc(sK2(sK0,X0),sK0) | v2_struct_0(sK0)) )),
% 1.40/0.54    inference(resolution,[],[f98,f82])).
% 1.40/0.54  fof(f98,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | m1_pre_topc(sK2(X0,X1),X0) | v2_struct_0(X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f64])).
% 1.40/0.54  fof(f251,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~m1_pre_topc(X1,sK0) | ~m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1) | m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.40/0.54    inference(global_subsumption,[],[f79,f248])).
% 1.40/0.54  fof(f248,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 1.40/0.54    inference(resolution,[],[f96,f82])).
% 1.40/0.54  fof(f96,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f38])).
% 1.40/0.54  fof(f38,plain,(
% 1.40/0.54    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.40/0.54    inference(flattening,[],[f37])).
% 1.40/0.54  fof(f37,plain,(
% 1.40/0.54    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.40/0.54    inference(ennf_transformation,[],[f13])).
% 1.40/0.54  fof(f13,axiom,(
% 1.40/0.54    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).
% 1.40/0.54  fof(f546,plain,(
% 1.40/0.54    ~m1_subset_1(sK4(sK1),u1_struct_0(sK0)) | v2_tex_2(sK1,sK0)),
% 1.40/0.54    inference(backward_demodulation,[],[f341,f541])).
% 1.40/0.54  fof(f541,plain,(
% 1.40/0.54    sK1 = k1_tarski(sK4(sK1))),
% 1.40/0.54    inference(global_subsumption,[],[f83,f540])).
% 1.40/0.54  fof(f540,plain,(
% 1.40/0.54    sK1 = k1_tarski(sK4(sK1)) | v1_xboole_0(sK1)),
% 1.40/0.54    inference(duplicate_literal_removal,[],[f537])).
% 1.40/0.54  fof(f537,plain,(
% 1.40/0.54    sK1 = k1_tarski(sK4(sK1)) | sK1 = k1_tarski(sK4(sK1)) | v1_xboole_0(sK1)),
% 1.40/0.54    inference(resolution,[],[f536,f108])).
% 1.40/0.54  fof(f108,plain,(
% 1.40/0.54    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f70])).
% 1.40/0.54  fof(f70,plain,(
% 1.40/0.54    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.40/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f68,f69])).
% 1.40/0.54  fof(f69,plain,(
% 1.40/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 1.40/0.54    introduced(choice_axiom,[])).
% 1.40/0.54  fof(f68,plain,(
% 1.40/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.40/0.54    inference(rectify,[],[f67])).
% 1.40/0.54  fof(f67,plain,(
% 1.40/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.40/0.54    inference(nnf_transformation,[],[f1])).
% 1.40/0.54  fof(f1,axiom,(
% 1.40/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.40/0.54  fof(f536,plain,(
% 1.40/0.54    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_tarski(X0) = sK1 | sK1 = k1_tarski(sK4(sK1))) )),
% 1.40/0.54    inference(global_subsumption,[],[f87,f535])).
% 1.40/0.54  fof(f535,plain,(
% 1.40/0.54    ( ! [X0] : (sK1 = k1_tarski(sK4(sK1)) | k1_tarski(X0) = sK1 | v1_xboole_0(k1_tarski(X0)) | ~r2_hidden(X0,sK1)) )),
% 1.40/0.54    inference(resolution,[],[f534,f120])).
% 1.40/0.54  fof(f120,plain,(
% 1.40/0.54    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f78])).
% 1.40/0.54  fof(f78,plain,(
% 1.40/0.54    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.40/0.54    inference(nnf_transformation,[],[f4])).
% 1.40/0.54  fof(f4,axiom,(
% 1.40/0.54    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.40/0.54  % (5951)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.40/0.54  fof(f534,plain,(
% 1.40/0.54    ( ! [X0] : (~r1_tarski(X0,sK1) | sK1 = k1_tarski(sK4(sK1)) | sK1 = X0 | v1_xboole_0(X0)) )),
% 1.40/0.54    inference(global_subsumption,[],[f83,f533])).
% 1.40/0.54  fof(f533,plain,(
% 1.40/0.54    ( ! [X0] : (sK1 = k1_tarski(sK4(sK1)) | ~r1_tarski(X0,sK1) | sK1 = X0 | v1_xboole_0(sK1) | v1_xboole_0(X0)) )),
% 1.40/0.54    inference(resolution,[],[f532,f88])).
% 1.40/0.54  fof(f88,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | ~r1_tarski(X0,X1) | X0 = X1 | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f29])).
% 1.40/0.54  fof(f29,plain,(
% 1.40/0.54    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.40/0.54    inference(flattening,[],[f28])).
% 1.40/0.54  fof(f28,plain,(
% 1.40/0.54    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.40/0.54    inference(ennf_transformation,[],[f19])).
% 1.40/0.54  fof(f19,axiom,(
% 1.40/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 1.40/0.54  fof(f532,plain,(
% 1.40/0.54    v1_zfmisc_1(sK1) | sK1 = k1_tarski(sK4(sK1))),
% 1.40/0.54    inference(resolution,[],[f531,f85])).
% 1.40/0.54  fof(f85,plain,(
% 1.40/0.54    v2_tex_2(sK1,sK0) | v1_zfmisc_1(sK1)),
% 1.40/0.54    inference(cnf_transformation,[],[f62])).
% 1.40/0.54  fof(f62,plain,(
% 1.40/0.54    ((~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.40/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f59,f61,f60])).
% 1.40/0.54  fof(f60,plain,(
% 1.40/0.54    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.40/0.54    introduced(choice_axiom,[])).
% 1.40/0.54  fof(f61,plain,(
% 1.40/0.54    ? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1))),
% 1.40/0.54    introduced(choice_axiom,[])).
% 1.40/0.54  fof(f59,plain,(
% 1.40/0.54    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.40/0.54    inference(flattening,[],[f58])).
% 1.40/0.54  fof(f58,plain,(
% 1.40/0.54    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.40/0.54    inference(nnf_transformation,[],[f27])).
% 1.40/0.54  fof(f27,plain,(
% 1.40/0.54    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.40/0.54    inference(flattening,[],[f26])).
% 1.40/0.54  fof(f26,plain,(
% 1.40/0.54    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.40/0.54    inference(ennf_transformation,[],[f23])).
% 1.40/0.54  fof(f23,negated_conjecture,(
% 1.40/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.40/0.54    inference(negated_conjecture,[],[f22])).
% 1.40/0.54  fof(f22,conjecture,(
% 1.40/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).
% 1.40/0.54  fof(f531,plain,(
% 1.40/0.54    ~v2_tex_2(sK1,sK0) | sK1 = k1_tarski(sK4(sK1))),
% 1.40/0.54    inference(duplicate_literal_removal,[],[f530])).
% 1.40/0.54  fof(f530,plain,(
% 1.40/0.54    ~v2_tex_2(sK1,sK0) | sK1 = k1_tarski(sK4(sK1)) | ~v2_tex_2(sK1,sK0)),
% 1.40/0.54    inference(resolution,[],[f529,f491])).
% 1.40/0.54  fof(f491,plain,(
% 1.40/0.54    l1_pre_topc(sK3(sK0,sK1)) | ~v2_tex_2(sK1,sK0)),
% 1.40/0.54    inference(global_subsumption,[],[f83,f490])).
% 1.40/0.54  fof(f490,plain,(
% 1.40/0.54    v1_xboole_0(sK1) | ~v2_tex_2(sK1,sK0) | l1_pre_topc(sK3(sK0,sK1))),
% 1.40/0.54    inference(resolution,[],[f475,f84])).
% 1.40/0.54  fof(f475,plain,(
% 1.40/0.54    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3) | ~v2_tex_2(X3,sK0) | l1_pre_topc(sK3(sK0,X3))) )),
% 1.40/0.54    inference(resolution,[],[f472,f126])).
% 1.40/0.54  fof(f126,plain,(
% 1.40/0.54    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) )),
% 1.40/0.54    inference(resolution,[],[f94,f82])).
% 1.40/0.54  fof(f94,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f35])).
% 1.40/0.54  fof(f35,plain,(
% 1.40/0.54    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.40/0.54    inference(ennf_transformation,[],[f11])).
% 1.40/0.54  fof(f11,axiom,(
% 1.40/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.40/0.54  fof(f472,plain,(
% 1.40/0.54    ( ! [X0] : (m1_pre_topc(sK3(sK0,X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | ~v2_tex_2(X0,sK0)) )),
% 1.40/0.54    inference(global_subsumption,[],[f82,f79,f469])).
% 1.40/0.54  fof(f469,plain,(
% 1.40/0.54    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | ~l1_pre_topc(sK0) | m1_pre_topc(sK3(sK0,X0),sK0) | v2_struct_0(sK0)) )),
% 1.40/0.54    inference(resolution,[],[f104,f80])).
% 1.40/0.54  fof(f80,plain,(
% 1.40/0.54    v2_pre_topc(sK0)),
% 1.40/0.54    inference(cnf_transformation,[],[f62])).
% 1.40/0.54  fof(f104,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | m1_pre_topc(sK3(X0,X1),X0) | v2_struct_0(X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f66])).
% 1.40/0.54  fof(f66,plain,(
% 1.40/0.54    ! [X0] : (! [X1] : ((u1_struct_0(sK3(X0,X1)) = X1 & m1_pre_topc(sK3(X0,X1),X0) & v1_tdlat_3(sK3(X0,X1)) & ~v2_struct_0(sK3(X0,X1))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.40/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f46,f65])).
% 1.40/0.54  fof(f65,plain,(
% 1.40/0.54    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK3(X0,X1)) = X1 & m1_pre_topc(sK3(X0,X1),X0) & v1_tdlat_3(sK3(X0,X1)) & ~v2_struct_0(sK3(X0,X1))))),
% 1.40/0.54    introduced(choice_axiom,[])).
% 1.40/0.54  fof(f46,plain,(
% 1.40/0.54    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.40/0.54    inference(flattening,[],[f45])).
% 1.40/0.54  fof(f45,plain,(
% 1.40/0.54    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.40/0.54    inference(ennf_transformation,[],[f24])).
% 1.40/0.54  fof(f24,plain,(
% 1.40/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 1.40/0.54    inference(pure_predicate_removal,[],[f20])).
% 1.40/0.54  fof(f20,axiom,(
% 1.40/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tex_2)).
% 1.40/0.54  fof(f529,plain,(
% 1.40/0.54    ~l1_pre_topc(sK3(sK0,sK1)) | ~v2_tex_2(sK1,sK0) | sK1 = k1_tarski(sK4(sK1))),
% 1.40/0.54    inference(resolution,[],[f528,f89])).
% 1.40/0.54  fof(f528,plain,(
% 1.40/0.54    ~l1_struct_0(sK3(sK0,sK1)) | sK1 = k1_tarski(sK4(sK1)) | ~v2_tex_2(sK1,sK0)),
% 1.40/0.54    inference(global_subsumption,[],[f86,f527])).
% 1.40/0.54  fof(f527,plain,(
% 1.40/0.54    ~l1_struct_0(sK3(sK0,sK1)) | v1_zfmisc_1(sK1) | sK1 = k1_tarski(sK4(sK1)) | ~v2_tex_2(sK1,sK0)),
% 1.40/0.54    inference(resolution,[],[f526,f503])).
% 1.40/0.54  fof(f503,plain,(
% 1.40/0.54    v7_struct_0(sK3(sK0,sK1)) | ~v2_tex_2(sK1,sK0)),
% 1.40/0.54    inference(global_subsumption,[],[f84,f83,f82,f80,f79,f502])).
% 1.40/0.54  fof(f502,plain,(
% 1.40/0.54    ~v2_tex_2(sK1,sK0) | v7_struct_0(sK3(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.40/0.54    inference(duplicate_literal_removal,[],[f501])).
% 1.40/0.54  fof(f501,plain,(
% 1.40/0.54    ~v2_tex_2(sK1,sK0) | v7_struct_0(sK3(sK0,sK1)) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.40/0.54    inference(resolution,[],[f495,f102])).
% 1.40/0.54  fof(f102,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~v2_struct_0(sK3(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f66])).
% 1.40/0.54  fof(f495,plain,(
% 1.40/0.54    v2_struct_0(sK3(sK0,sK1)) | ~v2_tex_2(sK1,sK0) | v7_struct_0(sK3(sK0,sK1))),
% 1.40/0.54    inference(subsumption_resolution,[],[f485,f491])).
% 1.40/0.54  fof(f485,plain,(
% 1.40/0.54    v7_struct_0(sK3(sK0,sK1)) | ~v2_tex_2(sK1,sK0) | v2_struct_0(sK3(sK0,sK1)) | ~l1_pre_topc(sK3(sK0,sK1))),
% 1.40/0.54    inference(global_subsumption,[],[f397,f482])).
% 1.40/0.54  fof(f482,plain,(
% 1.40/0.54    v2_tdlat_3(sK3(sK0,sK1)) | ~v2_tex_2(sK1,sK0)),
% 1.40/0.54    inference(global_subsumption,[],[f83,f481])).
% 1.40/0.54  fof(f481,plain,(
% 1.40/0.54    v1_xboole_0(sK1) | ~v2_tex_2(sK1,sK0) | v2_tdlat_3(sK3(sK0,sK1))),
% 1.40/0.54    inference(resolution,[],[f474,f84])).
% 1.40/0.54  fof(f474,plain,(
% 1.40/0.54    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X2) | ~v2_tex_2(X2,sK0) | v2_tdlat_3(sK3(sK0,X2))) )),
% 1.40/0.54    inference(resolution,[],[f472,f157])).
% 1.40/0.54  fof(f157,plain,(
% 1.40/0.54    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_tdlat_3(X0)) )),
% 1.40/0.54    inference(global_subsumption,[],[f82,f81,f79,f154])).
% 1.40/0.54  fof(f154,plain,(
% 1.40/0.54    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | v2_tdlat_3(X0) | v2_struct_0(sK0)) )),
% 1.40/0.54    inference(resolution,[],[f100,f80])).
% 1.40/0.54  fof(f100,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | v2_tdlat_3(X1) | v2_struct_0(X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f42])).
% 1.40/0.54  fof(f42,plain,(
% 1.40/0.54    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.40/0.54    inference(flattening,[],[f41])).
% 1.40/0.54  fof(f41,plain,(
% 1.40/0.54    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.40/0.54    inference(ennf_transformation,[],[f17])).
% 1.40/0.54  fof(f17,axiom,(
% 1.40/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_tdlat_3(X1)))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_tdlat_3)).
% 1.40/0.54  fof(f81,plain,(
% 1.40/0.54    v2_tdlat_3(sK0)),
% 1.40/0.54    inference(cnf_transformation,[],[f62])).
% 1.40/0.54  fof(f397,plain,(
% 1.40/0.54    ~v2_tdlat_3(sK3(sK0,sK1)) | v7_struct_0(sK3(sK0,sK1)) | ~v2_tex_2(sK1,sK0) | v2_struct_0(sK3(sK0,sK1)) | ~l1_pre_topc(sK3(sK0,sK1))),
% 1.40/0.54    inference(duplicate_literal_removal,[],[f396])).
% 1.40/0.54  fof(f396,plain,(
% 1.40/0.54    ~v2_tdlat_3(sK3(sK0,sK1)) | v7_struct_0(sK3(sK0,sK1)) | ~v2_tex_2(sK1,sK0) | v2_struct_0(sK3(sK0,sK1)) | ~l1_pre_topc(sK3(sK0,sK1)) | ~v2_tdlat_3(sK3(sK0,sK1)) | ~l1_pre_topc(sK3(sK0,sK1))),
% 1.40/0.54    inference(resolution,[],[f388,f90])).
% 1.40/0.54  fof(f90,plain,(
% 1.40/0.54    ( ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f32])).
% 1.40/0.54  fof(f32,plain,(
% 1.40/0.54    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 1.40/0.54    inference(flattening,[],[f31])).
% 1.40/0.54  fof(f31,plain,(
% 1.40/0.54    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 1.40/0.54    inference(ennf_transformation,[],[f15])).
% 1.40/0.54  fof(f15,axiom,(
% 1.40/0.54    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).
% 1.40/0.54  fof(f388,plain,(
% 1.40/0.54    ~v2_pre_topc(sK3(sK0,sK1)) | ~v2_tdlat_3(sK3(sK0,sK1)) | v7_struct_0(sK3(sK0,sK1)) | ~v2_tex_2(sK1,sK0) | v2_struct_0(sK3(sK0,sK1)) | ~l1_pre_topc(sK3(sK0,sK1))),
% 1.40/0.54    inference(resolution,[],[f387,f92])).
% 1.40/0.54  fof(f92,plain,(
% 1.40/0.54    ( ! [X0] : (~v1_tdlat_3(X0) | ~v2_tdlat_3(X0) | v7_struct_0(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f34])).
% 1.40/0.54  fof(f34,plain,(
% 1.40/0.54    ! [X0] : ((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.40/0.54    inference(flattening,[],[f33])).
% 1.40/0.54  fof(f33,plain,(
% 1.40/0.54    ! [X0] : (((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | (~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.40/0.54    inference(ennf_transformation,[],[f16])).
% 1.40/0.54  fof(f16,axiom,(
% 1.40/0.54    ! [X0] : (l1_pre_topc(X0) => ((v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0))))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_1)).
% 1.40/0.54  % (5948)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.40/0.54  fof(f387,plain,(
% 1.40/0.54    v1_tdlat_3(sK3(sK0,sK1)) | ~v2_tex_2(sK1,sK0)),
% 1.40/0.54    inference(global_subsumption,[],[f83,f385])).
% 1.40/0.54  fof(f385,plain,(
% 1.40/0.54    ~v2_tex_2(sK1,sK0) | v1_xboole_0(sK1) | v1_tdlat_3(sK3(sK0,sK1))),
% 1.40/0.54    inference(resolution,[],[f384,f84])).
% 1.40/0.54  fof(f384,plain,(
% 1.40/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | v1_xboole_0(X0) | v1_tdlat_3(sK3(sK0,X0))) )),
% 1.40/0.54    inference(global_subsumption,[],[f82,f79,f381])).
% 1.40/0.54  fof(f381,plain,(
% 1.40/0.54    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | ~l1_pre_topc(sK0) | v1_tdlat_3(sK3(sK0,X0)) | v2_struct_0(sK0)) )),
% 1.40/0.54    inference(resolution,[],[f103,f80])).
% 1.40/0.54  fof(f103,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v1_tdlat_3(sK3(X0,X1)) | v2_struct_0(X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f66])).
% 1.40/0.54  fof(f526,plain,(
% 1.40/0.54    ~v7_struct_0(sK3(sK0,sK1)) | ~l1_struct_0(sK3(sK0,sK1)) | v1_zfmisc_1(sK1) | sK1 = k1_tarski(sK4(sK1))),
% 1.40/0.54    inference(superposition,[],[f106,f525])).
% 1.40/0.54  fof(f525,plain,(
% 1.40/0.54    sK1 = u1_struct_0(sK3(sK0,sK1)) | sK1 = k1_tarski(sK4(sK1))),
% 1.40/0.54    inference(global_subsumption,[],[f83,f522])).
% 1.40/0.54  fof(f522,plain,(
% 1.40/0.54    sK1 = k1_tarski(sK4(sK1)) | sK1 = u1_struct_0(sK3(sK0,sK1)) | v1_xboole_0(sK1)),
% 1.40/0.54    inference(resolution,[],[f521,f108])).
% 1.40/0.54  fof(f521,plain,(
% 1.40/0.54    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_tarski(X0) = sK1 | sK1 = u1_struct_0(sK3(sK0,sK1))) )),
% 1.40/0.54    inference(global_subsumption,[],[f87,f520])).
% 1.40/0.54  fof(f520,plain,(
% 1.40/0.54    ( ! [X0] : (sK1 = u1_struct_0(sK3(sK0,sK1)) | k1_tarski(X0) = sK1 | v1_xboole_0(k1_tarski(X0)) | ~r2_hidden(X0,sK1)) )),
% 1.40/0.54    inference(resolution,[],[f519,f120])).
% 1.40/0.54  fof(f519,plain,(
% 1.40/0.54    ( ! [X0] : (~r1_tarski(X0,sK1) | sK1 = u1_struct_0(sK3(sK0,sK1)) | sK1 = X0 | v1_xboole_0(X0)) )),
% 1.40/0.54    inference(global_subsumption,[],[f83,f518])).
% 1.40/0.54  fof(f518,plain,(
% 1.40/0.54    ( ! [X0] : (sK1 = u1_struct_0(sK3(sK0,sK1)) | ~r1_tarski(X0,sK1) | sK1 = X0 | v1_xboole_0(sK1) | v1_xboole_0(X0)) )),
% 1.40/0.54    inference(resolution,[],[f517,f88])).
% 1.40/0.54  fof(f517,plain,(
% 1.40/0.54    v1_zfmisc_1(sK1) | sK1 = u1_struct_0(sK3(sK0,sK1))),
% 1.40/0.54    inference(resolution,[],[f516,f85])).
% 1.40/0.54  fof(f86,plain,(
% 1.40/0.54    ~v2_tex_2(sK1,sK0) | ~v1_zfmisc_1(sK1)),
% 1.40/0.54    inference(cnf_transformation,[],[f62])).
% 1.40/0.54  fof(f87,plain,(
% 1.40/0.54    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 1.40/0.54    inference(cnf_transformation,[],[f3])).
% 1.40/0.54  fof(f3,axiom,(
% 1.40/0.54    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).
% 1.40/0.54  fof(f341,plain,(
% 1.40/0.54    v2_tex_2(k1_tarski(sK4(sK1)),sK0) | ~m1_subset_1(sK4(sK1),u1_struct_0(sK0))),
% 1.40/0.54    inference(superposition,[],[f222,f340])).
% 1.40/0.54  fof(f340,plain,(
% 1.40/0.54    k1_tarski(sK4(sK1)) = k6_domain_1(u1_struct_0(sK0),sK4(sK1))),
% 1.40/0.54    inference(global_subsumption,[],[f83,f338])).
% 1.40/0.54  fof(f338,plain,(
% 1.40/0.54    k1_tarski(sK4(sK1)) = k6_domain_1(u1_struct_0(sK0),sK4(sK1)) | v1_xboole_0(sK1)),
% 1.40/0.54    inference(resolution,[],[f333,f84])).
% 1.40/0.54  fof(f333,plain,(
% 1.40/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tarski(sK4(sK1)) = k6_domain_1(u1_struct_0(sK0),sK4(sK1)) | v1_xboole_0(X0)) )),
% 1.40/0.54    inference(resolution,[],[f332,f95])).
% 1.40/0.54  fof(f95,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f36])).
% 1.40/0.54  fof(f36,plain,(
% 1.40/0.54    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.40/0.54    inference(ennf_transformation,[],[f5])).
% 1.40/0.54  fof(f5,axiom,(
% 1.40/0.54    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.40/0.54  fof(f332,plain,(
% 1.40/0.54    v1_xboole_0(u1_struct_0(sK0)) | k1_tarski(sK4(sK1)) = k6_domain_1(u1_struct_0(sK0),sK4(sK1))),
% 1.40/0.54    inference(global_subsumption,[],[f84,f83,f82,f79,f331])).
% 1.40/0.54  fof(f331,plain,(
% 1.40/0.54    v1_xboole_0(u1_struct_0(sK0)) | k1_tarski(sK4(sK1)) = k6_domain_1(u1_struct_0(sK0),sK4(sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.40/0.54    inference(resolution,[],[f330,f97])).
% 1.40/0.54  fof(f330,plain,(
% 1.40/0.54    v2_struct_0(sK2(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK0)) | k1_tarski(sK4(sK1)) = k6_domain_1(u1_struct_0(sK0),sK4(sK1))),
% 1.40/0.54    inference(global_subsumption,[],[f83,f326])).
% 1.40/0.54  fof(f326,plain,(
% 1.40/0.54    k1_tarski(sK4(sK1)) = k6_domain_1(u1_struct_0(sK0),sK4(sK1)) | v1_xboole_0(u1_struct_0(sK0)) | v2_struct_0(sK2(sK0,sK1)) | v1_xboole_0(sK1)),
% 1.40/0.54    inference(resolution,[],[f323,f108])).
% 1.40/0.54  fof(f323,plain,(
% 1.40/0.54    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_tarski(X0) = k6_domain_1(u1_struct_0(sK0),X0) | v1_xboole_0(u1_struct_0(sK0)) | v2_struct_0(sK2(sK0,sK1))) )),
% 1.40/0.54    inference(resolution,[],[f319,f109])).
% 1.40/0.54  fof(f319,plain,(
% 1.40/0.54    ( ! [X0] : (~m1_subset_1(X0,sK1) | v2_struct_0(sK2(sK0,sK1)) | k1_tarski(X0) = k6_domain_1(u1_struct_0(sK0),X0) | v1_xboole_0(u1_struct_0(sK0))) )),
% 1.40/0.54    inference(resolution,[],[f318,f114])).
% 1.40/0.54  fof(f114,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1) | v1_xboole_0(X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f57])).
% 1.40/0.54  fof(f57,plain,(
% 1.40/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.40/0.54    inference(flattening,[],[f56])).
% 1.40/0.54  fof(f56,plain,(
% 1.40/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.40/0.54    inference(ennf_transformation,[],[f14])).
% 1.40/0.54  fof(f14,axiom,(
% 1.40/0.54    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.40/0.54  fof(f222,plain,(
% 1.40/0.54    ( ! [X0] : (v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.40/0.54    inference(global_subsumption,[],[f82,f79,f219])).
% 1.40/0.54  fof(f219,plain,(
% 1.40/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0) | v2_struct_0(sK0)) )),
% 1.40/0.54    inference(resolution,[],[f101,f80])).
% 1.40/0.54  fof(f101,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | v2_struct_0(X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f44])).
% 1.40/0.54  fof(f44,plain,(
% 1.40/0.54    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.40/0.54    inference(flattening,[],[f43])).
% 1.40/0.54  fof(f43,plain,(
% 1.40/0.54    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.40/0.54    inference(ennf_transformation,[],[f21])).
% 1.40/0.54  fof(f21,axiom,(
% 1.40/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).
% 1.40/0.54  fof(f550,plain,(
% 1.40/0.54    r2_hidden(sK4(sK1),sK1)),
% 1.40/0.54    inference(superposition,[],[f122,f541])).
% 1.40/0.54  fof(f122,plain,(
% 1.40/0.54    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 1.40/0.54    inference(equality_resolution,[],[f121])).
% 1.40/0.54  fof(f121,plain,(
% 1.40/0.54    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 1.40/0.54    inference(equality_resolution,[],[f116])).
% 1.40/0.54  fof(f116,plain,(
% 1.40/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.40/0.54    inference(cnf_transformation,[],[f77])).
% 1.40/0.54  fof(f77,plain,(
% 1.40/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.40/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f75,f76])).
% 1.40/0.54  fof(f76,plain,(
% 1.40/0.54    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1))))),
% 1.40/0.54    introduced(choice_axiom,[])).
% 1.40/0.54  fof(f75,plain,(
% 1.40/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.40/0.54    inference(rectify,[],[f74])).
% 1.40/0.54  fof(f74,plain,(
% 1.40/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.40/0.54    inference(nnf_transformation,[],[f2])).
% 1.40/0.54  fof(f2,axiom,(
% 1.40/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.40/0.54  fof(f79,plain,(
% 1.40/0.54    ~v2_struct_0(sK0)),
% 1.40/0.54    inference(cnf_transformation,[],[f62])).
% 1.40/0.54  fof(f82,plain,(
% 1.40/0.54    l1_pre_topc(sK0)),
% 1.40/0.54    inference(cnf_transformation,[],[f62])).
% 1.40/0.54  fof(f83,plain,(
% 1.40/0.54    ~v1_xboole_0(sK1)),
% 1.40/0.54    inference(cnf_transformation,[],[f62])).
% 1.40/0.54  fof(f84,plain,(
% 1.40/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.40/0.54    inference(cnf_transformation,[],[f62])).
% 1.40/0.54  fof(f516,plain,(
% 1.40/0.54    ~v2_tex_2(sK1,sK0) | sK1 = u1_struct_0(sK3(sK0,sK1))),
% 1.40/0.54    inference(global_subsumption,[],[f83,f515])).
% 1.40/0.54  fof(f515,plain,(
% 1.40/0.54    ~v2_tex_2(sK1,sK0) | v1_xboole_0(sK1) | sK1 = u1_struct_0(sK3(sK0,sK1))),
% 1.40/0.54    inference(resolution,[],[f479,f84])).
% 1.40/0.55  fof(f479,plain,(
% 1.40/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | v1_xboole_0(X0) | u1_struct_0(sK3(sK0,X0)) = X0) )),
% 1.40/0.55    inference(global_subsumption,[],[f82,f79,f476])).
% 1.40/0.55  fof(f476,plain,(
% 1.40/0.55    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | ~l1_pre_topc(sK0) | u1_struct_0(sK3(sK0,X0)) = X0 | v2_struct_0(sK0)) )),
% 1.40/0.55    inference(resolution,[],[f105,f80])).
% 1.40/0.55  fof(f105,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | u1_struct_0(sK3(X0,X1)) = X1 | v2_struct_0(X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f66])).
% 1.40/0.55  fof(f106,plain,(
% 1.40/0.55    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f48])).
% 1.40/0.55  fof(f48,plain,(
% 1.40/0.55    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 1.40/0.55    inference(flattening,[],[f47])).
% 1.40/0.55  fof(f47,plain,(
% 1.40/0.55    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 1.40/0.55    inference(ennf_transformation,[],[f12])).
% 1.40/0.55  fof(f12,axiom,(
% 1.40/0.55    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).
% 1.40/0.55  fof(f636,plain,(
% 1.40/0.55    ~v1_zfmisc_1(sK1)),
% 1.40/0.55    inference(subsumption_resolution,[],[f86,f635])).
% 1.40/0.55  fof(f648,plain,(
% 1.40/0.55    v7_struct_0(sK3(sK0,sK1))),
% 1.40/0.55    inference(subsumption_resolution,[],[f503,f635])).
% 1.40/0.55  fof(f639,plain,(
% 1.40/0.55    l1_pre_topc(sK3(sK0,sK1))),
% 1.40/0.55    inference(subsumption_resolution,[],[f491,f635])).
% 1.40/0.55  % SZS output end Proof for theBenchmark
% 1.40/0.55  % (5940)------------------------------
% 1.40/0.55  % (5940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (5940)Termination reason: Refutation
% 1.40/0.55  
% 1.40/0.55  % (5940)Memory used [KB]: 7291
% 1.40/0.55  % (5940)Time elapsed: 0.129 s
% 1.40/0.55  % (5940)------------------------------
% 1.40/0.55  % (5940)------------------------------
% 1.40/0.55  % (5923)Success in time 0.188 s
%------------------------------------------------------------------------------
