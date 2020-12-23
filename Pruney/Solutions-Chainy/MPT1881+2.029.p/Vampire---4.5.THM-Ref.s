%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:57 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 967 expanded)
%              Number of leaves         :   21 ( 259 expanded)
%              Depth                    :   29
%              Number of atoms          :  606 (5643 expanded)
%              Number of equality atoms :   58 ( 216 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f393,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f96,f169,f193,f383])).

fof(f383,plain,
    ( ~ spl4_1
    | spl4_4 ),
    inference(avatar_contradiction_clause,[],[f382])).

fof(f382,plain,
    ( $false
    | ~ spl4_1
    | spl4_4 ),
    inference(subsumption_resolution,[],[f381,f228])).

% (17533)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f228,plain,(
    r1_tarski(sK1,k2_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f227])).

fof(f227,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0))
    | r1_tarski(sK1,k2_struct_0(sK0)) ),
    inference(resolution,[],[f225,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f51,f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f225,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(X0,k2_struct_0(sK0)),sK1)
      | r1_tarski(X0,k2_struct_0(sK0)) ) ),
    inference(resolution,[],[f104,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f104,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_struct_0(sK0))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f103,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f103,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f58,f101])).

fof(f101,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f100,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f100,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f57,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f57,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( v1_subset_1(sK1,u1_struct_0(sK0))
      | ~ v3_tex_2(sK1,sK0) )
    & ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
      | v3_tex_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v1_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f41,f40])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( v1_subset_1(X1,u1_struct_0(X0))
              | ~ v3_tex_2(X1,X0) )
            & ( ~ v1_subset_1(X1,u1_struct_0(X0))
              | v3_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(sK0))
            | ~ v3_tex_2(X1,sK0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(sK0))
            | v3_tex_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v1_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X1] :
        ( ( v1_subset_1(X1,u1_struct_0(sK0))
          | ~ v3_tex_2(X1,sK0) )
        & ( ~ v1_subset_1(X1,u1_struct_0(sK0))
          | v3_tex_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( v1_subset_1(sK1,u1_struct_0(sK0))
        | ~ v3_tex_2(sK1,sK0) )
      & ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
        | v3_tex_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

% (17522)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tex_2)).

fof(f58,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f381,plain,
    ( ~ r1_tarski(sK1,k2_struct_0(sK0))
    | ~ spl4_1
    | spl4_4 ),
    inference(forward_demodulation,[],[f380,f62])).

fof(f62,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f380,plain,
    ( ~ r1_tarski(sK1,k2_subset_1(k2_struct_0(sK0)))
    | ~ spl4_1
    | spl4_4 ),
    inference(subsumption_resolution,[],[f379,f176])).

fof(f176,plain,
    ( sK1 != k2_struct_0(sK0)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl4_4
  <=> sK1 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f379,plain,
    ( sK1 = k2_struct_0(sK0)
    | ~ r1_tarski(sK1,k2_subset_1(k2_struct_0(sK0)))
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f376,f62])).

fof(f376,plain,
    ( sK1 = k2_subset_1(k2_struct_0(sK0))
    | ~ r1_tarski(sK1,k2_subset_1(k2_struct_0(sK0)))
    | ~ spl4_1 ),
    inference(resolution,[],[f373,f63])).

% (17511)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f63,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f373,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | sK1 = X1
        | ~ r1_tarski(sK1,X1) )
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f372,f220])).

% (17508)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f220,plain,(
    ! [X10] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_tex_2(X10,sK0) ) ),
    inference(subsumption_resolution,[],[f219,f54])).

fof(f54,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f219,plain,(
    ! [X10] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_tex_2(X10,sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f218,f55])).

fof(f55,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f218,plain,(
    ! [X10] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_tex_2(X10,sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f217,f56])).

fof(f56,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f217,plain,(
    ! [X10] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_tex_2(X10,sK0)
      | ~ v1_tdlat_3(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f205,f57])).

fof(f205,plain,(
    ! [X10] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_tex_2(X10,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_tdlat_3(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f77,f101])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

fof(f372,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK1,X1)
        | ~ v2_tex_2(X1,sK0)
        | sK1 = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f366,f89])).

fof(f89,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl4_1
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f366,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK1,X1)
      | ~ v2_tex_2(X1,sK0)
      | sK1 = X1
      | ~ v3_tex_2(sK1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(resolution,[],[f212,f103])).

fof(f212,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_tarski(X5,X4)
      | ~ v2_tex_2(X4,sK0)
      | X4 = X5
      | ~ v3_tex_2(X5,sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f200,f57])).

fof(f200,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_tarski(X5,X4)
      | ~ v2_tex_2(X4,sK0)
      | X4 = X5
      | ~ v3_tex_2(X5,sK0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f72,f101])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X3)
      | ~ v2_tex_2(X3,X0)
      | X1 = X3
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK2(X0,X1) != X1
                & r1_tarski(X1,sK2(X0,X1))
                & v2_tex_2(sK2(X0,X1),X0)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f46,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK2(X0,X1) != X1
        & r1_tarski(X1,sK2(X0,X1))
        & v2_tex_2(sK2(X0,X1),X0)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

fof(f193,plain,
    ( ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f189,f180])).

fof(f180,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f179,f177])).

fof(f177,plain,
    ( sK1 = k2_struct_0(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f175])).

fof(f179,plain,
    ( v1_subset_1(sK1,k2_struct_0(sK0))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f94,f101])).

fof(f94,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl4_2
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f189,plain,
    ( ~ v1_subset_1(sK1,sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f182,f86])).

fof(f86,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
      | ~ v1_subset_1(X1,X1) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f182,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f103,f177])).

fof(f169,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f167,f108])).

fof(f108,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | spl4_2 ),
    inference(backward_demodulation,[],[f103,f106])).

fof(f106,plain,
    ( sK1 = k2_struct_0(sK0)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f105,f102])).

fof(f102,plain,
    ( ~ v1_subset_1(sK1,k2_struct_0(sK0))
    | spl4_2 ),
    inference(backward_demodulation,[],[f93,f101])).

fof(f93,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f105,plain,
    ( sK1 = k2_struct_0(sK0)
    | v1_subset_1(sK1,k2_struct_0(sK0)) ),
    inference(resolution,[],[f103,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f167,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | spl4_1
    | spl4_2 ),
    inference(forward_demodulation,[],[f166,f110])).

fof(f110,plain,
    ( u1_struct_0(sK0) = sK1
    | spl4_2 ),
    inference(backward_demodulation,[],[f101,f106])).

fof(f166,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f165,f57])).

fof(f165,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f164,f155])).

fof(f155,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f154,f90])).

fof(f90,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f154,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ v1_tops_1(sK1,sK0)
    | spl4_2 ),
    inference(forward_demodulation,[],[f153,f62])).

fof(f153,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | v3_tex_2(k2_subset_1(sK1),sK0)
    | spl4_2 ),
    inference(forward_demodulation,[],[f151,f62])).

fof(f151,plain,
    ( ~ v1_tops_1(k2_subset_1(sK1),sK0)
    | v3_tex_2(k2_subset_1(sK1),sK0)
    | spl4_2 ),
    inference(resolution,[],[f144,f63])).

fof(f144,plain,
    ( ! [X11] :
        ( ~ m1_subset_1(X11,k1_zfmisc_1(sK1))
        | ~ v1_tops_1(X11,sK0)
        | v3_tex_2(X11,sK0) )
    | spl4_2 ),
    inference(subsumption_resolution,[],[f143,f140])).

% (17509)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f140,plain,
    ( ! [X10] :
        ( ~ m1_subset_1(X10,k1_zfmisc_1(sK1))
        | v2_tex_2(X10,sK0) )
    | spl4_2 ),
    inference(subsumption_resolution,[],[f139,f54])).

fof(f139,plain,
    ( ! [X10] :
        ( ~ m1_subset_1(X10,k1_zfmisc_1(sK1))
        | v2_tex_2(X10,sK0)
        | v2_struct_0(sK0) )
    | spl4_2 ),
    inference(subsumption_resolution,[],[f138,f55])).

fof(f138,plain,
    ( ! [X10] :
        ( ~ m1_subset_1(X10,k1_zfmisc_1(sK1))
        | v2_tex_2(X10,sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl4_2 ),
    inference(subsumption_resolution,[],[f137,f56])).

fof(f137,plain,
    ( ! [X10] :
        ( ~ m1_subset_1(X10,k1_zfmisc_1(sK1))
        | v2_tex_2(X10,sK0)
        | ~ v1_tdlat_3(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl4_2 ),
    inference(subsumption_resolution,[],[f124,f57])).

fof(f124,plain,
    ( ! [X10] :
        ( ~ m1_subset_1(X10,k1_zfmisc_1(sK1))
        | v2_tex_2(X10,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_tdlat_3(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl4_2 ),
    inference(superposition,[],[f77,f110])).

fof(f143,plain,
    ( ! [X11] :
        ( ~ m1_subset_1(X11,k1_zfmisc_1(sK1))
        | ~ v2_tex_2(X11,sK0)
        | ~ v1_tops_1(X11,sK0)
        | v3_tex_2(X11,sK0) )
    | spl4_2 ),
    inference(subsumption_resolution,[],[f142,f54])).

fof(f142,plain,
    ( ! [X11] :
        ( ~ m1_subset_1(X11,k1_zfmisc_1(sK1))
        | ~ v2_tex_2(X11,sK0)
        | ~ v1_tops_1(X11,sK0)
        | v3_tex_2(X11,sK0)
        | v2_struct_0(sK0) )
    | spl4_2 ),
    inference(subsumption_resolution,[],[f141,f55])).

fof(f141,plain,
    ( ! [X11] :
        ( ~ m1_subset_1(X11,k1_zfmisc_1(sK1))
        | ~ v2_tex_2(X11,sK0)
        | ~ v1_tops_1(X11,sK0)
        | v3_tex_2(X11,sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl4_2 ),
    inference(subsumption_resolution,[],[f125,f57])).

fof(f125,plain,
    ( ! [X11] :
        ( ~ m1_subset_1(X11,k1_zfmisc_1(sK1))
        | ~ v2_tex_2(X11,sK0)
        | ~ v1_tops_1(X11,sK0)
        | v3_tex_2(X11,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl4_2 ),
    inference(superposition,[],[f78,f110])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ v1_tops_1(X1,X0)
      | v3_tex_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_tex_2(X1,X0)
              & v1_tops_1(X1,X0) )
           => v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tex_2)).

fof(f164,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f162,f106])).

fof(f162,plain,
    ( sK1 != k2_struct_0(sK0)
    | v1_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl4_2 ),
    inference(superposition,[],[f70,f160])).

% (17513)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f160,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | spl4_2 ),
    inference(forward_demodulation,[],[f159,f62])).

fof(f159,plain,
    ( k2_subset_1(sK1) = k2_pre_topc(sK0,k2_subset_1(sK1))
    | spl4_2 ),
    inference(subsumption_resolution,[],[f158,f111])).

fof(f111,plain,
    ( v4_pre_topc(sK1,sK0)
    | spl4_2 ),
    inference(backward_demodulation,[],[f98,f106])).

fof(f98,plain,(
    v4_pre_topc(k2_struct_0(sK0),sK0) ),
    inference(subsumption_resolution,[],[f97,f57])).

fof(f97,plain,
    ( ~ l1_pre_topc(sK0)
    | v4_pre_topc(k2_struct_0(sK0),sK0) ),
    inference(resolution,[],[f55,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(k2_struct_0(X0),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

fof(f158,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | k2_subset_1(sK1) = k2_pre_topc(sK0,k2_subset_1(sK1))
    | spl4_2 ),
    inference(forward_demodulation,[],[f156,f62])).

fof(f156,plain,
    ( ~ v4_pre_topc(k2_subset_1(sK1),sK0)
    | k2_subset_1(sK1) = k2_pre_topc(sK0,k2_subset_1(sK1))
    | spl4_2 ),
    inference(resolution,[],[f126,f63])).

fof(f126,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | ~ v4_pre_topc(X0,sK0)
        | k2_pre_topc(sK0,X0) = X0 )
    | spl4_2 ),
    inference(subsumption_resolution,[],[f115,f57])).

fof(f115,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | ~ v4_pre_topc(X0,sK0)
        | k2_pre_topc(sK0,X0) = X0
        | ~ l1_pre_topc(sK0) )
    | spl4_2 ),
    inference(superposition,[],[f67,f110])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

fof(f96,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f59,f92,f88])).

fof(f59,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f95,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f60,f92,f88])).

% (17515)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f60,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 16:41:51 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.51  % (17514)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.20/0.53  % (17529)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.20/0.53  % (17506)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.20/0.53  % (17506)Refutation not found, incomplete strategy% (17506)------------------------------
% 1.20/0.53  % (17506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.53  % (17506)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.53  
% 1.20/0.53  % (17506)Memory used [KB]: 1663
% 1.20/0.53  % (17506)Time elapsed: 0.100 s
% 1.20/0.53  % (17506)------------------------------
% 1.20/0.53  % (17506)------------------------------
% 1.20/0.53  % (17521)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.20/0.54  % (17514)Refutation found. Thanks to Tanya!
% 1.20/0.54  % SZS status Theorem for theBenchmark
% 1.20/0.54  % (17507)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.37/0.55  % (17528)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.37/0.55  % (17510)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.37/0.55  % SZS output start Proof for theBenchmark
% 1.37/0.55  fof(f393,plain,(
% 1.37/0.55    $false),
% 1.37/0.55    inference(avatar_sat_refutation,[],[f95,f96,f169,f193,f383])).
% 1.37/0.55  fof(f383,plain,(
% 1.37/0.55    ~spl4_1 | spl4_4),
% 1.37/0.55    inference(avatar_contradiction_clause,[],[f382])).
% 1.37/0.55  fof(f382,plain,(
% 1.37/0.55    $false | (~spl4_1 | spl4_4)),
% 1.37/0.55    inference(subsumption_resolution,[],[f381,f228])).
% 1.37/0.55  % (17533)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.37/0.55  fof(f228,plain,(
% 1.37/0.55    r1_tarski(sK1,k2_struct_0(sK0))),
% 1.37/0.55    inference(duplicate_literal_removal,[],[f227])).
% 1.37/0.55  fof(f227,plain,(
% 1.37/0.55    r1_tarski(sK1,k2_struct_0(sK0)) | r1_tarski(sK1,k2_struct_0(sK0))),
% 1.37/0.55    inference(resolution,[],[f225,f84])).
% 1.37/0.55  fof(f84,plain,(
% 1.37/0.55    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f53])).
% 1.37/0.55  fof(f53,plain,(
% 1.37/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.37/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f51,f52])).
% 1.37/0.55  fof(f52,plain,(
% 1.37/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.37/0.55    introduced(choice_axiom,[])).
% 1.37/0.55  fof(f51,plain,(
% 1.37/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.37/0.55    inference(rectify,[],[f50])).
% 1.37/0.55  fof(f50,plain,(
% 1.37/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.37/0.55    inference(nnf_transformation,[],[f37])).
% 1.37/0.55  fof(f37,plain,(
% 1.37/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.37/0.55    inference(ennf_transformation,[],[f1])).
% 1.37/0.55  fof(f1,axiom,(
% 1.37/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.37/0.55  fof(f225,plain,(
% 1.37/0.55    ( ! [X0] : (~r2_hidden(sK3(X0,k2_struct_0(sK0)),sK1) | r1_tarski(X0,k2_struct_0(sK0))) )),
% 1.37/0.55    inference(resolution,[],[f104,f85])).
% 1.37/0.55  fof(f85,plain,(
% 1.37/0.55    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f53])).
% 1.37/0.55  fof(f104,plain,(
% 1.37/0.55    ( ! [X0] : (r2_hidden(X0,k2_struct_0(sK0)) | ~r2_hidden(X0,sK1)) )),
% 1.37/0.55    inference(resolution,[],[f103,f82])).
% 1.37/0.55  fof(f82,plain,(
% 1.37/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f36])).
% 1.37/0.55  fof(f36,plain,(
% 1.37/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.37/0.55    inference(ennf_transformation,[],[f4])).
% 1.37/0.55  fof(f4,axiom,(
% 1.37/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.37/0.55  fof(f103,plain,(
% 1.37/0.55    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.37/0.55    inference(backward_demodulation,[],[f58,f101])).
% 1.37/0.55  fof(f101,plain,(
% 1.37/0.55    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.37/0.55    inference(resolution,[],[f100,f64])).
% 1.37/0.55  fof(f64,plain,(
% 1.37/0.55    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f20])).
% 1.37/0.55  fof(f20,plain,(
% 1.37/0.55    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.37/0.55    inference(ennf_transformation,[],[f6])).
% 1.37/0.55  fof(f6,axiom,(
% 1.37/0.55    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 1.37/0.55  fof(f100,plain,(
% 1.37/0.55    l1_struct_0(sK0)),
% 1.37/0.55    inference(resolution,[],[f57,f65])).
% 1.37/0.55  fof(f65,plain,(
% 1.37/0.55    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f21])).
% 1.37/0.55  fof(f21,plain,(
% 1.37/0.55    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.37/0.55    inference(ennf_transformation,[],[f7])).
% 1.37/0.55  fof(f7,axiom,(
% 1.37/0.55    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.37/0.55  fof(f57,plain,(
% 1.37/0.55    l1_pre_topc(sK0)),
% 1.37/0.55    inference(cnf_transformation,[],[f42])).
% 1.37/0.55  fof(f42,plain,(
% 1.37/0.55    ((v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)) & (~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.37/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f41,f40])).
% 1.37/0.55  fof(f40,plain,(
% 1.37/0.55    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((v1_subset_1(X1,u1_struct_0(sK0)) | ~v3_tex_2(X1,sK0)) & (~v1_subset_1(X1,u1_struct_0(sK0)) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.37/0.55    introduced(choice_axiom,[])).
% 1.37/0.55  fof(f41,plain,(
% 1.37/0.55    ? [X1] : ((v1_subset_1(X1,u1_struct_0(sK0)) | ~v3_tex_2(X1,sK0)) & (~v1_subset_1(X1,u1_struct_0(sK0)) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)) & (~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.37/0.55    introduced(choice_axiom,[])).
% 1.37/0.55  fof(f39,plain,(
% 1.37/0.55    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.37/0.55    inference(flattening,[],[f38])).
% 1.37/0.55  fof(f38,plain,(
% 1.37/0.55    ? [X0] : (? [X1] : (((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.37/0.55    inference(nnf_transformation,[],[f19])).
% 1.37/0.55  fof(f19,plain,(
% 1.37/0.55    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.37/0.55    inference(flattening,[],[f18])).
% 1.37/0.55  fof(f18,plain,(
% 1.37/0.55    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.37/0.55    inference(ennf_transformation,[],[f17])).
% 1.37/0.55  fof(f17,negated_conjecture,(
% 1.37/0.55    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 1.37/0.55    inference(negated_conjecture,[],[f16])).
% 1.37/0.55  % (17522)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.37/0.55  fof(f16,conjecture,(
% 1.37/0.55    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tex_2)).
% 1.37/0.55  fof(f58,plain,(
% 1.37/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.37/0.55    inference(cnf_transformation,[],[f42])).
% 1.37/0.55  fof(f381,plain,(
% 1.37/0.55    ~r1_tarski(sK1,k2_struct_0(sK0)) | (~spl4_1 | spl4_4)),
% 1.37/0.55    inference(forward_demodulation,[],[f380,f62])).
% 1.37/0.55  fof(f62,plain,(
% 1.37/0.55    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.37/0.55    inference(cnf_transformation,[],[f2])).
% 1.37/0.55  fof(f2,axiom,(
% 1.37/0.55    ! [X0] : k2_subset_1(X0) = X0),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.37/0.55  fof(f380,plain,(
% 1.37/0.55    ~r1_tarski(sK1,k2_subset_1(k2_struct_0(sK0))) | (~spl4_1 | spl4_4)),
% 1.37/0.55    inference(subsumption_resolution,[],[f379,f176])).
% 1.37/0.55  fof(f176,plain,(
% 1.37/0.55    sK1 != k2_struct_0(sK0) | spl4_4),
% 1.37/0.55    inference(avatar_component_clause,[],[f175])).
% 1.37/0.55  fof(f175,plain,(
% 1.37/0.55    spl4_4 <=> sK1 = k2_struct_0(sK0)),
% 1.37/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.37/0.55  fof(f379,plain,(
% 1.37/0.55    sK1 = k2_struct_0(sK0) | ~r1_tarski(sK1,k2_subset_1(k2_struct_0(sK0))) | ~spl4_1),
% 1.37/0.55    inference(forward_demodulation,[],[f376,f62])).
% 1.37/0.55  fof(f376,plain,(
% 1.37/0.55    sK1 = k2_subset_1(k2_struct_0(sK0)) | ~r1_tarski(sK1,k2_subset_1(k2_struct_0(sK0))) | ~spl4_1),
% 1.37/0.55    inference(resolution,[],[f373,f63])).
% 1.37/0.55  % (17511)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.37/0.55  fof(f63,plain,(
% 1.37/0.55    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.37/0.55    inference(cnf_transformation,[],[f3])).
% 1.37/0.55  fof(f3,axiom,(
% 1.37/0.55    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.37/0.55  fof(f373,plain,(
% 1.37/0.55    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | sK1 = X1 | ~r1_tarski(sK1,X1)) ) | ~spl4_1),
% 1.37/0.55    inference(subsumption_resolution,[],[f372,f220])).
% 1.37/0.55  % (17508)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.37/0.55  fof(f220,plain,(
% 1.37/0.55    ( ! [X10] : (~m1_subset_1(X10,k1_zfmisc_1(k2_struct_0(sK0))) | v2_tex_2(X10,sK0)) )),
% 1.37/0.55    inference(subsumption_resolution,[],[f219,f54])).
% 1.37/0.55  fof(f54,plain,(
% 1.37/0.55    ~v2_struct_0(sK0)),
% 1.37/0.55    inference(cnf_transformation,[],[f42])).
% 1.37/0.55  fof(f219,plain,(
% 1.37/0.55    ( ! [X10] : (~m1_subset_1(X10,k1_zfmisc_1(k2_struct_0(sK0))) | v2_tex_2(X10,sK0) | v2_struct_0(sK0)) )),
% 1.37/0.55    inference(subsumption_resolution,[],[f218,f55])).
% 1.37/0.55  fof(f55,plain,(
% 1.37/0.55    v2_pre_topc(sK0)),
% 1.37/0.55    inference(cnf_transformation,[],[f42])).
% 1.37/0.55  fof(f218,plain,(
% 1.37/0.55    ( ! [X10] : (~m1_subset_1(X10,k1_zfmisc_1(k2_struct_0(sK0))) | v2_tex_2(X10,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.37/0.55    inference(subsumption_resolution,[],[f217,f56])).
% 1.37/0.55  fof(f56,plain,(
% 1.37/0.55    v1_tdlat_3(sK0)),
% 1.37/0.55    inference(cnf_transformation,[],[f42])).
% 1.37/0.55  fof(f217,plain,(
% 1.37/0.55    ( ! [X10] : (~m1_subset_1(X10,k1_zfmisc_1(k2_struct_0(sK0))) | v2_tex_2(X10,sK0) | ~v1_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.37/0.55    inference(subsumption_resolution,[],[f205,f57])).
% 1.37/0.55  fof(f205,plain,(
% 1.37/0.55    ( ! [X10] : (~m1_subset_1(X10,k1_zfmisc_1(k2_struct_0(sK0))) | v2_tex_2(X10,sK0) | ~l1_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.37/0.55    inference(superposition,[],[f77,f101])).
% 1.37/0.55  fof(f77,plain,(
% 1.37/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f30])).
% 1.37/0.55  fof(f30,plain,(
% 1.37/0.55    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.37/0.55    inference(flattening,[],[f29])).
% 1.37/0.55  fof(f29,plain,(
% 1.37/0.55    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.37/0.55    inference(ennf_transformation,[],[f14])).
% 1.37/0.55  fof(f14,axiom,(
% 1.37/0.55    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).
% 1.37/0.55  fof(f372,plain,(
% 1.37/0.55    ( ! [X1] : (~r1_tarski(sK1,X1) | ~v2_tex_2(X1,sK0) | sK1 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl4_1),
% 1.37/0.55    inference(subsumption_resolution,[],[f366,f89])).
% 1.37/0.55  fof(f89,plain,(
% 1.37/0.55    v3_tex_2(sK1,sK0) | ~spl4_1),
% 1.37/0.55    inference(avatar_component_clause,[],[f88])).
% 1.37/0.55  fof(f88,plain,(
% 1.37/0.55    spl4_1 <=> v3_tex_2(sK1,sK0)),
% 1.37/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.37/0.55  fof(f366,plain,(
% 1.37/0.55    ( ! [X1] : (~r1_tarski(sK1,X1) | ~v2_tex_2(X1,sK0) | sK1 = X1 | ~v3_tex_2(sK1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 1.37/0.55    inference(resolution,[],[f212,f103])).
% 1.37/0.55  fof(f212,plain,(
% 1.37/0.55    ( ! [X4,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X5,X4) | ~v2_tex_2(X4,sK0) | X4 = X5 | ~v3_tex_2(X5,sK0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 1.37/0.55    inference(subsumption_resolution,[],[f200,f57])).
% 1.37/0.55  fof(f200,plain,(
% 1.37/0.55    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X5,X4) | ~v2_tex_2(X4,sK0) | X4 = X5 | ~v3_tex_2(X5,sK0) | ~m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 1.37/0.55    inference(superposition,[],[f72,f101])).
% 1.37/0.55  fof(f72,plain,(
% 1.37/0.55    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | X1 = X3 | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f48])).
% 1.37/0.55  fof(f48,plain,(
% 1.37/0.55    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.37/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f46,f47])).
% 1.37/0.55  fof(f47,plain,(
% 1.37/0.55    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.37/0.55    introduced(choice_axiom,[])).
% 1.37/0.55  fof(f46,plain,(
% 1.37/0.55    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.37/0.55    inference(rectify,[],[f45])).
% 1.37/0.55  fof(f45,plain,(
% 1.37/0.55    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.37/0.55    inference(flattening,[],[f44])).
% 1.37/0.55  fof(f44,plain,(
% 1.37/0.55    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.37/0.55    inference(nnf_transformation,[],[f28])).
% 1.37/0.55  fof(f28,plain,(
% 1.37/0.55    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.37/0.55    inference(flattening,[],[f27])).
% 1.37/0.55  fof(f27,plain,(
% 1.37/0.55    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.37/0.55    inference(ennf_transformation,[],[f13])).
% 1.37/0.55  fof(f13,axiom,(
% 1.37/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).
% 1.37/0.55  fof(f193,plain,(
% 1.37/0.55    ~spl4_2 | ~spl4_4),
% 1.37/0.55    inference(avatar_contradiction_clause,[],[f192])).
% 1.37/0.55  fof(f192,plain,(
% 1.37/0.55    $false | (~spl4_2 | ~spl4_4)),
% 1.37/0.55    inference(subsumption_resolution,[],[f189,f180])).
% 1.37/0.55  fof(f180,plain,(
% 1.37/0.55    v1_subset_1(sK1,sK1) | (~spl4_2 | ~spl4_4)),
% 1.37/0.55    inference(backward_demodulation,[],[f179,f177])).
% 1.37/0.55  fof(f177,plain,(
% 1.37/0.55    sK1 = k2_struct_0(sK0) | ~spl4_4),
% 1.37/0.55    inference(avatar_component_clause,[],[f175])).
% 1.37/0.55  fof(f179,plain,(
% 1.37/0.55    v1_subset_1(sK1,k2_struct_0(sK0)) | ~spl4_2),
% 1.37/0.55    inference(forward_demodulation,[],[f94,f101])).
% 1.37/0.55  fof(f94,plain,(
% 1.37/0.55    v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl4_2),
% 1.37/0.55    inference(avatar_component_clause,[],[f92])).
% 1.37/0.55  fof(f92,plain,(
% 1.37/0.55    spl4_2 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.37/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.37/0.55  fof(f189,plain,(
% 1.37/0.55    ~v1_subset_1(sK1,sK1) | ~spl4_4),
% 1.37/0.55    inference(resolution,[],[f182,f86])).
% 1.37/0.55  fof(f86,plain,(
% 1.37/0.55    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(X1)) | ~v1_subset_1(X1,X1)) )),
% 1.37/0.55    inference(equality_resolution,[],[f80])).
% 1.37/0.55  fof(f80,plain,(
% 1.37/0.55    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.37/0.55    inference(cnf_transformation,[],[f49])).
% 1.37/0.55  fof(f49,plain,(
% 1.37/0.55    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.37/0.55    inference(nnf_transformation,[],[f35])).
% 1.37/0.55  fof(f35,plain,(
% 1.37/0.55    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.37/0.55    inference(ennf_transformation,[],[f12])).
% 1.37/0.55  fof(f12,axiom,(
% 1.37/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 1.37/0.55  fof(f182,plain,(
% 1.37/0.55    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~spl4_4),
% 1.37/0.55    inference(backward_demodulation,[],[f103,f177])).
% 1.37/0.55  fof(f169,plain,(
% 1.37/0.55    spl4_1 | spl4_2),
% 1.37/0.55    inference(avatar_contradiction_clause,[],[f168])).
% 1.37/0.55  fof(f168,plain,(
% 1.37/0.55    $false | (spl4_1 | spl4_2)),
% 1.37/0.55    inference(subsumption_resolution,[],[f167,f108])).
% 1.37/0.55  fof(f108,plain,(
% 1.37/0.55    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | spl4_2),
% 1.37/0.55    inference(backward_demodulation,[],[f103,f106])).
% 1.37/0.55  fof(f106,plain,(
% 1.37/0.55    sK1 = k2_struct_0(sK0) | spl4_2),
% 1.37/0.55    inference(subsumption_resolution,[],[f105,f102])).
% 1.37/0.55  fof(f102,plain,(
% 1.37/0.55    ~v1_subset_1(sK1,k2_struct_0(sK0)) | spl4_2),
% 1.37/0.55    inference(backward_demodulation,[],[f93,f101])).
% 1.37/0.55  fof(f93,plain,(
% 1.37/0.55    ~v1_subset_1(sK1,u1_struct_0(sK0)) | spl4_2),
% 1.37/0.55    inference(avatar_component_clause,[],[f92])).
% 1.37/0.55  fof(f105,plain,(
% 1.37/0.55    sK1 = k2_struct_0(sK0) | v1_subset_1(sK1,k2_struct_0(sK0))),
% 1.37/0.55    inference(resolution,[],[f103,f81])).
% 1.37/0.55  fof(f81,plain,(
% 1.37/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f49])).
% 1.37/0.55  fof(f167,plain,(
% 1.37/0.55    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | (spl4_1 | spl4_2)),
% 1.37/0.55    inference(forward_demodulation,[],[f166,f110])).
% 1.37/0.55  fof(f110,plain,(
% 1.37/0.55    u1_struct_0(sK0) = sK1 | spl4_2),
% 1.37/0.55    inference(backward_demodulation,[],[f101,f106])).
% 1.37/0.55  fof(f166,plain,(
% 1.37/0.55    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl4_1 | spl4_2)),
% 1.37/0.55    inference(subsumption_resolution,[],[f165,f57])).
% 1.37/0.55  fof(f165,plain,(
% 1.37/0.55    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl4_1 | spl4_2)),
% 1.37/0.55    inference(subsumption_resolution,[],[f164,f155])).
% 1.37/0.55  fof(f155,plain,(
% 1.37/0.55    ~v1_tops_1(sK1,sK0) | (spl4_1 | spl4_2)),
% 1.37/0.55    inference(subsumption_resolution,[],[f154,f90])).
% 1.37/0.55  fof(f90,plain,(
% 1.37/0.55    ~v3_tex_2(sK1,sK0) | spl4_1),
% 1.37/0.55    inference(avatar_component_clause,[],[f88])).
% 1.37/0.55  fof(f154,plain,(
% 1.37/0.55    v3_tex_2(sK1,sK0) | ~v1_tops_1(sK1,sK0) | spl4_2),
% 1.37/0.55    inference(forward_demodulation,[],[f153,f62])).
% 1.37/0.55  fof(f153,plain,(
% 1.37/0.55    ~v1_tops_1(sK1,sK0) | v3_tex_2(k2_subset_1(sK1),sK0) | spl4_2),
% 1.37/0.55    inference(forward_demodulation,[],[f151,f62])).
% 1.37/0.55  fof(f151,plain,(
% 1.37/0.55    ~v1_tops_1(k2_subset_1(sK1),sK0) | v3_tex_2(k2_subset_1(sK1),sK0) | spl4_2),
% 1.37/0.55    inference(resolution,[],[f144,f63])).
% 1.37/0.55  fof(f144,plain,(
% 1.37/0.55    ( ! [X11] : (~m1_subset_1(X11,k1_zfmisc_1(sK1)) | ~v1_tops_1(X11,sK0) | v3_tex_2(X11,sK0)) ) | spl4_2),
% 1.37/0.55    inference(subsumption_resolution,[],[f143,f140])).
% 1.37/0.55  % (17509)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.37/0.55  fof(f140,plain,(
% 1.37/0.55    ( ! [X10] : (~m1_subset_1(X10,k1_zfmisc_1(sK1)) | v2_tex_2(X10,sK0)) ) | spl4_2),
% 1.37/0.55    inference(subsumption_resolution,[],[f139,f54])).
% 1.37/0.55  fof(f139,plain,(
% 1.37/0.55    ( ! [X10] : (~m1_subset_1(X10,k1_zfmisc_1(sK1)) | v2_tex_2(X10,sK0) | v2_struct_0(sK0)) ) | spl4_2),
% 1.37/0.55    inference(subsumption_resolution,[],[f138,f55])).
% 1.37/0.55  fof(f138,plain,(
% 1.37/0.55    ( ! [X10] : (~m1_subset_1(X10,k1_zfmisc_1(sK1)) | v2_tex_2(X10,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | spl4_2),
% 1.37/0.55    inference(subsumption_resolution,[],[f137,f56])).
% 1.37/0.55  fof(f137,plain,(
% 1.37/0.55    ( ! [X10] : (~m1_subset_1(X10,k1_zfmisc_1(sK1)) | v2_tex_2(X10,sK0) | ~v1_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | spl4_2),
% 1.37/0.55    inference(subsumption_resolution,[],[f124,f57])).
% 1.37/0.55  fof(f124,plain,(
% 1.37/0.55    ( ! [X10] : (~m1_subset_1(X10,k1_zfmisc_1(sK1)) | v2_tex_2(X10,sK0) | ~l1_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | spl4_2),
% 1.37/0.55    inference(superposition,[],[f77,f110])).
% 1.37/0.55  fof(f143,plain,(
% 1.37/0.55    ( ! [X11] : (~m1_subset_1(X11,k1_zfmisc_1(sK1)) | ~v2_tex_2(X11,sK0) | ~v1_tops_1(X11,sK0) | v3_tex_2(X11,sK0)) ) | spl4_2),
% 1.37/0.55    inference(subsumption_resolution,[],[f142,f54])).
% 1.37/0.55  fof(f142,plain,(
% 1.37/0.55    ( ! [X11] : (~m1_subset_1(X11,k1_zfmisc_1(sK1)) | ~v2_tex_2(X11,sK0) | ~v1_tops_1(X11,sK0) | v3_tex_2(X11,sK0) | v2_struct_0(sK0)) ) | spl4_2),
% 1.37/0.55    inference(subsumption_resolution,[],[f141,f55])).
% 1.37/0.55  fof(f141,plain,(
% 1.37/0.55    ( ! [X11] : (~m1_subset_1(X11,k1_zfmisc_1(sK1)) | ~v2_tex_2(X11,sK0) | ~v1_tops_1(X11,sK0) | v3_tex_2(X11,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | spl4_2),
% 1.37/0.55    inference(subsumption_resolution,[],[f125,f57])).
% 1.37/0.55  fof(f125,plain,(
% 1.37/0.55    ( ! [X11] : (~m1_subset_1(X11,k1_zfmisc_1(sK1)) | ~v2_tex_2(X11,sK0) | ~v1_tops_1(X11,sK0) | v3_tex_2(X11,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | spl4_2),
% 1.37/0.55    inference(superposition,[],[f78,f110])).
% 1.37/0.55  fof(f78,plain,(
% 1.37/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | v3_tex_2(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f32])).
% 1.37/0.55  fof(f32,plain,(
% 1.37/0.55    ! [X0] : (! [X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.37/0.55    inference(flattening,[],[f31])).
% 1.37/0.55  fof(f31,plain,(
% 1.37/0.55    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) | (~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.37/0.55    inference(ennf_transformation,[],[f15])).
% 1.37/0.55  fof(f15,axiom,(
% 1.37/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tex_2)).
% 1.37/0.55  fof(f164,plain,(
% 1.37/0.55    v1_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl4_2),
% 1.37/0.55    inference(subsumption_resolution,[],[f162,f106])).
% 1.37/0.55  fof(f162,plain,(
% 1.37/0.55    sK1 != k2_struct_0(sK0) | v1_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl4_2),
% 1.37/0.55    inference(superposition,[],[f70,f160])).
% 1.37/0.55  % (17513)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.37/0.55  fof(f160,plain,(
% 1.37/0.55    sK1 = k2_pre_topc(sK0,sK1) | spl4_2),
% 1.37/0.55    inference(forward_demodulation,[],[f159,f62])).
% 1.37/0.55  fof(f159,plain,(
% 1.37/0.55    k2_subset_1(sK1) = k2_pre_topc(sK0,k2_subset_1(sK1)) | spl4_2),
% 1.37/0.55    inference(subsumption_resolution,[],[f158,f111])).
% 1.37/0.55  fof(f111,plain,(
% 1.37/0.55    v4_pre_topc(sK1,sK0) | spl4_2),
% 1.37/0.55    inference(backward_demodulation,[],[f98,f106])).
% 1.37/0.55  fof(f98,plain,(
% 1.37/0.55    v4_pre_topc(k2_struct_0(sK0),sK0)),
% 1.37/0.55    inference(subsumption_resolution,[],[f97,f57])).
% 1.37/0.55  fof(f97,plain,(
% 1.37/0.55    ~l1_pre_topc(sK0) | v4_pre_topc(k2_struct_0(sK0),sK0)),
% 1.37/0.55    inference(resolution,[],[f55,f79])).
% 1.37/0.55  fof(f79,plain,(
% 1.37/0.55    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v4_pre_topc(k2_struct_0(X0),X0)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f34])).
% 1.37/0.55  fof(f34,plain,(
% 1.37/0.55    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.37/0.55    inference(flattening,[],[f33])).
% 1.37/0.55  fof(f33,plain,(
% 1.37/0.55    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.37/0.55    inference(ennf_transformation,[],[f8])).
% 1.37/0.55  fof(f8,axiom,(
% 1.37/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).
% 1.37/0.55  fof(f158,plain,(
% 1.37/0.55    ~v4_pre_topc(sK1,sK0) | k2_subset_1(sK1) = k2_pre_topc(sK0,k2_subset_1(sK1)) | spl4_2),
% 1.37/0.55    inference(forward_demodulation,[],[f156,f62])).
% 1.37/0.55  fof(f156,plain,(
% 1.37/0.55    ~v4_pre_topc(k2_subset_1(sK1),sK0) | k2_subset_1(sK1) = k2_pre_topc(sK0,k2_subset_1(sK1)) | spl4_2),
% 1.37/0.55    inference(resolution,[],[f126,f63])).
% 1.37/0.55  fof(f126,plain,(
% 1.37/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | ~v4_pre_topc(X0,sK0) | k2_pre_topc(sK0,X0) = X0) ) | spl4_2),
% 1.37/0.55    inference(subsumption_resolution,[],[f115,f57])).
% 1.37/0.55  fof(f115,plain,(
% 1.37/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | ~v4_pre_topc(X0,sK0) | k2_pre_topc(sK0,X0) = X0 | ~l1_pre_topc(sK0)) ) | spl4_2),
% 1.37/0.55    inference(superposition,[],[f67,f110])).
% 1.37/0.55  fof(f67,plain,(
% 1.37/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f25])).
% 1.37/0.55  fof(f25,plain,(
% 1.37/0.55    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.37/0.55    inference(flattening,[],[f24])).
% 1.37/0.55  fof(f24,plain,(
% 1.37/0.55    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.37/0.55    inference(ennf_transformation,[],[f9])).
% 1.37/0.55  fof(f9,axiom,(
% 1.37/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.37/0.55  fof(f70,plain,(
% 1.37/0.55    ( ! [X0,X1] : (k2_struct_0(X0) != k2_pre_topc(X0,X1) | v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f43])).
% 1.37/0.55  fof(f43,plain,(
% 1.37/0.55    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.37/0.55    inference(nnf_transformation,[],[f26])).
% 1.37/0.55  fof(f26,plain,(
% 1.37/0.55    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.37/0.55    inference(ennf_transformation,[],[f10])).
% 1.37/0.55  fof(f10,axiom,(
% 1.37/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).
% 1.37/0.55  fof(f96,plain,(
% 1.37/0.55    spl4_1 | ~spl4_2),
% 1.37/0.55    inference(avatar_split_clause,[],[f59,f92,f88])).
% 1.37/0.55  fof(f59,plain,(
% 1.37/0.55    ~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)),
% 1.37/0.55    inference(cnf_transformation,[],[f42])).
% 1.37/0.55  fof(f95,plain,(
% 1.37/0.55    ~spl4_1 | spl4_2),
% 1.37/0.55    inference(avatar_split_clause,[],[f60,f92,f88])).
% 1.37/0.55  % (17515)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.37/0.55  fof(f60,plain,(
% 1.37/0.55    v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)),
% 1.37/0.55    inference(cnf_transformation,[],[f42])).
% 1.37/0.55  % SZS output end Proof for theBenchmark
% 1.37/0.55  % (17514)------------------------------
% 1.37/0.55  % (17514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (17514)Termination reason: Refutation
% 1.37/0.55  
% 1.37/0.55  % (17514)Memory used [KB]: 10874
% 1.37/0.55  % (17514)Time elapsed: 0.110 s
% 1.37/0.55  % (17514)------------------------------
% 1.37/0.55  % (17514)------------------------------
% 1.37/0.56  % (17516)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.37/0.56  % (17505)Success in time 0.178 s
%------------------------------------------------------------------------------
