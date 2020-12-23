%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:41 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 590 expanded)
%              Number of leaves         :   24 ( 187 expanded)
%              Depth                    :   18
%              Number of atoms          :  534 (2671 expanded)
%              Number of equality atoms :   27 ( 404 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f290,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f103,f121,f160,f172,f178,f200,f223,f232,f237,f271,f289])).

fof(f289,plain,
    ( ~ spl3_4
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f288])).

fof(f288,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f155,f248])).

fof(f248,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0))
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f142,f236])).

fof(f236,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f234])).

fof(f234,plain,
    ( spl3_12
  <=> u1_pre_topc(sK0) = u1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f142,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1))
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f141,f43])).

fof(f43,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ~ v3_tdlat_3(sK1)
    & v3_tdlat_3(sK0)
    & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f32,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v3_tdlat_3(X1)
            & v3_tdlat_3(X0)
            & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v3_tdlat_3(X1)
          & v3_tdlat_3(sK0)
          & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X1] :
        ( ~ v3_tdlat_3(X1)
        & v3_tdlat_3(sK0)
        & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        & l1_pre_topc(X1) )
   => ( ~ v3_tdlat_3(sK1)
      & v3_tdlat_3(sK0)
      & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tdlat_3(X1)
          & v3_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

% (4068)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tdlat_3(X1)
          & v3_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v3_tdlat_3(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v3_tdlat_3(X1) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v3_tdlat_3(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v3_tdlat_3(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tex_2)).

fof(f141,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f131,f46])).

fof(f46,plain,(
    ~ v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f131,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1))
    | v3_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ spl3_4 ),
    inference(superposition,[],[f53,f102])).

fof(f102,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl3_4
  <=> u1_struct_0(sK0) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f53,plain,(
    ! [X0] :
      ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK2(X0)),u1_pre_topc(X0))
      | v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK2(X0)),u1_pre_topc(X0))
            & r2_hidden(sK2(X0),u1_pre_topc(X0))
            & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
              | ~ r2_hidden(X2,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r2_hidden(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK2(X0)),u1_pre_topc(X0))
        & r2_hidden(sK2(X0),u1_pre_topc(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
              & r2_hidden(X1,u1_pre_topc(X0))
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
              | ~ r2_hidden(X2,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
              & r2_hidden(X1,u1_pre_topc(X0))
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
              | ~ r2_hidden(X1,u1_pre_topc(X0))
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
            | ~ r2_hidden(X1,u1_pre_topc(X0))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
            | ~ r2_hidden(X1,u1_pre_topc(X0))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r2_hidden(X1,u1_pre_topc(X0))
             => r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tdlat_3)).

fof(f155,plain,
    ( r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl3_5
  <=> r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f271,plain,
    ( spl3_6
    | ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f270])).

fof(f270,plain,
    ( $false
    | spl3_6
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f269,f43])).

fof(f269,plain,
    ( ~ l1_pre_topc(sK1)
    | spl3_6
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f268,f46])).

fof(f268,plain,
    ( v3_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1)
    | spl3_6
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f260,f159])).

fof(f159,plain,
    ( ~ r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl3_6
  <=> r2_hidden(sK2(sK1),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f260,plain,
    ( r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | v3_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ spl3_12 ),
    inference(superposition,[],[f52,f236])).

fof(f52,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),u1_pre_topc(X0))
      | v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f237,plain,
    ( ~ spl3_10
    | spl3_12
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f224,f175,f234,f193])).

fof(f193,plain,
    ( spl3_10
  <=> r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f175,plain,
    ( spl3_9
  <=> r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f224,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(sK1)
    | ~ r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1))
    | ~ spl3_9 ),
    inference(resolution,[],[f177,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

% (4081)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
fof(f40,plain,(
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

fof(f177,plain,
    ( r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f175])).

fof(f232,plain,
    ( ~ spl3_4
    | spl3_11 ),
    inference(avatar_contradiction_clause,[],[f231])).

fof(f231,plain,
    ( $false
    | ~ spl3_4
    | spl3_11 ),
    inference(subsumption_resolution,[],[f230,f42])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f230,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_4
    | spl3_11 ),
    inference(resolution,[],[f229,f48])).

fof(f48,plain,(
    ! [X0] :
      ( v1_tops_2(u1_pre_topc(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v1_tops_2(u1_pre_topc(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => v1_tops_2(u1_pre_topc(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_compts_1)).

fof(f229,plain,
    ( ~ v1_tops_2(u1_pre_topc(sK0),sK0)
    | ~ spl3_4
    | spl3_11 ),
    inference(subsumption_resolution,[],[f228,f42])).

fof(f228,plain,
    ( ~ v1_tops_2(u1_pre_topc(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_4
    | spl3_11 ),
    inference(subsumption_resolution,[],[f227,f115])).

fof(f115,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f114,f43])).

fof(f114,plain,
    ( ~ l1_pre_topc(sK1)
    | m1_pre_topc(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,
    ( ~ l1_pre_topc(sK1)
    | m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f110,f47])).

fof(f47,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f110,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK1)
      | ~ l1_pre_topc(X1)
      | m1_pre_topc(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f105,f42])).

fof(f105,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK1)
      | ~ l1_pre_topc(X1)
      | m1_pre_topc(X1,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f73,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f73,plain,(
    ! [X1] :
      ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_pre_topc(X1,sK1)
      | ~ l1_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f70,f43])).

fof(f70,plain,(
    ! [X1] :
      ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_pre_topc(X1,sK1)
      | ~ l1_pre_topc(sK1)
      | ~ l1_pre_topc(X1) ) ),
    inference(superposition,[],[f54,f44])).

fof(f44,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f227,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ v1_tops_2(u1_pre_topc(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_4
    | spl3_11 ),
    inference(duplicate_literal_removal,[],[f225])).

fof(f225,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ v1_tops_2(u1_pre_topc(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_4
    | spl3_11 ),
    inference(resolution,[],[f209,f49])).

fof(f49,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f209,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ m1_pre_topc(sK1,X0)
        | ~ v1_tops_2(u1_pre_topc(sK0),X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_4
    | spl3_11 ),
    inference(subsumption_resolution,[],[f208,f42])).

fof(f208,plain,
    ( ! [X0] :
        ( ~ v1_tops_2(u1_pre_topc(sK0),X0)
        | ~ m1_pre_topc(sK1,X0)
        | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_4
    | spl3_11 ),
    inference(subsumption_resolution,[],[f206,f199])).

fof(f199,plain,
    ( ~ v1_tops_2(u1_pre_topc(sK0),sK1)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl3_11
  <=> v1_tops_2(u1_pre_topc(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f206,plain,
    ( ! [X0] :
        ( v1_tops_2(u1_pre_topc(sK0),sK1)
        | ~ v1_tops_2(u1_pre_topc(sK0),X0)
        | ~ m1_pre_topc(sK1,X0)
        | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_4 ),
    inference(resolution,[],[f137,f49])).

fof(f137,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v1_tops_2(X6,sK1)
        | ~ v1_tops_2(X6,X7)
        | ~ m1_pre_topc(sK1,X7)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))
        | ~ l1_pre_topc(X7) )
    | ~ spl3_4 ),
    inference(superposition,[],[f66,f102])).

fof(f66,plain,(
    ! [X2,X0,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | v1_tops_2(X3,X2)
      | ~ v1_tops_2(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_tops_2(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v1_tops_2(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              | ~ v1_tops_2(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v1_tops_2(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              | ~ v1_tops_2(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v1_tops_2(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                   => ( X1 = X3
                     => v1_tops_2(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tops_2)).

fof(f223,plain,
    ( ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f222])).

fof(f222,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f221,f90])).

fof(f90,plain,(
    m1_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f89,f42])).

fof(f89,plain,
    ( m1_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,
    ( m1_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f78,f47])).

fof(f78,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_pre_topc(X0,sK1)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f76,f42])).

fof(f76,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,sK1)
      | ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f72,f54])).

fof(f72,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | m1_pre_topc(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f69,f43])).

fof(f69,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | m1_pre_topc(X0,sK1)
      | ~ l1_pre_topc(sK1) ) ),
    inference(superposition,[],[f61,f44])).

fof(f221,plain,
    ( ~ m1_pre_topc(sK0,sK1)
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f220,f205])).

fof(f205,plain,
    ( v1_tops_2(u1_pre_topc(sK1),sK1)
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f202,f68])).

fof(f68,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f202,plain,
    ( ~ r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK1))
    | v1_tops_2(u1_pre_topc(sK1),sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f146,f138])).

fof(f138,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f128,f43])).

fof(f128,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK1)
    | ~ spl3_4 ),
    inference(superposition,[],[f49,f102])).

fof(f146,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X4,u1_pre_topc(sK1))
        | v1_tops_2(X4,sK1) )
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f135,f43])).

fof(f135,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X4,u1_pre_topc(sK1))
        | v1_tops_2(X4,sK1)
        | ~ l1_pre_topc(sK1) )
    | ~ spl3_4 ),
    inference(superposition,[],[f59,f102])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r1_tarski(X1,u1_pre_topc(X0))
      | v1_tops_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ~ r1_tarski(X1,u1_pre_topc(X0)) )
            & ( r1_tarski(X1,u1_pre_topc(X0))
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tops_2)).

fof(f220,plain,
    ( ~ v1_tops_2(u1_pre_topc(sK1),sK1)
    | ~ m1_pre_topc(sK0,sK1)
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f219,f43])).

fof(f219,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_tops_2(u1_pre_topc(sK1),sK1)
    | ~ m1_pre_topc(sK0,sK1)
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f213,f138])).

fof(f213,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK1)
    | ~ v1_tops_2(u1_pre_topc(sK1),sK1)
    | ~ m1_pre_topc(sK0,sK1)
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(superposition,[],[f167,f102])).

fof(f167,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0)
        | ~ v1_tops_2(u1_pre_topc(sK1),X0)
        | ~ m1_pre_topc(sK0,X0) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl3_7
  <=> ! [X0] :
        ( ~ v1_tops_2(u1_pre_topc(sK1),X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ m1_pre_topc(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f200,plain,
    ( spl3_10
    | ~ spl3_11
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f191,f100,f197,f193])).

fof(f191,plain,
    ( ~ v1_tops_2(u1_pre_topc(sK0),sK1)
    | r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1))
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f189,f42])).

fof(f189,plain,
    ( ~ v1_tops_2(u1_pre_topc(sK0),sK1)
    | r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(resolution,[],[f145,f49])).

fof(f145,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ v1_tops_2(X3,sK1)
        | r1_tarski(X3,u1_pre_topc(sK1)) )
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f134,f43])).

fof(f134,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ v1_tops_2(X3,sK1)
        | r1_tarski(X3,u1_pre_topc(sK1))
        | ~ l1_pre_topc(sK1) )
    | ~ spl3_4 ),
    inference(superposition,[],[f58,f102])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_tops_2(X1,X0)
      | r1_tarski(X1,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f178,plain,
    ( spl3_9
    | ~ spl3_8
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f173,f100,f169,f175])).

fof(f169,plain,
    ( spl3_8
  <=> v1_tops_2(u1_pre_topc(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f173,plain,
    ( ~ v1_tops_2(u1_pre_topc(sK1),sK0)
    | r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0))
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f162,f42])).

fof(f162,plain,
    ( ~ v1_tops_2(u1_pre_topc(sK1),sK0)
    | r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(resolution,[],[f138,f58])).

fof(f172,plain,
    ( spl3_7
    | spl3_8
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f161,f100,f169,f166])).

fof(f161,plain,
    ( ! [X0] :
        ( v1_tops_2(u1_pre_topc(sK1),sK0)
        | ~ v1_tops_2(u1_pre_topc(sK1),X0)
        | ~ m1_pre_topc(sK0,X0)
        | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0) )
    | ~ spl3_4 ),
    inference(resolution,[],[f138,f66])).

fof(f160,plain,
    ( spl3_5
    | ~ spl3_6
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f151,f100,f157,f153])).

fof(f151,plain,
    ( ~ r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0))
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f150,f42])).

fof(f150,plain,
    ( ~ r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f148,f45])).

fof(f45,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f148,plain,
    ( ~ r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0))
    | ~ v3_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(resolution,[],[f140,f50])).

% (4071)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
fof(f50,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,u1_pre_topc(X0))
      | r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f140,plain,
    ( m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f139,f43])).

fof(f139,plain,
    ( m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK1)
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f130,f46])).

fof(f130,plain,
    ( m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ spl3_4 ),
    inference(superposition,[],[f51,f102])).

fof(f51,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f121,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | spl3_3 ),
    inference(subsumption_resolution,[],[f119,f42])).

fof(f119,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_3 ),
    inference(subsumption_resolution,[],[f117,f98])).

fof(f98,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl3_3
  <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f117,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f115,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f103,plain,
    ( ~ spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f94,f100,f96])).

fof(f94,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f93,f64])).

fof(f93,plain,(
    r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f91,f43])).

fof(f91,plain,
    ( r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f90,f57])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:49:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.53  % (4059)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (4064)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.24/0.54  % (4059)Refutation found. Thanks to Tanya!
% 1.24/0.54  % SZS status Theorem for theBenchmark
% 1.24/0.54  % (4064)Refutation not found, incomplete strategy% (4064)------------------------------
% 1.24/0.54  % (4064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.54  % (4064)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.54  
% 1.24/0.54  % (4064)Memory used [KB]: 10618
% 1.24/0.54  % (4064)Time elapsed: 0.114 s
% 1.24/0.54  % (4064)------------------------------
% 1.24/0.54  % (4064)------------------------------
% 1.24/0.54  % SZS output start Proof for theBenchmark
% 1.24/0.54  fof(f290,plain,(
% 1.24/0.54    $false),
% 1.24/0.54    inference(avatar_sat_refutation,[],[f103,f121,f160,f172,f178,f200,f223,f232,f237,f271,f289])).
% 1.24/0.54  fof(f289,plain,(
% 1.24/0.54    ~spl3_4 | ~spl3_5 | ~spl3_12),
% 1.24/0.54    inference(avatar_contradiction_clause,[],[f288])).
% 1.24/0.54  fof(f288,plain,(
% 1.24/0.54    $false | (~spl3_4 | ~spl3_5 | ~spl3_12)),
% 1.24/0.54    inference(subsumption_resolution,[],[f155,f248])).
% 1.24/0.54  fof(f248,plain,(
% 1.24/0.54    ~r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0)) | (~spl3_4 | ~spl3_12)),
% 1.24/0.54    inference(backward_demodulation,[],[f142,f236])).
% 1.24/0.54  fof(f236,plain,(
% 1.24/0.54    u1_pre_topc(sK0) = u1_pre_topc(sK1) | ~spl3_12),
% 1.24/0.54    inference(avatar_component_clause,[],[f234])).
% 1.24/0.54  fof(f234,plain,(
% 1.24/0.54    spl3_12 <=> u1_pre_topc(sK0) = u1_pre_topc(sK1)),
% 1.24/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.24/0.54  fof(f142,plain,(
% 1.24/0.54    ~r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1)) | ~spl3_4),
% 1.24/0.54    inference(subsumption_resolution,[],[f141,f43])).
% 1.24/0.54  fof(f43,plain,(
% 1.24/0.54    l1_pre_topc(sK1)),
% 1.24/0.54    inference(cnf_transformation,[],[f33])).
% 1.24/0.54  fof(f33,plain,(
% 1.24/0.54    (~v3_tdlat_3(sK1) & v3_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & l1_pre_topc(sK1)) & l1_pre_topc(sK0)),
% 1.24/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f32,f31])).
% 1.24/0.54  fof(f31,plain,(
% 1.24/0.54    ? [X0] : (? [X1] : (~v3_tdlat_3(X1) & v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (~v3_tdlat_3(X1) & v3_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) & l1_pre_topc(X1)) & l1_pre_topc(sK0))),
% 1.24/0.54    introduced(choice_axiom,[])).
% 1.24/0.54  fof(f32,plain,(
% 1.24/0.54    ? [X1] : (~v3_tdlat_3(X1) & v3_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) & l1_pre_topc(X1)) => (~v3_tdlat_3(sK1) & v3_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & l1_pre_topc(sK1))),
% 1.24/0.54    introduced(choice_axiom,[])).
% 1.24/0.54  fof(f16,plain,(
% 1.24/0.54    ? [X0] : (? [X1] : (~v3_tdlat_3(X1) & v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 1.24/0.54    inference(flattening,[],[f15])).
% 1.24/0.54  % (4068)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.24/0.54  fof(f15,plain,(
% 1.24/0.54    ? [X0] : (? [X1] : ((~v3_tdlat_3(X1) & (v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 1.24/0.54    inference(ennf_transformation,[],[f14])).
% 1.24/0.54  fof(f14,negated_conjecture,(
% 1.24/0.54    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v3_tdlat_3(X1))))),
% 1.24/0.54    inference(negated_conjecture,[],[f13])).
% 1.24/0.54  fof(f13,conjecture,(
% 1.24/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v3_tdlat_3(X1))))),
% 1.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tex_2)).
% 1.24/0.54  fof(f141,plain,(
% 1.24/0.54    ~r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1)) | ~l1_pre_topc(sK1) | ~spl3_4),
% 1.24/0.54    inference(subsumption_resolution,[],[f131,f46])).
% 1.24/0.54  fof(f46,plain,(
% 1.24/0.54    ~v3_tdlat_3(sK1)),
% 1.24/0.54    inference(cnf_transformation,[],[f33])).
% 1.24/0.54  fof(f131,plain,(
% 1.24/0.54    ~r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1)) | v3_tdlat_3(sK1) | ~l1_pre_topc(sK1) | ~spl3_4),
% 1.24/0.54    inference(superposition,[],[f53,f102])).
% 1.24/0.54  fof(f102,plain,(
% 1.24/0.54    u1_struct_0(sK0) = u1_struct_0(sK1) | ~spl3_4),
% 1.24/0.54    inference(avatar_component_clause,[],[f100])).
% 1.24/0.54  fof(f100,plain,(
% 1.24/0.54    spl3_4 <=> u1_struct_0(sK0) = u1_struct_0(sK1)),
% 1.24/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.24/0.54  fof(f53,plain,(
% 1.24/0.54    ( ! [X0] : (~r2_hidden(k6_subset_1(u1_struct_0(X0),sK2(X0)),u1_pre_topc(X0)) | v3_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f37])).
% 1.24/0.54  fof(f37,plain,(
% 1.24/0.54    ! [X0] : (((v3_tdlat_3(X0) | (~r2_hidden(k6_subset_1(u1_struct_0(X0),sK2(X0)),u1_pre_topc(X0)) & r2_hidden(sK2(X0),u1_pre_topc(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0))),
% 1.24/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).
% 1.24/0.54  fof(f36,plain,(
% 1.24/0.54    ! [X0] : (? [X1] : (~r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~r2_hidden(k6_subset_1(u1_struct_0(X0),sK2(X0)),u1_pre_topc(X0)) & r2_hidden(sK2(X0),u1_pre_topc(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.24/0.54    introduced(choice_axiom,[])).
% 1.24/0.54  fof(f35,plain,(
% 1.24/0.54    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0))),
% 1.24/0.54    inference(rectify,[],[f34])).
% 1.24/0.54  fof(f34,plain,(
% 1.24/0.54    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0))),
% 1.24/0.54    inference(nnf_transformation,[],[f21])).
% 1.24/0.54  fof(f21,plain,(
% 1.24/0.54    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.24/0.54    inference(flattening,[],[f20])).
% 1.24/0.54  fof(f20,plain,(
% 1.24/0.54    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.24/0.54    inference(ennf_transformation,[],[f12])).
% 1.24/0.54  fof(f12,axiom,(
% 1.24/0.54    ! [X0] : (l1_pre_topc(X0) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) => r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))))))),
% 1.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tdlat_3)).
% 1.24/0.54  fof(f155,plain,(
% 1.24/0.54    r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0)) | ~spl3_5),
% 1.24/0.54    inference(avatar_component_clause,[],[f153])).
% 1.24/0.54  fof(f153,plain,(
% 1.24/0.54    spl3_5 <=> r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0))),
% 1.24/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.24/0.54  fof(f271,plain,(
% 1.24/0.54    spl3_6 | ~spl3_12),
% 1.24/0.54    inference(avatar_contradiction_clause,[],[f270])).
% 1.24/0.54  fof(f270,plain,(
% 1.24/0.54    $false | (spl3_6 | ~spl3_12)),
% 1.24/0.54    inference(subsumption_resolution,[],[f269,f43])).
% 1.24/0.54  fof(f269,plain,(
% 1.24/0.54    ~l1_pre_topc(sK1) | (spl3_6 | ~spl3_12)),
% 1.24/0.54    inference(subsumption_resolution,[],[f268,f46])).
% 1.24/0.54  fof(f268,plain,(
% 1.24/0.54    v3_tdlat_3(sK1) | ~l1_pre_topc(sK1) | (spl3_6 | ~spl3_12)),
% 1.24/0.54    inference(subsumption_resolution,[],[f260,f159])).
% 1.24/0.54  fof(f159,plain,(
% 1.24/0.54    ~r2_hidden(sK2(sK1),u1_pre_topc(sK0)) | spl3_6),
% 1.24/0.54    inference(avatar_component_clause,[],[f157])).
% 1.24/0.54  fof(f157,plain,(
% 1.24/0.54    spl3_6 <=> r2_hidden(sK2(sK1),u1_pre_topc(sK0))),
% 1.24/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.24/0.54  fof(f260,plain,(
% 1.24/0.54    r2_hidden(sK2(sK1),u1_pre_topc(sK0)) | v3_tdlat_3(sK1) | ~l1_pre_topc(sK1) | ~spl3_12),
% 1.24/0.54    inference(superposition,[],[f52,f236])).
% 1.24/0.54  fof(f52,plain,(
% 1.24/0.54    ( ! [X0] : (r2_hidden(sK2(X0),u1_pre_topc(X0)) | v3_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f37])).
% 1.24/0.54  fof(f237,plain,(
% 1.24/0.54    ~spl3_10 | spl3_12 | ~spl3_9),
% 1.24/0.54    inference(avatar_split_clause,[],[f224,f175,f234,f193])).
% 1.24/0.54  fof(f193,plain,(
% 1.24/0.54    spl3_10 <=> r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1))),
% 1.24/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.24/0.54  fof(f175,plain,(
% 1.24/0.54    spl3_9 <=> r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0))),
% 1.24/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.24/0.54  fof(f224,plain,(
% 1.24/0.54    u1_pre_topc(sK0) = u1_pre_topc(sK1) | ~r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1)) | ~spl3_9),
% 1.24/0.54    inference(resolution,[],[f177,f64])).
% 1.24/0.54  fof(f64,plain,(
% 1.24/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f41])).
% 1.24/0.54  fof(f41,plain,(
% 1.24/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.24/0.54    inference(flattening,[],[f40])).
% 1.24/0.54  % (4081)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.24/0.54  fof(f40,plain,(
% 1.24/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.24/0.54    inference(nnf_transformation,[],[f1])).
% 1.24/0.54  fof(f1,axiom,(
% 1.24/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.24/0.54  fof(f177,plain,(
% 1.24/0.54    r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0)) | ~spl3_9),
% 1.24/0.54    inference(avatar_component_clause,[],[f175])).
% 1.24/0.54  fof(f232,plain,(
% 1.24/0.54    ~spl3_4 | spl3_11),
% 1.24/0.54    inference(avatar_contradiction_clause,[],[f231])).
% 1.24/0.54  fof(f231,plain,(
% 1.24/0.54    $false | (~spl3_4 | spl3_11)),
% 1.24/0.54    inference(subsumption_resolution,[],[f230,f42])).
% 1.24/0.54  fof(f42,plain,(
% 1.24/0.54    l1_pre_topc(sK0)),
% 1.24/0.54    inference(cnf_transformation,[],[f33])).
% 1.24/0.54  fof(f230,plain,(
% 1.24/0.54    ~l1_pre_topc(sK0) | (~spl3_4 | spl3_11)),
% 1.24/0.54    inference(resolution,[],[f229,f48])).
% 1.24/0.54  fof(f48,plain,(
% 1.24/0.54    ( ! [X0] : (v1_tops_2(u1_pre_topc(X0),X0) | ~l1_pre_topc(X0)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f18])).
% 1.24/0.54  fof(f18,plain,(
% 1.24/0.54    ! [X0] : (v1_tops_2(u1_pre_topc(X0),X0) | ~l1_pre_topc(X0))),
% 1.24/0.54    inference(ennf_transformation,[],[f9])).
% 1.24/0.54  fof(f9,axiom,(
% 1.24/0.54    ! [X0] : (l1_pre_topc(X0) => v1_tops_2(u1_pre_topc(X0),X0))),
% 1.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_compts_1)).
% 1.24/0.54  fof(f229,plain,(
% 1.24/0.54    ~v1_tops_2(u1_pre_topc(sK0),sK0) | (~spl3_4 | spl3_11)),
% 1.24/0.54    inference(subsumption_resolution,[],[f228,f42])).
% 1.24/0.54  fof(f228,plain,(
% 1.24/0.54    ~v1_tops_2(u1_pre_topc(sK0),sK0) | ~l1_pre_topc(sK0) | (~spl3_4 | spl3_11)),
% 1.24/0.54    inference(subsumption_resolution,[],[f227,f115])).
% 1.24/0.54  fof(f115,plain,(
% 1.24/0.54    m1_pre_topc(sK1,sK0)),
% 1.24/0.54    inference(subsumption_resolution,[],[f114,f43])).
% 1.24/0.54  fof(f114,plain,(
% 1.24/0.54    ~l1_pre_topc(sK1) | m1_pre_topc(sK1,sK0)),
% 1.24/0.54    inference(duplicate_literal_removal,[],[f112])).
% 1.24/0.54  fof(f112,plain,(
% 1.24/0.54    ~l1_pre_topc(sK1) | m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK1)),
% 1.24/0.54    inference(resolution,[],[f110,f47])).
% 1.24/0.54  fof(f47,plain,(
% 1.24/0.54    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f17])).
% 1.24/0.54  fof(f17,plain,(
% 1.24/0.54    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 1.24/0.54    inference(ennf_transformation,[],[f10])).
% 1.24/0.54  fof(f10,axiom,(
% 1.24/0.54    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 1.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 1.24/0.54  fof(f110,plain,(
% 1.24/0.54    ( ! [X1] : (~m1_pre_topc(X1,sK1) | ~l1_pre_topc(X1) | m1_pre_topc(X1,sK0)) )),
% 1.24/0.54    inference(subsumption_resolution,[],[f105,f42])).
% 1.24/0.54  fof(f105,plain,(
% 1.24/0.54    ( ! [X1] : (~m1_pre_topc(X1,sK1) | ~l1_pre_topc(X1) | m1_pre_topc(X1,sK0) | ~l1_pre_topc(sK0)) )),
% 1.24/0.54    inference(resolution,[],[f73,f61])).
% 1.24/0.54  fof(f61,plain,(
% 1.24/0.54    ( ! [X0,X1] : (~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f28])).
% 1.24/0.54  fof(f28,plain,(
% 1.24/0.54    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.24/0.54    inference(ennf_transformation,[],[f5])).
% 1.24/0.54  fof(f5,axiom,(
% 1.24/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 1.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).
% 1.24/0.54  fof(f73,plain,(
% 1.24/0.54    ( ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_pre_topc(X1,sK1) | ~l1_pre_topc(X1)) )),
% 1.24/0.54    inference(subsumption_resolution,[],[f70,f43])).
% 1.24/0.54  fof(f70,plain,(
% 1.24/0.54    ( ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_pre_topc(X1,sK1) | ~l1_pre_topc(sK1) | ~l1_pre_topc(X1)) )),
% 1.24/0.54    inference(superposition,[],[f54,f44])).
% 1.24/0.54  fof(f44,plain,(
% 1.24/0.54    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 1.24/0.54    inference(cnf_transformation,[],[f33])).
% 1.24/0.54  fof(f54,plain,(
% 1.24/0.54    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f38])).
% 1.24/0.54  fof(f38,plain,(
% 1.24/0.54    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.24/0.54    inference(nnf_transformation,[],[f22])).
% 1.24/0.54  fof(f22,plain,(
% 1.24/0.54    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.24/0.54    inference(ennf_transformation,[],[f6])).
% 1.24/0.54  fof(f6,axiom,(
% 1.24/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 1.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).
% 1.24/0.54  fof(f227,plain,(
% 1.24/0.54    ~m1_pre_topc(sK1,sK0) | ~v1_tops_2(u1_pre_topc(sK0),sK0) | ~l1_pre_topc(sK0) | (~spl3_4 | spl3_11)),
% 1.24/0.54    inference(duplicate_literal_removal,[],[f225])).
% 1.24/0.54  fof(f225,plain,(
% 1.24/0.54    ~m1_pre_topc(sK1,sK0) | ~v1_tops_2(u1_pre_topc(sK0),sK0) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK0) | (~spl3_4 | spl3_11)),
% 1.24/0.54    inference(resolution,[],[f209,f49])).
% 1.24/0.54  fof(f49,plain,(
% 1.24/0.54    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f19])).
% 1.24/0.54  fof(f19,plain,(
% 1.24/0.54    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.24/0.54    inference(ennf_transformation,[],[f4])).
% 1.24/0.54  fof(f4,axiom,(
% 1.24/0.54    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 1.24/0.54  fof(f209,plain,(
% 1.24/0.54    ( ! [X0] : (~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(sK1,X0) | ~v1_tops_2(u1_pre_topc(sK0),X0) | ~l1_pre_topc(X0)) ) | (~spl3_4 | spl3_11)),
% 1.24/0.54    inference(subsumption_resolution,[],[f208,f42])).
% 1.24/0.54  fof(f208,plain,(
% 1.24/0.54    ( ! [X0] : (~v1_tops_2(u1_pre_topc(sK0),X0) | ~m1_pre_topc(sK1,X0) | ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~l1_pre_topc(sK0)) ) | (~spl3_4 | spl3_11)),
% 1.24/0.54    inference(subsumption_resolution,[],[f206,f199])).
% 1.24/0.54  fof(f199,plain,(
% 1.24/0.54    ~v1_tops_2(u1_pre_topc(sK0),sK1) | spl3_11),
% 1.24/0.54    inference(avatar_component_clause,[],[f197])).
% 1.24/0.54  fof(f197,plain,(
% 1.24/0.54    spl3_11 <=> v1_tops_2(u1_pre_topc(sK0),sK1)),
% 1.24/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.24/0.54  fof(f206,plain,(
% 1.24/0.54    ( ! [X0] : (v1_tops_2(u1_pre_topc(sK0),sK1) | ~v1_tops_2(u1_pre_topc(sK0),X0) | ~m1_pre_topc(sK1,X0) | ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~l1_pre_topc(sK0)) ) | ~spl3_4),
% 1.24/0.54    inference(resolution,[],[f137,f49])).
% 1.24/0.54  fof(f137,plain,(
% 1.24/0.54    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(X6,sK1) | ~v1_tops_2(X6,X7) | ~m1_pre_topc(sK1,X7) | ~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7)))) | ~l1_pre_topc(X7)) ) | ~spl3_4),
% 1.24/0.54    inference(superposition,[],[f66,f102])).
% 1.24/0.54  fof(f66,plain,(
% 1.24/0.54    ( ! [X2,X0,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | v1_tops_2(X3,X2) | ~v1_tops_2(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.24/0.54    inference(equality_resolution,[],[f60])).
% 1.24/0.54  fof(f60,plain,(
% 1.24/0.54    ( ! [X2,X0,X3,X1] : (v1_tops_2(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | ~v1_tops_2(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f27])).
% 1.24/0.54  fof(f27,plain,(
% 1.24/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v1_tops_2(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) | ~v1_tops_2(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.24/0.54    inference(flattening,[],[f26])).
% 1.24/0.54  fof(f26,plain,(
% 1.24/0.54    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v1_tops_2(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) | ~v1_tops_2(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.24/0.54    inference(ennf_transformation,[],[f7])).
% 1.24/0.54  fof(f7,axiom,(
% 1.24/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_pre_topc(X2,X0) => (v1_tops_2(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) => (X1 = X3 => v1_tops_2(X3,X2)))))))),
% 1.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tops_2)).
% 1.24/0.54  fof(f223,plain,(
% 1.24/0.54    ~spl3_4 | ~spl3_7),
% 1.24/0.54    inference(avatar_contradiction_clause,[],[f222])).
% 1.24/0.54  fof(f222,plain,(
% 1.24/0.54    $false | (~spl3_4 | ~spl3_7)),
% 1.24/0.54    inference(subsumption_resolution,[],[f221,f90])).
% 1.24/0.54  fof(f90,plain,(
% 1.24/0.54    m1_pre_topc(sK0,sK1)),
% 1.24/0.54    inference(subsumption_resolution,[],[f89,f42])).
% 1.24/0.54  fof(f89,plain,(
% 1.24/0.54    m1_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.24/0.54    inference(duplicate_literal_removal,[],[f88])).
% 1.24/0.54  fof(f88,plain,(
% 1.24/0.54    m1_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK0)),
% 1.24/0.54    inference(resolution,[],[f78,f47])).
% 1.24/0.54  fof(f78,plain,(
% 1.24/0.54    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_pre_topc(X0,sK1) | ~l1_pre_topc(X0)) )),
% 1.24/0.54    inference(subsumption_resolution,[],[f76,f42])).
% 1.24/0.54  fof(f76,plain,(
% 1.24/0.54    ( ! [X0] : (m1_pre_topc(X0,sK1) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | ~l1_pre_topc(X0)) )),
% 1.24/0.54    inference(resolution,[],[f72,f54])).
% 1.24/0.54  fof(f72,plain,(
% 1.24/0.54    ( ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | m1_pre_topc(X0,sK1)) )),
% 1.24/0.54    inference(subsumption_resolution,[],[f69,f43])).
% 1.24/0.54  fof(f69,plain,(
% 1.24/0.54    ( ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | m1_pre_topc(X0,sK1) | ~l1_pre_topc(sK1)) )),
% 1.24/0.54    inference(superposition,[],[f61,f44])).
% 1.24/0.54  fof(f221,plain,(
% 1.24/0.54    ~m1_pre_topc(sK0,sK1) | (~spl3_4 | ~spl3_7)),
% 1.24/0.54    inference(subsumption_resolution,[],[f220,f205])).
% 1.24/0.54  fof(f205,plain,(
% 1.24/0.54    v1_tops_2(u1_pre_topc(sK1),sK1) | ~spl3_4),
% 1.24/0.54    inference(subsumption_resolution,[],[f202,f68])).
% 1.24/0.54  fof(f68,plain,(
% 1.24/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.24/0.54    inference(equality_resolution,[],[f62])).
% 1.24/0.54  fof(f62,plain,(
% 1.24/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.24/0.54    inference(cnf_transformation,[],[f41])).
% 1.24/0.54  fof(f202,plain,(
% 1.24/0.54    ~r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK1)) | v1_tops_2(u1_pre_topc(sK1),sK1) | ~spl3_4),
% 1.24/0.54    inference(resolution,[],[f146,f138])).
% 1.24/0.54  fof(f138,plain,(
% 1.24/0.54    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_4),
% 1.24/0.54    inference(subsumption_resolution,[],[f128,f43])).
% 1.24/0.54  fof(f128,plain,(
% 1.24/0.54    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK1) | ~spl3_4),
% 1.24/0.54    inference(superposition,[],[f49,f102])).
% 1.24/0.54  fof(f146,plain,(
% 1.24/0.54    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X4,u1_pre_topc(sK1)) | v1_tops_2(X4,sK1)) ) | ~spl3_4),
% 1.24/0.54    inference(subsumption_resolution,[],[f135,f43])).
% 1.24/0.54  fof(f135,plain,(
% 1.24/0.54    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X4,u1_pre_topc(sK1)) | v1_tops_2(X4,sK1) | ~l1_pre_topc(sK1)) ) | ~spl3_4),
% 1.24/0.54    inference(superposition,[],[f59,f102])).
% 1.24/0.54  fof(f59,plain,(
% 1.24/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X1,u1_pre_topc(X0)) | v1_tops_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f39])).
% 1.24/0.54  fof(f39,plain,(
% 1.24/0.54    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(X0))) & (r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.24/0.54    inference(nnf_transformation,[],[f25])).
% 1.24/0.54  fof(f25,plain,(
% 1.24/0.54    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.24/0.54    inference(ennf_transformation,[],[f8])).
% 1.24/0.54  fof(f8,axiom,(
% 1.24/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 1.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tops_2)).
% 1.24/0.54  fof(f220,plain,(
% 1.24/0.54    ~v1_tops_2(u1_pre_topc(sK1),sK1) | ~m1_pre_topc(sK0,sK1) | (~spl3_4 | ~spl3_7)),
% 1.24/0.54    inference(subsumption_resolution,[],[f219,f43])).
% 1.24/0.54  fof(f219,plain,(
% 1.24/0.54    ~l1_pre_topc(sK1) | ~v1_tops_2(u1_pre_topc(sK1),sK1) | ~m1_pre_topc(sK0,sK1) | (~spl3_4 | ~spl3_7)),
% 1.24/0.54    inference(subsumption_resolution,[],[f213,f138])).
% 1.24/0.54  fof(f213,plain,(
% 1.24/0.54    ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK1) | ~v1_tops_2(u1_pre_topc(sK1),sK1) | ~m1_pre_topc(sK0,sK1) | (~spl3_4 | ~spl3_7)),
% 1.24/0.54    inference(superposition,[],[f167,f102])).
% 1.24/0.54  fof(f167,plain,(
% 1.24/0.54    ( ! [X0] : (~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tops_2(u1_pre_topc(sK1),X0) | ~m1_pre_topc(sK0,X0)) ) | ~spl3_7),
% 1.24/0.54    inference(avatar_component_clause,[],[f166])).
% 1.24/0.54  fof(f166,plain,(
% 1.24/0.54    spl3_7 <=> ! [X0] : (~v1_tops_2(u1_pre_topc(sK1),X0) | ~l1_pre_topc(X0) | ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(sK0,X0))),
% 1.24/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.24/0.54  fof(f200,plain,(
% 1.24/0.54    spl3_10 | ~spl3_11 | ~spl3_4),
% 1.24/0.54    inference(avatar_split_clause,[],[f191,f100,f197,f193])).
% 1.24/0.54  fof(f191,plain,(
% 1.24/0.54    ~v1_tops_2(u1_pre_topc(sK0),sK1) | r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1)) | ~spl3_4),
% 1.24/0.54    inference(subsumption_resolution,[],[f189,f42])).
% 1.24/0.54  fof(f189,plain,(
% 1.24/0.54    ~v1_tops_2(u1_pre_topc(sK0),sK1) | r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1)) | ~l1_pre_topc(sK0) | ~spl3_4),
% 1.24/0.54    inference(resolution,[],[f145,f49])).
% 1.24/0.54  fof(f145,plain,(
% 1.24/0.54    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(X3,sK1) | r1_tarski(X3,u1_pre_topc(sK1))) ) | ~spl3_4),
% 1.24/0.54    inference(subsumption_resolution,[],[f134,f43])).
% 1.24/0.54  fof(f134,plain,(
% 1.24/0.54    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(X3,sK1) | r1_tarski(X3,u1_pre_topc(sK1)) | ~l1_pre_topc(sK1)) ) | ~spl3_4),
% 1.24/0.54    inference(superposition,[],[f58,f102])).
% 1.24/0.54  fof(f58,plain,(
% 1.24/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0) | r1_tarski(X1,u1_pre_topc(X0)) | ~l1_pre_topc(X0)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f39])).
% 1.24/0.54  fof(f178,plain,(
% 1.24/0.54    spl3_9 | ~spl3_8 | ~spl3_4),
% 1.24/0.54    inference(avatar_split_clause,[],[f173,f100,f169,f175])).
% 1.24/0.54  fof(f169,plain,(
% 1.24/0.54    spl3_8 <=> v1_tops_2(u1_pre_topc(sK1),sK0)),
% 1.24/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.24/0.54  fof(f173,plain,(
% 1.24/0.54    ~v1_tops_2(u1_pre_topc(sK1),sK0) | r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0)) | ~spl3_4),
% 1.24/0.54    inference(subsumption_resolution,[],[f162,f42])).
% 1.24/0.54  fof(f162,plain,(
% 1.24/0.54    ~v1_tops_2(u1_pre_topc(sK1),sK0) | r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0)) | ~l1_pre_topc(sK0) | ~spl3_4),
% 1.24/0.54    inference(resolution,[],[f138,f58])).
% 1.24/0.54  fof(f172,plain,(
% 1.24/0.54    spl3_7 | spl3_8 | ~spl3_4),
% 1.24/0.54    inference(avatar_split_clause,[],[f161,f100,f169,f166])).
% 1.24/0.54  fof(f161,plain,(
% 1.24/0.54    ( ! [X0] : (v1_tops_2(u1_pre_topc(sK1),sK0) | ~v1_tops_2(u1_pre_topc(sK1),X0) | ~m1_pre_topc(sK0,X0) | ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) ) | ~spl3_4),
% 1.24/0.54    inference(resolution,[],[f138,f66])).
% 1.24/0.54  fof(f160,plain,(
% 1.24/0.54    spl3_5 | ~spl3_6 | ~spl3_4),
% 1.24/0.54    inference(avatar_split_clause,[],[f151,f100,f157,f153])).
% 1.24/0.54  fof(f151,plain,(
% 1.24/0.54    ~r2_hidden(sK2(sK1),u1_pre_topc(sK0)) | r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0)) | ~spl3_4),
% 1.24/0.54    inference(subsumption_resolution,[],[f150,f42])).
% 1.24/0.54  fof(f150,plain,(
% 1.24/0.54    ~r2_hidden(sK2(sK1),u1_pre_topc(sK0)) | r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0)) | ~l1_pre_topc(sK0) | ~spl3_4),
% 1.24/0.54    inference(subsumption_resolution,[],[f148,f45])).
% 1.24/0.54  fof(f45,plain,(
% 1.24/0.54    v3_tdlat_3(sK0)),
% 1.24/0.54    inference(cnf_transformation,[],[f33])).
% 1.24/0.54  fof(f148,plain,(
% 1.24/0.54    ~r2_hidden(sK2(sK1),u1_pre_topc(sK0)) | r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0)) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~spl3_4),
% 1.24/0.54    inference(resolution,[],[f140,f50])).
% 1.24/0.54  % (4071)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.24/0.54  fof(f50,plain,(
% 1.24/0.54    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,u1_pre_topc(X0)) | r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f37])).
% 1.24/0.54  fof(f140,plain,(
% 1.24/0.54    m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_4),
% 1.24/0.54    inference(subsumption_resolution,[],[f139,f43])).
% 1.24/0.54  fof(f139,plain,(
% 1.24/0.54    m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK1) | ~spl3_4),
% 1.24/0.54    inference(subsumption_resolution,[],[f130,f46])).
% 1.24/0.54  fof(f130,plain,(
% 1.24/0.54    m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tdlat_3(sK1) | ~l1_pre_topc(sK1) | ~spl3_4),
% 1.24/0.54    inference(superposition,[],[f51,f102])).
% 1.24/0.54  fof(f51,plain,(
% 1.24/0.54    ( ! [X0] : (m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) | v3_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f37])).
% 1.24/0.54  fof(f121,plain,(
% 1.24/0.54    spl3_3),
% 1.24/0.54    inference(avatar_contradiction_clause,[],[f120])).
% 1.24/0.54  fof(f120,plain,(
% 1.24/0.54    $false | spl3_3),
% 1.24/0.54    inference(subsumption_resolution,[],[f119,f42])).
% 1.24/0.54  fof(f119,plain,(
% 1.24/0.54    ~l1_pre_topc(sK0) | spl3_3),
% 1.24/0.54    inference(subsumption_resolution,[],[f117,f98])).
% 1.24/0.54  fof(f98,plain,(
% 1.24/0.54    ~r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) | spl3_3),
% 1.24/0.54    inference(avatar_component_clause,[],[f96])).
% 1.24/0.54  fof(f96,plain,(
% 1.24/0.54    spl3_3 <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))),
% 1.24/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.24/0.54  fof(f117,plain,(
% 1.24/0.54    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 1.24/0.54    inference(resolution,[],[f115,f57])).
% 1.24/0.54  fof(f57,plain,(
% 1.24/0.54    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f24])).
% 1.24/0.54  fof(f24,plain,(
% 1.24/0.54    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.24/0.54    inference(ennf_transformation,[],[f11])).
% 1.24/0.54  fof(f11,axiom,(
% 1.24/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 1.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).
% 1.24/0.54  fof(f103,plain,(
% 1.24/0.54    ~spl3_3 | spl3_4),
% 1.24/0.54    inference(avatar_split_clause,[],[f94,f100,f96])).
% 1.24/0.54  fof(f94,plain,(
% 1.24/0.54    u1_struct_0(sK0) = u1_struct_0(sK1) | ~r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))),
% 1.24/0.54    inference(resolution,[],[f93,f64])).
% 1.24/0.54  fof(f93,plain,(
% 1.24/0.54    r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.24/0.54    inference(subsumption_resolution,[],[f91,f43])).
% 1.24/0.54  fof(f91,plain,(
% 1.24/0.54    r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1)),
% 1.24/0.54    inference(resolution,[],[f90,f57])).
% 1.24/0.54  % SZS output end Proof for theBenchmark
% 1.24/0.54  % (4059)------------------------------
% 1.24/0.54  % (4059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.54  % (4059)Termination reason: Refutation
% 1.24/0.54  
% 1.24/0.54  % (4059)Memory used [KB]: 10746
% 1.24/0.54  % (4059)Time elapsed: 0.118 s
% 1.24/0.54  % (4059)------------------------------
% 1.24/0.54  % (4059)------------------------------
% 1.24/0.54  % (4073)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.24/0.54  % (4057)Success in time 0.182 s
%------------------------------------------------------------------------------
