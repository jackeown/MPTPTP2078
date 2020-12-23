%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 621 expanded)
%              Number of leaves         :   24 ( 179 expanded)
%              Depth                    :   20
%              Number of atoms          :  618 (4351 expanded)
%              Number of equality atoms :   46 (  76 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f700,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f98,f290,f302,f386,f513,f545,f548,f562,f620,f681,f684,f692])).

fof(f692,plain,
    ( ~ spl3_1
    | spl3_18 ),
    inference(avatar_split_clause,[],[f691,f248,f90])).

fof(f90,plain,
    ( spl3_1
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f248,plain,
    ( spl3_18
  <=> v1_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f691,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f690,f55])).

fof(f55,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ( v1_subset_1(sK1,u1_struct_0(sK0))
      | ~ v3_tex_2(sK1,sK0) )
    & ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
      | v3_tex_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v1_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f43,f45,f44])).

fof(f44,plain,
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

fof(f45,plain,
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

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).

fof(f690,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ v3_tex_2(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f689,f56])).

fof(f56,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f689,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ v3_tex_2(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f688,f58])).

fof(f58,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f688,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ v3_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f415,f280])).

fof(f280,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f279,f56])).

fof(f279,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f278,f58])).

fof(f278,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f264,f57])).

fof(f57,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f264,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f59,f70])).

fof(f70,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK2(X0),X0)
            & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f51,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK2(X0),X0)
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).

fof(f59,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f415,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ v3_tex_2(sK1,sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f59,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tex_2(X1,X0)
              & v3_pre_topc(X1,X0) )
           => v1_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tex_2)).

fof(f684,plain,
    ( spl3_18
    | ~ spl3_23
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f683,f258,f299,f248])).

fof(f299,plain,
    ( spl3_23
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f258,plain,
    ( spl3_20
  <=> u1_struct_0(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f683,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | v1_tops_1(sK1,sK0)
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f682,f260])).

fof(f260,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f258])).

fof(f682,plain,
    ( v1_tops_1(sK1,sK0)
    | u1_struct_0(sK0) != k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f419,f58])).

fof(f419,plain,
    ( v1_tops_1(sK1,sK0)
    | u1_struct_0(sK0) != k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f59,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | u1_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

fof(f681,plain,
    ( ~ spl3_18
    | spl3_1 ),
    inference(avatar_split_clause,[],[f680,f90,f248])).

fof(f680,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f679,f55])).

fof(f679,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ v1_tops_1(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f678,f56])).

fof(f678,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ v1_tops_1(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f621,f58])).

fof(f621,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ v1_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f414,f284])).

fof(f284,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f283,f55])).

fof(f283,plain,
    ( v2_tex_2(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f282,f56])).

fof(f282,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f281,f57])).

fof(f281,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f265,f58])).

fof(f265,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f59,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

fof(f414,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ v1_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f59,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_tex_2(X1,X0)
              & v1_tops_1(X1,X0) )
           => v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).

fof(f620,plain,
    ( ~ spl3_2
    | ~ spl3_20 ),
    inference(avatar_contradiction_clause,[],[f619])).

fof(f619,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f618,f571])).

fof(f571,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl3_2
    | ~ spl3_20 ),
    inference(backward_demodulation,[],[f96,f260])).

fof(f96,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl3_2
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f618,plain,
    ( ~ v1_subset_1(sK1,sK1)
    | ~ spl3_20 ),
    inference(resolution,[],[f570,f84])).

fof(f84,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f570,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl3_20 ),
    inference(backward_demodulation,[],[f59,f260])).

fof(f562,plain,
    ( ~ spl3_22
    | spl3_20
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f561,f287,f258,f295])).

fof(f295,plain,
    ( spl3_22
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f287,plain,
    ( spl3_21
  <=> u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f561,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ v4_pre_topc(sK1,sK0)
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f560,f289])).

fof(f289,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f287])).

fof(f560,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f420,f58])).

fof(f420,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f59,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f548,plain,
    ( spl3_22
    | ~ spl3_26 ),
    inference(avatar_contradiction_clause,[],[f547])).

fof(f547,plain,
    ( $false
    | spl3_22
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f546,f297])).

fof(f297,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl3_22 ),
    inference(avatar_component_clause,[],[f295])).

fof(f546,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f466,f306])).

fof(f306,plain,(
    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f270,f58])).

fof(f270,plain,
    ( sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f59,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f466,plain,
    ( v4_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),sK0)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f464])).

fof(f464,plain,
    ( spl3_26
  <=> v4_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f545,plain,(
    spl3_24 ),
    inference(avatar_contradiction_clause,[],[f544])).

fof(f544,plain,
    ( $false
    | spl3_24 ),
    inference(subsumption_resolution,[],[f543,f59])).

fof(f543,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_24 ),
    inference(forward_demodulation,[],[f458,f306])).

fof(f458,plain,
    ( ~ m1_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_24 ),
    inference(avatar_component_clause,[],[f456])).

fof(f456,plain,
    ( spl3_24
  <=> m1_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f513,plain,
    ( ~ spl3_24
    | spl3_26 ),
    inference(avatar_split_clause,[],[f512,f464,f456])).

fof(f512,plain,
    ( v4_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),sK0)
    | ~ m1_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f511,f56])).

fof(f511,plain,
    ( v4_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),sK0)
    | ~ m1_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f510,f58])).

fof(f510,plain,
    ( v4_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),sK0)
    | ~ m1_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f509,f307])).

fof(f307,plain,(
    m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f271,f58])).

fof(f271,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f59,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f509,plain,
    ( v4_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),sK0)
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ m1_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f448,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                  | ~ v4_pre_topc(X2,X0) )
                & ( v4_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_borsuk_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                  | ~ v4_pre_topc(X2,X0) )
                & ( v4_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_borsuk_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <=> v4_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <=> v4_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                <=> v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tsep_1)).

fof(f448,plain,(
    v1_borsuk_1(k1_pre_topc(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f447,f55])).

fof(f447,plain,
    ( v1_borsuk_1(k1_pre_topc(sK0,sK1),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f446,f56])).

fof(f446,plain,
    ( v1_borsuk_1(k1_pre_topc(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f445,f57])).

fof(f445,plain,
    ( v1_borsuk_1(k1_pre_topc(sK0,sK1),sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f441,f58])).

fof(f441,plain,
    ( v1_borsuk_1(k1_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f307,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_borsuk_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tdlat_3(X1)
            & v1_borsuk_1(X1,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tdlat_3(X1)
            & v1_borsuk_1(X1,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
            & v1_borsuk_1(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
            & v1_tsep_1(X1,X0)
            & v1_borsuk_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_tdlat_3)).

fof(f386,plain,
    ( spl3_20
    | spl3_2 ),
    inference(avatar_split_clause,[],[f272,f94,f258])).

fof(f272,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | u1_struct_0(sK0) = sK1 ),
    inference(resolution,[],[f59,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f302,plain,
    ( ~ spl3_22
    | spl3_23 ),
    inference(avatar_split_clause,[],[f293,f299,f295])).

fof(f293,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f268,f58])).

fof(f268,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f59,f76])).

fof(f290,plain,
    ( ~ spl3_18
    | spl3_21 ),
    inference(avatar_split_clause,[],[f285,f287,f248])).

fof(f285,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f266,f58])).

fof(f266,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ v1_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f59,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f98,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f60,f94,f90])).

fof(f60,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f97,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f61,f94,f90])).

fof(f61,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:31:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.44  % (8600)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.45  % (8600)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f700,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(avatar_sat_refutation,[],[f97,f98,f290,f302,f386,f513,f545,f548,f562,f620,f681,f684,f692])).
% 0.20/0.45  fof(f692,plain,(
% 0.20/0.45    ~spl3_1 | spl3_18),
% 0.20/0.45    inference(avatar_split_clause,[],[f691,f248,f90])).
% 0.20/0.45  fof(f90,plain,(
% 0.20/0.45    spl3_1 <=> v3_tex_2(sK1,sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.45  fof(f248,plain,(
% 0.20/0.45    spl3_18 <=> v1_tops_1(sK1,sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.45  fof(f691,plain,(
% 0.20/0.45    v1_tops_1(sK1,sK0) | ~v3_tex_2(sK1,sK0)),
% 0.20/0.45    inference(subsumption_resolution,[],[f690,f55])).
% 0.20/0.45  fof(f55,plain,(
% 0.20/0.45    ~v2_struct_0(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f46])).
% 0.20/0.45  fof(f46,plain,(
% 0.20/0.45    ((v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)) & (~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f43,f45,f44])).
% 0.20/0.45  fof(f44,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((v1_subset_1(X1,u1_struct_0(sK0)) | ~v3_tex_2(X1,sK0)) & (~v1_subset_1(X1,u1_struct_0(sK0)) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f45,plain,(
% 0.20/0.45    ? [X1] : ((v1_subset_1(X1,u1_struct_0(sK0)) | ~v3_tex_2(X1,sK0)) & (~v1_subset_1(X1,u1_struct_0(sK0)) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)) & (~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f43,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f42])).
% 0.20/0.45  fof(f42,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.45    inference(nnf_transformation,[],[f20])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f19])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f16])).
% 0.20/0.45  fof(f16,negated_conjecture,(
% 0.20/0.45    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.20/0.45    inference(negated_conjecture,[],[f15])).
% 0.20/0.45  fof(f15,conjecture,(
% 0.20/0.45    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).
% 0.20/0.45  fof(f690,plain,(
% 0.20/0.45    v1_tops_1(sK1,sK0) | ~v3_tex_2(sK1,sK0) | v2_struct_0(sK0)),
% 0.20/0.45    inference(subsumption_resolution,[],[f689,f56])).
% 0.20/0.45  fof(f56,plain,(
% 0.20/0.45    v2_pre_topc(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f46])).
% 0.20/0.45  fof(f689,plain,(
% 0.20/0.45    v1_tops_1(sK1,sK0) | ~v3_tex_2(sK1,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.45    inference(subsumption_resolution,[],[f688,f58])).
% 0.20/0.45  fof(f58,plain,(
% 0.20/0.45    l1_pre_topc(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f46])).
% 0.20/0.45  fof(f688,plain,(
% 0.20/0.45    v1_tops_1(sK1,sK0) | ~v3_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.45    inference(subsumption_resolution,[],[f415,f280])).
% 0.20/0.45  fof(f280,plain,(
% 0.20/0.45    v3_pre_topc(sK1,sK0)),
% 0.20/0.45    inference(subsumption_resolution,[],[f279,f56])).
% 0.20/0.45  fof(f279,plain,(
% 0.20/0.45    v3_pre_topc(sK1,sK0) | ~v2_pre_topc(sK0)),
% 0.20/0.45    inference(subsumption_resolution,[],[f278,f58])).
% 0.20/0.45  fof(f278,plain,(
% 0.20/0.45    v3_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.20/0.45    inference(subsumption_resolution,[],[f264,f57])).
% 0.20/0.45  fof(f57,plain,(
% 0.20/0.45    v1_tdlat_3(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f46])).
% 0.20/0.45  fof(f264,plain,(
% 0.20/0.45    v3_pre_topc(sK1,sK0) | ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.20/0.45    inference(resolution,[],[f59,f70])).
% 0.20/0.45  fof(f70,plain,(
% 0.20/0.45    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f53])).
% 0.20/0.45  fof(f53,plain,(
% 0.20/0.45    ! [X0] : (((v1_tdlat_3(X0) | (~v3_pre_topc(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f51,f52])).
% 0.20/0.45  fof(f52,plain,(
% 0.20/0.45    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f51,plain,(
% 0.20/0.45    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.45    inference(rectify,[],[f50])).
% 0.20/0.45  fof(f50,plain,(
% 0.20/0.45    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.45    inference(nnf_transformation,[],[f29])).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.45    inference(flattening,[],[f28])).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f11])).
% 0.20/0.45  fof(f11,axiom,(
% 0.20/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v3_pre_topc(X1,X0))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).
% 0.20/0.45  fof(f59,plain,(
% 0.20/0.45    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.45    inference(cnf_transformation,[],[f46])).
% 0.20/0.45  fof(f415,plain,(
% 0.20/0.45    v1_tops_1(sK1,sK0) | ~v3_tex_2(sK1,sK0) | ~v3_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.45    inference(resolution,[],[f59,f66])).
% 0.20/0.45  fof(f66,plain,(
% 0.20/0.45    ( ! [X0,X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f25])).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f24])).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) | (~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f13])).
% 0.20/0.45  fof(f13,axiom,(
% 0.20/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tex_2(X1,X0) & v3_pre_topc(X1,X0)) => v1_tops_1(X1,X0))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tex_2)).
% 0.20/0.45  fof(f684,plain,(
% 0.20/0.45    spl3_18 | ~spl3_23 | ~spl3_20),
% 0.20/0.45    inference(avatar_split_clause,[],[f683,f258,f299,f248])).
% 0.20/0.45  fof(f299,plain,(
% 0.20/0.45    spl3_23 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.20/0.45  fof(f258,plain,(
% 0.20/0.45    spl3_20 <=> u1_struct_0(sK0) = sK1),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.45  fof(f683,plain,(
% 0.20/0.45    sK1 != k2_pre_topc(sK0,sK1) | v1_tops_1(sK1,sK0) | ~spl3_20),
% 0.20/0.45    inference(forward_demodulation,[],[f682,f260])).
% 0.20/0.45  fof(f260,plain,(
% 0.20/0.45    u1_struct_0(sK0) = sK1 | ~spl3_20),
% 0.20/0.45    inference(avatar_component_clause,[],[f258])).
% 0.20/0.45  fof(f682,plain,(
% 0.20/0.45    v1_tops_1(sK1,sK0) | u1_struct_0(sK0) != k2_pre_topc(sK0,sK1)),
% 0.20/0.45    inference(subsumption_resolution,[],[f419,f58])).
% 0.20/0.45  fof(f419,plain,(
% 0.20/0.45    v1_tops_1(sK1,sK0) | u1_struct_0(sK0) != k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 0.20/0.45    inference(resolution,[],[f59,f75])).
% 0.20/0.45  fof(f75,plain,(
% 0.20/0.45    ( ! [X0,X1] : (v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f54])).
% 0.20/0.45  fof(f54,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.45    inference(nnf_transformation,[],[f32])).
% 0.20/0.45  fof(f32,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f9])).
% 0.20/0.45  fof(f9,axiom,(
% 0.20/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).
% 0.20/0.45  fof(f681,plain,(
% 0.20/0.45    ~spl3_18 | spl3_1),
% 0.20/0.45    inference(avatar_split_clause,[],[f680,f90,f248])).
% 0.20/0.45  fof(f680,plain,(
% 0.20/0.45    v3_tex_2(sK1,sK0) | ~v1_tops_1(sK1,sK0)),
% 0.20/0.45    inference(subsumption_resolution,[],[f679,f55])).
% 0.20/0.45  fof(f679,plain,(
% 0.20/0.45    v3_tex_2(sK1,sK0) | ~v1_tops_1(sK1,sK0) | v2_struct_0(sK0)),
% 0.20/0.45    inference(subsumption_resolution,[],[f678,f56])).
% 0.20/0.45  fof(f678,plain,(
% 0.20/0.45    v3_tex_2(sK1,sK0) | ~v1_tops_1(sK1,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.45    inference(subsumption_resolution,[],[f621,f58])).
% 0.20/0.45  fof(f621,plain,(
% 0.20/0.45    v3_tex_2(sK1,sK0) | ~v1_tops_1(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.45    inference(subsumption_resolution,[],[f414,f284])).
% 0.20/0.45  fof(f284,plain,(
% 0.20/0.45    v2_tex_2(sK1,sK0)),
% 0.20/0.45    inference(subsumption_resolution,[],[f283,f55])).
% 0.20/0.45  fof(f283,plain,(
% 0.20/0.45    v2_tex_2(sK1,sK0) | v2_struct_0(sK0)),
% 0.20/0.45    inference(subsumption_resolution,[],[f282,f56])).
% 0.20/0.45  fof(f282,plain,(
% 0.20/0.45    v2_tex_2(sK1,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.45    inference(subsumption_resolution,[],[f281,f57])).
% 0.20/0.45  fof(f281,plain,(
% 0.20/0.45    v2_tex_2(sK1,sK0) | ~v1_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.45    inference(subsumption_resolution,[],[f265,f58])).
% 0.20/0.45  fof(f265,plain,(
% 0.20/0.45    v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.45    inference(resolution,[],[f59,f73])).
% 0.20/0.45  fof(f73,plain,(
% 0.20/0.45    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f31])).
% 0.20/0.45  fof(f31,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f30])).
% 0.20/0.45  fof(f30,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f12])).
% 0.20/0.45  fof(f12,axiom,(
% 0.20/0.45    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).
% 0.20/0.45  fof(f414,plain,(
% 0.20/0.45    v3_tex_2(sK1,sK0) | ~v2_tex_2(sK1,sK0) | ~v1_tops_1(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.45    inference(resolution,[],[f59,f65])).
% 0.20/0.45  fof(f65,plain,(
% 0.20/0.45    ( ! [X0,X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f23])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f22])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) | (~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f14])).
% 0.20/0.45  fof(f14,axiom,(
% 0.20/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).
% 0.20/0.45  fof(f620,plain,(
% 0.20/0.45    ~spl3_2 | ~spl3_20),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f619])).
% 0.20/0.45  fof(f619,plain,(
% 0.20/0.45    $false | (~spl3_2 | ~spl3_20)),
% 0.20/0.45    inference(subsumption_resolution,[],[f618,f571])).
% 0.20/0.45  fof(f571,plain,(
% 0.20/0.45    v1_subset_1(sK1,sK1) | (~spl3_2 | ~spl3_20)),
% 0.20/0.45    inference(backward_demodulation,[],[f96,f260])).
% 0.20/0.45  fof(f96,plain,(
% 0.20/0.45    v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl3_2),
% 0.20/0.45    inference(avatar_component_clause,[],[f94])).
% 0.20/0.45  fof(f94,plain,(
% 0.20/0.45    spl3_2 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.45  fof(f618,plain,(
% 0.20/0.45    ~v1_subset_1(sK1,sK1) | ~spl3_20),
% 0.20/0.45    inference(resolution,[],[f570,f84])).
% 0.20/0.45  fof(f84,plain,(
% 0.20/0.45    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 0.20/0.45    inference(equality_resolution,[],[f62])).
% 0.20/0.45  fof(f62,plain,(
% 0.20/0.45    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f47])).
% 0.20/0.45  fof(f47,plain,(
% 0.20/0.45    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.45    inference(nnf_transformation,[],[f21])).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f10])).
% 0.20/0.45  fof(f10,axiom,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.20/0.45  fof(f570,plain,(
% 0.20/0.45    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~spl3_20),
% 0.20/0.45    inference(backward_demodulation,[],[f59,f260])).
% 0.20/0.45  fof(f562,plain,(
% 0.20/0.45    ~spl3_22 | spl3_20 | ~spl3_21),
% 0.20/0.45    inference(avatar_split_clause,[],[f561,f287,f258,f295])).
% 0.20/0.45  fof(f295,plain,(
% 0.20/0.45    spl3_22 <=> v4_pre_topc(sK1,sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.20/0.45  fof(f287,plain,(
% 0.20/0.45    spl3_21 <=> u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.45  fof(f561,plain,(
% 0.20/0.45    u1_struct_0(sK0) = sK1 | ~v4_pre_topc(sK1,sK0) | ~spl3_21),
% 0.20/0.45    inference(forward_demodulation,[],[f560,f289])).
% 0.20/0.45  fof(f289,plain,(
% 0.20/0.45    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~spl3_21),
% 0.20/0.45    inference(avatar_component_clause,[],[f287])).
% 0.20/0.45  fof(f560,plain,(
% 0.20/0.45    sK1 = k2_pre_topc(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 0.20/0.45    inference(subsumption_resolution,[],[f420,f58])).
% 0.20/0.45  fof(f420,plain,(
% 0.20/0.45    sK1 = k2_pre_topc(sK0,sK1) | ~v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.20/0.45    inference(resolution,[],[f59,f76])).
% 0.20/0.45  fof(f76,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f34])).
% 0.20/0.45  fof(f34,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.45    inference(flattening,[],[f33])).
% 0.20/0.45  fof(f33,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f5])).
% 0.20/0.45  fof(f5,axiom,(
% 0.20/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.20/0.45  fof(f548,plain,(
% 0.20/0.45    spl3_22 | ~spl3_26),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f547])).
% 0.20/0.45  fof(f547,plain,(
% 0.20/0.45    $false | (spl3_22 | ~spl3_26)),
% 0.20/0.45    inference(subsumption_resolution,[],[f546,f297])).
% 0.20/0.45  fof(f297,plain,(
% 0.20/0.45    ~v4_pre_topc(sK1,sK0) | spl3_22),
% 0.20/0.45    inference(avatar_component_clause,[],[f295])).
% 0.20/0.45  fof(f546,plain,(
% 0.20/0.45    v4_pre_topc(sK1,sK0) | ~spl3_26),
% 0.20/0.45    inference(forward_demodulation,[],[f466,f306])).
% 0.20/0.45  fof(f306,plain,(
% 0.20/0.45    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))),
% 0.20/0.45    inference(subsumption_resolution,[],[f270,f58])).
% 0.20/0.45  fof(f270,plain,(
% 0.20/0.45    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.20/0.45    inference(resolution,[],[f59,f78])).
% 0.20/0.45  fof(f78,plain,(
% 0.20/0.45    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f35])).
% 0.20/0.45  fof(f35,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).
% 0.20/0.45  fof(f466,plain,(
% 0.20/0.45    v4_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),sK0) | ~spl3_26),
% 0.20/0.45    inference(avatar_component_clause,[],[f464])).
% 0.20/0.45  fof(f464,plain,(
% 0.20/0.45    spl3_26 <=> v4_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.20/0.45  fof(f545,plain,(
% 0.20/0.45    spl3_24),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f544])).
% 0.20/0.45  fof(f544,plain,(
% 0.20/0.45    $false | spl3_24),
% 0.20/0.45    inference(subsumption_resolution,[],[f543,f59])).
% 0.20/0.45  fof(f543,plain,(
% 0.20/0.45    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_24),
% 0.20/0.45    inference(forward_demodulation,[],[f458,f306])).
% 0.20/0.45  fof(f458,plain,(
% 0.20/0.45    ~m1_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_24),
% 0.20/0.45    inference(avatar_component_clause,[],[f456])).
% 0.20/0.45  fof(f456,plain,(
% 0.20/0.45    spl3_24 <=> m1_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.20/0.45  fof(f513,plain,(
% 0.20/0.45    ~spl3_24 | spl3_26),
% 0.20/0.45    inference(avatar_split_clause,[],[f512,f464,f456])).
% 0.20/0.45  fof(f512,plain,(
% 0.20/0.45    v4_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),sK0) | ~m1_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.45    inference(subsumption_resolution,[],[f511,f56])).
% 0.20/0.45  fof(f511,plain,(
% 0.20/0.45    v4_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),sK0) | ~m1_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0)),
% 0.20/0.45    inference(subsumption_resolution,[],[f510,f58])).
% 0.20/0.45  fof(f510,plain,(
% 0.20/0.45    v4_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),sK0) | ~m1_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.20/0.45    inference(subsumption_resolution,[],[f509,f307])).
% 0.20/0.45  fof(f307,plain,(
% 0.20/0.45    m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)),
% 0.20/0.45    inference(subsumption_resolution,[],[f271,f58])).
% 0.20/0.45  fof(f271,plain,(
% 0.20/0.45    m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | ~l1_pre_topc(sK0)),
% 0.20/0.45    inference(resolution,[],[f59,f83])).
% 0.20/0.45  fof(f83,plain,(
% 0.20/0.45    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f41])).
% 0.20/0.45  fof(f41,plain,(
% 0.20/0.45    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.45    inference(flattening,[],[f40])).
% 0.20/0.45  fof(f40,plain,(
% 0.20/0.45    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f18])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_pre_topc(k1_pre_topc(X0,X1),X0))),
% 0.20/0.45    inference(pure_predicate_removal,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 0.20/0.45  fof(f509,plain,(
% 0.20/0.45    v4_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),sK0) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | ~m1_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.20/0.45    inference(resolution,[],[f448,f88])).
% 0.20/0.45  fof(f88,plain,(
% 0.20/0.45    ( ! [X0,X1] : (v4_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.45    inference(duplicate_literal_removal,[],[f87])).
% 0.20/0.45  fof(f87,plain,(
% 0.20/0.45    ( ! [X0,X1] : (v4_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.45    inference(equality_resolution,[],[f67])).
% 0.20/0.45  fof(f67,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (v4_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f49])).
% 0.20/0.45  fof(f49,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) | ~v4_pre_topc(X2,X0)) & (v4_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.45    inference(flattening,[],[f48])).
% 0.20/0.45  fof(f48,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) | ~v4_pre_topc(X2,X0)) & (v4_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.45    inference(nnf_transformation,[],[f27])).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.45    inference(flattening,[],[f26])).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,axiom,(
% 0.20/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0))))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tsep_1)).
% 0.20/0.45  fof(f448,plain,(
% 0.20/0.45    v1_borsuk_1(k1_pre_topc(sK0,sK1),sK0)),
% 0.20/0.45    inference(subsumption_resolution,[],[f447,f55])).
% 0.20/0.45  fof(f447,plain,(
% 0.20/0.45    v1_borsuk_1(k1_pre_topc(sK0,sK1),sK0) | v2_struct_0(sK0)),
% 0.20/0.45    inference(subsumption_resolution,[],[f446,f56])).
% 0.20/0.45  fof(f446,plain,(
% 0.20/0.45    v1_borsuk_1(k1_pre_topc(sK0,sK1),sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.45    inference(subsumption_resolution,[],[f445,f57])).
% 0.20/0.45  fof(f445,plain,(
% 0.20/0.45    v1_borsuk_1(k1_pre_topc(sK0,sK1),sK0) | ~v1_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.45    inference(subsumption_resolution,[],[f441,f58])).
% 0.20/0.45  fof(f441,plain,(
% 0.20/0.45    v1_borsuk_1(k1_pre_topc(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.45    inference(resolution,[],[f307,f80])).
% 0.20/0.45  fof(f80,plain,(
% 0.20/0.45    ( ! [X0,X1] : (v1_borsuk_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f39])).
% 0.20/0.45  fof(f39,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : ((v1_tdlat_3(X1) & v1_borsuk_1(X1,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f38])).
% 0.20/0.45  fof(f38,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : ((v1_tdlat_3(X1) & v1_borsuk_1(X1,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f17])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_borsuk_1(X1,X0))))),
% 0.20/0.45    inference(pure_predicate_removal,[],[f8])).
% 0.20/0.45  fof(f8,axiom,(
% 0.20/0.45    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_tsep_1(X1,X0) & v1_borsuk_1(X1,X0))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_tdlat_3)).
% 0.20/0.45  fof(f386,plain,(
% 0.20/0.45    spl3_20 | spl3_2),
% 0.20/0.45    inference(avatar_split_clause,[],[f272,f94,f258])).
% 0.20/0.45  fof(f272,plain,(
% 0.20/0.45    v1_subset_1(sK1,u1_struct_0(sK0)) | u1_struct_0(sK0) = sK1),
% 0.20/0.45    inference(resolution,[],[f59,f63])).
% 0.20/0.45  fof(f63,plain,(
% 0.20/0.45    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f47])).
% 0.20/0.45  fof(f302,plain,(
% 0.20/0.45    ~spl3_22 | spl3_23),
% 0.20/0.45    inference(avatar_split_clause,[],[f293,f299,f295])).
% 0.20/0.45  fof(f293,plain,(
% 0.20/0.45    sK1 = k2_pre_topc(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 0.20/0.45    inference(subsumption_resolution,[],[f268,f58])).
% 0.20/0.45  fof(f268,plain,(
% 0.20/0.45    sK1 = k2_pre_topc(sK0,sK1) | ~v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.20/0.45    inference(resolution,[],[f59,f76])).
% 0.20/0.45  fof(f290,plain,(
% 0.20/0.45    ~spl3_18 | spl3_21),
% 0.20/0.45    inference(avatar_split_clause,[],[f285,f287,f248])).
% 0.20/0.45  fof(f285,plain,(
% 0.20/0.45    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~v1_tops_1(sK1,sK0)),
% 0.20/0.45    inference(subsumption_resolution,[],[f266,f58])).
% 0.20/0.45  fof(f266,plain,(
% 0.20/0.45    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~v1_tops_1(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.20/0.45    inference(resolution,[],[f59,f74])).
% 0.20/0.45  fof(f74,plain,(
% 0.20/0.45    ( ! [X0,X1] : (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f54])).
% 0.20/0.45  fof(f98,plain,(
% 0.20/0.45    spl3_1 | ~spl3_2),
% 0.20/0.45    inference(avatar_split_clause,[],[f60,f94,f90])).
% 0.20/0.45  fof(f60,plain,(
% 0.20/0.45    ~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f46])).
% 0.20/0.45  fof(f97,plain,(
% 0.20/0.45    ~spl3_1 | spl3_2),
% 0.20/0.45    inference(avatar_split_clause,[],[f61,f94,f90])).
% 0.20/0.45  fof(f61,plain,(
% 0.20/0.45    v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f46])).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (8600)------------------------------
% 0.20/0.45  % (8600)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (8600)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (8600)Memory used [KB]: 6268
% 0.20/0.45  % (8600)Time elapsed: 0.037 s
% 0.20/0.45  % (8600)------------------------------
% 0.20/0.45  % (8600)------------------------------
% 0.20/0.46  % (8580)Success in time 0.093 s
%------------------------------------------------------------------------------
