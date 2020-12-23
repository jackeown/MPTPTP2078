%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 319 expanded)
%              Number of leaves         :   38 ( 126 expanded)
%              Depth                    :    9
%              Number of atoms          :  507 (1646 expanded)
%              Number of equality atoms :   39 (  55 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1333,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f97,f99,f184,f198,f200,f212,f256,f258,f260,f283,f285,f287,f344,f353,f355,f918,f1322,f1330,f1332])).

fof(f1332,plain,
    ( ~ spl3_10
    | ~ spl3_8
    | spl3_2
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f1331,f930,f82,f175,f191])).

fof(f191,plain,
    ( spl3_10
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f175,plain,
    ( spl3_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f82,plain,
    ( spl3_2
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f930,plain,
    ( spl3_41
  <=> v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f1331,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_41 ),
    inference(resolution,[],[f931,f222])).

fof(f222,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(k4_xboole_0(u1_struct_0(X0),X1),X0)
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f220])).

fof(f220,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(k4_xboole_0(u1_struct_0(X0),X1),X0)
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(superposition,[],[f60,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(f931,plain,
    ( v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f930])).

fof(f1330,plain,
    ( ~ spl3_14
    | ~ spl3_10
    | ~ spl3_15
    | spl3_41
    | ~ spl3_34
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f920,f853,f857,f930,f253,f191,f249])).

fof(f249,plain,
    ( spl3_14
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f253,plain,
    ( spl3_15
  <=> v3_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f857,plain,
    ( spl3_34
  <=> v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f853,plain,
    ( spl3_33
  <=> m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f920,plain,
    ( ~ v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_33 ),
    inference(resolution,[],[f854,f64])).

fof(f64,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | v3_pre_topc(X2,X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK2(X0),X0)
            & v4_pre_topc(sK2(X0),X0)
            & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK2(X0),X0)
        & v4_pre_topc(sK2(X0),X0)
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

fof(f854,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f853])).

fof(f1322,plain,
    ( ~ spl3_8
    | ~ spl3_10
    | ~ spl3_1
    | spl3_34
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f1309,f853,f857,f78,f191,f175])).

fof(f78,plain,
    ( spl3_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f1309,plain,
    ( v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_33 ),
    inference(resolution,[],[f396,f854])).

fof(f396,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(k4_xboole_0(u1_struct_0(X8),X9),k1_zfmisc_1(u1_struct_0(X8)))
      | v4_pre_topc(k4_xboole_0(u1_struct_0(X8),X9),X8)
      | ~ v3_pre_topc(X9,X8)
      | ~ l1_pre_topc(X8)
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8))) ) ),
    inference(superposition,[],[f60,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f73,f72])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f918,plain,(
    spl3_33 ),
    inference(avatar_contradiction_clause,[],[f917])).

fof(f917,plain,
    ( $false
    | spl3_33 ),
    inference(resolution,[],[f908,f49])).

fof(f49,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    & v3_tex_2(sK1,sK0)
    & ( v4_pre_topc(sK1,sK0)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v3_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_subset_1(X1,u1_struct_0(X0))
            & v3_tex_2(X1,X0)
            & ( v4_pre_topc(X1,X0)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(sK0))
          & v3_tex_2(X1,sK0)
          & ( v4_pre_topc(X1,sK0)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v3_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( v1_subset_1(X1,u1_struct_0(sK0))
        & v3_tex_2(X1,sK0)
        & ( v4_pre_topc(X1,sK0)
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( v1_subset_1(sK1,u1_struct_0(sK0))
      & v3_tex_2(sK1,sK0)
      & ( v4_pre_topc(sK1,sK0)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v3_tex_2(X1,X0)
          & ( v4_pre_topc(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v3_tex_2(X1,X0)
          & ( v4_pre_topc(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ~ ( v1_subset_1(X1,u1_struct_0(X0))
                & v3_tex_2(X1,X0)
                & ( v4_pre_topc(X1,X0)
                  | v3_pre_topc(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( v1_subset_1(X1,u1_struct_0(X0))
              & v3_tex_2(X1,X0)
              & ( v4_pre_topc(X1,X0)
                | v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_tex_2)).

fof(f908,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_33 ),
    inference(resolution,[],[f855,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f71,f72])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f855,plain,
    ( ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_33 ),
    inference(avatar_component_clause,[],[f853])).

fof(f355,plain,
    ( ~ spl3_8
    | ~ spl3_9
    | spl3_7 ),
    inference(avatar_split_clause,[],[f354,f169,f179,f175])).

fof(f179,plain,
    ( spl3_9
  <=> v1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f169,plain,
    ( spl3_7
  <=> v1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f354,plain,
    ( ~ v1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_7 ),
    inference(superposition,[],[f171,f72])).

fof(f171,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f169])).

fof(f353,plain,
    ( spl3_3
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f350,f169,f94,f90])).

fof(f90,plain,
    ( spl3_3
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f94,plain,
    ( spl3_4
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f350,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f49,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(k3_subset_1(X0,X1))
      | ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X0))
        & v1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tex_2)).

fof(f344,plain,
    ( spl3_9
    | ~ spl3_13 ),
    inference(avatar_contradiction_clause,[],[f343])).

fof(f343,plain,
    ( $false
    | spl3_9
    | ~ spl3_13 ),
    inference(resolution,[],[f318,f53])).

fof(f53,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f318,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_9
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f306,f147])).

fof(f147,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f131,f86])).

fof(f86,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(resolution,[],[f75,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f75,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f68,f70])).

fof(f70,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f68,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f131,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f76,f54])).

fof(f54,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f76,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f69,f70,f70])).

fof(f69,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f306,plain,
    ( ~ v1_xboole_0(k4_xboole_0(sK1,sK1))
    | spl3_9
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f181,f210])).

fof(f210,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl3_13
  <=> u1_struct_0(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f181,plain,
    ( ~ v1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f179])).

fof(f287,plain,(
    ~ spl3_16 ),
    inference(avatar_contradiction_clause,[],[f286])).

fof(f286,plain,
    ( $false
    | ~ spl3_16 ),
    inference(resolution,[],[f278,f45])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f278,plain,
    ( v2_struct_0(sK0)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f276])).

fof(f276,plain,
    ( spl3_16
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f285,plain,(
    spl3_17 ),
    inference(avatar_contradiction_clause,[],[f284])).

fof(f284,plain,
    ( $false
    | spl3_17 ),
    inference(resolution,[],[f282,f51])).

fof(f51,plain,(
    v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f282,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | spl3_17 ),
    inference(avatar_component_clause,[],[f280])).

fof(f280,plain,
    ( spl3_17
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f283,plain,
    ( spl3_16
    | ~ spl3_14
    | ~ spl3_10
    | spl3_12
    | ~ spl3_1
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f272,f280,f78,f204,f191,f249,f276])).

fof(f204,plain,
    ( spl3_12
  <=> v1_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f272,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | v1_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f63,f49])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ v3_pre_topc(X1,X0)
      | v1_tops_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tex_2(X1,X0)
              & v3_pre_topc(X1,X0) )
           => v1_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tex_2)).

fof(f260,plain,(
    spl3_15 ),
    inference(avatar_contradiction_clause,[],[f259])).

fof(f259,plain,
    ( $false
    | spl3_15 ),
    inference(resolution,[],[f255,f47])).

fof(f47,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f255,plain,
    ( ~ v3_tdlat_3(sK0)
    | spl3_15 ),
    inference(avatar_component_clause,[],[f253])).

fof(f258,plain,(
    spl3_14 ),
    inference(avatar_contradiction_clause,[],[f257])).

fof(f257,plain,
    ( $false
    | spl3_14 ),
    inference(resolution,[],[f251,f46])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f251,plain,
    ( ~ v2_pre_topc(sK0)
    | spl3_14 ),
    inference(avatar_component_clause,[],[f249])).

fof(f256,plain,
    ( ~ spl3_14
    | ~ spl3_10
    | ~ spl3_15
    | spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f245,f82,f78,f253,f191,f249])).

fof(f245,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f64,f49])).

fof(f212,plain,
    ( ~ spl3_10
    | ~ spl3_8
    | ~ spl3_12
    | spl3_13
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f202,f195,f208,f204,f175,f191])).

fof(f195,plain,
    ( spl3_11
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f202,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ v1_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_11 ),
    inference(superposition,[],[f197,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

fof(f197,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f195])).

fof(f200,plain,(
    spl3_10 ),
    inference(avatar_contradiction_clause,[],[f199])).

fof(f199,plain,
    ( $false
    | spl3_10 ),
    inference(resolution,[],[f193,f48])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f193,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f191])).

fof(f198,plain,
    ( ~ spl3_10
    | spl3_11
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f187,f82,f195,f191])).

fof(f187,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f55,f49])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f184,plain,(
    spl3_8 ),
    inference(avatar_contradiction_clause,[],[f183])).

fof(f183,plain,
    ( $false
    | spl3_8 ),
    inference(resolution,[],[f177,f49])).

fof(f177,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f175])).

fof(f99,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f98])).

fof(f98,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f96,f52])).

fof(f52,plain,(
    v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f96,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f97,plain,
    ( ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f88,f94,f90])).

fof(f88,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f61,f49])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ~ v1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_subset_1)).

fof(f85,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f50,f82,f78])).

fof(f50,plain,
    ( v4_pre_topc(sK1,sK0)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:28:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (14092)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (14092)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f1333,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f85,f97,f99,f184,f198,f200,f212,f256,f258,f260,f283,f285,f287,f344,f353,f355,f918,f1322,f1330,f1332])).
% 0.21/0.46  fof(f1332,plain,(
% 0.21/0.46    ~spl3_10 | ~spl3_8 | spl3_2 | ~spl3_41),
% 0.21/0.46    inference(avatar_split_clause,[],[f1331,f930,f82,f175,f191])).
% 0.21/0.46  fof(f191,plain,(
% 0.21/0.46    spl3_10 <=> l1_pre_topc(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.46  fof(f175,plain,(
% 0.21/0.46    spl3_8 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.46  fof(f82,plain,(
% 0.21/0.46    spl3_2 <=> v4_pre_topc(sK1,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.46  fof(f930,plain,(
% 0.21/0.46    spl3_41 <=> v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.21/0.46  fof(f1331,plain,(
% 0.21/0.46    v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_41),
% 0.21/0.46    inference(resolution,[],[f931,f222])).
% 0.21/0.46  fof(f222,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v3_pre_topc(k4_xboole_0(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f220])).
% 0.21/0.46  fof(f220,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v3_pre_topc(k4_xboole_0(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.46    inference(superposition,[],[f60,f72])).
% 0.21/0.46  fof(f72,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f32])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f40])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.46    inference(nnf_transformation,[],[f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,axiom,(
% 0.21/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).
% 0.21/0.46  fof(f931,plain,(
% 0.21/0.46    v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~spl3_41),
% 0.21/0.46    inference(avatar_component_clause,[],[f930])).
% 0.21/0.46  fof(f1330,plain,(
% 0.21/0.46    ~spl3_14 | ~spl3_10 | ~spl3_15 | spl3_41 | ~spl3_34 | ~spl3_33),
% 0.21/0.46    inference(avatar_split_clause,[],[f920,f853,f857,f930,f253,f191,f249])).
% 0.21/0.46  fof(f249,plain,(
% 0.21/0.46    spl3_14 <=> v2_pre_topc(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.46  fof(f253,plain,(
% 0.21/0.46    spl3_15 <=> v3_tdlat_3(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.46  fof(f857,plain,(
% 0.21/0.46    spl3_34 <=> v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.21/0.46  fof(f853,plain,(
% 0.21/0.46    spl3_33 <=> m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.21/0.46  fof(f920,plain,(
% 0.21/0.46    ~v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl3_33),
% 0.21/0.46    inference(resolution,[],[f854,f64])).
% 0.21/0.46  fof(f64,plain,(
% 0.21/0.46    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | v3_pre_topc(X2,X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f44])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    ! [X0] : (((v3_tdlat_3(X0) | (~v3_pre_topc(sK2(X0),X0) & v4_pre_topc(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK2(X0),X0) & v4_pre_topc(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.46    inference(rectify,[],[f41])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.46    inference(nnf_transformation,[],[f30])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.46    inference(flattening,[],[f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,axiom,(
% 0.21/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_pre_topc(X1,X0)))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).
% 0.21/0.46  fof(f854,plain,(
% 0.21/0.46    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_33),
% 0.21/0.46    inference(avatar_component_clause,[],[f853])).
% 0.21/0.46  fof(f1322,plain,(
% 0.21/0.46    ~spl3_8 | ~spl3_10 | ~spl3_1 | spl3_34 | ~spl3_33),
% 0.21/0.46    inference(avatar_split_clause,[],[f1309,f853,f857,f78,f191,f175])).
% 0.21/0.46  fof(f78,plain,(
% 0.21/0.46    spl3_1 <=> v3_pre_topc(sK1,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.46  fof(f1309,plain,(
% 0.21/0.46    v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~v3_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_33),
% 0.21/0.46    inference(resolution,[],[f396,f854])).
% 0.21/0.46  fof(f396,plain,(
% 0.21/0.46    ( ! [X8,X9] : (~m1_subset_1(k4_xboole_0(u1_struct_0(X8),X9),k1_zfmisc_1(u1_struct_0(X8))) | v4_pre_topc(k4_xboole_0(u1_struct_0(X8),X9),X8) | ~v3_pre_topc(X9,X8) | ~l1_pre_topc(X8) | ~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))) )),
% 0.21/0.46    inference(superposition,[],[f60,f125])).
% 0.21/0.46  fof(f125,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f121])).
% 0.21/0.46  fof(f121,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.46    inference(superposition,[],[f73,f72])).
% 0.21/0.46  fof(f73,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f33])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,axiom,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.46  fof(f918,plain,(
% 0.21/0.46    spl3_33),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f917])).
% 0.21/0.46  fof(f917,plain,(
% 0.21/0.46    $false | spl3_33),
% 0.21/0.46    inference(resolution,[],[f908,f49])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.46    inference(cnf_transformation,[],[f38])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    (v1_subset_1(sK1,u1_struct_0(sK0)) & v3_tex_2(sK1,sK0) & (v4_pre_topc(sK1,sK0) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f37,f36])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (v1_subset_1(X1,u1_struct_0(sK0)) & v3_tex_2(X1,sK0) & (v4_pre_topc(X1,sK0) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ? [X1] : (v1_subset_1(X1,u1_struct_0(sK0)) & v3_tex_2(X1,sK0) & (v4_pre_topc(X1,sK0) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (v1_subset_1(sK1,u1_struct_0(sK0)) & v3_tex_2(sK1,sK0) & (v4_pre_topc(sK1,sK0) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f18])).
% 0.21/0.46  fof(f18,negated_conjecture,(
% 0.21/0.46    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)))))),
% 0.21/0.46    inference(negated_conjecture,[],[f17])).
% 0.21/0.46  fof(f17,conjecture,(
% 0.21/0.46    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_tex_2)).
% 0.21/0.46  fof(f908,plain,(
% 0.21/0.46    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_33),
% 0.21/0.46    inference(resolution,[],[f855,f109])).
% 0.21/0.46  fof(f109,plain,(
% 0.21/0.46    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f108])).
% 0.21/0.46  fof(f108,plain,(
% 0.21/0.46    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.46    inference(superposition,[],[f71,f72])).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,axiom,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.46  fof(f855,plain,(
% 0.21/0.46    ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_33),
% 0.21/0.46    inference(avatar_component_clause,[],[f853])).
% 0.21/0.46  fof(f355,plain,(
% 0.21/0.46    ~spl3_8 | ~spl3_9 | spl3_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f354,f169,f179,f175])).
% 0.21/0.46  fof(f179,plain,(
% 0.21/0.46    spl3_9 <=> v1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.46  fof(f169,plain,(
% 0.21/0.46    spl3_7 <=> v1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.46  fof(f354,plain,(
% 0.21/0.46    ~v1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_7),
% 0.21/0.46    inference(superposition,[],[f171,f72])).
% 0.21/0.46  fof(f171,plain,(
% 0.21/0.46    ~v1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1)) | spl3_7),
% 0.21/0.46    inference(avatar_component_clause,[],[f169])).
% 0.21/0.46  fof(f353,plain,(
% 0.21/0.46    spl3_3 | ~spl3_4 | ~spl3_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f350,f169,f94,f90])).
% 0.21/0.46  fof(f90,plain,(
% 0.21/0.46    spl3_3 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.46  fof(f94,plain,(
% 0.21/0.46    spl3_4 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.46  fof(f350,plain,(
% 0.21/0.46    ~v1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1)) | ~v1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.46    inference(resolution,[],[f49,f74])).
% 0.21/0.46  fof(f74,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(k3_subset_1(X0,X1)) | ~v1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f35])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ! [X0,X1] : (~v1_xboole_0(k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.46    inference(flattening,[],[f34])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ! [X0,X1] : (~v1_xboole_0(k3_subset_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,axiom,(
% 0.21/0.46    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(X0)) & v1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k3_subset_1(X0,X1)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tex_2)).
% 0.21/0.46  fof(f344,plain,(
% 0.21/0.46    spl3_9 | ~spl3_13),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f343])).
% 0.21/0.46  fof(f343,plain,(
% 0.21/0.46    $false | (spl3_9 | ~spl3_13)),
% 0.21/0.46    inference(resolution,[],[f318,f53])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    v1_xboole_0(k1_xboole_0)),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    v1_xboole_0(k1_xboole_0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.46  fof(f318,plain,(
% 0.21/0.46    ~v1_xboole_0(k1_xboole_0) | (spl3_9 | ~spl3_13)),
% 0.21/0.46    inference(forward_demodulation,[],[f306,f147])).
% 0.21/0.46  fof(f147,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.46    inference(forward_demodulation,[],[f131,f86])).
% 0.21/0.46  fof(f86,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 0.21/0.46    inference(resolution,[],[f75,f62])).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f68,f70])).
% 0.21/0.46  fof(f70,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.46  fof(f68,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.46  fof(f131,plain,(
% 0.21/0.46    ( ! [X0] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0)) )),
% 0.21/0.46    inference(superposition,[],[f76,f54])).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.46  fof(f76,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f69,f70,f70])).
% 0.21/0.46  fof(f69,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.46  fof(f306,plain,(
% 0.21/0.46    ~v1_xboole_0(k4_xboole_0(sK1,sK1)) | (spl3_9 | ~spl3_13)),
% 0.21/0.46    inference(backward_demodulation,[],[f181,f210])).
% 0.21/0.46  fof(f210,plain,(
% 0.21/0.46    u1_struct_0(sK0) = sK1 | ~spl3_13),
% 0.21/0.46    inference(avatar_component_clause,[],[f208])).
% 0.21/0.46  fof(f208,plain,(
% 0.21/0.46    spl3_13 <=> u1_struct_0(sK0) = sK1),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.46  fof(f181,plain,(
% 0.21/0.46    ~v1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1)) | spl3_9),
% 0.21/0.46    inference(avatar_component_clause,[],[f179])).
% 0.21/0.46  fof(f287,plain,(
% 0.21/0.46    ~spl3_16),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f286])).
% 0.21/0.46  fof(f286,plain,(
% 0.21/0.46    $false | ~spl3_16),
% 0.21/0.46    inference(resolution,[],[f278,f45])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    ~v2_struct_0(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f38])).
% 0.21/0.46  fof(f278,plain,(
% 0.21/0.46    v2_struct_0(sK0) | ~spl3_16),
% 0.21/0.46    inference(avatar_component_clause,[],[f276])).
% 0.21/0.46  fof(f276,plain,(
% 0.21/0.46    spl3_16 <=> v2_struct_0(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.46  fof(f285,plain,(
% 0.21/0.46    spl3_17),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f284])).
% 0.21/0.46  fof(f284,plain,(
% 0.21/0.46    $false | spl3_17),
% 0.21/0.46    inference(resolution,[],[f282,f51])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    v3_tex_2(sK1,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f38])).
% 0.21/0.46  fof(f282,plain,(
% 0.21/0.46    ~v3_tex_2(sK1,sK0) | spl3_17),
% 0.21/0.46    inference(avatar_component_clause,[],[f280])).
% 0.21/0.46  fof(f280,plain,(
% 0.21/0.46    spl3_17 <=> v3_tex_2(sK1,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.46  fof(f283,plain,(
% 0.21/0.46    spl3_16 | ~spl3_14 | ~spl3_10 | spl3_12 | ~spl3_1 | ~spl3_17),
% 0.21/0.46    inference(avatar_split_clause,[],[f272,f280,f78,f204,f191,f249,f276])).
% 0.21/0.46  fof(f204,plain,(
% 0.21/0.46    spl3_12 <=> v1_tops_1(sK1,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.46  fof(f272,plain,(
% 0.21/0.46    ~v3_tex_2(sK1,sK0) | ~v3_pre_topc(sK1,sK0) | v1_tops_1(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.46    inference(resolution,[],[f63,f49])).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | v1_tops_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) | (~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f16])).
% 0.21/0.46  fof(f16,axiom,(
% 0.21/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tex_2(X1,X0) & v3_pre_topc(X1,X0)) => v1_tops_1(X1,X0))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tex_2)).
% 0.21/0.46  fof(f260,plain,(
% 0.21/0.46    spl3_15),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f259])).
% 0.21/0.46  fof(f259,plain,(
% 0.21/0.46    $false | spl3_15),
% 0.21/0.46    inference(resolution,[],[f255,f47])).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    v3_tdlat_3(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f38])).
% 0.21/0.46  fof(f255,plain,(
% 0.21/0.46    ~v3_tdlat_3(sK0) | spl3_15),
% 0.21/0.46    inference(avatar_component_clause,[],[f253])).
% 0.21/0.46  fof(f258,plain,(
% 0.21/0.46    spl3_14),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f257])).
% 0.21/0.46  fof(f257,plain,(
% 0.21/0.46    $false | spl3_14),
% 0.21/0.46    inference(resolution,[],[f251,f46])).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    v2_pre_topc(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f38])).
% 0.21/0.46  fof(f251,plain,(
% 0.21/0.46    ~v2_pre_topc(sK0) | spl3_14),
% 0.21/0.46    inference(avatar_component_clause,[],[f249])).
% 0.21/0.46  fof(f256,plain,(
% 0.21/0.46    ~spl3_14 | ~spl3_10 | ~spl3_15 | spl3_1 | ~spl3_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f245,f82,f78,f253,f191,f249])).
% 0.21/0.46  fof(f245,plain,(
% 0.21/0.46    ~v4_pre_topc(sK1,sK0) | v3_pre_topc(sK1,sK0) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.46    inference(resolution,[],[f64,f49])).
% 0.21/0.46  fof(f212,plain,(
% 0.21/0.46    ~spl3_10 | ~spl3_8 | ~spl3_12 | spl3_13 | ~spl3_11),
% 0.21/0.46    inference(avatar_split_clause,[],[f202,f195,f208,f204,f175,f191])).
% 0.21/0.46  fof(f195,plain,(
% 0.21/0.46    spl3_11 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.46  fof(f202,plain,(
% 0.21/0.46    u1_struct_0(sK0) = sK1 | ~v1_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_11),
% 0.21/0.46    inference(superposition,[],[f197,f57])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    ( ! [X0,X1] : (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f39])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.46    inference(nnf_transformation,[],[f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,axiom,(
% 0.21/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).
% 0.21/0.46  fof(f197,plain,(
% 0.21/0.46    sK1 = k2_pre_topc(sK0,sK1) | ~spl3_11),
% 0.21/0.46    inference(avatar_component_clause,[],[f195])).
% 0.21/0.46  fof(f200,plain,(
% 0.21/0.46    spl3_10),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f199])).
% 0.21/0.46  fof(f199,plain,(
% 0.21/0.46    $false | spl3_10),
% 0.21/0.46    inference(resolution,[],[f193,f48])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    l1_pre_topc(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f38])).
% 0.21/0.46  fof(f193,plain,(
% 0.21/0.46    ~l1_pre_topc(sK0) | spl3_10),
% 0.21/0.46    inference(avatar_component_clause,[],[f191])).
% 0.21/0.46  fof(f198,plain,(
% 0.21/0.46    ~spl3_10 | spl3_11 | ~spl3_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f187,f82,f195,f191])).
% 0.21/0.46  fof(f187,plain,(
% 0.21/0.46    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 0.21/0.46    inference(resolution,[],[f55,f49])).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.46    inference(flattening,[],[f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,axiom,(
% 0.21/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.21/0.46  fof(f184,plain,(
% 0.21/0.46    spl3_8),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f183])).
% 0.21/0.46  fof(f183,plain,(
% 0.21/0.46    $false | spl3_8),
% 0.21/0.46    inference(resolution,[],[f177,f49])).
% 0.21/0.46  fof(f177,plain,(
% 0.21/0.46    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_8),
% 0.21/0.46    inference(avatar_component_clause,[],[f175])).
% 0.21/0.46  fof(f99,plain,(
% 0.21/0.46    spl3_4),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f98])).
% 0.21/0.46  fof(f98,plain,(
% 0.21/0.46    $false | spl3_4),
% 0.21/0.46    inference(resolution,[],[f96,f52])).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.46    inference(cnf_transformation,[],[f38])).
% 0.21/0.46  fof(f96,plain,(
% 0.21/0.46    ~v1_subset_1(sK1,u1_struct_0(sK0)) | spl3_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f94])).
% 0.21/0.46  fof(f97,plain,(
% 0.21/0.46    ~spl3_3 | ~spl3_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f88,f94,f90])).
% 0.21/0.46  fof(f88,plain,(
% 0.21/0.46    ~v1_subset_1(sK1,u1_struct_0(sK0)) | ~v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.46    inference(resolution,[],[f61,f49])).
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,axiom,(
% 0.21/0.46    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~v1_subset_1(X1,X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_subset_1)).
% 0.21/0.46  fof(f85,plain,(
% 0.21/0.46    spl3_1 | spl3_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f50,f82,f78])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    v4_pre_topc(sK1,sK0) | v3_pre_topc(sK1,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f38])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (14092)------------------------------
% 0.21/0.46  % (14092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (14092)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (14092)Memory used [KB]: 6652
% 0.21/0.46  % (14092)Time elapsed: 0.058 s
% 0.21/0.46  % (14092)------------------------------
% 0.21/0.46  % (14092)------------------------------
% 0.21/0.46  % (14085)Success in time 0.104 s
%------------------------------------------------------------------------------
