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
% DateTime   : Thu Dec  3 13:21:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :  221 ( 990 expanded)
%              Number of leaves         :   42 ( 315 expanded)
%              Depth                    :   16
%              Number of atoms          :  910 (6160 expanded)
%              Number of equality atoms :   74 ( 231 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1546,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f187,f190,f365,f367,f376,f383,f390,f421,f423,f481,f483,f569,f668,f673,f704,f783,f791,f1014,f1024,f1038,f1054,f1276,f1323,f1543,f1545])).

fof(f1545,plain,(
    spl5_102 ),
    inference(avatar_contradiction_clause,[],[f1544])).

fof(f1544,plain,
    ( $false
    | spl5_102 ),
    inference(subsumption_resolution,[],[f428,f1542])).

fof(f1542,plain,
    ( ~ m1_subset_1(sK1,u1_pre_topc(sK0))
    | spl5_102 ),
    inference(avatar_component_clause,[],[f1541])).

fof(f1541,plain,
    ( spl5_102
  <=> m1_subset_1(sK1,u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_102])])).

fof(f428,plain,(
    m1_subset_1(sK1,u1_pre_topc(sK0)) ),
    inference(backward_demodulation,[],[f146,f193])).

fof(f193,plain,(
    k9_setfam_1(u1_struct_0(sK0)) = u1_pre_topc(sK0) ),
    inference(global_subsumption,[],[f96,f191])).

fof(f191,plain,
    ( k9_setfam_1(u1_struct_0(sK0)) = u1_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f95,f110])).

fof(f110,plain,(
    ! [X0] :
      ( ~ v1_tdlat_3(X0)
      | u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | u1_pre_topc(X0) != k9_setfam_1(u1_struct_0(X0)) )
        & ( u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tdlat_3)).

fof(f95,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,
    ( ( v1_subset_1(sK1,u1_struct_0(sK0))
      | ~ v3_tex_2(sK1,sK0) )
    & ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
      | v3_tex_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v1_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f76,f78,f77])).

fof(f77,plain,
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

fof(f78,plain,
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

fof(f76,plain,(
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
    inference(flattening,[],[f75])).

% (13026)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f75,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f31])).

fof(f31,conjecture,(
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

fof(f96,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f79])).

fof(f146,plain,(
    m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0))) ),
    inference(definition_unfolding,[],[f97,f103])).

fof(f103,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f97,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f79])).

fof(f1543,plain,
    ( spl5_3
    | ~ spl5_67
    | ~ spl5_66
    | ~ spl5_102
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f1516,f239,f1541,f987,f990,f213])).

fof(f213,plain,
    ( spl5_3
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f990,plain,
    ( spl5_67
  <=> v1_borsuk_1(sK3(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).

fof(f987,plain,
    ( spl5_66
  <=> m1_pre_topc(sK3(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_66])])).

fof(f239,plain,
    ( spl5_8
  <=> sK1 = u1_struct_0(sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f1516,plain,
    ( ~ m1_subset_1(sK1,u1_pre_topc(sK0))
    | ~ m1_pre_topc(sK3(sK0,sK1),sK0)
    | ~ v1_borsuk_1(sK3(sK0,sK1),sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ spl5_8 ),
    inference(superposition,[],[f468,f240])).

fof(f240,plain,
    ( sK1 = u1_struct_0(sK3(sK0,sK1))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f239])).

fof(f468,plain,(
    ! [X12] :
      ( ~ m1_subset_1(u1_struct_0(X12),u1_pre_topc(sK0))
      | ~ m1_pre_topc(X12,sK0)
      | ~ v1_borsuk_1(X12,sK0)
      | v4_pre_topc(u1_struct_0(X12),sK0) ) ),
    inference(global_subsumption,[],[f96,f94,f444])).

fof(f444,plain,(
    ! [X12] :
      ( ~ m1_subset_1(u1_struct_0(X12),u1_pre_topc(sK0))
      | ~ m1_pre_topc(X12,sK0)
      | ~ v1_borsuk_1(X12,sK0)
      | v4_pre_topc(u1_struct_0(X12),sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(superposition,[],[f180,f193])).

fof(f180,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k9_setfam_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | v4_pre_topc(u1_struct_0(X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f178])).

fof(f178,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k9_setfam_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f170])).

fof(f170,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f136,f103])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
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
    inference(flattening,[],[f90])).

fof(f90,plain,(
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
    inference(nnf_transformation,[],[f67])).

fof(f67,plain,(
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
    inference(flattening,[],[f66])).

fof(f66,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tsep_1)).

fof(f94,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f79])).

fof(f1323,plain,(
    spl5_41 ),
    inference(avatar_contradiction_clause,[],[f1322])).

fof(f1322,plain,
    ( $false
    | spl5_41 ),
    inference(subsumption_resolution,[],[f428,f1321])).

fof(f1321,plain,
    ( ~ m1_subset_1(sK1,u1_pre_topc(sK0))
    | spl5_41 ),
    inference(forward_demodulation,[],[f671,f193])).

fof(f671,plain,
    ( ~ m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0)))
    | spl5_41 ),
    inference(avatar_component_clause,[],[f670])).

fof(f670,plain,
    ( spl5_41
  <=> m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f1276,plain,
    ( spl5_21
    | ~ spl5_16
    | spl5_7
    | ~ spl5_41
    | spl5_66 ),
    inference(avatar_split_clause,[],[f1273,f987,f670,f236,f297,f315])).

fof(f315,plain,
    ( spl5_21
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f297,plain,
    ( spl5_16
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f236,plain,
    ( spl5_7
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f1273,plain,
    ( ~ m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_66 ),
    inference(resolution,[],[f988,f163])).

fof(f163,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK3(X0,X1),X0)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f131,f103])).

fof(f131,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK3(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK3(X0,X1)) = X1
            & m1_pre_topc(sK3(X0,X1),X0)
            & v1_pre_topc(sK3(X0,X1))
            & ~ v2_struct_0(sK3(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f63,f84])).

fof(f84,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK3(X0,X1)) = X1
        & m1_pre_topc(sK3(X0,X1),X0)
        & v1_pre_topc(sK3(X0,X1))
        & ~ v2_struct_0(sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
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

fof(f988,plain,
    ( ~ m1_pre_topc(sK3(sK0,sK1),sK0)
    | spl5_66 ),
    inference(avatar_component_clause,[],[f987])).

fof(f1054,plain,
    ( ~ spl5_6
    | spl5_1
    | ~ spl5_35 ),
    inference(avatar_split_clause,[],[f867,f388,f182,f228])).

fof(f228,plain,
    ( spl5_6
  <=> v1_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f182,plain,
    ( spl5_1
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f388,plain,
    ( spl5_35
  <=> u1_pre_topc(sK0) = k9_setfam_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f867,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ v1_tops_1(sK1,sK0)
    | ~ spl5_35 ),
    inference(resolution,[],[f846,f712])).

fof(f712,plain,
    ( m1_subset_1(sK1,k9_setfam_1(sK1))
    | ~ spl5_35 ),
    inference(backward_demodulation,[],[f428,f389])).

fof(f389,plain,
    ( u1_pre_topc(sK0) = k9_setfam_1(sK1)
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f388])).

fof(f846,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k9_setfam_1(sK1))
        | v3_tex_2(X4,sK0)
        | ~ v1_tops_1(X4,sK0) )
    | ~ spl5_35 ),
    inference(forward_demodulation,[],[f459,f389])).

fof(f459,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_pre_topc(sK0))
      | v3_tex_2(X4,sK0)
      | ~ v1_tops_1(X4,sK0) ) ),
    inference(global_subsumption,[],[f96,f94,f93,f458,f434])).

fof(f434,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_pre_topc(sK0))
      | ~ v2_tex_2(X4,sK0)
      | ~ v1_tops_1(X4,sK0)
      | v3_tex_2(X4,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f158,f193])).

fof(f158,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ v1_tops_1(X1,X0)
      | v3_tex_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f122,f103])).

fof(f122,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
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

fof(f458,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_pre_topc(sK0))
      | v2_tex_2(X3,sK0) ) ),
    inference(global_subsumption,[],[f96,f94,f93,f95,f433])).

fof(f433,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_pre_topc(sK0))
      | v2_tex_2(X3,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_tdlat_3(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f157,f193])).

fof(f157,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f121,f103])).

fof(f121,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

fof(f93,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f79])).

fof(f1038,plain,
    ( ~ spl5_7
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f1037,f182,f236])).

fof(f1037,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | ~ v1_xboole_0(sK1) ),
    inference(global_subsumption,[],[f1035])).

fof(f1035,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | ~ v1_xboole_0(sK1) ),
    inference(global_subsumption,[],[f96,f94,f93,f200])).

fof(f200,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | ~ v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f146,f160])).

fof(f160,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f124,f103])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

fof(f1024,plain,
    ( ~ spl5_7
    | ~ spl5_42
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f731,f337,f734,f236])).

fof(f734,plain,
    ( spl5_42
  <=> v1_subset_1(sK2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f337,plain,
    ( spl5_27
  <=> m1_subset_1(sK2(sK0),k9_setfam_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f731,plain,
    ( ~ v1_subset_1(sK2(sK0),sK1)
    | ~ v1_xboole_0(sK1)
    | ~ spl5_27 ),
    inference(resolution,[],[f338,f156])).

fof(f156,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(X0))
      | ~ v1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f118,f103])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_subset_1)).

fof(f338,plain,
    ( m1_subset_1(sK2(sK0),k9_setfam_1(sK1))
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f337])).

fof(f1014,plain,
    ( spl5_21
    | ~ spl5_17
    | ~ spl5_22
    | ~ spl5_16
    | ~ spl5_66
    | spl5_67 ),
    inference(avatar_split_clause,[],[f1013,f990,f987,f297,f318,f300,f315])).

fof(f300,plain,
    ( spl5_17
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f318,plain,
    ( spl5_22
  <=> v1_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f1013,plain,
    ( ~ m1_pre_topc(sK3(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_67 ),
    inference(resolution,[],[f991,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( v1_borsuk_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tdlat_3(X1)
            & v1_borsuk_1(X1,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tdlat_3(X1)
            & v1_borsuk_1(X1,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
            & v1_borsuk_1(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f20,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_tdlat_3)).

fof(f991,plain,
    ( ~ v1_borsuk_1(sK3(sK0,sK1),sK0)
    | spl5_67 ),
    inference(avatar_component_clause,[],[f990])).

fof(f791,plain,
    ( spl5_42
    | spl5_44
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f786,f337,f742,f734])).

fof(f742,plain,
    ( spl5_44
  <=> sK1 = sK2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f786,plain,
    ( sK1 = sK2(sK0)
    | v1_subset_1(sK2(sK0),sK1)
    | ~ spl5_27 ),
    inference(resolution,[],[f338,f172])).

fof(f172,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(definition_unfolding,[],[f142,f103])).

fof(f142,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f783,plain,
    ( spl5_21
    | ~ spl5_17
    | ~ spl5_16
    | spl5_3
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f781,f742,f213,f297,f300,f315])).

fof(f781,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_44 ),
    inference(superposition,[],[f128,f743])).

fof(f743,plain,
    ( sK1 = sK2(sK0)
    | ~ spl5_44 ),
    inference(avatar_component_clause,[],[f742])).

fof(f128,plain,(
    ! [X0] :
      ( v4_pre_topc(sK2(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( ( v4_pre_topc(sK2(X0),X0)
        & v3_pre_topc(sK2(X0),X0)
        & ~ v1_xboole_0(sK2(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f61,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v4_pre_topc(sK2(X0),X0)
        & v3_pre_topc(sK2(X0),X0)
        & ~ v1_xboole_0(sK2(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_tops_1)).

fof(f704,plain,
    ( spl5_21
    | ~ spl5_17
    | ~ spl5_16
    | spl5_27
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f687,f254,f337,f297,f300,f315])).

fof(f254,plain,
    ( spl5_11
  <=> u1_struct_0(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f687,plain,
    ( m1_subset_1(sK2(sK0),k9_setfam_1(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_11 ),
    inference(superposition,[],[f161,f255])).

fof(f255,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f254])).

fof(f161,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f125,f103])).

fof(f125,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f673,plain,
    ( ~ spl5_16
    | ~ spl5_41
    | spl5_6
    | ~ spl5_11
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f572,f216,f254,f228,f670,f297])).

fof(f216,plain,
    ( spl5_4
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f572,plain,
    ( u1_struct_0(sK0) != sK1
    | v1_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_4 ),
    inference(superposition,[],[f154,f220])).

fof(f220,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f216])).

fof(f154,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) != k2_pre_topc(X0,X1)
      | v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f117,f103])).

fof(f117,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | u1_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

fof(f668,plain,
    ( ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f667])).

fof(f667,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f623,f665])).

fof(f665,plain,
    ( ~ v1_subset_1(sK1,sK1)
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(resolution,[],[f657,f179])).

fof(f179,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(X1))
      | ~ v1_subset_1(X1,X1) ) ),
    inference(equality_resolution,[],[f173])).

fof(f173,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k9_setfam_1(X0)) ) ),
    inference(definition_unfolding,[],[f141,f103])).

fof(f141,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f657,plain,
    ( m1_subset_1(sK1,k9_setfam_1(sK1))
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(backward_demodulation,[],[f428,f618])).

fof(f618,plain,
    ( u1_pre_topc(sK0) = k9_setfam_1(sK1)
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(backward_demodulation,[],[f193,f617])).

fof(f617,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f226,f220])).

fof(f226,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f225])).

fof(f225,plain,
    ( spl5_5
  <=> u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f623,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(backward_demodulation,[],[f186,f617])).

fof(f186,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl5_2
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f569,plain,
    ( spl5_4
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f568,f213,f216])).

fof(f568,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(global_subsumption,[],[f219])).

fof(f219,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(global_subsumption,[],[f96,f195])).

fof(f195,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f146,f153])).

fof(f153,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f114,f103])).

fof(f114,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f483,plain,
    ( spl5_6
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f482,f182,f228])).

fof(f482,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(global_subsumption,[],[f391])).

fof(f391,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(global_subsumption,[],[f252,f96,f94,f93,f199])).

fof(f199,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | v1_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f146,f159])).

fof(f159,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ v3_pre_topc(X1,X0)
      | v1_tops_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f123,f103])).

fof(f123,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tex_2(X1,X0)
              & v3_pre_topc(X1,X0) )
           => v1_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tex_2)).

fof(f252,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(global_subsumption,[],[f94,f95,f96,f204])).

fof(f204,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f146,f167])).

fof(f167,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X0)))
      | v3_pre_topc(X2,X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f133,f103])).

fof(f133,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK4(X0),X0)
            & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f87,f88])).

fof(f88,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK4(X0),X0)
        & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f87,plain,(
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
    inference(rectify,[],[f86])).

fof(f86,plain,(
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
    inference(nnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).

fof(f481,plain,
    ( spl5_2
    | spl5_11 ),
    inference(avatar_split_clause,[],[f414,f254,f185])).

fof(f414,plain,
    ( u1_struct_0(sK0) = sK1
    | v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f146,f172])).

fof(f423,plain,
    ( spl5_7
    | spl5_8 ),
    inference(avatar_split_clause,[],[f422,f239,f236])).

fof(f422,plain,
    ( sK1 = u1_struct_0(sK3(sK0,sK1))
    | v1_xboole_0(sK1) ),
    inference(global_subsumption,[],[f96,f93,f408])).

fof(f408,plain,
    ( sK1 = u1_struct_0(sK3(sK0,sK1))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f146,f162])).

fof(f162,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | u1_struct_0(sK3(X0,X1)) = X1
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f132,f103])).

fof(f132,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK3(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f421,plain,
    ( spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f420,f228,f225])).

fof(f420,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(global_subsumption,[],[f96,f403])).

fof(f403,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f146,f155])).

fof(f155,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f116,f103])).

fof(f116,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f390,plain,
    ( ~ spl5_16
    | spl5_35
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f386,f254,f388,f297])).

fof(f386,plain,
    ( u1_pre_topc(sK0) = k9_setfam_1(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f384,f255])).

fof(f384,plain,
    ( k9_setfam_1(u1_struct_0(sK0)) = u1_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f95,f110])).

fof(f383,plain,(
    spl5_22 ),
    inference(avatar_contradiction_clause,[],[f382])).

fof(f382,plain,
    ( $false
    | spl5_22 ),
    inference(subsumption_resolution,[],[f95,f319])).

fof(f319,plain,
    ( ~ v1_tdlat_3(sK0)
    | spl5_22 ),
    inference(avatar_component_clause,[],[f318])).

fof(f376,plain,(
    ~ spl5_21 ),
    inference(avatar_contradiction_clause,[],[f375])).

fof(f375,plain,
    ( $false
    | ~ spl5_21 ),
    inference(subsumption_resolution,[],[f93,f316])).

fof(f316,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f315])).

fof(f367,plain,(
    spl5_17 ),
    inference(avatar_contradiction_clause,[],[f366])).

fof(f366,plain,
    ( $false
    | spl5_17 ),
    inference(subsumption_resolution,[],[f94,f301])).

fof(f301,plain,
    ( ~ v2_pre_topc(sK0)
    | spl5_17 ),
    inference(avatar_component_clause,[],[f300])).

fof(f365,plain,(
    spl5_16 ),
    inference(avatar_contradiction_clause,[],[f364])).

fof(f364,plain,
    ( $false
    | spl5_16 ),
    inference(subsumption_resolution,[],[f96,f298])).

fof(f298,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_16 ),
    inference(avatar_component_clause,[],[f297])).

fof(f190,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f98,f185,f182])).

fof(f98,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f79])).

fof(f187,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f99,f185,f182])).

fof(f99,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f79])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:16:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (13015)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (13011)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (13007)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (13015)Refutation not found, incomplete strategy% (13015)------------------------------
% 0.21/0.52  % (13015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (13005)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (13015)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (13015)Memory used [KB]: 10618
% 0.21/0.52  % (13015)Time elapsed: 0.101 s
% 0.21/0.52  % (13015)------------------------------
% 0.21/0.52  % (13015)------------------------------
% 0.21/0.53  % (13028)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (13005)Refutation not found, incomplete strategy% (13005)------------------------------
% 0.21/0.53  % (13005)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (13005)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (13005)Memory used [KB]: 1663
% 0.21/0.53  % (13005)Time elapsed: 0.115 s
% 0.21/0.53  % (13005)------------------------------
% 0.21/0.53  % (13005)------------------------------
% 0.21/0.53  % (13020)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (13031)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (13027)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (13034)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (13023)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (13006)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (13021)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (13009)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (13012)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (13032)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (13008)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (13029)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (13016)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (13010)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.55  % (13030)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (13025)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (13013)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (13019)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.56  % (13017)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (13022)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.56  % (13033)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.56  % (13022)Refutation not found, incomplete strategy% (13022)------------------------------
% 0.21/0.56  % (13022)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (13022)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (13022)Memory used [KB]: 10618
% 0.21/0.56  % (13022)Time elapsed: 0.147 s
% 0.21/0.56  % (13022)------------------------------
% 0.21/0.56  % (13022)------------------------------
% 0.21/0.56  % (13027)Refutation not found, incomplete strategy% (13027)------------------------------
% 0.21/0.56  % (13027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (13027)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (13027)Memory used [KB]: 10874
% 0.21/0.56  % (13027)Time elapsed: 0.154 s
% 0.21/0.56  % (13027)------------------------------
% 0.21/0.56  % (13027)------------------------------
% 0.21/0.56  % (13014)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.56  % (13024)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.57  % (13009)Refutation not found, incomplete strategy% (13009)------------------------------
% 0.21/0.57  % (13009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (13009)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (13009)Memory used [KB]: 6396
% 0.21/0.57  % (13009)Time elapsed: 0.155 s
% 0.21/0.57  % (13009)------------------------------
% 0.21/0.57  % (13009)------------------------------
% 0.21/0.57  % (13007)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f1546,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(avatar_sat_refutation,[],[f187,f190,f365,f367,f376,f383,f390,f421,f423,f481,f483,f569,f668,f673,f704,f783,f791,f1014,f1024,f1038,f1054,f1276,f1323,f1543,f1545])).
% 0.21/0.57  fof(f1545,plain,(
% 0.21/0.57    spl5_102),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f1544])).
% 0.21/0.57  fof(f1544,plain,(
% 0.21/0.57    $false | spl5_102),
% 0.21/0.57    inference(subsumption_resolution,[],[f428,f1542])).
% 0.21/0.57  fof(f1542,plain,(
% 0.21/0.57    ~m1_subset_1(sK1,u1_pre_topc(sK0)) | spl5_102),
% 0.21/0.57    inference(avatar_component_clause,[],[f1541])).
% 0.21/0.57  fof(f1541,plain,(
% 0.21/0.57    spl5_102 <=> m1_subset_1(sK1,u1_pre_topc(sK0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_102])])).
% 0.21/0.57  fof(f428,plain,(
% 0.21/0.57    m1_subset_1(sK1,u1_pre_topc(sK0))),
% 0.21/0.57    inference(backward_demodulation,[],[f146,f193])).
% 0.21/0.57  fof(f193,plain,(
% 0.21/0.57    k9_setfam_1(u1_struct_0(sK0)) = u1_pre_topc(sK0)),
% 0.21/0.57    inference(global_subsumption,[],[f96,f191])).
% 0.21/0.57  fof(f191,plain,(
% 0.21/0.57    k9_setfam_1(u1_struct_0(sK0)) = u1_pre_topc(sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.57    inference(resolution,[],[f95,f110])).
% 0.21/0.57  fof(f110,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_tdlat_3(X0) | u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f80])).
% 0.21/0.57  fof(f80,plain,(
% 0.21/0.57    ! [X0] : (((v1_tdlat_3(X0) | u1_pre_topc(X0) != k9_setfam_1(u1_struct_0(X0))) & (u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.57    inference(nnf_transformation,[],[f43])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    ! [X0] : ((v1_tdlat_3(X0) <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f21])).
% 0.21/0.57  fof(f21,axiom,(
% 0.21/0.57    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tdlat_3)).
% 0.21/0.57  fof(f95,plain,(
% 0.21/0.57    v1_tdlat_3(sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f79])).
% 0.21/0.57  fof(f79,plain,(
% 0.21/0.57    ((v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)) & (~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f76,f78,f77])).
% 0.21/0.57  fof(f77,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((v1_subset_1(X1,u1_struct_0(sK0)) | ~v3_tex_2(X1,sK0)) & (~v1_subset_1(X1,u1_struct_0(sK0)) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f78,plain,(
% 0.21/0.57    ? [X1] : ((v1_subset_1(X1,u1_struct_0(sK0)) | ~v3_tex_2(X1,sK0)) & (~v1_subset_1(X1,u1_struct_0(sK0)) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)) & (~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f76,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.57    inference(flattening,[],[f75])).
% 0.21/0.57  % (13026)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.57  fof(f75,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : (((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.57    inference(nnf_transformation,[],[f36])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.57    inference(flattening,[],[f35])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f32])).
% 0.21/0.57  fof(f32,negated_conjecture,(
% 0.21/0.57    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.21/0.57    inference(negated_conjecture,[],[f31])).
% 0.21/0.57  fof(f31,conjecture,(
% 0.21/0.57    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tex_2)).
% 0.21/0.57  fof(f96,plain,(
% 0.21/0.57    l1_pre_topc(sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f79])).
% 0.21/0.57  fof(f146,plain,(
% 0.21/0.57    m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0)))),
% 0.21/0.57    inference(definition_unfolding,[],[f97,f103])).
% 0.21/0.57  fof(f103,plain,(
% 0.21/0.57    ( ! [X0] : (k1_zfmisc_1(X0) = k9_setfam_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f12])).
% 0.21/0.57  fof(f12,axiom,(
% 0.21/0.57    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).
% 0.21/0.57  fof(f97,plain,(
% 0.21/0.57    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.57    inference(cnf_transformation,[],[f79])).
% 0.21/0.57  fof(f1543,plain,(
% 0.21/0.57    spl5_3 | ~spl5_67 | ~spl5_66 | ~spl5_102 | ~spl5_8),
% 0.21/0.57    inference(avatar_split_clause,[],[f1516,f239,f1541,f987,f990,f213])).
% 0.21/0.57  fof(f213,plain,(
% 0.21/0.57    spl5_3 <=> v4_pre_topc(sK1,sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.57  fof(f990,plain,(
% 0.21/0.57    spl5_67 <=> v1_borsuk_1(sK3(sK0,sK1),sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).
% 0.21/0.57  fof(f987,plain,(
% 0.21/0.57    spl5_66 <=> m1_pre_topc(sK3(sK0,sK1),sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_66])])).
% 0.21/0.57  fof(f239,plain,(
% 0.21/0.57    spl5_8 <=> sK1 = u1_struct_0(sK3(sK0,sK1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.57  fof(f1516,plain,(
% 0.21/0.57    ~m1_subset_1(sK1,u1_pre_topc(sK0)) | ~m1_pre_topc(sK3(sK0,sK1),sK0) | ~v1_borsuk_1(sK3(sK0,sK1),sK0) | v4_pre_topc(sK1,sK0) | ~spl5_8),
% 0.21/0.57    inference(superposition,[],[f468,f240])).
% 0.21/0.57  fof(f240,plain,(
% 0.21/0.57    sK1 = u1_struct_0(sK3(sK0,sK1)) | ~spl5_8),
% 0.21/0.57    inference(avatar_component_clause,[],[f239])).
% 0.21/0.57  fof(f468,plain,(
% 0.21/0.57    ( ! [X12] : (~m1_subset_1(u1_struct_0(X12),u1_pre_topc(sK0)) | ~m1_pre_topc(X12,sK0) | ~v1_borsuk_1(X12,sK0) | v4_pre_topc(u1_struct_0(X12),sK0)) )),
% 0.21/0.57    inference(global_subsumption,[],[f96,f94,f444])).
% 0.21/0.57  fof(f444,plain,(
% 0.21/0.57    ( ! [X12] : (~m1_subset_1(u1_struct_0(X12),u1_pre_topc(sK0)) | ~m1_pre_topc(X12,sK0) | ~v1_borsuk_1(X12,sK0) | v4_pre_topc(u1_struct_0(X12),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.57    inference(superposition,[],[f180,f193])).
% 0.21/0.57  fof(f180,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k9_setfam_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | v4_pre_topc(u1_struct_0(X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f178])).
% 0.21/0.57  fof(f178,plain,(
% 0.21/0.57    ( ! [X0,X1] : (v4_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k9_setfam_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.57    inference(equality_resolution,[],[f170])).
% 0.21/0.57  fof(f170,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (v4_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k9_setfam_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f136,f103])).
% 0.21/0.57  fof(f136,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (v4_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f91])).
% 0.21/0.57  fof(f91,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) | ~v4_pre_topc(X2,X0)) & (v4_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.57    inference(flattening,[],[f90])).
% 0.21/0.57  fof(f90,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) | ~v4_pre_topc(X2,X0)) & (v4_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.57    inference(nnf_transformation,[],[f67])).
% 0.21/0.57  fof(f67,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.57    inference(flattening,[],[f66])).
% 0.21/0.57  fof(f66,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f17])).
% 0.21/0.57  fof(f17,axiom,(
% 0.21/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0))))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tsep_1)).
% 0.21/0.57  fof(f94,plain,(
% 0.21/0.57    v2_pre_topc(sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f79])).
% 0.21/0.57  fof(f1323,plain,(
% 0.21/0.57    spl5_41),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f1322])).
% 0.21/0.57  fof(f1322,plain,(
% 0.21/0.57    $false | spl5_41),
% 0.21/0.57    inference(subsumption_resolution,[],[f428,f1321])).
% 0.21/0.57  fof(f1321,plain,(
% 0.21/0.57    ~m1_subset_1(sK1,u1_pre_topc(sK0)) | spl5_41),
% 0.21/0.57    inference(forward_demodulation,[],[f671,f193])).
% 0.21/0.57  fof(f671,plain,(
% 0.21/0.57    ~m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0))) | spl5_41),
% 0.21/0.57    inference(avatar_component_clause,[],[f670])).
% 0.21/0.57  fof(f670,plain,(
% 0.21/0.57    spl5_41 <=> m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 0.21/0.57  fof(f1276,plain,(
% 0.21/0.57    spl5_21 | ~spl5_16 | spl5_7 | ~spl5_41 | spl5_66),
% 0.21/0.57    inference(avatar_split_clause,[],[f1273,f987,f670,f236,f297,f315])).
% 0.21/0.57  fof(f315,plain,(
% 0.21/0.57    spl5_21 <=> v2_struct_0(sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.57  fof(f297,plain,(
% 0.21/0.57    spl5_16 <=> l1_pre_topc(sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.57  fof(f236,plain,(
% 0.21/0.57    spl5_7 <=> v1_xboole_0(sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.57  fof(f1273,plain,(
% 0.21/0.57    ~m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl5_66),
% 0.21/0.57    inference(resolution,[],[f988,f163])).
% 0.21/0.57  fof(f163,plain,(
% 0.21/0.57    ( ! [X0,X1] : (m1_pre_topc(sK3(X0,X1),X0) | ~m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f131,f103])).
% 0.21/0.57  fof(f131,plain,(
% 0.21/0.57    ( ! [X0,X1] : (m1_pre_topc(sK3(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f85])).
% 0.21/0.57  fof(f85,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : ((u1_struct_0(sK3(X0,X1)) = X1 & m1_pre_topc(sK3(X0,X1),X0) & v1_pre_topc(sK3(X0,X1)) & ~v2_struct_0(sK3(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f63,f84])).
% 0.21/0.57  fof(f84,plain,(
% 0.21/0.57    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK3(X0,X1)) = X1 & m1_pre_topc(sK3(X0,X1),X0) & v1_pre_topc(sK3(X0,X1)) & ~v2_struct_0(sK3(X0,X1))))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f63,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.57    inference(flattening,[],[f62])).
% 0.21/0.57  fof(f62,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f25])).
% 0.21/0.57  fof(f25,axiom,(
% 0.21/0.57    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tsep_1)).
% 0.21/0.57  fof(f988,plain,(
% 0.21/0.57    ~m1_pre_topc(sK3(sK0,sK1),sK0) | spl5_66),
% 0.21/0.57    inference(avatar_component_clause,[],[f987])).
% 0.21/0.57  fof(f1054,plain,(
% 0.21/0.57    ~spl5_6 | spl5_1 | ~spl5_35),
% 0.21/0.57    inference(avatar_split_clause,[],[f867,f388,f182,f228])).
% 0.21/0.57  fof(f228,plain,(
% 0.21/0.57    spl5_6 <=> v1_tops_1(sK1,sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.57  fof(f182,plain,(
% 0.21/0.57    spl5_1 <=> v3_tex_2(sK1,sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.57  fof(f388,plain,(
% 0.21/0.57    spl5_35 <=> u1_pre_topc(sK0) = k9_setfam_1(sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 0.21/0.57  fof(f867,plain,(
% 0.21/0.57    v3_tex_2(sK1,sK0) | ~v1_tops_1(sK1,sK0) | ~spl5_35),
% 0.21/0.57    inference(resolution,[],[f846,f712])).
% 0.21/0.57  fof(f712,plain,(
% 0.21/0.57    m1_subset_1(sK1,k9_setfam_1(sK1)) | ~spl5_35),
% 0.21/0.57    inference(backward_demodulation,[],[f428,f389])).
% 0.21/0.57  fof(f389,plain,(
% 0.21/0.57    u1_pre_topc(sK0) = k9_setfam_1(sK1) | ~spl5_35),
% 0.21/0.57    inference(avatar_component_clause,[],[f388])).
% 0.21/0.57  fof(f846,plain,(
% 0.21/0.57    ( ! [X4] : (~m1_subset_1(X4,k9_setfam_1(sK1)) | v3_tex_2(X4,sK0) | ~v1_tops_1(X4,sK0)) ) | ~spl5_35),
% 0.21/0.57    inference(forward_demodulation,[],[f459,f389])).
% 0.21/0.57  fof(f459,plain,(
% 0.21/0.57    ( ! [X4] : (~m1_subset_1(X4,u1_pre_topc(sK0)) | v3_tex_2(X4,sK0) | ~v1_tops_1(X4,sK0)) )),
% 0.21/0.57    inference(global_subsumption,[],[f96,f94,f93,f458,f434])).
% 0.21/0.57  fof(f434,plain,(
% 0.21/0.57    ( ! [X4] : (~m1_subset_1(X4,u1_pre_topc(sK0)) | ~v2_tex_2(X4,sK0) | ~v1_tops_1(X4,sK0) | v3_tex_2(X4,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.57    inference(superposition,[],[f158,f193])).
% 0.21/0.57  fof(f158,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | v3_tex_2(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f122,f103])).
% 0.21/0.57  fof(f122,plain,(
% 0.21/0.57    ( ! [X0,X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f55])).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.57    inference(flattening,[],[f54])).
% 0.21/0.57  fof(f54,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) | (~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f30])).
% 0.21/0.57  fof(f30,axiom,(
% 0.21/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tex_2)).
% 0.21/0.57  fof(f458,plain,(
% 0.21/0.57    ( ! [X3] : (~m1_subset_1(X3,u1_pre_topc(sK0)) | v2_tex_2(X3,sK0)) )),
% 0.21/0.57    inference(global_subsumption,[],[f96,f94,f93,f95,f433])).
% 0.21/0.57  fof(f433,plain,(
% 0.21/0.57    ( ! [X3] : (~m1_subset_1(X3,u1_pre_topc(sK0)) | v2_tex_2(X3,sK0) | ~l1_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.57    inference(superposition,[],[f157,f193])).
% 0.21/0.58  fof(f157,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) | v2_tex_2(X1,X0) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.58    inference(definition_unfolding,[],[f121,f103])).
% 0.21/0.58  fof(f121,plain,(
% 0.21/0.58    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f53])).
% 0.21/0.58  fof(f53,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.58    inference(flattening,[],[f52])).
% 0.21/0.58  fof(f52,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f27])).
% 0.21/0.58  fof(f27,axiom,(
% 0.21/0.58    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).
% 0.21/0.58  fof(f93,plain,(
% 0.21/0.58    ~v2_struct_0(sK0)),
% 0.21/0.58    inference(cnf_transformation,[],[f79])).
% 0.21/0.58  fof(f1038,plain,(
% 0.21/0.58    ~spl5_7 | ~spl5_1),
% 0.21/0.58    inference(avatar_split_clause,[],[f1037,f182,f236])).
% 0.21/0.58  fof(f1037,plain,(
% 0.21/0.58    ~v3_tex_2(sK1,sK0) | ~v1_xboole_0(sK1)),
% 0.21/0.58    inference(global_subsumption,[],[f1035])).
% 0.21/0.58  fof(f1035,plain,(
% 0.21/0.58    ~v3_tex_2(sK1,sK0) | ~v1_xboole_0(sK1)),
% 0.21/0.58    inference(global_subsumption,[],[f96,f94,f93,f200])).
% 0.21/0.58  fof(f200,plain,(
% 0.21/0.58    ~v3_tex_2(sK1,sK0) | ~v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.58    inference(resolution,[],[f146,f160])).
% 0.21/0.58  fof(f160,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | ~v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.58    inference(definition_unfolding,[],[f124,f103])).
% 0.21/0.58  fof(f124,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f59])).
% 0.21/0.58  fof(f59,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.58    inference(flattening,[],[f58])).
% 0.21/0.58  fof(f58,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f28])).
% 0.21/0.58  fof(f28,axiom,(
% 0.21/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).
% 0.21/0.58  fof(f1024,plain,(
% 0.21/0.58    ~spl5_7 | ~spl5_42 | ~spl5_27),
% 0.21/0.58    inference(avatar_split_clause,[],[f731,f337,f734,f236])).
% 0.21/0.58  fof(f734,plain,(
% 0.21/0.58    spl5_42 <=> v1_subset_1(sK2(sK0),sK1)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 0.21/0.58  fof(f337,plain,(
% 0.21/0.58    spl5_27 <=> m1_subset_1(sK2(sK0),k9_setfam_1(sK1))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.21/0.58  fof(f731,plain,(
% 0.21/0.58    ~v1_subset_1(sK2(sK0),sK1) | ~v1_xboole_0(sK1) | ~spl5_27),
% 0.21/0.58    inference(resolution,[],[f338,f156])).
% 0.21/0.58  fof(f156,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k9_setfam_1(X0)) | ~v1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.58    inference(definition_unfolding,[],[f118,f103])).
% 0.21/0.58  fof(f118,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f49])).
% 0.21/0.58  fof(f49,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f10])).
% 0.21/0.58  fof(f10,axiom,(
% 0.21/0.58    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~v1_subset_1(X1,X0)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_subset_1)).
% 0.21/0.58  fof(f338,plain,(
% 0.21/0.58    m1_subset_1(sK2(sK0),k9_setfam_1(sK1)) | ~spl5_27),
% 0.21/0.58    inference(avatar_component_clause,[],[f337])).
% 0.21/0.58  fof(f1014,plain,(
% 0.21/0.58    spl5_21 | ~spl5_17 | ~spl5_22 | ~spl5_16 | ~spl5_66 | spl5_67),
% 0.21/0.58    inference(avatar_split_clause,[],[f1013,f990,f987,f297,f318,f300,f315])).
% 0.21/0.58  fof(f300,plain,(
% 0.21/0.58    spl5_17 <=> v2_pre_topc(sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.58  fof(f318,plain,(
% 0.21/0.58    spl5_22 <=> v1_tdlat_3(sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.21/0.58  fof(f1013,plain,(
% 0.21/0.58    ~m1_pre_topc(sK3(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl5_67),
% 0.21/0.58    inference(resolution,[],[f991,f119])).
% 0.21/0.58  fof(f119,plain,(
% 0.21/0.58    ( ! [X0,X1] : (v1_borsuk_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f51])).
% 0.21/0.58  fof(f51,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : ((v1_tdlat_3(X1) & v1_borsuk_1(X1,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.58    inference(flattening,[],[f50])).
% 0.21/0.58  fof(f50,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : ((v1_tdlat_3(X1) & v1_borsuk_1(X1,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f34])).
% 0.21/0.58  fof(f34,plain,(
% 0.21/0.58    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_borsuk_1(X1,X0))))),
% 0.21/0.58    inference(pure_predicate_removal,[],[f20])).
% 0.21/0.58  fof(f20,axiom,(
% 0.21/0.58    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_tsep_1(X1,X0) & v1_borsuk_1(X1,X0))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_tdlat_3)).
% 0.21/0.58  fof(f991,plain,(
% 0.21/0.58    ~v1_borsuk_1(sK3(sK0,sK1),sK0) | spl5_67),
% 0.21/0.58    inference(avatar_component_clause,[],[f990])).
% 0.21/0.58  fof(f791,plain,(
% 0.21/0.58    spl5_42 | spl5_44 | ~spl5_27),
% 0.21/0.58    inference(avatar_split_clause,[],[f786,f337,f742,f734])).
% 0.21/0.58  fof(f742,plain,(
% 0.21/0.58    spl5_44 <=> sK1 = sK2(sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).
% 0.21/0.58  fof(f786,plain,(
% 0.21/0.58    sK1 = sK2(sK0) | v1_subset_1(sK2(sK0),sK1) | ~spl5_27),
% 0.21/0.58    inference(resolution,[],[f338,f172])).
% 0.21/0.58  fof(f172,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k9_setfam_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.21/0.58    inference(definition_unfolding,[],[f142,f103])).
% 0.21/0.58  fof(f142,plain,(
% 0.21/0.58    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f92])).
% 0.21/0.58  fof(f92,plain,(
% 0.21/0.58    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.58    inference(nnf_transformation,[],[f71])).
% 0.21/0.58  fof(f71,plain,(
% 0.21/0.58    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f23])).
% 0.21/0.58  fof(f23,axiom,(
% 0.21/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 0.21/0.58  fof(f783,plain,(
% 0.21/0.58    spl5_21 | ~spl5_17 | ~spl5_16 | spl5_3 | ~spl5_44),
% 0.21/0.58    inference(avatar_split_clause,[],[f781,f742,f213,f297,f300,f315])).
% 0.21/0.58  fof(f781,plain,(
% 0.21/0.58    v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_44),
% 0.21/0.58    inference(superposition,[],[f128,f743])).
% 0.21/0.58  fof(f743,plain,(
% 0.21/0.58    sK1 = sK2(sK0) | ~spl5_44),
% 0.21/0.58    inference(avatar_component_clause,[],[f742])).
% 0.21/0.58  fof(f128,plain,(
% 0.21/0.58    ( ! [X0] : (v4_pre_topc(sK2(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f83])).
% 0.21/0.58  fof(f83,plain,(
% 0.21/0.58    ! [X0] : ((v4_pre_topc(sK2(X0),X0) & v3_pre_topc(sK2(X0),X0) & ~v1_xboole_0(sK2(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f61,f82])).
% 0.21/0.58  fof(f82,plain,(
% 0.21/0.58    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v4_pre_topc(sK2(X0),X0) & v3_pre_topc(sK2(X0),X0) & ~v1_xboole_0(sK2(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f61,plain,(
% 0.21/0.58    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.58    inference(flattening,[],[f60])).
% 0.21/0.58  fof(f60,plain,(
% 0.21/0.58    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f16])).
% 0.21/0.58  fof(f16,axiom,(
% 0.21/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_tops_1)).
% 0.21/0.58  fof(f704,plain,(
% 0.21/0.58    spl5_21 | ~spl5_17 | ~spl5_16 | spl5_27 | ~spl5_11),
% 0.21/0.58    inference(avatar_split_clause,[],[f687,f254,f337,f297,f300,f315])).
% 0.21/0.58  fof(f254,plain,(
% 0.21/0.58    spl5_11 <=> u1_struct_0(sK0) = sK1),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.58  fof(f687,plain,(
% 0.21/0.58    m1_subset_1(sK2(sK0),k9_setfam_1(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_11),
% 0.21/0.58    inference(superposition,[],[f161,f255])).
% 0.21/0.58  fof(f255,plain,(
% 0.21/0.58    u1_struct_0(sK0) = sK1 | ~spl5_11),
% 0.21/0.58    inference(avatar_component_clause,[],[f254])).
% 0.21/0.58  fof(f161,plain,(
% 0.21/0.58    ( ! [X0] : (m1_subset_1(sK2(X0),k9_setfam_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.58    inference(definition_unfolding,[],[f125,f103])).
% 0.21/0.58  fof(f125,plain,(
% 0.21/0.58    ( ! [X0] : (m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f83])).
% 0.21/0.58  fof(f673,plain,(
% 0.21/0.58    ~spl5_16 | ~spl5_41 | spl5_6 | ~spl5_11 | ~spl5_4),
% 0.21/0.58    inference(avatar_split_clause,[],[f572,f216,f254,f228,f670,f297])).
% 0.21/0.58  fof(f216,plain,(
% 0.21/0.58    spl5_4 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.58  fof(f572,plain,(
% 0.21/0.58    u1_struct_0(sK0) != sK1 | v1_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl5_4),
% 0.21/0.58    inference(superposition,[],[f154,f220])).
% 0.21/0.58  fof(f220,plain,(
% 0.21/0.58    sK1 = k2_pre_topc(sK0,sK1) | ~spl5_4),
% 0.21/0.58    inference(avatar_component_clause,[],[f216])).
% 0.21/0.58  fof(f154,plain,(
% 0.21/0.58    ( ! [X0,X1] : (u1_struct_0(X0) != k2_pre_topc(X0,X1) | v1_tops_1(X1,X0) | ~m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.58    inference(definition_unfolding,[],[f117,f103])).
% 0.21/0.58  fof(f117,plain,(
% 0.21/0.58    ( ! [X0,X1] : (v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f81])).
% 0.21/0.58  fof(f81,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.58    inference(nnf_transformation,[],[f48])).
% 0.21/0.58  fof(f48,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f22])).
% 0.21/0.58  fof(f22,axiom,(
% 0.21/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).
% 0.21/0.58  fof(f668,plain,(
% 0.21/0.58    ~spl5_2 | ~spl5_4 | ~spl5_5),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f667])).
% 0.21/0.58  fof(f667,plain,(
% 0.21/0.58    $false | (~spl5_2 | ~spl5_4 | ~spl5_5)),
% 0.21/0.58    inference(subsumption_resolution,[],[f623,f665])).
% 0.21/0.58  fof(f665,plain,(
% 0.21/0.58    ~v1_subset_1(sK1,sK1) | (~spl5_4 | ~spl5_5)),
% 0.21/0.58    inference(resolution,[],[f657,f179])).
% 0.21/0.58  fof(f179,plain,(
% 0.21/0.58    ( ! [X1] : (~m1_subset_1(X1,k9_setfam_1(X1)) | ~v1_subset_1(X1,X1)) )),
% 0.21/0.58    inference(equality_resolution,[],[f173])).
% 0.21/0.58  fof(f173,plain,(
% 0.21/0.58    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k9_setfam_1(X0))) )),
% 0.21/0.58    inference(definition_unfolding,[],[f141,f103])).
% 1.65/0.58  fof(f141,plain,(
% 1.65/0.58    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f92])).
% 1.65/0.58  fof(f657,plain,(
% 1.65/0.58    m1_subset_1(sK1,k9_setfam_1(sK1)) | (~spl5_4 | ~spl5_5)),
% 1.65/0.58    inference(backward_demodulation,[],[f428,f618])).
% 1.65/0.58  fof(f618,plain,(
% 1.65/0.58    u1_pre_topc(sK0) = k9_setfam_1(sK1) | (~spl5_4 | ~spl5_5)),
% 1.65/0.58    inference(backward_demodulation,[],[f193,f617])).
% 1.65/0.58  fof(f617,plain,(
% 1.65/0.58    u1_struct_0(sK0) = sK1 | (~spl5_4 | ~spl5_5)),
% 1.65/0.58    inference(forward_demodulation,[],[f226,f220])).
% 1.65/0.58  fof(f226,plain,(
% 1.65/0.58    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~spl5_5),
% 1.65/0.58    inference(avatar_component_clause,[],[f225])).
% 1.65/0.58  fof(f225,plain,(
% 1.65/0.58    spl5_5 <=> u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.65/0.58  fof(f623,plain,(
% 1.65/0.58    v1_subset_1(sK1,sK1) | (~spl5_2 | ~spl5_4 | ~spl5_5)),
% 1.65/0.58    inference(backward_demodulation,[],[f186,f617])).
% 1.65/0.58  fof(f186,plain,(
% 1.65/0.58    v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl5_2),
% 1.65/0.58    inference(avatar_component_clause,[],[f185])).
% 1.65/0.58  fof(f185,plain,(
% 1.65/0.58    spl5_2 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.65/0.58  fof(f569,plain,(
% 1.65/0.58    spl5_4 | ~spl5_3),
% 1.65/0.58    inference(avatar_split_clause,[],[f568,f213,f216])).
% 1.65/0.58  fof(f568,plain,(
% 1.65/0.58    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1)),
% 1.65/0.58    inference(global_subsumption,[],[f219])).
% 1.65/0.58  fof(f219,plain,(
% 1.65/0.58    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1)),
% 1.65/0.58    inference(global_subsumption,[],[f96,f195])).
% 1.65/0.58  fof(f195,plain,(
% 1.65/0.58    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.65/0.58    inference(resolution,[],[f146,f153])).
% 1.65/0.58  fof(f153,plain,(
% 1.65/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 1.65/0.58    inference(definition_unfolding,[],[f114,f103])).
% 1.65/0.58  fof(f114,plain,(
% 1.65/0.58    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f47])).
% 1.65/0.58  fof(f47,plain,(
% 1.65/0.58    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.65/0.58    inference(flattening,[],[f46])).
% 1.65/0.58  fof(f46,plain,(
% 1.65/0.58    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.65/0.58    inference(ennf_transformation,[],[f15])).
% 1.65/0.58  fof(f15,axiom,(
% 1.65/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.65/0.58  fof(f483,plain,(
% 1.65/0.58    spl5_6 | ~spl5_1),
% 1.65/0.58    inference(avatar_split_clause,[],[f482,f182,f228])).
% 1.65/0.58  fof(f482,plain,(
% 1.65/0.58    ~v3_tex_2(sK1,sK0) | v1_tops_1(sK1,sK0)),
% 1.65/0.58    inference(global_subsumption,[],[f391])).
% 1.65/0.58  fof(f391,plain,(
% 1.65/0.58    ~v3_tex_2(sK1,sK0) | v1_tops_1(sK1,sK0)),
% 1.65/0.58    inference(global_subsumption,[],[f252,f96,f94,f93,f199])).
% 1.65/0.58  fof(f199,plain,(
% 1.65/0.58    ~v3_tex_2(sK1,sK0) | ~v3_pre_topc(sK1,sK0) | v1_tops_1(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.65/0.58    inference(resolution,[],[f146,f159])).
% 1.65/0.58  fof(f159,plain,(
% 1.65/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | v1_tops_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.65/0.58    inference(definition_unfolding,[],[f123,f103])).
% 1.65/0.58  fof(f123,plain,(
% 1.65/0.58    ( ! [X0,X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f57])).
% 1.65/0.58  fof(f57,plain,(
% 1.65/0.58    ! [X0] : (! [X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.65/0.58    inference(flattening,[],[f56])).
% 1.65/0.58  fof(f56,plain,(
% 1.65/0.58    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) | (~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.65/0.58    inference(ennf_transformation,[],[f29])).
% 1.65/0.58  fof(f29,axiom,(
% 1.65/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tex_2(X1,X0) & v3_pre_topc(X1,X0)) => v1_tops_1(X1,X0))))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tex_2)).
% 1.65/0.58  fof(f252,plain,(
% 1.65/0.58    v3_pre_topc(sK1,sK0)),
% 1.65/0.58    inference(global_subsumption,[],[f94,f95,f96,f204])).
% 1.65/0.58  fof(f204,plain,(
% 1.65/0.58    v3_pre_topc(sK1,sK0) | ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 1.65/0.58    inference(resolution,[],[f146,f167])).
% 1.65/0.58  fof(f167,plain,(
% 1.65/0.58    ( ! [X2,X0] : (~m1_subset_1(X2,k9_setfam_1(u1_struct_0(X0))) | v3_pre_topc(X2,X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.65/0.58    inference(definition_unfolding,[],[f133,f103])).
% 1.65/0.58  fof(f133,plain,(
% 1.65/0.58    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f89])).
% 1.65/0.58  fof(f89,plain,(
% 1.65/0.58    ! [X0] : (((v1_tdlat_3(X0) | (~v3_pre_topc(sK4(X0),X0) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.65/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f87,f88])).
% 1.65/0.58  fof(f88,plain,(
% 1.65/0.58    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK4(X0),X0) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.65/0.58    introduced(choice_axiom,[])).
% 1.65/0.58  fof(f87,plain,(
% 1.65/0.58    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.65/0.58    inference(rectify,[],[f86])).
% 1.65/0.58  fof(f86,plain,(
% 1.65/0.58    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.65/0.58    inference(nnf_transformation,[],[f65])).
% 1.65/0.58  fof(f65,plain,(
% 1.65/0.58    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.65/0.58    inference(flattening,[],[f64])).
% 1.65/0.58  fof(f64,plain,(
% 1.65/0.58    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.65/0.58    inference(ennf_transformation,[],[f26])).
% 1.65/0.58  fof(f26,axiom,(
% 1.65/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v3_pre_topc(X1,X0))))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).
% 1.65/0.58  fof(f481,plain,(
% 1.65/0.58    spl5_2 | spl5_11),
% 1.65/0.58    inference(avatar_split_clause,[],[f414,f254,f185])).
% 1.65/0.58  fof(f414,plain,(
% 1.65/0.58    u1_struct_0(sK0) = sK1 | v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.65/0.58    inference(resolution,[],[f146,f172])).
% 1.65/0.58  fof(f423,plain,(
% 1.65/0.58    spl5_7 | spl5_8),
% 1.65/0.58    inference(avatar_split_clause,[],[f422,f239,f236])).
% 1.65/0.58  fof(f422,plain,(
% 1.65/0.58    sK1 = u1_struct_0(sK3(sK0,sK1)) | v1_xboole_0(sK1)),
% 1.65/0.58    inference(global_subsumption,[],[f96,f93,f408])).
% 1.65/0.58  fof(f408,plain,(
% 1.65/0.58    sK1 = u1_struct_0(sK3(sK0,sK1)) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.65/0.58    inference(resolution,[],[f146,f162])).
% 1.65/0.58  fof(f162,plain,(
% 1.65/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) | u1_struct_0(sK3(X0,X1)) = X1 | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.65/0.58    inference(definition_unfolding,[],[f132,f103])).
% 1.65/0.58  fof(f132,plain,(
% 1.65/0.58    ( ! [X0,X1] : (u1_struct_0(sK3(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f85])).
% 1.65/0.58  fof(f421,plain,(
% 1.65/0.58    spl5_5 | ~spl5_6),
% 1.65/0.58    inference(avatar_split_clause,[],[f420,f228,f225])).
% 1.65/0.58  fof(f420,plain,(
% 1.65/0.58    ~v1_tops_1(sK1,sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.65/0.58    inference(global_subsumption,[],[f96,f403])).
% 1.65/0.58  fof(f403,plain,(
% 1.65/0.58    ~v1_tops_1(sK1,sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.65/0.58    inference(resolution,[],[f146,f155])).
% 1.65/0.58  fof(f155,plain,(
% 1.65/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~l1_pre_topc(X0)) )),
% 1.65/0.58    inference(definition_unfolding,[],[f116,f103])).
% 1.65/0.58  fof(f116,plain,(
% 1.65/0.58    ( ! [X0,X1] : (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f81])).
% 1.65/0.58  fof(f390,plain,(
% 1.65/0.58    ~spl5_16 | spl5_35 | ~spl5_11),
% 1.65/0.58    inference(avatar_split_clause,[],[f386,f254,f388,f297])).
% 1.65/0.58  fof(f386,plain,(
% 1.65/0.58    u1_pre_topc(sK0) = k9_setfam_1(sK1) | ~l1_pre_topc(sK0) | ~spl5_11),
% 1.65/0.58    inference(forward_demodulation,[],[f384,f255])).
% 1.65/0.58  fof(f384,plain,(
% 1.65/0.58    k9_setfam_1(u1_struct_0(sK0)) = u1_pre_topc(sK0) | ~l1_pre_topc(sK0)),
% 1.65/0.58    inference(resolution,[],[f95,f110])).
% 1.65/0.58  fof(f383,plain,(
% 1.65/0.58    spl5_22),
% 1.65/0.58    inference(avatar_contradiction_clause,[],[f382])).
% 1.65/0.58  fof(f382,plain,(
% 1.65/0.58    $false | spl5_22),
% 1.65/0.58    inference(subsumption_resolution,[],[f95,f319])).
% 1.65/0.58  fof(f319,plain,(
% 1.65/0.58    ~v1_tdlat_3(sK0) | spl5_22),
% 1.65/0.58    inference(avatar_component_clause,[],[f318])).
% 1.65/0.58  fof(f376,plain,(
% 1.65/0.58    ~spl5_21),
% 1.65/0.58    inference(avatar_contradiction_clause,[],[f375])).
% 1.65/0.58  fof(f375,plain,(
% 1.65/0.58    $false | ~spl5_21),
% 1.65/0.58    inference(subsumption_resolution,[],[f93,f316])).
% 1.65/0.58  fof(f316,plain,(
% 1.65/0.58    v2_struct_0(sK0) | ~spl5_21),
% 1.65/0.58    inference(avatar_component_clause,[],[f315])).
% 1.65/0.58  fof(f367,plain,(
% 1.65/0.58    spl5_17),
% 1.65/0.58    inference(avatar_contradiction_clause,[],[f366])).
% 1.65/0.58  fof(f366,plain,(
% 1.65/0.58    $false | spl5_17),
% 1.65/0.58    inference(subsumption_resolution,[],[f94,f301])).
% 1.65/0.58  fof(f301,plain,(
% 1.65/0.58    ~v2_pre_topc(sK0) | spl5_17),
% 1.65/0.58    inference(avatar_component_clause,[],[f300])).
% 1.65/0.58  fof(f365,plain,(
% 1.65/0.58    spl5_16),
% 1.65/0.58    inference(avatar_contradiction_clause,[],[f364])).
% 1.65/0.58  fof(f364,plain,(
% 1.65/0.58    $false | spl5_16),
% 1.65/0.58    inference(subsumption_resolution,[],[f96,f298])).
% 1.65/0.58  fof(f298,plain,(
% 1.65/0.58    ~l1_pre_topc(sK0) | spl5_16),
% 1.65/0.58    inference(avatar_component_clause,[],[f297])).
% 1.65/0.58  fof(f190,plain,(
% 1.65/0.58    spl5_1 | ~spl5_2),
% 1.65/0.58    inference(avatar_split_clause,[],[f98,f185,f182])).
% 1.65/0.58  fof(f98,plain,(
% 1.65/0.58    ~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)),
% 1.65/0.58    inference(cnf_transformation,[],[f79])).
% 1.65/0.58  fof(f187,plain,(
% 1.65/0.58    ~spl5_1 | spl5_2),
% 1.65/0.58    inference(avatar_split_clause,[],[f99,f185,f182])).
% 1.65/0.58  fof(f99,plain,(
% 1.65/0.58    v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)),
% 1.65/0.58    inference(cnf_transformation,[],[f79])).
% 1.65/0.58  % SZS output end Proof for theBenchmark
% 1.65/0.58  % (13007)------------------------------
% 1.65/0.58  % (13007)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.58  % (13007)Termination reason: Refutation
% 1.65/0.58  
% 1.65/0.58  % (13007)Memory used [KB]: 11641
% 1.65/0.58  % (13007)Time elapsed: 0.160 s
% 1.65/0.58  % (13007)------------------------------
% 1.65/0.58  % (13007)------------------------------
% 1.65/0.59  % (13004)Success in time 0.218 s
%------------------------------------------------------------------------------
