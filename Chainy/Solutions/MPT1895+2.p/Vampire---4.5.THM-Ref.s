%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1895+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:36 EST 2020

% Result     : Theorem 1.73s
% Output     : Refutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 113 expanded)
%              Number of leaves         :   17 (  52 expanded)
%              Depth                    :    7
%              Number of atoms          :  199 ( 567 expanded)
%              Number of equality atoms :   27 (  81 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9271,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f8532,f8536,f8540,f8544,f8548,f8552,f8556,f8799,f8820,f8959,f9270])).

fof(f9270,plain,
    ( u1_struct_0(sK215) != k2_pre_topc(sK215,sK216)
    | k3_tarski(a_2_0_tex_2(sK215,sK216)) != k2_pre_topc(sK215,sK216)
    | u1_struct_0(sK215) = k3_tarski(a_2_0_tex_2(sK215,sK216)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f8959,plain,
    ( ~ spl540_4
    | spl540_62
    | ~ spl540_25
    | ~ spl540_3 ),
    inference(avatar_split_clause,[],[f8668,f8538,f8806,f8957,f8542])).

fof(f8542,plain,
    ( spl540_4
  <=> l1_pre_topc(sK215) ),
    introduced(avatar_definition,[new_symbols(naming,[spl540_4])])).

fof(f8957,plain,
    ( spl540_62
  <=> u1_struct_0(sK215) = k2_pre_topc(sK215,sK216) ),
    introduced(avatar_definition,[new_symbols(naming,[spl540_62])])).

fof(f8806,plain,
    ( spl540_25
  <=> v1_tops_1(sK216,sK215) ),
    introduced(avatar_definition,[new_symbols(naming,[spl540_25])])).

fof(f8538,plain,
    ( spl540_3
  <=> m1_subset_1(sK216,k1_zfmisc_1(u1_struct_0(sK215))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl540_3])])).

fof(f8668,plain,
    ( ~ v1_tops_1(sK216,sK215)
    | u1_struct_0(sK215) = k2_pre_topc(sK215,sK216)
    | ~ l1_pre_topc(sK215)
    | ~ spl540_3 ),
    inference(resolution,[],[f8539,f6939])).

fof(f6939,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f5527])).

fof(f5527,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f4113])).

fof(f4113,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3604])).

fof(f3604,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

fof(f8539,plain,
    ( m1_subset_1(sK216,k1_zfmisc_1(u1_struct_0(sK215)))
    | ~ spl540_3 ),
    inference(avatar_component_clause,[],[f8538])).

fof(f8820,plain,
    ( spl540_7
    | ~ spl540_6
    | ~ spl540_5
    | ~ spl540_4
    | spl540_25
    | ~ spl540_2
    | ~ spl540_3 ),
    inference(avatar_split_clause,[],[f8634,f8538,f8534,f8806,f8542,f8546,f8550,f8554])).

fof(f8554,plain,
    ( spl540_7
  <=> v2_struct_0(sK215) ),
    introduced(avatar_definition,[new_symbols(naming,[spl540_7])])).

fof(f8550,plain,
    ( spl540_6
  <=> v2_pre_topc(sK215) ),
    introduced(avatar_definition,[new_symbols(naming,[spl540_6])])).

fof(f8546,plain,
    ( spl540_5
  <=> v3_tdlat_3(sK215) ),
    introduced(avatar_definition,[new_symbols(naming,[spl540_5])])).

fof(f8534,plain,
    ( spl540_2
  <=> v3_tex_2(sK216,sK215) ),
    introduced(avatar_definition,[new_symbols(naming,[spl540_2])])).

fof(f8634,plain,
    ( ~ v3_tex_2(sK216,sK215)
    | v1_tops_1(sK216,sK215)
    | ~ l1_pre_topc(sK215)
    | ~ v3_tdlat_3(sK215)
    | ~ v2_pre_topc(sK215)
    | v2_struct_0(sK215)
    | ~ spl540_3 ),
    inference(resolution,[],[f8539,f6344])).

fof(f6344,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | v1_tops_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3781])).

fof(f3781,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3780])).

fof(f3780,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3719])).

fof(f3719,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
           => v1_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tex_2)).

fof(f8799,plain,
    ( spl540_7
    | ~ spl540_6
    | ~ spl540_5
    | ~ spl540_4
    | spl540_23
    | ~ spl540_3 ),
    inference(avatar_split_clause,[],[f8628,f8538,f8797,f8542,f8546,f8550,f8554])).

fof(f8797,plain,
    ( spl540_23
  <=> k3_tarski(a_2_0_tex_2(sK215,sK216)) = k2_pre_topc(sK215,sK216) ),
    introduced(avatar_definition,[new_symbols(naming,[spl540_23])])).

fof(f8628,plain,
    ( k3_tarski(a_2_0_tex_2(sK215,sK216)) = k2_pre_topc(sK215,sK216)
    | ~ l1_pre_topc(sK215)
    | ~ v3_tdlat_3(sK215)
    | ~ v2_pre_topc(sK215)
    | v2_struct_0(sK215)
    | ~ spl540_3 ),
    inference(resolution,[],[f8539,f6338])).

fof(f6338,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k3_tarski(a_2_0_tex_2(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3771])).

fof(f3771,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k3_tarski(a_2_0_tex_2(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3770])).

fof(f3770,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k3_tarski(a_2_0_tex_2(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3711])).

fof(f3711,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k3_tarski(a_2_0_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tex_2)).

fof(f8556,plain,(
    ~ spl540_7 ),
    inference(avatar_split_clause,[],[f6202,f8554])).

fof(f6202,plain,(
    ~ v2_struct_0(sK215) ),
    inference(cnf_transformation,[],[f5097])).

fof(f5097,plain,
    ( u1_struct_0(sK215) != k3_tarski(a_2_0_tex_2(sK215,sK216))
    & v3_tex_2(sK216,sK215)
    & m1_subset_1(sK216,k1_zfmisc_1(u1_struct_0(sK215)))
    & l1_pre_topc(sK215)
    & v3_tdlat_3(sK215)
    & v2_pre_topc(sK215)
    & ~ v2_struct_0(sK215) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK215,sK216])],[f3747,f5096,f5095])).

fof(f5095,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( u1_struct_0(X0) != k3_tarski(a_2_0_tex_2(X0,X1))
            & v3_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( u1_struct_0(sK215) != k3_tarski(a_2_0_tex_2(sK215,X1))
          & v3_tex_2(X1,sK215)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK215))) )
      & l1_pre_topc(sK215)
      & v3_tdlat_3(sK215)
      & v2_pre_topc(sK215)
      & ~ v2_struct_0(sK215) ) ),
    introduced(choice_axiom,[])).

fof(f5096,plain,
    ( ? [X1] :
        ( u1_struct_0(sK215) != k3_tarski(a_2_0_tex_2(sK215,X1))
        & v3_tex_2(X1,sK215)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK215))) )
   => ( u1_struct_0(sK215) != k3_tarski(a_2_0_tex_2(sK215,sK216))
      & v3_tex_2(sK216,sK215)
      & m1_subset_1(sK216,k1_zfmisc_1(u1_struct_0(sK215))) ) ),
    introduced(choice_axiom,[])).

fof(f3747,plain,(
    ? [X0] :
      ( ? [X1] :
          ( u1_struct_0(X0) != k3_tarski(a_2_0_tex_2(X0,X1))
          & v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3746])).

fof(f3746,plain,(
    ? [X0] :
      ( ? [X1] :
          ( u1_struct_0(X0) != k3_tarski(a_2_0_tex_2(X0,X1))
          & v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3721])).

fof(f3721,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
             => u1_struct_0(X0) = k3_tarski(a_2_0_tex_2(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f3720])).

fof(f3720,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
           => u1_struct_0(X0) = k3_tarski(a_2_0_tex_2(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_tex_2)).

fof(f8552,plain,(
    spl540_6 ),
    inference(avatar_split_clause,[],[f6203,f8550])).

fof(f6203,plain,(
    v2_pre_topc(sK215) ),
    inference(cnf_transformation,[],[f5097])).

fof(f8548,plain,(
    spl540_5 ),
    inference(avatar_split_clause,[],[f6204,f8546])).

fof(f6204,plain,(
    v3_tdlat_3(sK215) ),
    inference(cnf_transformation,[],[f5097])).

fof(f8544,plain,(
    spl540_4 ),
    inference(avatar_split_clause,[],[f6205,f8542])).

fof(f6205,plain,(
    l1_pre_topc(sK215) ),
    inference(cnf_transformation,[],[f5097])).

fof(f8540,plain,(
    spl540_3 ),
    inference(avatar_split_clause,[],[f6206,f8538])).

fof(f6206,plain,(
    m1_subset_1(sK216,k1_zfmisc_1(u1_struct_0(sK215))) ),
    inference(cnf_transformation,[],[f5097])).

fof(f8536,plain,(
    spl540_2 ),
    inference(avatar_split_clause,[],[f6207,f8534])).

fof(f6207,plain,(
    v3_tex_2(sK216,sK215) ),
    inference(cnf_transformation,[],[f5097])).

fof(f8532,plain,(
    ~ spl540_1 ),
    inference(avatar_split_clause,[],[f6208,f8530])).

fof(f8530,plain,
    ( spl540_1
  <=> u1_struct_0(sK215) = k3_tarski(a_2_0_tex_2(sK215,sK216)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl540_1])])).

fof(f6208,plain,(
    u1_struct_0(sK215) != k3_tarski(a_2_0_tex_2(sK215,sK216)) ),
    inference(cnf_transformation,[],[f5097])).
%------------------------------------------------------------------------------
