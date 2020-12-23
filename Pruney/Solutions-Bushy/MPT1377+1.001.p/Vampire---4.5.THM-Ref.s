%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1377+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:50 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :  221 ( 628 expanded)
%              Number of leaves         :   39 ( 235 expanded)
%              Depth                    :   20
%              Number of atoms          :  866 (3870 expanded)
%              Number of equality atoms :   42 ( 121 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f877,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f82,f85,f95,f100,f107,f141,f166,f168,f171,f183,f188,f195,f314,f318,f322,f323,f591,f602,f610,f619,f621,f649,f650,f700,f701,f702,f835,f845,f851,f867,f876])).

fof(f876,plain,
    ( spl6_16
    | spl6_68 ),
    inference(avatar_contradiction_clause,[],[f875])).

fof(f875,plain,
    ( $false
    | spl6_16
    | spl6_68 ),
    inference(resolution,[],[f873,f194])).

fof(f194,plain,
    ( ~ sP0(sK3,sK2)
    | spl6_16 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl6_16
  <=> sP0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f873,plain,
    ( sP0(sK3,sK2)
    | spl6_68 ),
    inference(resolution,[],[f866,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_tops_2(sK4(X0,X1),X1)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ! [X3] :
              ( ~ v1_finset_1(X3)
              | ~ m1_setfam_1(X3,X0)
              | ~ r1_tarski(X3,sK4(X0,X1))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
          & v1_tops_2(sK4(X0,X1),X1)
          & m1_setfam_1(sK4(X0,X1),X0)
          & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) )
      & ( ! [X4] :
            ( ( v1_finset_1(sK5(X0,X1,X4))
              & m1_setfam_1(sK5(X0,X1,X4),X0)
              & r1_tarski(sK5(X0,X1,X4),X4)
              & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
            | ~ v1_tops_2(X4,X1)
            | ~ m1_setfam_1(X4,X0)
            | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f30,f32,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ v1_finset_1(X3)
              | ~ m1_setfam_1(X3,X0)
              | ~ r1_tarski(X3,X2)
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
          & v1_tops_2(X2,X1)
          & m1_setfam_1(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
     => ( ! [X3] :
            ( ~ v1_finset_1(X3)
            | ~ m1_setfam_1(X3,X0)
            | ~ r1_tarski(X3,sK4(X0,X1))
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
        & v1_tops_2(sK4(X0,X1),X1)
        & m1_setfam_1(sK4(X0,X1),X0)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( v1_finset_1(X5)
          & m1_setfam_1(X5,X0)
          & r1_tarski(X5,X4)
          & m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
     => ( v1_finset_1(sK5(X0,X1,X4))
        & m1_setfam_1(sK5(X0,X1,X4),X0)
        & r1_tarski(sK5(X0,X1,X4),X4)
        & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ v1_finset_1(X3)
                | ~ m1_setfam_1(X3,X0)
                | ~ r1_tarski(X3,X2)
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
            & v1_tops_2(X2,X1)
            & m1_setfam_1(X2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( v1_finset_1(X5)
                & m1_setfam_1(X5,X0)
                & r1_tarski(X5,X4)
                & m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
            | ~ v1_tops_2(X4,X1)
            | ~ m1_setfam_1(X4,X0)
            | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ! [X3] :
                ( ~ v1_finset_1(X3)
                | ~ m1_setfam_1(X3,X1)
                | ~ r1_tarski(X3,X2)
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & v1_tops_2(X2,X0)
            & m1_setfam_1(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( v1_finset_1(X3)
                & m1_setfam_1(X3,X1)
                & r1_tarski(X3,X2)
                & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            | ~ v1_tops_2(X2,X0)
            | ~ m1_setfam_1(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( ? [X3] :
              ( v1_finset_1(X3)
              & m1_setfam_1(X3,X1)
              & r1_tarski(X3,X2)
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ v1_tops_2(X2,X0)
          | ~ m1_setfam_1(X2,X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f866,plain,
    ( ~ v1_tops_2(sK4(sK3,sK2),sK2)
    | spl6_68 ),
    inference(avatar_component_clause,[],[f864])).

fof(f864,plain,
    ( spl6_68
  <=> v1_tops_2(sK4(sK3,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).

fof(f867,plain,
    ( spl6_12
    | ~ spl6_55
    | ~ spl6_13
    | ~ spl6_68
    | ~ spl6_66
    | spl6_65 ),
    inference(avatar_split_clause,[],[f861,f828,f832,f864,f158,f612,f154])).

fof(f154,plain,
    ( spl6_12
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f612,plain,
    ( spl6_55
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).

fof(f158,plain,
    ( spl6_13
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f832,plain,
    ( spl6_66
  <=> m1_subset_1(sK4(sK3,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).

fof(f828,plain,
    ( spl6_65
  <=> v1_tops_2(sK4(sK3,sK2),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).

fof(f861,plain,
    ( ~ m1_subset_1(sK4(sK3,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ v1_tops_2(sK4(sK3,sK2),sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl6_65 ),
    inference(resolution,[],[f830,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_tops_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & v1_tops_2(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
              & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            | ~ v1_tops_2(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & v1_tops_2(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
              & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            | ~ v1_tops_2(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_compts_1)).

fof(f830,plain,
    ( ~ v1_tops_2(sK4(sK3,sK2),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | spl6_65 ),
    inference(avatar_component_clause,[],[f828])).

fof(f851,plain,
    ( ~ spl6_20
    | ~ spl6_23
    | ~ spl6_24
    | spl6_66 ),
    inference(avatar_contradiction_clause,[],[f849])).

fof(f849,plain,
    ( $false
    | ~ spl6_20
    | ~ spl6_23
    | ~ spl6_24
    | spl6_66 ),
    inference(resolution,[],[f834,f796])).

fof(f796,plain,
    ( m1_subset_1(sK4(sK3,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl6_20
    | ~ spl6_23
    | ~ spl6_24 ),
    inference(backward_demodulation,[],[f716,f793])).

fof(f793,plain,
    ( sK4(sK3,sK2) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),sK4(sK3,sK2)))
    | ~ spl6_24 ),
    inference(equality_resolution,[],[f285])).

fof(f285,plain,
    ( ! [X6,X5] :
        ( g1_pre_topc(X5,X6) != g1_pre_topc(u1_struct_0(sK2),sK4(sK3,sK2))
        | u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),sK4(sK3,sK2))) = X6 )
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f284])).

fof(f284,plain,
    ( spl6_24
  <=> ! [X5,X6] :
        ( g1_pre_topc(X5,X6) != g1_pre_topc(u1_struct_0(sK2),sK4(sK3,sK2))
        | u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),sK4(sK3,sK2))) = X6 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f716,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),sK4(sK3,sK2))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl6_20
    | ~ spl6_23 ),
    inference(backward_demodulation,[],[f267,f715])).

fof(f715,plain,
    ( u1_struct_0(sK2) = u1_struct_0(g1_pre_topc(u1_struct_0(sK2),sK4(sK3,sK2)))
    | ~ spl6_23 ),
    inference(equality_resolution,[],[f281])).

fof(f281,plain,
    ( ! [X2,X1] :
        ( g1_pre_topc(X1,X2) != g1_pre_topc(u1_struct_0(sK2),sK4(sK3,sK2))
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),sK4(sK3,sK2))) = X1 )
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f280])).

fof(f280,plain,
    ( spl6_23
  <=> ! [X1,X2] :
        ( g1_pre_topc(X1,X2) != g1_pre_topc(u1_struct_0(sK2),sK4(sK3,sK2))
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),sK4(sK3,sK2))) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f267,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),sK4(sK3,sK2))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),sK4(sK3,sK2))))))
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f266])).

fof(f266,plain,
    ( spl6_20
  <=> m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),sK4(sK3,sK2))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),sK4(sK3,sK2)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f834,plain,
    ( ~ m1_subset_1(sK4(sK3,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | spl6_66 ),
    inference(avatar_component_clause,[],[f832])).

fof(f845,plain,
    ( spl6_16
    | spl6_64 ),
    inference(avatar_contradiction_clause,[],[f844])).

fof(f844,plain,
    ( $false
    | spl6_16
    | spl6_64 ),
    inference(resolution,[],[f843,f194])).

fof(f843,plain,
    ( sP0(sK3,sK2)
    | spl6_64 ),
    inference(resolution,[],[f826,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_setfam_1(sK4(X0,X1),X0)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f826,plain,
    ( ~ m1_setfam_1(sK4(sK3,sK2),sK3)
    | spl6_64 ),
    inference(avatar_component_clause,[],[f824])).

fof(f824,plain,
    ( spl6_64
  <=> m1_setfam_1(sK4(sK3,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).

fof(f835,plain,
    ( ~ spl6_64
    | ~ spl6_7
    | ~ spl6_65
    | ~ spl6_66
    | ~ spl6_10
    | spl6_16 ),
    inference(avatar_split_clause,[],[f822,f192,f139,f832,f828,f104,f824])).

fof(f104,plain,
    ( spl6_7
  <=> sP0(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f139,plain,
    ( spl6_10
  <=> ! [X1,X2] :
        ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X1,X2)
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f822,plain,
    ( ~ m1_subset_1(sK4(sK3,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ v1_tops_2(sK4(sK3,sK2),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ sP0(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ m1_setfam_1(sK4(sK3,sK2),sK3)
    | ~ spl6_10
    | spl6_16 ),
    inference(duplicate_literal_removal,[],[f821])).

fof(f821,plain,
    ( ~ m1_subset_1(sK4(sK3,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ v1_tops_2(sK4(sK3,sK2),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ sP0(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ m1_setfam_1(sK4(sK3,sK2),sK3)
    | ~ m1_subset_1(sK4(sK3,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl6_10
    | spl6_16 ),
    inference(forward_demodulation,[],[f819,f175])).

fof(f175,plain,
    ( u1_struct_0(sK2) = u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ spl6_10 ),
    inference(equality_resolution,[],[f140])).

fof(f140,plain,
    ( ! [X2,X1] :
        ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X1,X2)
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = X1 )
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f139])).

fof(f819,plain,
    ( ~ v1_tops_2(sK4(sK3,sK2),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ m1_subset_1(sK4(sK3,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
    | ~ sP0(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ m1_setfam_1(sK4(sK3,sK2),sK3)
    | ~ m1_subset_1(sK4(sK3,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl6_10
    | spl6_16 ),
    inference(duplicate_literal_removal,[],[f816])).

fof(f816,plain,
    ( ~ v1_tops_2(sK4(sK3,sK2),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ m1_subset_1(sK4(sK3,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
    | ~ sP0(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v1_tops_2(sK4(sK3,sK2),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ m1_setfam_1(sK4(sK3,sK2),sK3)
    | ~ m1_subset_1(sK4(sK3,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ sP0(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ spl6_10
    | spl6_16 ),
    inference(resolution,[],[f661,f196])).

fof(f196,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK5(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
        | ~ m1_setfam_1(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | ~ sP0(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) )
    | ~ spl6_10 ),
    inference(superposition,[],[f48,f175])).

fof(f48,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ v1_tops_2(X4,X1)
      | ~ m1_setfam_1(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f661,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(sK3,X0,sK4(sK3,sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | ~ v1_tops_2(sK4(sK3,sK2),X0)
        | ~ m1_subset_1(sK4(sK3,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ sP0(sK3,X0) )
    | spl6_16 ),
    inference(resolution,[],[f194,f462])).

fof(f462,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1)
      | ~ m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ v1_tops_2(sK4(X0,X1),X2)
      | ~ m1_subset_1(sK5(X0,X2,sK4(X0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ sP0(X0,X2) ) ),
    inference(duplicate_literal_removal,[],[f461])).

fof(f461,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1)
      | ~ m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ v1_tops_2(sK4(X0,X1),X2)
      | ~ m1_subset_1(sK5(X0,X2,sK4(X0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ sP0(X0,X2)
      | sP0(X0,X1) ) ),
    inference(resolution,[],[f381,f53])).

fof(f381,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_setfam_1(sK4(X0,X2),X0)
      | sP0(X0,X2)
      | ~ m1_subset_1(sK4(X0,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ v1_tops_2(sK4(X0,X2),X1)
      | ~ m1_subset_1(sK5(X0,X1,sK4(X0,X2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ sP0(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f380])).

fof(f380,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1)
      | sP0(X0,X2)
      | ~ m1_subset_1(sK4(X0,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ v1_tops_2(sK4(X0,X2),X1)
      | ~ m1_subset_1(sK5(X0,X1,sK4(X0,X2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ v1_tops_2(sK4(X0,X2),X1)
      | ~ m1_setfam_1(sK4(X0,X2),X0)
      | ~ m1_subset_1(sK4(X0,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ sP0(X0,X1) ) ),
    inference(resolution,[],[f311,f50])).

fof(f50,plain,(
    ! [X4,X0,X1] :
      ( m1_setfam_1(sK5(X0,X1,X4),X0)
      | ~ v1_tops_2(X4,X1)
      | ~ m1_setfam_1(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f311,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_setfam_1(sK5(X0,X2,sK4(X0,X1)),X0)
      | ~ sP0(X0,X2)
      | sP0(X0,X1)
      | ~ m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ v1_tops_2(sK4(X0,X1),X2)
      | ~ m1_subset_1(sK5(X0,X2,sK4(X0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    inference(duplicate_literal_removal,[],[f310])).

fof(f310,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ sP0(X0,X2)
      | sP0(X0,X1)
      | ~ m1_setfam_1(sK5(X0,X2,sK4(X0,X1)),X0)
      | ~ v1_tops_2(sK4(X0,X1),X2)
      | ~ m1_subset_1(sK5(X0,X2,sK4(X0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | sP0(X0,X1) ) ),
    inference(resolution,[],[f250,f53])).

fof(f250,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_setfam_1(sK4(X0,X1),X2)
      | ~ m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
      | ~ sP0(X2,X3)
      | sP0(X0,X1)
      | ~ m1_setfam_1(sK5(X2,X3,sK4(X0,X1)),X0)
      | ~ v1_tops_2(sK4(X0,X1),X3)
      | ~ m1_subset_1(sK5(X2,X3,sK4(X0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    inference(duplicate_literal_removal,[],[f249])).

fof(f249,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_setfam_1(sK4(X0,X1),X2)
      | ~ m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
      | ~ sP0(X2,X3)
      | sP0(X0,X1)
      | ~ m1_setfam_1(sK5(X2,X3,sK4(X0,X1)),X0)
      | ~ v1_tops_2(sK4(X0,X1),X3)
      | ~ m1_subset_1(sK5(X2,X3,sK4(X0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ v1_tops_2(sK4(X0,X1),X3)
      | ~ m1_setfam_1(sK4(X0,X1),X2)
      | ~ m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
      | ~ sP0(X2,X3) ) ),
    inference(resolution,[],[f110,f49])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( r1_tarski(sK5(X0,X1,X4),X4)
      | ~ v1_tops_2(X4,X1)
      | ~ m1_setfam_1(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f110,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_tarski(sK5(X2,X1,X0),sK4(X3,X4))
      | ~ m1_setfam_1(X0,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ sP0(X2,X1)
      | sP0(X3,X4)
      | ~ m1_setfam_1(sK5(X2,X1,X0),X3)
      | ~ v1_tops_2(X0,X1)
      | ~ m1_subset_1(sK5(X2,X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X4)))) ) ),
    inference(resolution,[],[f51,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_finset_1(X3)
      | sP0(X0,X1)
      | ~ m1_setfam_1(X3,X0)
      | ~ r1_tarski(X3,sK4(X0,X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( v1_finset_1(sK5(X0,X1,X4))
      | ~ v1_tops_2(X4,X1)
      | ~ m1_setfam_1(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f702,plain,
    ( ~ spl6_20
    | spl6_23
    | spl6_16 ),
    inference(avatar_split_clause,[],[f674,f192,f280,f266])).

fof(f674,plain,
    ( ! [X2,X1] :
        ( g1_pre_topc(X1,X2) != g1_pre_topc(u1_struct_0(sK2),sK4(sK3,sK2))
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),sK4(sK3,sK2))) = X1
        | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),sK4(sK3,sK2))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),sK4(sK3,sK2)))))) )
    | spl6_16 ),
    inference(superposition,[],[f63,f663])).

fof(f663,plain,
    ( g1_pre_topc(u1_struct_0(sK2),sK4(sK3,sK2)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),sK4(sK3,sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),sK4(sK3,sK2))))
    | spl6_16 ),
    inference(resolution,[],[f194,f115])).

fof(f115,plain,(
    ! [X2,X1] :
      ( sP0(X2,X1)
      | g1_pre_topc(u1_struct_0(X1),sK4(X2,X1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),sK4(X2,X1))),u1_pre_topc(g1_pre_topc(u1_struct_0(X1),sK4(X2,X1)))) ) ),
    inference(resolution,[],[f113,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) = g1_pre_topc(u1_struct_0(g1_pre_topc(X0,X1)),u1_pre_topc(g1_pre_topc(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) = g1_pre_topc(u1_struct_0(g1_pre_topc(X0,X1)),u1_pre_topc(g1_pre_topc(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f97,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(g1_pre_topc(X0,X1))
      | g1_pre_topc(X0,X1) = g1_pre_topc(u1_struct_0(g1_pre_topc(X0,X1)),u1_pre_topc(g1_pre_topc(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f45,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f701,plain,
    ( ~ spl6_20
    | spl6_24
    | spl6_16 ),
    inference(avatar_split_clause,[],[f676,f192,f284,f266])).

fof(f676,plain,
    ( ! [X6,X5] :
        ( g1_pre_topc(X5,X6) != g1_pre_topc(u1_struct_0(sK2),sK4(sK3,sK2))
        | u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),sK4(sK3,sK2))) = X6
        | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),sK4(sK3,sK2))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),sK4(sK3,sK2)))))) )
    | spl6_16 ),
    inference(superposition,[],[f64,f663])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f700,plain,
    ( spl6_20
    | ~ spl6_22 ),
    inference(avatar_contradiction_clause,[],[f698])).

fof(f698,plain,
    ( $false
    | spl6_20
    | ~ spl6_22 ),
    inference(resolution,[],[f329,f277])).

fof(f277,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),sK4(sK3,sK2)))
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f275])).

fof(f275,plain,
    ( spl6_22
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),sK4(sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f329,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),sK4(sK3,sK2)))
    | spl6_20 ),
    inference(resolution,[],[f268,f44])).

fof(f44,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f268,plain,
    ( ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),sK4(sK3,sK2))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),sK4(sK3,sK2))))))
    | spl6_20 ),
    inference(avatar_component_clause,[],[f266])).

fof(f650,plain,
    ( spl6_16
    | ~ spl6_1
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f320,f185,f66,f192])).

fof(f66,plain,
    ( spl6_1
  <=> v2_compts_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f185,plain,
    ( spl6_15
  <=> sP1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f320,plain,
    ( ~ v2_compts_1(sK3,sK2)
    | sP0(sK3,sK2)
    | ~ spl6_15 ),
    inference(resolution,[],[f187,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ v2_compts_1(X1,X0)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( v2_compts_1(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v2_compts_1(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v2_compts_1(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f187,plain,
    ( sP1(sK2,sK3)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f185])).

fof(f649,plain,
    ( spl6_7
    | spl6_56 ),
    inference(avatar_contradiction_clause,[],[f647])).

fof(f647,plain,
    ( $false
    | spl6_7
    | spl6_56 ),
    inference(resolution,[],[f639,f105])).

fof(f105,plain,
    ( ~ sP0(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f104])).

fof(f639,plain,
    ( sP0(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | spl6_56 ),
    inference(resolution,[],[f618,f54])).

fof(f618,plain,
    ( ~ v1_tops_2(sK4(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | spl6_56 ),
    inference(avatar_component_clause,[],[f616])).

fof(f616,plain,
    ( spl6_56
  <=> v1_tops_2(sK4(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).

fof(f621,plain,(
    spl6_55 ),
    inference(avatar_contradiction_clause,[],[f620])).

fof(f620,plain,
    ( $false
    | spl6_55 ),
    inference(resolution,[],[f614,f37])).

fof(f37,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
      | ~ v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v2_compts_1(sK3,sK2) )
    & ( ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
        & v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) )
      | ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
        & v2_compts_1(sK3,sK2) ) )
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f24,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v2_compts_1(X1,X0) )
            & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
                & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
              | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v2_compts_1(X1,X0) ) ) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
            | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
            | ~ v2_compts_1(X1,sK2) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
              & v2_compts_1(X1,sK2) ) ) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
          | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
          | ~ v2_compts_1(X1,sK2) )
        & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) )
          | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
            & v2_compts_1(X1,sK2) ) ) )
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
        | ~ v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ v2_compts_1(sK3,sK2) )
      & ( ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
          & v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) )
        | ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
          & v2_compts_1(sK3,sK2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v2_compts_1(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) ) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v2_compts_1(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) ) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_compts_1)).

fof(f614,plain,
    ( ~ v2_pre_topc(sK2)
    | spl6_55 ),
    inference(avatar_component_clause,[],[f612])).

fof(f619,plain,
    ( spl6_12
    | ~ spl6_55
    | ~ spl6_13
    | ~ spl6_56
    | ~ spl6_53
    | ~ spl6_10
    | spl6_52 ),
    inference(avatar_split_clause,[],[f607,f584,f139,f588,f616,f158,f612,f154])).

fof(f588,plain,
    ( spl6_53
  <=> m1_subset_1(sK4(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f584,plain,
    ( spl6_52
  <=> v1_tops_2(sK4(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f607,plain,
    ( ~ m1_subset_1(sK4(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ v1_tops_2(sK4(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl6_10
    | spl6_52 ),
    inference(forward_demodulation,[],[f606,f175])).

fof(f606,plain,
    ( ~ m1_subset_1(sK4(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
    | ~ v1_tops_2(sK4(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl6_52 ),
    inference(resolution,[],[f586,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
      | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f586,plain,
    ( ~ v1_tops_2(sK4(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),sK2)
    | spl6_52 ),
    inference(avatar_component_clause,[],[f584])).

fof(f610,plain,
    ( spl6_7
    | ~ spl6_10
    | spl6_53 ),
    inference(avatar_contradiction_clause,[],[f608])).

fof(f608,plain,
    ( $false
    | spl6_7
    | ~ spl6_10
    | spl6_53 ),
    inference(resolution,[],[f590,f325])).

fof(f325,plain,
    ( m1_subset_1(sK4(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | spl6_7
    | ~ spl6_10 ),
    inference(resolution,[],[f105,f198])).

fof(f198,plain,
    ( ! [X3] :
        ( sP0(X3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
        | m1_subset_1(sK4(X3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
    | ~ spl6_10 ),
    inference(superposition,[],[f52,f175])).

fof(f590,plain,
    ( ~ m1_subset_1(sK4(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | spl6_53 ),
    inference(avatar_component_clause,[],[f588])).

fof(f602,plain,
    ( spl6_7
    | spl6_51 ),
    inference(avatar_contradiction_clause,[],[f600])).

fof(f600,plain,
    ( $false
    | spl6_7
    | spl6_51 ),
    inference(resolution,[],[f599,f105])).

fof(f599,plain,
    ( sP0(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | spl6_51 ),
    inference(resolution,[],[f582,f53])).

fof(f582,plain,
    ( ~ m1_setfam_1(sK4(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),sK3)
    | spl6_51 ),
    inference(avatar_component_clause,[],[f580])).

fof(f580,plain,
    ( spl6_51
  <=> m1_setfam_1(sK4(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f591,plain,
    ( ~ spl6_51
    | ~ spl6_16
    | ~ spl6_52
    | ~ spl6_53
    | spl6_7
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f578,f139,f104,f588,f584,f192,f580])).

fof(f578,plain,
    ( ~ m1_subset_1(sK4(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ v1_tops_2(sK4(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),sK2)
    | ~ sP0(sK3,sK2)
    | ~ m1_setfam_1(sK4(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),sK3)
    | spl6_7
    | ~ spl6_10 ),
    inference(duplicate_literal_removal,[],[f573])).

fof(f573,plain,
    ( ~ m1_subset_1(sK4(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ v1_tops_2(sK4(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),sK2)
    | ~ sP0(sK3,sK2)
    | ~ v1_tops_2(sK4(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),sK2)
    | ~ m1_setfam_1(sK4(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),sK3)
    | ~ m1_subset_1(sK4(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ sP0(sK3,sK2)
    | spl6_7
    | ~ spl6_10 ),
    inference(resolution,[],[f570,f48])).

fof(f570,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK5(sK3,X3,sK4(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | ~ m1_subset_1(sK4(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
        | ~ v1_tops_2(sK4(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),X3)
        | ~ sP0(sK3,X3) )
    | spl6_7
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f568,f175])).

fof(f568,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK4(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
        | ~ v1_tops_2(sK4(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),X3)
        | ~ m1_subset_1(sK5(sK3,X3,sK4(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
        | ~ sP0(sK3,X3) )
    | spl6_7 ),
    inference(resolution,[],[f462,f105])).

fof(f323,plain,
    ( spl6_3
    | ~ spl6_7
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f101,f92,f104,f74])).

fof(f74,plain,
    ( spl6_3
  <=> v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f92,plain,
    ( spl6_6
  <=> sP1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f101,plain,
    ( ~ sP0(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ spl6_6 ),
    inference(resolution,[],[f94,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ sP0(X1,X0)
      | v2_compts_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f94,plain,
    ( sP1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f92])).

fof(f322,plain,
    ( ~ spl6_2
    | spl6_4
    | ~ spl6_10 ),
    inference(avatar_contradiction_clause,[],[f321])).

fof(f321,plain,
    ( $false
    | ~ spl6_2
    | spl6_4
    | ~ spl6_10 ),
    inference(resolution,[],[f315,f71])).

fof(f71,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl6_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f315,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | spl6_4
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f80,f175])).

fof(f80,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
    | spl6_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl6_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f318,plain,
    ( ~ spl6_13
    | spl6_15
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f317,f70,f185,f158])).

fof(f317,plain,
    ( sP1(sK2,sK3)
    | ~ l1_pre_topc(sK2)
    | ~ spl6_2 ),
    inference(resolution,[],[f71,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f15,f21,f20])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_compts_1(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( v1_finset_1(X3)
                    & m1_setfam_1(X3,X1)
                    & r1_tarski(X3,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                | ~ v1_tops_2(X2,X0)
                | ~ m1_setfam_1(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_compts_1(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( v1_finset_1(X3)
                    & m1_setfam_1(X3,X1)
                    & r1_tarski(X3,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                | ~ v1_tops_2(X2,X0)
                | ~ m1_setfam_1(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_compts_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                       => ~ ( v1_finset_1(X3)
                            & m1_setfam_1(X3,X1)
                            & r1_tarski(X3,X2) ) )
                    & v1_tops_2(X2,X0)
                    & m1_setfam_1(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_compts_1)).

fof(f314,plain,
    ( spl6_16
    | spl6_22 ),
    inference(avatar_contradiction_clause,[],[f313])).

fof(f313,plain,
    ( $false
    | spl6_16
    | spl6_22 ),
    inference(resolution,[],[f312,f194])).

fof(f312,plain,
    ( sP0(sK3,sK2)
    | spl6_22 ),
    inference(resolution,[],[f305,f52])).

fof(f305,plain,
    ( ~ m1_subset_1(sK4(sK3,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | spl6_22 ),
    inference(resolution,[],[f276,f62])).

fof(f276,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),sK4(sK3,sK2)))
    | spl6_22 ),
    inference(avatar_component_clause,[],[f275])).

fof(f195,plain,
    ( spl6_1
    | ~ spl6_16
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f189,f185,f192,f66])).

fof(f189,plain,
    ( ~ sP0(sK3,sK2)
    | v2_compts_1(sK3,sK2)
    | ~ spl6_15 ),
    inference(resolution,[],[f187,f47])).

fof(f188,plain,
    ( ~ spl6_13
    | spl6_15
    | ~ spl6_4
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f182,f139,f78,f185,f158])).

fof(f182,plain,
    ( sP1(sK2,sK3)
    | ~ l1_pre_topc(sK2)
    | ~ spl6_4
    | ~ spl6_10 ),
    inference(resolution,[],[f180,f56])).

fof(f180,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl6_4
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f79,f175])).

fof(f79,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f183,plain,
    ( spl6_2
    | ~ spl6_4
    | ~ spl6_10 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | spl6_2
    | ~ spl6_4
    | ~ spl6_10 ),
    inference(resolution,[],[f180,f72])).

fof(f72,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f171,plain,
    ( ~ spl6_5
    | spl6_8 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | ~ spl6_5
    | spl6_8 ),
    inference(resolution,[],[f151,f89])).

fof(f89,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl6_5
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f151,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | spl6_8 ),
    inference(resolution,[],[f132,f44])).

fof(f132,plain,
    ( ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
    | spl6_8 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl6_8
  <=> m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f168,plain,(
    ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f167])).

fof(f167,plain,
    ( $false
    | ~ spl6_12 ),
    inference(resolution,[],[f156,f36])).

fof(f36,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f156,plain,
    ( v2_struct_0(sK2)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f154])).

fof(f166,plain,(
    spl6_13 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | spl6_13 ),
    inference(resolution,[],[f160,f38])).

fof(f38,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f160,plain,
    ( ~ l1_pre_topc(sK2)
    | spl6_13 ),
    inference(avatar_component_clause,[],[f158])).

fof(f141,plain,
    ( ~ spl6_8
    | spl6_10 ),
    inference(avatar_split_clause,[],[f124,f139,f130])).

fof(f124,plain,(
    ! [X2,X1] :
      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X1,X2)
      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = X1
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) ) ),
    inference(superposition,[],[f63,f117])).

fof(f117,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) ),
    inference(resolution,[],[f114,f38])).

fof(f114,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) ) ),
    inference(resolution,[],[f113,f44])).

fof(f107,plain,
    ( spl6_7
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f102,f92,f74,f104])).

fof(f102,plain,
    ( ~ v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | sP0(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ spl6_6 ),
    inference(resolution,[],[f94,f46])).

fof(f100,plain,(
    spl6_5 ),
    inference(avatar_contradiction_clause,[],[f99])).

fof(f99,plain,
    ( $false
    | spl6_5 ),
    inference(resolution,[],[f98,f38])).

fof(f98,plain,
    ( ~ l1_pre_topc(sK2)
    | spl6_5 ),
    inference(resolution,[],[f96,f44])).

fof(f96,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | spl6_5 ),
    inference(resolution,[],[f90,f62])).

fof(f90,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | spl6_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f95,plain,
    ( ~ spl6_5
    | spl6_6
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f86,f78,f92,f88])).

fof(f86,plain,
    ( sP1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ spl6_4 ),
    inference(resolution,[],[f56,f79])).

fof(f85,plain,
    ( spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f39,f74,f66])).

fof(f39,plain,
    ( v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | v2_compts_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f82,plain,
    ( spl6_2
    | spl6_4 ),
    inference(avatar_split_clause,[],[f42,f78,f70])).

fof(f42,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f27])).

fof(f81,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f43,f78,f74,f70,f66])).

fof(f43,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
    | ~ v2_compts_1(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_compts_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f27])).

%------------------------------------------------------------------------------
